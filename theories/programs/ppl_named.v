(**md**************************************************************************)
(** * Saito–Affeldt-style named-variable surface syntax for the PPL of [ppl.v]

    This file defines a NAMED-VARIABLE concrete syntax for the De Bruijn
    intrinsically-typed PPL of [theories/programs/ppl.v], in the style of
    Saito–Affeldt (APLAS 2023 §5.1–§5.3, §6).  The semantics is delegated
    one-to-one to [eD] of [ppl.v] via a structural translation
    [nexp_to_dexp : named_expr Γ t → expr (drop_names Γ) t]; nothing is
    re-interpreted.  As a corollary, the axiom-clean structural reductions
    [ex_random_constant_denot_E] / [ex_random_linear_denot_E] carry over
    unchanged to the named versions.

    ** Design (Saito–Affeldt skeleton) **

    - A named context [named_ctx := seq (string * ppl_type Ar)] pairs each
      slot with a string identifier.
    - [drop_names : named_ctx → ppl_ctx] forgets the names; this is the
      bridge to [ppl.v]'s [ppl_ctx = list ppl_type].
    - [named_var Γ t] is the named analogue of [has_var]: a witness that
      a string identifier in [Γ] has type [t].  Two constructors:
        - [nv_head x t Γ : named_var ((x,t) :: Γ) t] (variable is the head);
        - [nv_tail x t y s (Hxy : x <> y) v : named_var ((y,s) :: Γ) t]
          (variable is in the tail, with a string-disequality witness).
    - [named_expr : named_ctx → ppl_type → Type] mirrors [expr]
      constructor-for-constructor, using [named_var] in place of
      [has_var] and extending [named_ctx] with strings at binding sites
      ([nlam], [nbind]).
    - [nv_to_hv] and [nexp_to_dexp] are TOTAL structural translations
      to the De Bruijn syntax; the named semantics is one line:
      [neD e := eD (nexp_to_dexp e)].

    ** Variable lookup encoding — CANONICAL STRUCTURES (Saito–Affeldt §5.2) **

    The Saito–Affeldt encoding (paper §5.2) achieves "write [#"x"], let
    Coq infer the context slot" by canonical structures [found_tag] /
    [recurse_tag] + the [infer] typeclass of mathcomp-analysis.  We
    follow that pattern verbatim:

      - [tagged_nctx] — a tagged wrapper around [named_ctx];
      - [find_nv s t] — a structure pairing a tagged context with a
        [named_var]-witness of "[s] is bound to type [t] in that
        context";
      - [found_nctx] (canonical) / [recurse_nctx] — the two tags driving
        head-first / tail-recursive canonical-structure search;
      - [found_nv] (canonical) : the head case [(s, t) :: G];
      - [recurse_nv] (canonical) : the tail case with an
        [infer (String.eqb s y = false)] disequality witness;
      - [ne_var' s _] : the user-facing variable form whose [t] and
        whole [find_nv] structure are filled by canonical search.

    The [infer] typeclass comes from [mathcomp.reals.signed].  Both
    [String.eqb] (Stdlib) and [infer] are reusable infrastructure
    already present — no new typeclass / boolean-equality wiring is
    needed.

    All examples in this file use concrete strings, so canonical-search
    succeeds by [vm_compute] of the boolean disequality at every step.
    For abstract contexts the user would have to pass an explicit
    [find_nv] proof — exactly the Saito–Affeldt ergonomic story.

    ** Bidirectionality hints (the [&] marks) **

    Every constructor that BINDS in its body ([ne_lam], [ne_bind]) AND
    every constructor whose context is shared by sub-terms ([ne_add],
    [ne_mul], [ne_pair], [ne_fst], [ne_snd], [ne_app], [ne_ret]) carries
    a bidirectionality hint [&] in its [Arguments] directive.  These
    hints tell Coq's elaborator: resolve the outer context [G] FIRST
    (using the expected type from the enclosing term), THEN propagate
    into the sub-expressions.  Without these hints the canonical-
    structure lookup at [#"x"] sites is fired with an OPEN context
    metavariable and commits to a wrong [find_nv] instance (typically
    [found_nv] at the wrong head slot).  The hints are crucial — they
    are the difference between the linear example type-checking and
    failing.  This is exactly the Saito–Affeldt
    [Arguments exp_letin {g} & {t1 t2}] pattern (paper §5.1).

    ** Surface notation — custom entry [ppl_named] **

    Following Saito–Affeldt §5.3:

      [...]                         enter the named-PPL grammar
      {...}                         escape back to Coq
      Ret e                         e_ret (named)
      let "x" := M in N             monadic let (= e_bind + e_lam-style)
      Sample (mu , Hmu)             sample primitive
      Score (r , Hr0 , Hr1)         score primitive
      \ "x" ::: A => M               lambda with named binder of type A
      M @ N                         direct application
      # "x"                         variable lookup by string
      M + N , M * N                 e_add / e_mul on tR
      e1 , e2 ; fst e ; snd e ; ()  pairs / projections / unit
      [|r|]                         real literal (= e_real)

    Note: pure [let] (non-monadic) is omitted on purpose — our PPL is
    monadic by construction; the surface [let "x" := M in N] desugars to
    [e_bind] (which matches the QBS-paper convention since every term is
    a Kleisli arrow).  For pure lambdas use [\"x" ::: A => M].

    ** Cheat sheet **

    [[
      Surface (named)                     | Desugars to (De Bruijn)
      ---------------------------------- | ----------------------------------
      [ Ret e ]                          | e_ret e
      [ let "x" := M in N ]              | e_bind M (e_ret (e_lam (...N...)))
                                         |   Actually: e_bind M N' where N' = nexp_to_dexp N
                                         |   in the extended named ctx
                                         |   ("x", t) :: G ;
                                         |   #"x" inside N becomes hv_zero.
      [ Sample (mu, Hmu) ]               | e_sample mu Hmu
      [ Score (r, Hr0, Hr1) ]            | e_score r Hr0 Hr1
      [ \"x" ::: A => M ]                 | e_lam (...M...) with #"x" = hv_zero
      [ M @ N ]                          | e_app M N
      [ # "x" ]                          | e_var (fn_proof (g : find_nv "x" _))
                                         |   where [g] is found by canonical search
      [ M + N ]                          | e_add M N
      [ M * N ]                          | e_mul M N
      [ (M , N) ]                        | e_pair M N
      [ fst M ] / [ snd M ]              | e_fst M / e_snd M
      [ () ]                             | e_tt
      [ [| r |] ]                        | e_real r
      [ { x } ]                          | x : escape to Coq term
    ]]

    The two existing flagship examples re-cast in this surface notation:

    [[
      Definition ex_named_random_constant : named_expr [] (tprob (tfun tR tR)) :=
        [ let "c" := Sample (mu , Hmu) in Ret (\"x" ::: tR => # "c") ].

      Definition ex_named_random_linear : named_expr [] (tprob (tfun tR tR)) :=
        [ let "m" := Sample (mu , Hmu) in
          let "b" := Sample (mu , Hmu) in
          Ret (\"x" ::: tR => # "m" * # "x" + # "b") ].
    ]]

    The corresponding equivalence lemmas

      Lemma ex_named_random_constant_E : nexp_to_dexp ex_named_random_constant
                                        = ex_random_constant mu Hmu.
      Lemma ex_named_random_linear_E   : nexp_to_dexp ex_named_random_linear
                                        = ex_random_linear   mu Hmu.

    are both [Proof. by []. Qed.] — the translation is structural and the
    concrete contexts let Coq's conversion check that #"c" / #"m" /
    #"x" / #"b" resolve to the right De Bruijn index.  Hence the existing
    axiom-clean reductions [ex_random_constant_denot_E] and
    [ex_random_linear_denot_E] carry over to the named versions verbatim.
*)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals signed.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import measure dirac_measure.

From Stdlib Require Import Strings.String.

Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.cone_cat.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.icones.icone.
Require Import Icones.homs.coalgebra.
Require Import Icones.homs.em_cat.
Require Import Icones.programs.cbv.
Require Import Icones.programs.ppl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** Named contexts and named-variable witnesses *)

Section NamedCtx.
Variable (R : realType) (Ar : MeasSubcat R).

Definition named_ctx : Type := list (string * ppl_type Ar).

Definition drop_names (G : named_ctx) : ppl_ctx Ar :=
  map snd G.

(** [named_var G t]: a witness that some string identifier in [G] is
    bound to type [t]. *)
Inductive named_var : named_ctx -> ppl_type Ar -> Type :=
  | nv_head (x : string) (t : ppl_type Ar) (G : named_ctx) :
      named_var ((x, t) :: G) t
  | nv_tail (y : string) (s : ppl_type Ar) (G : named_ctx)
            (t : ppl_type Ar) (v : named_var G t) :
      named_var ((y, s) :: G) t.

End NamedCtx.

Arguments named_ctx {R} Ar.
Arguments drop_names {R Ar} G.
Arguments named_var {R Ar} G t.
Arguments nv_head {R Ar} x t G.
Arguments nv_tail {R Ar} y s G {t} v.

(** ** Named-expression syntax — mirror of [expr], one constructor each *)

Section NamedSyntax.
Variable (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).

Local Notation tR' := (tR R_obj).
Local Notation T := (@ppl_type R Ar).

Inductive named_expr : named_ctx Ar -> T -> Type :=
  | ne_var   (G : named_ctx Ar) (t : T) :
      named_var G t -> named_expr G t
  | ne_tt    (G : named_ctx Ar) : named_expr G tunit
  | ne_pair  (G : named_ctx Ar) (t1 t2 : T) :
      named_expr G t1 -> named_expr G t2 -> named_expr G (tprod t1 t2)
  | ne_fst   (G : named_ctx Ar) (t1 t2 : T) :
      named_expr G (tprod t1 t2) -> named_expr G t1
  | ne_snd   (G : named_ctx Ar) (t1 t2 : T) :
      named_expr G (tprod t1 t2) -> named_expr G t2
  | ne_lam   (G : named_ctx Ar) (x : string) (t1 t2 : T) :
      named_expr ((x, t1) :: G) t2 -> named_expr G (tfun t1 t2)
  | ne_app   (G : named_ctx Ar) (t1 t2 : T) :
      named_expr G (tfun t1 t2) -> named_expr G t1 -> named_expr G t2
  | ne_ret   (G : named_ctx Ar) (t : T) :
      named_expr G t -> named_expr G (tprob t)
  | ne_bind  (G : named_ctx Ar) (x : string) (t1 t2 : T) :
      named_expr G (tprob t1) ->
      named_expr ((x, t1) :: G) (tprob t2) ->
      named_expr G (tprob t2)
  | ne_sample (G : named_ctx Ar) (X : ar_obj Ar)
              (mu : fmeas R (ar_carrier Ar X))
              (Hmu : (cone_norm mu <= 1)%R) :
      named_expr G (tprob (tbase X))
  | ne_real  (G : named_ctx Ar) (r : R) : named_expr G tR'
  | ne_score (G : named_ctx Ar) (r : R)
             (Hr0 : (0 <= r)%R) (Hr1 : (r <= 1)%R) :
      named_expr G (tprob tunit)
  | ne_add   (G : named_ctx Ar) :
      named_expr G tR' -> named_expr G tR' -> named_expr G tR'
  | ne_mul   (G : named_ctx Ar) :
      named_expr G tR' -> named_expr G tR' -> named_expr G tR'.

End NamedSyntax.

Arguments named_expr {R Ar R_obj} G t.
Arguments ne_var {R Ar R_obj G t} v.
Arguments ne_tt {R Ar R_obj G}.
Arguments ne_pair {R Ar R_obj G t1 t2} M N.
Arguments ne_fst {R Ar R_obj G t1 t2} M.
Arguments ne_snd {R Ar R_obj G t1 t2} M.
(** Bidirectionality hints ([&]) on the binding-site constructors:
    tell Coq to resolve the outer index [G] (and the binder slot's type
    [t1] where applicable) FIRST, then propagate into the body so the
    canonical-structure search of [#"x"] sees a concrete context.
    Without these hints the [find_nv] CS lookup is launched with an
    open context metavariable and picks the wrong instance — see the
    [find_nv] docstring. *)
Arguments ne_pair {R Ar R_obj G t1 t2} & M N.
Arguments ne_fst {R Ar R_obj G t1 t2} & M.
Arguments ne_snd {R Ar R_obj G t1 t2} & M.
Arguments ne_lam {R Ar R_obj G} x & {t1 t2} M.
Arguments ne_app {R Ar R_obj G t1 t2} & F X.
Arguments ne_ret {R Ar R_obj G t} & M.
Arguments ne_bind {R Ar R_obj G} x & {t1 t2} M K.
Arguments ne_sample {R Ar R_obj G X} mu Hmu.
Arguments ne_real {R Ar R_obj G} r.
Arguments ne_score {R Ar R_obj G} r Hr0 Hr1.
Arguments ne_add {R Ar R_obj G} & M N.
Arguments ne_mul {R Ar R_obj G} & M N.

(** ** Translation to De Bruijn — the semantic bridge *)

Section Translate.
Variable (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).

(** Translate a named variable witness to its De Bruijn index in the
    name-stripped context.  Structural recursion on [v]. *)
Fixpoint nv_to_hv (G : named_ctx Ar) (t : ppl_type Ar)
    (v : named_var G t) {struct v} : has_var (drop_names G) t :=
  match v in named_var G0 t0 return has_var (drop_names G0) t0 with
  | nv_head _ _ _ => hv_zero
  | nv_tail _ _ _ _ v' => hv_succ (nv_to_hv v')
  end.

(** Translate a named expression to a De Bruijn expression.  Structural
    recursion on [e], one clause per constructor of [named_expr]. *)
Fixpoint nexp_to_dexp (G : named_ctx Ar) (t : ppl_type Ar)
    (e : @named_expr R Ar R_obj G t) {struct e} :
    @expr R Ar R_obj (drop_names G) t :=
  match e in named_expr G0 t0 return @expr R Ar R_obj (drop_names G0) t0 with
  | ne_var _ _ v => e_var (nv_to_hv v)
  | ne_tt _ => e_tt
  | ne_pair _ _ _ M N => e_pair (nexp_to_dexp M) (nexp_to_dexp N)
  | ne_fst _ _ _ M => e_fst (nexp_to_dexp M)
  | ne_snd _ _ _ M => e_snd (nexp_to_dexp M)
  | ne_lam _ _ _ _ M => e_lam (nexp_to_dexp M)
  | ne_app _ _ _ F X => e_app (nexp_to_dexp F) (nexp_to_dexp X)
  | ne_ret _ _ M => e_ret (nexp_to_dexp M)
  | ne_bind _ _ _ _ M K => e_bind (nexp_to_dexp M) (nexp_to_dexp K)
  | ne_sample _ _ mu Hmu => e_sample mu Hmu
  | ne_real _ r => e_real r
  | ne_score _ r Hr0 Hr1 => e_score r Hr0 Hr1
  | ne_add _ M N => e_add (nexp_to_dexp M) (nexp_to_dexp N)
  | ne_mul _ M N => e_mul (nexp_to_dexp M) (nexp_to_dexp N)
  end.

End Translate.

Arguments nv_to_hv {R Ar G t} v.
Arguments nexp_to_dexp {R Ar R_obj G t} e.

(** ** Named-PPL semantics — one line via [eD]. *)

Section NamedSemantics.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Definition neD (G : named_ctx Ar) (t : ppl_type Ar)
    (e : @named_expr R Ar R_obj G t) :
    coalg_hom (ctxD (drop_names G)) (Tobj (tyD t)) :=
  @eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas
      (drop_names G) t (nexp_to_dexp e).

End NamedSemantics.

Arguments neD {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G t} e.

(** ** Variable lookup by string — Saito–Affeldt canonical structures *)

(** The Saito–Affeldt encoding (APLAS 2023 §5.2) uses a tagged structure
    [find_nv s t] whose canonical-structure search builds the context
    along with type inference.  The user writes [#"x"] and Coq's
    canonical-structure search finds the right named context AND the
    right type AND the right [named_var] witness in one go.

    Concretely:

    - [tagged_nctx] = a tagged [named_ctx] (so we can drive canonical
      search through it);
    - [find_nv s t] = a structure paired with a [tagged_nctx] and a
      [named_var]-of-that-context-at-type-[t] witness;
    - [found_tag] / [recurse_tag] : two tags for the head/tail cases
      ([found_tag] is canonical, so canonical search tries the head
      case first; otherwise Coq unfolds [found_tag] to reveal
      [recurse_tag] and recurses on the tail).

    To handle the "different-string-in-tail" case we rely on
    [infer (String.eqb s y = false)] : the [infer] class of
    [mathcomp.reals.signed] resolves to a [vm_compute]-reducible
    truth-of-boolean witness for the *concrete* string disequalities
    that occur in our examples — exactly the Saito–Affeldt usage of
    [infer]. *)

(** Tagged named-context — the canonical-structure dispatcher.  Note:
    we deliberately keep [tagged_nctx] / [find_nv] / the canonical
    instances OUTSIDE any [Section] so that [Set Implicit Arguments]
    binds [R, Ar] as STRICT IMPLICIT directly on the structure (rather
    than as section-discharged parameters), matching the way
    Saito–Affeldt's [find] structure is set up in their development.
    [R] and [Ar] are then inferred from the surrounding context at
    every canonical-structure use site. *)
Structure tagged_nctx (R : realType) (Ar : MeasSubcat R) :=
  Tag_nctx { untag_nctx : named_ctx Ar }.

Arguments Tag_nctx {R Ar} _.

(** The [find_nv s t] structure: a tagged context together with a proof
    that the string [s] is bound to type [t] in that context.  *)
Structure find_nv (R : realType) (Ar : MeasSubcat R)
    (s : string) (t : ppl_type Ar) : Type := Find_nv {
  fn_ctx  : tagged_nctx Ar;
  fn_proof : named_var (untag_nctx fn_ctx) t
}.

Arguments Find_nv {R Ar} s t _ _.

(** The two tags: [found_nctx] (canonical) and [recurse_nctx] (fallback).
    Both unfold to [Tag_nctx], but [found_nctx] is the one Coq's
    canonical-structure search tries FIRST.  Verbatim from
    Saito–Affeldt §5.2 ([found_tag] / [recurse_tag]). *)
Definition recurse_nctx (R : realType) (Ar : MeasSubcat R)
    (G : named_ctx Ar) := Tag_nctx G.
Canonical found_nctx (R : realType) (Ar : MeasSubcat R)
    (G : named_ctx Ar) := recurse_nctx G.

(** Canonical instance 1 (head case): the sought string is the head of
    the context. *)
Canonical found_nv (R : realType) (Ar : MeasSubcat R)
    (s : string) (t : ppl_type Ar) (G : named_ctx Ar) :
    find_nv s t :=
  @Find_nv R Ar s t (found_nctx ((s, t) :: G)) (nv_head s t G).

(** Canonical instance 2 (tail case): the sought string is NOT the head
    of the context.  Driven by [infer (String.eqb s y = false)]; the
    boolean disequality witness is found by canonical search /
    [vm_compute] in concrete cases. *)
Canonical recurse_nv (R : realType) (Ar : MeasSubcat R)
    (s : string) (t : ppl_type Ar) (y : string)
    (sty : ppl_type Ar) (Hneq : infer (String.eqb s y = false))
    (g : find_nv s t) : find_nv s t :=
  @Find_nv R Ar s t
    (recurse_nctx ((y, sty) :: untag_nctx (fn_ctx g)))
    (nv_tail y sty (untag_nctx (fn_ctx g)) (fn_proof g)).

(** [ne_var'] — the canonical-structure-driven version of [ne_var].  The
    user writes [ne_var' "x" _] (or just [#"x"] via the notation) and
    Coq fills in the context [G] AND the type [t] AND the
    [named_var]-witness all by canonical-structure resolution. *)
Definition ne_var' (R : realType) (Ar : MeasSubcat R) (R_obj : ar_obj Ar)
    (s : string) (t : ppl_type Ar) (g : find_nv s t) :
    @named_expr R Ar R_obj (untag_nctx (fn_ctx g)) t :=
  ne_var (fn_proof g).

(** Force [s] to be EXPLICIT and [R, Ar, R_obj, t] implicit in
    [ne_var'].  Crucial for the [# x] notation. *)
Arguments ne_var' {R Ar R_obj} s {t} g.

(** ** Surface notation — custom entry [ppl_named] *)

Declare Custom Entry ppl_named.

(** Brackets [...] enter the surface grammar.  Curly braces {...} drop
    back into ambient Coq. *)
Notation "[ e ]" := e (e custom ppl_named at level 90).
Notation "{ x }" := x (in custom ppl_named at level 0, x constr).

(** Parenthesisation inside the surface. *)
Notation "( e )" := e (in custom ppl_named at level 0, e custom ppl_named).

(** Unit literal. *)
Notation "()" := ne_tt (in custom ppl_named at level 0).

(** Variable lookup [# "x"] : uses the canonical-structures [ne_var']
    so Coq's canonical-structure search fills in the context AND the
    type AND the [named_var] witness automatically.  In concrete
    contexts the search reduces by [vm_compute] / canonical resolution
    to the right [nv_head] / [nv_tail] cascade. *)
Notation "# x" :=
  (ne_var' x%string _)
  (in custom ppl_named at level 1, x constr at level 0).

(** Real literal — write as [| r |] to keep the entry self-contained. *)
Notation "[| r |]" := (ne_real r) (in custom ppl_named at level 1, r constr).

(** Monadic return. *)
Notation "'Ret' e" := (ne_ret e)
  (in custom ppl_named at level 60, e custom ppl_named at level 60,
   right associativity).

(** Sample primitive — takes a [(mu, Hmu)] Coq pair. *)
Notation "'Sample' ( mu , Hmu )" :=
  (ne_sample mu Hmu)
  (in custom ppl_named at level 1, mu constr, Hmu constr).

(** Score primitive — takes a [(r, Hr0, Hr1)] Coq triple. *)
Notation "'Score' ( r , Hr0 , Hr1 )" :=
  (ne_score r Hr0 Hr1)
  (in custom ppl_named at level 1, r constr, Hr0 constr, Hr1 constr).

(** Pair, projections. *)
Notation "( e1 , e2 )" := (ne_pair e1 e2)
  (in custom ppl_named at level 0,
   e1 custom ppl_named at level 60,
   e2 custom ppl_named at level 60).
Notation "'fst' e" := (ne_fst e)
  (in custom ppl_named at level 10, e custom ppl_named at level 10).
Notation "'snd' e" := (ne_snd e)
  (in custom ppl_named at level 10, e custom ppl_named at level 10).

(** Application — [M @ N] (left associative). *)
Notation "M @ N" := (ne_app M N)
  (in custom ppl_named at level 20, left associativity,
   M custom ppl_named, N custom ppl_named).

(** Arithmetic. *)
Notation "M + N" := (ne_add M N)
  (in custom ppl_named at level 40, left associativity,
   N custom ppl_named at level 39).
Notation "M * N" := (ne_mul M N)
  (in custom ppl_named at level 30, left associativity,
   N custom ppl_named at level 29).

(** Lambda — [\"x" :: A => M] : explicit type annotation [A] on the
    binder.  We carry the type explicitly because [ne_lam] needs to
    extend the named context with a [(string, ppl_type)] pair.  We use
    [::] (not [:>]) for the type ascription since [:>] is reserved at
    constr level and would clash with the [x constr] parser. *)
Notation "'\' x ':::' A '=>' M" :=
  (ne_lam x%string (t1 := A) M)
  (in custom ppl_named at level 70, x constr at level 0,
   A constr at level 0,
   M custom ppl_named at level 60, right associativity).

(** Monadic let-binding — [let "x" := M in N] : desugars to [ne_bind]
    in the extended named context [(x, _) :: G].  The bound-type slot
    is inferred from [M]'s type [tprob t1]. *)
Notation "'let' x ':=' M 'in' N" :=
  (ne_bind x%string M N)
  (in custom ppl_named at level 80, x constr at level 0,
   M custom ppl_named at level 70,
   N custom ppl_named at level 80,
   right associativity).

(** ** Reproduced examples — named versions of [ex_random_constant]
       and [ex_random_linear]. *)

Section NamedExamples.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).

Variable (mu : fmeas R (ar_carrier Ar R_obj)).
Hypothesis Hmu : (cone_norm mu <= 1)%R.

Local Notation tR' := (tR R_obj).

(** [ex_named_random_constant] in the surface syntax:

    [[
       [ let "c" := Sample (mu, Hmu) in Ret (\"x" ::: tR => # "c") ]
    ]]

    Desugaring (one [ne_bind], one [ne_ret], one [ne_lam], one
    [ne_var']):

    [[
       ne_bind "c" (ne_sample mu Hmu)
         (ne_ret (ne_lam "x" (t1 := tR) (ne_var' "c" _)))
    ]]
    The [_] feeding into [ne_var'] is filled by canonical-structure
    search in the [find_nv "c" ?t] structure.  In the lambda body's
    context [("x", tR) :: ("c", tR) :: nil] canonical search picks
    [recurse_nv "x" tR _ (found_nv "c" tR nil)] (the head case
    [recurse_nv] strips [("x", tR)] using [infer ("x" =? "c" = false)],
    then [found_nv] matches [("c", tR)]).  Translation through
    [nv_to_hv] yields [hv_succ hv_zero] — exactly the De Bruijn index
    in [ex_rc_body]. *)
Definition ex_named_random_constant :
    @named_expr R Ar R_obj nil (tprob (tfun tR' tR')) :=
  [ let "c" := Sample (mu , Hmu) in Ret (\ "x" ::: tR' => # "c") ].

(** [ex_named_random_linear] in the surface syntax:

    [[
       [ let "m" := Sample (mu, Hmu) in
         let "b" := Sample (mu, Hmu) in
         Ret (\"x" ::: tR => # "m" * # "x" + # "b") ]
    ]]
    The lambda's bound context is [("x", tR) :: ("b", tR) :: ("m", tR) :: nil];
    canonical-structure resolution yields:
      [#"m"] = [recurse_nv "x" tR _ (recurse_nv "b" tR _ (found_nv "m" tR _))]
        (= De Bruijn [hv_succ (hv_succ hv_zero)]);
      [#"x"] = [found_nv "x" tR _] (= [hv_zero]);
      [#"b"] = [recurse_nv "x" tR _ (found_nv "b" tR _)]
        (= [hv_succ hv_zero])
    — exactly the indices in [ex_rl_body]. *)
Definition ex_named_random_linear :
    @named_expr R Ar R_obj nil (tprob (tfun tR' tR')) :=
  [ let "m" := Sample (mu , Hmu) in
    let "b" := Sample (mu , Hmu) in
    Ret (\ "x" ::: tR' => # "m" * # "x" + # "b") ].

(** ** Equivalence with the De Bruijn examples of [ppl.v] *)

Lemma ex_named_random_constant_E :
  nexp_to_dexp ex_named_random_constant = ex_random_constant mu Hmu.
Proof. by []. Qed.

Lemma ex_named_random_linear_E :
  nexp_to_dexp ex_named_random_linear = ex_random_linear mu Hmu.
Proof. by []. Qed.

End NamedExamples.

Arguments ex_named_random_constant {R Ar R_obj} mu Hmu.
Arguments ex_named_random_linear {R Ar R_obj} mu Hmu.
Arguments ex_named_random_constant_E {R Ar R_obj} mu Hmu.
Arguments ex_named_random_linear_E {R Ar R_obj} mu Hmu.
