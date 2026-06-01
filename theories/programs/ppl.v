(**md**************************************************************************)
(** * A higher-order probabilistic PPL — named-variable, direct-style,
       single-sort, with Kleisli-exponential semantics in [EM(!)]

    A higher-order probabilistic programming calculus, intrinsically
    typed and interpreted in the integrable-cones model.  The calculus
    shape follows the canonical QBS paper PPL
    (Heunen–Kammar–Staton–Yang, "A Convenient Category for Higher-Order
    Probability Theory"); the denotational semantics is the
    Eilenberg–Moore [EM(!)] / CBV chain of [theories/programs/cbv.v];
    the named-variable surface follows the Saito–Affeldt encoding
    (APLAS 2023 §5.1–§5.3, §6).

    ** Surface calculus — direct-style CBV **

    - a single inductive [named_expr Γ τ] indexed by an
      intrinsically-typed, MULTI-VARIABLE named context [Γ :
      named_ctx Ar = seq (string * ppl_type Ar)] and a type [τ :
      ppl_type];
    - DIRECT STYLE (Plotkin/Girard CBV): the source language never
      mentions the probability monad.  Function types are [tfun A B]
      (NOT [tprob (tfun ...)]); there is no [Ret], no [tprob], no
      [bind].  The monadic structure is INTERNALISED in [tyD (tfun A B)
      = !̃(U A ⊸ U(T B))] — the Kleisli exponential, with the [Tobj]
      on the codomain making every function call effectful — and in
      [eD], whose codomain is uniformly [Tobj (tyD τ)] for every
      expression;
    - direct-style application [ne_app f x : named_expr Γ B], NOT
      fine-grain Moggi: the user-facing calculus matches the
      Plotkin/Girard textbook CBV calculus;
    - a built-in measurable-space base [tbase X] for [X : ar_obj Ar], a
      unit type, binary products, and the higher-order arrow
      [tfun A B] = [!̃(U A ⊸ U(T B))] (the Kleisli exponential);
    - a [Custom Entry ppl_named] surface notation lets users write
      [\ "x" ::: tR => # "x"] etc. directly; the [# "x"] variable
      lookup is resolved by canonical-structure search ([find_nv]).

    ** Constructors **

    The full inductive [named_expr Γ τ] carries:
    - [ne_var v] — named projection from [Γ] (witness [named_var]);
    - [ne_tt] — the unit value;
    - [ne_pair] / [ne_fst] / [ne_snd] — binary products;
    - [ne_lam x M] / [ne_app] — higher-order lambda (with string
      binder [x]) / direct application;
    - [ne_let x M K] — direct-style CBV sequencer [let x = M in K]
      (carries a string binder);
    - [ne_sample mu Hmu] — sample from a unit-ball
      [mu : FMeas R_obj] (DIRECT STYLE: returns a [tR R_obj]
      expression — the monad is hidden in [eD]);
    - [ne_real r] — real literal [r : R] of type [tR];
    - [ne_score f Hf_meas Hf_ge0 Hf_le1 e] — TERM-LEVEL score by
      [f(r)] where [r] is the value of a [named_expr Γ tR] (the
      load-bearing constructor for genuine Bayesian inference; in
      direct style it returns a [tunit] expression);
    - [ne_add] / [ne_mul] — pointwise [+]/[×] on two [tR]-valued
      computations.
    - [ne_true] / [ne_false] — boolean constants of type [tbool],
      interpreted as the constant Kleisli arrows at the bool-cone
      Diracs [bool_dirac_true] / [bool_dirac_false] of
      [theories/cones/bool_cone.v].
    - [ne_bernoulli p Hp_ge0 Hp_le1] — sample from a Bernoulli
      distribution: the 2-point sub-probability [(p, 1-p)] on
      [bool_cone] (norm exactly [1]).

    ** Type and context interpretation **

    [[
       ⟦tunit⟧       = EM_term
       ⟦tbase X⟧     = FMeas_coalgebra X         (Theorem 9.7)
       ⟦tprod t1 t2⟧ = EM_prod ⟦t1⟧ ⟦t2⟧
       ⟦tfun  t1 t2⟧ = !̃(U⟦t1⟧ ⊸ U(T ⟦t2⟧))     (Kleisli exponential of [T])
    ]]
    Contexts are interpreted by [ctxD : seq (ppl_type Ar) -> Coalgebra Ar]
    on the De Bruijn skeleton [drop_names Γ : seq (ppl_type Ar)]
    obtained by forgetting the string identifiers; every expression
    denotes a Kleisli arrow [eD M : coalg_hom (ctxD (drop_names Γ))
    (Tobj (tyD τ))].  The monad lives uniformly in [eD] and in the
    [Tobj] on the codomain of [tyD (tfun A B)] — the source language
    NEVER exposes it.  See [cbv.v]'s header for the natural-bijection
    chain [Hom_EM(C×A, T B) ≅ Hom_EM(C, !̃(U A ⊸ U(T B)))]
    realising lambda + application.

    ** Infrastructure **

    The arithmetic and term-level-score constructors lean on the FMeas
    lax monoidal map of paper §9 ([theories/homs/fmeas_lax.v]):
    - [fmeas_lax X Y : FMeas X ⊗ FMeas Y ⊸ FMeas (X × Y)] is the Phase-A
      "tensored pair to joint measure" map, with Dirac identity
      [fmeas_lax_dirac : fmeas_lax (δ_a ⊗ δ_b) = δ_(a,b)] (used directly
      by [add_lift_dirac] / [mul_lift_dirac]);
    - the §6 follow-up [int_to_linhom_pres_path_in_cone] is what
      unblocked promoting paths into [linhom_car]s axiom-free, and is
      what [score_lift] re-uses to package the term-level score
      density as an [icones_hom (FMeas R_obj) (cone_one_car Ar)].

    The "Dirac/integration view" makes the reductions transparent:
    - [add_lift_dirac a b] / [mul_lift_dirac a b]: the arithmetic lift
      on point masses reduces to the arithmetic on the carriers;
    - [score_lift_dirac r]: the term-level score on a point mass
      reduces to [f r · one1] packaged as a [cone_one_car] element.

    Three end-to-end examples in surface syntax — [ex_random_constant]
    / [ex_random_linear] / [ex_bayes_linear] — live in
    [theories/programs/examples.v] together with their structural
    reduction lemmas. *)

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
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.cone.
Require Import Icones.cones.cone_cat.
Require Import Icones.cones.bool_cone.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.mcones.path.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.icone.
Require Import Icones.icones.examples_icone.
Require Import Icones.icones.icone_cat.
Require Import Icones.stable.scones_cat.
Require Import Icones.stable.scones_ccc.
Require Import Icones.homs.icones_iso.
Require Import Icones.homs.linhom.
Require Import Icones.homs.bilin.
Require Import Icones.homs.tensor.
Require Import Icones.homs.tensor_construct.
Require Import Icones.homs.smcc.
Require Import Icones.homs.exp_adjunction.
Require Import Icones.homs.bang.
Require Import Icones.homs.seely_defs.
Require Import Icones.homs.seely.
Require Import Icones.homs.tensor_hom_iso.
Require Import Icones.homs.bool_case_hom.
Require Import Icones.homs.coalgebra.
Require Import Icones.homs.fmeas_lax.
Require Import Icones.homs.em_cat.
Require Import Icones.homs.em_seely_comonoid.
Require Import Icones.homs.em_cartesian.
Require Import Icones.homs.cbv_adjunction.
Require Import Icones.homs.em_continuity.
Require Import Icones.homs.em_fix.
Require Import Icones.programs.cbv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Opaque tensor_mor tensor_assoc tensor_lunit tensor_runit tensor_braid
       ptensor tau Seely2.
Opaque dig der prom bang_fmap d_bang e_bang unit_cofree_str Coalg
       tens_cofree_str m_bang.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** Types — single-sort PPL types, parameterised by [Ar] *)

Section Types.
Variable (R : realType) (Ar : MeasSubcat R).

Inductive ppl_type : Type :=
  | tunit
  | tbool
  | tbase (X : ar_obj Ar)
  | tprod (t1 t2 : ppl_type)
  | tfun  (t1 t2 : ppl_type).

End Types.

Arguments ppl_type {R} Ar.
Arguments tunit {R Ar}.
Arguments tbool {R Ar}.
Arguments tbase {R Ar} X.
Arguments tprod {R Ar} t1 t2.
Arguments tfun {R Ar} t1 t2.

(** ** Contexts — named-variable surface, with the type-only De Bruijn
       skeleton kept as a PRIVATE projection for the semantic plumbing.

    The user-facing context is [named_ctx Ar = seq (string * ppl_type Ar)]:
    every binding slot carries a string identifier.  The PRIVATE projection
    [drop_names : named_ctx Ar -> seq (ppl_type Ar)] forgets the names; it
    is the carrier on which the categorical interpretation [ctxD] lives.

    [has_var (drop_names G) t] is the intrinsic De Bruijn index used by
    [var_lookup] / [eD]; it is built from a [named_var G t] witness via
    [named_var_to_has_var]. *)

Section Contexts.
Variable (R : realType) (Ar : MeasSubcat R).

Definition ppl_ctx : Type := list (ppl_type Ar).

(** [has_var G t]: a witness of "[t] is somewhere in [G]".  Intrinsic De
    Bruijn index: [hv_zero] points to the HEAD, [hv_succ] skips it.  Lives
    over the De Bruijn skeleton [seq (ppl_type Ar)]; the user-facing form
    is [named_var] below. *)
Inductive has_var : ppl_ctx -> ppl_type Ar -> Type :=
  | hv_zero (G : ppl_ctx) (t : ppl_type Ar) : has_var (t :: G) t
  | hv_succ (G : ppl_ctx) (t s : ppl_type Ar) :
      has_var G t -> has_var (s :: G) t.

(** Named contexts pair each binding slot with a string identifier. *)
Definition named_ctx : Type := list (string * ppl_type Ar).

Definition drop_names (G : named_ctx) : ppl_ctx :=
  map snd G.

(** [named_var G t]: a witness that some string identifier in [G] is
    bound to type [t].  Two constructors:
    - [nv_head x t G : named_var ((x, t) :: G) t] — the head case;
    - [nv_tail y s G t v : named_var ((y, s) :: G) t] — strip the head
      and recurse. *)
Inductive named_var : named_ctx -> ppl_type Ar -> Type :=
  | nv_head (x : string) (t : ppl_type Ar) (G : named_ctx) :
      named_var ((x, t) :: G) t
  | nv_tail (y : string) (s : ppl_type Ar) (G : named_ctx)
            (t : ppl_type Ar) (v : named_var G t) :
      named_var ((y, s) :: G) t.

(** Project a [named_var] witness to its De Bruijn index in the
    name-stripped context.  Structural recursion on [v]; this is the
    one-line bridge from named to skeletal contexts. *)
Fixpoint named_var_to_has_var (G : named_ctx) (t : ppl_type Ar)
    (v : named_var G t) {struct v} : has_var (drop_names G) t :=
  match v in named_var G0 t0 return has_var (drop_names G0) t0 with
  | nv_head _ t' G' => @hv_zero (drop_names G') t'
  | nv_tail _ sty G' t' v' =>
      @hv_succ (drop_names G') t' sty (named_var_to_has_var v')
  end.

End Contexts.

Arguments ppl_ctx {R} Ar.
Arguments has_var {R Ar} G t.
Arguments hv_zero {R Ar G t}.
Arguments hv_succ {R Ar G t s} v.
Arguments named_ctx {R} Ar.
Arguments drop_names {R Ar} G.
Arguments named_var {R Ar} G t.
Arguments nv_head {R Ar} x t G.
Arguments nv_tail {R Ar} y s G {t} v.
Arguments named_var_to_has_var {R Ar G t} v.

(** ** Distinguished real-object section — for [e_real] and [e_score]

    The PPL has a distinguished real-valued base type [tR] = [tbase R_obj]
    for a chosen [R_obj : ar_obj Ar] whose carrier IS the realType [R].  The
    propositional cast [R_carrier_eq] is the witness; [e_real]/[e_score]/
    [e_add]/[e_mul] use it to translate an [R]-literal to a value in
    [ar_carrier Ar R_obj]. *)

Section RealObj.
Variable (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.

(** Convert an [R] to an [ar_carrier Ar R_obj] via the propositional cast.
    Used by [e_real]/[e_score]. *)
Definition R_to_carrier (r : R) : ar_carrier Ar R_obj :=
  eq_rect_r (fun T : Type => T) r R_carrier_eq.

Definition tR : ppl_type Ar := tbase R_obj.

End RealObj.

Arguments R_to_carrier {R Ar R_obj} R_carrier_eq r.
Arguments tR {R Ar} R_obj.

(** ** Terms — single intrinsically-typed inductive [named_expr Γ τ]

    The user-facing surface syntax is NAMED: contexts carry string
    identifiers at every binding slot and variable lookup is by string.
    Direct-style application [ne_app : named_expr G (tfun t1 t2) ->
    named_expr G t1 -> named_expr G t2] (not Moggi fine-grain) matches
    the QBS-paper calculus shape; the Moggi monadic structure is
    uncovered by [eD] via the Kleisli-exponential chain.

    The constructors:
    - [ne_var] : project a value from the named context (via a
      [named_var] witness; the surface notation [#"x"] uses canonical
      structures to BUILD this witness from a string);
    - [ne_tt] : the unit value [()];
    - [ne_pair] / [ne_fst] / [ne_snd] : binary products;
    - [ne_lam] : higher-order lambda — carries a [string] for the
      binder name (body is a [named_expr] in the extended named
      context — IT IS NOT marked as a computation; the Moggi/Kleisli
      structure is in the SEMANTICS, not the syntax);
    - [ne_app] : DIRECT application;
    - [ne_let] : direct-style CBV sequencer [let x = M in K] — carries
      a [string] for the bound name (this is the Plotkin/Girard CBV
      let; semantically its interpretation is the extended-context
      Kleisli bind [kbind_ext], identical to the old monadic-style
      [ne_bind] minus the type-level [tprob] markers that are now
      gone);
    - [ne_sample] : sample from a fixed measure
      [µ : FMeas R_obj] in the unit ball (the constructor carries the
      cone-norm bound [Hmu : ‖µ‖ ≤ 1] that the
      [linhom_icones]-wrapping needs; DIRECT STYLE: returns a [tR]
      expression);
    - [ne_real] : real literal [r : R] of type [tR] (the Dirac at [r]
      has unit norm — no bound proof needed);
    - [ne_score] : TERM-LEVEL score by [f r : R] where [r] is the
      value of a [named_expr G tR]; the meta-parameter [f : R → R] is
      measurable and pointwise in [[0,1]] (the bound is needed by
      the cone-norm / unit-ball discipline of [linhom_icones]).  This
      is the constructor that makes Bayesian-style observation
      actually possible: the score factor can depend on a bound
      variable through [e]; DIRECT STYLE: returns a [tunit] expression;
    - [ne_add] : pointwise sum of two [tR]-valued computations
      (interpretation: lax-monoidal pairing of the two pushforwards
      followed by [FMeas]-functorial action of measurable [+]);
    - [ne_mul] : pointwise product, analogous to [ne_add]. *)
Section Syntax.
Variable (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.

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
  (* OCaml-style [let rec]: the body has access to the recursive
     function via a fresh name [s : tfun t1 t2] in the context.  Only
     function types are allowed (the user-authorised restriction:
     "It is normal to restrict recursion to function, and this is also
     the choice of ocaml where let rec is thunked.") *)
  | ne_fix   (G : named_ctx Ar) (s : string) (t1 t2 : T) :
      named_expr ((s, tfun t1 t2) :: G) (tfun t1 t2) -> named_expr G (tfun t1 t2)
  | ne_app   (G : named_ctx Ar) (t1 t2 : T) :
      named_expr G (tfun t1 t2) -> named_expr G t1 -> named_expr G t2
  | ne_let   (G : named_ctx Ar) (x : string) (t1 t2 : T) :
      named_expr G t1 ->
      named_expr ((x, t1) :: G) t2 ->
      named_expr G t2
  | ne_sample (G : named_ctx Ar)
              (mu : fmeas R (ar_carrier Ar R_obj))
              (Hmu : (cone_norm mu <= 1)%R) :
      named_expr G tR'
  | ne_real  (G : named_ctx Ar) (r : R) : named_expr G tR'
  | ne_score (G : named_ctx Ar)
             (f : R -> R)
             (Hf_meas : measurable_fun [set: R] f)
             (Hf_ge0 : forall r : R, (0 <= f r)%R)
             (Hf_le1 : forall r : R, (f r <= 1)%R)
             (e : named_expr G tR') : named_expr G tunit
  | ne_add   (G : named_ctx Ar) :
      named_expr G tR' -> named_expr G tR' -> named_expr G tR'
  | ne_mul   (G : named_ctx Ar) :
      named_expr G tR' -> named_expr G tR' -> named_expr G tR'
  (* Boolean constants [True], [False] of type [tbool]. *)
  | ne_true  (G : named_ctx Ar) : named_expr G tbool
  | ne_false (G : named_ctx Ar) : named_expr G tbool
  (* [Bernoulli p Hp_ge0 Hp_le1] : sample from the 2-point sub-probability
     distribution [(p, 1-p)] on [bool_cone].  Both branches' weights are
     witnessed non-negative by [Hp_ge0] and [Hp_le1], and the total mass
     is exactly [1] (norm-1). *)
  | ne_bernoulli (G : named_ctx Ar) (p : R)
                 (Hp_ge0 : (0 <= p)%R) (Hp_le1 : (p <= 1)%R) :
      named_expr G tbool
  (* [if e then M else N] — boolean elimination.  [e] is a [tbool]
     expression (semantically a sub-probability distribution on [bool]),
     and [M, N : t] are the two branches.  The denotation [eD] uses
     [kbind_ext] with the [case_em] combinator. *)
  | ne_if (G : named_ctx Ar) (t : T) :
      named_expr G tbool ->
      named_expr G t ->
      named_expr G t ->
      named_expr G t.

End Syntax.

Arguments named_expr {R Ar R_obj} G t.
Arguments ne_var {R Ar R_obj G t} v.
Arguments ne_tt {R Ar R_obj G}.
Arguments ne_fst {R Ar R_obj G t1 t2} M.
Arguments ne_snd {R Ar R_obj G t1 t2} M.
Arguments ne_sample {R Ar R_obj G} mu Hmu.
Arguments ne_real {R Ar R_obj G} r.
(** Bidirectionality hints ([&]) on the binding-site / context-shared
    constructors: tell Coq's elaborator to resolve the outer index [G]
    (and the binder slot's type [t1] where applicable) FIRST, then
    propagate into the sub-expressions.  Without these hints the
    [find_nv] canonical-structure lookup at [#"x"] sites is fired with
    an open context metavariable and picks the wrong instance — see
    the [find_nv] docstring.  This is exactly the Saito–Affeldt
    [Arguments exp_letin {g} & {t1 t2}] pattern (APLAS 2023 §5.1). *)
Arguments ne_pair {R Ar R_obj G t1 t2} & M N.
Arguments ne_fst {R Ar R_obj G t1 t2} & M.
Arguments ne_snd {R Ar R_obj G t1 t2} & M.
Arguments ne_lam {R Ar R_obj G} x & {t1 t2} M.
Arguments ne_fix {R Ar R_obj G} s & {t1 t2} M.
Arguments ne_app {R Ar R_obj G t1 t2} & F X.
Arguments ne_let {R Ar R_obj G} x & {t1 t2} M K.
Arguments ne_score {R Ar R_obj G} & f Hf_meas Hf_ge0 Hf_le1 e.
Arguments ne_add {R Ar R_obj G} & M N.
Arguments ne_mul {R Ar R_obj G} & M N.
Arguments ne_true {R Ar R_obj G}.
Arguments ne_false {R Ar R_obj G}.
Arguments ne_bernoulli {R Ar R_obj G} p Hp_ge0 Hp_le1.
(** Bidirectionality on [ne_if]: resolve [G] and [t] FIRST (from the
    scrutinee and the branches' types), then propagate into the
    sub-expressions.  Same pattern as [ne_let] / [ne_app]. *)
Arguments ne_if {R Ar R_obj G} & t e M N.

(** ** Type and context interpretation [tyD] / [ctxD]

    Every type denotes a coalgebra of [EM(!)]:
    [[
       ⟦tunit⟧       = EM_term
       ⟦tbase X⟧     = FMeas_coalgebra X         (Theorem 9.7)
       ⟦tprod t1 t2⟧ = EM_prod ⟦t1⟧ ⟦t2⟧
       ⟦tfun  t1 t2⟧ = !̃(U⟦t1⟧ ⊸ U(T ⟦t2⟧))     (Kleisli exponential of [T])
    ]]
    DIRECT STYLE: the source language has no [tprob] marker; every
    expression's denotation is uniformly a Kleisli arrow [⟦expr G t⟧ ∈
    coalg_hom (ctxD G) (Tobj (tyD t))], and the monadic structure
    lives uniformly in [eD] and in the [Tobj] on the codomain of [tyD
    (tfun A B)].

    Contexts are interpreted with the HEAD of the list on the RIGHT:
    [[
       ⟦[]⟧      = EM_term
       ⟦t :: G⟧  = EM_prod ⟦G⟧ ⟦t⟧.
    ]]
    With this orientation, the variable [hv_zero] (= the head) is the
    SECOND component of the product (read by [em_proj2]), and [hv_succ]
    strips off the head by reading the FIRST component (via [em_proj1]) and
    recursing.  The orientation matches the [lam_coalg] / [app_kleisli]
    helpers below: the body of [e_lam : expr (t1 :: G) t2 -> expr G (tfun
    t1 t2)] is interpreted in [⟦t1 :: G⟧ = EM_prod ⟦G⟧ ⟦t1⟧] — exactly the
    domain of the Kleisli-exponential curry of [cbv.v]. *)
Section TypeInterp.
Variables (R : realType) (Ar : MeasSubcat R).

Fixpoint tyD (t : ppl_type Ar) : Coalgebra Ar :=
  match t with
  | tunit => EM_term
  (* [tbool] is interpreted as the cofree coalgebra over the 2-point
     sub-probability cone [bool_cone_car Ar].  We use [bang_cofree]
     (the canonical, uniformly available coalgebra structure on any
     iconeType) rather than a custom structure map, mirroring [tfun]
     and side-stepping the need to build a measure-space-style
     coalgebra structure on the 2-point cone. *)
  | tbool => bang_cofree (bool_cone_car Ar)
  | tbase X => FMeas_coalgebra X
  | tprod s1 s2 => EM_prod (tyD s1) (tyD s2)
  (* Direct-style CBV: the function type is the Kleisli exponential
     [!̃(U(⟦A⟧) ⊸ U(T ⟦B⟧))].  The [Tobj] on the codomain is what makes
     EVERY function call effectful at the level of the semantic model;
     the user-facing source language never mentions the monad ([tprob]
     is gone), and the monadic structure is uniformly carried by [eD]
     and by the [Tobj] in the linhom-codomain. *)
  | tfun A B => bang_cofree (linhom_car Ar (coalg_obj (tyD A))
                                          (coalg_obj (Tobj (tyD B))))
  end.

Fixpoint ctxD (G : ppl_ctx Ar) : Coalgebra Ar :=
  match G with
  | nil => EM_term
  | t :: G' => EM_prod (ctxD G') (tyD t)
  end.

End TypeInterp.

Arguments tyD {R Ar} t.
Arguments ctxD {R Ar} G.

(** ** Kleisli infrastructure on top of [cbv.v]

    The CBV monad [T], its unit [tunit_eta], Kleisli composition [kcomp] /
    extension [kbind], the three monad laws ([kcomp_etaR]/[kcomp_etaL]/
    [kcomp_A]) and the slick engine [adj_phi_kcomp] are inherited from
    [theories/programs/cbv.v].  This section adds the genuinely-new
    higher-order / strength helpers that the multi-variable direct-style
    [expr] interpretation needs.

    The first is the (left) tensor strength of [T]
    [[
       T_str_l : EM_prod G (T A) -> T (EM_prod G A)
    ]]
    obtained as [bang_m ∘ (tunit_eta G ⊗ id_{T A})]: pre-compose the lax
    binary comparison [bang_m : T P × T Q → T (P × Q)] with
    [η_G ⊗ id : G × T A → T G × T A].  This is the standard Moggi monadic
    strength for a commutative monoidal monad.

    The second is the "extended-context Kleisli bind"
    [[
       kbind_ext : (coalg_hom (EM_prod G A) (Tobj B)) ->
                   (coalg_hom G (Tobj A)) ->
                   (coalg_hom G (Tobj B))
    ]]
    used by [e_bind].  It is [kcomp k (T_str_l ∘ ⟨id,m⟩)]: pair [m] with
    the identity to keep the environment, strength to push the [T] outside
    the [G ⊗ —], then [kcomp] with the continuation [k]. *)

Section KleisliExt.
Variables (R : realType) (Ar : MeasSubcat R).

(** The left strength [τ : G ⊗ T A → T (G ⊗ A)].

    Concretely [τ = bang_m (U G) (U A) ∘ (η_G ⊗ id_{T A})].  Since [T A =
    bang_cofree (U A)], the right factor is identity (its target equals
    its source); the left factor is the unit [η_G : G → !̃(U G) = T G] of
    the comonoidal adjunction; and [bang_m] is the commutative comonoid
    "merge" of [cbv_adjunction.v]. *)
Definition T_str_l (G A : Coalgebra Ar) :
    coalg_hom (EM_prod G (Tobj A)) (Tobj (EM_prod G A)) :=
  coalg_comp (bang_m (coalg_obj G) (coalg_obj A))
    (em_pair (coalg_comp (tunit_eta G) (em_proj1 G (Tobj A)))
             (em_proj2 G (Tobj A))).

(** "Extended-context Kleisli bind": given a Kleisli arrow [m : G ⇝ A]
    and a continuation [k : G × A ⇝ B] (with the bound variable on the
    RIGHT — matching the context convention [ctxD (t :: G) = EM_prod G (tyD
    t)]), produce a Kleisli arrow [G ⇝ B].

    [kbind_ext k m] is [kcomp k (τ ∘ ⟨id_G, m⟩)]: pair [m] with the
    identity, apply the strength, kbind with [k]. *)
Definition kbind_ext (G A B : Coalgebra Ar)
    (k : coalg_hom (EM_prod G A) (Tobj B))
    (m : coalg_hom G (Tobj A)) :
    coalg_hom G (Tobj B) :=
  kcomp k (coalg_comp (T_str_l G A) (em_pair (coalg_id G) m)).

End KleisliExt.

Arguments T_str_l {R Ar} G A.
Arguments kbind_ext {R Ar G A B} k m.

(** ** Monad-law toolkit for [kbind_ext]

    The equational laws downstream PPL identity proofs need.  All are
    proven axiom-free; the only assumptions are the boolp axioms
    inherited from [mathcomp-analysis] (LEM, propext, FunExt).

    Helpers (pairing naturality):
    - [em_pair_mor_natR] : [tensor_mor f g ∘ ⟨a, b⟩ = ⟨f∘a, g∘b⟩]
      (pure naturality of pairing in the codomain factors, no side
      condition).
    - [em_pair_mor_natL] : [⟨p, q⟩ ∘ h = ⟨p∘h, q∘h⟩] provided [h] is a
      coalgebra morphism (uses [coalg_mor_d]).

    Laws:
    - [kbind_ext_etaR] (Law 1, right unit) : binding the canonical
      [η ∘ π₂] is the identity (the [let x = m in return x] law).
    - [kbind_ext_terminal_source] (Law 3, EM_term source collapse) :
      when the source is [EM_term], kbind_ext reduces to plain Kleisli
      composition via the canonical iso [EM_prod EM_term A ≅ A].
    - [adj_phi_kbind_ext] : the slick "Kleisli-pairing" form
      [adj_phi (kbind_ext k m) = adj_phi k ∘ ⟨id, adj_phi m⟩].

    NOT INCLUDED — Law 2 (full associativity-with-substitution): in the
    shape proposed by the prompt
    [kbind_ext h (kbind_ext k m) = kbind_ext (kbind_ext shifted_h k) m]
    the proof reduces (via [adj_phi_kbind_ext]) to an icones-level
    identity that requires either the cartesian "pair-of-projections is
    the identity" rule
    [em_pair_mor(em_proj1_mor, em_proj2_mor) = id_{EM_prod P Q}] or a
    "tensor_mor / coalg_d swap" identity that is NOT available
    axiom-free in the current cones library (it requires uniqueness of
    the cartesian product, which only holds via the [U] functor's
    faithfulness and only for COALG morphisms — [adj_phi k]/[adj_phi m]
    are NOT coalg morphisms in general).  Recording this as a precise
    gap; downstream Lemma 2 callers can either supply a stronger
    helper or work around. *)

Section KbindExtLaws.
Variables (R : realType) (Ar : MeasSubcat R).

(** *** Helper — naturality of [em_pair_mor] in its output factors *)

(** Right-naturality: [tensor_mor f g ∘ ⟨a,b⟩ = ⟨f∘a, g∘b⟩].  Pure
    tensor / pairing identity, no side condition. *)
Lemma em_pair_mor_natR (Z P Q P' Q' : Coalgebra Ar)
    (a : icones_hom Ar (coalg_obj Z) (coalg_obj P))
    (b : icones_hom Ar (coalg_obj Z) (coalg_obj Q))
    (f : icones_hom Ar (coalg_obj P) (coalg_obj P'))
    (g : icones_hom Ar (coalg_obj Q) (coalg_obj Q')) :
  icones_comp (tensor_mor f g) (em_pair_mor a b)
  = em_pair_mor (icones_comp f a) (icones_comp g b).
Proof.
rewrite /em_pair_mor icones_compA.
by rewrite (tensor_mor_comp f a g b).
Qed.

(** Left-naturality: [⟨p,q⟩ ∘ h = ⟨p∘h, q∘h⟩] provided [h] is a coalgebra
    morphism — uses the comonoid-morphism property of [coalg_d]
    ([coalg_mor_d]). *)
Lemma em_pair_mor_natL (Z Y P Q : Coalgebra Ar)
    (h : icones_hom Ar (coalg_obj Z) (coalg_obj Y))
    (p : icones_hom Ar (coalg_obj Y) (coalg_obj P))
    (q : icones_hom Ar (coalg_obj Y) (coalg_obj Q))
    (Hh : is_coalg_mor Z Y h) :
  icones_comp (@em_pair_mor R Ar Y P Q p q) h
  = @em_pair_mor R Ar Z P Q (icones_comp p h) (icones_comp q h).
Proof.
rewrite /em_pair_mor -icones_compA (coalg_mor_d _ Hh).
rewrite icones_compA (tensor_mor_comp p h q h).
by rewrite icones_compA.
Qed.

(** *** Law 1 — Right-unit of [kbind_ext] on the canonical [η ∘ π₂] *)

(** Binding by the canonical "return the bound variable" continuation
    [η_A ∘ π₂_{G,A}] is the identity: the [let x = m in return x] law.
    Proof: route through [adj_phi]; reduce [adj_phi (kbind_ext ..)] step
    by step using [adj_phi_kcomp], [adj_phi_natL], [adj_triangleL] +
    [adj_counit_monoidal2] (= [der ∘ m_bang = der ⊗ der]), then absorb
    the projections via [em_proj1_pair] / [em_proj2_pair]. *)
Lemma kbind_ext_etaR (G A : Coalgebra Ar) (m : coalg_hom G (Tobj A)) :
  kbind_ext (coalg_comp (tunit_eta A) (em_proj2 G A)) m = m.
Proof.
apply: adj_phi_inj.
rewrite /kbind_ext adj_phi_kcomp.
rewrite (adj_phi_natL (tunit_eta A) (em_proj2 G A)).
rewrite adj_triangleL icones_compIl.
rewrite (adj_phi_natL (T_str_l G A) (em_pair (coalg_id G) m)).
rewrite /T_str_l.
rewrite (adj_phi_natL (bang_m (coalg_obj G) (coalg_obj A))).
rewrite /adj_phi /U_mor /=.
rewrite (adj_counit_monoidal2 (coalg_obj G) (coalg_obj A)).
rewrite (em_pair_mor_natR (Z := EM_prod G (Tobj A))
                          (P := Tobj G) (Q := Tobj A)
                          (P' := G) (Q' := A)
           _ _ (adj_counit (coalg_obj G)) (adj_counit (coalg_obj A))).
rewrite (icones_compA (adj_counit (coalg_obj G))).
rewrite /adj_counit (coalg_counit G) icones_compIl.
have Hpair : is_coalg_mor G (EM_prod G (Tobj A))
    (em_pair_mor (icones_id Ar (coalg_obj G)) (ch_mor m))
  by apply: em_pair_is_mor;
     [exact: (ch_is_mor (coalg_id G)) | exact: ch_is_mor m].
rewrite (@em_pair_mor_natL G (EM_prod G (Tobj A)) G A
           (em_pair_mor (icones_id Ar (coalg_obj G)) (ch_mor m))
           (em_proj1_mor G (Tobj A))
           (icones_comp (der (coalg_obj A)) (em_proj2_mor G (Tobj A)))
           Hpair).
have Hm := ch_is_mor m.
have Hid : is_coalg_mor G G (icones_id Ar (coalg_obj G))
  by exact: (ch_is_mor (coalg_id G)).
rewrite (em_proj1_pair Hm).
rewrite -(icones_compA (der (coalg_obj A)) (em_proj2_mor G (Tobj A))).
rewrite (em_proj2_pair Hid).
by rewrite (em_proj2_pair Hid).
Qed.

End KbindExtLaws.

Arguments em_pair_mor_natR {R Ar Z P Q P' Q'} a b f g.
Arguments em_pair_mor_natL {R Ar Z Y P Q h} p q Hh.
Arguments kbind_ext_etaR {R Ar G A} m.

(** ** [adj_phi] of [kbind_ext] — the clean "Kleisli pairing"

    The reduction [adj_phi (kbind_ext k m) = adj_phi k ∘ ⟨id, adj_phi m⟩]
    is the standard "monad-on-EM(!)-as-Kleisli-pairing" identity.  It is
    the slick engine for the rest of the monad-law toolkit: every
    [kbind_ext] equation reduces, via [adj_phi_inj], to an [icones_hom]
    equation involving the "id ⊗ —" pairing and the postcomposition by
    [adj_phi k]/[adj_phi m]. *)
Section AdjPhiKbindExt.
Variables (R : realType) (Ar : MeasSubcat R).

(** [adj_phi (T_str_l G A ∘ ⟨id_G, m⟩)] is the Kleisli pairing
    [em_pair_mor (id_{U G}, adj_phi m)].  This is the central "strength
    reduces to pairing under [adj_phi]" identity.  Proof: same chain as
    in [kbind_ext_etaR] — [adj_phi_natL] / [adj_counit_monoidal2] /
    [em_pair_mor_natR] / [coalg_counit] / [em_pair_mor_natL] /
    [em_proj1_pair] / [em_proj2_pair]. *)
Lemma adj_phi_T_str_l_em_pair (G A : Coalgebra Ar) (m : coalg_hom G (Tobj A)) :
  adj_phi (coalg_comp (T_str_l G A) (em_pair (coalg_id G) m))
  = em_pair_mor (icones_id Ar (coalg_obj G)) (adj_phi m).
Proof.
rewrite (adj_phi_natL (T_str_l G A) (em_pair (coalg_id G) m)) /T_str_l.
rewrite (adj_phi_natL (bang_m (coalg_obj G) (coalg_obj A))).
rewrite /adj_phi /U_mor /=.
rewrite (adj_counit_monoidal2 (coalg_obj G) (coalg_obj A)).
rewrite (em_pair_mor_natR (Z := EM_prod G (Tobj A))
                          (P := Tobj G) (Q := Tobj A)
                          (P' := G) (Q' := A)
           _ _ (adj_counit (coalg_obj G)) (adj_counit (coalg_obj A))).
rewrite (icones_compA (adj_counit (coalg_obj G))).
rewrite /adj_counit (coalg_counit G) icones_compIl.
have Hpair : is_coalg_mor G (EM_prod G (Tobj A))
    (em_pair_mor (icones_id Ar (coalg_obj G)) (ch_mor m))
  by apply: em_pair_is_mor;
     [exact: (ch_is_mor (coalg_id G)) | exact: ch_is_mor m].
rewrite (em_pair_mor_natL (Z := G) (Y := EM_prod G (Tobj A))
                          (P := G) (Q := A)
           (h := em_pair_mor (icones_id Ar (coalg_obj G)) (ch_mor m))
           (em_proj1_mor G (Tobj A))
           (icones_comp (der (coalg_obj A)) (em_proj2_mor G (Tobj A)))
           Hpair).
have Hm := ch_is_mor m.
have Hid : is_coalg_mor G G (icones_id Ar (coalg_obj G))
  by exact: (ch_is_mor (coalg_id G)).
rewrite (em_proj1_pair Hm).
rewrite -(icones_compA (der (coalg_obj A)) (em_proj2_mor G (Tobj A))).
by rewrite (em_proj2_pair Hid).
Qed.

(** [adj_phi (kbind_ext k m) = adj_phi k ∘ ⟨id, adj_phi m⟩]. *)
Lemma adj_phi_kbind_ext (G A B : Coalgebra Ar)
    (k : coalg_hom (EM_prod G A) (Tobj B)) (m : coalg_hom G (Tobj A)) :
  adj_phi (kbind_ext k m)
  = icones_comp (adj_phi k)
                (em_pair_mor (icones_id Ar (coalg_obj G)) (adj_phi m)).
Proof.
by rewrite /kbind_ext adj_phi_kcomp adj_phi_T_str_l_em_pair.
Qed.

End AdjPhiKbindExt.

Arguments adj_phi_T_str_l_em_pair {R Ar G A} m.
Arguments adj_phi_kbind_ext {R Ar G A B} k m.

(** ** Law 3 — Terminal-source collapse of [kbind_ext]

    When the source is the terminal coalgebra [EM_term], [kbind_ext]
    reduces to plain Kleisli composition [kcomp] through the canonical
    iso [EM_prod EM_term A ≅ A] (whose inverse is
    [em_pair (em_term_mor A) (coalg_id A)] : A → EM_prod EM_term A]).

    Proof chain (all via [adj_phi_inj]):
    1. [adj_phi (LHS) = adj_phi k ∘ ⟨id_{cone_one}, adj_phi m⟩]    [adj_phi_kbind_ext]
    2. [adj_phi (RHS) = adj_phi k ∘ ⟨e_A, id_{cA}⟩ ∘ adj_phi m]    [adj_phi_kcomp + adj_phi_natL]
    3. Suffices: [⟨id_{cone_one}, adj_phi m⟩ = ⟨e_A, id_{cA}⟩ ∘ adj_phi m]
    4. RHS: [⟨e_A, id⟩ = iso_bwd (tensor_lunit cA)]                 [emc_counitL]
    5. LHS: [⟨id, X⟩ = tensor_mor(id, X) ∘ coalg_d EM_term]
       [= tensor_mor(id, X) ∘ iso_bwd (tensor_lunit cone_one)]      [coalg_d_EM_term]
       [= iso_bwd (tensor_lunit cA) ∘ X]                             [tensor_lunit_nat_bwd]
    6. = RHS. *)
Section Law3Helpers.
Variables (R : realType) (Ar : MeasSubcat R).

(** [⟨e_P, id_{cP}⟩ = tensor_lunit^{-1}_{cP}].  Standard cartesian fact:
    pair-of-(counit, identity) is the left-unitor inverse. *)
Lemma em_pair_mor_coalg_e_lunit (P : Coalgebra Ar) :
  @em_pair_mor R Ar P EM_term P (coalg_e P) (icones_id Ar (coalg_obj P))
  = iso_bwd (tensor_lunit (coalg_obj P)).
Proof.
have HemL := @emc_counitL R Ar P (EMComon_all P).
rewrite /em_pair_mor.
have step :
    icones_comp (iso_bwd (tensor_lunit (coalg_obj P)))
      (icones_comp (iso_fwd (tensor_lunit (coalg_obj P)))
         (icones_comp
            (tensor_mor (coalg_e P) (icones_id Ar (coalg_obj P)))
            (coalg_d P)))
  = icones_comp (iso_bwd (tensor_lunit (coalg_obj P)))
                (icones_id Ar (coalg_obj P))
  by rewrite HemL.
rewrite icones_compA (iso_fwdK (tensor_lunit (coalg_obj P))) in step.
rewrite icones_compIl in step.
by rewrite icones_compIr in step; rewrite step.
Qed.

(** [coalg_d EM_term = tensor_lunit^{-1}_{cone_one}]. *)
Lemma coalg_d_EM_term :
  coalg_d (EM_term : Coalgebra Ar)
  = iso_bwd (tensor_lunit (cone_one_car Ar)).
Proof.
have H : @em_pair_mor R Ar EM_term EM_term EM_term
            (coalg_e EM_term) (icones_id Ar (cone_one_car Ar))
       = iso_bwd (tensor_lunit (cone_one_car Ar))
  by apply: (em_pair_mor_coalg_e_lunit EM_term).
rewrite -H.
by rewrite /em_pair_mor coalg_e_term tensor_mor_id icones_compIl.
Qed.

(** Backward form of [tensor_lunit_nat]: [(id ⊗ f) ∘ tlu^{-1} = tlu^{-1} ∘ f]. *)
Lemma tensor_lunit_nat_bwd (A A' : ICone.type Ar) (f : icones_hom Ar A A') :
  icones_comp (tensor_mor (icones_id Ar (cone_one_car Ar)) f)
              (iso_bwd (tensor_lunit A))
  = icones_comp (iso_bwd (tensor_lunit A')) f.
Proof.
have Hnat := tensor_lunit_nat f.
move/(congr1 (fun x => icones_comp (iso_bwd (tensor_lunit A')) x)) : Hnat.
rewrite icones_compA (iso_fwdK (tensor_lunit A')) icones_compIl => Hnat'.
move/(congr1 (fun x => icones_comp x (iso_bwd (tensor_lunit A)))) : Hnat'.
move=> H; rewrite H.
rewrite -2!icones_compA (iso_bwdK (tensor_lunit A)).
by rewrite icones_compIr.
Qed.

(** *** Law 3 — terminal-source collapse *)
Lemma kbind_ext_terminal_source (A B : Coalgebra Ar)
    (k : coalg_hom (EM_prod EM_term A) (Tobj B))
    (m : coalg_hom EM_term (Tobj A)) :
  kbind_ext k m
  = kcomp (coalg_comp k (em_pair (em_term_mor A) (coalg_id A))) m.
Proof.
apply: adj_phi_inj.
rewrite adj_phi_kbind_ext adj_phi_kcomp.
rewrite (adj_phi_natL k (em_pair (em_term_mor A) (coalg_id A))).
rewrite /U_mor /=.
rewrite -icones_compA.
congr (icones_comp _ _).
rewrite (em_pair_mor_coalg_e_lunit A).
rewrite /em_pair_mor coalg_d_EM_term.
by rewrite tensor_lunit_nat_bwd.
Qed.

End Law3Helpers.

Arguments em_pair_mor_coalg_e_lunit {R Ar} P.
Arguments coalg_d_EM_term {R Ar}.
Arguments tensor_lunit_nat_bwd {R Ar} A A' f.
Arguments kbind_ext_terminal_source {R Ar A B} k m.

(** ** Variable lookup [var_lookup]

    Given a De Bruijn witness [v : has_var G t], project the value of type
    [tyD t] out of the context [ctxD G].  By recursion on [v]: [hv_zero]
    reads the SECOND component (the head), [hv_succ] reads the FIRST and
    recurses. *)
Section VarLookup.
Variables (R : realType) (Ar : MeasSubcat R).

Fixpoint var_lookup (G : ppl_ctx Ar) (t : ppl_type Ar)
    (v : has_var G t) {struct v} :
    coalg_hom (ctxD G) (tyD t) :=
  match v in has_var G0 t0 return coalg_hom (ctxD G0) (tyD t0) with
  | hv_zero G' t' => em_proj2 (ctxD G') (tyD t')
  | hv_succ G' t' s v' =>
      coalg_comp (var_lookup v') (em_proj1 (ctxD G') (tyD s))
  end.

End VarLookup.

Arguments var_lookup {R Ar G t} v.

(** ** Lambda and application via the Kleisli-exponential chain

    The two helpers [lam_coalg'] and [app_kleisli'] reuse [lam_coalg] /
    [app_kleisli] of [theories/programs/ppl.v]'s former higher-order
    package — except that here [lam_coalg]/[app_kleisli] are imported from
    [cbv.v]'s siblings... no, [cbv.v] does NOT export them.  We inline
    them here under the same names from the previous higher-order ppl. *)

Section LamApp.
Variables (R : realType) (Ar : MeasSubcat R).

(** *** Lambda — LEFT to RIGHT through the Kleisli-exponential chain.

    Direct-style: a lambda body is interpreted as a Kleisli arrow
    [MB : coalg_hom (EM_prod G A) (Tobj B)].  The result is a VALUE in
    [tyD (tfun A B) = bang_cofree (linhom A (U(T B)))] obtained by
    [adj_psi ∘ tensor_curry ∘ ch_mor].  Note: with [U(Tobj B) =
    coalg_obj (Tobj B) = Bang(U B)] (definitional), [ch_mor MB] is
    already an [icones_hom (U(G) ⊗ U(A)) (U(Tobj B))], so we
    [tensor_curry] then [adj_psi] to land in the [bang_cofree] envelope. *)
Definition lam_under (G A B : Coalgebra Ar)
    (MB : coalg_hom (EM_prod G A) (Tobj B)) :
    icones_hom Ar (coalg_obj G)
      (linhom_car Ar (coalg_obj A) (coalg_obj (Tobj B))) :=
  tensor_curry (ch_mor MB).

Definition lam_coalg (G A B : Coalgebra Ar)
    (MB : coalg_hom (EM_prod G A) (Tobj B)) :
    coalg_hom G (bang_cofree (linhom_car Ar (coalg_obj A)
                                            (coalg_obj (Tobj B)))) :=
  adj_psi (lam_under MB).

(** *** Application — RIGHT to LEFT through the chain.

    Given a function value [VF : G → bang_cofree (linhom A (U(T B)))]
    and an argument value [VA : G → A], fire the closure.  The
    [tensor_uncurry (adj_phi VF)] reads as [icones_hom (U G ⊗ U A)
    (U(T B))]; we then [adj_psi] to land in [coalg_hom G (T (T B))],
    and finally [tmul] collapses the double-monad.  This is the
    standard "compute closure then call" pattern; the [tmul] is the
    monad-multiplication that makes the call effectful. *)
Definition app_under (G A B : Coalgebra Ar)
    (VF : coalg_hom G
            (bang_cofree (linhom_car Ar (coalg_obj A) (coalg_obj (Tobj B)))))
    (VA : coalg_hom G A) :
    icones_hom Ar (coalg_obj G) (coalg_obj (Tobj B)) :=
  icones_comp (tensor_uncurry (adj_phi VF))
    (icones_comp (tensor_mor (icones_id Ar (coalg_obj G)) (ch_mor VA))
                 (coalg_d G)).

Definition app_kleisli (G A B : Coalgebra Ar)
    (VF : coalg_hom G
            (bang_cofree (linhom_car Ar (coalg_obj A) (coalg_obj (Tobj B)))))
    (VA : coalg_hom G A) :
    coalg_hom G (Tobj B) :=
  coalg_comp (tmul B) (adj_psi (app_under VF VA)).

(** *** [app_pair] — the Kleisli "evaluate" arrow on a value pair

    Given a pair value [(f, a) : EM_prod (tfun A B) A], project the
    components and apply [app_kleisli].  This is the continuation used
    to interpret direct-style application as monadic application after
    both [f] and [a] have been EVALUATED to values. *)
Definition app_pair (A B : Coalgebra Ar) :
    coalg_hom (EM_prod (bang_cofree (linhom_car Ar (coalg_obj A)
                                                  (coalg_obj (Tobj B)))) A)
              (Tobj B) :=
  app_kleisli
    (em_proj1 (bang_cofree (linhom_car Ar (coalg_obj A) (coalg_obj (Tobj B)))) A)
    (em_proj2 (bang_cofree (linhom_car Ar (coalg_obj A) (coalg_obj (Tobj B)))) A).

(** *** [app_kleisli_lam] — the higher-order CBV β-law at the cones level

    The load-bearing meta-theorem for the PPL: applying the lambda value
    [lam_coalg M] (= [adj_psi ∘ tensor_curry ∘ ch_mor M]) to an
    argument value [V : coalg_hom G A], via the EM Kleisli-exponential
    application [app_kleisli], yields back the open computation [M]
    substituted by [V] — concretely [coalg_comp M (em_pair (coalg_id G) V)].

    Proof outline.  Unfold [app_kleisli] and [app_under] at the [ch_mor]
    level (via the faithful [U]) :
    [[
      ch_mor (app_kleisli (lam_coalg M) V)
        = bang_fmap (der (U B)) ∘ bang_fmap (app_under (lam_coalg M) V) ∘ coalg_str G.
    ]]
    The inner [app_under (lam_coalg M) V] is:
    [[
      tensor_uncurry (adj_phi (lam_coalg M)) ∘ ((id ⊗ ch_mor V) ∘ coalg_d G).
    ]]
    By [adj_phiK] (φ∘ψ = id), [adj_phi (lam_coalg M) = lam_under M =
    tensor_curry (ch_mor M)].  By [tensor_curryK] (uncurry∘curry = id),
    [tensor_uncurry (tensor_curry (ch_mor M)) = ch_mor M].  Hence
    [app_under (lam_coalg M) V = ch_mor M ∘ em_pair_mor id (ch_mor V)
    = ch_mor (coalg_comp M (em_pair (coalg_id G) V))].

    Let [H := coalg_comp M (em_pair (coalg_id G) V)].  Then
    [ch_mor (app_kleisli ...) = !(der) ∘ !(ch_mor H) ∘ coalg_str G].
    Use the coalgebra-morphism square of [H : G → Tobj B]
    ([dig ∘ ch_mor H = !(ch_mor H) ∘ coalg_str G]) to rewrite the right
    factor:
    [!(der) ∘ !(ch_mor H) ∘ coalg_str G = !(der) ∘ dig ∘ ch_mor H
    = id ∘ ch_mor H = ch_mor H]   (by [comonad_counitR]).
    Apply [coalg_hom_eqP] to conclude.

    Note on the statement.  The PPL's [eD_lam] clause produces
    [coalg_comp (tunit_eta C) (lam_coalg M)] with codomain [Tobj C] (a
    Kleisli-COMPUTATION of a lambda VALUE).  That outer [tunit_eta] is
    consumed by the [bang_m / kcomp] machinery of [eD_app], NOT by
    [app_kleisli].  The β-rule at the [app_kleisli] level — the
    irreducible categorical heart of the substitution lemma — is the
    one stated below, without the outer [tunit_eta]. *)
Lemma app_kleisli_lam (G A B : Coalgebra Ar)
    (M : coalg_hom (EM_prod G A) (Tobj B)) (V : coalg_hom G A) :
  app_kleisli (lam_coalg M) V = coalg_comp M (em_pair (coalg_id G) V).
Proof.
apply: coalg_hom_eqP.
rewrite /app_kleisli /lam_coalg /app_under /lam_under.
rewrite !coalg_comp_mor /=.
rewrite adj_phiK tensor_curryK.
set H := icones_comp (ch_mor M) (em_pair_mor (icones_id Ar (coalg_obj G)) (ch_mor V)).
have HH : is_coalg_mor G (Tobj B) H
  by exact: (ch_is_mor (coalg_comp M (em_pair (coalg_id G) V))).
rewrite /is_coalg_mor /= in HH.
by rewrite -HH icones_compA (comonad_counitR (U_obj B)) icones_compIl.
Qed.

End LamApp.

Arguments lam_under {R Ar G A B} MB.
Arguments lam_coalg {R Ar G A B} MB.
Arguments app_under {R Ar G A B} VF VA.
Arguments app_kleisli {R Ar G A B} VF VA.
Arguments app_pair {R Ar} A B.
Arguments app_kleisli_lam {R Ar G A B} M V.

(** ** Infrastructure for the surface β-rule on [eD]

    Two pure categorical identities about [coalg_hom]s and [bang_m]
    that arise when reducing the [eD]-image of [ne_app (ne_lam x M) V]
    against [eD_app] / [eD_lam] clauses.

    - [dig_ch_mor_F] : for a value [F : G → bang_cofree X],
      [dig X ∘ ch_mor F = bang_fmap (ch_mor F) ∘ coalg_str G].
      This is the coalgebra-morphism square at the [bang_cofree]
      codomain, with [coalg_str (bang_cofree X) = dig X] folded.

    - [adj_phi_bang_m_em_pair_eta] : for a value
      [F : G → bang_cofree X] and any [V : G → A],
      [adj_phi (bang_m ∘ em_pair (η ∘ F) (η ∘ V)) = em_pair_mor (ch_mor F) (ch_mor V)].
      Pre-composes [bang_m] with an [η]-paired value pair and applies
      [adj_phi]: the result is the underlying pairing
      [em_pair_mor (ch_mor F) (ch_mor V)] without any [Bang] / [bang_m]
      wrapping.  Uses [adj_counit_monoidal2] +
      [comonad_counitL] + [coalg_counit].

    These two lemmas are the unconditional half of the surface β
    machinery; the missing piece — the full β rule connecting
    [kcomp app_pair (bang_m ∘ em_pair (η ∘ lam_coalg M) V)] to
    [kbind_ext M V] — would additionally require a naturality lemma
    [app_under (em_proj1 _ _) (em_proj2 _ _) ∘ em_pair_mor F V = app_under F V],
    which the SAFT tensor-uncurry layer does not currently expose as a
    one-step rewrite (only [tensor_curry_natural_post] /
    [tensor_curry_natural_B_post] are available, and they require
    detouring through [tensor_mor_l]). *)

Section EDAppLamSubst.
Variables (R : realType) (Ar : MeasSubcat R).

Opaque der dig coalg_str bang_fmap coalg_d.

(** [dig X ∘ ch_mor F = bang_fmap (ch_mor F) ∘ coalg_str G] for a
    value [F : G → bang_cofree X].  The coalg-morphism square
    [coalg_str (bang_cofree X) ∘ ch_mor F = bang_fmap (ch_mor F) ∘
    coalg_str G] with [coalg_str (bang_cofree X) = dig X]
    ([bang_cofree_str]) folded. *)
Lemma dig_ch_mor_F (G : Coalgebra Ar) (X : ICone.type Ar)
    (F : coalg_hom G (bang_cofree X)) :
  icones_comp (dig X) (ch_mor F)
  = icones_comp (bang_fmap (ch_mor F)) (coalg_str G).
Proof.
have := ch_is_mor F.
rewrite /is_coalg_mor /=.
by rewrite bang_cofree_str.
Qed.

(** [adj_phi (bang_m ∘ em_pair (η ∘ F) (η ∘ V)) = em_pair_mor (ch_mor F) (ch_mor V)]
    for a value [F : G → bang_cofree X] and [V : G → A].  Chases:

    1. [adj_phi_natL] / [adj_counit_monoidal2]: [adj_phi (bang_m ∘ —)
       = tensor_mor (adj_counit (Bang X)) (adj_counit A) ∘ U_mor (em_pair —)].
    2. [coalg_comp_mor] + [bang_cofree_str]: [ch_mor (η ∘ F) = dig X ∘
       ch_mor F]; similarly [ch_mor (η ∘ V) = coalg_str A ∘ ch_mor V].
    3. Tensor-functoriality: combine the four icones_homs through the
       tensor_mor.
    4. [comonad_counitL] : [der (Bang X) ∘ dig X = id]; [coalg_counit] :
       [der (coalg_obj A) ∘ coalg_str A = id].  Both [tensor_mor]
       arguments collapse to [ch_mor F] / [ch_mor V] respectively. *)
Lemma adj_phi_bang_m_em_pair_eta (G A : Coalgebra Ar) (X : ICone.type Ar)
    (F : coalg_hom G (bang_cofree X))
    (V : coalg_hom G A) :
  adj_phi (coalg_comp (bang_m (Bang Ar X) (coalg_obj A))
                      (em_pair (coalg_comp (tunit_eta _) F)
                               (coalg_comp (tunit_eta A) V)))
  = em_pair_mor (ch_mor F) (ch_mor V).
Proof.
rewrite (adj_phi_natL (bang_m (Bang Ar X) (coalg_obj A))
                      (em_pair (coalg_comp (tunit_eta _) F)
                               (coalg_comp (tunit_eta A) V))).
rewrite /adj_phi /U_mor /=.
rewrite (adj_counit_monoidal2 (Bang Ar X) (coalg_obj A)).
rewrite /em_pair /em_pair_mor /=.
rewrite icones_compA.
rewrite -tensor_mor_comp.
rewrite bang_cofree_str.
rewrite icones_compA.
rewrite /adj_counit.
rewrite (comonad_counitL X).
rewrite icones_compIl.
rewrite (icones_compA (der (coalg_obj A))).
rewrite (coalg_counit A).
by rewrite icones_compIl.
Qed.

(** [adj_phi (em_proj1) ∘ em_pair_mor (ch_mor F) (ch_mor V) = adj_phi F]:
    the projection-pair law transported through the [adj_phi] bijection.
    Chases:

    1. [em_pair_mor (ch_mor F) (ch_mor V) = U_mor (em_pair F V) =
       ch_mor (em_pair F V)] (definitional: [ch_mor (em_pair F V)] is
       defined to be [em_pair_mor (ch_mor F) (ch_mor V)]).
    2. [adj_phi_natL] (reverse) gives:
       [adj_phi (em_proj1) ∘ U_mor (em_pair F V) = adj_phi (coalg_comp em_proj1 (em_pair F V))].
    3. [coalg_comp em_proj1 (em_pair F V) = F] by [em_proj1_pair (ch_is_mor V)]
       lifted through [coalg_hom_eqP]. *)
Lemma adj_phi_em_proj1_em_pair (G A : Coalgebra Ar) (X : ICone.type Ar)
    (F : coalg_hom G (bang_cofree X))
    (V : coalg_hom G A) :
  icones_comp (adj_phi (em_proj1 (bang_cofree X) A))
              (em_pair_mor (ch_mor F) (ch_mor V))
  = adj_phi F.
Proof.
have HF : coalg_comp (em_proj1 (bang_cofree X) A) (em_pair F V) = F.
  apply: coalg_hom_eqP.
  rewrite coalg_comp_mor /=.
  apply: (em_proj1_pair (Z := G) (P := bang_cofree X) (Q := A)
                        (f := ch_mor F) (g := ch_mor V)).
  exact: ch_is_mor.
rewrite -[em_pair_mor (ch_mor F) (ch_mor V)]
  /(U_mor (em_pair F V)).
rewrite -(adj_phi_natL (em_proj1 (bang_cofree X) A) (em_pair F V)).
by rewrite HF.
Qed.

(** *** [app_under_proj_em_pair] — the icones-level β decomposition

    The categorical heart of the surface β rule.  Given a value
    [F : G → bang_cofree (linhom A (U(T B)))] (a function value at type
    [tfun A B]) and a value [V : G → A], applying [app_under] to the
    canonical [em_proj]s and precomposing by the [em_pair_mor (F, V)]
    pairing recovers [app_under F V] — i.e., the substitution-by-pair
    that [eD_app] performs reduces to direct value-application.

    Proof (the gap-A chain).
    1. [coalg_mor_d] pulls [coalg_d (EM_prod ...)] through [em_pair_mor (F, V)]:
       [coalg_d ∘ em_pair_mor F V = tensor_mor (em_pair_mor F V) (em_pair_mor F V) ∘ coalg_d G].
    2. [tensor_mor_comp] + [em_proj2_pair (ch_is_mor F)] absorb the
       second component into [ch_mor V]:
       [tensor_mor id (em_proj2_mor) ∘ tensor_mor (em_pair F V) (em_pair F V)
        = tensor_mor (em_pair F V) (em_proj2_mor ∘ em_pair F V)
        = tensor_mor (em_pair F V) (ch_mor V)].
    3. Split [tensor_mor (em_pair F V) (ch_mor V) = tensor_mor (em_pair F V) id
       ∘ tensor_mor id (ch_mor V)] (via [tensor_mor_comp]).
    4. [tensor_uncurry_natL] (Step 2 of the gap):
       [tensor_uncurry (adj_phi (em_proj1)) ∘ tensor_mor (em_pair F V) id
        = tensor_uncurry (adj_phi (em_proj1) ∘ em_pair_mor F V)].
    5. [adj_phi_em_proj1_em_pair] (Step 3 of the gap):
       [adj_phi (em_proj1) ∘ em_pair_mor F V = adj_phi F]. *)
Lemma app_under_proj_em_pair (G A B : Coalgebra Ar)
    (F : coalg_hom G (bang_cofree (linhom_car Ar (coalg_obj A) (coalg_obj (Tobj B)))))
    (V : coalg_hom G A) :
  icones_comp
    (app_under (em_proj1 (bang_cofree (linhom_car Ar (coalg_obj A) (coalg_obj (Tobj B)))) A)
               (em_proj2 (bang_cofree (linhom_car Ar (coalg_obj A) (coalg_obj (Tobj B)))) A))
    (em_pair_mor (ch_mor F) (ch_mor V))
  = app_under F V.
Proof.
rewrite /app_under.
Local Opaque tensor_uncurry adj_phi em_proj1 em_proj2 em_pair_mor.
have HempMor := em_pair_is_mor (Z := G)
                  (P := bang_cofree (linhom_car Ar (coalg_obj A) (coalg_obj (Tobj B))))
                  (Q := A)
                  (ch_is_mor F) (ch_is_mor V).
rewrite -(icones_compA (tensor_uncurry _) _ (em_pair_mor _ _)).
rewrite -(icones_compA (tensor_mor _ _) _ (em_pair_mor _ _)).
rewrite (coalg_mor_d _ HempMor).
rewrite (icones_compA (tensor_mor _ _) (tensor_mor _ _) (coalg_d G)).
rewrite -(tensor_mor_comp (icones_id _ _) (em_pair_mor (ch_mor F) (ch_mor V))
                          (ch_mor (em_proj2 _ A)) (em_pair_mor (ch_mor F) (ch_mor V))).
rewrite icones_compIl.
rewrite -[ch_mor (em_proj2 _ _)]/(em_proj2_mor _ _).
rewrite (em_proj2_pair (P := bang_cofree (linhom_car Ar (coalg_obj A) (coalg_obj (Tobj B))))
                       (Q := A) (Z := G) (f := ch_mor F) (g := ch_mor V) (ch_is_mor F)).
rewrite (_ : tensor_mor (em_pair_mor (ch_mor F) (ch_mor V)) (ch_mor V)
           = icones_comp
               (tensor_mor (em_pair_mor (ch_mor F) (ch_mor V)) (icones_id Ar (coalg_obj A)))
               (tensor_mor (icones_id Ar (coalg_obj G)) (ch_mor V))); last first.
  by rewrite -tensor_mor_comp icones_compIr icones_compIl.
rewrite -(icones_compA (tensor_mor (em_pair_mor _ _) _) (tensor_mor _ _) (coalg_d G)).
rewrite (icones_compA (tensor_uncurry _) (tensor_mor (em_pair_mor _ _) _) (icones_comp _ _)).
rewrite (tensor_uncurry_natL (em_pair_mor (ch_mor F) (ch_mor V)) _).
by rewrite (adj_phi_em_proj1_em_pair F V).
Local Transparent tensor_uncurry adj_phi em_proj1 em_proj2 em_pair_mor.
Qed.

End EDAppLamSubst.

Arguments dig_ch_mor_F {R Ar G X} F.
Arguments adj_phi_bang_m_em_pair_eta {R Ar G A X} F V.
Arguments adj_phi_em_proj1_em_pair {R Ar G A X} F V.
Arguments app_under_proj_em_pair {R Ar G A B} F V.

(** ** Surface beta-rule for the named-syntax PPL

    The categorical β-rule corresponding to the named-syntax reduction
    [ne_app (ne_lam x M) V' = M[V'/x]].  Two flavours, both at the cones
    level:

    - [adj_phi_bang_m_em_pair_eta_L] : the half-η variant of
      [adj_phi_bang_m_em_pair_eta] — only the LEFT factor is η-wrapped,
      the RIGHT factor is an arbitrary Kleisli arrow.  Reads:
      [[
        adj_phi (bang_m ∘ em_pair (η ∘ F) V')
        = em_pair_mor (ch_mor F) (adj_phi V').
      ]]

    - [eD_app_lam_subst] : the headline β reduction.  Given a lambda
      body [M : EM_prod G A ⇝ B] and a Kleisli arrow [V' : G ⇝ A], the
      [eD]-image of [ne_app (ne_lam x M) V']-shape reduces to
      [kbind_ext M V'] — the direct-style "sequence V', then run M
      with the bound variable".  This is the equational law that lets
      the marginal-at-[x] identities of [examples.v] discharge their
      headline forms. *)
Section EDAppLamSubstSurface.
Variables (R : realType) (Ar : MeasSubcat R).

Opaque der dig coalg_str bang_fmap coalg_d.

(** [adj_phi (bang_m ∘ em_pair (η ∘ F) V') = em_pair_mor (ch_mor F) (adj_phi V')]:
    half-η variant of [adj_phi_bang_m_em_pair_eta].  Chases:

    1. [adj_phi_natL] reduces the outer [adj_phi] to
       [adj_phi (bang_m) ∘ U_mor (em_pair (η ∘ F) V')].
    2. [adj_counit_monoidal2] reduces [adj_phi (bang_m)] to
       [tensor_mor (der X) (der (U A))].
    3. [em_pair_mor_natR]-style absorption reduces the [tensor_mor ∘ em_pair_mor]
       composite to [em_pair_mor (der X ∘ ch_mor (η∘F)) (der (U A) ∘ ch_mor V')].
    4. [bang_cofree_str] + [comonad_counitL X] collapse the LEFT factor to
       [ch_mor F]; the RIGHT factor is by definition [adj_phi V']. *)
Lemma adj_phi_bang_m_em_pair_eta_L (G A : Coalgebra Ar) (X : ICone.type Ar)
    (F : coalg_hom G (bang_cofree X))
    (V' : coalg_hom G (Tobj A)) :
  adj_phi (coalg_comp (bang_m (Bang Ar X) (coalg_obj A))
                      (em_pair (coalg_comp (tunit_eta _) F) V'))
  = em_pair_mor (ch_mor F) (adj_phi V').
Proof.
rewrite (adj_phi_natL (bang_m (Bang Ar X) (coalg_obj A))
                      (em_pair (coalg_comp (tunit_eta _) F) V')).
rewrite /adj_phi /U_mor /=.
rewrite (adj_counit_monoidal2 (Bang Ar X) (coalg_obj A)).
rewrite /em_pair /em_pair_mor /=.
rewrite icones_compA.
rewrite -tensor_mor_comp.
rewrite bang_cofree_str.
rewrite icones_compA.
rewrite /adj_counit.
rewrite (comonad_counitL X).
by rewrite icones_compIl.
Qed.

(** *** [adj_phi_app_kleisli] — adj_phi computes app_kleisli as der ∘ app_under

    For any value function [VF : G → bang_cofree (linhom A (U(T B)))] and
    value argument [VA : G → A], [adj_phi (app_kleisli VF VA) =
    der (U B) ∘ app_under VF VA].

    Proof.  Unfold [app_kleisli VF VA = coalg_comp (tmul B) (adj_psi (app_under
    VF VA))] and apply [adj_phi_natL].  The composite [adj_phi (tmul B) ∘
    U_mor (adj_psi (app_under VF VA))] reduces, via [bang_fmap_comp] +
    [der_nat] + [adj_triangleL P] ([der ∘ coalg_str P = id_{U P}], a
    coalgebra-counit law transported through the [U]-side), to
    [(der (U B) ∘ app_under VF VA)].  This is the standard "monad-mult
    collapses to dereliction" reduction for [tmul / der]. *)
Lemma adj_phi_app_kleisli (G A B : Coalgebra Ar)
    (VF : coalg_hom G
            (bang_cofree (linhom_car Ar (coalg_obj A) (coalg_obj (Tobj B)))))
    (VA : coalg_hom G A) :
  adj_phi (app_kleisli VF VA)
  = icones_comp (der (coalg_obj B)) (app_under VF VA).
Proof.
rewrite /app_kleisli.
rewrite adj_phi_natL.
rewrite /adj_phi /tmul /U_mor /adj_counit /=.
rewrite -[U_obj B]/(coalg_obj B).
rewrite -(icones_compA (der (coalg_obj B)) (bang_fmap (der (coalg_obj B))) _).
rewrite (icones_compA (bang_fmap (der (coalg_obj B))) (bang_fmap (app_under VF VA))
                      (coalg_str G)).
rewrite -bang_fmap_comp.
rewrite (icones_compA (der _) (bang_fmap _) (coalg_str G)).
rewrite -(der_nat (icones_comp (der (coalg_obj B)) (app_under VF VA))).
rewrite -icones_compA.
rewrite (coalg_counit G).
by rewrite icones_compIr.
Qed.

(** *** [eD_app_lam_subst] — the categorical surface β rule (VALUE form)

    Given a lambda body [M : EM_prod G A ⇝ B] and a VALUE argument
    [V : G → A], the eD-image of the named-syntax reduction
    [ne_app (ne_lam x M) (η ∘ V)] is [coalg_comp M (em_pair id V)] —
    the body substituted by [V].  Reads (with the [eD_app] / [eD_lam]
    unfoldings folded back in):
    [[
      kcomp (app_pair A B)
            (coalg_comp (bang_m (Bang (linhom A (U(T B)))) (U A))
                        (em_pair (coalg_comp (tunit_eta _) (lam_coalg M))
                                 (coalg_comp (tunit_eta A) V)))
      = coalg_comp M (em_pair (coalg_id G) V).
    ]]
    Proof (the gap chain): [adj_phi_inj] + [adj_phi_kcomp] +
    [adj_phi_bang_m_em_pair_eta] reduce the LHS to
    [adj_phi (app_pair) ∘ em_pair_mor (ch_mor (lam M)) (ch_mor V)];
    [adj_phi_app_kleisli] turns this into
    [der (U B) ∘ app_under (em_proj1) (em_proj2) ∘ em_pair_mor (...)];
    [app_under_proj_em_pair] (the gap-A identity) collapses the icones-
    level β to [der (U B) ∘ app_under (lam_coalg M) V]; reading backwards
    through [adj_phi_app_kleisli] this is [adj_phi (app_kleisli (lam_coalg
    M) V)]; and by [app_kleisli_lam] the [coalg_hom] this projects from
    is [coalg_comp M (em_pair id V)] — the RHS. *)
Lemma eD_app_lam_subst (G A B : Coalgebra Ar)
    (M : coalg_hom (EM_prod G A) (Tobj B))
    (V : coalg_hom G A) :
  kcomp (app_pair A B)
        (coalg_comp (bang_m (Bang Ar (linhom_car Ar (coalg_obj A)
                                                    (coalg_obj (Tobj B))))
                            (coalg_obj A))
                    (em_pair (coalg_comp (tunit_eta _) (lam_coalg M))
                             (coalg_comp (tunit_eta A) V)))
  = coalg_comp M (em_pair (coalg_id G) V).
Proof.
rewrite -(app_kleisli_lam M V).
apply: adj_phi_inj.
rewrite adj_phi_kcomp.
rewrite (adj_phi_bang_m_em_pair_eta (lam_coalg M) V).
rewrite /app_pair adj_phi_app_kleisli adj_phi_app_kleisli.
rewrite -icones_compA.
by rewrite (app_under_proj_em_pair (lam_coalg M) V).
Qed.

End EDAppLamSubstSurface.

Arguments adj_phi_bang_m_em_pair_eta_L {R Ar G A X} F V'.
Arguments adj_phi_app_kleisli {R Ar G A B} VF VA.
Arguments eD_app_lam_subst {R Ar G A B} M V.

(** ** Term interpretation [eD]

    Every expression denotes a Kleisli arrow [⟦Γ ⊢ M : τ⟧ : coalg_hom (ctxD
    Γ) (Tobj (tyD τ))] in the EM category, by structural recursion on the
    syntax.

    - [e_var i] : [var_lookup i] is a VALUE (a [coalg_hom (ctxD G) (tyD
      t)]); compose with [tunit_eta] to get a Kleisli arrow into [Tobj].
    - [e_tt] : compose [tunit_eta EM_term] with the terminal map
      [em_term_mor].
    - [e_pair M N] : interpret both components as Kleisli arrows; pair
      via [em_pair] into [Tobj A × Tobj B]; then apply the commutative
      monoidal-monad pairing [bang_m] to land in [Tobj (A × B)].
    - [e_fst M] / [e_snd M] : post-compose with [Tmap em_proj1] /
      [Tmap em_proj2] (the functorial action of [T] on the projection
      values).
    - [e_lam M] : the body [M : (t1 :: G) ⇝ t2] = a Kleisli arrow on
      [EM_prod (ctxD G) (tyD t1)] into [Tobj (tyD t2)]; [lam_coalg]
      curries it through the Kleisli-exponential chain to a VALUE
      [coalg_hom G (tyD (tfun t1 t2))], then [tunit_eta] makes it a
      computation.
    - [e_app F X] : DIRECT-style application.  Interpret [F] / [X] as
      Kleisli arrows of type [G ⇝ tfun A B] / [G ⇝ A]; pair them with
      [em_pair] into [Tobj (tfun A B) × Tobj A]; apply [bang_m] to land
      in [Tobj (EM_prod (tfun A B) A)]; finally [kbind] with [app_pair]
      to actually fire the closure on its argument.  This is the
      "evaluate-evaluate-then-fire" Moggi semantics of direct
      application.
    - [e_let M K] : the extended-context Kleisli bind [kbind_ext]
      glueing [M : G ⇝ t1] with the continuation [K : (t1 :: G) ⇝ t2].
      This is the direct-style CBV sequencer; semantically identical
      to the old monadic-style [e_bind] minus the [tprob] markers.
    - [e_sample mu] : the constant Kleisli arrow [G ⇝ FMeas X] whose
      value is [mu], composed through [tunit_eta] of [FMeas_coalgebra X].
    - [e_real r] : the constant Kleisli arrow [G ⇝ tR] whose value is the
      Dirac at [R_to_carrier r] (norm exactly [1]).
    - [e_score f Hf_meas Hf_ge0 Hf_le1 e] : term-level score by [f(r)]
      where [r] is the value of [e], packaged via [score_lift].

    The two constant-style constructors ([e_sample]/[e_real]) share the
    same packaging pattern: build an [icones_hom] [coalg_obj G → C] by
    composing the cone-eraser [coalg_e (ctxD G) : coalg_obj G →
    cone_one_car] with the linear-point map [lin_pt c : cone_one_car →
    C] at the chosen unit-ball value [c]; lift the result to a
    coalgebra morphism into [Tobj] via [adj_psi] (which is
    UNCONDITIONAL — no coalgebra-morphism side condition on the
    icones_hom). *)

(** *** [const_kleisli c Hc] — the constant Kleisli arrow at [c]

    For [c : C] in the unit ball (witness [Hc : ‖c‖ ≤ 1]) and any
    coalgebra [G], produce a coalgebra morphism [G → bang_cofree C]
    whose underlying value is the constant Dirac-at-[c]-style lift.
    Concretely: [adj_psi (lin_pt c ∘ coalg_e G)]. *)
Section ConstKleisli.
Variables (R : realType) (Ar : MeasSubcat R).

(** A constant icones_hom out of any coalgebra, into [C], whose value is
    the [lin_pt]-scaling of a unit-ball element [c]. *)
Lemma lin_pt_norm_le1 (C : ICone.type Ar) (c : C) :
    (cone_norm c <= 1)%R ->
    (cone_norm (lin_pt c) <= 1)%R.
Proof.
move=> Hc.
rewrite -[cone_norm _]/(linhom_norm (lin_pt c)).
apply: linhom_norm_sup_lub => s Hs.
apply: le_trans (lin_pt_norm_le c s) _.
by rewrite -[1%R]mul1r; apply: ler_pM=> //;
  [exact: cone_norm_ge0|exact: cone_norm_ge0].
Qed.

Definition const_icones (G : Coalgebra Ar) (C : ICone.type Ar) (c : C)
    (Hc : (cone_norm c <= 1)%R) :
    icones_hom Ar (coalg_obj G) C :=
  icones_comp (linhom_icones (lin_pt c) (@lin_pt_norm_le1 C c Hc)) (coalg_e G).

Definition const_kleisli (G : Coalgebra Ar) (C : ICone.type Ar) (c : C)
    (Hc : (cone_norm c <= 1)%R) :
    coalg_hom G (bang_cofree C) :=
  adj_psi (@const_icones G C c Hc).

End ConstKleisli.

Arguments lin_pt_norm_le1 {R Ar C} c Hc.
Arguments const_icones {R Ar} G {C} c Hc.
Arguments const_kleisli {R Ar} G {C} c Hc.

(** ** Bridge: [const_kleisli] factors as [η ∘ const_value]

    The headline-form Lemmas 1/2 of [examples.v] apply a lambda
    [λ_. — ] at a literal real [|x|] = [real_kleisli x] = [const_kleisli
    G (dirac_fmeas x) Hd] : [coalg_hom G (Tobj (FMeas_coalgebra X))].
    The surface β rule [eD_app_lam_subst] of [Section
    EDAppLamSubstSurface] applies to a VALUE argument of the shape
    [coalg_comp (tunit_eta A) V] for [V : coalg_hom G A].  The bridge
    here closes the gap: it shows that under a "[prom]-fixedness"
    hypothesis on the chosen constant [c : coalg_obj A] —
    [coalg_str A ∘ lin_pt c = bang_fmap (lin_pt c) ∘ unit_cofree_str]
    — the [const_icones G c Hc] icones_hom IS a coalg morphism
    [G → A], and the [const_kleisli] factorisation
    [const_kleisli G c Hc = coalg_comp (tunit_eta A) (const_value G)]
    holds.

    The [prom]-fixedness hypothesis is automatic for Diracs in
    [FMeas_coalgebra X] (by [Coalg_dirac]); the [dirac_Hprom_str]
    lemma packages this.  Downstream, [real_kleisli x] / Lemma-1/2
    instantiate the bridge at [c = dirac_fmeas (R_to_carrier x)]. *)
Section ConstKleisliBridge.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

(** *** [const_icones] is a coalgebra morphism under [Hprom_str].

    Given [c : coalg_obj A] with [cone_norm c <= 1] and the [prom]-
    fixedness condition [coalg_str A ∘ lin_pt c = bang_fmap (lin_pt c)
    ∘ unit_cofree_str], the constant icones_hom [lin_pt c ∘ coalg_e G
    : G → A] is a coalgebra morphism.

    Proof.  Reduce [is_coalg_mor] (= [coalg_str A ∘ const = bang_fmap
    const ∘ coalg_str G]), unfold [const = lin_pt c ∘ coalg_e G],
    apply [Hprom_str] on the left, [bang_fmap_comp] + the coalg-mor
    property of [coalg_e G] ([coalg_e_is_mor_gen]) on the right.  Both
    sides reduce to [bang_fmap (lin_pt c) ∘ unit_cofree_str ∘ coalg_e G]. *)
Lemma const_value_is_coalg_mor (A : Coalgebra Ar) (c : coalg_obj A)
    (Hc : (cone_norm c <= 1)%R)
    (Hprom_str :
      icones_comp (coalg_str A) (linhom_icones (lin_pt c) (lin_pt_norm_le1 c Hc))
      = icones_comp (bang_fmap (linhom_icones (lin_pt c) (lin_pt_norm_le1 c Hc)))
                    unit_cofree_str)
    (G : Coalgebra Ar) :
  is_coalg_mor G A (const_icones G c Hc).
Proof.
rewrite /is_coalg_mor /const_icones.
rewrite icones_compA Hprom_str.
rewrite -icones_compA bang_fmap_comp.
rewrite -icones_compA.
have Hce := coalg_e_is_mor_gen G.
rewrite /is_coalg_mor /= in Hce.
rewrite -Hce.
by rewrite icones_compA.
Qed.

(** [const_value G c Hc Hprom_str] — the [coalg_hom G A] value
    whose underlying icones_hom is [const_icones G c Hc]. *)
Definition const_value (A : Coalgebra Ar) (c : coalg_obj A)
    (Hc : (cone_norm c <= 1)%R)
    (Hprom_str :
      icones_comp (coalg_str A) (linhom_icones (lin_pt c) (lin_pt_norm_le1 c Hc))
      = icones_comp (bang_fmap (linhom_icones (lin_pt c) (lin_pt_norm_le1 c Hc)))
                    unit_cofree_str)
    (G : Coalgebra Ar) : coalg_hom G A :=
  MkCoalgHom (const_value_is_coalg_mor Hprom_str G).

(** *** The bridge identity: [const_kleisli = η ∘ const_value]

    Under [Hprom_str], the [const_kleisli] arrow factors as
    [coalg_comp (tunit_eta A) (const_value G c Hc Hprom_str)] —
    exactly the value-form shape demanded by [eD_app_lam_subst].

    Proof.  Reduce both sides via [coalg_hom_eqP] to icones_homs.
    LHS = [adj_psi const_icones] = [bang_fmap const_icones ∘ coalg_str
    G].  RHS underlying = [coalg_str A ∘ const_icones G c Hc].  Unfold
    [const_icones]; apply [bang_fmap_comp] + the coalg-mor property of
    [coalg_e G] on LHS; [Hprom_str] (reverse) on the rewritten LHS to
    expose [coalg_str A ∘ lin_pt c ∘ coalg_e G] — same as RHS. *)
Lemma const_kleisli_eq_tunit_eta_const (A : Coalgebra Ar) (c : coalg_obj A)
    (Hc : (cone_norm c <= 1)%R)
    (Hprom_str :
      icones_comp (coalg_str A) (linhom_icones (lin_pt c) (lin_pt_norm_le1 c Hc))
      = icones_comp (bang_fmap (linhom_icones (lin_pt c) (lin_pt_norm_le1 c Hc)))
                    unit_cofree_str)
    (G : Coalgebra Ar) :
  const_kleisli G c Hc = coalg_comp (tunit_eta A) (const_value Hprom_str G).
Proof.
apply: coalg_hom_eqP.
rewrite coalg_comp_mor /=.
rewrite /tunit_eta /adj_unit /=.
rewrite /const_kleisli /adj_psi /=.
rewrite /const_icones.
rewrite bang_fmap_comp -icones_compA.
have Hce := coalg_e_is_mor_gen G.
rewrite /is_coalg_mor /= in Hce.
rewrite -Hce.
rewrite (icones_compA (bang_fmap _) unit_cofree_str (coalg_e G)).
rewrite -Hprom_str.
by rewrite icones_compA.
Qed.

(** *** [dirac_Hprom_str] — [Hprom_str] is automatic for Diracs.

    For [c = dirac_fmeas r : FMeas X] in [FMeas_coalgebra X], the
    [prom]-fixedness equation holds because [Coalg X (δ_r) = prom δ_r]
    ([Coalg_dirac]) and [unit_cofree_str one1 = prom one1] reduces the
    RHS to [prom (lin_pt(δ_r) one1) = prom δ_r] via [bang_fmap_prom].
    [one_ext] (a morphism out of the cone-unit is determined by its
    value at [one1]) closes the equation of icones_homs. *)
Lemma dirac_Hprom_str (X : ar_obj Ar) (r : ar_carrier Ar X)
    (Hc : (cone_norm (dirac_fmeas r : FMeas X) <= 1)%R) :
  icones_comp (coalg_str (FMeas_coalgebra X))
              (linhom_icones (lin_pt (dirac_fmeas r)) (lin_pt_norm_le1 _ Hc))
  = icones_comp (bang_fmap (linhom_icones (lin_pt (dirac_fmeas r))
                                          (lin_pt_norm_le1 _ Hc)))
                unit_cofree_str.
Proof.
apply: one_ext.
rewrite -[Lfun (icones_comp (coalg_str _) _) one1]
        /(Lfun (coalg_str (FMeas_coalgebra X))
               (Lfun (linhom_icones (lin_pt (dirac_fmeas r)) _) one1)).
rewrite (linhom_iconesE (lin_pt _) _ one1).
rewrite lin_pt_unit.
rewrite -[Lfun (coalg_str (FMeas_coalgebra X)) (dirac_fmeas r)]
        /(Lfun (Coalg X) (dirac_fmeas r)).
rewrite (Coalg_dirac X r).
rewrite -[Lfun (icones_comp (bang_fmap _) _) one1]
        /(Lfun (bang_fmap _) (Lfun unit_cofree_str one1)).
rewrite unit_cofree_str_one1.
have H1 : cone_norm (one1 : cone_one_car Ar) <= 1.
  by rewrite (_ : cone_norm one1 = 1) // /cone_norm /= /c1_norm.
rewrite (bang_fmap_prom _ one1 H1).
rewrite -[(linhom_icones _ _) one1]
        /(Lfun (linhom_icones (lin_pt (dirac_fmeas r)) _) one1).
rewrite (linhom_iconesE (lin_pt _) _ one1).
by rewrite lin_pt_unit.
Qed.

End ConstKleisliBridge.

Arguments const_value_is_coalg_mor {R Ar A c Hc} Hprom_str G.
Arguments const_value {R Ar A c Hc} Hprom_str G.
Arguments const_kleisli_eq_tunit_eta_const {R Ar A c Hc} Hprom_str G.
Arguments dirac_Hprom_str {R Ar X} r Hc.

(** ** Specialised β rule for [const_kleisli] arguments

    The headline-form β rule for the surface PPL: when the
    application's argument is a [const_kleisli] (e.g. a literal real
    [|x|] = [real_kleisli x] or a [sample_kleisli µ]) and the
    [prom]-fixedness condition [Hprom_str] holds, the [eD]-image of
    the application reduces by the value-form β rule of [Section
    EDAppLamSubstSurface] composed with the [const_kleisli/η-const]
    bridge of [Section ConstKleisliBridge].

    Reads (with [eD_app] / [eD_lam] / [eD_real] unfolded):
    [[
      kcomp (app_pair A B)
            (bang_m ∘ em_pair (η ∘ lam M) (const_kleisli G c Hc))
      = coalg_comp M (em_pair coalg_id (const_value Hprom_str G)).
    ]]
    Proof: [const_kleisli_eq_tunit_eta_const] rewrites the
    [const_kleisli] argument to [η ∘ const_value], then
    [eD_app_lam_subst] (the VALUE-form β rule) closes. *)
Section EDAppLamSubstConst.
Variables (R : realType) (Ar : MeasSubcat R).

Lemma eD_app_lam_subst_const (G A B : Coalgebra Ar)
    (M : coalg_hom (EM_prod G A) (Tobj B))
    (c : coalg_obj A) (Hc : (cone_norm c <= 1)%R)
    (Hprom_str :
      icones_comp (coalg_str A) (linhom_icones (lin_pt c) (lin_pt_norm_le1 c Hc))
      = icones_comp (bang_fmap (linhom_icones (lin_pt c) (lin_pt_norm_le1 c Hc)))
                    unit_cofree_str) :
  kcomp (app_pair A B)
        (coalg_comp (bang_m (Bang Ar (linhom_car Ar (coalg_obj A)
                                                    (coalg_obj (Tobj B))))
                            (coalg_obj A))
                    (em_pair (coalg_comp (tunit_eta _) (lam_coalg M))
                             (const_kleisli G c Hc)))
  = coalg_comp M (em_pair (coalg_id G) (const_value Hprom_str G)).
Proof.
rewrite (const_kleisli_eq_tunit_eta_const Hprom_str G).
exact: (eD_app_lam_subst M (const_value Hprom_str G)).
Qed.

End EDAppLamSubstConst.

Arguments eD_app_lam_subst_const {R Ar G A B} M {c Hc} Hprom_str.

(** ** Kleisli helpers for the headline-form examples.

    Three small auxiliaries used to discharge the headline-form
    Lemmas 1/2 of [theories/programs/examples.v]:

    - [em_pair_coalg_comp] : [⟨f,g⟩ ∘ h = ⟨f∘h, g∘h⟩] for [h : Z ⇝ Y]
      a coalg morphism — pair-naturality at the [coalg_hom] level.
      (The [em_pair_mor_natL] of [Section KbindExtLaws] is the
      icones-level version; this lemma lifts it.)

    - [kcomp_eta_natR] : [kcomp g (η ∘ v) = g ∘ v].  When the input
      Kleisli arrow [η ∘ v] is the [η]-lift of a value [v], the
      kbind collapses to direct composition.  This is the key
      collapsing step for the headline-form proofs: it lets us
      reduce [kcomp K_outer ((η ∘ lam_coalg M) ∘ ...)] to
      [K_outer ∘ (lam_coalg M ∘ ...)], removing the [kbind] wrapper
      over the literal lambda value.

    - [const_kleisli_natL] : [const_kleisli G c Hc ∘ h = const_kleisli
      G' c Hc] for [h : G' ⇝ G] a coalg morphism — the source-coalgebra
      naturality of [const_kleisli]; constant arrows are invariant
      under precomposition by any coalg-mor. *)
Section KleisliHelpers.
Variables (R : realType) (Ar : MeasSubcat R).

Lemma em_pair_coalg_comp (Z Y P Q : Coalgebra Ar)
    (h : coalg_hom Z Y) (f : coalg_hom Y P) (g : coalg_hom Y Q) :
  coalg_comp (em_pair f g) h = em_pair (coalg_comp f h) (coalg_comp g h).
Proof.
apply: coalg_hom_eqP.
rewrite !coalg_comp_mor /=.
apply: em_pair_mor_natL.
exact: ch_is_mor h.
Qed.

Lemma kcomp_eta_natR (P Q S : Coalgebra Ar)
    (g : coalg_hom Q (Tobj S)) (v : coalg_hom P Q) :
  kcomp g (coalg_comp (tunit_eta Q) v) = coalg_comp g v.
Proof.
apply: adj_phi_inj.
rewrite adj_phi_kcomp.
rewrite (adj_phi_natL (tunit_eta Q) v).
rewrite adj_triangleL icones_compIl.
by rewrite -adj_phi_natL.
Qed.

(** [coalg_comp (kcomp g f) h = kcomp g (coalg_comp f h)] — [kcomp]'s
    source-precomposition is just associativity of [coalg_comp]. *)
Lemma kcomp_coalg_compR (P P' Q S : Coalgebra Ar)
    (g : coalg_hom Q (Tobj S)) (f : coalg_hom P (Tobj Q)) (h : coalg_hom P' P) :
  coalg_comp (kcomp g f) h = kcomp g (coalg_comp f h).
Proof. by rewrite /kcomp coalg_compA. Qed.

Lemma const_kleisli_natL (G G' : Coalgebra Ar) (C : ICone.type Ar)
    (c : C) (Hc : (cone_norm c <= 1)%R) (h : coalg_hom G' G) :
  coalg_comp (const_kleisli G c Hc) h = const_kleisli G' c Hc.
Proof.
apply: coalg_hom_eqP.
rewrite coalg_comp_mor /=.
rewrite /const_kleisli /adj_psi /=.
rewrite /const_icones.
have Hh := ch_is_mor h.
rewrite /is_coalg_mor /= in Hh.
rewrite -icones_compA Hh.
rewrite icones_compA -bang_fmap_comp.
have Hce : icones_comp (coalg_e G) (ch_mor h) = coalg_e G'.
  exact: (@coalg_mor_e _ _ G' G (ch_mor h) Hh).
rewrite -[icones_comp (icones_comp _ (coalg_e G)) (ch_mor h)]icones_compA.
by rewrite Hce.
Qed.

End KleisliHelpers.

Arguments em_pair_coalg_comp {R Ar Z Y P Q} h f g.
Arguments kcomp_eta_natR {R Ar P Q S} g v.
Arguments kcomp_coalg_compR {R Ar P P' Q S} g f h.
Arguments const_kleisli_natL {R Ar G G' C} c Hc h.

(** ** Arithmetic lifts on the cone level — [add_lift] / [mul_lift]

    For the distinguished real-valued base type [tR = tbase R_obj], we
    package binary [+] and [×] on [R] as [icones_hom]s into [FMeas R_obj]:
    [[
        add_lift, mul_lift :
          icones_hom Ar (FMeas R_obj ⊗ FMeas R_obj) (FMeas R_obj).
    ]]
    Construction.  Each of these is the composition
    [[
        FMeas_fmap op_meas ∘ fmeas_lax R_obj R_obj
    ]]
    where [op_meas : ar_hom (ar_prod R_obj R_obj) R_obj] is the
    transport of the corresponding [R × R → R] operation across the
    Type-level cast [R_carrier_eq], and [fmeas_lax R_obj R_obj] is the
    icones-level lax monoidal of paper §9 ([theories/homs/fmeas_lax.v]).

    The arithmetic [op_meas] requires the cast [R_carrier_eq] to be a
    [measurable] function; we therefore add the hypothesis
    [R_carrier_meas] to the section.  This is a Type-level cast, so
    measurability is a separate fact not implied by the
    [:> Type] equation. *)

(** *** Casts and round-trip identities (independent of measurability) *)

Section ArithCast.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.

Definition carrier_to_R (c : ar_carrier Ar R_obj) : R :=
  eq_rect _ (fun T : Type => T) c _ R_carrier_eq.

Lemma carrier_to_RK (c : ar_carrier Ar R_obj) :
  R_to_carrier R_carrier_eq (carrier_to_R c) = c.
Proof.
rewrite /R_to_carrier /carrier_to_R /eq_rect_r.
by move: c; case: _ / R_carrier_eq=> c.
Qed.

Lemma R_to_carrierK (r : R) :
  carrier_to_R (R_to_carrier R_carrier_eq r) = r.
Proof.
rewrite /R_to_carrier /carrier_to_R /eq_rect_r.
by move: r; case: _ / R_carrier_eq=> r.
Qed.

End ArithCast.

Arguments carrier_to_R {R Ar R_obj} R_carrier_eq c.
Arguments carrier_to_RK {R Ar R_obj} R_carrier_eq c.
Arguments R_to_carrierK {R Ar R_obj} R_carrier_eq r.

(** *** Arithmetic lifts proper *)

Section Arith.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Lemma carrier_to_R_meas :
  measurable_fun [set: ar_carrier Ar R_obj] (carrier_to_R R_carrier_eq).
Proof. exact: R_carrier_meas. Qed.

(** [add_fun] and [mul_fun]: the two binary operations transported
    through [R_carrier_eq] and [ar_prod_uncast] / [ar_prod_carrier_eq]. *)

Definition add_fun (p : ar_carrier Ar (ar_prod Ar R_obj R_obj)) :
    ar_carrier Ar R_obj :=
  R_to_carrier R_carrier_eq
    (carrier_to_R R_carrier_eq (ar_prod_uncast p).1 +
     carrier_to_R R_carrier_eq (ar_prod_uncast p).2).

Definition mul_fun (p : ar_carrier Ar (ar_prod Ar R_obj R_obj)) :
    ar_carrier Ar R_obj :=
  R_to_carrier R_carrier_eq
    (carrier_to_R R_carrier_eq (ar_prod_uncast p).1 *
     carrier_to_R R_carrier_eq (ar_prod_uncast p).2).

(** [add_fun] is measurable. *)
Lemma add_fun_meas : measurable_fun [set: _] add_fun.
Proof.
rewrite /add_fun.
apply: (measurableT_comp (f := R_to_carrier R_carrier_eq));
  first exact: R_to_carrier_meas.
have meas_unc : measurable_fun [set: _]
    (ar_prod_uncast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj))
  by exact: (ar_prod_uncast_meas Ar R_obj R_obj).
have meas_fst :
  measurable_fun [set: ar_carrier Ar (ar_prod Ar R_obj R_obj)]
    (fun p => (ar_prod_uncast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj) p).1).
  exact: (measurableT_comp measurable_fst meas_unc).
have meas_snd :
  measurable_fun [set: ar_carrier Ar (ar_prod Ar R_obj R_obj)]
    (fun p => (ar_prod_uncast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj) p).2).
  exact: (measurableT_comp measurable_snd meas_unc).
have meas_fst_R :
  measurable_fun [set: _]
    (fun p => carrier_to_R R_carrier_eq
                (ar_prod_uncast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj) p).1).
  exact: (measurableT_comp carrier_to_R_meas meas_fst).
have meas_snd_R :
  measurable_fun [set: _]
    (fun p => carrier_to_R R_carrier_eq
                (ar_prod_uncast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj) p).2).
  exact: (measurableT_comp carrier_to_R_meas meas_snd).
exact: measurable_funD.
Qed.

Lemma mul_fun_meas : measurable_fun [set: _] mul_fun.
Proof.
rewrite /mul_fun.
apply: (measurableT_comp (f := R_to_carrier R_carrier_eq));
  first exact: R_to_carrier_meas.
have meas_unc : measurable_fun [set: _]
    (ar_prod_uncast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj))
  by exact: (ar_prod_uncast_meas Ar R_obj R_obj).
have meas_fst :
  measurable_fun [set: ar_carrier Ar (ar_prod Ar R_obj R_obj)]
    (fun p => (ar_prod_uncast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj) p).1).
  exact: (measurableT_comp measurable_fst meas_unc).
have meas_snd :
  measurable_fun [set: ar_carrier Ar (ar_prod Ar R_obj R_obj)]
    (fun p => (ar_prod_uncast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj) p).2).
  exact: (measurableT_comp measurable_snd meas_unc).
have meas_fst_R :
  measurable_fun [set: _]
    (fun p => carrier_to_R R_carrier_eq
                (ar_prod_uncast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj) p).1).
  exact: (measurableT_comp carrier_to_R_meas meas_fst).
have meas_snd_R :
  measurable_fun [set: _]
    (fun p => carrier_to_R R_carrier_eq
                (ar_prod_uncast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj) p).2).
  exact: (measurableT_comp carrier_to_R_meas meas_snd).
exact: measurable_funM.
Qed.

HB.instance Definition _ :=
  isMeasurableFun.Build _ _ _ _ add_fun add_fun_meas.

HB.instance Definition _ :=
  isMeasurableFun.Build _ _ _ _ mul_fun mul_fun_meas.

Definition add_meas : ar_hom Ar (ar_prod Ar R_obj R_obj) R_obj := add_fun.
Definition mul_meas : ar_hom Ar (ar_prod Ar R_obj R_obj) R_obj := mul_fun.

(** Computation: [add_meas (ar_prod_cast (a, b)) = R_to_carrier (cR a + cR b)]. *)
Lemma add_meas_cast (a b : ar_carrier Ar R_obj) :
  add_meas (ar_prod_cast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj) (a, b)) =
  R_to_carrier R_carrier_eq
    (carrier_to_R R_carrier_eq a + carrier_to_R R_carrier_eq b).
Proof.
by rewrite -[LHS]/(add_fun (ar_prod_cast (a, b))) /add_fun ar_prod_castK.
Qed.

Lemma mul_meas_cast (a b : ar_carrier Ar R_obj) :
  mul_meas (ar_prod_cast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj) (a, b)) =
  R_to_carrier R_carrier_eq
    (carrier_to_R R_carrier_eq a * carrier_to_R R_carrier_eq b).
Proof.
by rewrite -[LHS]/(mul_fun (ar_prod_cast (a, b))) /mul_fun ar_prod_castK.
Qed.

(** The arithmetic lifts as [icones_hom]s. *)

Definition add_lift :
    icones_hom Ar
      (tensor Ar (FMeas R_obj) (FMeas R_obj))
      (FMeas R_obj) :=
  icones_comp (FMeas_fmap add_meas) (fmeas_lax R_obj R_obj).

Definition mul_lift :
    icones_hom Ar
      (tensor Ar (FMeas R_obj) (FMeas R_obj))
      (FMeas R_obj) :=
  icones_comp (FMeas_fmap mul_meas) (fmeas_lax R_obj R_obj).

(** [add_lift_dirac]: the load-bearing Dirac identity for [+]. *)

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

Lemma add_lift_dirac (a b : R) :
  Lfun add_lift
    (ptensor (B := FMeas R_obj) (C := FMeas R_obj)
       (dirac_fmeas (R_to_carrier R_carrier_eq a))
       (dirac_fmeas (R_to_carrier R_carrier_eq b))) =
  dirac_fmeas (R_to_carrier R_carrier_eq (a + b)).
Proof.
rewrite /add_lift.
rewrite -[LHS]/(Lfun (FMeas_fmap add_meas)
  (Lfun (fmeas_lax R_obj R_obj)
    (ptensor (B := FMeas R_obj) (C := FMeas R_obj)
       (dirac_fmeas (R_to_carrier R_carrier_eq a))
       (dirac_fmeas (R_to_carrier R_carrier_eq b))))).
rewrite (fmeas_lax_dirac (R_to_carrier R_carrier_eq a) (R_to_carrier R_carrier_eq b)).
rewrite (FMeas_fmap_dirac add_meas
  (ar_prod_cast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj)
                (R_to_carrier R_carrier_eq a, R_to_carrier R_carrier_eq b))).
by rewrite add_meas_cast !R_to_carrierK.
Qed.

Lemma mul_lift_dirac (a b : R) :
  Lfun mul_lift
    (ptensor (B := FMeas R_obj) (C := FMeas R_obj)
       (dirac_fmeas (R_to_carrier R_carrier_eq a))
       (dirac_fmeas (R_to_carrier R_carrier_eq b))) =
  dirac_fmeas (R_to_carrier R_carrier_eq (a * b)).
Proof.
rewrite /mul_lift.
rewrite -[LHS]/(Lfun (FMeas_fmap mul_meas)
  (Lfun (fmeas_lax R_obj R_obj)
    (ptensor (B := FMeas R_obj) (C := FMeas R_obj)
       (dirac_fmeas (R_to_carrier R_carrier_eq a))
       (dirac_fmeas (R_to_carrier R_carrier_eq b))))).
rewrite (fmeas_lax_dirac (R_to_carrier R_carrier_eq a) (R_to_carrier R_carrier_eq b)).
rewrite (FMeas_fmap_dirac mul_meas
  (ar_prod_cast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj)
                (R_to_carrier R_carrier_eq a, R_to_carrier R_carrier_eq b))).
by rewrite mul_meas_cast !R_to_carrierK.
Qed.

End Arith.

Arguments add_fun {R Ar R_obj} R_carrier_eq p.
Arguments mul_fun {R Ar R_obj} R_carrier_eq p.
Arguments add_meas {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}.
Arguments mul_meas {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}.
Arguments add_lift {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}.
Arguments mul_lift {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}.
Arguments add_lift_dirac {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} a b.
Arguments mul_lift_dirac {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} a b.

(** ** Term-level score lift — [score_lift]

    For a measurable [f : R → R] with pointwise [0 ≤ f r ≤ 1], we build
    an [icones_hom] from [FMeas R_obj] to the unit cone:
    [[
       score_lift f Hf_meas Hf_ge0 Hf_le1 :
         icones_hom Ar (FMeas R_obj) (cone_one_car Ar).
    ]]
    Construction.
    1.  [score_path_fun] : the path [r ↦ f(carrier_to_R r) · one1] in
        the unit cone, packaged via [MkConeOne].  Measurability of the
        path follows from measurability of [f ∘ carrier_to_R]
        (Lemma [hot_pres_path] template — every test of [cone_one_car]
        is [id_test], so the per-test measurability reduces to that of
        the scalar function).
    2.  Wrap as [path_car Ar R_obj (cone_one_car Ar)] ([MkPath]).
    3.  Apply [int_to_linhom] (paper Thm 6.1) — for the codomain
        [cone_one_car], the integral against [µ] is [∫ f(r) dµ(r) · one1].
    4.  Norm-bound [≤ 1] of the [linhom_car] follows from
        [int_to_linhom_norm_le] and the path-norm bound [≤ 1]
        (pointwise bound [f r ≤ 1] uniformly).
    5.  Promote to [icones_hom] via [linhom_icones].

    The **load-bearing Dirac identity** for the reduction lemmas:
    [[
       Lfun (score_lift f …) (dirac_fmeas (R_to_carrier r))
         = MkConeOne (NngNum (Hf_ge0 r)).
    ]]
    On a Dirac at [R_to_carrier r], the score reduces to the SCALAR
    [f r] times the unit-cone basis element. *)

Section ScoreTmLift.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).

Variable (f : R -> R).
Hypothesis Hf_meas : measurable_fun [set: R] f.
Hypothesis Hf_ge0 : forall r : R, (0 <= f r)%R.
Hypothesis Hf_le1 : forall r : R, (f r <= 1)%R.

Local Notation cR := (carrier_to_R R_carrier_eq).
Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

(** The path value at [r] : [MkConeOne (NngNum (Hf_ge0 (cR r)))]. *)
Definition score_path_fun (r : ar_carrier Ar R_obj) : cone_one_car Ar :=
  MkConeOne Ar (NngNum (Hf_ge0 (cR r))).

Lemma score_path_fun_norm (r : ar_carrier Ar R_obj) :
  (cone_norm (score_path_fun r) <= 1)%R.
Proof.
by rewrite /cone_norm/= /c1_norm/= /score_path_fun/=; exact: Hf_le1.
Qed.

(** Composite [f ∘ cR] is measurable. *)
Lemma f_cR_meas :
  measurable_fun [set: ar_carrier Ar R_obj] (fun r => f (cR r)).
Proof.
apply: (measurableT_comp (f := f)).
- exact: Hf_meas.
- exact: R_carrier_meas.
Qed.

(** [score_path_fun] is a measurable path. *)
Lemma score_path_is_path :
  is_measurable_path (Ar := Ar) (C := cone_one_car Ar) (X := R_obj)
    score_path_fun.
Proof.
split.
  exists 1 => r; exact: score_path_fun_norm.
move=> Y m mM.
(* The only test of [cone_one_car] is [id_test]; on it, the per-test
   map [(z,r) ↦ test_fun m z (score_path_fun r)] reduces to
   [(z,r) ↦ f(cR r)], which is measurable. *)
have Em : m = ConeOneMConeAux.id_test (R := R) (Ar := Ar) Y := mM.
rewrite Em /ConeOneMConeAux.id_test /=
        /ConeOneMConeAux.id_test_fun /score_path_fun /=.
apply: (measurableT_comp (f := fun r => f (cR r))).
- exact: f_cR_meas.
- exact: measurable_snd.
Qed.

Definition score_path : path_car Ar R_obj (cone_one_car Ar) :=
  MkPath score_path_is_path.

(** Path-norm bound: the path values are all [≤ 1], so the sup is [≤ 1]. *)
Lemma score_path_norm_le1 : (path_norm score_path <= 1)%R.
Proof.
apply: ge_sup; first exact: path_normset_nonempty.
by move=> _ [r ->] /=; exact: score_path_fun_norm.
Qed.

(** Norm bound for [int_to_linhom score_path]. *)
Lemma score_int_norm_le1 :
  (cone_norm (int_to_linhom score_path) <= 1)%R.
Proof.
apply: le_trans (int_to_linhom_norm_le score_path) _.
exact: score_path_norm_le1.
Qed.

(** The lift as an [icones_hom]. *)
Definition score_lift :
    icones_hom Ar (FMeas R_obj) (cone_one_car Ar) :=
  linhom_icones (int_to_linhom score_path) score_int_norm_le1.

(** **** Load-bearing Dirac identity.

    On a Dirac at [R_to_carrier r] in [FMeas R_obj], the score
    lift evaluates to [f r · one1] (packaged as a [cone_one_car]). *)
Lemma score_lift_dirac (r : R) :
  Lfun score_lift (dirac_fmeas (R_to_carrier R_carrier_eq r)) =
  MkConeOne Ar (NngNum (Hf_ge0 r)).
Proof.
rewrite /score_lift.
rewrite (linhom_iconesE _ score_int_norm_le1
           (dirac_fmeas (R_to_carrier R_carrier_eq r))).
rewrite -[linhom_fun _ _]/(int_to_linhom_fun score_path
                            (dirac_fmeas (R_to_carrier R_carrier_eq r))).
rewrite (int_to_linhom_fun_dirac score_path
           (R_to_carrier R_carrier_eq r)).
rewrite -[path_fun _ _]/(score_path_fun (R_to_carrier R_carrier_eq r)).
rewrite /score_path_fun.
apply: cone_one_eq; apply: val_inj => /=.
by rewrite R_to_carrierK.
Qed.

End ScoreTmLift.

Arguments score_path_fun {R Ar R_obj} R_carrier_eq f Hf_ge0 r.
Arguments score_path {R Ar R_obj R_carrier_eq R_carrier_meas f}
                        Hf_meas Hf_ge0 Hf_le1.
Arguments score_lift {R Ar R_obj R_carrier_eq R_carrier_meas f}
                        Hf_meas Hf_ge0 Hf_le1.
Arguments score_lift_dirac {R Ar R_obj R_carrier_eq R_carrier_meas f}
                              Hf_meas Hf_ge0 Hf_le1 r.

(** ** Boolean Kleisli helpers — constant arrows at [bool_dirac_true],
    [bool_dirac_false], and at a Bernoulli element [(p, 1-p)] of the
    bool cone.

    All three constructors of [tbool] ([ne_true], [ne_false],
    [ne_bernoulli]) are CONSTANT Kleisli arrows: their value does not
    depend on the input environment.  We package each as the
    composition of [tunit_eta (tyD tbool)] with a [const_kleisli]
    delivering the appropriate [bool_cone_car] element.

    The norm-1 facts ([bool_dirac_true_norm], [bool_dirac_false_norm],
    [bernoulli_norm]) all rewrite to [1], so the [≤ 1] bound is
    [lexx].  *)

Section BoolKleisliHelpers.
Variables (R : realType) (Ar : MeasSubcat R).

(** Norm bound for [bool_dirac_true]: norm exactly [1]. *)
Lemma bool_dirac_true_norm_le1 :
    (cone_norm (bool_dirac_true : bool_cone_car Ar) <= 1)%R.
Proof. by rewrite bool_dirac_true_norm. Qed.

(** Norm bound for [bool_dirac_false]: norm exactly [1]. *)
Lemma bool_dirac_false_norm_le1 :
    (cone_norm (bool_dirac_false : bool_cone_car Ar) <= 1)%R.
Proof. by rewrite bool_dirac_false_norm. Qed.

(** [1 - p ≥ 0] from [p ≤ 1] via [subr_ge0]. *)
Lemma onem_ge0 (p : R) (Hp_le1 : (p <= 1)%R) : (0 <= 1 - p)%R.
Proof. by rewrite subr_ge0. Qed.

(** The Bernoulli element [(p, 1-p)] as a [bool_cone_car Ar],
    parameterised by [Hp_ge0 : 0 ≤ p] and [Hp_le1 : p ≤ 1] (the latter
    witnesses [0 ≤ 1-p] via [onem_ge0]). *)
Definition bernoulli (p : R) (Hp_ge0 : (0 <= p)%R) (Hp_le1 : (p <= 1)%R)
    : bool_cone_car Ar :=
  MkBoolCone Ar (NngNum Hp_ge0) (NngNum (onem_ge0 Hp_le1)).

(** Norm-1 fact for [bernoulli]: total mass is [p + (1-p) = 1]. *)
Lemma bernoulli_norm (p : R) (Hp_ge0 : (0 <= p)%R) (Hp_le1 : (p <= 1)%R) :
  cone_norm (bernoulli Hp_ge0 Hp_le1) = 1.
Proof.
rewrite /cone_norm/= /bc_norm /bernoulli/=.
by rewrite addrCA subrr addr0.
Qed.

(** Norm bound for [bernoulli]: norm exactly [1]. *)
Lemma bernoulli_norm_le1 (p : R) (Hp_ge0 : (0 <= p)%R) (Hp_le1 : (p <= 1)%R) :
  (cone_norm (bernoulli Hp_ge0 Hp_le1) <= 1)%R.
Proof. by rewrite bernoulli_norm. Qed.

(** Constant Kleisli arrow at [bool_dirac_true], lifted to [Tobj]. *)
Definition true_kleisli (G : Coalgebra Ar) :
    coalg_hom G (Tobj (bang_cofree (bool_cone_car Ar))) :=
  coalg_comp (tunit_eta (bang_cofree (bool_cone_car Ar)))
             (@const_kleisli _ _ G (bool_cone_car Ar)
                bool_dirac_true bool_dirac_true_norm_le1).

(** Constant Kleisli arrow at [bool_dirac_false], lifted to [Tobj]. *)
Definition false_kleisli (G : Coalgebra Ar) :
    coalg_hom G (Tobj (bang_cofree (bool_cone_car Ar))) :=
  coalg_comp (tunit_eta (bang_cofree (bool_cone_car Ar)))
             (@const_kleisli _ _ G (bool_cone_car Ar)
                bool_dirac_false bool_dirac_false_norm_le1).

(** Constant Kleisli arrow at the Bernoulli element [(p, 1-p)], lifted
    to [Tobj]. *)
Definition bernoulli_kleisli (G : Coalgebra Ar) (p : R)
    (Hp_ge0 : (0 <= p)%R) (Hp_le1 : (p <= 1)%R) :
    coalg_hom G (Tobj (bang_cofree (bool_cone_car Ar))) :=
  coalg_comp (tunit_eta (bang_cofree (bool_cone_car Ar)))
             (@const_kleisli _ _ G (bool_cone_car Ar)
                (bernoulli Hp_ge0 Hp_le1)
                (bernoulli_norm_le1 Hp_ge0 Hp_le1)).

End BoolKleisliHelpers.

Arguments bool_dirac_true_norm_le1 {R Ar}.
Arguments bool_dirac_false_norm_le1 {R Ar}.
Arguments onem_ge0 {R} p Hp_le1.
Arguments bernoulli {R Ar} p Hp_ge0 Hp_le1.
Arguments bernoulli_norm {R Ar} p Hp_ge0 Hp_le1.
Arguments bernoulli_norm_le1 {R Ar} p Hp_ge0 Hp_le1.
Arguments true_kleisli {R Ar} G.
Arguments false_kleisli {R Ar} G.
Arguments bernoulli_kleisli {R Ar} G p Hp_ge0 Hp_le1.

(** ** [case_em] — the EM(!) [if-then-else] combinator

    Given two Kleisli arrows [a, b : G ⇝ Tobj A] (the two branches) and an
    implicit Kleisli bool source [Tobj tbool = bang_cofree (bool_cone_car)],
    we want an EM-Kleisli arrow
    [[
       case_em a b : EM_prod G (bang_cofree (bool_cone_car Ar)) ⇝ Tobj A
    ]]
    that semantically computes [bool_case (der x) (a g) (b g)] for
    [(g, x) ∈ G × bang_cofree bool_cone].

    Structural finding (carried over from the [case_em] plan).  The map
    [(a, b) ↦ bool_case · a · b] is NOT bilinear in [(a, b)]: at the
    icones level [bool_case x (a₁+a₂) b ≠ bool_case x a₁ b + bool_case x
    a₂ b] (a [bc_f·b] discrepancy).  We therefore cannot uncurry the
    bundled branches through a single tensor; instead, we exploit the
    fact that for an [icones_hom h : (coalg_obj G) → !(coalg_obj A)] the
    operator norm is automatically [≤ 1] ([icones_to_linhom_norm_le1]),
    so each [ch_mor a], [ch_mor b] lifts to a NORM-[≤1] point in the
    hom-cone [linhom_car (coalg_obj G) (!(coalg_obj A))].  The
    unit-ball version [bool_case_linhom] of [bool_case_hom.v] then
    delivers a norm-[≤1] [linhom_car (bool_cone_car Ar)
    (linhom_car (coalg_obj G) (!(coalg_obj A)))], which we bridge to an
    [icones_hom] ([linhom_icones]) and SAFT-uncurry ([tensor_uncurry])
    into [tensor (bool_cone_car) (coalg_obj G) → !(coalg_obj A)].  Braid
    and pre-compose with [(id_G ⊗ der_{bool_cone})] to reach the right
    source [(coalg_obj G) ⊗ !(bool_cone_car) → !(coalg_obj A)].
    Finally [adj_psi] wraps this underlying icones_hom as a coalgebra
    morphism into [bang_cofree (coalg_obj A) = Tobj A].

    The [bool_case]/[α + β] decomposition of [bool_case_hom.v] is what
    makes the linhom_car packaging at Step (b) work axiom-free: the two
    branches enter SEPARATELY (each as a unit-ball point in the hom-cone),
    so the bilinearity-in-[(a, b)] obstruction never surfaces. *)
Section CaseEM.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (G A : Coalgebra Ar).
Variables (a b : coalg_hom G (Tobj A)).

(** Branches as norm-[≤1] points in the hom-cone
    [linhom_car (coalg_obj G) (!(coalg_obj A))]. *)
Let a_lh : linhom_car Ar (coalg_obj G) (Bang Ar (coalg_obj A)) :=
  icones_to_linhom (ch_mor a).
Let b_lh : linhom_car Ar (coalg_obj G) (Bang Ar (coalg_obj A)) :=
  icones_to_linhom (ch_mor b).

Lemma case_em_a_lh_norm : (cone_norm a_lh <= 1)%R.
Proof. exact: icones_to_linhom_norm_le1 (ch_mor a). Qed.

Lemma case_em_b_lh_norm : (cone_norm b_lh <= 1)%R.
Proof. exact: icones_to_linhom_norm_le1 (ch_mor b). Qed.

(** Step (b): [bool_case_linhom] at the linhom-cone level. *)
Let case_em_lh : linhom_car Ar (bool_cone_car Ar)
    (linhom_car Ar (coalg_obj G) (Bang Ar (coalg_obj A))) :=
  bool_case_linhom a_lh b_lh case_em_a_lh_norm case_em_b_lh_norm.

Lemma case_em_lh_norm : (cone_norm case_em_lh <= 1)%R.
Proof. exact: bool_case_linhom_norm_le1 a_lh b_lh _ _. Qed.

(** Step (c): bridge to an [icones_hom]. *)
Let case_em_hom : icones_hom Ar (bool_cone_car Ar)
    (linhom_car Ar (coalg_obj G) (Bang Ar (coalg_obj A))) :=
  linhom_icones case_em_lh case_em_lh_norm.

(** Step (d): SAFT uncurry to [bool_cone ⊗ G → !A]. *)
Let case_em_uncurried : icones_hom Ar
    (tensor Ar (bool_cone_car Ar) (coalg_obj G)) (Bang Ar (coalg_obj A)) :=
  tensor_uncurry case_em_hom.

(** Step (e): the full underlying icones_hom [G ⊗ !bool → !A].

    Pre-compose with [id_G ⊗ der_{bool}] (replace [Bg bool] by [bool]),
    then braid [G ⊗ bool → bool ⊗ G] to feed [case_em_uncurried]. *)
Definition case_em_under :
    icones_hom Ar
      (tensor Ar (coalg_obj G) (Bang Ar (bool_cone_car Ar)))
      (Bang Ar (coalg_obj A)) :=
  icones_comp case_em_uncurried
    (icones_comp (iso_fwd (tensor_braid (coalg_obj G) (bool_cone_car Ar)))
                 (tensor_mor (icones_id Ar (coalg_obj G))
                             (der (bool_cone_car Ar)))).

(** The EM-Kleisli combinator: [adj_psi] wraps the underlying icones_hom
    as a coalg morphism, satisfying the [is_coalg_mor] square
    automatically ([adj_psi_is_mor]).

    [U_obj (EM_prod G (bang_cofree (bool_cone_car Ar))) =
     coalg_obj (EM_prod G (bang_cofree (bool_cone_car Ar))) =
     tensor (coalg_obj G) (Bang Ar (bool_cone_car Ar))]; this is the
    underlying icone of [case_em_under], so [adj_psi case_em_under] has
    the right type. *)
(** Bridge to [adj_psi]: [adj_psi] expects an icones_hom into [coalg_obj A]
    (without the outer [!]), so we post-compose [case_em_under] with the
    counit [der (coalg_obj A) : !(coalg_obj A) → coalg_obj A], landing in
    [coalg_obj A] as required.  Note: the [!]-image of this composite is
    what [adj_psi] then takes as the underlying icones_hom of the result
    (via [bang_fmap]), recovering an arrow into [Bang Ar (coalg_obj A) =
    coalg_obj (Tobj A)]. *)
Definition case_em_under_der :
    icones_hom Ar
      (tensor Ar (coalg_obj G) (Bang Ar (bool_cone_car Ar)))
      (coalg_obj A) :=
  icones_comp (der (coalg_obj A)) case_em_under.

Definition case_em :
    coalg_hom (EM_prod G (bang_cofree (bool_cone_car Ar))) (Tobj A) :=
  adj_psi (P := EM_prod G (bang_cofree (bool_cone_car Ar)))
          (B := coalg_obj A) case_em_under_der.

End CaseEM.

Arguments case_em_under {R Ar G A} a b.
Arguments case_em {R Ar G A} a b.

(** ** The term interpretation [eD] *)
Section TermInterp.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Local Notation T := (@ppl_type R Ar).
Local Notation EX G t :=
    (coalg_hom (ctxD (drop_names G)) (Tobj (tyD t))).

(** Helper: Dirac in [FMeas R_obj] has norm exactly [1], hence [≤ 1]. *)
Lemma dirac_fmeas_norm_le1 (r : ar_carrier Ar R_obj) :
    (cone_norm (dirac_fmeas r : FMeas R_obj) <= 1)%R.
Proof. by rewrite dirac_fmeas_norm. Qed.

Definition real_kleisli (G : Coalgebra Ar) (r : R) :
    coalg_hom G (Tobj (FMeas_coalgebra R_obj)) :=
  @const_kleisli _ _ G (FMeas R_obj)
    (dirac_fmeas (R_to_carrier R_carrier_eq r))
    (dirac_fmeas_norm_le1 _).

(** Sample with a unit-ball measure. *)
Definition sample_kleisli (G : Coalgebra Ar) (X : ar_obj Ar)
    (mu : fmeas R (ar_carrier Ar X))
    (Hmu : (cone_norm mu <= 1)%R) :
    coalg_hom G (Tobj (FMeas_coalgebra X)) :=
  @const_kleisli _ _ G (FMeas X) mu Hmu.

(** The denotation of a named expression as a coalgebra (Kleisli)
    morphism.  By structural recursion on [named_expr]; the [ne_var]
    clause runs the named-to-skeletal projection
    [named_var_to_has_var] and then [var_lookup]. *)
Fixpoint eD (G : named_ctx Ar) (t : T)
    (M : @named_expr R Ar R_obj G t) {struct M} : EX G t :=
  match M in named_expr G0 t0 return EX G0 t0 with
  | ne_var _ _ v =>
      coalg_comp (tunit_eta (tyD _))
                 (var_lookup (named_var_to_has_var v))
  | ne_tt G0 =>
      coalg_comp (tunit_eta EM_term) (em_term_mor (ctxD (drop_names G0)))
  | ne_pair G0 t1 t2 M1 M2 =>
      coalg_comp (bang_m (coalg_obj (tyD t1)) (coalg_obj (tyD t2)))
                 (em_pair (eD M1) (eD M2))
  | ne_fst G0 t1 t2 M0 =>
      coalg_comp (Tmap (em_proj1 (tyD t1) (tyD t2))) (eD M0)
  | ne_snd G0 t1 t2 M0 =>
      coalg_comp (Tmap (em_proj2 (tyD t1) (tyD t2))) (eD M0)
  | ne_lam G0 _ t1 t2 body =>
      coalg_comp (tunit_eta (tyD (tfun t1 t2))) (lam_coalg (eD body))
  (* [ne_fix s t1 t2 body]: package the body's denotation
     [eD body : coalg_hom (EM_prod (ctxD G0) (tyD (tfun t1 t2))) (Tobj (tyD (tfun t1 t2)))]
     into [Yfix_fun_T (eD body) : coalg_hom (ctxD G0) (Tobj (tyD (tfun t1 t2)))].
     The fixpoint construction lives in [theories/homs/em_fix.v]. *)
  | ne_fix G0 _ t1 t2 body =>
      Yfix_fun_T (eD body)
  | ne_app G0 t1 t2 Vf Va =>
      kcomp (app_pair (tyD t1) (tyD t2))
        (coalg_comp (bang_m (coalg_obj (tyD (tfun t1 t2))) (coalg_obj (tyD t1)))
                    (em_pair (eD Vf) (eD Va)))
  (* Direct-style CBV [let]: same shape as the old [ne_bind], minus
     the [tprob] marker on the types.  The cone-side definition
     [kbind_ext] is unchanged. *)
  | ne_let G0 _ t1 t2 M0 K =>
      kbind_ext (eD K) (eD M0)
  | ne_sample G0 mu Hmu =>
      @sample_kleisli (ctxD (drop_names G0)) R_obj mu Hmu
  | ne_real G0 r =>
      @real_kleisli (ctxD (drop_names G0)) r
  | ne_score G0 f Hf_meas Hf_ge0 Hf_le1 e0 =>
      coalg_comp
        (bang_cofree_hom
          (@score_lift R Ar R_obj R_carrier_eq R_carrier_meas
                       f Hf_meas Hf_ge0 Hf_le1))
        (eD e0)
  | ne_add G0 M0 N0 =>
      coalg_comp
        (bang_cofree_hom
          (@add_lift R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas))
        (coalg_comp
          (bang_m (FMeas R_obj) (FMeas R_obj))
          (em_pair (eD M0) (eD N0)))
  | ne_mul G0 M0 N0 =>
      coalg_comp
        (bang_cofree_hom
          (@mul_lift R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas))
        (coalg_comp
          (bang_m (FMeas R_obj) (FMeas R_obj))
          (em_pair (eD M0) (eD N0)))
  (* Boolean constants: constant Kleisli arrows at [bool_dirac_true] /
     [bool_dirac_false] : [bool_cone_car Ar].  Built via
     [const_kleisli] then lifted to [Tobj] via [tunit_eta]. *)
  | ne_true G0 =>
      @true_kleisli R Ar (ctxD (drop_names G0))
  | ne_false G0 =>
      @false_kleisli R Ar (ctxD (drop_names G0))
  (* Bernoulli sample: constant Kleisli arrow at [(p, 1-p)] :
     [bool_cone_car Ar].  Total mass is exactly [1], so the unit-ball
     side condition is direct. *)
  | ne_bernoulli G0 p Hp_ge0 Hp_le1 =>
      @bernoulli_kleisli R Ar (ctxD (drop_names G0)) p Hp_ge0 Hp_le1
  (* [if e then M else N]: bind the scrutinee via [kbind_ext]; the
     continuation, in context [G0 ⊗ tyD tbool], dispatches via the
     EM-Kleisli [case_em] combinator on the two branch denotations
     (precomposed with [em_proj1] to drop the bound bool from each
     branch's local context). *)
  | ne_if G0 t e M N =>
      @kbind_ext R Ar (ctxD (drop_names G0)) (bang_cofree (bool_cone_car Ar))
                 (tyD t)
        (case_em (eD M) (eD N))
        (eD e)
  end.

End TermInterp.

Arguments eD {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G t} M.
Arguments real_kleisli {R Ar R_obj R_carrier_eq} G r.
Arguments sample_kleisli {R Ar} G {X} mu Hmu.
Arguments dirac_fmeas_norm_le1 {R Ar R_obj} r.

(** ** Dirac-to-integral lifting — Lemma C (EM-Kleisli convenience)

    A direct EM-Kleisli wrapping of [icones_hom_dirac_to_integral]
    ([theories/homs/coalgebra.v]).  An EM-Kleisli arrow
    [K : FMeas_coalgebra X ⇝ B] is determined on every [µ] by
    integration against the measurable path of its values on Diracs:
    given a measurable path [φ : X → coalg_obj B] that matches [K]
    on every Dirac [δ_r], [Lfun (ch_mor K) µ = ∫φ dµ] for every µ.

    This is purely a renaming of the icones_hom-level lemma applied
    to the underlying [ch_mor K]; it exists so that EM-Kleisli proofs
    don't have to unfold [ch_mor] manually. *)
Section KleisliDiracToIntegral.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

Lemma kleisli_dirac_to_integral
    (X : ar_obj Ar) (B : Coalgebra Ar)
    (K : coalg_hom (FMeas_coalgebra X) B)
    (phi : ar_carrier Ar X -> coalg_obj B)
    (Hphi_path : is_measurable_path (Ar:=Ar) (C:=coalg_obj B) (X:=X) phi)
    (Hphi : forall r, Lfun (ch_mor K) (dirac_fmeas r) = phi r)
    (mu : fmeas R (ar_carrier Ar X)) :
  Lfun (ch_mor K) mu = int_to_linhom_fun (MkPath Hphi_path) mu.
Proof. exact: icones_hom_dirac_to_integral Hphi_path Hphi mu. Qed.

End KleisliDiracToIntegral.

Arguments kleisli_dirac_to_integral
  {R Ar X B} K phi Hphi_path Hphi mu.

(** ** Soundness — definitional [eD] equations + structural laws *)
Section Soundness.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Local Notation EX' G t :=
    (coalg_hom (ctxD (drop_names G)) (Tobj (tyD t))).
Local Notation tR' := (tR R_obj).
Local Notation eD' :=
  (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas).

(** *** Definitional unfoldings of [eD]

    Stated as lemmas so [rewrite] folds them cleanly without an
    aggressive [/=] that would unfold all the categorical packaging. *)

Lemma eD_var (G : named_ctx Ar) (t : ppl_type Ar) (v : named_var G t) :
  eD' (ne_var (R_obj := R_obj) v) =
  coalg_comp (tunit_eta (tyD t)) (var_lookup (named_var_to_has_var v)).
Proof. by []. Qed.

Lemma eD_tt (G : named_ctx Ar) :
  eD' (ne_tt (R_obj := R_obj) (G := G)) =
  coalg_comp (tunit_eta EM_term) (em_term_mor (ctxD (drop_names G))).
Proof. by []. Qed.

Lemma eD_pair (G : named_ctx Ar) (t1 t2 : ppl_type Ar)
    (M : named_expr G t1) (N : named_expr G t2) :
  eD' (ne_pair M N) =
  coalg_comp (bang_m (coalg_obj (tyD t1)) (coalg_obj (tyD t2)))
             (em_pair (eD' M) (eD' N)).
Proof. by []. Qed.

Lemma eD_fst (G : named_ctx Ar) (t1 t2 : ppl_type Ar)
    (M : named_expr G (tprod t1 t2)) :
  eD' (ne_fst M) = coalg_comp (Tmap (em_proj1 (tyD t1) (tyD t2))) (eD' M).
Proof. by []. Qed.

Lemma eD_snd (G : named_ctx Ar) (t1 t2 : ppl_type Ar)
    (M : named_expr G (tprod t1 t2)) :
  eD' (ne_snd M) = coalg_comp (Tmap (em_proj2 (tyD t1) (tyD t2))) (eD' M).
Proof. by []. Qed.

Lemma eD_lam (G : named_ctx Ar) (x : string) (t1 t2 : ppl_type Ar)
    (body : named_expr ((x, t1) :: G) t2) :
  eD' (ne_lam x body) =
  coalg_comp (tunit_eta (tyD (tfun t1 t2))) (lam_coalg (eD' body)).
Proof. by []. Qed.

Lemma eD_app (G : named_ctx Ar) (t1 t2 : ppl_type Ar)
    (F : named_expr G (tfun t1 t2)) (X : named_expr G t1) :
  eD' (ne_app F X) =
  kcomp (app_pair (tyD t1) (tyD t2))
    (coalg_comp (bang_m (coalg_obj (tyD (tfun t1 t2))) (coalg_obj (tyD t1)))
                (em_pair (eD' F) (eD' X))).
Proof. by []. Qed.

(** *** Direct-style [let] reduction

    [ne_let] denotes the extended-context Kleisli bind [kbind_ext];
    this is the same shape as the old [ne_bind] minus the [tprob] tag
    on the types.  No analogue of [eD_ret] survives: in direct style,
    every expression already denotes a Kleisli arrow and there is no
    syntactic [return] constructor. *)
Lemma eD_let (G : named_ctx Ar) (x : string) (t1 t2 : ppl_type Ar)
    (M : named_expr G t1) (K : named_expr ((x, t1) :: G) t2) :
  eD' (ne_let x M K) = kbind_ext (eD' K) (eD' M).
Proof. by []. Qed.

Lemma eD_sample (G : named_ctx Ar)
    (mu : fmeas R (ar_carrier Ar R_obj)) (Hmu : (cone_norm mu <= 1)%R) :
  eD' (ne_sample (R_obj := R_obj) (G := G) mu Hmu) =
  sample_kleisli (ctxD (drop_names G)) mu Hmu.
Proof. by []. Qed.

Lemma eD_real (G : named_ctx Ar) (r : R) :
  eD' (ne_real (G := G) (R_obj := R_obj) r) =
  @real_kleisli _ _ R_obj R_carrier_eq (ctxD (drop_names G)) r.
Proof. by []. Qed.

Lemma eD_score (G : named_ctx Ar)
    (f : R -> R)
    (Hf_meas : measurable_fun [set: R] f)
    (Hf_ge0 : forall r : R, (0 <= f r)%R)
    (Hf_le1 : forall r : R, (f r <= 1)%R)
    (e : named_expr G tR') :
  eD' (ne_score (R_obj := R_obj) f Hf_meas Hf_ge0 Hf_le1 e) =
  coalg_comp
    (bang_cofree_hom
      (@score_lift R Ar R_obj R_carrier_eq R_carrier_meas
                   f Hf_meas Hf_ge0 Hf_le1))
    (eD' e).
Proof. by []. Qed.

Lemma eD_add (G : named_ctx Ar) (M N : named_expr G tR') :
  eD' (ne_add M N) =
  coalg_comp
    (bang_cofree_hom
      (@add_lift R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas))
    (coalg_comp
       (bang_m (FMeas R_obj) (FMeas R_obj))
       (em_pair (eD' M) (eD' N))).
Proof. by []. Qed.

Lemma eD_mul (G : named_ctx Ar) (M N : named_expr G tR') :
  eD' (ne_mul M N) =
  coalg_comp
    (bang_cofree_hom
      (@mul_lift R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas))
    (coalg_comp
       (bang_m (FMeas R_obj) (FMeas R_obj))
       (em_pair (eD' M) (eD' N))).
Proof. by []. Qed.

(** *** Monad laws (re-exported from [cbv.v])

    Stated here in the form [eD] needs them.  These are the [kcomp]
    laws of [theories/programs/cbv.v]: [kcomp_etaR]/[kcomp_etaL]/[kcomp_A].
    The HEADLINE for this file: the analogous laws for [kbind_ext] (the
    extended-context bind used by [e_bind]) are derived from the [kcomp]
    laws plus the strength's interaction with the EM-comonoidal
    structure.  We expose the [kbind_ext] form below. *)

End Soundness.

Arguments eD_var {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G t} v.
Arguments eD_tt {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} G.
Arguments eD_pair {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G t1 t2} M N.
Arguments eD_fst {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G t1 t2} M.
Arguments eD_snd {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G t1 t2} M.
Arguments eD_lam {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G} x {t1 t2} body.
Arguments eD_app {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G t1 t2} F X.
Arguments eD_let {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G} x {t1 t2} M K.
Arguments eD_sample {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G} mu Hmu.
Arguments eD_real {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G} r.
Arguments eD_score
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G f}
  Hf_meas Hf_ge0 Hf_le1 e.
Arguments eD_add {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G} M N.
Arguments eD_mul {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G} M N.

(** ** Variable lookup by string — Saito–Affeldt canonical structures

    The Saito–Affeldt encoding (APLAS 2023 §5.2) uses a tagged structure
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

(** ** Surface notation — custom entry [ppl_named]

    Following Saito–Affeldt §5.3:

      [...]                         enter the named-PPL grammar
      {...}                         escape back to Coq
      let "x" := M in N             direct-style CBV let (= ne_let)
      Sample (mu , Hmu)             sample primitive
      Score { f, Hm, Hg, Hl } e     term-level score primitive
      \ "x" ::: A => M              lambda with named binder of type A
      M @ N                         direct application
      # "x"                         variable lookup by string
      M + N , M * N                 ne_add / ne_mul on tR
      e1 , e2 ; fst e ; snd e ; ()  pairs / projections / unit
      [|r|]                         real literal (= ne_real)

    Note: the PPL is DIRECT-STYLE CBV; the source language does not
    expose the probability monad ([tprob] is gone, [Ret] is gone, [let
    "x" := M in N] desugars to [ne_let], NOT [ne_bind]).  Every
    [named_expr G t]'s denotation is still a Kleisli arrow [ctxD G
    ⇝ tyD t]; the monadic structure is uniformly inside [eD]. *)

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

(** Sample primitive — takes a [(mu, Hmu)] Coq pair.  In the
    direct-style refactor, [ne_sample] produces a pure [tR R_obj]
    expression; the probability monad is unwrapped at the level of
    [eD] only. *)
Notation "'Sample' ( mu , Hmu )" :=
  (ne_sample mu Hmu)
  (in custom ppl_named at level 1, mu constr, Hmu constr).

(** Term-level score primitive — [Score { f , Hf_meas , Hf_ge0 , Hf_le1 } e]:
    score by the measurable function [f : R -> R] applied to the value of
    the named sub-expression [e : named_expr G tR'].
      - braces around the Coq-level measurability witnesses [{ f , Hm , Hg , Hl }];
      - a SURFACE sub-expression [e] outside the braces, parsed in the
        custom entry [ppl_named].
    This matches the [ne_score] constructor one-for-one. *)
Notation "'Score' '{' f ',' Hf_meas ',' Hf_ge0 ',' Hf_le1 '}' e" :=
  (ne_score f Hf_meas Hf_ge0 Hf_le1 e)
  (in custom ppl_named at level 60, e custom ppl_named at level 60,
   f constr, Hf_meas constr, Hf_ge0 constr, Hf_le1 constr,
   right associativity).

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

(** Lambda — [\"x" ::: A => M] : explicit type annotation [A] on the
    binder.  We carry the type explicitly because [ne_lam] needs to
    extend the named context with a [(string, ppl_type)] pair.  We use
    [::] (not [:>]) for the type ascription since [:>] is reserved at
    constr level and would clash with the [x constr] parser. *)
Notation "'\' x ':::' A '=>' M" :=
  (ne_lam x%string (t1 := A) M)
  (in custom ppl_named at level 70, x constr at level 0,
   A constr at level 0,
   M custom ppl_named at level 60, right associativity).

(** OCaml-style [let rec]: [fix s ::: tfun A B in M] binds the
    recursive function [s : tfun A B] in [M : tfun A B].  Only allowed
    when the body has function type ([tfun]). *)
Notation "'fix' s ':::' 'tfun' A B 'in' M" :=
  (ne_fix s%string (t1 := A) (t2 := B) M)
  (in custom ppl_named at level 80, s constr at level 0,
   A constr at level 0, B constr at level 0,
   M custom ppl_named at level 60, right associativity).

(** Direct-style CBV let-binding — [let "x" := M in N] : desugars to
    [ne_let] in the extended named context [(x, _) :: G].  In the
    refactored direct-style PPL, source types are pure; the monadic
    sequencing is hidden inside [eD] (as [kbind_ext]).  The bound-type
    slot is inferred from [M]'s type [t1]. *)
Notation "'let' x ':=' M 'in' N" :=
  (ne_let x%string M N)
  (in custom ppl_named at level 80, x constr at level 0,
   M custom ppl_named at level 70,
   N custom ppl_named at level 80,
   right associativity).

(** ** Boolean surface notations.

    The boolean primitives ([True], [False], [Bernoulli p Hp_ge0
    Hp_le1]) are constants of type [tbool].  [True] / [False] are
    written as keywords; [Bernoulli] follows the [Score { ... }]
    convention of putting the Coq-level non-negativity / unit-ball
    witnesses in braces. *)

(** Boolean true literal — [True] in surface syntax. *)
Notation "'True'" := ne_true (in custom ppl_named at level 0).

(** Boolean false literal — [False] in surface syntax. *)
Notation "'False'" := ne_false (in custom ppl_named at level 0).

(** Bernoulli sampling — [Bernoulli { p, Hp_ge0, Hp_le1 }] returns
    a [tbool] expression. *)
Notation "'Bernoulli' '{' p ',' Hp_ge0 ',' Hp_le1 '}'" :=
  (ne_bernoulli p Hp_ge0 Hp_le1)
  (in custom ppl_named at level 1,
   p constr, Hp_ge0 constr, Hp_le1 constr).

(** [if e then M else N] — boolean elimination in surface syntax.

    The branches [M], [N] are at custom level 80 (so [let] / [\] /
    nested [if] all parse cleanly inside them); the scrutinee [e] is at
    the same level.  Right-associative so [if e1 then if e2 then ...]
    parses as nested-then.  Implicit return type [t] is resolved by the
    bidirectionality hint on [ne_if]. *)
Notation "'if' e 'then' M 'else' N" :=
  (ne_if _ e M N)
  (in custom ppl_named at level 80,
   e custom ppl_named at level 80,
   M custom ppl_named at level 80,
   N custom ppl_named at level 80,
   right associativity).
