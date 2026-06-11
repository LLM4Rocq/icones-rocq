(**md**************************************************************************)
(** * A higher-order probabilistic PPL — named-variable, direct-style,
       shared surface syntax + shared semantic helpers

    A higher-order probabilistic programming calculus, intrinsically
    typed.  The calculus shape follows the canonical QBS paper PPL
    (Heunen–Kammar–Staton–Yang, "A Convenient Category for Higher-Order
    Probability Theory"); the named-variable surface follows the
    Saito–Affeldt encoding (APLAS 2023 §5.1–§5.3, §6).

    THIS FILE CONTAINS NO INTERPRETER.  It provides the shared surface
    syntax (types [ppl_type], named contexts, the intrinsically-typed
    terms [named_expr Γ τ], the [Custom Entry ppl_named] notation) and
    the measure/arithmetic helpers used by the CBV stack
    ([add_lift] / [mul_lift] / [score_lift] / [const_icones] / the
    boolean-primitive norm bounds).  The interpretation lives in
    [theories/programs/ppl_cbv.v] — the CBV interpreter: linhom-valued
    [eD], comonoid-primitive; types denote [EM(!̃)]-coalgebras with a
    SINGLE outer [!̃] on [tfun A B] = [!̃(U⟦A⟧ ⊸ U⟦B⟧)] (no [Tobj]
    on the codomain — the old Kleisli-exponential design is gone).
    (A call-by-name interpretation stack is preserved on the
    [cbn-track] branch; main is CBV-only.)

    ** Surface calculus — direct style **

    - a single inductive [named_expr Γ τ] indexed by an
      intrinsically-typed, MULTI-VARIABLE named context [Γ :
      named_ctx Ar = seq (string * ppl_type Ar)] and a type [τ :
      ppl_type];
    - DIRECT STYLE (Plotkin/Girard CBV): the source language never
      mentions the probability monad.  Function types are [tfun A B]
      (NOT [tprob (tfun ...)]); there is no [Ret], no [tprob], no
      [bind].  Effects live in the SEMANTICS only;
    - direct-style application [ne_app f x : named_expr Γ B], NOT
      fine-grain Moggi: the user-facing calculus matches the
      Plotkin/Girard textbook CBV calculus;
    - a built-in measurable-space base [tbase X] for [X : ar_obj Ar], a
      unit type, binary products, and the higher-order arrow
      [tfun A B];
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
      interpreted as the constant morphisms at the bool-cone
      Diracs [bool_dirac_true] / [bool_dirac_false] of
      [theories/programs/infra/bool_cone.v].
    - [ne_bernoulli p Hp_ge0 Hp_le1] — sample from a Bernoulli
      distribution: the 2-point sub-probability [(p, 1-p)] on
      [bool_cone] (norm exactly [1]).
    - [ne_bernoulli_f f Hf_meas Hf_ge0 Hf_le1 e] — VALUE-DEPENDENT
      Bernoulli: flip a coin with success probability [f r] where
      [r] is the value of the [tR]-valued sub-expression [e]
      (witness layout mirrors [ne_score]); semantically the
      composite of [eD e] with the path lift [bern_lift]
      ([µ ↦ (∫ f dµ, ∫ (1-f) dµ)]).  The accept/reject primitive
      of [examples.v::ex_reject].

    ** Type, context and term interpretation **

    NOT in this file.  The CBV interpretation ([tyD_cbv] / [ctxD_cbv]
    on the De Bruijn skeleton [drop_names Γ], and the linhom-valued
    [eD]) is in [theories/programs/ppl_cbv.v]; see its header for the
    clause-by-clause recipes.

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
From mathcomp.reals Require Import reals signed constructive_ereal.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import measure dirac_measure.
From mathcomp.analysis Require Import lebesgue_integral_definition.
From mathcomp.analysis Require Import lebesgue_integral_nonneg.

From Stdlib Require Import Strings.String.

Require Import Icones.cones.precone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.cone.
Require Import Icones.cones.cone_cat.
Require Import Icones.programs.infra.bool_cone.
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
Require Import Icones.programs.infra.bool_case_hom.
Require Import Icones.homs.coalgebra.
Require Import Icones.homs.fmeas_lax.
Require Import Icones.homs.em_cat.
Require Import Icones.homs.em_seely_comonoid.
Require Import Icones.homs.em_cartesian.
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

(** ** Free-coalgebra types — types whose [tyD] is (provably) a free
       [!]-coalgebra, hence supports the CBV value-fixpoint construction
       (and so the [ne_fix_mr] mutual-recursion constructor below).

    The predicate [is_free_coalg_type] characterises the surface types
    [τ] whose CBV interpretation [tyD τ] admits a value-fixpoint:

    - [tfun A B]: the base case — [tyD_cbv (tfun A B) = bang_cofree L]
      with [L = U⟦A⟧ ⊸ U⟦B⟧] (no [Tobj] on the codomain).
      Free at the cone [L].

    - [tprod τ1 τ2] WITH BOTH [τi] free-coalgebra: the product of two
      free coalgebras IS a free coalgebra by the Seely iso [Seely2]:
      [tensor (bang_cofree L1) (bang_cofree L2) ≅ bang_cofree (sprod L1
      L2)] ([theories/homs/seely.v]).  This is the constructor that
      ENABLES mutually-recursive function pairs (the construction
      "marche sur les types dont l'interprétation est une coalgèbre
      libre, ce qui inclut aussi les produits de types fonction et permet
      de définir des fonctions mutuellement récursives").

    - All other surface types ([tunit] / [tbool] / [tbase X]) are NOT
      considered "free" here: although technically [tunit]'s
      interpretation is the tensor unit (terminal coalgebra, free at the
      zero cone), the rec-bound name there can only hold the unit value,
      so the constructor is uninteresting; [tbool] and [tbase X] are
      base-type values whose recursive denotation would diverge to the
      cone zero anyway. *)

Section IsFreeCoalgType.
Variable (R : realType) (Ar : MeasSubcat R).

Fixpoint is_free_coalg_type (t : ppl_type Ar) : bool :=
  match t with
  | tfun _ _ => true
  | tprod t1 t2 => is_free_coalg_type t1 && is_free_coalg_type t2
  | _ => false
  end.

End IsFreeCoalgType.

Arguments is_free_coalg_type {R Ar} t.

(** ** Terms — single intrinsically-typed inductive [named_expr Γ τ]

    The user-facing surface syntax is NAMED: contexts carry string
    identifiers at every binding slot and variable lookup is by string.
    Direct-style application [ne_app : named_expr G (tfun t1 t2) ->
    named_expr G t1 -> named_expr G t2] (not Moggi fine-grain) matches
    the QBS-paper calculus shape; effects appear only in the
    interpretation ([ppl_cbv.v]).

    The constructors:
    - [ne_var] : project a value from the named context (via a
      [named_var] witness; the surface notation [#"x"] uses canonical
      structures to BUILD this witness from a string);
    - [ne_tt] : the unit value [()];
    - [ne_pair] / [ne_fst] / [ne_snd] : binary products;
    - [ne_lam] : higher-order lambda — carries a [string] for the
      binder name (body is a [named_expr] in the extended named
      context — IT IS NOT marked as a computation; the effect
      structure is in the SEMANTICS, not the syntax);
    - [ne_app] : DIRECT application;
    - [ne_let] : direct-style CBV sequencer [let x = M in K] — carries
      a [string] for the bound name (this is the Plotkin/Girard CBV
      let; the CBV interpretation is the comonoid-diagonal recipe
      [δ_Γ ; (id_Γ ⊗ ⟦M⟧) ; ⟦K⟧] of [ppl_cbv.v]);
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
  (* Mutual-recursion [let rec] — generalises [ne_fix] from [tfun t1 t2]
     to any body type [t] with [is_free_coalg_type t = true].  The
     surface motivation: a body type [tprod (tfun A1 B1) (tfun A2 B2)]
     denotes a PAIR of functions, and the recursive name [s] can hold
     this pair — so the two components can call each other via [fst #s]
     / [snd #s].  This is MUTUAL RECURSION.

     The CBV interpretation [eD] ([ppl_cbv.v]) dispatches [ne_fix_mr]
     on the body type ([fix_mr_clause]): at [tfun t1 t2] it routes
     through the SAME genuine seeded value-fixpoint combinator
     [fix_comb] of [theories/programs/infra/em_fix_value.v] as
     [ne_fix]; at [tprod]-of-frees it still keeps the legacy
     [Yfix_fun_lin] of [theories/programs/infra/em_fix.v] (provably
     the zero linhom — [em_fix_value.v::Yfix_fun_lin_eq0]) pending the
     Seely transport of [fix_comb] along
     [EM_prod (bang_cofree X) (bang_cofree Y) ≅ bang_cofree (X ⊗ Y)]. *)
  | ne_fix_mr (G : named_ctx Ar) (s : string) (t : T)
              (Hfree : is_free_coalg_type t) :
      named_expr ((s, t) :: G) t -> named_expr G t
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
  (* [Bernoulli_f { f, Hm, Hg, Hl } e] : VALUE-DEPENDENT Bernoulli —
     sample from the 2-point sub-probability [(f r, 1 - f r)] where
     [r] is the value of the [tR']-valued sub-expression [e].  The
     witness layout mirrors [ne_score] one-for-one ([f : R -> R]
     measurable, valued in [[0, 1]]); the CBV denotation post-composes
     [eD e] with the path lift [bern_lift] (Section [BernTmLift]
     below), exactly as [ne_score] post-composes with [score_lift].
     This is the accept/reject primitive of the rejection-sampling
     headline example [examples.v::ex_reject]. *)
  | ne_bernoulli_f (G : named_ctx Ar)
                   (f : R -> R)
                   (Hf_meas : measurable_fun [set: R] f)
                   (Hf_ge0 : forall r : R, (0 <= f r)%R)
                   (Hf_le1 : forall r : R, (f r <= 1)%R)
                   (e : named_expr G tR') : named_expr G tbool
  (* [if e then M else N] — boolean elimination.  [e] is a [tbool]
     expression (semantically a sub-probability distribution on [bool]),
     and [M, N : t] are the two branches.  The CBV denotation [eD]
     dispatches via the universal co-pairing [bool_case_linhom] — see
     [ppl_cbv.v::if_icones]. *)
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
Arguments ne_fix_mr {R Ar R_obj G} s & t Hfree M.
Arguments ne_app {R Ar R_obj G t1 t2} & F X.
Arguments ne_let {R Ar R_obj G} x & {t1 t2} M K.
Arguments ne_score {R Ar R_obj G} & f Hf_meas Hf_ge0 Hf_le1 e.
Arguments ne_add {R Ar R_obj G} & M N.
Arguments ne_mul {R Ar R_obj G} & M N.
Arguments ne_true {R Ar R_obj G}.
Arguments ne_false {R Ar R_obj G}.
Arguments ne_bernoulli {R Ar R_obj G} p Hp_ge0 Hp_le1.
Arguments ne_bernoulli_f {R Ar R_obj G} & f Hf_meas Hf_ge0 Hf_le1 e.
(** Bidirectionality on [ne_if]: resolve [G] and [t] FIRST (from the
    scrutinee and the branches' types), then propagate into the
    sub-expressions.  Same pattern as [ne_let] / [ne_app]. *)
Arguments ne_if {R Ar R_obj G} & t e M N.


(** ** Shared semantic helpers — arithmetic, score, boolean, constants

    These helpers were originally part of the OLD-CBV [eD] machinery in
    [ppl.v].  After the CBV refactor (task #207) the OLD [eD] / Moggi
    apparatus is gone, but the helpers themselves are independent of
    that machinery: they package arithmetic-on-FMeas, term-level
    scoring, constant icones_homs and the boolean primitives' norm
    bounds in a form usable by the CBV stack ([ppl_cbv.v]).  See
    [theories/programs/examples.v] for the surface programs that
    exercise them. *)

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

(** ** Bilinearity at zero for [add_lift] / [mul_lift]

    Both [add_lift] and [mul_lift] factor as [icones_comp]s of two
    [icones_hom]s, hence each is linear in its single packaged argument
    [ptensor x y].  Combined with [ptensor_0r] / [ptensor_0l] (the
    tensor smash-product vanishes on a zero coordinate, paper §5),
    this gives bilinearity at zero:
    [[
       add_lift (x ⊗p 0) = 0  /  add_lift (0 ⊗p y) = 0
       mul_lift (x ⊗p 0) = 0  /  mul_lift (0 ⊗p y) = 0
    ]]
    These identities are load-bearing for the recursive mass-closure
    theorems (notably [ex_geom] in [theories/programs/examples.v]):
    the recursive tail [1 + g()] contributes zero mass when [g] is
    bound to a diverging value [g() = 0], via bilinear [add_lift]. *)

Lemma add_lift_zero_R (x : FMeas R_obj) :
  Lfun add_lift
    (ptensor (B := FMeas R_obj) (C := FMeas R_obj) x precone_zero) =
  precone_zero.
Proof.
rewrite /add_lift.
rewrite -[LHS]/(Lfun (FMeas_fmap add_meas)
  (Lfun (fmeas_lax R_obj R_obj)
    (ptensor (B := FMeas R_obj) (C := FMeas R_obj) x precone_zero))).
have -> : ptensor (B := FMeas R_obj) (C := FMeas R_obj) x precone_zero
        = precone_zero by exact: ptensor_0r.
have [Hfl0 _ _] := cones_hom_linear
  (mcones_hom_cones (icones_hom_mcones (fmeas_lax R_obj R_obj))).
rewrite Hfl0.
have [Hfm0 _ _] := cones_hom_linear
  (mcones_hom_cones (icones_hom_mcones (FMeas_fmap add_meas))).
exact: Hfm0.
Qed.

Lemma add_lift_zero_L (y : FMeas R_obj) :
  Lfun add_lift
    (ptensor (B := FMeas R_obj) (C := FMeas R_obj) precone_zero y) =
  precone_zero.
Proof.
rewrite /add_lift.
rewrite -[LHS]/(Lfun (FMeas_fmap add_meas)
  (Lfun (fmeas_lax R_obj R_obj)
    (ptensor (B := FMeas R_obj) (C := FMeas R_obj) precone_zero y))).
have -> : ptensor (B := FMeas R_obj) (C := FMeas R_obj) precone_zero y
        = precone_zero by exact: ptensor_0l.
have [Hfl0 _ _] := cones_hom_linear
  (mcones_hom_cones (icones_hom_mcones (fmeas_lax R_obj R_obj))).
rewrite Hfl0.
have [Hfm0 _ _] := cones_hom_linear
  (mcones_hom_cones (icones_hom_mcones (FMeas_fmap add_meas))).
exact: Hfm0.
Qed.

Lemma mul_lift_zero_R (x : FMeas R_obj) :
  Lfun mul_lift
    (ptensor (B := FMeas R_obj) (C := FMeas R_obj) x precone_zero) =
  precone_zero.
Proof.
rewrite /mul_lift.
rewrite -[LHS]/(Lfun (FMeas_fmap mul_meas)
  (Lfun (fmeas_lax R_obj R_obj)
    (ptensor (B := FMeas R_obj) (C := FMeas R_obj) x precone_zero))).
have -> : ptensor (B := FMeas R_obj) (C := FMeas R_obj) x precone_zero
        = precone_zero by exact: ptensor_0r.
have [Hfl0 _ _] := cones_hom_linear
  (mcones_hom_cones (icones_hom_mcones (fmeas_lax R_obj R_obj))).
rewrite Hfl0.
have [Hfm0 _ _] := cones_hom_linear
  (mcones_hom_cones (icones_hom_mcones (FMeas_fmap mul_meas))).
exact: Hfm0.
Qed.

Lemma mul_lift_zero_L (y : FMeas R_obj) :
  Lfun mul_lift
    (ptensor (B := FMeas R_obj) (C := FMeas R_obj) precone_zero y) =
  precone_zero.
Proof.
rewrite /mul_lift.
rewrite -[LHS]/(Lfun (FMeas_fmap mul_meas)
  (Lfun (fmeas_lax R_obj R_obj)
    (ptensor (B := FMeas R_obj) (C := FMeas R_obj) precone_zero y))).
have -> : ptensor (B := FMeas R_obj) (C := FMeas R_obj) precone_zero y
        = precone_zero by exact: ptensor_0l.
have [Hfl0 _ _] := cones_hom_linear
  (mcones_hom_cones (icones_hom_mcones (fmeas_lax R_obj R_obj))).
rewrite Hfl0.
have [Hfm0 _ _] := cones_hom_linear
  (mcones_hom_cones (icones_hom_mcones (FMeas_fmap mul_meas))).
exact: Hfm0.
Qed.

Local Open Scope ereal_scope.

(** ** Translation-mass invariance — [add_lift_mass]

    The headline mass identity for the [ex_geom] mass-1 closure:
    [[
       mass(add_lift(δ_a ⊗ m)) = mass(m).
    ]]
    Adding a constant [a] to each sample does not change the total
    mass. This is Fubini + pushforward-mass-preservation.

    Proof outline (Route A — direct).
    1. [add_lift = FMeas_fmap add_meas ∘ fmeas_lax R_obj R_obj] by
       definition. By [fmeas_lax_E], on the pure tensor [δ_a ⊗ m] the
       inner [fmeas_lax R_obj R_obj] reduces to [fmeas_lax_pre δ_a m].
    2. [FMeas_fmap_setT_E]: for any measurable [φ], the pushforward
       [FMeas_fmap φ] preserves total mass: [(FMeas_fmap φ)(ν) setT =
       ν setT]. Proved via the Pettis equation against [fmeas_eU setT]:
       [fmeas_mu (icone_integral (r ↦ δ_(φ r)) _ ν) setT
        = ∫_ν δ_(φ r) setT = ∫_ν 1 = ν setT] by [dirac_fmeas_setT_E]
       and [integral_cst].
    3. [fmeas_lax_pre_setT]: [fmeas_lax_pre (δ_a, m) setT
       = δ_a(setT) · m(setT) = 1 · m(setT) = m(setT)] by
       [dirac_fmeas_setT_E].
    Composing (1), (2), (3) gives the headline. *)

(** Auxiliary: the pushforward [FMeas_fmap φ] preserves total mass.
    For any measurable [φ : X → Y] and any [ν : FMeas X],
    [(FMeas_fmap φ)(ν) setT = ν setT].

    Proved by the Pettis equation against [fmeas_eU setT]: the
    integrand [δ_(φ r) setT] is identically [1] (by [diracT] /
    [dirac_fmeas_setT_E]), so its integral against [ν] is [ν setT]. *)
Lemma FMeas_fmap_setT_E (X Y : ar_obj Ar) (φ : ar_hom Ar X Y)
    (ν : fmeas R (ar_carrier Ar X)) :
  fmeas_mu (Lfun (FMeas_fmap φ) ν) [set: ar_carrier Ar Y] =
  fmeas_mu ν [set: ar_carrier Ar X].
Proof.
(* Step 1.  Unfold [FMeas_fmap] to [int_to_linhom (push_dirac_path φ)]. *)
rewrite /FMeas_fmap (linhom_iconesE _ (FMeas_fmap_norm_le1 φ) ν).
(* Step 2.  Read off the value via [icone_integralP] against
   [fmeas_eU setT]. *)
have mT : measurable [set: ar_carrier Ar Y]
  := @measurableT _ (ar_carrier Ar Y).
set II := linhom_fun (int_to_linhom (push_dirac_path φ)) ν.
have HII_E : II =
    icone_integral (path_fun (push_dirac_path φ))
                   (path_is_path (push_dirac_path φ)) ν.
  by [].
have HP := icone_integralP (path_fun (push_dirac_path φ))
                           (path_is_path (push_dirac_path φ)) ν
             (fmeas_eU (ar_zero Ar) mT)
             (ex_intro _ [set: ar_carrier Ar Y] (ex_intro _ mT erefl))
             (ar_zero_pt Ar).
rewrite /fmeas_eU /eU_fun /= in HP.
rewrite HII_E.
(* Step 3.  Finiteness on both sides. *)
have HIIfin :
    fmeas_mu (icone_integral (path_fun (push_dirac_path φ))
              (path_is_path (push_dirac_path φ)) ν)
              [set: ar_carrier Ar Y] \is a fin_num
  by exact: fmeas_setT_fin.
have HνTfin : fmeas_mu ν [set: ar_carrier Ar X] \is a fin_num
  by exact: fmeas_setT_fin.
(* Step 4.  Reduce the inner integrand via [dirac_fmeas_setT_E].
   [path_fun (push_dirac_path φ) r] is definitionally
   [dirac_fmeas (φ r) : FMeas Y]. *)
have step :
    \int[fmeas_mu ν]_(r in [set: ar_carrier Ar X])
      (fine (fmeas_mu (path_fun (push_dirac_path φ) r)
                      [set: ar_carrier Ar Y]))%:E
    = fmeas_mu ν [set: ar_carrier Ar X].
  under eq_integral => r _.
    have -> : fmeas_mu (path_fun (push_dirac_path φ) r)
                      [set: ar_carrier Ar Y]
            = fmeas_mu (dirac_fmeas (φ r) : FMeas Y)
                       [set: ar_carrier Ar Y]
      by [].
    rewrite dirac_fmeas_setT_E /=.
    over.
  by rewrite integral_cst//= mul1e.
(* Step 5.  Convert the [fine]-form Pettis equation back to ereal. *)
rewrite -(fineK HIIfin) -(fineK HνTfin); congr (_%:E).
rewrite HP.
have step_fin :
    fine (\int[fmeas_mu ν]_(r in [set: ar_carrier Ar X])
      (fine (fmeas_mu (path_fun (push_dirac_path φ) r)
                      [set: ar_carrier Ar Y]))%:E)
    = fine (fmeas_mu ν [set: ar_carrier Ar X])
  by rewrite step.
exact: step_fin.
Qed.

(** Main lemma: translation-mass invariance.

    For any [a : R] and any [m : FMeas R_obj]:
    [[
       mass(add_lift (δ_(R_to_carrier a) ⊗ m)) = mass(m).
    ]]
    Composing [fmeas_lax_E] (the lax pure-tensor identity),
    [FMeas_fmap_setT_E] (pushforward preserves setT), and
    [fmeas_lax_pre_setT] (product-measure total mass) +
    [dirac_fmeas_setT_E] ([δ_a] has unit total mass). *)
Lemma add_lift_mass (a : R) (m : FMeas R_obj) :
  fmeas_mu (Lfun add_lift
             (ptensor (B := FMeas R_obj) (C := FMeas R_obj)
                (dirac_fmeas (R_to_carrier R_carrier_eq a)) m))
           [set: ar_carrier Ar R_obj]
  = fmeas_mu m [set: ar_carrier Ar R_obj].
Proof.
rewrite /add_lift.
(* Step 1.  Decompose [add_lift = FMeas_fmap add_meas ∘ fmeas_lax]. *)
rewrite -[LHS]/(fmeas_mu (Lfun (FMeas_fmap add_meas)
  (Lfun (fmeas_lax R_obj R_obj)
    (ptensor (B := FMeas R_obj) (C := FMeas R_obj)
       (dirac_fmeas (R_to_carrier R_carrier_eq a)) m)))
  [set: ar_carrier Ar R_obj]).
(* Step 2.  [fmeas_lax_E]: pure-tensor identity. *)
rewrite (fmeas_lax_E (dirac_fmeas (R_to_carrier R_carrier_eq a)) m).
(* Step 3.  [FMeas_fmap_setT_E]: pushforward preserves setT. *)
rewrite FMeas_fmap_setT_E.
(* Step 4.  [fmeas_lax_pre_setT]: total mass of the product measure. *)
rewrite fmeas_lax_pre_setT.
(* Step 5.  [δ_a] has unit total mass. *)
by rewrite dirac_fmeas_setT_E mul1e.
Qed.

Local Close Scope ereal_scope.

End Arith.

Arguments add_fun {R Ar R_obj} R_carrier_eq p.
Arguments mul_fun {R Ar R_obj} R_carrier_eq p.
Arguments add_meas {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}.
Arguments mul_meas {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}.
Arguments add_lift {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}.
Arguments mul_lift {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}.
Arguments add_lift_dirac {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} a b.
Arguments mul_lift_dirac {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} a b.
Arguments add_lift_zero_R {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} x.
Arguments add_lift_zero_L {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} y.
Arguments mul_lift_zero_R {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} x.
Arguments mul_lift_zero_L {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} y.
Arguments add_lift_mass {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} a m.


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

Section ConstIcones.
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

End ConstIcones.

Arguments lin_pt_norm_le1 {R Ar C} c Hc.
Arguments const_icones {R Ar} G {C} c Hc.

Section NormHelpers.
Variables (R : realType) (Ar : MeasSubcat R).

(** [precone_zero] in any [ICone.type Ar] has cone-norm 0, hence ≤ 1. *)
Lemma precone_zero_norm_le1 (P : ICone.type Ar) :
  (cone_norm (precone_zero : P) <= 1)%R.
Proof. by rewrite cone_norm0 ler01. Qed.

(** Dirac in [FMeas X] has norm exactly [1], hence [≤ 1]. *)
Lemma dirac_fmeas_norm_le1 (X : ar_obj Ar) (r : ar_carrier Ar X) :
    (cone_norm (dirac_fmeas r : FMeas X) <= 1)%R.
Proof. by rewrite dirac_fmeas_norm. Qed.

End NormHelpers.

Arguments precone_zero_norm_le1 {R Ar} P.
Arguments dirac_fmeas_norm_le1 {R Ar X} r.

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

End BoolKleisliHelpers.

Arguments bool_dirac_true_norm_le1 {R Ar}.
Arguments bool_dirac_false_norm_le1 {R Ar}.
Arguments onem_ge0 {R} p Hp_le1.
Arguments bernoulli {R Ar} p Hp_ge0 Hp_le1.
Arguments bernoulli_norm {R Ar} p Hp_ge0 Hp_le1.
Arguments bernoulli_norm_le1 {R Ar} p Hp_ge0 Hp_le1.

(** ** [bern_lift] — the value-dependent Bernoulli lift

    The semantic engine of [ne_bernoulli_f]: an [icones_hom
    (FMeas R_obj) (bool_cone_car Ar)] sending a measure [µ] on the
    reals to the 2-point sub-probability
    [[
        (∫ f dµ, ∫ (1 - f) dµ)
    ]]
    — sample [r ~ µ], then flip a coin with success probability
    [f r].  Construction is the PATH route, a verbatim clone of
    [Section ScoreTmLift]: package [r ↦ bernoulli (f (cR r))] as a
    measurable path into [bool_cone_car Ar] (the three tests of the
    bool cone evaluate along the path to [f∘cR], [1 - f∘cR] and the
    constant [1]), then promote with [int_to_linhom].  The integral
    semantics is automatic by Pettis uniqueness against the
    componentwise integral [bool_int] of
    [theories/programs/infra/bool_cone.v] ([bern_lift_E]); the
    Dirac identity ([bern_lift_dirac]) and total-mass identity
    ([bern_lift_mass]: the lift preserves total mass — the coin is
    NORM-1 pointwise) are the load-bearing laws for the
    rejection-sampling headline. *)

Section BernTmLift.
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

(** The path value at [r] : the Bernoulli element
    [(f (cR r), 1 - f (cR r))]. *)
Definition bern_path_fun (r : ar_carrier Ar R_obj) : bool_cone_car Ar :=
  bernoulli (f (cR r)) (Hf_ge0 (cR r)) (Hf_le1 (cR r)).

(** Pointwise the path is NORM-1 exactly (the coin always lands). *)
Lemma bern_path_fun_norm (r : ar_carrier Ar R_obj) :
  cone_norm (bern_path_fun r) = 1%R.
Proof. exact: bernoulli_norm. Qed.

(** Composite [f ∘ cR] is measurable (clone of [f_cR_meas]). *)
Lemma bern_f_cR_meas :
  measurable_fun [set: ar_carrier Ar R_obj] (fun r => f (cR r)).
Proof.
apply: (measurableT_comp (f := f)).
- exact: Hf_meas.
- exact: R_carrier_meas.
Qed.

(** [bern_path_fun] is a measurable path.  The tests of
    [bool_cone_car] are the three tags [π_t] / [π_f] / norm
    ([bool_cone.v::mcone_M_bool]); along the path they evaluate to
    [(z,r) ↦ f (cR r)], [(z,r) ↦ 1 - f (cR r)] and
    [(z,r) ↦ f (cR r) + (1 - f (cR r))], all measurable. *)
Lemma bern_path_is_path :
  is_measurable_path (Ar := Ar) (C := bool_cone_car Ar) (X := R_obj)
    bern_path_fun.
Proof.
split.
  by exists 1%R => r; rewrite bern_path_fun_norm.
move=> Y m [o _ <-].
have meas_snd :
    measurable_fun
      [set: (ar_carrier Ar Y * ar_carrier Ar R_obj)%type]
      (fun p : (ar_carrier Ar Y * ar_carrier Ar R_obj)%type =>
         f (cR p.2)).
  apply: (measurableT_comp (f := fun r => f (cR r))).
  - exact: bern_f_cR_meas.
  - exact: measurable_snd.
have meas_onem :
    measurable_fun
      [set: (ar_carrier Ar Y * ar_carrier Ar R_obj)%type]
      (fun p : (ar_carrier Ar Y * ar_carrier Ar R_obj)%type =>
         (1 - f (cR p.2))%R).
  by apply: measurable_funB; [exact: measurable_cst | exact: meas_snd].
rewrite /BoolConeMConeAux.bool_test/= /BoolConeMConeAux.bool_test_fun
        /BoolConeMConeAux.bc_test_val /bern_path_fun /bernoulli/=.
case: o => [[]|]/=.
- exact: meas_snd.
- exact: meas_onem.
- exact: measurable_funD meas_snd meas_onem.
Qed.

Definition bern_path : path_car Ar R_obj (bool_cone_car Ar) :=
  MkPath bern_path_is_path.

(** Path-norm bound: the path values are all of norm [1], so the sup
    is [≤ 1]. *)
Lemma bern_path_norm_le1 : (path_norm bern_path <= 1)%R.
Proof.
apply: ge_sup; first exact: path_normset_nonempty.
by move=> _ [r ->] /=; rewrite bern_path_fun_norm.
Qed.

(** Norm bound for [int_to_linhom bern_path]. *)
Lemma bern_int_norm_le1 :
  (cone_norm (int_to_linhom bern_path) <= 1)%R.
Proof.
apply: le_trans (int_to_linhom_norm_le bern_path) _.
exact: bern_path_norm_le1.
Qed.

(** The lift as an [icones_hom]. *)
Definition bern_lift :
    icones_hom Ar (FMeas R_obj) (bool_cone_car Ar) :=
  linhom_icones (int_to_linhom bern_path) bern_int_norm_le1.

(** **** Load-bearing Dirac identity.

    On a Dirac at [R_to_carrier r] in [FMeas R_obj], the lift
    evaluates to the Bernoulli element [(f r, 1 - f r)]. *)
Lemma bern_lift_dirac (r : R) :
  Lfun bern_lift (dirac_fmeas (R_to_carrier R_carrier_eq r)) =
  bernoulli (f r) (Hf_ge0 r) (Hf_le1 r).
Proof.
rewrite /bern_lift.
rewrite (linhom_iconesE _ bern_int_norm_le1
           (dirac_fmeas (R_to_carrier R_carrier_eq r))).
rewrite -[linhom_fun _ _]/(int_to_linhom_fun bern_path
                            (dirac_fmeas (R_to_carrier R_carrier_eq r))).
rewrite (int_to_linhom_fun_dirac bern_path
           (R_to_carrier R_carrier_eq r)).
rewrite -[path_fun _ _]/(bern_path_fun (R_to_carrier R_carrier_eq r)).
rewrite /bern_path_fun /bernoulli.
by apply: bool_cone_eq; apply: val_inj => /=; rewrite R_to_carrierK.
Qed.

Local Open Scope ereal_scope.

(** **** The integral identity, via Pettis uniqueness.

    [bern_lift µ] IS the componentwise integral [bool_int] of
    [bool_cone.v]: both satisfy the Pettis equation
    [path_integral_eq bern_path_fun µ], which has a unique
    solution. *)
Lemma bern_lift_E (mu : fmeas R (ar_carrier Ar R_obj)) :
  Lfun bern_lift mu = bool_int bern_path_is_path mu.
Proof.
rewrite /bern_lift (linhom_iconesE _ bern_int_norm_le1 mu).
rewrite -[linhom_fun _ _]/(int_to_linhom_fun bern_path mu).
rewrite /int_to_linhom_fun.
apply/esym/icone_integral_eqP.
exact: bool_int_pettis.
Qed.

(** Coordinate readings: the [true]-coordinate is [∫ f dµ] … *)
Lemma bern_lift_t_E (mu : fmeas R (ar_carrier Ar R_obj)) :
  ((bc_t (Lfun bern_lift mu))%:num)%R =
  fine (\int[fmeas_mu mu]_(r in [set: ar_carrier Ar R_obj])
          (f (cR r))%:E).
Proof. by rewrite bern_lift_E. Qed.

(** … and the [false]-coordinate is [∫ (1 - f) dµ]. *)
Lemma bern_lift_f_E (mu : fmeas R (ar_carrier Ar R_obj)) :
  ((bc_f (Lfun bern_lift mu))%:num)%R =
  fine (\int[fmeas_mu mu]_(r in [set: ar_carrier Ar R_obj])
          ((1 - f (cR r))%R)%:E).
Proof. by rewrite bern_lift_E. Qed.

(** **** Total-mass identity.

    The lift preserves total mass: the coin is norm-1 pointwise, so
    [‖bern_lift µ‖ = ∫ (f + (1-f)) dµ = µ(setT)].  (For the
    rejection-sampling headline: with [‖µ‖ = 1], the reject weight is
    [1 - ∫ f dµ].) *)
Lemma bern_lift_mass (mu : fmeas R (ar_carrier Ar R_obj)) :
  cone_norm (Lfun bern_lift mu) =
  fine (fmeas_mu mu [set: ar_carrier Ar R_obj]).
Proof.
rewrite bern_lift_E.
have fin_t : \int[fmeas_mu mu]_(r in [set: ar_carrier Ar R_obj])
               (f (cR r))%:E \is a fin_num
  by exact: (bool_int_fin bern_path_is_path mu true).
have fin_f : \int[fmeas_mu mu]_(r in [set: ar_carrier Ar R_obj])
               ((1 - f (cR r))%R)%:E \is a fin_num
  by exact: (bool_int_fin bern_path_is_path mu false).
have meas_t : measurable_fun [set: ar_carrier Ar R_obj]
                (fun r => (f (cR r))%:E)
  by exact: (bool_coord_meas bern_path_is_path true).
have meas_f : measurable_fun [set: ar_carrier Ar R_obj]
                (fun r => ((1 - f (cR r))%R)%:E)
  by exact: (bool_coord_meas bern_path_is_path false).
rewrite -[cone_norm _]/(((bc_t (bool_int bern_path_is_path mu))%:num
                       + (bc_f (bool_int bern_path_is_path mu))%:num)%R).
rewrite -[((bc_t (bool_int bern_path_is_path mu))%:num)%R]/(fine
  (\int[fmeas_mu mu]_(r in [set: ar_carrier Ar R_obj]) (f (cR r))%:E)).
rewrite -[((bc_f (bool_int bern_path_is_path mu))%:num)%R]/(fine
  (\int[fmeas_mu mu]_(r in [set: ar_carrier Ar R_obj])
      ((1 - f (cR r))%R)%:E)).
rewrite -fineD//.
rewrite -ge0_integralD//; first last.
- by move=> r _; rewrite lee_fin subr_ge0.
- by move=> r _; rewrite lee_fin.
under eq_integral => r _.
  rewrite -EFinD addrCA subrr addr0.
  over.
by rewrite integral_cst//= mul1e.
Qed.

End BernTmLift.

Arguments bern_path_fun {R Ar R_obj} R_carrier_eq f Hf_ge0 Hf_le1 r.
Arguments bern_path {R Ar R_obj R_carrier_eq R_carrier_meas f}
                       Hf_meas Hf_ge0 Hf_le1.
Arguments bern_path_is_path {R Ar R_obj R_carrier_eq R_carrier_meas f}
                               Hf_meas Hf_ge0 Hf_le1.
Arguments bern_lift {R Ar R_obj R_carrier_eq R_carrier_meas f}
                       Hf_meas Hf_ge0 Hf_le1.
Arguments bern_lift_dirac {R Ar R_obj R_carrier_eq R_carrier_meas f}
                             Hf_meas Hf_ge0 Hf_le1 r.
Arguments bern_lift_E {R Ar R_obj R_carrier_eq R_carrier_meas f}
                         Hf_meas Hf_ge0 Hf_le1 mu.
Arguments bern_lift_t_E {R Ar R_obj R_carrier_eq R_carrier_meas f}
                           Hf_meas Hf_ge0 Hf_le1 mu.
Arguments bern_lift_f_E {R Ar R_obj R_carrier_eq R_carrier_meas f}
                           Hf_meas Hf_ge0 Hf_le1 mu.
Arguments bern_lift_mass {R Ar R_obj R_carrier_eq R_carrier_meas f}
                            Hf_meas Hf_ge0 Hf_le1 mu.


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
    [named_expr G t]'s CBV denotation is a linear morphism
    [U⟦Γ⟧ ⊸ U⟦t⟧] ([ppl_cbv.v::eD]); effects live in the semantics,
    not the syntax. *)

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

(** Mutual-recursion [let rec]: [fix_mr s 'as' T 'by' Hfree 'in' M]
    binds the recursive name [s : T] in [M : T], for any body type [T]
    satisfying [is_free_coalg_type T = true].  [Hfree] is the Coq-level
    witness (typically [erefl] at concrete shapes). *)
Notation "'fix_mr' s 'as' T 'by' Hfree 'in' M" :=
  (ne_fix_mr s%string T Hfree M)
  (in custom ppl_named at level 80, s constr at level 0,
   T constr at level 0, Hfree constr at level 0,
   M custom ppl_named at level 60, right associativity).

(** Direct-style CBV let-binding — [let "x" := M in N] : desugars to
    [ne_let] in the extended named context [(x, _) :: G].  In the
    direct-style PPL, source types are pure; the CBV sequencing is the
    comonoid-diagonal recipe [δ_Γ ; (id_Γ ⊗ ⟦M⟧) ; ⟦N⟧] inside [eD]
    ([ppl_cbv.v]).  The bound-type slot is inferred from [M]'s type
    [t1]. *)
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

(** Value-dependent Bernoulli —
    [Bernoulli_f { f , Hf_meas , Hf_ge0 , Hf_le1 } e]: flip a coin
    whose success probability is [f] applied to the value of the
    [tR]-typed surface sub-expression [e].  Same shape as the
    [Score { … } e] notation (Coq-level witnesses in braces, surface
    scrutinee outside); the leading keyword [Bernoulli_f] is distinct
    from [Bernoulli], so the two grammars do not conflict. *)
Notation "'Bernoulli_f' '{' f ',' Hf_meas ',' Hf_ge0 ',' Hf_le1 '}' e" :=
  (ne_bernoulli_f f Hf_meas Hf_ge0 Hf_le1 e)
  (in custom ppl_named at level 60, e custom ppl_named at level 60,
   f constr, Hf_meas constr, Hf_ge0 constr, Hf_le1 constr,
   right associativity).

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
