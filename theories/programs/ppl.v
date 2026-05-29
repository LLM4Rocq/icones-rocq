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
Require Import Icones.homs.coalgebra.
Require Import Icones.homs.fmeas_lax.
Require Import Icones.homs.em_cat.
Require Import Icones.homs.em_seely_comonoid.
Require Import Icones.homs.em_cartesian.
Require Import Icones.homs.cbv_adjunction.
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
  | tbase (X : ar_obj Ar)
  | tprod (t1 t2 : ppl_type)
  | tfun  (t1 t2 : ppl_type).

End Types.

Arguments ppl_type {R} Ar.
Arguments tunit {R Ar}.
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
      named_expr G tR' -> named_expr G tR' -> named_expr G tR'.

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
Arguments ne_app {R Ar R_obj G t1 t2} & F X.
Arguments ne_let {R Ar R_obj G} x & {t1 t2} M K.
Arguments ne_score {R Ar R_obj G} & f Hf_meas Hf_ge0 Hf_le1 e.
Arguments ne_add {R Ar R_obj G} & M N.
Arguments ne_mul {R Ar R_obj G} & M N.

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

End LamApp.

Arguments lam_under {R Ar G A B} MB.
Arguments lam_coalg {R Ar G A B} MB.
Arguments app_under {R Ar G A B} VF VA.
Arguments app_kleisli {R Ar G A B} VF VA.
Arguments app_pair {R Ar} A B.

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
  end.

End TermInterp.

Arguments eD {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G t} M.
Arguments real_kleisli {R Ar R_obj R_carrier_eq} G r.
Arguments sample_kleisli {R Ar} G {X} mu Hmu.
Arguments dirac_fmeas_norm_le1 {R Ar R_obj} r.

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
