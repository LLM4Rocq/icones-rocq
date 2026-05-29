(**md**************************************************************************)
(** * A higher-order probabilistic PPL — single-sort, direct-style, multi-var
       De Bruijn, with Kleisli-exponential semantics in [EM(!)]

    This file ports the canonical mathcomp-qbs higher-order PPL
    ([mathcomp-qbs/theories/ppl_qbs.v] + [showcase/ppl_examples.v]) to the
    integrable-cones model, with the SAME calculus shape as the QBS port:

    - a single inductive [expr Γ τ] indexed by an intrinsically-typed,
      MULTI-VARIABLE De Bruijn context [Γ : ppl_ctx] and a type [τ :
      ppl_type];
    - direct-style application [e_app f x : expr Γ B], NOT fine-grain Moggi:
      the user-facing calculus matches a textbook QBS-style PPL, while the
      interpretation goes through the same EM(!)-Kleisli-exponential chain as
      [theories/programs/cbv.v] (= [Tobj = !̃ ∘ U]);
    - monadic [e_ret] / [e_bind] returning to the probability type [tprob τ];
    - a built-in measurable-space base [tbase X] for [X : ar_obj Ar], a unit
      type, binary products, and the higher-order arrow [tfun A B] = [!̃(U A
      ⊸ U B)] (the Kleisli exponential of the CBV computation monad).

    ** The mathematical framework **

    Identical to [theories/programs/cbv.v]: the value category is the FULL
    Eilenberg–Moore category [EM(!)] of the exponential comonad
    ([em_cartesian.v]); the CBV computation monad is [T = !̃ ∘ U]
    ([Tobj] in [cbv.v]).  The Kleisli exponential for [T] gives the
    higher-order arrow type denotation
    [[
        ⟦tfun A B⟧ := !̃(U A ⊸ U B)
                    = bang_cofree (linhom_car Ar (coalg_obj ⟦A⟧)
                                                 (coalg_obj ⟦B⟧)).
    ]]
    See the header of [cbv.v] for the full discussion of the
    natural-bijection chain [Hom_EM(C×A, T B) ≅ Hom_EM(C, !̃(U A ⊸ U B))]
    realising lambda + application.

    ** Headline example — [ex_random_constant] **

    [[
        ex_random_constant ≜
          e_bind (e_sample µ) (e_ret (e_lam (e_var (hv_succ hv_zero))))
                : expr [] (tprob (tfun tR tR))
    ]]
    in the empty context: draw [c ~ µ : FMeas R], then return the constant
    function [λx.c] (whose body is the OUTER-bound variable, hence
    [hv_succ hv_zero] in the lambda body).  This is the QBS-paper-flagship
    "distribution over a function space" example, recovered here in the
    EM(!) Kleisli-exponential discipline.

    The three names [ex_random_constant], [ex_random_constant_denot] and
    [ex_random_constant_denot_E] are preserved (the README / blueprint /
    AUDITOR.md reference them). *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import measure dirac_measure.

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
  | tfun  (t1 t2 : ppl_type)
  | tprob (t : ppl_type).

End Types.

Arguments ppl_type {R} Ar.
Arguments tunit {R Ar}.
Arguments tbase {R Ar} X.
Arguments tprod {R Ar} t1 t2.
Arguments tfun {R Ar} t1 t2.
Arguments tprob {R Ar} t.

(** ** Contexts and De Bruijn variable witnesses *)

Section Contexts.
Variable (R : realType) (Ar : MeasSubcat R).

Definition ppl_ctx : Type := list (ppl_type Ar).

(** [has_var G t]: a witness of "[t] is somewhere in [G]".  Intrinsic De
    Bruijn index: [hv_zero] points to the HEAD, [hv_succ] skips it. *)
Inductive has_var : ppl_ctx -> ppl_type Ar -> Type :=
  | hv_zero (G : ppl_ctx) (t : ppl_type Ar) : has_var (t :: G) t
  | hv_succ (G : ppl_ctx) (t s : ppl_type Ar) :
      has_var G t -> has_var (s :: G) t.

End Contexts.

Arguments ppl_ctx {R} Ar.
Arguments has_var {R Ar} G t.
Arguments hv_zero {R Ar G t}.
Arguments hv_succ {R Ar G t s} v.

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

(** ** Terms — single intrinsically-typed inductive [expr Γ τ]

    Notice we use DIRECT-style application [e_app : expr G (tfun t1 t2) ->
    expr G t1 -> expr G t2] (not Moggi fine-grain), matching the QBS-paper
    calculus shape; the Moggi monadic structure is uncovered by [eD] via the
    Kleisli-exponential chain.

    The constructors:
    - [e_var] : project a value from the De Bruijn context;
    - [e_tt] : the unit value [()];
    - [e_pair] / [e_fst] / [e_snd] : binary products;
    - [e_lam] : higher-order lambda (body is an [expr] in the extended
      context — IT IS NOT marked as a computation; the Moggi/Kleisli
      structure is in the SEMANTICS, not the syntax);
    - [e_app] : DIRECT application;
    - [e_ret] : monadic return [tprob t];
    - [e_bind] : monadic bind [do x <- m; k];
    - [e_sample] : sample from a fixed measure [µ : FMeas X] in the unit
      ball (the constructor carries the cone-norm bound [Hmu : ‖µ‖ ≤ 1]
      that the [linhom_icones]-wrapping needs);
    - [e_real] : real literal [r : R] of type [tR] (the Dirac at [r] has
      unit norm — no bound proof needed);
    - [e_score] : score by [r : R] with [0 ≤ r ≤ 1] proofs, returning
      [tprob tunit];
    - [e_score_tm] : TERM-LEVEL score by [f r : R] where [r] is the
      value of an [expr G tR]; the meta-parameter [f : R → R] is
      measurable and pointwise in [[0,1]] (the bound is needed by
      the cone-norm / unit-ball discipline of [linhom_icones]).  This
      is the constructor that makes Bayesian-style observation
      actually possible: the score factor can depend on a bound
      variable through [e];
    - [e_add] : pointwise sum of two [tR]-valued computations
      (interpretation: lax-monoidal pairing of the two pushforwards
      followed by [FMeas]-functorial action of measurable [+]);
    - [e_mul] : pointwise product, analogous to [e_add]. *)
Section Syntax.
Variable (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.

Local Notation tR' := (tR R_obj).
Local Notation T := (@ppl_type R Ar).

Inductive expr : ppl_ctx Ar -> T -> Type :=
  | e_var   (G : ppl_ctx Ar) (t : T) :
      has_var G t -> expr G t
  | e_tt    (G : ppl_ctx Ar) : expr G tunit
  | e_pair  (G : ppl_ctx Ar) (t1 t2 : T) :
      expr G t1 -> expr G t2 -> expr G (tprod t1 t2)
  | e_fst   (G : ppl_ctx Ar) (t1 t2 : T) :
      expr G (tprod t1 t2) -> expr G t1
  | e_snd   (G : ppl_ctx Ar) (t1 t2 : T) :
      expr G (tprod t1 t2) -> expr G t2
  | e_lam   (G : ppl_ctx Ar) (t1 t2 : T) :
      expr (t1 :: G) t2 -> expr G (tfun t1 t2)
  | e_app   (G : ppl_ctx Ar) (t1 t2 : T) :
      expr G (tfun t1 t2) -> expr G t1 -> expr G t2
  | e_ret   (G : ppl_ctx Ar) (t : T) :
      expr G t -> expr G (tprob t)
  | e_bind  (G : ppl_ctx Ar) (t1 t2 : T) :
      expr G (tprob t1) -> expr (t1 :: G) (tprob t2) ->
      expr G (tprob t2)
  | e_sample (G : ppl_ctx Ar) (X : ar_obj Ar)
             (mu : fmeas R (ar_carrier Ar X))
             (Hmu : (cone_norm mu <= 1)%R) :
      expr G (tprob (tbase X))
  | e_real  (G : ppl_ctx Ar) (r : R) : expr G tR'
  | e_score (G : ppl_ctx Ar) (r : R)
            (Hr0 : (0 <= r)%R) (Hr1 : (r <= 1)%R) :
      expr G (tprob tunit)
  | e_score_tm (G : ppl_ctx Ar)
               (f : R -> R)
               (Hf_meas : measurable_fun [set: R] f)
               (Hf_ge0 : forall r : R, (0 <= f r)%R)
               (Hf_le1 : forall r : R, (f r <= 1)%R)
               (e : expr G tR') : expr G (tprob tunit)
  | e_add   (G : ppl_ctx Ar) : expr G tR' -> expr G tR' -> expr G tR'
  | e_mul   (G : ppl_ctx Ar) : expr G tR' -> expr G tR' -> expr G tR'.

End Syntax.

Arguments expr {R Ar R_obj} G t.
Arguments e_var {R Ar R_obj G t} v.
Arguments e_tt {R Ar R_obj G}.
Arguments e_pair {R Ar R_obj G t1 t2} M N.
Arguments e_fst {R Ar R_obj G t1 t2} M.
Arguments e_snd {R Ar R_obj G t1 t2} M.
Arguments e_lam {R Ar R_obj G t1 t2} M.
Arguments e_app {R Ar R_obj G t1 t2} F X.
Arguments e_ret {R Ar R_obj G t} M.
Arguments e_bind {R Ar R_obj G t1 t2} M K.
Arguments e_sample {R Ar R_obj G X} mu Hmu.
Arguments e_real {R Ar R_obj G} r.
Arguments e_score {R Ar R_obj G} r Hr0 Hr1.
Arguments e_score_tm {R Ar R_obj G} f Hf_meas Hf_ge0 Hf_le1 e.
Arguments e_add {R Ar R_obj G} M N.
Arguments e_mul {R Ar R_obj G} M N.

(** ** Type and context interpretation [tyD] / [ctxD]

    Every type denotes a coalgebra of [EM(!)]:
    [[
       ⟦tunit⟧       = EM_term
       ⟦tbase X⟧     = FMeas_coalgebra X         (Theorem 9.7)
       ⟦tprod t1 t2⟧ = EM_prod ⟦t1⟧ ⟦t2⟧
       ⟦tfun  t1 t2⟧ = !̃(U⟦t1⟧ ⊸ U⟦t2⟧)         (Kleisli exponential of [T])
       ⟦tprob t⟧     = ⟦t⟧.
    ]]
    The [tprob] marker is SYNTACTIC: every expression is interpreted
    uniformly through the CBV computation monad [T = !̃ ∘ U] (every
    [⟦expr G t⟧ ∈ coalg_hom (ctxD G) (Tobj (tyD t))]), and the
    [e_ret]/[e_bind]/[e_sample]/etc. constructors all participate in
    that monadic shape.  The [tprob] marker at the TYPE level does NOT
    add a further [Tobj]: that would be a double-monad and is not what
    the calculus intends.

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
  | tfun A B => bang_cofree (linhom_car Ar (coalg_obj (tyD A))
                                          (coalg_obj (tyD B)))
  (* [tprob t] is the SYNTACTIC marker for "this is a computation in
     the probability monad".  Semantically every expression is
     interpreted through the monad uniformly ([eD] wraps EVERY
     denotation in [Tobj]), so [tyD (tprob t) = tyD t]: the [tprob]
     marker does NOT add an extra layer of [Tobj] at the type-level
     interpretation.  The monadic structure is in [eD], not [tyD]. *)
  | tprob t0 => tyD t0
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

(** Lambda — LEFT to RIGHT through the Kleisli-exponential chain.  Given
    a body [coalg_hom (EM_prod G A) (Tobj B)], produce
    [coalg_hom G (tyD (tfun A B))] = [coalg_hom G (!̃(U A ⊸ U B))]. *)
Definition lam_under (G A B : Coalgebra Ar)
    (MB : coalg_hom (EM_prod G A) (Tobj B)) :
    icones_hom Ar (coalg_obj G)
      (linhom_car Ar (coalg_obj A) (coalg_obj B)) :=
  tensor_curry (adj_phi MB).

Definition lam_coalg (G A B : Coalgebra Ar)
    (MB : coalg_hom (EM_prod G A) (Tobj B)) :
    coalg_hom G (bang_cofree (linhom_car Ar (coalg_obj A) (coalg_obj B))) :=
  adj_psi (lam_under MB).

(** Application — RIGHT to LEFT through the chain.  Given a value of the
    function type and a value of the argument type, produce a Kleisli
    arrow [G ⇝ B].  Both VF and VA are VALUES (coalgebra morphisms), NOT
    computations — this is the "value" form of application, used INSIDE
    [app_pair] below to actually fire the closure at a pair. *)
Definition app_under (G A B : Coalgebra Ar)
    (VF : coalg_hom G
            (bang_cofree (linhom_car Ar (coalg_obj A) (coalg_obj B))))
    (VA : coalg_hom G A) :
    icones_hom Ar (coalg_obj G) (coalg_obj B) :=
  icones_comp (tensor_uncurry (adj_phi VF))
    (icones_comp (tensor_mor (icones_id Ar (coalg_obj G)) (ch_mor VA))
                 (coalg_d G)).

Definition app_kleisli (G A B : Coalgebra Ar)
    (VF : coalg_hom G
            (bang_cofree (linhom_car Ar (coalg_obj A) (coalg_obj B))))
    (VA : coalg_hom G A) :
    coalg_hom G (Tobj B) :=
  adj_psi (app_under VF VA).

(** *** [app_pair] — the Kleisli "evaluate" arrow on a value pair

    Given a pair value [(f, a) : EM_prod (tfun A B) A], project the
    components and apply [app_kleisli].  This is the continuation used to
    interpret direct-style application as monadic application after both
    [f] and [a] have been EVALUATED to values. *)
Definition app_pair (A B : Coalgebra Ar) :
    coalg_hom (EM_prod (bang_cofree (linhom_car Ar (coalg_obj A) (coalg_obj B))) A)
              (Tobj B) :=
  app_kleisli
    (em_proj1 (bang_cofree (linhom_car Ar (coalg_obj A) (coalg_obj B))) A)
    (em_proj2 (bang_cofree (linhom_car Ar (coalg_obj A) (coalg_obj B))) A).

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
    - [e_ret M] : evaluate [M] (already a Kleisli arrow into [Tobj]) and
      then wrap once more with [tunit_eta].
    - [e_bind M K] : the extended-context Kleisli bind [kbind_ext]
      glueing [M : G ⇝ t1] with the continuation [K : (t1 :: G) ⇝ t2].
    - [e_sample mu] : the constant Kleisli arrow [G ⇝ FMeas X] whose
      value is [mu], composed through [tunit_eta] of [FMeas_coalgebra X].
    - [e_real r] : the constant Kleisli arrow [G ⇝ tR] whose value is the
      Dirac at [R_to_carrier r] (norm exactly [1]).
    - [e_score r Hr0 Hr1] : the constant Kleisli arrow [G ⇝ tunit] whose
      value is [r · η(⋆)] — i.e. [r] times the canonical element of the
      unit cone; the two hypotheses [0 ≤ r] and [r ≤ 1] guarantee the
      cone-norm bound that [linhom_icones] needs.

    The three sample-style constructors ([e_sample]/[e_real]/[e_score])
    share the same packaging pattern: build an [icones_hom] [coalg_obj G →
    C] by composing the cone-eraser [coalg_e (ctxD G) : coalg_obj G →
    cone_one_car] with the linear-point map [lin_pt c : cone_one_car → C]
    at the chosen unit-ball value [c]; lift the result to a coalgebra
    morphism into [Tobj] via [adj_psi] (which is UNCONDITIONAL — no
    coalgebra-morphism side condition on the icones_hom). *)

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

(** ** Term-level score lift — [score_tm_lift]

    For a measurable [f : R → R] with pointwise [0 ≤ f r ≤ 1], we build
    an [icones_hom] from [FMeas R_obj] to the unit cone:
    [[
       score_tm_lift f Hf_meas Hf_ge0 Hf_le1 :
         icones_hom Ar (FMeas R_obj) (cone_one_car Ar).
    ]]
    Construction.
    1.  [score_tm_path_fun] : the path [r ↦ f(carrier_to_R r) · one1] in
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
       Lfun (score_tm_lift f …) (dirac_fmeas (R_to_carrier r))
         = MkConeOne (NngNum (Hf_ge0 r)).
    ]]
    On a Dirac at [R_to_carrier r], the score reduces to the SCALAR
    [f r] times the unit-cone basis element — exactly the
    [score_value]-style packaging the scalar [e_score] already uses. *)

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
Definition score_tm_path_fun (r : ar_carrier Ar R_obj) : cone_one_car Ar :=
  MkConeOne Ar (NngNum (Hf_ge0 (cR r))).

Lemma score_tm_path_fun_norm (r : ar_carrier Ar R_obj) :
  (cone_norm (score_tm_path_fun r) <= 1)%R.
Proof.
by rewrite /cone_norm/= /c1_norm/= /score_tm_path_fun/=; exact: Hf_le1.
Qed.

(** Composite [f ∘ cR] is measurable. *)
Lemma f_cR_meas :
  measurable_fun [set: ar_carrier Ar R_obj] (fun r => f (cR r)).
Proof.
apply: (measurableT_comp (f := f)).
- exact: Hf_meas.
- exact: R_carrier_meas.
Qed.

(** [score_tm_path_fun] is a measurable path. *)
Lemma score_tm_path_is_path :
  is_measurable_path (Ar := Ar) (C := cone_one_car Ar) (X := R_obj)
    score_tm_path_fun.
Proof.
split.
  exists 1 => r; exact: score_tm_path_fun_norm.
move=> Y m mM.
(* The only test of [cone_one_car] is [id_test]; on it, the per-test
   map [(z,r) ↦ test_fun m z (score_tm_path_fun r)] reduces to
   [(z,r) ↦ f(cR r)], which is measurable. *)
have Em : m = ConeOneMConeAux.id_test (R := R) (Ar := Ar) Y := mM.
rewrite Em /ConeOneMConeAux.id_test /=
        /ConeOneMConeAux.id_test_fun /score_tm_path_fun /=.
apply: (measurableT_comp (f := fun r => f (cR r))).
- exact: f_cR_meas.
- exact: measurable_snd.
Qed.

Definition score_tm_path : path_car Ar R_obj (cone_one_car Ar) :=
  MkPath score_tm_path_is_path.

(** Path-norm bound: the path values are all [≤ 1], so the sup is [≤ 1]. *)
Lemma score_tm_path_norm_le1 : (path_norm score_tm_path <= 1)%R.
Proof.
apply: ge_sup; first exact: path_normset_nonempty.
by move=> _ [r ->] /=; exact: score_tm_path_fun_norm.
Qed.

(** Norm bound for [int_to_linhom score_tm_path]. *)
Lemma score_tm_int_norm_le1 :
  (cone_norm (int_to_linhom score_tm_path) <= 1)%R.
Proof.
apply: le_trans (int_to_linhom_norm_le score_tm_path) _.
exact: score_tm_path_norm_le1.
Qed.

(** The lift as an [icones_hom]. *)
Definition score_tm_lift :
    icones_hom Ar (FMeas R_obj) (cone_one_car Ar) :=
  linhom_icones (int_to_linhom score_tm_path) score_tm_int_norm_le1.

(** **** Load-bearing Dirac identity.

    On a Dirac at [R_to_carrier r] in [FMeas R_obj], the score
    lift evaluates to [f r · one1] (packaged as a [cone_one_car]). *)
Lemma score_tm_lift_dirac (r : R) :
  Lfun score_tm_lift (dirac_fmeas (R_to_carrier R_carrier_eq r)) =
  MkConeOne Ar (NngNum (Hf_ge0 r)).
Proof.
rewrite /score_tm_lift.
rewrite (linhom_iconesE _ score_tm_int_norm_le1
           (dirac_fmeas (R_to_carrier R_carrier_eq r))).
rewrite -[linhom_fun _ _]/(int_to_linhom_fun score_tm_path
                            (dirac_fmeas (R_to_carrier R_carrier_eq r))).
rewrite (int_to_linhom_fun_dirac score_tm_path
           (R_to_carrier R_carrier_eq r)).
rewrite -[path_fun _ _]/(score_tm_path_fun (R_to_carrier R_carrier_eq r)).
rewrite /score_tm_path_fun.
apply: cone_one_eq; apply: val_inj => /=.
by rewrite R_to_carrierK.
Qed.

End ScoreTmLift.

Arguments score_tm_path_fun {R Ar R_obj} R_carrier_eq f Hf_ge0 r.
Arguments score_tm_path {R Ar R_obj R_carrier_eq R_carrier_meas f}
                        Hf_meas Hf_ge0 Hf_le1.
Arguments score_tm_lift {R Ar R_obj R_carrier_eq R_carrier_meas f}
                        Hf_meas Hf_ge0 Hf_le1.
Arguments score_tm_lift_dirac {R Ar R_obj R_carrier_eq R_carrier_meas f}
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
    (coalg_hom (ctxD G) (Tobj (tyD t))).

(** [score_value r Hr0 Hr1 : cone_one_car Ar] — the element [r · one1] of
    the unit cone, with norm exactly [r] (and in particular [≤ 1]). *)
Definition score_value (r : R) (Hr0 : (0 <= r)%R) (Hr1 : (r <= 1)%R) :
    cone_one_car Ar :=
  MkConeOne Ar (NngNum Hr0).

Lemma score_value_norm_le1 (r : R) (Hr0 : (0 <= r)%R) (Hr1 : (r <= 1)%R) :
    (cone_norm (@score_value r Hr0 Hr1) <= 1)%R.
Proof.
by rewrite /cone_norm/= /c1_norm /=.
Qed.

(** The constant Kleisli arrow at the [score_value]. *)
Definition score_kleisli (G : Coalgebra Ar) (r : R)
    (Hr0 : (0 <= r)%R) (Hr1 : (r <= 1)%R) :
    coalg_hom G (bang_cofree (cone_one_car Ar)) :=
  @const_kleisli _ _ G (cone_one_car Ar) (@score_value r Hr0 Hr1)
                 (@score_value_norm_le1 r Hr0 Hr1).

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

(** The denotation of an expression as a coalgebra (Kleisli) morphism. *)
Fixpoint eD (G : ppl_ctx Ar) (t : T)
    (M : @expr R Ar R_obj G t) {struct M} : EX G t :=
  match M in expr G0 t0 return EX G0 t0 with
  | e_var _ _ v =>
      coalg_comp (tunit_eta (tyD _)) (var_lookup v)
  | e_tt G0 =>
      coalg_comp (tunit_eta EM_term) (em_term_mor (ctxD G0))
  | e_pair G0 t1 t2 M1 M2 =>
      coalg_comp (bang_m (coalg_obj (tyD t1)) (coalg_obj (tyD t2)))
                 (em_pair (eD M1) (eD M2))
  | e_fst G0 t1 t2 M0 =>
      coalg_comp (Tmap (em_proj1 (tyD t1) (tyD t2))) (eD M0)
  | e_snd G0 t1 t2 M0 =>
      coalg_comp (Tmap (em_proj2 (tyD t1) (tyD t2))) (eD M0)
  | e_lam G0 t1 t2 body =>
      coalg_comp (tunit_eta (tyD (tfun t1 t2))) (lam_coalg (eD body))
  | e_app G0 t1 t2 Vf Va =>
      kcomp (app_pair (tyD t1) (tyD t2))
        (coalg_comp (bang_m (coalg_obj (tyD (tfun t1 t2))) (coalg_obj (tyD t1)))
                    (em_pair (eD Vf) (eD Va)))
  (* In this uniform-monadic semantics, [tyD (tprob t) = tyD t] (the
     [tprob] marker is purely syntactic, see the [tyD] docstring), so
     [e_ret M] denotes the SAME Kleisli arrow as [M] itself.  This is
     consistent with treating EVERY expression as a Kleisli arrow into
     [Tobj (tyD t)]. *)
  | e_ret G0 t0 M0 => eD M0
  | e_bind G0 t1 t2 M0 K =>
      kbind_ext (eD K) (eD M0)
  | e_sample G0 X mu Hmu =>
      @sample_kleisli (ctxD G0) X mu Hmu
  | e_real G0 r =>
      @real_kleisli (ctxD G0) r
  | e_score G0 r Hr0 Hr1 =>
      @score_kleisli (ctxD G0) r Hr0 Hr1
  | e_score_tm G0 f Hf_meas Hf_ge0 Hf_le1 e0 =>
      coalg_comp
        (bang_cofree_hom
          (@score_tm_lift R Ar R_obj R_carrier_eq R_carrier_meas
                          f Hf_meas Hf_ge0 Hf_le1))
        (eD e0)
  | e_add G0 M0 N0 =>
      coalg_comp
        (bang_cofree_hom
          (@add_lift R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas))
        (coalg_comp
          (bang_m (FMeas R_obj) (FMeas R_obj))
          (em_pair (eD M0) (eD N0)))
  | e_mul G0 M0 N0 =>
      coalg_comp
        (bang_cofree_hom
          (@mul_lift R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas))
        (coalg_comp
          (bang_m (FMeas R_obj) (FMeas R_obj))
          (em_pair (eD M0) (eD N0)))
  end.

End TermInterp.

Arguments eD {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G t} M.
Arguments score_value {R Ar} r Hr0 Hr1.
Arguments score_kleisli {R Ar} G r Hr0 Hr1.
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
    (coalg_hom (ctxD G) (Tobj (tyD t))).
Local Notation tR' := (tR R_obj).
Local Notation eD' :=
  (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas).

(** *** Definitional unfoldings of [eD]

    Stated as lemmas so [rewrite] folds them cleanly without an
    aggressive [/=] that would unfold all the categorical packaging. *)

Lemma eD_var (G : ppl_ctx Ar) (t : ppl_type Ar) (v : has_var G t) :
  eD' (e_var (R_obj := R_obj) v) =
  coalg_comp (tunit_eta (tyD t)) (var_lookup v).
Proof. by []. Qed.

Lemma eD_tt (G : ppl_ctx Ar) :
  eD' (e_tt (R_obj := R_obj) (G := G)) =
  coalg_comp (tunit_eta EM_term) (em_term_mor (ctxD G)).
Proof. by []. Qed.

Lemma eD_pair (G : ppl_ctx Ar) (t1 t2 : ppl_type Ar)
    (M : expr G t1) (N : expr G t2) :
  eD' (e_pair M N) =
  coalg_comp (bang_m (coalg_obj (tyD t1)) (coalg_obj (tyD t2)))
             (em_pair (eD' M) (eD' N)).
Proof. by []. Qed.

Lemma eD_fst (G : ppl_ctx Ar) (t1 t2 : ppl_type Ar) (M : expr G (tprod t1 t2)) :
  eD' (e_fst M) = coalg_comp (Tmap (em_proj1 (tyD t1) (tyD t2))) (eD' M).
Proof. by []. Qed.

Lemma eD_snd (G : ppl_ctx Ar) (t1 t2 : ppl_type Ar) (M : expr G (tprod t1 t2)) :
  eD' (e_snd M) = coalg_comp (Tmap (em_proj2 (tyD t1) (tyD t2))) (eD' M).
Proof. by []. Qed.

Lemma eD_lam (G : ppl_ctx Ar) (t1 t2 : ppl_type Ar)
    (body : expr (t1 :: G) t2) :
  eD' (e_lam body) =
  coalg_comp (tunit_eta (tyD (tfun t1 t2))) (lam_coalg (eD' body)).
Proof. by []. Qed.

Lemma eD_app (G : ppl_ctx Ar) (t1 t2 : ppl_type Ar)
    (F : expr G (tfun t1 t2)) (X : expr G t1) :
  eD' (e_app F X) =
  kcomp (app_pair (tyD t1) (tyD t2))
    (coalg_comp (bang_m (coalg_obj (tyD (tfun t1 t2))) (coalg_obj (tyD t1)))
                (em_pair (eD' F) (eD' X))).
Proof. by []. Qed.

(** *** The "[e_ret] is identity" law

    Because [tyD (tprob t) = tyD t] and EVERY expression is interpreted
    as a Kleisli arrow, [e_ret M] denotes the same arrow as [M].  This
    is the genuine "tprob is purely syntactic" content. *)
Lemma eD_ret (G : ppl_ctx Ar) (t : ppl_type Ar) (M : expr G t) :
  eD' (e_ret M) = eD' M.
Proof. by []. Qed.

Lemma eD_bind (G : ppl_ctx Ar) (t1 t2 : ppl_type Ar)
    (M : expr G (tprob t1)) (K : expr (t1 :: G) (tprob t2)) :
  eD' (e_bind M K) = kbind_ext (eD' K) (eD' M).
Proof. by []. Qed.

Lemma eD_sample (G : ppl_ctx Ar) (X : ar_obj Ar)
    (mu : fmeas R (ar_carrier Ar X)) (Hmu : (cone_norm mu <= 1)%R) :
  eD' (e_sample (R_obj := R_obj) (G := G) mu Hmu) =
  sample_kleisli (ctxD G) mu Hmu.
Proof. by []. Qed.

Lemma eD_real (G : ppl_ctx Ar) (r : R) :
  eD' (e_real (G := G) (R_obj := R_obj) r) =
  @real_kleisli _ _ R_obj R_carrier_eq (ctxD G) r.
Proof. by []. Qed.

Lemma eD_score (G : ppl_ctx Ar) (r : R) (Hr0 : (0 <= r)%R) (Hr1 : (r <= 1)%R) :
  eD' (e_score (R_obj := R_obj) (G := G) r Hr0 Hr1) =
  score_kleisli (ctxD G) r Hr0 Hr1.
Proof. by []. Qed.

Lemma eD_score_tm (G : ppl_ctx Ar)
    (f : R -> R)
    (Hf_meas : measurable_fun [set: R] f)
    (Hf_ge0 : forall r : R, (0 <= f r)%R)
    (Hf_le1 : forall r : R, (f r <= 1)%R)
    (e : expr G tR') :
  eD' (e_score_tm (R_obj := R_obj) f Hf_meas Hf_ge0 Hf_le1 e) =
  coalg_comp
    (bang_cofree_hom
      (@score_tm_lift R Ar R_obj R_carrier_eq R_carrier_meas
                      f Hf_meas Hf_ge0 Hf_le1))
    (eD' e).
Proof. by []. Qed.

Lemma eD_add (G : ppl_ctx Ar) (M N : expr G tR') :
  eD' (e_add M N) =
  coalg_comp
    (bang_cofree_hom
      (@add_lift R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas))
    (coalg_comp
       (bang_m (FMeas R_obj) (FMeas R_obj))
       (em_pair (eD' M) (eD' N))).
Proof. by []. Qed.

Lemma eD_mul (G : ppl_ctx Ar) (M N : expr G tR') :
  eD' (e_mul M N) =
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
Arguments eD_lam {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G t1 t2} body.
Arguments eD_app {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G t1 t2} F X.
Arguments eD_ret {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G t} M.
Arguments eD_bind {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G t1 t2} M K.
Arguments eD_sample {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G X} mu Hmu.
Arguments eD_real {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G} r.
Arguments eD_score {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G r} Hr0 Hr1.
Arguments eD_score_tm
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G f}
  Hf_meas Hf_ge0 Hf_le1 e.
Arguments eD_add {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G} M N.
Arguments eD_mul {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G} M N.

(** ** Headline example — [ex_random_constant]

    The QBS-paper-flagship "distribution over a function space" example,
    ported from [mathcomp-qbs/theories/showcase/ppl_examples.v]'s
    [random_constant].  Parameterised by a measure [mu] on [R_obj]
    standing in for QBS's [Normal(0,1)] (we do not commit to a concrete
    constructor here: any unit-ball [mu : fmeas R (ar_carrier Ar R_obj)]
    works — the headline is the term, the reduction, and the type, not
    the choice of base sampler).

    [[
        ex_random_constant ≜
          e_bind (e_sample mu Hmu)
                 (e_ret (e_lam (e_var (hv_succ hv_zero))))
        : expr [] (tprob (tfun tR tR))
    ]]

    Reading: draw [c ∼ mu], then return the constant function [λ x. c]
    (the lambda body's [hv_succ hv_zero] index skips the lambda
    parameter and reads the outer bound [c]).  This is a distribution
    over [tR → tR] — the "higher-order" content the QBS paper
    invokes QBS for.

    The reduction lemma [ex_random_constant_denot_E] uses the
    definitional [eD_ret] (= identity at the Kleisli level) and
    [eD_bind] to expose the structural form
    [kbind_ext lam_denot sample_denot]. *)
Section RandomConstant.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Variable (mu : fmeas R (ar_carrier Ar R_obj)).
Hypothesis Hmu : (cone_norm mu <= 1)%R.

Local Notation tR' := (tR R_obj).

(** The lambda body: [hv_succ hv_zero] in context [tR :: tR :: nil]
    skips the lambda parameter and reads the outer bound variable. *)
Definition ex_rc_body : @expr R Ar R_obj (tR' :: tR' :: nil) tR' :=
  e_var (hv_succ hv_zero).

(** The lambda closure: in context [tR :: nil] returns a function
    [tR → tR] = the constant-c closure. *)
Definition ex_rc_lam : @expr R Ar R_obj (tR' :: nil) (tfun tR' tR') :=
  e_lam ex_rc_body.

(** The PPL term: [do c <- sample mu; return (λ x. c)]. *)
Definition ex_random_constant :
    @expr R Ar R_obj nil (tprob (tfun tR' tR')) :=
  e_bind (e_sample mu Hmu) (e_ret ex_rc_lam).

(** Its denotation — a Kleisli arrow [⟦[]⟧ ⇝ ⟦tfun tR tR⟧], i.e.
    [EM_term → Tobj (!̃(U tR ⊸ U tR))]. *)
Definition ex_random_constant_denot :
    coalg_hom (ctxD (Ar := Ar) nil) (Tobj (tyD (tfun tR' tR'))) :=
  @eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas
      nil (tprob (tfun tR' tR')) ex_random_constant.

(** The structural reduction: [eD_ret] is the identity, [eD_bind] is
    [kbind_ext]; combining them, the denotation reads as
    [kbind_ext (eD ex_rc_lam) (eD (e_sample mu Hmu))]. *)
Lemma ex_random_constant_denot_E :
  ex_random_constant_denot =
  kbind_ext
    (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _ ex_rc_lam)
    (sample_kleisli (ctxD nil) mu Hmu).
Proof.
rewrite /ex_random_constant_denot /ex_random_constant.
rewrite eD_bind eD_ret eD_sample.
by [].
Qed.

End RandomConstant.

Arguments ex_rc_body {R Ar R_obj}.
Arguments ex_rc_lam {R Ar R_obj}.
Arguments ex_random_constant {R Ar R_obj} mu Hmu.
Arguments ex_random_constant_denot
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} mu Hmu.
Arguments ex_random_constant_denot_E
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} mu Hmu.

(** ** Headline example — [ex_random_linear]

    The QBS-style "random linear function" example: draw two random
    coefficients [m, b ~ mu] and return the random function [λx. m·x + b]
    of type [tprob (tfun tR tR)].  This exercises both [e_add]/[e_mul]
    and shows that the [eD] semantics produces a Kleisli arrow whose
    structural form reads as
    [[
       kbind_ext m_kont (sample_kleisli mu)
    ]]
    where [m_kont] is the extended-context continuation, itself a nested
    [kbind_ext] in the inner [b] draw.  There is NO closed-form
    posterior — the headline is just the term, its type, the [Inductive]
    coverage of [e_add]/[e_mul], and the structural reduction. *)

Section RandomLinear.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Variable (mu : fmeas R (ar_carrier Ar R_obj)).
Hypothesis Hmu : (cone_norm mu <= 1)%R.

Local Notation tR' := (tR R_obj).

(** The lambda body in context [tR :: tR :: tR :: nil]:
    - [hv_zero] = [x] (lambda parameter, most-recently bound, head);
    - [hv_succ hv_zero] = [b] (the inner [e_bind]);
    - [hv_succ (hv_succ hv_zero)] = [m] (the outer [e_bind]).
    Term: [m * x + b]. *)
Definition ex_rl_body :
    @expr R Ar R_obj (tR' :: tR' :: tR' :: nil) tR' :=
  e_add (e_mul (e_var (hv_succ (hv_succ hv_zero))) (e_var hv_zero))
        (e_var (hv_succ hv_zero)).

(** The lambda closure: in context [tR :: tR :: nil], returns the
    function [λx. m*x + b]. *)
Definition ex_rl_lam :
    @expr R Ar R_obj (tR' :: tR' :: nil) (tfun tR' tR') :=
  e_lam ex_rl_body.

(** The PPL term:
    [do m <- sample mu; do b <- sample mu; return (λx. m*x + b)]. *)
Definition ex_random_linear :
    @expr R Ar R_obj nil (tprob (tfun tR' tR')) :=
  e_bind (e_sample mu Hmu)
    (e_bind (e_sample mu Hmu)
       (e_ret ex_rl_lam)).

(** Its denotation — a Kleisli arrow [⟦[]⟧ ⇝ ⟦tfun tR tR⟧]. *)
Definition ex_random_linear_denot :
    coalg_hom (ctxD (Ar := Ar) nil) (Tobj (tyD (tfun tR' tR'))) :=
  @eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas
      nil (tprob (tfun tR' tR')) ex_random_linear.

(** Structural reduction — exposes the nested-[kbind_ext] form.

    [ex_random_linear_denot
       = kbind_ext (kbind_ext (eD ex_rl_lam) (sample_kleisli mu))
                   (sample_kleisli mu)].
    The outer [kbind_ext] is the [m]-draw; its continuation is the
    [b]-draw's [kbind_ext] continued by [eD ex_rl_lam], the lambda
    closure denotation. *)
Lemma ex_random_linear_denot_E :
  ex_random_linear_denot =
  kbind_ext
    (kbind_ext
       (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _
            ex_rl_lam)
       (sample_kleisli (ctxD (tR' :: nil)) mu Hmu))
    (sample_kleisli (ctxD nil) mu Hmu).
Proof.
rewrite /ex_random_linear_denot /ex_random_linear.
rewrite eD_bind eD_bind eD_ret !eD_sample.
by [].
Qed.

End RandomLinear.

Arguments ex_rl_body {R Ar R_obj}.
Arguments ex_rl_lam {R Ar R_obj}.
Arguments ex_random_linear {R Ar R_obj} mu Hmu.
Arguments ex_random_linear_denot
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} mu Hmu.
Arguments ex_random_linear_denot_E
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} mu Hmu.

(** ** Headline example — [ex_bayes_linear]

    The textbook Bayesian-observation pattern: a sample from a unit-ball
    prior [mu], scored by a measurable likelihood [f : R → R] that
    pointwise lies in [[0,1]] (think [f = gaussian_lik y] for some fixed
    observation [y : R], CLIPPED to the unit interval to fit the
    integrable-cone discipline).  The PPL term is
    [[
       ex_bayes_linear ≜
         e_bind (e_sample mu Hmu)             (* prior:    m ~ mu *)
           (e_bind (e_score_tm f … (e_var hv_zero))
                                              (* score by  f(m) *)
              (e_ret (e_var (hv_succ hv_zero))))
                                              (* return    m *)
         : expr [] (tprob tR).
    ]]

    **Honest scope note.**  This is the UNNORMALISED posterior: the
    denotation is a sub-probability measure whose total mass equals
    [∫ f(m) dµ(m)].  We do NOT claim Bayes-optimality — we claim only
    that the denotation reduces to the expected nested-[kbind_ext] form
    glueing the prior sample, the score's [bang_cofree_hom score_tm_lift]
    post-composition, and the [m]-projection return.  Normalisation
    would require a [qbs_normalize]-style downstream pass we have not
    introduced.

    Reading: the prior is named [mu]; the score uses [f] supplied by
    the caller (e.g. a clipped Gaussian likelihood of the observation
    [y]); the lambda body returns the OUTER bound [m] (because after
    the score's [e_bind] the de Bruijn head is the score's [tunit]
    result, and [m] is one position back). *)

Section BayesLinear.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Variable (mu : fmeas R (ar_carrier Ar R_obj)).
Hypothesis Hmu : (cone_norm mu <= 1)%R.

Variable (f : R -> R).
Hypothesis Hf_meas : measurable_fun [set: R] f.
Hypothesis Hf_ge0 : forall r : R, (0 <= f r)%R.
Hypothesis Hf_le1 : forall r : R, (f r <= 1)%R.

Local Notation tR' := (tR R_obj).

(** The score sub-term [score_tm f (e_var hv_zero)] in context [tR :: nil]:
    the [hv_zero] reads the (only) bound variable [m]. *)
Definition ex_bl_score :
    @expr R Ar R_obj (tR' :: nil) (tprob tunit) :=
  e_score_tm f Hf_meas Hf_ge0 Hf_le1 (e_var hv_zero).

(** The continuation under the prior bind, in context [tR :: nil]:
    [do _ <- score f(m); return m]. *)
Definition ex_bl_cont :
    @expr R Ar R_obj (tR' :: nil) (tprob tR') :=
  e_bind ex_bl_score (e_ret (e_var (hv_succ hv_zero))).

(** The PPL term:
    [do m <- sample mu; do _ <- score f(m); return m]. *)
Definition ex_bayes_linear :
    @expr R Ar R_obj nil (tprob tR') :=
  e_bind (e_sample mu Hmu) ex_bl_cont.

(** Its denotation — a Kleisli arrow [⟦[]⟧ ⇝ ⟦tR⟧]. *)
Definition ex_bayes_linear_denot :
    coalg_hom (ctxD (Ar := Ar) nil) (Tobj (tyD tR')) :=
  @eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas
      nil (tprob tR') ex_bayes_linear.

(** Structural reduction.

    [ex_bayes_linear_denot
       = kbind_ext (eD ex_bl_cont) (sample_kleisli mu Hmu)].

    The outer-most layer is the prior bind, exposed by [eD_bind] and
    [eD_sample].  The inner continuation [eD ex_bl_cont] is itself a
    [kbind_ext] of the score-then-return shape, but the headline
    asserts only the OUTER reduction (the inner one follows by
    re-applying [eD_bind] / [eD_ret] / [eD_score_tm] — the
    [score_tm_lift_dirac] identity is what would give a Dirac-input
    point-reduction, but we do not commit to that here). *)
Lemma ex_bayes_linear_denot_E :
  ex_bayes_linear_denot =
  kbind_ext
    (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas
         _ _ ex_bl_cont)
    (sample_kleisli (ctxD nil) mu Hmu).
Proof.
rewrite /ex_bayes_linear_denot /ex_bayes_linear.
rewrite eD_bind eD_sample.
by [].
Qed.

End BayesLinear.

Arguments ex_bl_score {R Ar R_obj} f Hf_meas Hf_ge0 Hf_le1.
Arguments ex_bl_cont {R Ar R_obj} f Hf_meas Hf_ge0 Hf_le1.
Arguments ex_bayes_linear {R Ar R_obj} mu Hmu f Hf_meas Hf_ge0 Hf_le1.
Arguments ex_bayes_linear_denot
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}
  mu Hmu f Hf_meas Hf_ge0 Hf_le1.
Arguments ex_bayes_linear_denot_E
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}
  mu Hmu f Hf_meas Hf_ge0 Hf_le1.
