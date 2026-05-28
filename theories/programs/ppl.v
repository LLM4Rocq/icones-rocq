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

    ** Scope of this commit (C-partial: NO arithmetic yet) **

    The full constructor list is in the [Inductive expr] below, but here is
    what is intentionally NOT in this version:

    - [e_add] : sum of two random variables of type [tprob tR];
    - [e_mul] : product of two random variables of type [tprob tR];
    - [ex_random_linear] : the QBS-style mixture example exercising [e_add]
      / [e_mul].

    These three pieces depend on the lax monoidal bundling of [FMeas]
    ([theories/homs/fmeas_lax.v]'s [icones_hom] wrapping the function-level
    [fmeas_lax_pre]), which is being added by a parallel agent.  A small
    follow-up integration commit will EXTEND the [Inductive expr] with the
    two arithmetic constructors and add the [ex_random_linear] example once
    the bundle lands.  This file is consistent and axiom-free WITHOUT
    [e_add]/[e_mul].

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
    propositional cast [R_carrier_eq] is the witness; [e_real]/[e_score] use
    it to translate an [R]-literal to a value in [ar_carrier Ar R_obj].

    (No [e_add]/[e_mul] in this commit — the follow-up integration agent
    appends them.) *)

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
    - [e_sample] : sample from a fixed measure [µ : FMeas X];
    - [e_real] : real literal [r : R] of type [tR];
    - [e_score] : score by [r : R], returning [tprob tunit].

    *** TODO: NOT IN THIS COMMIT (follow-up agent appends them) ***

    The arithmetic constructors below are NOT YET in the inductive; they
    depend on the [icones_hom] bundling of [FMeas]'s lax monoidal pre-map
    that the parallel [theories/homs/fmeas_lax.v] agent is producing.  The
    follow-up integration agent will append:
    [[
       | e_add  : forall G, expr G (tprob tR) -> expr G (tprob tR) ->
                            expr G (tprob tR)
       | e_mul  : forall G, expr G (tprob tR) -> expr G (tprob tR) ->
                            expr G (tprob tR)
    ]]
    together with the example [ex_random_linear] that exercises them. *)
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
             (mu : fmeas R (ar_carrier Ar X)) :
      expr G (tprob (tbase X))
  | e_real  (G : ppl_ctx Ar) (r : R) : expr G tR'
  | e_score (G : ppl_ctx Ar) (r : R) : expr G (tprob tunit).

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
Arguments e_sample {R Ar R_obj G X} mu.
Arguments e_real {R Ar R_obj G} r.
Arguments e_score {R Ar R_obj G} r.

(** ** Type and context interpretation [tyD] / [ctxD]

    Every type denotes a coalgebra of [EM(!)]:
    [[
       ⟦tunit⟧       = EM_term
       ⟦tbase X⟧     = FMeas_coalgebra X         (Theorem 9.7)
       ⟦tprod t1 t2⟧ = EM_prod ⟦t1⟧ ⟦t2⟧
       ⟦tfun  t1 t2⟧ = !̃(U⟦t1⟧ ⊸ U⟦t2⟧)         (Kleisli exponential of [T])
       ⟦tprob t⟧     = Tobj ⟦t⟧ = !̃(U⟦t⟧)        (CBV computation monad)
    ]]

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
  | tprob t0 => Tobj (tyD t0)
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
      Dirac at [R_to_carrier r] (a coalgebra morphism via [Coalg_dirac]).
    - [e_score r] : the constant Kleisli arrow [G ⇝ tunit] whose value
      is [r · η(⋆)] — i.e. [r] times the monad unit at unit.  See note
      below for the precise formulation. *)
