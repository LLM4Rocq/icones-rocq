(**md**************************************************************************)
(** * Kleene infrastructure for the CBV value fixpoint — [Phi_fun]
      + the linhom LFP core, on the CLEAN linhom cone — CBV §6

    *** PPL CBV chapter infrastructure

    This file is NOT part of the Ehrhard–Geoffroy 2025 formalization
    (paper §9.2 has the SCones-side [Yfix] for CBN; the CBV value
    fixpoint at this clean-cone shape is paper-level folklore not in
    the literature).

    This file states the NAIVE linear Kleene step [Phi_fun] and the
    linhom LFP core it used to be iterated in.  Its remaining job is to
    supply exactly what §1 of [theories/programs/infra/em_fix_value.v]
    consumes for the DEGENERACY theorem [Phi_fun_lfp_eq0]; the GENUINE
    seeded combinator [fix_comb] does NOT route through anything here —
    it is built on [em_fix_value.v]'s own seeded Kleene core
    ([kleene_from] / [lfp_from], §2), which replaces the cone-zero seed
    by an arbitrary [b0] with [b0 <=p f b0].

    Provided:

    - the Kleene step on the clean linhom cone (no [Tobj] / [!̃U] /
      Kleisli-exponential wrap on [B])

        [Phi_fun M prev := M ∘ (id_Γ ⊗ prev) ∘ Δ_Γ : Γ → B]

      where [M : icones_hom Ar (Γ ⊗ B) B] is the body of the recursive
      function (with the self-reference threaded through [B]), together
      with its unit-ball laws [Phi_fun_ball] / [Phi_fun_incr];
    - the linhom shadow [tensor_mor_R_lin] of [tensor_mor (icones_id G) ·]
      with its computation lemmas and its monotonicity
      [tensor_mor_R_lin_incr], plus [tensor_ext_linhom];
    - the linhom LFP core [kleene_lin] / [linhom_lfp] /
      [linhom_lfp_fixpoint] — [stable/fixpoint.v]'s generic Kleene
      engine instantiated at the coneType [linhom_car Ar C D].

    The naive ZERO-SEEDED operator that used to live here (the
    [linhom_lfp] of [Phi_fun], seeded at the linhom cone-zero) was
    removed after being proven degenerate — it is the zero linhom for
    every diagonal and every body; the degeneracy record survives as
    [em_fix_value.v]'s §1 ([Phi_fun_zero] + the generic [lfp_eq0],
    packaged as [Phi_fun_lfp_eq0]).

    The ω-continuity component that existed only to feed that removed
    operator ([Phi_fun_omega_cont], [tensor_mor_omega_cont_R],
    [linhom_pre_icones_sup], [linhom_post_icones_sup], and the unit-ball
    side conditions [kleene_lin_ball] / [kleene_lin_chain] /
    [linhom_lfp_norm_le1]) was removed together with that operator —
    it documented properties of a construction the degeneracy theorem
    retired.

    Author: Guillaume Baudart <guillaume.baudart@inria.fr>. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import measurable_structure measurable_function.

Require Import Icones.prelude.nonneg_extra.
Require Import Icones.cones.precone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.cone.
Require Import Icones.cones.omega_general.
Require Import Icones.cones.cone_cat.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_cat.
Require Import Icones.stable.totmono.
Require Import Icones.stable.fixpoint.
Require Import Icones.homs.linhom.
Require Import Icones.homs.linhom_functor.
Require Import Icones.homs.bilin.
Require Import Icones.homs.tensor.
Require Import Icones.homs.tensor_construct.
Require Import Icones.homs.smcc.
Require Import Icones.homs.tensor_iso.
Require Import Icones.homs.tensor_hom_iso.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** File-level shorthand: the raw function underlying an [icones_hom]. *)
Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

(** ** Pure-tensor extensionality at the [linhom_car] level

    Two norm-[≤1] linear maps [φ, ψ : B ⊗ C ⊸ D] agreeing on every pure
    tensor [x ⊗p y] (no norm restriction on [x], [y]) are equal.
    Package each as an [icones_hom] via [linhom_icones]; the [icones_hom]
    level [tensor_ext] (Paper Prop 5.14) yields their equality; then
    [linhom_eq] transports back. *)

Section TensorExtLinhom.
Variables (R : realType) (Ar : MeasSubcat R).

Lemma tensor_ext_linhom (B C D : ICone.type Ar)
    (phi psi : linhom_car Ar (tensor Ar B C) D)
    (Hphi : cone_norm phi <= 1) (Hpsi : cone_norm psi <= 1) :
  (forall (x : B) (y : C),
     linhom_fun phi (ptensor x y) = linhom_fun psi (ptensor x y)) ->
  phi = psi.
Proof.
move=> Hpp.
have Heq : linhom_icones phi Hphi = linhom_icones psi Hpsi.
  apply: tensor_ext => x y.
  by rewrite !linhom_iconesE; exact: Hpp.
apply: linhom_eq => z.
by rewrite -(linhom_iconesE phi Hphi z) -(linhom_iconesE psi Hpsi z) Heq.
Qed.

End TensorExtLinhom.

Arguments tensor_ext_linhom {R Ar B C D} phi psi Hphi Hpsi.

(** ** The linhom shadow of [tensor_mor (icones_id G) ·]

    The [icones_to_linhom] packaging of [tensor_mor (icones_id G) f] and
    its two computation lemmas — the layer-1 ingredient of [Phi_fun].
    (Its ω-continuity [tensor_mor_omega_cont_R] was removed together
    with the rest of the component that only the retired zero-seeded
    operator needed.) *)

Section TensorMorIdLinShadow.
Variables (R : realType) (Ar : MeasSubcat R).

(** "Linhom-shadow" of [tensor_mor (icones_id G) f] for [f : C1 → C2]:
    the [icones_to_linhom] packaging of [tensor_mor (icones_id G) f] as a
    [linhom_car (G ⊗ C1) (G ⊗ C2)]. *)
Definition tensor_mor_R_lin (G C1 C2 : ICone.type Ar)
    (f : icones_hom Ar C1 C2) :
    linhom_car Ar (tensor Ar G C1) (tensor Ar G C2) :=
  icones_to_linhom (tensor_mor (icones_id Ar G) f).

Lemma tensor_mor_R_lin_norm_le1 (G C1 C2 : ICone.type Ar)
    (f : icones_hom Ar C1 C2) :
  cone_norm (tensor_mor_R_lin G f) <= 1.
Proof. exact: icones_to_linhom_norm_le1. Qed.

(** Pointwise reading on a pure tensor [x ⊗p y]:
    [tensor_mor_R_lin G f (x ⊗p y) = x ⊗p (f y)]. *)
Lemma tensor_mor_R_lin_ptensor (G C1 C2 : ICone.type Ar)
    (f : icones_hom Ar C1 C2) (x : G) (y : C1) :
  linhom_fun (tensor_mor_R_lin G f) (ptensor x y) = ptensor x (Lfun f y).
Proof.
rewrite /tensor_mor_R_lin icones_to_linhomE tensor_morE.
by rewrite -[Lfun (icones_id Ar G) x]/x.
Qed.

End TensorMorIdLinShadow.

Arguments tensor_mor_R_lin {R Ar} G {C1 C2} f.
Arguments tensor_mor_R_lin_norm_le1 {R Ar} G {C1 C2} f.
Arguments tensor_mor_R_lin_ptensor {R Ar} G {C1 C2} f x y.

(** ** Monotonicity of [tensor_mor (icones_id G) ·]

    Dual to the removed [tensor_mor_omega_cont_R].
    Given a [precone_le prev1 prev2]
    of [linhom_car C1 C2] (with both norms [≤ 1]), the [linhom_car]
    shadow [tensor_mor_R_lin G ·] is monotone in its argument.  This one
    is live: it is the monotonicity content of [Phi_fun_incr]. *)

Section TensorMorRLinIncr.
Variables (R : realType) (Ar : MeasSubcat R).

Lemma tensor_mor_R_lin_incr (G C1 C2 : ICone.type Ar)
    (prev1 prev2 : linhom_car Ar C1 C2)
    (Hprev1 : cone_norm prev1 <= 1) (Hprev2 : cone_norm prev2 <= 1) :
  precone_le prev1 prev2 ->
  precone_le (tensor_mor_R_lin G (linhom_icones prev1 Hprev1))
             (tensor_mor_R_lin G (linhom_icones prev2 Hprev2)).
Proof.
move=> Hle.
case: Hle => δ deltaE.
have δ_le_prev2 : precone_le δ prev2.
  by exists prev1; rewrite deltaE; symmetry; exact: precone_addC.
have δ_norm : cone_norm δ <= 1.
  by apply: le_trans Hprev2; exact: cone_normp.
exists (tensor_mor_R_lin G (linhom_icones δ δ_norm)).
have <- : linhom_add (tensor_mor_R_lin G (linhom_icones prev1 Hprev1))
                     (tensor_mor_R_lin G (linhom_icones δ δ_norm)) =
          precone_add (tensor_mor_R_lin G (linhom_icones prev1 Hprev1))
                      (tensor_mor_R_lin G (linhom_icones δ δ_norm))
  by [].
have half_ge0 : 0 <= ((2 : R)^-1) by rewrite invr_ge0 ler0n.
pose half : {nonneg R} := NngNum half_ge0.
have two_ge0 : 0 <= ((2 : R)) by rewrite ler0n.
pose two : {nonneg R} := NngNum two_ge0.
have half_le1 : half%:num <= 1.
  by rewrite /= invf_le1// ?ler1n//; exact: ltr0Sn.
have two_half_eq : (two%:num * half%:num)%:nng = 1%:nng :> {nonneg R}.
  by apply: val_inj => /=; rewrite mulfV// gt_eqF// ltr0Sn.
rewrite -[X in X = _]linhom_scale_1.
rewrite -[X in _ = X]linhom_scale_1.
rewrite -[in X in X = _]two_half_eq linhom_scale_A.
rewrite -[in X in _ = X]two_half_eq linhom_scale_A.
congr (linhom_scale two _).
rewrite linhom_scale_DAr.
have prev2_lin_norm :
    linhom_norm (tensor_mor_R_lin G (linhom_icones prev2 Hprev2)) <= 1
  by exact: tensor_mor_R_lin_norm_le1.
have prev1_lin_norm :
    linhom_norm (tensor_mor_R_lin G (linhom_icones prev1 Hprev1)) <= 1
  by exact: tensor_mor_R_lin_norm_le1.
have δ_lin_norm :
    linhom_norm (tensor_mor_R_lin G (linhom_icones δ δ_norm)) <= 1
  by exact: tensor_mor_R_lin_norm_le1.
have LHS_norm :
  cone_norm
    (linhom_scale half (tensor_mor_R_lin G (linhom_icones prev2 Hprev2))) <= 1.
  rewrite -[cone_norm _]/(linhom_norm _) linhom_normh.
  rewrite -[X in _ <= X]mulr1; apply: ler_pM => //.
  exact: linhom_norm_ge0.
have RHS_norm :
  cone_norm (linhom_add
    (linhom_scale half (tensor_mor_R_lin G (linhom_icones prev1 Hprev1)))
    (linhom_scale half (tensor_mor_R_lin G (linhom_icones δ δ_norm)))) <= 1.
  rewrite -[cone_norm _]/(linhom_norm _).
  apply: le_trans (linhom_normt _ _) _.
  rewrite !linhom_normh.
  have e2 : half%:num * 1 + half%:num * 1 = 1.
    by rewrite mulr1 -mulr2n -mulr_natr /= mulVf// gt_eqF// ltr0Sn.
  rewrite -e2; apply: lerD; apply: ler_pM => //; exact: linhom_norm_ge0.
apply: (tensor_ext_linhom _ _ LHS_norm RHS_norm).
move=> x y.
have LHS_pt :
  linhom_fun
    (linhom_scale half (tensor_mor_R_lin G (linhom_icones prev2 Hprev2)))
    (ptensor x y) =
  precone_scale half (ptensor x (linhom_fun prev2 y)).
  rewrite /linhom_fun /= /linhom_scale_fun.
  congr (precone_scale half _).
  by rewrite -[linhom_fun _ _]
       /(linhom_fun (tensor_mor_R_lin G (linhom_icones prev2 Hprev2))
          (ptensor x y))
     tensor_mor_R_lin_ptensor linhom_iconesE.
rewrite LHS_pt.
have RHS_pt :
  linhom_fun (linhom_add
    (linhom_scale half (tensor_mor_R_lin G (linhom_icones prev1 Hprev1)))
    (linhom_scale half (tensor_mor_R_lin G (linhom_icones δ δ_norm))))
    (ptensor x y) =
  precone_add (precone_scale half (ptensor x (linhom_fun prev1 y)))
              (precone_scale half (ptensor x (linhom_fun δ y))).
  rewrite /linhom_fun /= /linhom_add_fun /linhom_scale_fun.
  congr (precone_add _ _); congr (precone_scale half _).
  - by rewrite -[linhom_fun _ _]
         /(linhom_fun (tensor_mor_R_lin G (linhom_icones prev1 Hprev1))
            (ptensor x y))
       tensor_mor_R_lin_ptensor linhom_iconesE.
  - by rewrite -[linhom_fun _ _]
         /(linhom_fun (tensor_mor_R_lin G (linhom_icones δ δ_norm))
            (ptensor x y))
       tensor_mor_R_lin_ptensor linhom_iconesE.
rewrite RHS_pt.
have prev2_y :
  linhom_fun prev2 y = precone_add (linhom_fun prev1 y) (linhom_fun δ y).
  by have /(congr1 (fun h => linhom_fun h y)) /= := deltaE.
rewrite prev2_y.
have tau_lin :
  ptensor x (precone_add (linhom_fun prev1 y) (linhom_fun δ y)) =
  precone_add (ptensor x (linhom_fun prev1 y)) (ptensor x (linhom_fun δ y)).
  rewrite /ptensor /linhom_fun.
  by have [_ HD _] := linhom_pre_linear (linhom_pre_of (tau G C2 x)); exact: HD.
rewrite tau_lin.
exact: precone_scale_DAr.
Qed.

End TensorMorRLinIncr.

Arguments tensor_mor_R_lin_incr {R Ar} G {C1 C2} prev1 prev2 Hprev1 Hprev2.

(** ** Generic Kleene fixpoint on the linhom unit ball
       — parametric in [Phi : linhom C D → linhom C D]

    This is [stable/fixpoint.v]'s generic [Section KleeneCore] /
    [Section KleeneFixpoint] INSTANTIATED at the coneType
    [linhom_car Ar C D]; the [kleene_lin*] / [linhom_lfp*] names are
    kept as the linhom-level interface consumed downstream
    ([em_fix_value.v], [ppl_cbv.v]). *)

Section LinhomLFP.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (C D : ICone.type Ar).

Variable Phi : linhom_car Ar C D -> linhom_car Ar C D.
Hypothesis Phi_incr : forall x y : linhom_car Ar C D,
  precone_le x y -> cone_norm y <= 1 -> precone_le (Phi x) (Phi y).
Hypothesis Phi_ball : forall x : linhom_car Ar C D,
  cone_norm x <= 1 -> cone_norm (Phi x) <= 1.

(** The Kleene iterates [Phi^n(0)] (using the linhom cone-zero). *)
Definition kleene_lin (n : nat) : linhom_car Ar C D := kleene Phi n.

Lemma kleene_lin_S n : kleene_lin n.+1 = Phi (kleene_lin n).
Proof. exact: kleeneS. Qed.

(** The linhom-level least fixpoint of [Phi]. *)
Definition linhom_lfp : linhom_car Ar C D := lfp Phi Phi_incr Phi_ball.

End LinhomLFP.

Arguments kleene_lin {R Ar C D} Phi n.
Arguments linhom_lfp {R Ar C D} Phi Phi_incr Phi_ball.

(** ** The Kleene fixpoint equation, under linhom-ω-continuity *)

Section LinhomLFPFix.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (C D : ICone.type Ar).

Variable Phi : linhom_car Ar C D -> linhom_car Ar C D.
Hypothesis Phi_incr : forall x y : linhom_car Ar C D,
  precone_le x y -> cone_norm y <= 1 -> precone_le (Phi x) (Phi y).
Hypothesis Phi_ball : forall x : linhom_car Ar C D,
  cone_norm x <= 1 -> cone_norm (Phi x) <= 1.

(** ω-continuity of [Phi] on the unit ball. *)
Hypothesis Phi_cont :
  forall (u : nat -> linhom_car Ar C D)
         (uch : forall n, precone_le (u n) (u n.+1))
         (ub1 : forall n, cone_norm (u n) <= 1)
         (Pch : forall n, precone_le (Phi (u n)) (Phi (u n.+1)))
         (Pub1 : forall n, cone_norm (Phi (u n)) <= 1),
    Phi (cone_sup_ball u uch ub1) =
    cone_sup_ball (Phi \o u) Pch Pub1.

(** Bridge to the generic continuity packaging: on unit-ball chains
    the image chain is itself in the unit ball (by [Phi_ball]), so the
    radius-[Mf] supremum of [is_scott_continuous_unit] collapses to
    the unit-ball one.  Since [cone_sup_at] and [cone_sup_ball] are
    both phantom-witness wrappers around the total operator
    [cone_sup], that collapse is now DEFINITIONAL — the radius, the
    chain and the bound witnesses are all irrelevant to the term, so
    the historical [cone_sup_at_indep] + [cone_sup_at_ball] rewrites
    are no longer needed and [Phi_cont] applies directly. *)
Lemma Phi_scott_unit : is_scott_continuous_unit Phi.
Proof.
move=> Mf u uch ub1 fuch fubMf Mfpos.
have Pub1 n : cone_norm (Phi (u n)) <= 1 by apply: Phi_ball; exact: ub1.
exact: Phi_cont.
Qed.

Lemma linhom_lfp_fixpoint :
  Phi (linhom_lfp Phi Phi_incr Phi_ball) = linhom_lfp Phi Phi_incr Phi_ball.
Proof. exact: (lfp_fixpoint Phi Phi_incr Phi_ball Phi_scott_unit). Qed.

End LinhomLFPFix.

Arguments linhom_lfp_fixpoint {R Ar C D} Phi Phi_incr Phi_ball Phi_cont.

(** ** The CBV value-fixpoint Kleene step [Phi_fun] — clean cone

    Body [M : icones_hom Ar (Γ ⊗ B) B] (NO [Tobj]/[!̃U] wrap on [B]).
    Step: [Phi_fun M prev := M ∘ (id_Γ ⊗ prev) ∘ Δ_Γ : Γ → B] where
    [Δ_Γ = coalg_d Γ : Γ → Γ ⊗ Γ] is the comonoid diagonal of the
    coalgebra [Γ] (per Cor 20 / Mellies Prop 28, [em_cartesian.v]).

    Concretely we package the three linhom-level operations:

    - [tensor_mor_R_lin Γ (linhom_icones prev _)
         : linhom_car (Γ⊗Γ) (Γ ⊗ B)]
      (monotone in prev via [tensor_mor_R_lin_incr]; its ω-continuity
      lemma [tensor_mor_omega_cont_R] was removed with the retired
      operator);
    - [linhom_pre_act diag] applied to that, landing in
      [linhom_car Γ (Γ ⊗ B)];
    - [linhom_post M] applied to that, landing in [linhom_car Γ B]. *)

Section PhiFun.
Variables (R : realType) (Ar : MeasSubcat R).

(** The CBV step needs three things from the ambient context:
    - the underlying cone [Gamma : ICone.type Ar];
    - the codomain cone [B : ICone.type Ar];
    - a diagonal map [diag : Γ → Γ ⊗ Γ] — supplied by the caller (in
      practice [coalg_d (ctxD_cbv G)]).

    Keeping [diag] as an explicit parameter makes [Phi_fun] usable for
    both [ne_fix] and [ne_fix_mr], and for [ne_fix_mr]'s
    product-case where the diagonal is derived from the EM_prod
    coalgebra of [ctxD_cbv G]. *)

Variables (Gamma B : ICone.type Ar).
Variable diag : icones_hom Ar Gamma (tensor Ar Gamma Gamma).
Variable M : icones_hom Ar (tensor Ar Gamma B) B.

(** The "safe" version of [Phi_fun] taking a norm-witness as input. *)
Definition Phi_fun_safe
    (prev : linhom_car Ar Gamma B)
    (Hprev : cone_norm prev <= 1) :
    linhom_car Ar Gamma B :=
  linhom_post M
    (linhom_pre_act diag
      (tensor_mor_R_lin Gamma
        (linhom_icones prev Hprev))).

(** The TOTAL [Phi_fun] (defined on all of [linhom_car], not just the
    unit ball).  On unit-ball [prev] it computes to [Phi_fun_safe prev
    _]; off the unit ball we return [precone_zero] (irrelevant for the
    Kleene chain, which stays in the unit ball). *)
Arguments Phi_fun_safe prev Hprev : clear implicits.

Definition Phi_fun
    (prev : linhom_car Ar Gamma B) :
    linhom_car Ar Gamma B :=
  match pselect (cone_norm prev <= 1) with
  | left Hball => Phi_fun_safe prev Hball
  | right _ => precone_zero
  end.

Lemma Phi_fun_unit (prev : linhom_car Ar Gamma B)
    (Hprev : cone_norm prev <= 1) :
  Phi_fun prev = Phi_fun_safe prev Hprev.
Proof.
rewrite /Phi_fun; case: pselect => [Hball | Hball]; last by [].
by congr Phi_fun_safe; exact: Prop_irrelevance.
Qed.

(** ** Ball preservation and monotonicity *)

Lemma Phi_fun_safe_ball
    (prev : linhom_car Ar Gamma B)
    (Hprev : cone_norm prev <= 1) :
  cone_norm (Phi_fun_safe prev Hprev) <= 1.
Proof.
rewrite /Phi_fun_safe.
rewrite -linhom_post_iconesE.
apply: le_trans (cones_hom_norm_le1
                   (mcones_hom_cones (icones_hom_mcones
                     (linhom_post_icones M))) _) _.
rewrite -linhom_pre_iconesE.
apply: le_trans (cones_hom_norm_le1
                   (mcones_hom_cones (icones_hom_mcones
                     (linhom_pre_icones diag))) _) _.
exact: tensor_mor_R_lin_norm_le1.
Qed.

Lemma Phi_fun_ball (prev : linhom_car Ar Gamma B) :
  cone_norm prev <= 1 -> cone_norm (Phi_fun prev) <= 1.
Proof.
move=> Hprev; rewrite (Phi_fun_unit Hprev); exact: Phi_fun_safe_ball.
Qed.

Lemma Phi_fun_safe_incr
    (prev1 prev2 : linhom_car Ar Gamma B)
    (Hprev1 : cone_norm prev1 <= 1) (Hprev2 : cone_norm prev2 <= 1) :
  precone_le prev1 prev2 ->
  precone_le (Phi_fun_safe prev1 Hprev1) (Phi_fun_safe prev2 Hprev2).
Proof.
move=> Hle.
rewrite /Phi_fun_safe.
have tens_le : precone_le
    (tensor_mor_R_lin Gamma (linhom_icones prev1 Hprev1))
    (tensor_mor_R_lin Gamma (linhom_icones prev2 Hprev2))
  by exact: tensor_mor_R_lin_incr.
have pre_le : precone_le
    (linhom_pre_act diag
      (tensor_mor_R_lin Gamma (linhom_icones prev1 Hprev1)))
    (linhom_pre_act diag
      (tensor_mor_R_lin Gamma (linhom_icones prev2 Hprev2))).
  rewrite -!linhom_pre_iconesE.
  apply: linear_increasing => //.
  exact: cones_hom_linear (mcones_hom_cones
            (icones_hom_mcones (linhom_pre_icones diag))).
rewrite -!linhom_post_iconesE.
apply: linear_increasing => //.
exact: cones_hom_linear (mcones_hom_cones
          (icones_hom_mcones (linhom_post_icones M))).
Qed.

Lemma Phi_fun_incr (prev1 prev2 : linhom_car Ar Gamma B) :
  precone_le prev1 prev2 -> cone_norm prev2 <= 1 ->
  precone_le (Phi_fun prev1) (Phi_fun prev2).
Proof.
move=> Hle Hprev2.
have Hprev1 : cone_norm prev1 <= 1.
  by apply: le_trans Hprev2; exact: cone_normp.
rewrite (Phi_fun_unit Hprev1) (Phi_fun_unit Hprev2).
exact: Phi_fun_safe_incr.
Qed.

End PhiFun.

Arguments Phi_fun_safe {R Ar Gamma B} diag M prev Hprev.
Arguments Phi_fun {R Ar Gamma B} diag M prev.
Arguments Phi_fun_unit {R Ar Gamma B} diag M prev Hprev.
Arguments Phi_fun_safe_ball {R Ar Gamma B} diag M prev Hprev.
Arguments Phi_fun_ball {R Ar Gamma B} diag M prev.
Arguments Phi_fun_safe_incr {R Ar Gamma B} diag M prev1 prev2 Hprev1 Hprev2.
Arguments Phi_fun_incr {R Ar Gamma B} diag M prev1 prev2.
