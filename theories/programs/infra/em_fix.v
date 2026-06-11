(**md**************************************************************************)
(** * The CBV value-fixpoint Kleene operator [Yfix_fun_lin]
      — on the CLEAN linhom cone, no [Tobj] / [!̃U] wrap on [B] — CBV §6

    *** PPL CBV chapter infrastructure

    This file is NOT part of the Ehrhard–Geoffroy 2025 formalization
    (paper §9.2 has the SCones-side [Yfix] for CBN; the CBV value
    fixpoint at this clean-cone shape is paper-level folklore not in
    the literature).

    Provides the CBV value-fixpoint operator on the linhom cone

      [Yfix_fun_lin M : linhom_car Ar Γ B]

    where [M : icones_hom Ar (Γ ⊗ B) B] is the body of the recursive
    function (with the self-reference threaded through [B]).  The
    construction parallels [theories/stable/fixpoint.v]'s [Yfix] for
    SCones, at the ICones level: iterate the Kleene step

      [Phi_fun M prev := M ∘ (id_Γ ⊗ prev) ∘ Δ_Γ : Γ → B]

    on the unit-ball ω-CPO of [linhom_car Ar Γ B], starting from
    [precone_zero], and take the supremum.  The result is parametric
    in [Γ] and [B] — in particular it specialises to:
    - [B = bang_cofree L] for the function-type case of [ne_fix] (this
      gives an OCaml-style [let rec] at function types);
    - [B = coalg_obj (tyD t)] for any [t] with [is_free_coalg_type t]
      true, for the mutual-recursion constructor [ne_fix_mr];
    - non-cofree [B] (e.g. [bool_cone_car], [FMeas_coalgebra X]) when
      a recursive function returns a base / boolean / measure value.

    The clean cone — no [Tobj] / [!̃U] / Kleisli-exponential wrap on
    [B] — drops one full layer of [bang_fmap]/[der] threading from
    the old [em_fix.v] [Phi_fun_safe] of the [Tobj]-wrapped setup, so
    the construction is structurally cleaner.

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

(** ** ω-continuity of pre/post composition by an icones_hom

    These are CONSEQUENCES (NOT new theorems) of the fact that
    [linhom_post_icones g] is an icones_hom, hence its underlying
    [cones_hom_fun] is ω-continuous on the unit ball.  We expose the
    equation in the form we need downstream. *)

Section LinhomPostPreSup.
Variables (R : realType) (Ar : MeasSubcat R).

(** Post-composition by an icones_hom [g] preserves linhom-cone suprema. *)
Lemma linhom_post_icones_sup (C D1 D2 : ICone.type Ar)
    (g : icones_hom Ar D1 D2)
    (u : nat -> linhom_car Ar C D1)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, cone_norm (u n) <= 1)
    (gch : forall n, precone_le (linhom_post g (u n)) (linhom_post g (u n.+1)))
    (gub : forall n, cone_norm (linhom_post g (u n)) <= 1) :
  linhom_post g (cone_sup_ball u uch ub1) =
  cone_sup_ball (linhom_post g \o u) gch gub.
Proof.
set hh := @linhom_post_icones R Ar C _ _ g.
have Hcont :
    is_omega_continuous (cones_hom_fun
       (mcones_hom_cones (icones_hom_mcones hh))).
  exact: cones_hom_continuous.
have HE : Lfun hh (cone_sup_ball u uch ub1) =
          linhom_post g (cone_sup_ball u uch ub1).
  exact: linhom_post_iconesE.
rewrite -HE (Hcont u uch ub1 gch gub).
apply: precone_le_anti.
- apply: cone_sup_ball_lub => n.
  exact: (cone_sup_ball_ub (linhom_post g \o u) gch gub n).
- apply: cone_sup_ball_lub => n.
  exact: (cone_sup_ball_ub _ gch gub n).
Qed.

(** Pre-composition by an icones_hom [h] preserves linhom-cone suprema. *)
Lemma linhom_pre_icones_sup (C1 C2 D : ICone.type Ar)
    (h : icones_hom Ar C2 C1)
    (u : nat -> linhom_car Ar C1 D)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, cone_norm (u n) <= 1)
    (hch : forall n,
       precone_le (linhom_pre_act h (u n)) (linhom_pre_act h (u n.+1)))
    (hub : forall n, cone_norm (linhom_pre_act h (u n)) <= 1) :
  linhom_pre_act h (cone_sup_ball u uch ub1) =
  cone_sup_ball (linhom_pre_act h \o u) hch hub.
Proof.
set hh := @linhom_pre_icones R Ar _ _ D h.
have Hcont :
    is_omega_continuous (cones_hom_fun
       (mcones_hom_cones (icones_hom_mcones hh))).
  exact: cones_hom_continuous.
have HE : Lfun hh (cone_sup_ball u uch ub1) =
          linhom_pre_act h (cone_sup_ball u uch ub1).
  exact: linhom_pre_iconesE.
rewrite -HE (Hcont u uch ub1 hch hub).
apply: precone_le_anti.
- apply: cone_sup_ball_lub => n.
  exact: (cone_sup_ball_ub (linhom_pre_act h \o u) hch hub n).
- apply: cone_sup_ball_lub => n.
  exact: (cone_sup_ball_ub _ hch hub n).
Qed.

End LinhomPostPreSup.

Arguments linhom_post_icones_sup {R Ar C D1 D2}.
Arguments linhom_pre_icones_sup {R Ar C1 C2 D}.

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

(** ** ω-continuity of [tensor_mor (icones_id G) ·] — the workhorse for Yfix

    Given a unit-ball ω-chain [u_n : linhom_car C1 C2], the icones_hom
    [tensor_mor (icones_id G) (linhom_icones (sup u_n) LHS_norm)] equals
    (at the [icones_to_linhom] level) the linhom-cone supremum of
    [n ↦ icones_to_linhom
           (tensor_mor (icones_id G) (linhom_icones u_n (ub1 n)))]. *)

Section TensorMorIdLinOmegaCont.
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

(** **The headline ω-continuity of [tensor_mor (icones_id G) ·]**
    at the linhom level. *)
Lemma tensor_mor_omega_cont_R (G C1 C2 : ICone.type Ar)
    (u : nat -> linhom_car Ar C1 C2)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, cone_norm (u n) <= 1)
    (LHS_norm : cone_norm (linhom_sup_ball u uch ub1) <= 1)
    (T_n := fun n => tensor_mor_R_lin G (linhom_icones (u n) (ub1 n)))
    (tch : forall n, precone_le (T_n n) (T_n n.+1))
    (tub1 : forall n, cone_norm (T_n n) <= 1) :
  tensor_mor_R_lin G (linhom_icones _ LHS_norm) =
  linhom_sup_ball T_n tch tub1.
Proof.
apply: (tensor_ext_linhom _ _ (tensor_mor_R_lin_norm_le1 _ _)
                              (linhom_sup_ball_norm T_n tch tub1)).
move=> x y.
(* LHS at [x ⊗p y]: [tensor_mor_R_lin G (linhom_icones (sup u_n)) (x ⊗p y) =
   x ⊗p Lfun (linhom_icones (sup u_n) LHS_norm) y
   = x ⊗p (linhom_fun (sup u_n) y)]. *)
rewrite tensor_mor_R_lin_ptensor.
have LHS_eq : Lfun (linhom_icones _ LHS_norm) y =
              linhom_fun (linhom_sup_ball u uch ub1) y by [].
rewrite LHS_eq.
(* RHS at [x ⊗p y]: unfold the linhom-sup. *)
rewrite -[linhom_fun (linhom_sup_ball T_n tch tub1) _]
        /(linhom_sup_fun tch tub1 (ptensor x y)).
(* Reduce [y] to unit-ball by scaling. *)
set rinv := cnorm_succ_inv_nng y.
set r := cnorm_succ_nng y.
set y' := precone_scale rinv y.
have y'_ub : cone_norm y' <= 1 by exact: cnorm_inv_unit.
have y_eq : y = precone_scale r y' by rewrite /y' cnorm_succ_scaleK.
have LHS_lin : linhom_fun (linhom_sup_ball u uch ub1) y =
               precone_scale r (linhom_fun (linhom_sup_ball u uch ub1) y').
  rewrite y_eq /linhom_fun.
  by have [_ _ HZ] :=
    linhom_pre_linear (linhom_pre_of (linhom_sup_ball u uch ub1)); rewrite HZ.
rewrite LHS_lin ptensorZr.
have RHS_lin : linhom_sup_fun tch tub1 (ptensor x y) =
               precone_scale r (linhom_sup_fun tch tub1 (ptensor x y')).
  rewrite {1}y_eq ptensorZr.
  have [_ _ HZ] := linhom_pre_linear
                     (linhom_pre_of (linhom_sup_ball T_n tch tub1)).
  exact: HZ.
rewrite RHS_lin.
congr (precone_scale _ _).
have LHS_at_y' : linhom_fun (linhom_sup_ball u uch ub1) y' =
                 linhom_sup_unit uch ub1 y'_ub
  by exact: linhom_sup_fun_unitE.
rewrite LHS_at_y' linhom_sup_unitE.
set xinv := cnorm_succ_inv_nng x.
set xr := cnorm_succ_nng x.
set x' := precone_scale xinv x.
have x'_ub : cone_norm x' <= 1 by exact: cnorm_inv_unit.
have x_eq : x = precone_scale xr x' by rewrite /x' cnorm_succ_scaleK.
have xy'_norm : cone_norm (ptensor x' y') <= 1.
  apply: (le_trans (tensor_norm_le _ _)).
  apply: mulr_ile1 => //; exact: cone_norm_ge0.
rewrite x_eq ptensorZl.
have RHS_xrEq : linhom_sup_fun tch tub1 (ptensor (precone_scale xr x') y') =
                precone_scale xr (linhom_sup_fun tch tub1 (ptensor x' y')).
  rewrite ptensorZl.
  have [_ _ HZ] := linhom_pre_linear
                     (linhom_pre_of (linhom_sup_ball T_n tch tub1)).
  exact: HZ.
rewrite RHS_xrEq.
have RHS_at_xy' : linhom_sup_fun tch tub1 (ptensor x' y') =
                  linhom_sup_unit tch tub1 xy'_norm
  by exact: linhom_sup_fun_unitE.
rewrite RHS_at_xy' linhom_sup_unitE.
congr (precone_scale _ _).
(* Both sides are [cone_sup_ball] over [tensor Ar G C2]. *)
pose w (n : nat) : C2 := linhom_fun (u n) y'.
have wch : forall n, precone_le (w n) (w n.+1)
  by move=> n; rewrite /w; exact: linhom_sup_pw_chain uch y' n.
have wub1 : forall n, cone_norm (w n) <= 1
  by move=> n; rewrite /w; apply: linhom_sup_pw_ub1 => //.
have ptensor_x'_cont : is_omega_continuous (fun v : C2 => ptensor x' v).
  by exact: (linhom_pre_continuous (linhom_pre_of (tau G C2 x'))).
have pch : forall n, precone_le (ptensor x' (w n)) (ptensor x' (w n.+1)).
  move=> n; rewrite /w.
  apply: (linear_increasing (f := ptensor x'));
    last by exact: wch.
  exact: (linhom_pre_linear (linhom_pre_of (tau G C2 x'))).
have pub1 : forall n, cone_norm (ptensor x' (w n)) <= 1.
  move=> n; apply: (le_trans (tensor_norm_le _ _)).
  apply: mulr_ile1; first exact: cone_norm_ge0.
  - exact: cone_norm_ge0.
  - exact: x'_ub.
  - exact: wub1.
have heq : cone_sup_ball (fun n => linhom_fun (u n) y')
             [eta linhom_sup_pw_chain uch y'] (linhom_sup_pw_ub1 ub1 y'_ub) =
           cone_sup_ball w wch wub1.
  apply: precone_le_anti.
    by apply: cone_sup_ball_lub => n; exact: cone_sup_ball_ub.
  by apply: cone_sup_ball_lub => n; exact: cone_sup_ball_ub.
rewrite heq.
rewrite (ptensor_x'_cont w wch wub1 pch pub1).
apply: precone_le_anti.
- apply: cone_sup_ball_lub => n /=.
  have HE : ptensor x' (linhom_fun (u n) y') =
            linhom_fun (T_n n) (ptensor x' y').
    rewrite /T_n /=.
    by rewrite (tensor_mor_R_lin_ptensor (linhom_icones (u n) (ub1 n)) x' y').
  rewrite HE.
  exact: cone_sup_ball_ub.
- apply: cone_sup_ball_lub => n.
  have HE : linhom_fun (T_n n) (ptensor x' y') =
            ptensor x' (linhom_fun (u n) y').
    rewrite /T_n.
    by rewrite (tensor_mor_R_lin_ptensor (linhom_icones (u n) (ub1 n)) x' y').
  rewrite HE.
  exact: (cone_sup_ball_ub _ pch pub1 n).
Qed.

End TensorMorIdLinOmegaCont.

Arguments tensor_mor_R_lin {R Ar} G {C1 C2} f.
Arguments tensor_mor_R_lin_norm_le1 {R Ar} G {C1 C2} f.
Arguments tensor_mor_R_lin_ptensor {R Ar} G {C1 C2} f x y.
Arguments tensor_mor_omega_cont_R {R Ar} G {C1 C2} u uch ub1 LHS_norm.

(** ** Monotonicity of [tensor_mor (icones_id G) ·] — the workhorse for Yfix

    Dual to [tensor_mor_omega_cont_R].  Given a [precone_le prev1 prev2]
    of [linhom_car C1 C2] (with both norms [≤ 1]), the [linhom_car]
    shadow [tensor_mor_R_lin G ·] is monotone in its argument. *)

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

Lemma kleene_lin_0 : kleene_lin 0 = precone_zero. Proof. by []. Qed.

Lemma kleene_lin_S n : kleene_lin n.+1 = Phi (kleene_lin n).
Proof. exact: kleeneS. Qed.

Lemma kleene_lin_ball n : cone_norm (kleene_lin n) <= 1.
Proof. exact: kleene_ball Phi_ball n. Qed.

Lemma kleene_lin_chain n : precone_le (kleene_lin n) (kleene_lin n.+1).
Proof. exact: kleene_chain Phi_incr Phi_ball n. Qed.

(** The linhom-level least fixpoint of [Phi]. *)
Definition linhom_lfp : linhom_car Ar C D := lfp Phi Phi_incr Phi_ball.

Lemma linhom_lfp_norm_le1 : cone_norm linhom_lfp <= 1.
Proof. exact: lfp_ball. Qed.

End LinhomLFP.

Arguments kleene_lin {R Ar C D} Phi n.
Arguments linhom_lfp {R Ar C D} Phi Phi_incr Phi_ball.
Arguments linhom_lfp_norm_le1 {R Ar C D} Phi Phi_incr Phi_ball.
Arguments kleene_lin_ball {R Ar C D} Phi Phi_ball n.
Arguments kleene_lin_chain {R Ar C D} Phi Phi_incr Phi_ball n.

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
    the unit-ball one via [cone_sup_at_indep] + [cone_sup_at_ball]. *)
Lemma Phi_scott_unit : is_scott_continuous_unit Phi.
Proof.
move=> Mf u uch ub1 fuch fubMf Mfpos.
have Pub1 n : cone_norm (Phi (u n)) <= 1 by apply: Phi_ball; exact: ub1.
have Pub1' n : cone_norm ((Phi \o u) n) <= (1%:nng : {nonneg _})%:num.
  exact: Pub1.
rewrite (cone_sup_at_indep fuch fubMf Pub1' Mfpos ltr01).
rewrite (cone_sup_at_ball fuch Pub1 Pub1' ltr01).
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
      (ω-continuous in prev via [tensor_mor_omega_cont_R]; monotone via
      [tensor_mor_R_lin_incr]);
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

(** ** ω-continuity of [Phi_fun] *)

Lemma Phi_fun_omega_cont
    (u : nat -> linhom_car Ar Gamma B)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, cone_norm (u n) <= 1)
    (Pch : forall n, precone_le (Phi_fun (u n)) (Phi_fun (u n.+1)))
    (Pub1 : forall n, cone_norm (Phi_fun (u n)) <= 1) :
  Phi_fun (cone_sup_ball u uch ub1) =
  cone_sup_ball (Phi_fun \o u) Pch Pub1.
Proof.
have S_ub : cone_norm (cone_sup_ball u uch ub1) <= 1
  by exact: cone_sup_ball_norm.
rewrite (Phi_fun_unit S_ub).
rewrite /Phi_fun_safe.
(* Layer 1: tensor_mor_R_lin Gamma. *)
pose T_n (n : nat) := tensor_mor_R_lin Gamma
  (linhom_icones (u n) (ub1 n)).
have Tch : forall n, precone_le (T_n n) (T_n n.+1).
  by move=> n; rewrite /T_n; exact: tensor_mor_R_lin_incr.
have Tub1 : forall n, cone_norm (T_n n) <= 1.
  by move=> n; rewrite /T_n; exact: tensor_mor_R_lin_norm_le1.
have step1 : tensor_mor_R_lin Gamma
              (linhom_icones (cone_sup_ball u uch ub1) S_ub) =
             cone_sup_ball T_n Tch Tub1.
  exact: tensor_mor_omega_cont_R.
rewrite step1.
(* Layer 2: linhom_pre_act diag. *)
pose P_n (n : nat) := linhom_pre_act diag (T_n n).
have Pch2 : forall n, precone_le (P_n n) (P_n n.+1).
  move=> n; rewrite /P_n.
  rewrite -!linhom_pre_iconesE.
  apply: linear_increasing.
    exact: cones_hom_linear (mcones_hom_cones
             (icones_hom_mcones (linhom_pre_icones diag))).
  exact: Tch.
have Pub2 : forall n, cone_norm (P_n n) <= 1.
  move=> n; rewrite /P_n.
  rewrite -linhom_pre_iconesE.
  apply: le_trans (cones_hom_norm_le1
                     (mcones_hom_cones (icones_hom_mcones
                       (linhom_pre_icones diag))) _) _.
  exact: Tub1.
rewrite (linhom_pre_icones_sup diag T_n Tch Tub1 Pch2 Pub2).
(* Layer 3: linhom_post M. *)
pose Q_n (n : nat) := linhom_post M (P_n n).
have Qch : forall n, precone_le (Q_n n) (Q_n n.+1).
  move=> n; rewrite /Q_n /P_n.
  rewrite -!linhom_post_iconesE.
  apply: linear_increasing.
    exact: cones_hom_linear (mcones_hom_cones
             (icones_hom_mcones (linhom_post_icones M))).
  exact: Pch2.
have Qub : forall n, cone_norm (Q_n n) <= 1.
  move=> n; rewrite /Q_n.
  rewrite -linhom_post_iconesE.
  apply: le_trans (cones_hom_norm_le1
                     (mcones_hom_cones (icones_hom_mcones
                       (linhom_post_icones M))) _) _.
  exact: Pub2.
rewrite (linhom_post_icones_sup M P_n Pch2 Pub2 Qch Qub).
(* RHS: the goal sup is over the chain [Phi_fun \o u], which on
   unit-ball u_n equals [Phi_fun_safe (u n) (ub1 n)]. *)
apply: precone_le_anti.
- apply: cone_sup_ball_lub => n.
  rewrite -[(_ \o _) n]/(linhom_post M (P_n n)).
  have HE : linhom_post M (P_n n) =
            Phi_fun (u n).
    rewrite (Phi_fun_unit (ub1 n)).
    rewrite /Phi_fun_safe /Q_n /P_n /T_n.
    by [].
  rewrite HE.
  exact: cone_sup_ball_ub.
- apply: cone_sup_ball_lub => n.
  have HE : (Phi_fun \o u) n =
            linhom_post M (P_n n).
    rewrite /=.
    rewrite (Phi_fun_unit (ub1 n)).
    rewrite /Phi_fun_safe /Q_n /P_n /T_n.
    by [].
  rewrite HE.
  rewrite -[linhom_post _ (P_n n)]
          /((fun n0 => linhom_post M (P_n n0)) n).
  exact: cone_sup_ball_ub.
Qed.

(** ** The linhom-level CBV value-fixpoint [Yfix_fun_lin] *)

Definition Yfix_fun_lin : linhom_car Ar Gamma B :=
  linhom_lfp Phi_fun Phi_fun_incr Phi_fun_ball.

Lemma Yfix_fun_lin_norm_le1 : cone_norm Yfix_fun_lin <= 1.
Proof. exact: linhom_lfp_norm_le1. Qed.

(** The fixpoint equation: [Phi_fun (Yfix_fun_lin) = Yfix_fun_lin]. *)
Lemma Yfix_fun_lin_fixpoint : Phi_fun Yfix_fun_lin = Yfix_fun_lin.
Proof.
exact: (linhom_lfp_fixpoint Phi_fun Phi_fun_incr Phi_fun_ball
          Phi_fun_omega_cont).
Qed.

End PhiFun.

Arguments Phi_fun_safe {R Ar Gamma B} diag M prev Hprev.
Arguments Phi_fun {R Ar Gamma B} diag M prev.
Arguments Phi_fun_unit {R Ar Gamma B} diag M prev Hprev.
Arguments Phi_fun_safe_ball {R Ar Gamma B} diag M prev Hprev.
Arguments Phi_fun_ball {R Ar Gamma B} diag M prev.
Arguments Phi_fun_safe_incr {R Ar Gamma B} diag M prev1 prev2 Hprev1 Hprev2.
Arguments Phi_fun_incr {R Ar Gamma B} diag M prev1 prev2.
Arguments Phi_fun_omega_cont {R Ar Gamma B} diag M u uch ub1 Pch Pub1.
Arguments Yfix_fun_lin {R Ar Gamma B} diag M.
Arguments Yfix_fun_lin_norm_le1 {R Ar Gamma B} diag M.
Arguments Yfix_fun_lin_fixpoint {R Ar Gamma B} diag M.
