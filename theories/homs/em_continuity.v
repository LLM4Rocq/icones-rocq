(**md**************************************************************************)
(** * ω-continuity prerequisites for the CBV value fixpoint — CBV §6 (prep)

    Prerequisites for the CBV value fixpoint construction
    ([theories/homs/em_fix.v]).  We package the genuinely-new ω-continuity
    facts at the icones / EM(!) level that the fixpoint formula needs.

    The fundamental construction is:

    - [coalg_hom_sup_pack G P u uch ub1 Hcoalg]: take an ω-chain of
      bundled coalgebra morphisms whose underlying [linhom_car]s are in
      the unit ball, and produce a bundled [coalg_hom G P] whose
      underlying [icones_hom] is the linhom-cone supremum.

    The proof uses:
    - the existing [linhom_sup_ball] (a sup of a linhom-chain is a
      linhom_car of norm ≤ 1, [theories/homs/linhom.v]);
    - the bridge [linhom_icones] / [icones_to_linhom] of
      [tensor_hom_iso.v] / [seely.v] turning a norm-≤-1 linhom_car into
      an icones_hom;
    - the ω-continuity of the icones_homs [linhom_post_icones g] and
      [linhom_pre_icones h] (which IS the ω-continuity of the cones_hom_fun
      of any icones_hom).

    The headline ω-continuity facts (all stated at the linhom level, where
    the [cone_sup_ball] of [linhom_car] is the genuine pointwise sup
    [linhom_sup_ball]):

    - [linhom_post_icones_sup] : [g ∘ (sup u) = sup (g ∘ u)] for
      [g : icones_hom D1 D2] and an ω-chain [u] in the unit ball of
      [linhom_car C D1].
    - [linhom_pre_icones_sup] : [(sup u) ∘ h = sup (u ∘ h)] for
      [h : icones_hom C2 C1].

    Combining these with [is_coalg_mor]'s point-free shape gives the
    headline [coalg_hom_sup_is_mor]: the [is_coalg_mor] equation passes
    through the linhom supremum.  Hence [coalg_hom_sup_pack] builds a
    well-formed [coalg_hom].

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
Require Import Icones.stable.scones_cat.
Require Import Icones.homs.linhom.
Require Import Icones.homs.linhom_functor.
Require Import Icones.homs.exp_adjunction.
Require Import Icones.homs.bang.
Require Import Icones.homs.coalgebra.
Require Import Icones.homs.em_cat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** Common shorthands and the [icones_to_linhom] helper

    We re-derive a local [icones_to_linhom] (the one in [tensor_hom_iso.v]
    has the same signature but lives in a heavier import chain).  Norm
    bound from [cones_hom_norm_le1] in [icone_cat.v]. *)

Section IConesToLinhomLocal.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : ICone.type Ar.

Local Notation Lfun h := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

Variable h : icones_hom Ar B C.

Local Lemma i2l_bd : exists M : R, forall x : B, cone_norm x <= 1 ->
    cone_norm (Lfun h x) <= M.
Proof.
exists 1 => x Hx; apply: le_trans Hx; exact: cones_hom_norm_le1.
Qed.

Local Definition i2l_pre : linhom_pre Ar B C :=
  MkLinhomPre (Lfun h)
    (@cones_hom_linear R _ _ (mcones_hom_cones (icones_hom_mcones h)))
    (@cones_hom_continuous R _ _ (mcones_hom_cones (icones_hom_mcones h)))
    i2l_bd
    (fun X g Hg => mcones_hom_pres_path (icones_hom_mcones h) X g Hg).

Local Lemma i2l_int_pres
    (X : ar_obj Ar) (β : ar_carrier Ar X -> B)
    (Hβ : is_measurable_path β)
    (µ : fmeas R (ar_carrier Ar X)) :
  linhom_pre_fun i2l_pre (icone_integral β Hβ µ) =
  icone_integral
    (fun r => linhom_pre_fun i2l_pre (β r))
    (linhom_pre_pres_path i2l_pre X β Hβ) µ.
Proof.
rewrite /i2l_pre /= (icones_hom_pres_int h X β Hβ µ).
by congr icone_integral; exact: Prop_irrelevance.
Qed.

Definition icones_as_linhom : linhom_car Ar B C :=
  MkLinhom i2l_pre i2l_int_pres.

Lemma icones_as_linhomE (x : B) : linhom_fun icones_as_linhom x = Lfun h x.
Proof. by []. Qed.

Lemma icones_as_linhom_norm_le1 : cone_norm icones_as_linhom <= 1.
Proof.
rewrite -[cone_norm _]/(linhom_norm icones_as_linhom).
apply: linhom_norm_sup_lub => x Hx.
by apply: le_trans (cones_hom_norm_le1 _ x) _.
Qed.

End IConesToLinhomLocal.

Arguments icones_as_linhom {R Ar B C} h.
Arguments icones_as_linhomE {R Ar B C} h.
Arguments icones_as_linhom_norm_le1 {R Ar B C} h.

(** ** ω-continuity of pre/post composition by an icones_hom

    These are CONSEQUENCES (NOT new theorems) of the fact that
    [linhom_post_icones g] is an icones_hom, hence its underlying
    [cones_hom_fun] is ω-continuous on the unit ball.  We expose the
    equation in the form we need downstream. *)

Section LinhomPostPreSup.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

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
    (hch : forall n, precone_le (linhom_pre_act h (u n)) (linhom_pre_act h (u n.+1)))
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

(** ** ω-continuity of [prom] — Paper §9

    The promotion [x ↦ x! = sc_fun (nl B) x] is ω-continuous on the unit
    ball of [B] with image in the unit ball of [!B].  This is the
    [is_scott_continuous_unit] field of [nl B]'s [sc_meas_stable], reduced
    via [cone_sup_at_ball] (image radius = 1, since [‖x!‖ ≤ 1] for
    [‖x‖ ≤ 1] by [prom_ball]). *)

Section PromContinuous.
Variables (R : realType) (Ar : MeasSubcat R).

Lemma prom_omega_cont (B : ICone.type Ar)
    (y : nat -> B)
    (ych : forall n, precone_le (y n) (y n.+1))
    (yub1 : forall n, cone_norm (y n) <= 1)
    (pch : forall n, precone_le (prom (y n)) (prom (y n.+1)))
    (pub1 : forall n, cone_norm (prom (y n)) <= 1) :
  prom (cone_sup_ball y ych yub1) =
  cone_sup_ball (prom \o y) pch pub1.
Proof.
have [[_ _ Hsc] _] := sc_meas_stable (nl B).
move: Hsc; rewrite /is_scott_continuous_unit => Hsc.
have pubM : forall n, cone_norm ((prom \o y) n) <= (1%:nng : {nonneg R})%:num.
  by move=> n /=; exact: pub1.
have HE : prom (cone_sup_ball y ych yub1) =
          cone_sup_at (u := prom \o y) pch pubM ltr01.
  exact: (Hsc 1%:nng y ych yub1 pch pubM ltr01).
by rewrite HE (cone_sup_at_ball pch pub1 pubM ltr01).
Qed.

End PromContinuous.

Arguments prom_omega_cont {R Ar B} y.
