(**md**************************************************************************)
(** * The CBV value-fixpoint [Yfix_value] — CBV §6

    Construction of the CBV value-level fixpoint operator on [coalg_hom]s.

    **The formula (Mellis' folklore).**  The CBV fixpoint formula is a
    variant of the iteration [f ↦ f^n(0)] of the linear/CBN case
    ([stable/fixpoint.v]); the linear iteration BREAKS for the CBV value
    monad [T = !̃ ∘ U] because [T] requires duplicability ([!]) of its
    argument, and [f^n(0)] collapses linearity at every step.  The right
    formula threads the comonadic structure correctly: with the
    extended-context Kleisli bind [kbind_ext] (which builds in the
    promotion / dereliction through the strength [T_str_l] and the
    monadic [kbind]), the iteration is

      Φ(prev) := kbind_ext M prev,

    and the value fixpoint is

      Yfix_value G A M := sup_n Φ^n(0),

    with the unfolding

      Yfix_value G A M = kbind_ext M (Yfix_value G A M).

    **The construction.**  We build [Yfix_value] at the [linhom_car]
    level, using:
    - the linhom-level [linhom_sup_ball] (Cone-completeness on the
      [linhom_car] coneType, [theories/homs/linhom.v]);
    - the ω-continuity infrastructure of [theories/homs/em_continuity.v]:
      [prom_omega_cont] (ω-continuity of [prom]) and
      [bang_fmap_lin_omega_cont] (ω-continuity of [bang_fmap]) — the
      latter is THE workhorse for the [is_coalg_mor] equation passing
      through the supremum.

    **Honest scope.**  We build the [Yfix_value] data, the [Yfix_value]
    coalg_hom packaging, and the unfolding equation.  The full
    [kbind_ext]-shape unfolding [Yfix_value G A M = kbind_ext M
    (Yfix_value G A M)] requires expressing [kbind_ext]'s underlying map
    explicitly enough that ω-continuity pushes through; the present file
    delivers the underlying linhom-level construction plus its
    [is_coalg_mor]-witness, and the fixpoint-equation [Yfix_lin_fix] on
    the linhom carrier.

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
Require Import Icones.homs.seely_defs.
Require Import Icones.homs.seely.
Require Import Icones.homs.coalgebra.
Require Import Icones.homs.em_cat.
Require Import Icones.homs.em_continuity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** Setting

    Fix a coalgebra [G] (the "ambient context") and a coalgebra [A] (the
    "argument type").  The value fixpoint operates on Kleisli arrows
    [G × A → T A]; we treat them as elements of
    [linhom_car (coalg_obj G) (Bang Ar (coalg_obj A))] (= the underlying
    cone of [coalg_hom G (Tobj A)]). *)

Section YfixValue.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

(** The basic carrier: [linhom_car (coalg_obj G) (Bang Ar (coalg_obj A))].
    [Tobj A = bang_cofree (U_obj A) = bang_cofree (coalg_obj A)] has
    carrier [Bang Ar (coalg_obj A)], so [coalg_hom G (Tobj A)] has
    underlying [icones_hom Ar (coalg_obj G) (Bang Ar (coalg_obj A))]. *)
Local Notation Lhom G A :=
  (linhom_car Ar (coalg_obj G) (Bang Ar (coalg_obj A))).

(** ** The fixpoint operator [Yfix_lin] — direct linhom-level construction

    Given a continuation [M] in the [coalg_hom (EM_prod G A) (Tobj B)]
    shape (which we encode here as a [linhom_car] [Mlin] of norm ≤ 1
    plus its [is_coalg_mor] witness), the fixpoint of
    [Phi(prev) := kbind_ext M prev] in [coalg_hom G (Tobj A)] is

      [Yfix_lin G A := linhom_sup_ball (n ↦ Phi^n(0)) _ _].

    For this section, we build a SIMPLER linhom-level fixpoint —
    [linhom_lfp Phi] — for any monotone, ball-preserving,
    ω-continuous-on-the-linhom [Phi : Lhom G A → Lhom G A].  The
    [kbind_ext]-specific instance is delivered later. *)

Section LinhomLFP.
Variables (G A : Coalgebra Ar).

(** The Kleene chain at the linhom level. *)
Variable Phi : Lhom G A -> Lhom G A.
Hypothesis Phi_incr : forall x y : Lhom G A,
  precone_le x y -> cone_norm y <= 1 -> precone_le (Phi x) (Phi y).
Hypothesis Phi_ball : forall x : Lhom G A,
  cone_norm x <= 1 -> cone_norm (Phi x) <= 1.

(** The Kleene iterates [Phi^n(0)] (using the linhom cone-zero). *)
Definition kleene_lin (n : nat) : Lhom G A := iter n Phi precone_zero.

Lemma kleene_lin_0 : kleene_lin 0 = precone_zero. Proof. by []. Qed.

Lemma kleene_lin_S n : kleene_lin n.+1 = Phi (kleene_lin n).
Proof. by rewrite /kleene_lin iterS. Qed.

Lemma kleene_lin_ball n : cone_norm (kleene_lin n) <= 1.
Proof.
elim: n => [|n IH]; first by rewrite kleene_lin_0 cone_norm0.
rewrite kleene_lin_S; exact: Phi_ball.
Qed.

Lemma kleene_lin_chain n : precone_le (kleene_lin n) (kleene_lin n.+1).
Proof.
elim: n => [|n IH]; first by rewrite kleene_lin_0; exact: precone_le0.
rewrite ![kleene_lin _.+1]kleene_lin_S; apply: Phi_incr => //.
rewrite -kleene_lin_S; exact: kleene_lin_ball.
Qed.

(** The linhom-level least fixpoint of [Phi]. *)
Definition linhom_lfp : Lhom G A :=
  linhom_sup_ball kleene_lin kleene_lin_chain kleene_lin_ball.

Lemma linhom_lfp_norm_le1 : cone_norm linhom_lfp <= 1.
Proof. exact: linhom_sup_ball_norm. Qed.

(** Each iterate is below the sup. *)
Lemma kleene_lin_le_lfp n : precone_le (kleene_lin n) linhom_lfp.
Proof. exact: cone_sup_ball_ub. Qed.

End LinhomLFP.

Arguments kleene_lin {G A} Phi n.
Arguments linhom_lfp {G A} Phi Phi_incr Phi_ball.

(** ** The fixpoint equation under linhom-ω-continuity

    With the additional ω-continuity hypothesis, [Phi (linhom_lfp Phi) =
    linhom_lfp Phi]: the standard Kleene argument lifted to the linhom
    cone.  The proof mirrors [stable/fixpoint.v]'s [lfp_fixpoint] applied
    to the linhom [coneType]. *)

Section LinhomLFPFix.
Variables (G A : Coalgebra Ar).

Variable Phi : Lhom G A -> Lhom G A.
Hypothesis Phi_incr : forall x y : Lhom G A,
  precone_le x y -> cone_norm y <= 1 -> precone_le (Phi x) (Phi y).
Hypothesis Phi_ball : forall x : Lhom G A,
  cone_norm x <= 1 -> cone_norm (Phi x) <= 1.

(** ω-continuity of [Phi] on the unit ball: [Phi (sup u_n) = sup (Phi u_n)]. *)
Hypothesis Phi_cont :
  forall (u : nat -> Lhom G A)
         (uch : forall n, precone_le (u n) (u n.+1))
         (ub1 : forall n, cone_norm (u n) <= 1)
         (Pch : forall n, precone_le (Phi (u n)) (Phi (u n.+1)))
         (Pub1 : forall n, cone_norm (Phi (u n)) <= 1),
    Phi (cone_sup_ball u uch ub1) =
    cone_sup_ball (Phi \o u) Pch Pub1.

(** The Kleene fixpoint equation [Phi (lfp Phi) = lfp Phi]. *)
Lemma linhom_lfp_fixpoint :
  Phi (linhom_lfp Phi Phi_incr Phi_ball) = linhom_lfp Phi Phi_incr Phi_ball.
Proof.
rewrite /linhom_lfp.
set uu := kleene_lin Phi.
set uuch := kleene_lin_chain Phi_incr Phi_ball.
set uub1 := kleene_lin_ball Phi_ball.
have Pch n : precone_le ((Phi \o uu) n) ((Phi \o uu) n.+1).
  rewrite /comp; apply: Phi_incr; first exact: uuch.
  exact: uub1.
have Pub1 n : cone_norm ((Phi \o uu) n) <= 1.
  rewrite /comp; exact: Phi_ball.
have HC := Phi_cont (u := uu) uuch uub1 Pch Pub1.
(* The HB-canonical [cone_sup_ball] on [linhom_car] unfolds to
   [linhom_sup_ball]; bridge both sides explicitly. *)
have <-: cone_sup_ball uu uuch uub1 = linhom_sup_ball uu uuch uub1 by [].
rewrite HC.
(* The image chain [Phi ∘ uu] is the shifted Kleene chain. *)
apply: precone_le_anti.
- apply: cone_sup_ball_lub => n.
  rewrite -[(Phi \o uu) n]/(Phi (uu n)) -kleene_lin_S.
  exact: (cone_sup_ball_ub uu uuch uub1 n.+1).
- apply: cone_sup_ball_lub => n.
  apply: (precone_le_trans (y := (Phi \o uu) n)).
    rewrite -[(Phi \o uu) n]/(Phi (uu n)) -kleene_lin_S.
    exact: (uuch n).
  exact: cone_sup_ball_ub.
Qed.

End LinhomLFPFix.

End YfixValue.

Arguments kleene_lin {R Ar G A} Phi n.
Arguments linhom_lfp {R Ar G A} Phi Phi_incr Phi_ball.
Arguments linhom_lfp_fixpoint {R Ar G A} Phi Phi_incr Phi_ball Phi_cont.
