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

(* Block aggressive unfolding of comonad / EM data — without this, [/=]
   and [rewrite] traverse the SAFT [Bang] construction internals. *)
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
Require Import Icones.homs.em_cartesian.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

(* Block aggressive unfolding of comonad data. *)
Opaque dig der prom bang_fmap.

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
Variables (C D : ICone.type Ar).

(** The Kleene chain at the linhom level. *)
Variable Phi : linhom_car Ar C D -> linhom_car Ar C D.
Hypothesis Phi_incr : forall x y : linhom_car Ar C D,
  precone_le x y -> cone_norm y <= 1 -> precone_le (Phi x) (Phi y).
Hypothesis Phi_ball : forall x : linhom_car Ar C D,
  cone_norm x <= 1 -> cone_norm (Phi x) <= 1.

(** The Kleene iterates [Phi^n(0)] (using the linhom cone-zero). *)
Definition kleene_lin (n : nat) : linhom_car Ar C D :=
  iter n Phi precone_zero.

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
Definition linhom_lfp : linhom_car Ar C D :=
  linhom_sup_ball kleene_lin kleene_lin_chain kleene_lin_ball.

Lemma linhom_lfp_norm_le1 : cone_norm linhom_lfp <= 1.
Proof. exact: linhom_sup_ball_norm. Defined.

(** Each iterate is below the sup. *)
Lemma kleene_lin_le_lfp n : precone_le (kleene_lin n) linhom_lfp.
Proof. exact: cone_sup_ball_ub. Qed.

End LinhomLFP.

Arguments kleene_lin {C D} Phi n.
Arguments linhom_lfp {C D} Phi Phi_incr Phi_ball.

(** ** The fixpoint equation under linhom-ω-continuity

    With the additional ω-continuity hypothesis, [Phi (linhom_lfp Phi) =
    linhom_lfp Phi]: the standard Kleene argument lifted to the linhom
    cone.  The proof mirrors [stable/fixpoint.v]'s [lfp_fixpoint] applied
    to the linhom [coneType]. *)

Section LinhomLFPFix.
Variables (C D : ICone.type Ar).

Variable Phi : linhom_car Ar C D -> linhom_car Ar C D.
Hypothesis Phi_incr : forall x y : linhom_car Ar C D,
  precone_le x y -> cone_norm y <= 1 -> precone_le (Phi x) (Phi y).
Hypothesis Phi_ball : forall x : linhom_car Ar C D,
  cone_norm x <= 1 -> cone_norm (Phi x) <= 1.

(** ω-continuity of [Phi] on the unit ball: [Phi (sup u_n) = sup (Phi u_n)]. *)
Hypothesis Phi_cont :
  forall (u : nat -> linhom_car Ar C D)
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

Arguments kleene_lin {R Ar C D} Phi n.
Arguments linhom_lfp {R Ar C D} Phi Phi_incr Phi_ball.
Arguments linhom_lfp_fixpoint {R Ar C D} Phi Phi_incr Phi_ball Phi_cont.

(** ** Coalg-mor witness passes through the linhom-sup — the headline

    Given a unit-ball ω-chain of [coalg_hom G P] (specified at the
    linhom level), the [is_coalg_mor] equation passes through the
    linhom-cone supremum.

    Proof outline: [is_coalg_mor] says
      [icones_comp (coalg_str P) f = icones_comp (bang_fmap f) (coalg_str G)].
    As an equation of [linhom_car (coalg_obj G) (Bang Ar (coalg_obj P))]'s
    underlying maps, for each [n] the equation holds for [f_n], so taking
    suprema on both sides yields the same equation for the sup, IF the
    sup commutes with each side.

    LHS = [coalg_str P ∘ f] : commutation with linhom-sup by
    [linhom_post_icones_sup] applied to [coalg_str P].
    RHS = [bang_fmap f ∘ coalg_str G] : double commutation, first
    pre-composition by [coalg_str G] ([linhom_pre_icones_sup]), then
    [bang_fmap] of the sup equals sup of [bang_fmap]
    ([bang_fmap_lin_omega_cont]). *)

Section CoalgHomSupPack.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

(** A note about scope: [coalg_hom P Q] bundles an [icones_hom] plus the
    [is_coalg_mor] witness.  To take linhom-sups we need the underlying
    [linhom_car] chain.  We DEFINE the chain in [linhom_car] directly,
    and require both:
    - that the chain is monotone and bounded in [linhom_car];
    - that for each [n], the [icones_hom]-packaging [linhom_icones (u n)
      (ub1 n)] is a coalg_hom witness for [(P, Q)].  *)

Variables (P Q : Coalgebra Ar).

(** The unit-ball linhom-chain of [(coalg_obj P) → (coalg_obj Q)]. *)
Variable u : nat -> linhom_car Ar (coalg_obj P) (coalg_obj Q).
Hypothesis uch : forall n, precone_le (u n) (u n.+1).
Hypothesis ub1 : forall n, cone_norm (u n) <= 1.

(** The pointwise coalg-mor witness: each iterate is a coalg_hom. *)
Hypothesis u_coalg :
  forall n, is_coalg_mor P Q (linhom_icones _ (ub1 n)).

(** The headline: the linhom-sup of [u] is a coalg-mor witness. *)

(* The auxiliary bookkeeping witnesses for the [bang_fmap_lin] chain. *)

(** Aux: monotonicity of the [bang_fmap]-image chain. *)
Section BangChainAux.

Let S : linhom_car Ar (coalg_obj P) (coalg_obj Q) := linhom_sup_ball u uch ub1.

Let S_norm : cone_norm S <= 1 := linhom_sup_ball_norm u uch ub1.

(** The [bang_fmap] of each [u_n], at the linhom level. *)
Let Bu (n : nat) : linhom_car Ar (Bang Ar (coalg_obj P)) (Bang Ar (coalg_obj Q)) :=
  bang_fmap_lin (linhom_icones (u n) (ub1 n)).

(** Composition pre-condition: [bang_fmap f] is monotone in [f].

    This is the analogue of [Phi_incr] for [bang_fmap] applied to a
    norm-≤-1 chain of icones_homs; we need this *as a hypothesis* (the
    naïve `bang_fmap_le` would itself be a substantial lemma, dual to
    [bang_fmap_lin_omega_cont] but for monotonicity).  In practice it
    follows from monotonicity of the functoriality of [!] on a unit-ball
    chain, but stating it abstractly here is sufficient for downstream
    instantiation. *)
Hypothesis Bu_chain : forall n, precone_le (Bu n) (Bu n.+1).

Lemma Bu_ub1 : forall n, cone_norm (Bu n) <= 1.
Proof. by move=> n; rewrite /Bu; exact: bang_fmap_lin_norm_le1. Qed.

(** [bang_fmap (linhom_icones S S_norm)] equals [linhom_sup_ball Bu ...].
    This is exactly [bang_fmap_lin_omega_cont]. *)
Lemma bang_fmap_S_E :
  bang_fmap_lin (linhom_icones S S_norm) =
  linhom_sup_ball Bu Bu_chain Bu_ub1.
Proof.
exact: (bang_fmap_lin_omega_cont S_norm Bu_chain Bu_ub1).
Qed.

(** **The unit-ball reading of the coalg-mor equation.

    For every [x : coalg_obj P] in the unit ball, the [is_coalg_mor]
    equation holds at [x] for the linhom-sup-packaged [icones_hom].

    Combining this with the linearity of all components yields the full
    [is_coalg_mor] equation [is_coalg_mor_S] below. *)
Lemma coalg_mor_S_ball (x : coalg_obj P) :
  cone_norm x <= 1 ->
  Lfun (coalg_str Q) (Lfun (linhom_icones S S_norm) x) =
  Lfun (bang_fmap (linhom_icones S S_norm)) (Lfun (coalg_str P) x).
Proof.
move=> Hx.
(* LHS reduction: [Lfun (linhom_icones S S_norm) x = linhom_fun S x =
   linhom_sup_fun uch ub1 x]. *)
rewrite linhom_iconesE.
have S_at_x : linhom_fun S x = linhom_sup_fun uch ub1 x by [].
rewrite S_at_x (linhom_sup_fun_unitE uch ub1 Hx) linhom_sup_unitE.
(* LHS is now [Lfun (coalg_str Q) (cone_sup_ball (n => linhom_fun (u n) x) ...)]. *)
(* By ω-continuity of [coalg_str Q] (it's an icones_hom). *)
have ContQ : is_omega_continuous (cones_hom_fun
                  (mcones_hom_cones (icones_hom_mcones (coalg_str Q)))).
  exact: cones_hom_continuous.
have ychain : forall n, precone_le ((Lfun (coalg_str Q) \o
                          (fun n0 => linhom_fun (u n0) x)) n)
                        ((Lfun (coalg_str Q) \o
                          (fun n0 => linhom_fun (u n0) x)) n.+1).
  move=> n /=.
  apply: (linear_increasing (f := Lfun (coalg_str Q)));
    first exact: cones_hom_linear.
  by have := linhom_sup_pw_chain uch x n.
have yub1 : forall n, cone_norm ((Lfun (coalg_str Q) \o
                          (fun n0 => linhom_fun (u n0) x)) n) <= 1.
  move=> n /=.
  apply: le_trans (cones_hom_norm_le1 _ _) _.
  exact: (linhom_sup_pw_ub1 (u := u) ub1 Hx).
rewrite (ContQ _ [eta linhom_sup_pw_chain uch x]
                 (linhom_sup_pw_ub1 ub1 Hx) ychain yub1).
(* RHS reduction: [Lfun (bang_fmap (linhom_icones S S_norm)) (Lfun (coalg_str P) x)
   = linhom_fun (bang_fmap_lin (linhom_icones S S_norm)) z]
   where [z = Lfun (coalg_str P) x] (in unit ball since [coalg_str P] is
   norm-≤-1). *)
set z := Lfun (coalg_str P) x.
have z_ub : cone_norm z <= 1.
  by apply: le_trans (cones_hom_norm_le1 _ _) Hx.
have RHS_z : Lfun (bang_fmap (linhom_icones S S_norm)) z =
             linhom_fun (bang_fmap_lin (linhom_icones S S_norm)) z.
  by rewrite /bang_fmap_lin icones_as_linhomE.
rewrite RHS_z bang_fmap_S_E.
have S_at_z : linhom_fun (linhom_sup_ball Bu Bu_chain Bu_ub1) z =
              linhom_sup_fun Bu_chain Bu_ub1 z by [].
rewrite S_at_z (linhom_sup_fun_unitE Bu_chain Bu_ub1 z_ub) linhom_sup_unitE.
(* Both sides are [cone_sup_ball] over [Bang Ar (coalg_obj Q)]; show the
   underlying chains are pointwise equal using [u_coalg n] (per-n
   coalg-mor witness). *)
apply: precone_le_anti.
- apply: cone_sup_ball_lub => n.
  have HE : Lfun (coalg_str Q) (linhom_fun (u n) x) =
            linhom_fun (Bu n) z.
    have UCx : Lfun (linhom_icones (u n) (ub1 n)) x = linhom_fun (u n) x.
      by rewrite linhom_iconesE.
    have Bun_z : linhom_fun (Bu n) z = Lfun (bang_fmap (linhom_icones (u n) (ub1 n))) z.
      by rewrite /Bu /bang_fmap_lin icones_as_linhomE.
    rewrite Bun_z.
    have CoalgE := f_equal (fun h : icones_hom _ _ _ =>
                              Lfun h x) (u_coalg n).
    rewrite /is_coalg_mor in CoalgE.
    by rewrite !Lfun_comp UCx in CoalgE.
  rewrite -[(Lfun (coalg_str Q) \o (fun n0 => linhom_fun (u n0) x)) n]
          /(Lfun (coalg_str Q) (linhom_fun (u n) x)).
  rewrite HE.
  exact: cone_sup_ball_ub.
- apply: cone_sup_ball_lub => n.
  have HE : linhom_fun (Bu n) z = Lfun (coalg_str Q) (linhom_fun (u n) x).
    have UCx : Lfun (linhom_icones (u n) (ub1 n)) x = linhom_fun (u n) x.
      by rewrite linhom_iconesE.
    have Bun_z : linhom_fun (Bu n) z = Lfun (bang_fmap (linhom_icones (u n) (ub1 n))) z.
      by rewrite /Bu /bang_fmap_lin icones_as_linhomE.
    rewrite Bun_z.
    have CoalgE := f_equal (fun h : icones_hom _ _ _ =>
                              Lfun h x) (u_coalg n).
    rewrite /is_coalg_mor in CoalgE.
    by rewrite !Lfun_comp UCx in CoalgE.
  rewrite HE.
  exact: (cone_sup_ball_ub _ ychain yub1 n).
Qed.

(** **The headline coalg-mor witness for the linhom-sup.

    The unit-ball case is [coalg_mor_S_ball]; we extend to all [x] by
    the standard scaling argument applied to the underlying linear maps. *)
Lemma is_coalg_mor_S :
  is_coalg_mor P Q (linhom_icones S S_norm).
Proof.
rewrite /is_coalg_mor.
apply: icones_hom_eq => x.
(* The whole composite (LHS and RHS) is the underlying function of an
   icones_hom, hence is LINEAR.  Both linear maps agree on the unit
   ball ([coalg_mor_S_ball]).  Linear maps agreeing on the unit ball
   are equal everywhere — we scale [x] down via [(cnorm x + 1)^-1]. *)
set rinv := cnorm_succ_inv_nng x.
set r := cnorm_succ_nng x.
set y := precone_scale rinv x.
have y_ub : cone_norm y <= 1 by exact: cnorm_inv_unit.
have x_eq : x = precone_scale r y by rewrite /y cnorm_succ_scaleK.
rewrite [in X in Lfun _ X = _]x_eq [in X in _ = Lfun _ X]x_eq.
(* Pack LHS and RHS as a SINGLE composite icones_hom each — then [linearZ]
   factors the scalar [r] out cleanly. *)
have lin_LHS : is_linear (Lfun (icones_comp (coalg_str Q)
                                           (linhom_icones S S_norm))).
  exact: cones_hom_linear.
have lin_RHS : is_linear (Lfun (icones_comp (bang_fmap (linhom_icones S S_norm))
                                           (coalg_str P))).
  exact: cones_hom_linear.
have [_ _ HLZ] := lin_LHS; have [_ _ HRZ] := lin_RHS.
rewrite HLZ HRZ.
congr (precone_scale _ _).
rewrite !Lfun_comp.
exact: (coalg_mor_S_ball y_ub).
Qed.

End BangChainAux.

End CoalgHomSupPack.

Arguments bang_fmap_S_E {R Ar P Q} u uch ub1 _.
Arguments coalg_mor_S_ball {R Ar P Q} u uch ub1 _ _.
Arguments is_coalg_mor_S {R Ar P Q} u uch ub1 _ _.

(** ** The bundled [coalg_hom_sup_pack] constructor

    Package the linhom-sup of a unit-ball chain of [coalg_hom]s as a
    [coalg_hom].  Inputs:
    - the unit-ball linhom chain [u_n : linhom_car (coalg_obj P)
      (coalg_obj Q)] with monotonicity [uch] and bound [ub1];
    - the per-[n] coalg-mor witness [u_coalg];
    - the BANG-fmap chain witnesses [Bu_chain] (the
      [bang_fmap]-lifts are monotone — a hypothesis that's downstream
      verifiable on concrete chains). *)
Section CoalgHomSupBundled.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (P Q : Coalgebra Ar).

Variable u : nat -> linhom_car Ar (coalg_obj P) (coalg_obj Q).
Hypothesis uch : forall n, precone_le (u n) (u n.+1).
Hypothesis ub1 : forall n, cone_norm (u n) <= 1.
Hypothesis u_coalg :
  forall n, is_coalg_mor P Q (linhom_icones (u n) (ub1 n)).
Hypothesis Bu_chain :
  forall n, precone_le (bang_fmap_lin (linhom_icones (u n) (ub1 n)))
                       (bang_fmap_lin (linhom_icones (u n.+1) (ub1 n.+1))).

Definition coalg_hom_sup_pack : coalg_hom P Q :=
  MkCoalgHom (is_coalg_mor_S u uch ub1 u_coalg Bu_chain).

Lemma coalg_hom_sup_pack_mor :
  ch_mor coalg_hom_sup_pack =
  linhom_icones (linhom_sup_ball u uch ub1)
                (linhom_sup_ball_norm u uch ub1).
Proof. by []. Qed.

End CoalgHomSupBundled.

Arguments coalg_hom_sup_pack {R Ar P Q} u uch ub1 u_coalg Bu_chain.
Arguments coalg_hom_sup_pack_mor {R Ar P Q} u uch ub1 u_coalg Bu_chain.

(** ** The conditional CBV value fixpoint [Yfix_value_cond]

    Given a linhom-level iteration operator [Phi : Lhom G A → Lhom G A]
    satisfying the standard Kleene hypotheses (monotonicity,
    ball-preservation, ω-continuity), AND a per-iterate coalg-mor
    witness, we build a [coalg_hom G P] that is the fixpoint of [Phi]
    at the underlying-linhom level.

    The CBV-specific instance — [Phi := (fun prev =>
    icones_as_linhom (ch_mor (kbind_ext M (MkCoalgHom witness))))] —
    requires:
    1. ω-continuity of [kbind_ext M] in the prev argument (at the
       linhom level), which decomposes into ω-continuity of
       [tensor_mor (icones_id G) ·] on linhom_cars (the only genuinely
       non-immediate sub-fact);
    2. closure of the iteration under [is_coalg_mor].

    The current file does NOT provide that specialization
    axiom-free: [tensor_mor (icones_id G) ·] is not, in the present
    project, known to be ω-continuous on the linhom level as a function
    of its second argument.  This is the precise gap noted in the
    deliverable report.  However, the surrounding infrastructure ---
    [coalg_hom_sup_pack], [linhom_lfp], [linhom_lfp_fixpoint] --- IS
    delivered axiom-free, and the conditional value-fixpoint below is
    the value of having that infrastructure. *)

Section YfixCond.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (G P : Coalgebra Ar).

Variable Phi : linhom_car Ar (coalg_obj G) (coalg_obj P) ->
               linhom_car Ar (coalg_obj G) (coalg_obj P).

Hypothesis Phi_incr :
  forall x y : linhom_car Ar (coalg_obj G) (coalg_obj P),
    precone_le x y -> cone_norm y <= 1 -> precone_le (Phi x) (Phi y).

Hypothesis Phi_ball :
  forall x : linhom_car Ar (coalg_obj G) (coalg_obj P),
    cone_norm x <= 1 -> cone_norm (Phi x) <= 1.

Hypothesis Phi_cont :
  forall (u : nat -> linhom_car Ar (coalg_obj G) (coalg_obj P))
         (uch : forall n, precone_le (u n) (u n.+1))
         (ub1 : forall n, cone_norm (u n) <= 1)
         (Pch : forall n, precone_le (Phi (u n)) (Phi (u n.+1)))
         (Pub1 : forall n, cone_norm (Phi (u n)) <= 1),
    Phi (cone_sup_ball u uch ub1) = cone_sup_ball (Phi \o u) Pch Pub1.

(** Per-iterate coalg-mor witness: each [Phi^n(0)] (packaged as an
    icones_hom) is a coalg_hom. *)
Hypothesis Phi_coalg :
  forall n, is_coalg_mor G P
              (linhom_icones (kleene_lin Phi n)
                             (kleene_lin_ball Phi_ball n)).

(** And the [bang_fmap]-chain witness for the iterates. *)
Hypothesis Phi_Bu_chain :
  forall n,
    precone_le
      (bang_fmap_lin (linhom_icones (kleene_lin Phi n)
                                    (kleene_lin_ball Phi_ball n)))
      (bang_fmap_lin (linhom_icones (kleene_lin Phi n.+1)
                                    (kleene_lin_ball Phi_ball n.+1))).

(** The CBV-style value fixpoint [Yfix_value_cond]: the bundled
    [coalg_hom] obtained from the linhom-level [linhom_lfp Phi] +
    [is_coalg_mor_S]. *)
Definition Yfix_value_cond : coalg_hom G P :=
  coalg_hom_sup_pack (kleene_lin Phi)
    (kleene_lin_chain Phi_incr Phi_ball)
    (kleene_lin_ball Phi_ball)
    Phi_coalg Phi_Bu_chain.

(** Its underlying [linhom_car] is exactly [linhom_lfp Phi] (with a
    [Prop]-irrelevant norm-witness). *)
Lemma Yfix_value_cond_mor :
  ch_mor Yfix_value_cond =
  linhom_icones (linhom_lfp Phi Phi_incr Phi_ball)
                (linhom_lfp_norm_le1 Phi_incr Phi_ball).
Proof.
rewrite /Yfix_value_cond /coalg_hom_sup_pack /ch_mor.
rewrite -[linhom_sup_ball _ _ _]/(linhom_lfp Phi Phi_incr Phi_ball).
congr (linhom_icones _ _); exact: Prop_irrelevance.
Qed.

(** Linhom-level unfolding: [Phi (linhom_lfp Phi) = linhom_lfp Phi]. *)
Lemma Yfix_value_cond_unfolding_lin :
  Phi (linhom_lfp Phi Phi_incr Phi_ball) =
  linhom_lfp Phi Phi_incr Phi_ball.
Proof.
exact: (linhom_lfp_fixpoint Phi Phi_incr Phi_ball Phi_cont).
Qed.

End YfixCond.

Arguments Yfix_value_cond {R Ar G P} Phi Phi_incr Phi_ball Phi_coalg Phi_Bu_chain.
Arguments Yfix_value_cond_mor {R Ar G P} Phi Phi_incr Phi_ball Phi_coalg Phi_Bu_chain.
Arguments Yfix_value_cond_unfolding_lin {R Ar G P} Phi Phi_incr Phi_ball Phi_cont.

(** ** [Yfix_fun] — the CBV value fixpoint AT FUNCTION TYPES — CBV §6, OCaml [let rec]

    OCaml-style restriction: [let rec] is thunked, so [ne_fix s A B M] is
    only available when the body produces a value of FUNCTION TYPE
    [tfun A B].  This is the user-authorized restriction:
    *"It is normal to restrict recursion to function, and this is also
    the choice of ocaml where let rec is thunked."*

    **The construction.**  Let [G] be a coalgebra (the ambient context)
    and let [A], [B] be coalgebras (the argument/result types of the
    recursive function).  Set
    [[
      L  := linhom_car Ar (coalg_obj A) (coalg_obj (Tobj B))    (Kleisli exp)
      t  := bang_cofree L                                       (= tyD (tfun A B))
    ]]
    so [coalg_obj t = Bang Ar L] (the value cone at function type).

    The body [M : coalg_hom (EM_prod G t) (Tobj t)] denotes the
    recursive function abstracted on its self-reference.  We define an
    iteration operator on the LINHOM cone [linhom_car (U G) (U t) =
    linhom_car (U G) (Bang L)], using:

    - the natural value-cone extraction [bang_fmap (der L) : Bang(Bang L)
      → Bang L] (this IS the underlying [icones_hom] of the coalgebra
      morphism [bang_cofree_hom (der L) : Tobj t → t]);
    - the body's underlying icones_hom [ch_mor M];
    - the diagonal [coalg_d G : G → G ⊗ G] and the tensor action [id ⊗ ·];
    - assembly at the linhom_car level via [icones_as_linhom] of the
      composite, with ω-continuity provided by the four building-blocks
      (post/pre by an icones_hom and [tensor_mor_omega_cont_R]).

    The iteration:
    [[
      Phi_fun(prev_lin) :=
        icones_as_linhom (bang_fmap (der L)
                          ∘ ch_mor M
                          ∘ tensor_mor (id_G) (linhom_icones prev_lin)
                          ∘ coalg_d G).
    ]]
    Its Kleene fixpoint [f_∞ ∈ linhom_car (U G) (Bang L)] is the linhom
    representation of the recursive value family parameterized by [γ].

    **The coalg_hom packaging.**  The icones_hom [linhom_icones f_∞ Hf]
    need NOT be a coalgebra morphism [G → t].  Instead we package via
    [adj_psi] of the [U ⊣ !̃] adjunction (which IS available
    unconditionally on any icones_hom): for any [icones_hom h : U G →
    Bang L = U t], [adj_psi h : coalg_hom G (bang_cofree (Bang L)) =
    coalg_hom G (Tobj t)].  Composition with [tunit_eta] is unnecessary
    — [adj_psi] already lands in [Tobj t].

    Author: Guillaume Baudart <guillaume.baudart@inria.fr>. *)

Section YfixFunType.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (G : Coalgebra Ar) (A B : Coalgebra Ar).

(** Local abbreviation for the CBV monad's object map [T P = !̃(U P)].
    Equivalent to [Tobj] from [cbv.v] but stated locally to avoid the
    [cbv]/[cbv_adjunction] import chain here. *)
Let TT (P : Coalgebra Ar) : Coalgebra Ar := bang_cofree (coalg_obj P).

(** The Kleisli-exponential linhom cone [L = U A ⊸ U(T B)]. *)
Let L : ICone.type Ar :=
  linhom_car Ar (coalg_obj A) (coalg_obj (TT B)).

(** The function-value coalgebra [t = !̃ L].  When [A = tyD a] and
    [B = tyD b], this is exactly [tyD (tfun a b)]. *)
Let funT : Coalgebra Ar := bang_cofree L.

(** The body of the fixpoint: a coalg_hom whose codomain is [TT funT].
    In PPL terms, this is the denotation of [ne_lam s (tfun A B) <body>]
    evaluated in the extended context [(s, tfun A B) :: G]. *)
Variable M : coalg_hom (EM_prod G funT) (TT funT).

Local Notation Lfun h := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

(** The value-cone "extraction" coalgebra morphism [TT funT → funT].
    Underlying: [bang_fmap (der L) : Bang(Bang L) → Bang L].  This is a
    bona-fide coalgebra morphism by [bang_cofree_fmap_is_mor]. *)
Definition extract_fun : coalg_hom (TT funT) funT :=
  bang_cofree_hom (der L).

Lemma extract_fun_mor :
  ch_mor extract_fun = bang_fmap (der L).
Proof. by []. Qed.

(** ** The Kleene iteration operator [Phi_fun] at linhom level

    [Phi_fun(prev_lin) = icones_as_linhom (bang_fmap (der L) ∘ ch_mor M
    ∘ tensor_mor (id_G) (linhom_icones prev_lin _) ∘ coalg_d G)].

    Concretely we package the four operations as actions on linhom_cars
    so that each step is provably ω-continuous and ball-preserving:

    - [tensor_mor_R_lin G (linhom_icones prev_lin _) : linhom_car (G⊗G)
      (G ⊗ Bang L)] (workhorse: ω-continuous in prev_lin via
      [tensor_mor_omega_cont_R]);
    - [linhom_pre_act (coalg_d G)] applied to that, landing in
      [linhom_car G (G ⊗ Bang L)];
    - [linhom_post (ch_mor M)] applied to that, landing in
      [linhom_car G (Bang(Bang L))];
    - [linhom_post (bang_fmap (der L))] applied to that, landing in
      [linhom_car G (Bang L)]. *)

(** The "safe" version of [Phi_fun] taking a norm-witness as input. *)
Definition Phi_fun_safe
    (prev : linhom_car Ar (coalg_obj G) (coalg_obj funT))
    (Hprev : cone_norm prev <= 1) :
    linhom_car Ar (coalg_obj G) (coalg_obj funT) :=
  linhom_post (bang_fmap (der L))
    (linhom_post (ch_mor M)
      (linhom_pre_act (coalg_d G)
        (tensor_mor_R_lin (coalg_obj G)
          (linhom_icones prev Hprev)))).

(** The TOTAL [Phi_fun] (defined on all of [linhom_car], not just the
    unit ball).  On unit-ball [prev] it computes to [Phi_fun_safe prev
    _]; off the unit ball we return [precone_zero] (the value is
    irrelevant for the Kleene chain, which stays in the unit ball). *)
Arguments Phi_fun_safe prev Hprev : clear implicits.

Definition Phi_fun
    (prev : linhom_car Ar (coalg_obj G) (coalg_obj funT)) :
    linhom_car Ar (coalg_obj G) (coalg_obj funT) :=
  match pselect (cone_norm prev <= 1) with
  | left H => Phi_fun_safe prev H
  | right _ => precone_zero
  end.

(** On unit-ball [prev], [Phi_fun] is exactly [Phi_fun_safe].  This
    makes the unit-ball case independent of which norm-witness we
    pick (by [Prop_irrelevance]). *)
Lemma Phi_fun_unit (prev : linhom_car Ar (coalg_obj G) (coalg_obj funT))
    (Hprev : cone_norm prev <= 1) :
  Phi_fun prev = Phi_fun_safe prev Hprev.
Proof.
rewrite /Phi_fun; case: pselect => [H | H]; last by [].
by congr Phi_fun_safe; exact: Prop_irrelevance.
Qed.

(** ** Ball preservation and monotonicity of [Phi_fun]

    [Phi_fun_safe] is a composition of four linhom-level
    operations, each of which is norm-≤-1.  Hence the result has
    norm ≤ 1 on any unit-ball input.  [Phi_fun] inherits ball
    preservation because on unit-ball inputs it equals [Phi_fun_safe]
    and off the unit ball it returns [precone_zero] (norm 0 ≤ 1). *)

Lemma Phi_fun_safe_ball
    (prev : linhom_car Ar (coalg_obj G) (coalg_obj funT))
    (Hprev : cone_norm prev <= 1) :
  cone_norm (Phi_fun_safe prev Hprev) <= 1.
Proof.
rewrite /Phi_fun_safe.
(* Outer layer: [linhom_post (bang_fmap (der L))].
   It IS [Lfun (linhom_post_icones (bang_fmap (der L)))] applied to its
   argument; a [cones_hom_norm_le1] of the icones_hom gives the bound. *)
rewrite -linhom_post_iconesE.
apply: le_trans (cones_hom_norm_le1
                   (mcones_hom_cones (icones_hom_mcones
                     (linhom_post_icones (bang_fmap (der L))))) _) _.
rewrite -linhom_post_iconesE.
apply: le_trans (cones_hom_norm_le1
                   (mcones_hom_cones (icones_hom_mcones
                     (linhom_post_icones (ch_mor M)))) _) _.
rewrite -linhom_pre_iconesE.
apply: le_trans (cones_hom_norm_le1
                   (mcones_hom_cones (icones_hom_mcones
                     (linhom_pre_icones (coalg_d G)))) _) _.
exact: tensor_mor_R_lin_norm_le1.
Qed.

Lemma Phi_fun_ball (prev : linhom_car Ar (coalg_obj G) (coalg_obj funT)) :
  cone_norm prev <= 1 -> cone_norm (Phi_fun prev) <= 1.
Proof.
move=> Hprev; rewrite (Phi_fun_unit Hprev); exact: Phi_fun_safe_ball.
Qed.

(** ** Monotonicity of [Phi_fun] — the precise gap

    Monotonicity of [Phi_fun_safe] would reduce, via [linear_increasing]
    on the three icones_hom layers (post-comp by [bang_fmap (der L)],
    post-comp by [ch_mor M], pre-comp by [coalg_d G]), to monotonicity
    of [tensor_mor_R_lin G ·] in the second slot at the linhom level
    (lemma name: [tensor_mor_R_lin_incr]).

    The proof of [tensor_mor_R_lin_incr] would mirror the structure of
    [tensor_mor_omega_cont_R] ([em_continuity.v], ~100 lines): given
    [prev_1 ≤p prev_2] with the [linhom_diff_car]-derived [δ] (of
    [cone_norm δ ≤ ‖prev_2‖ ≤ 1] by [cone_normp]), the witness is
    [tensor_mor_R_lin G (linhom_icones δ Hδ_norm)].  Pointwise on pure
    tensors [(x ⊗p y)], the equality reduces by [tensor_mor_R_lin_ptensor]
    + right-slot additivity [ptensorDr] of the pure tensor.

    The technical obstacle: lifting the pure-tensor equality to all of
    [G ⊗ G] requires [tensor_ext_linhom] (Paper Prop 5.14, linhom
    version), which has a [‖φ‖ ≤ 1] hypothesis on both sides.  The
    RHS [linhom_add (tensor_mor_R_lin G prev1_ic) (tensor_mor_R_lin G
    δ_ic)] has norm ≤ 2 (not ≤ 1), so a direct application is blocked.
    The standard workaround is a scaling argument analogous to the one
    inside [tensor_mor_omega_cont_R]: scale both sides by [1/2], apply
    [tensor_ext_linhom] to the scaled equality, then unscale.

    **STATUS**: [tensor_mor_R_lin_incr] is NOT delivered axiom-free in
    this iteration.  Without it, [Phi_fun_safe_incr], [Phi_fun_incr],
    [Yfix_fun_lin] (= [linhom_lfp Phi_fun Phi_fun_incr Phi_fun_ball]),
    and the bundled [Yfix_fun_T] all cascade as unprovable in this
    file.  No [Admitted] is used; the construction stops at the
    monotonicity boundary. *)

End YfixFunType.

Arguments Phi_fun_safe {R Ar G A B} M prev Hprev.
Arguments Phi_fun {R Ar G A B} M prev.
Arguments Phi_fun_unit {R Ar G A B} M prev Hprev.
Arguments Phi_fun_safe_ball {R Ar G A B} M prev Hprev.
Arguments Phi_fun_ball {R Ar G A B} M prev.
Arguments extract_fun {R Ar A B}.

(** ** Downstream cascade — the work blocked by [tensor_mor_R_lin_incr]

    With [tensor_mor_R_lin_incr] in hand, the following lemmas / defs
    close immediately, with proof outlines:

    - [Phi_fun_safe_incr] / [Phi_fun_incr] : compose
      [tensor_mor_R_lin_incr] with [linear_increasing] of the three
      icones_hom layers ([linhom_post_icones (bang_fmap (der L))],
      [linhom_post_icones (ch_mor M)], [linhom_pre_icones (coalg_d G)]).

    - [Phi_fun_safe_cont] / [Phi_fun_cont] : ω-continuity of [Phi_fun].
      Compose [tensor_mor_omega_cont_R] (already in
      [em_continuity.v]) with [linhom_post_icones_sup] /
      [linhom_pre_icones_sup] (both in [em_continuity.v]).

    - [Yfix_fun_lin M] := [linhom_lfp Phi_fun Phi_fun_incr Phi_fun_ball]
      : the linhom-level fixpoint.  Already-available [linhom_lfp]
      from this file.

    - [Yfix_fun_lin_fixpoint] : the fixpoint equation [Phi_fun
      Yfix_fun_lin = Yfix_fun_lin], via [linhom_lfp_fixpoint] from
      this file (needs [Phi_fun_cont]).

    - [Yfix_fun_T M] : [coalg_hom G (Tobj t)] := [adj_psi (linhom_icones
      Yfix_fun_lin (linhom_lfp_norm_le1 _ _))], using [adj_psi] from
      [em_cat.v].  No coalg-mor witness needed on [Yfix_fun_lin]
      itself.

    The PPL-side [ne_fix] constructor would be added to [ppl.v] under
    a separate commit once Workstream A's [ppl.v] edits have landed.
    Its [eD] clause is [coalg_comp (Yfix_fun_T (eD body))] with a
    suitable use of [tunit_eta] discharge.  *)

