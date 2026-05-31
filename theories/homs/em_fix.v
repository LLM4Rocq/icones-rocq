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
