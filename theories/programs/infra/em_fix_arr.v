(**md**************************************************************************)
(** * [em_fix_arr] — Bang-level CBV-Y for [ex_geom] (the recipe operator)

    *** BEYOND THE PAPER — Bang-level Kleene iteration seeded at [prom 0]

    This file implements THE expert's CBV-Y recipe for [ex_geom]:

      for [F : EM(!A, !A)] a coalg morphism, [fix(nl(F))] is
      [sup_n F^n(nl(0))] in [Bang Ar L_geom],

    via the concrete operator [Phi_arr := Step_geom one1 : Bang L → Bang L].

    The existing [Yfix_fun_T] in [em_fix.v] iterates a LINEAR linhom
    map starting at the LINHOM-LEVEL [precone_zero] — provably wrong
    for [ex_geom] (collapses to mass 0 universally; cf.
    [ex_geom_step.F_n_mass_zero]).  The recipe sidesteps the collapse
    by iterating at the [Bang Ar L_geom] level starting from
    [prom (precone_zero : L_geom)] — a DISTINCT element of
    [Bang Ar L_geom] (the [nl_B]-PROMOTED zero, NOT the cone-zero).

    *** What this file delivers, AXIOM-FREE (modulo the three [boolp]
        axioms).

    Stage 1.  [Phi_arr], the Bang-level operator [Bang Ar L_geom →
              Bang Ar L_geom] given by [Phi_arr v := Step_geom one1 v].

    - [Phi_arr_ball] : ‖v‖ ≤ 1 → ‖Phi_arr v‖ ≤ 1.  Composition of
      three norm-≤-1 [cones_hom]s applied to the unit-ball pure
      tensor [one1 ⊗p v] (whose norm is ≤ 1·1 = 1 by
      [tensor_norm_le] + [cone_norm_one1]).

    - [Phi_arr_incr] : monotonicity of [Phi_arr] on the unit ball.
      Each component of [Step_geom one1 _] is linear in [v] hence
      increasing (by [linear_increasing] applied to [linhom_pre_fun]
      of [tau (cone_one_car Ar) (Bang Ar L_geom) one1], then by
      [cones_hom_linear] / [linear_increasing] on [Lfun (ch_mor
      M_body)] and [Lfun (bang_fmap (der L_geom))]).

    - [Phi_arr_cont] : ω-continuity of [Phi_arr] on the unit ball.
      Composition of three ω-continuous maps:
      [tau (cone_one_car Ar) (Bang Ar L_geom) one1] (linhom, hence
      its [linhom_pre_fun] is ω-continuous by [linhom_pre_continuous]),
      [Lfun (ch_mor M_body_arr)] and [Lfun (bang_fmap (der L_geom))]
      (both [cones_hom]s, hence ω-continuous by [cones_hom_continuous]).

    Stage 2.  The Kleene chain [kleene_arr n := iter n Phi_arr (prom 0_L)].
              [kleene_arr 0 = prom (precone_zero : L_geom)]; each
              iterate is in the unit ball by induction on [n] and
              [Phi_arr_ball] + [prom_ball].

    - [kleene_arr_ball n] : ‖kleene_arr n‖ ≤ 1 for every [n].

    - [kleene_arr_chain n] : [kleene_arr n ≤p kleene_arr n.+1] — by
      monotonicity of [Phi_arr] and the BASE CASE
      [prom 0_L ≤p Phi_arr (prom 0_L)].
      The base case is [prom_step_geom_seed_order] below: since
      [Phi_arr (prom 0_L)] is some [v_1 : Bang Ar L_geom] with
      [‖v_1‖ ≤ 1] AND [prom 0_L ≤p v_1] (because both are points in
      the unit ball of [Bang Ar L_geom] with [prom 0_L] PROVABLY
      below in the cone order — we obtain this from [totmono_increasing]
      on [nl_B]'s [is_meas_stable], using [precone_le0 : 0 ≤p
      (precone_zero : L_geom) + v] for [v : L_geom] with norm ≤ 1
      and the [v] being the [v_1]-inverse extracted via the iteration
      structure — see the proof below).

    Stage 3.  [Yfix_arr := cone_sup_ball kleene_arr ...] — the
              supremum of the Kleene chain in [Bang Ar L_geom].

    - [Yfix_arr_norm_le1] : ‖Yfix_arr‖ ≤ 1.
    - [Yfix_arr_fixpoint] : [Phi_arr Yfix_arr = Yfix_arr] (Kleene
      argument, via [Phi_arr_cont]).
    - [kleene_arr_le_Yfix n] : every iterate is below the sup.

    Stage 4.  The headline mass identity (deferred; cf. honest scope).

    *** Honest scope and limitations.

    Stages 1, 2, 3 are delivered AXIOM-FREE.  Stage 4 (the
    mass-recurrence [mass(F_{n+1}) = 1/2 + (1/2)·mass(F_n)] + the
    geometric-series convergence + the final [ex_geom_arr_mass_one])
    requires substantial additional infrastructure — [add_lift_mass]
    composed at every iterate, plus [fmeas_sup_cvg] coupled with
    [cvg_geometric] — and is deferred to a follow-up.  See the bottom
    of the file for the explicit headline statement we aim at.

    Author: Guillaume Baudart <guillaume.baudart@inria.fr>. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals signed constructive_ereal.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import measure dirac_measure.
From mathcomp.analysis Require Import sequences ereal normedtype topology.

From Stdlib Require Import Strings.String.

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
Require Import Icones.icones.examples_icone.
Require Import Icones.stable.totmono.
Require Import Icones.stable.scones_cat.
Require Import Icones.homs.icones_iso.
Require Import Icones.homs.linhom.
Require Import Icones.homs.bilin.
Require Import Icones.homs.linhom_functor.
Require Import Icones.homs.tensor.
Require Import Icones.homs.tensor_iso.
Require Import Icones.homs.smcc.
Require Import Icones.homs.exp_adjunction.
Require Import Icones.homs.bang.
Require Import Icones.homs.seely_defs.
Require Import Icones.homs.seely.
Require Import Icones.homs.coalgebra.
Require Import Icones.homs.em_cat.
Require Import Icones.homs.em_cartesian.
Require Import Icones.homs.em_seely_comonoid.
Require Import Icones.programs.infra.cbv_adjunction.
Require Import Icones.programs.infra.bool_cone.
Require Import Icones.programs.infra.bool_case_hom.
Require Import Icones.programs.infra.case_em_red.
Require Import Icones.programs.infra.curry_kbind.
Require Import Icones.programs.infra.em_continuity.
Require Import Icones.programs.infra.em_fix.
Require Import Icones.programs.infra.ex_geom_step.
Require Import Icones.programs.cbv.
Require Import Icones.programs.ppl.
Require Import Icones.programs.examples.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** Section setup *)

Section EmFixArr.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

Local Notation eD' :=
  (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas).

Local Notation tR' := (tR R_obj).

(** ** The linhom-carrier [L_geom] and function-coalgebra [funT_geom]
    — mirror of the [ex_geom_step.v] setup *)

Let L_geom : ICone.type Ar :=
  linhom_car Ar (coalg_obj (EM_term : Coalgebra Ar))
               (coalg_obj (Tobj (tyD tR' : Coalgebra Ar))).

Let funT_geom : Coalgebra Ar := bang_cofree L_geom.

(** [M_body_arr] aliases [M_body] from [ex_geom_step.v] with our
    section variables threaded.  Definitionally identical to
    [@M_body R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas]. *)
Local Notation M_body_arr :=
  (@M_body R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas).

(** The local [Step_geom] (delegate to ex_geom_step's section-closed
    definition, with the section parameters threaded).

    Note: [Step_geom] is exported with [Arguments Step_geom {R Ar
    R_obj} R_carrier_eq R_carrier_meas R_to_carrier_meas γ v]; we
    bake in the three explicit hypotheses to obtain a two-argument
    function [γ ↦ v ↦ ...]. *)
Local Notation Step_geom' :=
  (Step_geom R_carrier_eq R_carrier_meas R_to_carrier_meas).

(** ** Stage 1 — [Phi_arr]: the Bang-level fixpoint operator

    [Phi_arr v := Step_geom one1 v : Bang Ar L_geom].  The operator
    is iteration at the BANG level (i.e., on values [v : Bang Ar
    L_geom]), seeded at [prom (precone_zero : L_geom)]. *)

Definition Phi_arr (v : coalg_obj funT_geom) : coalg_obj funT_geom :=
  Step_geom' one1 v.

(** ** Stage 1a — Ball preservation: ‖v‖ ≤ 1 ⇒ ‖Phi_arr v‖ ≤ 1

    Composition of three norm-≤-1 [cones_hom]s applied to the
    unit-ball pure tensor [one1 ⊗p v]:
    - [ptensor one1 v] has norm ≤ 1·1 = 1 by [tensor_norm_le] +
      [cone_norm_one1].
    - [Lfun (ch_mor M_body_arr)] is a [cones_hom], norm-decreasing.
    - [Lfun (bang_fmap (der L_geom))] is a [cones_hom], norm-decreasing. *)

Lemma Phi_arr_ball (v : coalg_obj funT_geom) :
  cone_norm v <= 1 -> cone_norm (Phi_arr v) <= 1.
Proof.
move=> Hv.
rewrite /Phi_arr /Step_geom.
(* [ptensor one1 v] has norm ≤ 1 *)
have Hpt : cone_norm (ptensor (one1 : cone_one_car Ar) v) <= 1.
  apply: le_trans (tensor_norm_le _ _) _.
  rewrite -[1]mulr1; apply: ler_pM.
  - exact: cone_norm_ge0.
  - exact: cone_norm_ge0.
  - by rewrite cone_norm_one1.
  - exact: Hv.
(* [Lfun (ch_mor M_body_arr) _] is norm-decreasing *)
have HchM : cone_norm (Lfun (ch_mor M_body_arr) (ptensor one1 v)) <= 1.
  apply: le_trans (cones_hom_norm_le1 _ _) Hpt.
(* [Lfun (bang_fmap (der L_geom)) _] is norm-decreasing *)
apply: le_trans (cones_hom_norm_le1 _ _) HchM.
Qed.

(** ** Stage 1b — Monotonicity of [Phi_arr]

    Each of the three components of [Step_geom one1 v] is LINEAR in
    [v], hence increasing.

    - [tau (cone_one_car Ar) (Bang Ar L_geom) one1] is a linhom in
      its argument [v]; [ptensor one1 v = linhom_fun (tau _ _ one1)
      v] (definitional) and [linhom_pre_fun (linhom_pre_of (tau _ _
      one1))] is linear.
    - [Lfun (ch_mor M_body_arr)] is linear ([cones_hom_linear]).
    - [Lfun (bang_fmap (der L_geom))] is linear ([cones_hom_linear]).

    Each is hence increasing; composition is increasing. *)

Lemma Phi_arr_incr (v1 v2 : coalg_obj funT_geom) :
  precone_le v1 v2 -> precone_le (Phi_arr v1) (Phi_arr v2).
Proof.
move=> Hle.
rewrite /Phi_arr /Step_geom.
(* Step 1: [ptensor one1 _] is linear (and increasing) in its right argument *)
have Hpt_le : precone_le (ptensor (one1 : cone_one_car Ar) v1)
                         (ptensor (one1 : cone_one_car Ar) v2).
  have Htau_lin : is_linear
    (linhom_pre_fun (linhom_pre_of
      (tau (cone_one_car Ar) (coalg_obj funT_geom) one1))).
    exact: linhom_pre_linear.
  exact: (linear_increasing Htau_lin Hle).
(* Step 2: [Lfun (ch_mor M_body_arr)] is linear (and increasing) *)
have HchM_lin : is_linear (Lfun (ch_mor M_body_arr)).
  exact: cones_hom_linear.
have HchM_le : precone_le (Lfun (ch_mor M_body_arr)
                                (ptensor (one1 : cone_one_car Ar) v1))
                          (Lfun (ch_mor M_body_arr)
                                (ptensor (one1 : cone_one_car Ar) v2)).
  exact: (linear_increasing HchM_lin Hpt_le).
(* Step 3: [Lfun (bang_fmap (der L_geom))] is linear (and increasing) *)
have Hbang_lin : is_linear (Lfun (bang_fmap (der L_geom))).
  exact: cones_hom_linear.
exact: (linear_increasing Hbang_lin HchM_le).
Qed.

(** ** Stage 1c — ω-continuity of [Phi_arr]

    Composition of three ω-continuous maps on the unit ball.

    - [v ↦ ptensor one1 v] is [linhom_pre_fun (linhom_pre_of (tau
      (cone_one_car Ar) (Bang L_geom) one1))], which is
      ω-continuous by [linhom_pre_continuous].
    - [Lfun (ch_mor M_body_arr)] is ω-continuous ([cones_hom_continuous]).
    - [Lfun (bang_fmap (der L_geom))] is ω-continuous
      ([cones_hom_continuous]).

    Norm-≤-1 facts for the intermediate chains all follow from the
    norm-decreasing properties of the components. *)

Lemma Phi_arr_cont (u : nat -> coalg_obj funT_geom)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, cone_norm (u n) <= 1)
    (Pch : forall n, precone_le (Phi_arr (u n)) (Phi_arr (u n.+1)))
    (Pub1 : forall n, cone_norm (Phi_arr (u n)) <= 1) :
  Phi_arr (cone_sup_ball u uch ub1) =
  cone_sup_ball (Phi_arr \o u) Pch Pub1.
Proof.
rewrite /Phi_arr /Step_geom.
(* Step 1: [ptensor one1 v = linhom_fun (tau _ _ one1) v] (definitional).
   The linhom [tau (cone_one_car Ar) (coalg_obj funT_geom) one1] has
   ω-continuous [linhom_pre_fun] by [linhom_pre_continuous]. *)
pose tau1 : linhom_car Ar (coalg_obj funT_geom)
                          (tensor Ar (cone_one_car Ar) (coalg_obj funT_geom))
  := tau (cone_one_car Ar) (coalg_obj funT_geom) (one1 : cone_one_car Ar).
have Hpt_eq : forall v : coalg_obj funT_geom,
    ptensor (one1 : cone_one_car Ar) v = linhom_fun tau1 v.
  by move=> v; rewrite /tau1 -ptensorE.
(* Phi_arr v at the sup, rewritten via Hpt_eq *)
rewrite Hpt_eq.
(* Step 2: use ω-continuity of [linhom_fun tau1]
   (= linhom_pre_fun (linhom_pre_of tau1)) *)
pose f1 := linhom_fun tau1.
have Hf1_lin : is_linear f1.
  rewrite /f1 /linhom_fun.
  exact: (linhom_pre_linear (linhom_pre_of tau1)).
have Hf1_cont : is_omega_continuous f1.
  rewrite /f1 /linhom_fun.
  exact: (linhom_pre_continuous (linhom_pre_of tau1)).
(* Norm bound: ‖linhom_fun tau y‖ ≤ cone_norm tau · cone_norm y ≤ 1 · cone_norm y.
   tau is an icones_hom with norm ≤ 1, so [tau1 = tau B C one1] has
   norm ≤ ‖one1‖ ≤ 1.  We use [linhom_norm_apply_le] + [tau_norm_le1]. *)
have Htau1_norm : cone_norm tau1 <= 1.
  rewrite /tau1; apply: le_trans (cones_hom_norm_le1 _ _) _.
  by rewrite cone_norm_one1.
have Hf1_norm : forall x : coalg_obj funT_geom, cone_norm (f1 x) <= cone_norm x.
  move=> x.
  rewrite /f1.
  apply: le_trans (linhom_norm_apply_le Htau1_norm x) _.
  by rewrite mul1r.
have f1_ch : forall n, precone_le (f1 (u n)) (f1 (u n.+1)).
  by move=> n; apply: linear_increasing => //; exact: uch.
have f1_ub : forall n, cone_norm (f1 (u n)) <= 1.
  by move=> n; apply: le_trans (Hf1_norm _) _; exact: ub1.
(* Push through f1 = linhom_fun tau1.
   The goal currently has [linhom_fun tau1 (cone_sup_ball u uch ub1)];
   fold to [f1 ...] first so the rewrite matches. *)
rewrite -[linhom_fun tau1 (cone_sup_ball u uch ub1)]/(f1 (cone_sup_ball u uch ub1)).
rewrite (Hf1_cont u uch ub1 f1_ch f1_ub).
(* Step 3: ω-continuity of [Lfun (ch_mor M_body_arr)] *)
pose f2 := Lfun (ch_mor M_body_arr).
have Hf2_lin : is_linear f2 by exact: cones_hom_linear.
have Hf2_cont : is_omega_continuous f2 by exact: cones_hom_continuous.
have Hf2_norm : forall y, cone_norm (f2 y) <= cone_norm y.
  by move=> y; exact: cones_hom_norm_le1.
have f2f1_ch : forall n, precone_le (f2 (f1 (u n))) (f2 (f1 (u n.+1))).
  by move=> n; apply: linear_increasing => //; exact: f1_ch.
have f2f1_ub : forall n, cone_norm (f2 (f1 (u n))) <= 1.
  by move=> n; apply: le_trans (Hf2_norm _) _; exact: f1_ub.
rewrite -[Lfun (ch_mor M_body_arr) (cone_sup_ball (f1 \o u) f1_ch f1_ub)]
        /(f2 (cone_sup_ball (f1 \o u) f1_ch f1_ub)).
rewrite (Hf2_cont (f1 \o u) f1_ch f1_ub f2f1_ch f2f1_ub).
(* Step 4: ω-continuity of [Lfun (bang_fmap (der L_geom))] *)
pose f3 := Lfun (bang_fmap (der L_geom)).
have Hf3_lin : is_linear f3 by exact: cones_hom_linear.
have Hf3_cont : is_omega_continuous f3 by exact: cones_hom_continuous.
have Hf3_norm : forall z, cone_norm (f3 z) <= cone_norm z.
  by move=> z; exact: cones_hom_norm_le1.
have f3f2f1_ch : forall n, precone_le (f3 (f2 (f1 (u n))))
                                       (f3 (f2 (f1 (u n.+1)))).
  by move=> n; apply: linear_increasing => //; exact: f2f1_ch.
have f3f2f1_ub : forall n, cone_norm (f3 (f2 (f1 (u n)))) <= 1.
  by move=> n; apply: le_trans (Hf3_norm _) _; exact: f2f1_ub.
rewrite -[Lfun (bang_fmap (der L_geom))
            (cone_sup_ball (f2 \o f1 \o u) f2f1_ch f2f1_ub)]
        /(f3 (cone_sup_ball (f2 \o f1 \o u) f2f1_ch f2f1_ub)).
rewrite (Hf3_cont (f2 \o f1 \o u) f2f1_ch f2f1_ub f3f2f1_ch f3f2f1_ub).
(* Now both sides are [cone_sup_ball] over [coalg_obj funT_geom] with
   underlying chain [n ↦ f3 (f2 (f1 (u n)))] = [n ↦ Phi_arr (u n)]
   (modulo the [Hpt_eq] rewrite, which is definitional after unfolding). *)
apply: precone_le_anti.
- apply: cone_sup_ball_lub => n.
  exact: cone_sup_ball_ub.
- apply: cone_sup_ball_lub => n.
  exact: cone_sup_ball_ub.
Qed.

(** ** Stage 2 — The Kleene chain at the Bang level

    [kleene_arr n := iter n Phi_arr (prom (precone_zero : L_geom))].
    Each iterate is in the unit ball (induction + [Phi_arr_ball] +
    [prom_ball] on the base). *)

Definition kleene_arr (n : nat) : coalg_obj funT_geom :=
  iter n Phi_arr (prom (precone_zero : L_geom)).

Lemma kleene_arr_0 :
  kleene_arr 0 = prom (precone_zero : L_geom).
Proof. by []. Qed.

Lemma kleene_arr_S n :
  kleene_arr n.+1 = Phi_arr (kleene_arr n).
Proof. by rewrite /kleene_arr iterS. Qed.

Lemma cone_norm_prom_zero_le1 :
  cone_norm (prom (precone_zero : L_geom)) <= 1.
Proof. by apply: prom_ball; rewrite cone_norm0 ler01. Qed.

Lemma kleene_arr_ball n :
  cone_norm (kleene_arr n) <= 1.
Proof.
induction n.
- by rewrite kleene_arr_0; exact: cone_norm_prom_zero_le1.
- rewrite kleene_arr_S; exact: Phi_arr_ball.
Qed.

(** ** Stage 2a — Seed-order: [prom 0_L ≤p Phi_arr (prom 0_L)]

    Both sides are points in the unit ball of [Bang Ar L_geom].
    We use [precone_le0]: zero is always ≤p any element.  But
    [prom 0_L : Bang Ar L_geom] is NOT the cone-zero of [Bang Ar
    L_geom] (it's the [nl_B]-PROMOTED zero, a distinct element).

    The seed-order is NOT immediate from [precone_le0].  We rely on
    the structure of the chain at iterate 1:
    [Phi_arr (prom 0_L) = Step_geom one1 (prom 0_L)].  By
    [Step_geom_one_prom_zero_via_convex_E], this equals
    [prom K] where [K = Lfun (tensor_curry (ch_mor convex))
    (one1 ⊗p prom 0_L_geom)].

    So the seed-order reduces to [prom 0_L ≤p prom K] (in [Bang Ar
    L_geom]).  By [nl_B]'s [is_meas_stable], specifically
    [totmono_increasing] from the [is_totmono] component, [prom] is
    monotone on the unit ball.  Combined with [0_L ≤p K]
    ([precone_le0]) and the norm ≤ 1 hypothesis on [K]
    ([cone_norm_K_le1] from [ex_geom_step.v]), we get
    [prom 0_L ≤p prom K].

    Note: [prom = sc_fun (nl B)] and [sc_meas_stable (nl B)] is
    structurally a record giving us [is_meas_stable], whose first
    component [is_stable] gives [is_totmono].  Then
    [totmono_increasing] with [x = 0] and [v = K] (so [x + v = K])
    + the [‖K‖ ≤ 1] hypothesis gives [sc_fun (nl B) 0 ≤p sc_fun
    (nl B) K], which is [prom 0_L ≤p prom K] (after [precone_add0]
    to convert [x + v] to [v]). *)

(** Monotonicity of [prom] on the unit ball: if [‖y‖ ≤ 1] then
    [prom 0_B ≤p prom y].  By [is_totmono (sc_fun (nl B))] +
    [totmono_increasing]. *)
Lemma prom_le_unit_ball (B : ICone.type Ar) (y : B) :
  cone_norm y <= 1 -> precone_le (prom (precone_zero : B)) (prom y).
Proof.
move=> Hy.
have [[Htm _ _] _] := sc_meas_stable (nl B).
have Hxv : cone_norm (precone_add (precone_zero : B) y) <= 1.
  by rewrite precone_add0.
have Hle := @totmono_increasing R B (Bang Ar B) (sc_fun (nl B))
              Htm (precone_zero : B) y Hxv.
rewrite precone_add0 in Hle.
exact: Hle.
Qed.

(** *** The seed-order — base case for the Kleene chain.

    [prom (precone_zero : L_geom) ≤p Phi_arr (prom (precone_zero :
    L_geom))]. *)
Lemma prom_step_geom_seed_order :
  precone_le (prom (precone_zero : L_geom))
             (Phi_arr (prom (precone_zero : L_geom))).
Proof.
(* Rewrite Phi_arr via Step_geom_one_prom_zero_via_convex_E *)
rewrite /Phi_arr.
rewrite (@Step_geom_one_prom_zero_via_convex_E
           R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas).
(* Goal: prom 0 ≤p prom (Lfun (tensor_curry (ch_mor convex))
                              (one1 ⊗p prom 0)). *)
apply: prom_le_unit_ball.
(* Goal: cone_norm (Lfun (tensor_curry (ch_mor convex)) (one1 ⊗p prom 0)) <= 1 *)
exact: (@cone_norm_K_le1 R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas).
Qed.

(** *** The chain is increasing — induction on [n].

    Base [n=0]: seed-order [prom_step_geom_seed_order].
    Step: by [Phi_arr_incr] + IH. *)
Lemma kleene_arr_chain n :
  precone_le (kleene_arr n) (kleene_arr n.+1).
Proof.
induction n.
- rewrite kleene_arr_0 kleene_arr_S kleene_arr_0.
  exact: prom_step_geom_seed_order.
- rewrite ![kleene_arr _.+1]kleene_arr_S.
  exact: (Phi_arr_incr IHn).
Qed.

(** ** Stage 3 — [Yfix_arr]: the supremum of the Kleene chain *)

Definition Yfix_arr : coalg_obj funT_geom :=
  cone_sup_ball kleene_arr kleene_arr_chain kleene_arr_ball.

Lemma Yfix_arr_norm_le1 : cone_norm Yfix_arr <= 1.
Proof. exact: cone_sup_ball_norm. Qed.

Lemma kleene_arr_le_Yfix n : precone_le (kleene_arr n) Yfix_arr.
Proof. exact: cone_sup_ball_ub. Qed.

(** ** Stage 3a — Fixpoint identity [Phi_arr Yfix_arr = Yfix_arr]

    By [Phi_arr_cont]: pushing [Phi_arr] through the sup, then
    using [precone_le_anti] on the resulting sup of [Phi_arr ∘
    kleene_arr = kleene_arr ∘ S] (the shifted chain) vs.
    [kleene_arr]. *)

Lemma Yfix_arr_fixpoint : Phi_arr Yfix_arr = Yfix_arr.
Proof.
rewrite /Yfix_arr.
have Pch : forall n, precone_le (Phi_arr (kleene_arr n))
                                (Phi_arr (kleene_arr n.+1)).
  by move=> n; apply: Phi_arr_incr; exact: kleene_arr_chain.
have Pub1 : forall n, cone_norm (Phi_arr (kleene_arr n)) <= 1.
  by move=> n; apply: Phi_arr_ball; exact: kleene_arr_ball.
rewrite -> (@Phi_arr_cont kleene_arr kleene_arr_chain kleene_arr_ball Pch Pub1).
apply: precone_le_anti.
- apply: cone_sup_ball_lub => n.
  rewrite -[(Phi_arr \o kleene_arr) n]/(Phi_arr (kleene_arr n)).
  rewrite -kleene_arr_S.
  exact: (cone_sup_ball_ub kleene_arr kleene_arr_chain kleene_arr_ball n.+1).
- apply: cone_sup_ball_lub => n.
  apply: (precone_le_trans (y := (Phi_arr \o kleene_arr) n)).
    rewrite -[(Phi_arr \o kleene_arr) n]/(Phi_arr (kleene_arr n)).
    rewrite -kleene_arr_S.
    exact: kleene_arr_chain.
  exact: cone_sup_ball_ub.
Qed.

(** ** Stage 4 — FMeas extraction + base cases (n = 0, n = 1)

    We deliver Stage 4 PARTIALLY: the FMeas-mass extraction operator
    [F_arr n] applied to the Kleene chain, plus the n = 0 mass-zero
    base case and the explicit n = 1 mass-1/2 identity (the latter
    inherited from §1's [first_iterate_FMeas_mass_half]).

    The full geometric-series recurrence [mass(F_arr (n+1)) = 1/2 +
    (1/2)·mass(F_arr n)] requires generalizing the per-branch
    evaluation cascade from the SPECIFIC seed [prom (precone_zero :
    L_geom)] to a general iterate [kleene_arr n].  This generalization
    is non-trivial — in particular, the ELSE-branch [g := kleene_arr
    n] no longer kills the recursive call via [der_prom], but instead
    evaluates to the n-th iterate's mass.  Closing this requires
    re-running the §1 evaluation cascade with a parametric [v : Bang
    Ar L_geom] hypothesis; this is several hundred lines of fresh
    infrastructure left for a follow-up. *)

(** ** Stage 4a — The FMeas extraction at the n-th iterate

    [F_arr n] is the FMeas-element extracted from [kleene_arr n] by
    applying [der L_geom], evaluating at [one1], then [der (FMeas
    R_obj)] — the same pattern as §1's
    [first_iterate_FMeas_mass_half]. *)
Definition F_arr (n : nat) : FMeas R_obj :=
  Lfun (der (FMeas R_obj))
       (linhom_fun
          (Lfun (der L_geom) (kleene_arr n))
          (one1 : cone_one_car Ar)).

(** Base case [n = 0]: [kleene_arr 0 = prom 0_L_geom].  After [der
    L_geom], we get [precone_zero : L_geom] (via [der_prom] + linearity).
    After [linhom_fun _ one1], [precone_zero : Bang Ar (FMeas R_obj)].
    After [der (FMeas R_obj)], [precone_zero : FMeas R_obj].  Hence
    [F_arr 0 = precone_zero], whose mass is [0]. *)
Lemma F_arr_0_E : F_arr 0 = precone_zero.
Proof.
rewrite /F_arr kleene_arr_0.
(* Lfun (der L_geom) (prom 0_L_geom) = precone_zero : L_geom *)
have H0_le1 : (cone_norm (precone_zero : L_geom) <= 1)%R
  by rewrite cone_norm0 ler01.
rewrite (@der_prom R Ar L_geom (precone_zero : L_geom) H0_le1).
(* linhom_fun (precone_zero : L_geom) one1 = precone_zero : Bang FMeas *)
have Hlinhom0 :
  linhom_fun (precone_zero : L_geom) (one1 : cone_one_car Ar)
  = (precone_zero : Bang Ar (FMeas R_obj)) by [].
rewrite Hlinhom0.
(* Lfun (der (FMeas R_obj)) precone_zero = precone_zero : FMeas R_obj *)
have [Hder_F0 _ _] :=
  cones_hom_linear (mcones_hom_cones (icones_hom_mcones (der (FMeas R_obj)))).
exact: Hder_F0.
Qed.

Lemma F_arr_0_mass_zero :
  fmeas_mu (F_arr 0) [set: ar_carrier Ar R_obj] = 0%E.
Proof. by rewrite F_arr_0_E fmeas_zeroE. Qed.

(** ** Stage 4 structural — [Phi_arr] of a [prom] is a [prom]

    A key structural fact bridging the [Bang Ar L_geom] chain to the
    underlying [L_geom] linhom chain.

    For [u : L_geom] with [cone_norm u ≤ 1], [Phi_arr (prom u)] is of
    the form [prom v] for some [v : L_geom].  Combined with
    [kleene_arr 0 = prom 0_L_geom], this proves by induction that
    EVERY iterate [kleene_arr n] is a [prom] of some [L_geom] element.

    Proof: by [Step_geom_E] + [lam_coalg_at_one_prom] (which gives the
    inner [prom Y] form), and we just take [v := Y].

    Note: the implicit body_inner inlined by [Step_geom_E] is the
    body of [ex_geom_body], specifically [if Bernoulli(½) then [|0|]
    else [|1|] + g()].  We do NOT name the witness explicitly — the
    [eexists] tactic infers it from the post-rewrite goal. *)
Lemma Phi_arr_of_prom (u : L_geom) (Hu : cone_norm u <= 1) :
  exists v : L_geom, Phi_arr (prom u) = prom v.
Proof.
rewrite /Phi_arr.
rewrite (@Step_geom_E R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas
                       one1 (prom u)).
rewrite (@lam_coalg_at_one_prom R Ar R_obj _ u Hu).
by eexists.
Qed.

(** *** Norm-tracking version of [Phi_arr_of_prom]

    Same as [Phi_arr_of_prom] but additionally returns the norm bound
    [‖v‖ ≤ 1] on the witness.  The bound comes from the explicit
    [tensor_curry] form: [v] is the linhom-value at the unit-ball pure
    tensor [one1 ⊗p prom u], hence its [cone_norm] is bounded by
    [‖tensor_curry _‖ · ‖one1‖ · ‖prom u‖ ≤ 1 · 1 · 1 = 1] via
    [cones_hom_norm_le1] + [tensor_norm_le] + [cone_norm_one1] +
    [prom_ball]. *)
Lemma Phi_arr_of_prom_norm (u : L_geom) (Hu : cone_norm u <= 1) :
  exists v : L_geom, Phi_arr (prom u) = prom v /\ cone_norm v <= 1.
Proof.
rewrite /Phi_arr.
rewrite (@Step_geom_E R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas
                       one1 (prom u)).
rewrite (@lam_coalg_at_one_prom R Ar R_obj _ u Hu).
set inner_witness := Lfun _ (ptensor _ _).
have Hwitness_norm : cone_norm inner_witness <= 1.
  rewrite /inner_witness.
  apply: le_trans (cones_hom_norm_le1 _ _) _.
  apply: le_trans (tensor_norm_le _ _) _.
  rewrite -[1]mulr1; apply: ler_pM.
  - exact: cone_norm_ge0.
  - exact: cone_norm_ge0.
  - by rewrite cone_norm_one1.
  - exact: prom_ball Hu.
by exists inner_witness.
Qed.

(** *** Consequence: every Kleene iterate is a [prom] (with norm bound)

    By induction on [n], using [Phi_arr_of_prom_norm] at each step.
    Base case [n = 0]: [kleene_arr 0 = prom (precone_zero : L_geom)]
    with [‖0‖ = 0 ≤ 1].  Step case: by IH, [kleene_arr n = prom u_n]
    with [‖u_n‖ ≤ 1]; apply [Phi_arr_of_prom_norm] with [Hu_n] to get
    [Phi_arr (prom u_n) = prom v_{n+1}] with [‖v_{n+1}‖ ≤ 1]. *)
Lemma kleene_arr_is_prom (n : nat) :
  exists u : L_geom, kleene_arr n = prom u /\ cone_norm u <= 1.
Proof.
induction n.
- exists (precone_zero : L_geom); split.
  + by rewrite kleene_arr_0.
  + by rewrite cone_norm0 ler01.
- destruct IHn as [u [Hu_eq Hu_norm]].
  destruct (Phi_arr_of_prom_norm Hu_norm) as [v [Hv_eq Hv_norm]].
  exists v; split.
  + by rewrite kleene_arr_S Hu_eq.
  + exact: Hv_norm.
Qed.

(** Sanity: the [n = 0] case explicitly. *)
Lemma kleene_arr_0_is_prom :
  exists u : L_geom, kleene_arr 0 = prom u.
Proof. by exists (precone_zero : L_geom); rewrite kleene_arr_0. Qed.

(** Sanity: the [n = 1] case via [Phi_arr_of_prom] applied to the seed
    [precone_zero : L_geom] (norm ≤ 1). *)
Lemma kleene_arr_1_is_prom :
  exists u : L_geom, kleene_arr 1 = prom u.
Proof.
have H0_le1 : (cone_norm (precone_zero : L_geom) <= 1)%R
  by rewrite cone_norm0 ler01.
destruct (Phi_arr_of_prom H0_le1) as [v Hv].
exists v.
by rewrite kleene_arr_S kleene_arr_0.
Qed.

(** Stage 4b — [F_arr 1] mass = 1/2.

    Compose [kleene_arr_S 0]: [kleene_arr 1 = Phi_arr (kleene_arr 0)
    = Phi_arr (prom (precone_zero : L_geom)) = Step_geom one1 (prom
    precone_zero)].  This is exactly the form §1 closed at
    [first_iterate_FMeas_mass_half]. *)
Lemma F_arr_1_mass_half :
  fmeas_mu (F_arr 1) [set: ar_carrier Ar R_obj] = (1/2)%R%:E.
Proof.
rewrite /F_arr kleene_arr_S kleene_arr_0.
rewrite -[Phi_arr _]/(Step_geom R_carrier_eq R_carrier_meas R_to_carrier_meas
                                (one1 : cone_one_car Ar)
                                (prom (precone_zero : L_geom))).
exact: (@first_iterate_FMeas_mass_half
          R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas).
Qed.

(** ** Stage 4c — Headline target (deferred)

    The full mass-1 closure for [ex_geom] via [Yfix_arr]:
    [[
      ex_geom_arr_mass_one :
        fmeas_mu (Lfun (der (FMeas R_obj))
                       (linhom_fun (Lfun (der L_geom) Yfix_arr)
                                   (one1 : cone_one_car Ar)))
                 [set: ar_carrier Ar R_obj]
        = 1%:E.
    ]]

    Proof strategy:
    1. Per-iterate mass identity: [fmeas_mu (F_arr n) setT = 1 -
       (1/2)^n].  Base case [n = 0]: mass 0 ([F_arr_0_mass_zero]).
       Step case: mass-recurrence
       [[
         fmeas_mu (F_arr n.+1) setT = 1/2 + (1/2) * fmeas_mu (F_arr n) setT.
       ]]
       Requires re-running the §1 cascade with [g := kleene_arr n]
       instead of [g := prom 0_L_geom].  The THEN branch is unchanged
       (returns [δ_0] of mass 1).  The ELSE branch [g()] now evaluates
       to [Lfun (der L_geom) (kleene_arr n)] applied at [one1], whose
       [linhom_fun _ one1] reads as a [Bang Ar (FMeas R_obj)] element
       (def. F_arr's intermediate), and [Lfun (der (FMeas R_obj))]
       extracts a [FMeas R_obj].  The bilinear [add_lift] of [1] + this
       contribution is, via [add_lift_mass], [mass(F_arr n) = 1 -
       (1/2)^n], for a sum of [(1/2) + (1/2)·(1 - (1/2)^n) = 1 -
       (1/2)^{n+1}].
    2. Sup of [1 - (1/2)^n] = 1 via [cvg_geometric] (in
       [mathcomp.analysis.sequences]).
    3. [fmeas_sup_cvg] (from [theories/mcones/fmeas.v]) to commute
       mass with sup.

    Substantial infrastructure required at each step; deferred to a
    follow-up. *)

End EmFixArr.

Arguments Phi_arr
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} v.
Arguments Phi_arr_ball
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} v.
Arguments Phi_arr_incr
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} v1 v2.
Arguments Phi_arr_cont
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} u uch ub1.
Arguments kleene_arr
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} n.
Arguments kleene_arr_0
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}.
Arguments kleene_arr_S
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} n.
Arguments cone_norm_prom_zero_le1
  {R Ar R_obj}.
Arguments kleene_arr_ball
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} n.
Arguments prom_le_unit_ball
  {R Ar B} y.
Arguments prom_step_geom_seed_order
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}.
Arguments kleene_arr_chain
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} n.
Arguments Yfix_arr
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}.
Arguments Yfix_arr_norm_le1
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}.
Arguments kleene_arr_le_Yfix
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} n.
Arguments Yfix_arr_fixpoint
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}.
Arguments F_arr
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} n.
Arguments F_arr_0_E
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}.
Arguments F_arr_0_mass_zero
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}.
Arguments F_arr_1_mass_half
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}.
Arguments Phi_arr_of_prom
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} u Hu.
Arguments Phi_arr_of_prom_norm
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} u Hu.
Arguments kleene_arr_is_prom
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} n.
Arguments kleene_arr_0_is_prom
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}.
Arguments kleene_arr_1_is_prom
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}.
(** ** §5 — MASS RECURRENCE FOR ex_geom (EXPERT'S PROM-PEELING)

    BEYOND THE PAPER — Phase 4 mass-1 closure.

    The headline theorem [ex_geom_arr_mass_one]: the FMeas mass of the
    Yfix-extracted geometric distribution is exactly 1.

    *** Expert's recipe.

    P-A Melliès (consult. 2026-06-04): "All [!XYZ] values manipulated
    ARE promotions (i.e., of the form [nl(...)]) and formulas simplify
    on these — the same calculations as in CBN, just behind a
    promotion."

    Building on [kleene_arr_is_prom] (every Kleene iterate is a prom
    of some [u_n : L_geom]) and [Phi_arr_of_prom_norm] (Phi_arr
    preserves the prom form), we get an L_geom-level recurrence and
    via [tensor_curryEp] an FMeas-level recurrence
    [F_arr n.+1 = (1/2)·δ_0 + (1/2)·add_lift(δ_1, F_arr n)].

    [add_lift_mass] gives the mass recurrence
    [mass(F_arr n.+1) = 1/2 + (1/2)·mass(F_arr n)].

    Closed form: [mass(F_arr n) = 1 - (1/2)^n].  Convergence to 1 via
    [cvg_expr] ([|1/2| < 1]). *)

Section ExGeomArrMassOne.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

Local Notation eD' :=
  (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas).

Local Notation tR' := (tR R_obj).

Let L_geom : ICone.type Ar :=
  linhom_car Ar (coalg_obj (EM_term : Coalgebra Ar))
               (coalg_obj (Tobj (tyD tR' : Coalgebra Ar))).

Let funT_geom : Coalgebra Ar := bang_cofree L_geom.

Local Notation M_body_arr :=
  (@M_body R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas).

Local Notation G_geom :=
  (EM_prod (EM_prod (EM_term : Coalgebra Ar) funT_geom)
           (EM_term : Coalgebra Ar)).

Local Notation Step_geom' :=
  (Step_geom R_carrier_eq R_carrier_meas R_to_carrier_meas).

(** Local notations for the [then_e] / [else_e] expressions.  Identical
    in shape to the [Let]-defs of [ExGeomStep]. *)
Local Notation then_e :=
  (@ne_real R Ar R_obj
     (("_"%string, tunit) :: ("g"%string, tfun tunit tR') :: nil) 0%R).
Local Notation else_e :=
  (ne_add (@ne_real R Ar R_obj
            (("_"%string, tunit) :: ("g"%string, tfun tunit tR') :: nil) 1%R)
          (ne_app (ne_var (nv_tail "_"%string tunit _
                            (nv_head "g"%string (tfun tunit tR') nil)))
                  ne_tt)).

Local Notation kleene_arr' :=
  (@kleene_arr R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas).
Local Notation F_arr' :=
  (@F_arr R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas).
Local Notation Yfix_arr' :=
  (@Yfix_arr R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas).

(** *** §5.1 — Parametric outer point [at_outer_pt_u u]

    Generalizes [at_outer_pt] (=prom 0 form) of §1 to arbitrary
    [u : L_geom] with [‖u‖ ≤ 1]. *)
Definition at_outer_pt_u (u : L_geom) : coalg_obj G_geom :=
  ptensor (ptensor (one1 : cone_one_car Ar) (prom u))
          (one1 : cone_one_car Ar).

Lemma cone_norm_at_outer_pt_u_le1 (u : L_geom) (Hu : cone_norm u <= 1) :
  cone_norm (at_outer_pt_u u) <= 1.
Proof.
rewrite /at_outer_pt_u.
apply: le_trans (tensor_norm_le _ _) _.
rewrite -[1]mulr1; apply: ler_pM.
- exact: cone_norm_ge0.
- exact: cone_norm_ge0.
- apply: le_trans (tensor_norm_le _ _) _.
  rewrite -[1]mulr1; apply: ler_pM.
  + exact: cone_norm_ge0.
  + exact: cone_norm_ge0.
  + by rewrite cone_norm_one1.
  + exact: prom_ball Hu.
- by rewrite cone_norm_one1.
Qed.

Lemma cone_norm_inner_pt_u_le1 (u : L_geom) (Hu : cone_norm u <= 1) :
  cone_norm (ptensor (one1 : cone_one_car Ar) (prom u)) <= 1.
Proof.
apply: le_trans (tensor_norm_le _ _) _.
rewrite -[1]mulr1; apply: ler_pM.
- exact: cone_norm_ge0.
- exact: cone_norm_ge0.
- by rewrite cone_norm_one1.
- exact: prom_ball Hu.
Qed.

(** *** §5.2 — [coalg_str] on the parametric outer pt *)
Lemma coalg_str_G_on_outer_pt_u_E (u : L_geom) (Hu : cone_norm u <= 1) :
  Lfun (coalg_str G_geom) (at_outer_pt_u u) = prom (at_outer_pt_u u).
Proof.
rewrite (EM_prod_str_E (EM_prod (EM_term : Coalgebra Ar) funT_geom)
                       (EM_term : Coalgebra Ar)) /EM_prod_str.
rewrite -[Lfun (icones_comp _ _) _]
        /(Lfun (m_bang (coalg_obj _) (coalg_obj _))
               (Lfun (tensor_mor _ _) _)).
rewrite tensor_morE.
have Hinner :
  Lfun (coalg_str (EM_prod (EM_term : Coalgebra Ar) funT_geom))
       (ptensor (one1 : cone_one_car Ar) (prom u))
  = prom (ptensor (one1 : cone_one_car Ar) (prom u)).
  rewrite (EM_prod_str_E (EM_term : Coalgebra Ar) funT_geom) /EM_prod_str.
  rewrite -[Lfun (icones_comp _ _) _]
          /(Lfun (m_bang (coalg_obj _) (coalg_obj _))
                 (Lfun (tensor_mor _ _) _)).
  rewrite tensor_morE.
  rewrite -[coalg_str EM_term]/(unit_cofree_str (Ar:=Ar)) unit_cofree_str_one1.
  rewrite (bang_cofree_str L_geom) (dig_prom (B:=L_geom) u Hu).
  by rewrite (m_bang_prom (x:=one1) (y:=prom u)
                          (cone_norm_one1_le1 Ar) (prom_ball Hu)).
rewrite Hinner.
rewrite -[coalg_str EM_term]/(unit_cofree_str (Ar:=Ar)) unit_cofree_str_one1.
by rewrite (m_bang_prom (x:=ptensor (one1 : cone_one_car Ar) (prom u))
                        (y:=one1)
                        (cone_norm_inner_pt_u_le1 Hu) (cone_norm_one1_le1 Ar)).
Qed.

(** *** §5.3 — [coalg_e] on the parametric outer pt = [one1] *)
Lemma coalg_e_G_on_outer_pt_u_E (u : L_geom) (Hu : cone_norm u <= 1) :
  Lfun (coalg_e G_geom) (at_outer_pt_u u) = one1.
Proof.
have Hz_le1 : cone_norm (at_outer_pt_u u) <= 1
  by exact: cone_norm_at_outer_pt_u_le1.
have Hcs : Lfun (coalg_str G_geom) (at_outer_pt_u u) = prom (at_outer_pt_u u)
  by exact: coalg_str_G_on_outer_pt_u_E.
transitivity (Lfun (e_bang (coalg_obj G_geom))
                   (Lfun (coalg_str G_geom) (at_outer_pt_u u)));
  first by [].
rewrite Hcs.
exact: (@e_bang_prom R Ar (coalg_obj G_geom) (at_outer_pt_u u) Hz_le1).
Qed.




(** *** §5.4 — Parametric var-lookup, ne_var, app_g_tt cascade

    Generalized versions of [Lfun_var_lookup_g_at_outer_pt_E] etc. to
    arbitrary [u : L_geom] with [‖u‖ ≤ 1]. *)
Lemma Lfun_var_lookup_g_at_outer_pt_u_E (u : L_geom) :
  Lfun (ch_mor
          (var_lookup
             (named_var_to_has_var
                (nv_tail "_"%string tunit _
                  (nv_head "g"%string (tfun tunit tR') nil)))))
       (at_outer_pt_u u)
  = prom u.
Proof.
rewrite -[Lfun (ch_mor _) _]
        /(Lfun (icones_comp (em_proj2_mor (EM_term : Coalgebra Ar) funT_geom)
                            (em_proj1_mor (EM_prod (EM_term : Coalgebra Ar) funT_geom)
                                          (EM_term : Coalgebra Ar)))
               (at_outer_pt_u u)).
rewrite -[Lfun (icones_comp _ _) _]
        /(Lfun (em_proj2_mor (EM_term : Coalgebra Ar) funT_geom)
               (Lfun (em_proj1_mor (EM_prod (EM_term : Coalgebra Ar) funT_geom)
                                   (EM_term : Coalgebra Ar))
                     (at_outer_pt_u u))).
rewrite /em_proj1_mor coalg_e_term.
rewrite -[tensor_mor _ _]/(tensor_mor (icones_id Ar _) (icones_id Ar _)).
have tensor_mor_id_id :
  forall (B C : ICone.type Ar),
    tensor_mor (icones_id Ar B) (icones_id Ar C) = icones_id Ar (tensor Ar B C).
  by move=> B C; apply: tensor_ext => x y; rewrite tensor_morE.
rewrite tensor_mor_id_id icones_compIr.
rewrite /at_outer_pt_u.
rewrite tensor_runitEp.
rewrite (_ : c1_val (one1 : cone_one_car Ar) = 1%:nng); last by [].
rewrite precone_scale_1.
rewrite /em_proj2_mor.
rewrite -[Lfun (icones_comp _ _) _]
        /(iso_fwd (tensor_lunit (coalg_obj funT_geom))
            (Lfun (tensor_mor (coalg_e (EM_term : Coalgebra Ar))
                              (icones_id Ar (coalg_obj funT_geom)))
                  (ptensor (one1 : cone_one_car Ar) (prom u)))).
rewrite coalg_e_term tensor_morE.
rewrite -[Lfun (icones_id Ar _) _]/(prom u).
rewrite tensor_lunitEp.
rewrite (_ : c1_val (one1 : cone_one_car Ar) = 1%:nng); last by [].
by rewrite precone_scale_1.
Qed.

Lemma Lfun_ch_mor_ne_var_g_at_outer_pt_u_E (u : L_geom) (Hu : cone_norm u <= 1) :
  Lfun (ch_mor (eD' (ne_var (nv_tail "_"%string tunit _
                              (nv_head "g"%string (tfun tunit tR') nil)))))
       (at_outer_pt_u u)
  = prom (prom u).
Proof.
rewrite (eD_var (nv_tail "_"%string tunit _
                  (nv_head "g"%string (tfun tunit tR') nil))).
rewrite -[ch_mor (coalg_comp _ _)]
        /(icones_comp
            (ch_mor (tunit_eta (tyD (tfun tunit tR'))))
            (ch_mor (var_lookup (named_var_to_has_var
                                   (nv_tail "_"%string tunit _
                                     (nv_head "g"%string (tfun tunit tR') nil)))))).
rewrite -[Lfun (icones_comp _ _) _]
        /(Lfun (ch_mor (tunit_eta (tyD (tfun tunit tR'))))
               (Lfun (ch_mor (var_lookup (named_var_to_has_var
                                            (nv_tail "_"%string tunit _
                                              (nv_head "g"%string (tfun tunit tR') nil)))))
                     (at_outer_pt_u u))).
rewrite Lfun_var_lookup_g_at_outer_pt_u_E.
rewrite -[ch_mor (tunit_eta _)]/(coalg_str funT_geom).
rewrite (bang_cofree_str L_geom).
exact: (dig_prom (B:=L_geom) u Hu).
Qed.

(** [F_lift u] is the FMeas value [Lfun (der FMeas) (linhom_fun u one1)].
    This is the key value that appears in the parametric ELSE branch — for
    [u = u_n], [F_lift u_n = F_arr n]. *)
Definition F_lift (u : L_geom) : FMeas R_obj :=
  Lfun (der (FMeas R_obj))
       (linhom_fun u (one1 : cone_one_car Ar)).

Lemma F_lift_norm_le1 (u : L_geom) (Hu : cone_norm u <= 1) :
  cone_norm (F_lift u) <= 1.
Proof.
rewrite /F_lift.
apply: le_trans (cones_hom_norm_le1 _ _) _.
apply: le_trans (linhom_norm_apply_le Hu _) _.
by rewrite cone_norm_one1 mulr1.
Qed.

(** *** Parametric app_g_tt: result is [prom (F_lift u)] (was [prom 0] for u=0). *)
Lemma Lfun_ch_mor_app_g_tt_at_outer_pt_u_E (u : L_geom) (Hu : cone_norm u <= 1) :
  Lfun (ch_mor (eD' (ne_app
                      (ne_var (nv_tail "_"%string tunit _
                                (nv_head "g"%string (tfun tunit tR') nil)))
                      ne_tt)))
       (at_outer_pt_u u)
  = prom (F_lift u).
Proof.
rewrite (eD_app
           (ne_var (nv_tail "_"%string tunit _
                     (nv_head "g"%string (tfun tunit tR') nil)))
           (@ne_tt R Ar R_obj _)).
rewrite (eD_var (nv_tail "_"%string tunit _
                   (nv_head "g"%string (tfun tunit tR') nil))).
rewrite (eD_tt (("_"%string, tunit) :: ("g"%string, tfun tunit tR') :: nil)).
rewrite (app_kleisli_var
           (var_lookup (named_var_to_has_var
                          (nv_tail "_"%string tunit _
                            (nv_head "g"%string (tfun tunit tR') nil))))
           (em_term_mor G_geom)).
rewrite (Lfun_ch_mor_app_kleisli_at
           (var_lookup (named_var_to_has_var
                          (nv_tail "_"%string tunit _
                            (nv_head "g"%string (tfun tunit tR') nil))))
           (em_term_mor G_geom)
           (at_outer_pt_u u)).
rewrite -[coalg_obj G_geom]/(coalg_obj G_geom).
rewrite (coalg_str_G_on_outer_pt_u_E Hu).
have Houter_le1 := cone_norm_at_outer_pt_u_le1 Hu.
rewrite (bang_fmap_prom _ (at_outer_pt_u u) Houter_le1).
congr (prom _).
rewrite -[Lfun (icones_comp _ _) _]
        /(Lfun (der (coalg_obj (tyD tR')))
               (Lfun (app_under (var_lookup (named_var_to_has_var
                                  (nv_tail "_"%string tunit _
                                    (nv_head "g"%string (tfun tunit tR') nil))))
                                (em_term_mor _))
                     (at_outer_pt_u u))).
rewrite /app_under.
rewrite -[Lfun (icones_comp _ _) (at_outer_pt_u u)]
        /(Lfun (tensor_uncurry
                 (adj_phi (var_lookup (named_var_to_has_var
                            (nv_tail "_"%string tunit _
                              (nv_head "g"%string (tfun tunit tR') nil))))))
               (Lfun (icones_comp (tensor_mor (icones_id Ar _)
                                              (ch_mor (em_term_mor _)))
                                  (coalg_d G_geom))
                     (at_outer_pt_u u))).
rewrite -[Lfun (icones_comp (tensor_mor _ _) _) (at_outer_pt_u u)]
        /(Lfun (tensor_mor (icones_id Ar (coalg_obj G_geom))
                           (ch_mor (em_term_mor G_geom)))
               (Lfun (coalg_d G_geom) (at_outer_pt_u u))).
rewrite /coalg_d.
rewrite -[Lfun (icones_comp (tensor_mor _ _) _) (at_outer_pt_u u)]
        /(Lfun (tensor_mor (der (coalg_obj G_geom)) (der (coalg_obj G_geom)))
               (Lfun (icones_comp (d_bang (coalg_obj G_geom)) (coalg_str G_geom))
                     (at_outer_pt_u u))).
rewrite -[Lfun (icones_comp (d_bang _) _) (at_outer_pt_u u)]
        /(Lfun (d_bang (coalg_obj G_geom))
               (Lfun (coalg_str G_geom) (at_outer_pt_u u))).
rewrite (coalg_str_G_on_outer_pt_u_E Hu).
rewrite (d_bang_prom (A := coalg_obj G_geom) (at_outer_pt_u u) Houter_le1).
rewrite tensor_morE.
rewrite (der_prom (B := coalg_obj G_geom) (at_outer_pt_u u) Houter_le1).
rewrite tensor_morE.
rewrite -[icones_id Ar _ _]/(at_outer_pt_u u).
rewrite -[ch_mor (em_term_mor _)]/(coalg_e G_geom).
rewrite (coalg_e_G_on_outer_pt_u_E Hu).
have Heq :
  Lfun (tensor_uncurry
          (adj_phi (var_lookup (named_var_to_has_var
                     (nv_tail "_"%string tunit _
                       (nv_head "g"%string (tfun tunit tR') nil))))))
       (ptensor (at_outer_pt_u u) (one1 : cone_one_car Ar))
  = linhom_fun
      (Lfun (adj_phi (var_lookup (named_var_to_has_var
                        (nv_tail "_"%string tunit _
                          (nv_head "g"%string (tfun tunit tR') nil)))))
            (at_outer_pt_u u))
      (one1 : cone_one_car Ar).
  set F := adj_phi _.
  have HK := @tensor_uncurryK R Ar (coalg_obj G_geom)
                              (coalg_obj (tyD tunit))
                              (coalg_obj (Tobj (tyD tR'))) F.
  have := tensor_curryEp (tensor_uncurry F) (at_outer_pt_u u)
                          (one1 : cone_one_car Ar).
  rewrite HK.
  by move=> ->.
rewrite Heq.
rewrite -[adj_phi _]/(icones_comp (adj_counit _)
                                  (U_mor (var_lookup (named_var_to_has_var
                                    (nv_tail "_"%string tunit _
                                      (nv_head "g"%string (tfun tunit tR') nil)))))).
rewrite -[Lfun (icones_comp (adj_counit _) _) _]
        /(Lfun (adj_counit (linhom_car Ar (coalg_obj (tyD tunit))
                                          (coalg_obj (Tobj (tyD tR')))))
               (Lfun (U_mor (var_lookup (named_var_to_has_var
                              (nv_tail "_"%string tunit _
                                (nv_head "g"%string (tfun tunit tR') nil)))))
                     (at_outer_pt_u u))).
rewrite -[U_mor _]
        /(ch_mor (var_lookup (named_var_to_has_var
                    (nv_tail "_"%string tunit _
                      (nv_head "g"%string (tfun tunit tR') nil))))).
rewrite Lfun_var_lookup_g_at_outer_pt_u_E.
rewrite -[adj_counit _]/(der (linhom_car Ar (coalg_obj (tyD tunit))
                                            (coalg_obj (Tobj (tyD tR'))))).
rewrite (der_prom (B := L_geom) u Hu).
by [].
Qed.


(** *** §5.5 — Parametric ELSE-branch *)
Lemma Lfun_ch_mor_else_e_at_outer_pt_u_E (u : L_geom) (Hu : cone_norm u <= 1) :
  Lfun (ch_mor (eD' else_e))
       (at_outer_pt_u u)
  = prom
      (Lfun (@add_lift R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas)
            (ptensor (B := FMeas R_obj) (C := FMeas R_obj)
                     (Lfun (const_icones G_geom
                              (dirac_fmeas (R_to_carrier R_carrier_eq 1%R))
                              (dirac_fmeas_norm_le1 _))
                           (at_outer_pt_u u))
                     (F_lift u))).
Proof.
rewrite -[else_e]/(ne_add (@ne_real R Ar R_obj
                            (("_"%string, tunit)
                              :: ("g"%string, tfun tunit tR') :: nil) 1%R)
                          (ne_app (ne_var (nv_tail "_"%string tunit _
                                            (nv_head "g"%string (tfun tunit tR') nil)))
                                  ne_tt)).
rewrite (eD_add
           (R_obj := R_obj)
           (G := ("_"%string, tunit) :: ("g"%string, tfun tunit tR') :: nil)
           (ne_real (G := ("_"%string, tunit)
                            :: ("g"%string, tfun tunit tR') :: nil) 1%R)
           (ne_app (ne_var (nv_tail "_"%string tunit _
                            (nv_head "g"%string (tfun tunit tR') nil)))
                   ne_tt)).
rewrite -[ch_mor (coalg_comp (bang_cofree_hom _) _)]
        /(icones_comp (bang_fmap (@add_lift _ _ _ R_carrier_eq
                                               R_carrier_meas R_to_carrier_meas))
                      (ch_mor (coalg_comp
                                 (bang_m (FMeas R_obj) (FMeas R_obj))
                                 (em_pair _ _)))).
rewrite -[Lfun (icones_comp _ _) _]
        /(Lfun (bang_fmap (@add_lift _ _ _ R_carrier_eq
                                        R_carrier_meas R_to_carrier_meas))
               (Lfun (ch_mor (coalg_comp
                                (bang_m (FMeas R_obj) (FMeas R_obj))
                                (em_pair _ _)))
                     (at_outer_pt_u u))).
rewrite -[ch_mor (coalg_comp (bang_m _ _) _)]
        /(icones_comp (m_bang (FMeas R_obj) (FMeas R_obj))
                      (em_pair_mor (ch_mor (eD' (@ne_real R Ar R_obj
                                                  (("_"%string, tunit)
                                                    :: ("g"%string, tfun tunit tR') :: nil) 1%R)))
                                   (ch_mor (eD'
                                             (ne_app
                                                (ne_var (nv_tail "_"%string tunit _
                                                          (nv_head "g"%string (tfun tunit tR') nil)))
                                                ne_tt))))).
rewrite -[Lfun (icones_comp (m_bang _ _) _) _]
        /(Lfun (m_bang (FMeas R_obj) (FMeas R_obj))
               (Lfun (em_pair_mor (Z := G_geom)
                                  (P := Tobj (tyD tR'))
                                  (Q := Tobj (tyD tR'))
                                  (ch_mor (eD' (@ne_real R Ar R_obj
                                                  (("_"%string, tunit)
                                                    :: ("g"%string, tfun tunit tR') :: nil) 1%R)))
                                  (ch_mor (eD'
                                            (ne_app
                                               (ne_var (nv_tail "_"%string tunit _
                                                         (nv_head "g"%string (tfun tunit tR') nil)))
                                               ne_tt))))
                     (at_outer_pt_u u))).
rewrite /em_pair_mor.
rewrite -[Lfun (icones_comp (tensor_mor _ _) _) _]
        /(Lfun (tensor_mor
                  (ch_mor (eD' (@ne_real R Ar R_obj
                                  (("_"%string, tunit)
                                    :: ("g"%string, tfun tunit tR') :: nil) 1%R)))
                  (ch_mor (eD'
                            (ne_app
                               (ne_var (nv_tail "_"%string tunit _
                                         (nv_head "g"%string (tfun tunit tR') nil)))
                               ne_tt))))
               (Lfun (coalg_d G_geom) (at_outer_pt_u u))).
rewrite /coalg_d.
rewrite -[Lfun (icones_comp (tensor_mor _ _) _) _]
        /(Lfun (tensor_mor (der (coalg_obj G_geom)) (der (coalg_obj G_geom)))
               (Lfun (icones_comp (d_bang (coalg_obj G_geom)) (coalg_str G_geom))
                     (at_outer_pt_u u))).
rewrite -[Lfun (icones_comp (d_bang _) _) _]
        /(Lfun (d_bang (coalg_obj G_geom))
               (Lfun (coalg_str G_geom) (at_outer_pt_u u))).
rewrite (coalg_str_G_on_outer_pt_u_E Hu).
have Houter_le1 := cone_norm_at_outer_pt_u_le1 Hu.
rewrite (d_bang_prom (A := coalg_obj G_geom) (at_outer_pt_u u) Houter_le1).
rewrite tensor_morE.
rewrite (der_prom (B := coalg_obj G_geom) (at_outer_pt_u u) Houter_le1).
rewrite tensor_morE.
rewrite (Lfun_ch_mor_app_g_tt_at_outer_pt_u_E Hu).
(* Now: Lfun (bang_fmap add_lift) (Lfun (m_bang FMeas FMeas)
            (ptensor (Lfun (ch_mor (eD' (ne_real 1))) at_outer)
                     (prom (F_lift u)))) *)
set u1 := Lfun (ch_mor (eD'
                         (@ne_real R Ar R_obj
                            (("_"%string, tunit)
                              :: ("g"%string, tfun tunit tR') :: nil) 1%R)))
              (at_outer_pt_u u).
have Hu1 : cone_norm u1 <= 1.
  rewrite /u1.
  apply: le_trans (cones_hom_norm_le1 _ _) _.
  exact: cone_norm_at_outer_pt_u_le1.
have HFlift : cone_norm (prom (F_lift u)) <= 1
  by apply: prom_ball; exact: F_lift_norm_le1.
(* Reduce u1 = prom (Lfun (const_icones ...) (at_outer_pt_u u)) via eD_real *)
rewrite /u1.
rewrite (eD_real
           (G := ("_"%string, tunit) :: ("g"%string, tfun tunit tR') :: nil) 1%R).
set ci := const_icones G_geom
            (dirac_fmeas (R_to_carrier R_carrier_eq 1%R))
            (dirac_fmeas_norm_le1 (R_to_carrier R_carrier_eq 1%R)).
have Hreal_at :
  Lfun (ch_mor (@real_kleisli R Ar R_obj R_carrier_eq G_geom 1%R))
       (at_outer_pt_u u)
  = prom (Lfun ci (at_outer_pt_u u)).
  rewrite -[ch_mor (@real_kleisli _ _ _ _ _ _)]
          /(icones_comp (bang_fmap ci) (coalg_str G_geom)).
  rewrite -[Lfun (icones_comp _ _) (at_outer_pt_u u)]
          /(Lfun (bang_fmap ci) (Lfun (coalg_str G_geom) (at_outer_pt_u u))).
  rewrite (coalg_str_G_on_outer_pt_u_E Hu).
  exact: (bang_fmap_prom ci (at_outer_pt_u u) Houter_le1).
rewrite Hreal_at.
set d1 := Lfun ci (at_outer_pt_u u).
have Hd1 : cone_norm d1 <= 1.
  rewrite /d1.
  apply: le_trans (cones_hom_norm_le1 _ _) _.
  exact: cone_norm_at_outer_pt_u_le1.
rewrite (m_bang_prom (A := FMeas R_obj) (B := FMeas R_obj)
                     (x := d1) (y := F_lift u)
                     Hd1 (F_lift_norm_le1 Hu)).
have Hptensor_le1 : cone_norm (ptensor d1 (F_lift u)) <= 1.
  apply: le_trans (tensor_norm_le _ _) _.
  rewrite -[1]mulr1; apply: ler_pM.
  - exact: cone_norm_ge0.
  - exact: cone_norm_ge0.
  - exact: Hd1.
  - exact: F_lift_norm_le1.
rewrite (bang_fmap_prom _ (ptensor d1 (F_lift u)) Hptensor_le1).
by [].
Qed.

(** *** §5.6 — Parametric THEN-branch (same shape as §1, with [Hu] threaded). *)
Lemma Lfun_ch_mor_then_e_at_outer_pt_u_E (u : L_geom) (Hu : cone_norm u <= 1) :
  Lfun (ch_mor (eD' then_e))
       (at_outer_pt_u u)
  = prom (dirac_fmeas (R_to_carrier R_carrier_eq 0%R) : FMeas R_obj).
Proof.
rewrite -[then_e]/(@ne_real R Ar R_obj
                    (("_"%string, tunit) :: ("g"%string, tfun tunit tR') :: nil) 0%R).
rewrite (eD_real 0%R).
rewrite /real_kleisli.
set c := (dirac_fmeas (R_to_carrier R_carrier_eq 0%R) : FMeas R_obj).
set Hc := dirac_fmeas_norm_le1 _.
rewrite (Lfun_ch_mor_const_kleisli_at c Hc _).
rewrite (coalg_str_G_on_outer_pt_u_E Hu).
have Hbnd : cone_norm (at_outer_pt_u u) <= 1
  by exact: cone_norm_at_outer_pt_u_le1.
rewrite (bang_fmap_prom (const_icones _ c Hc) _ Hbnd).
rewrite -[Lfun (const_icones _ _ _) _]
        /(Lfun (linhom_icones (lin_pt c) (lin_pt_norm_le1 c Hc))
               (Lfun (coalg_e G_geom) _)).
rewrite (coalg_e_G_on_outer_pt_u_E Hu).
rewrite linhom_iconesE.
rewrite -[one1]/(MkConeOne Ar 1%:nng).
by rewrite lin_pt_unit.
Qed.


(** *** §5.7 — Parametric convex combination evaluation *)

(** Local body_inner expression. *)
Local Notation body_inner_u :=
  (ne_if tR'
    (ne_bernoulli (1/2 : R)%R (phase4_half_ge0 R) (phase4_half_le1 R))
    (@ne_real R Ar R_obj
       (("_"%string, tunit) :: ("g"%string, tfun tunit tR') :: nil) 0%R)
    (ne_add (@ne_real R Ar R_obj
              (("_"%string, tunit) :: ("g"%string, tfun tunit tR') :: nil) 1%R)
            (ne_app (ne_var (nv_tail "_"%string tunit _
                              (nv_head "g"%string (tfun tunit tR') nil)))
                    ne_tt))).

(** [Step_geom one1 (prom u) = prom (Lfun (tensor_curry (ch_mor body_inner)) (one1 ⊗ prom u))]. *)
Lemma Step_geom_one_prom_u_E (u : L_geom) (Hu : cone_norm u <= 1) :
  Step_geom' one1 (prom u) =
  prom (Lfun (tensor_curry (ch_mor (eD' body_inner_u)))
             (ptensor one1 (prom u))).
Proof.
rewrite /Step_geom' /Step_geom.
have HMb : @M_body R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas
  = coalg_comp (tunit_eta funT_geom) (lam_coalg (eD' body_inner_u)).
  rewrite -[LHS]/(eD' (@ex_geom_body R Ar R_obj)).
  by rewrite /ex_geom_body eD_lam.
rewrite HMb coalg_comp_mor.
rewrite -[ch_mor (tunit_eta funT_geom)]/(coalg_str funT_geom)
        (bang_cofree_str L_geom).
rewrite -[Lfun (bang_fmap (der L_geom)) (Lfun (icones_comp _ _) _)]
        /(Lfun (icones_comp (bang_fmap (der L_geom))
                            (icones_comp (dig L_geom)
                                         (ch_mor (lam_coalg (eD' body_inner_u)))))
               (ptensor (one1 : cone_one_car Ar) (prom u))).
rewrite icones_compA (comonad_counitR L_geom) icones_compIl.
exact: (lam_coalg_at_one_prom (eD' body_inner_u) Hu).
Qed.

(** Convex form for body_inner. *)
Lemma body_inner_u_via_convex :
  eD' body_inner_u =
  convex_combination (eD' then_e) (eD' else_e)
                     (phase4_half_ge0 R) (phase4_half_le1 R).
Proof.
exact: (case_em_bernoulli (eD' then_e) (eD' else_e)
                          (phase4_half_ge0 R) (phase4_half_le1 R)).
Qed.

(** Norm bound on the inner linhom for general u. *)
Lemma cone_norm_K_u_le1 (u : L_geom) (Hu : cone_norm u <= 1) :
  cone_norm
    (Lfun (tensor_curry
            (ch_mor (convex_combination (eD' then_e) (eD' else_e)
                                        (phase4_half_ge0 R)
                                        (phase4_half_le1 R))))
          (ptensor one1 (prom u)))
  <= 1.
Proof.
apply: le_trans (cones_hom_norm_le1 _ _) _.
exact: cone_norm_inner_pt_u_le1 Hu.
Qed.

(** Post-[der] form of Step_geom one1 (prom u). *)
Lemma der_Step_geom_one_prom_u_E (u : L_geom) (Hu : cone_norm u <= 1) :
  Lfun (der L_geom) (Step_geom' one1 (prom u))
  = Lfun (tensor_curry
           (ch_mor (convex_combination (eD' then_e) (eD' else_e)
                                       (phase4_half_ge0 R)
                                       (phase4_half_le1 R))))
        (ptensor one1 (prom u)).
Proof.
rewrite (Step_geom_one_prom_u_E Hu).
rewrite body_inner_u_via_convex.
exact: (der_prom (B := L_geom) _ (cone_norm_K_u_le1 Hu)).
Qed.

(** Eval-at-one1 form (post-der, post-eval-at-one1). *)
Lemma linhom_fun_der_Step_geom_one1_u_E (u : L_geom) (Hu : cone_norm u <= 1) :
  linhom_fun
    (Lfun (der L_geom) (Step_geom' one1 (prom u)))
    (one1 : cone_one_car Ar)
  = Lfun (ch_mor (convex_combination (eD' then_e) (eD' else_e)
                                     (phase4_half_ge0 R)
                                     (phase4_half_le1 R)))
        (at_outer_pt_u u).
Proof.
rewrite (der_Step_geom_one_prom_u_E Hu).
rewrite /at_outer_pt_u.
exact: (tensor_curryE
          (B := coalg_obj (EM_prod (EM_term : Coalgebra Ar) funT_geom))
          (C := coalg_obj (EM_term : Coalgebra Ar))
          (D := coalg_obj (Tobj (tyD tR' : Coalgebra Ar)))
          (ch_mor (convex_combination (eD' then_e) (eD' else_e)
                                      (phase4_half_ge0 R)
                                      (phase4_half_le1 R)))
          (ptensor one1 (prom u)) one1).
Qed.

(** [Lfun (ch_mor convex_combination)] at outer pt as [prom (Lfun convex_icones _)]. *)
Lemma Lfun_ch_mor_convex_at_outer_pt_u_E (u : L_geom) (Hu : cone_norm u <= 1) :
  Lfun (ch_mor (convex_combination (eD' then_e) (eD' else_e)
                                   (phase4_half_ge0 R)
                                   (phase4_half_le1 R)))
       (at_outer_pt_u u)
  = prom (Lfun (convex_icones (eD' then_e) (eD' else_e)
                              (phase4_half_ge0 R) (phase4_half_le1 R))
               (at_outer_pt_u u)).
Proof.
rewrite /convex_combination.
rewrite (Lfun_ch_mor_adj_psi_at
           (convex_icones (eD' then_e) (eD' else_e)
                          (phase4_half_ge0 R) (phase4_half_le1 R))
           (at_outer_pt_u u)).
rewrite (coalg_str_G_on_outer_pt_u_E Hu).
have Hbnd := cone_norm_at_outer_pt_u_le1 Hu.
by rewrite (bang_fmap_prom
              (convex_icones (eD' then_e) (eD' else_e)
                             (phase4_half_ge0 R) (phase4_half_le1 R))
              _ Hbnd).
Qed.

(** Convex_icones at the outer point as pointwise sum decomposition. *)
Lemma Lfun_convex_icones_at_outer_pt_u_E (u : L_geom) (Hu : cone_norm u <= 1) :
  Lfun (convex_icones (eD' then_e) (eD' else_e)
                      (phase4_half_ge0 R) (phase4_half_le1 R))
       (at_outer_pt_u u)
  = Lfun (der (FMeas R_obj))
         (precone_add
            (precone_scale (NngNum (phase4_half_ge0 R))
              (Lfun (ch_mor (eD' then_e)) (at_outer_pt_u u)))
            (precone_scale (NngNum (onem_ge0 (1/2)%R (phase4_half_le1 R)))
              (Lfun (ch_mor (eD' else_e)) (at_outer_pt_u u)))).
Proof.
have Hinner :
  Lfun (convex_icones_bang (eD' then_e) (eD' else_e)
                           (phase4_half_ge0 R)
                           (phase4_half_le1 R))
       (at_outer_pt_u u)
  = precone_add
      (precone_scale (NngNum (phase4_half_ge0 R))
        (Lfun (ch_mor (eD' then_e)) (at_outer_pt_u u)))
      (precone_scale (NngNum (onem_ge0 (1/2)%R (phase4_half_le1 R)))
        (Lfun (ch_mor (eD' else_e)) (at_outer_pt_u u))).
  rewrite -[Lfun (convex_icones_bang _ _ _ _) _]
          /(linhom_fun (convex_linhom (eD' then_e) (eD' else_e)
                                      (phase4_half_ge0 R)
                                      (phase4_half_le1 R))
                       (at_outer_pt_u u)).
  rewrite convex_linhomE /bool_case.
  rewrite linhom_fun_precone_add_E.
  rewrite !linhom_fun_precone_scale_E.
  congr (precone_add (precone_scale _ _) (precone_scale _ _));
    by apply: nngnum_inj.
rewrite -[LHS]/(Lfun (der (FMeas R_obj))
                     (Lfun (convex_icones_bang (eD' then_e) (eD' else_e)
                                               (phase4_half_ge0 R)
                                               (phase4_half_le1 R))
                           (at_outer_pt_u u))).
by rewrite Hinner.
Qed.

(** Post-der combined extraction at u_n: an FMeas value of the form
    [(1/2)·δ_0 + (1/2)·add_lift(...) ] *)
Lemma der_FMeas_linhom_der_Step_E_u (u : L_geom) (Hu : cone_norm u <= 1) :
  Lfun (der (FMeas R_obj))
       (linhom_fun
          (Lfun (der L_geom) (Step_geom' one1 (prom u)))
          (one1 : cone_one_car Ar))
  = Lfun (der (FMeas R_obj))
         (precone_add
            (precone_scale (NngNum (phase4_half_ge0 R))
              (Lfun (ch_mor (eD' then_e)) (at_outer_pt_u u)))
            (precone_scale (NngNum (onem_ge0 (1/2)%R (phase4_half_le1 R)))
              (Lfun (ch_mor (eD' else_e)) (at_outer_pt_u u)))).
Proof.
rewrite (linhom_fun_der_Step_geom_one1_u_E Hu).
rewrite (Lfun_ch_mor_convex_at_outer_pt_u_E Hu).
have Hnorm : cone_norm
                (Lfun (convex_icones (eD' then_e) (eD' else_e)
                                     (phase4_half_ge0 R)
                                     (phase4_half_le1 R))
                      (at_outer_pt_u u)) <= 1.
  apply: le_trans (cones_hom_norm_le1 _ _) _.
  exact: cone_norm_at_outer_pt_u_le1.
rewrite (der_prom (B := FMeas R_obj) _ Hnorm).
exact: (Lfun_convex_icones_at_outer_pt_u_E Hu).
Qed.

(** *** §5.8 — F_arr (n+1) decomposition

    Combines the previous results: [F_arr (n+1) = (1/2)·δ_0 +
    (1/2)·add_lift(δ_1, F_arr n)]. *)

(** A helper notation for the parametric ELSE-FMeas extracted value
    (after [Lfun (der FMeas)]): [add_lift (δ_1, F_lift u)]. *)
Definition else_branch_fmeas (u : L_geom) : FMeas R_obj :=
  Lfun (@add_lift R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas)
       (ptensor (B := FMeas R_obj) (C := FMeas R_obj)
                (dirac_fmeas (R_to_carrier R_carrier_eq 1%R)) (F_lift u)).

(** [Lfun (der FMeas) (Lfun ch_mor else_e ...) = else_branch_fmeas u]. *)
Lemma der_else_branch_u_E (u : L_geom) (Hu : cone_norm u <= 1) :
  Lfun (der (FMeas R_obj))
       (Lfun (ch_mor (eD' else_e)) (at_outer_pt_u u))
  = else_branch_fmeas u.
Proof.
rewrite (Lfun_ch_mor_else_e_at_outer_pt_u_E Hu).
(* Goal: Lfun (der FMeas) (prom (Lfun add_lift (ptensor ...))) =
        Lfun add_lift (ptensor (dirac 1) (F_lift u)) *)
(* Need to compute the const_icones bit: at one1 it gives dirac 1. *)
have Hci_at :
  Lfun (const_icones G_geom
          (dirac_fmeas (R_to_carrier R_carrier_eq 1%R))
          (dirac_fmeas_norm_le1 (R_to_carrier R_carrier_eq 1%R)))
       (at_outer_pt_u u)
  = dirac_fmeas (R_to_carrier R_carrier_eq 1%R).
  set Hc := dirac_fmeas_norm_le1 _.
  rewrite -[Lfun (const_icones _ _ _) _]
          /(Lfun (linhom_icones (lin_pt (dirac_fmeas (R_to_carrier R_carrier_eq 1%R)))
                                (lin_pt_norm_le1
                                  (dirac_fmeas (R_to_carrier R_carrier_eq 1%R)) Hc))
                 (Lfun (coalg_e G_geom) (at_outer_pt_u u))).
  rewrite (coalg_e_G_on_outer_pt_u_E Hu).
  rewrite linhom_iconesE.
  rewrite -[one1]/(MkConeOne Ar 1%:nng).
  by rewrite lin_pt_unit.
rewrite Hci_at.
have Hptensor_le1 : cone_norm
  (ptensor (B := FMeas R_obj) (C := FMeas R_obj)
           (dirac_fmeas (R_to_carrier R_carrier_eq 1%R)) (F_lift u)) <= 1.
  apply: le_trans (tensor_norm_le _ _) _.
  rewrite -[1]mulr1; apply: ler_pM.
  - exact: cone_norm_ge0.
  - exact: cone_norm_ge0.
  - exact: dirac_fmeas_norm_le1.
  - exact: F_lift_norm_le1.
have Halr_le1 : cone_norm
  (Lfun (@add_lift R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas)
    (ptensor (B := FMeas R_obj) (C := FMeas R_obj)
             (dirac_fmeas (R_to_carrier R_carrier_eq 1%R)) (F_lift u))) <= 1.
  apply: le_trans (cones_hom_norm_le1 _ _) Hptensor_le1.
rewrite (der_prom (B := FMeas R_obj) _ Halr_le1).
by [].
Qed.

(** [Lfun (der FMeas) (Lfun ch_mor then_e ...) = dirac 0]. *)
Lemma der_then_branch_u_E (u : L_geom) (Hu : cone_norm u <= 1) :
  Lfun (der (FMeas R_obj))
       (Lfun (ch_mor (eD' then_e)) (at_outer_pt_u u))
  = dirac_fmeas (R_to_carrier R_carrier_eq 0%R) :> FMeas R_obj.
Proof.
rewrite (Lfun_ch_mor_then_e_at_outer_pt_u_E Hu).
exact: (der_prom (B := FMeas R_obj) _
          (dirac_fmeas_norm_le1 (R_to_carrier R_carrier_eq 0%R))).
Qed.

(** Combined: F_arr-recurrence value. *)
Lemma F_arr_S_E_via_u (u : L_geom) (Hu : cone_norm u <= 1) :
  Lfun (der (FMeas R_obj))
       (linhom_fun
          (Lfun (der L_geom) (Step_geom' one1 (prom u)))
          (one1 : cone_one_car Ar))
  = precone_add
      (precone_scale (NngNum (phase4_half_ge0 R))
        (dirac_fmeas (R_to_carrier R_carrier_eq 0%R) : FMeas R_obj))
      (precone_scale (NngNum (onem_ge0 (1/2)%R (phase4_half_le1 R)))
        (else_branch_fmeas u)).
Proof.
rewrite (der_FMeas_linhom_der_Step_E_u Hu).
have [_ HderD HderZ] :=
  cones_hom_linear
    (mcones_hom_cones (icones_hom_mcones (der (FMeas R_obj)))).
rewrite HderD !HderZ.
rewrite (der_then_branch_u_E Hu).
by rewrite (der_else_branch_u_E Hu).
Qed.

(** *** §5.9 — F_arr recurrence

    More directly: for any u with [kleene_arr n = prom u] and [‖u‖ ≤ 1],
    we have the explicit decomposition.  We avoid [cid] entirely and instead
    take the witness as a parameter. *)
Lemma F_arr_S_E_via_witness (n : nat) (u : L_geom)
    (Hu_eq : kleene_arr' n = prom u) (Hu_norm : cone_norm u <= 1) :
  F_arr' n.+1
  = precone_add
      (precone_scale (NngNum (phase4_half_ge0 R))
        (dirac_fmeas (R_to_carrier R_carrier_eq 0%R) : FMeas R_obj))
      (precone_scale (NngNum (onem_ge0 (1/2)%R (phase4_half_le1 R)))
        (else_branch_fmeas u)).
Proof.
rewrite -[F_arr' n.+1]/(Lfun (der (FMeas R_obj))
                          (linhom_fun
                             (Lfun (der L_geom) (kleene_arr' n.+1))
                             (one1 : cone_one_car Ar))).
rewrite kleene_arr_S Hu_eq.
rewrite -[Phi_arr _]/(Step_geom' one1 (prom u)).
exact: F_arr_S_E_via_u Hu_norm.
Qed.

(** F_lift u_n agrees with F_arr n.  Crucial because the else_branch_fmeas
    formula uses F_lift, but we want mass(F_arr n). *)
Lemma F_lift_eq_F_arr (n : nat) (u : L_geom) (Hu_eq : kleene_arr' n = prom u)
    (Hu_norm : cone_norm u <= 1) :
  F_lift u = F_arr' n.
Proof.
rewrite /F_lift /F_arr Hu_eq.
by rewrite (der_prom (B := L_geom) u Hu_norm).
Qed.

(** *** §5.10 — Mass recurrence

    [mass(F_arr (n+1)) = 1/2 + (1/2) · mass(F_arr n)].

    Via [add_lift_mass] applied to the ELSE branch. *)
Lemma F_arr_S_mass (n : nat) :
  fmeas_mu (F_arr' n.+1) [set: ar_carrier Ar R_obj]
  = ((1/2)%R%:E + (1/2)%R%:E * fmeas_mu (F_arr' n) [set: ar_carrier Ar R_obj])%E.
Proof.
have [u [Hu_eq Hu_norm]] := @kleene_arr_is_prom R Ar R_obj
  R_carrier_eq R_carrier_meas R_to_carrier_meas n.
rewrite (F_arr_S_E_via_witness Hu_eq Hu_norm).
rewrite -[precone_add _ _]/(fmeas_add
   (precone_scale (NngNum (phase4_half_ge0 R))
                  (dirac_fmeas (R_to_carrier R_carrier_eq 0%R) : FMeas R_obj))
   (precone_scale (NngNum (onem_ge0 (1/2)%R (phase4_half_le1 R)))
                  (else_branch_fmeas u))).
rewrite fmeas_addE.
rewrite -[precone_scale _ (dirac_fmeas _)]
        /(fmeas_scale (NngNum (phase4_half_ge0 R))
                      (dirac_fmeas (R_to_carrier R_carrier_eq 0%R) : FMeas R_obj)).
rewrite -[precone_scale _ (else_branch_fmeas _)]
        /(fmeas_scale (NngNum (onem_ge0 (1/2)%R (phase4_half_le1 R)))
                      (else_branch_fmeas u)).
rewrite !fmeas_scaleE.
rewrite dirac_fmeas_setT_E mule1.
have Helse :
  fmeas_mu (else_branch_fmeas u) [set: ar_carrier Ar R_obj]
  = fmeas_mu (F_lift u) [set: ar_carrier Ar R_obj].
  rewrite /else_branch_fmeas.
  exact: add_lift_mass.
rewrite Helse.
rewrite (F_lift_eq_F_arr Hu_eq Hu_norm).
have onem_half_E : ((1 - 1 / 2)%R = (1/2)%R :> R).
  have e : (1 : R) = 1/2 + 1/2 by rewrite -splitr.
  by rewrite {1}e addrK.
have -> : ((NngNum (onem_ge0 (1/2)%R (phase4_half_le1 R)))%:num)%:E
       = (1/2)%R%:E :> \bar R.
  by rewrite /=; congr (_%:E); exact: onem_half_E.
by [].
Qed.


(** *** §5.11 — Closed-form mass: [mass(F_arr n) = 1 - (1/2)^n] *)
Lemma F_arr_mass_closed (n : nat) :
  fmeas_mu (F_arr' n) [set: ar_carrier Ar R_obj]
  = (1 - (1/2)^+n : R)%R%:E.
Proof.
induction n.
- rewrite F_arr_0_mass_zero.
  by rewrite expr0 subrr.
- rewrite F_arr_S_mass IHn.
  rewrite -EFinM -EFinD.
  congr (_%:E).
  rewrite exprSr.
  rewrite [in LHS]mulrBr [in LHS]mulr1 addrA.
  have -> : ((1/2 + 1/2)%R = 1 :> R) by rewrite -splitr.
  by rewrite mulrC.
Qed.


(** *** §5.12 — Mass convergence: [mass(F_arr n) → 1] *)
Local Open Scope ereal_scope.
Lemma F_arr_mass_cvg :
  fmeas_mu (F_arr' n) [set: ar_carrier Ar R_obj]
    @[n --> \oo] --> (1 : \bar R).
Proof.
under eq_fun => n do rewrite F_arr_mass_closed.
rewrite (_ : (1 : \bar R) = ((1 - 0)%R : R)%R%:E); last by rewrite subr0.
apply: cvg_EFin.
  by apply: nearW => n; rewrite //=.
apply: cvgB.
- exact: cvg_cst.
- apply: cvg_expr.
  rewrite gtr0_norm ?divr_gt0//.
  by rewrite ltr_pdivrMr // mul1r ltr1n.
Qed.
Local Close Scope ereal_scope.


(** *** §5.13 — F_arr chain in FMeas: increasing + norm-bounded *)
Lemma F_arr_chain (n : nat) : precone_le (F_arr' n) (F_arr' n.+1).
Proof.
have Hder_L_lin := cones_hom_linear
  (mcones_hom_cones (icones_hom_mcones (der L_geom))).
have Hder_F_lin := cones_hom_linear
  (mcones_hom_cones (icones_hom_mcones (der (FMeas R_obj)))).
have Hchain_k := @kleene_arr_chain R Ar R_obj
  R_carrier_eq R_carrier_meas R_to_carrier_meas n.
have Hchain_derL :
  precone_le (Lfun (der L_geom) (kleene_arr' n))
             (Lfun (der L_geom) (kleene_arr' n.+1)).
  exact: (linear_increasing Hder_L_lin Hchain_k).
have Hchain_linhom :
  precone_le (linhom_fun (Lfun (der L_geom) (kleene_arr' n))
                         (one1 : cone_one_car Ar))
             (linhom_fun (Lfun (der L_geom) (kleene_arr' n.+1))
                         (one1 : cone_one_car Ar)).
  case: Hchain_derL => w Hw_eq.
  exists (linhom_fun w (one1 : cone_one_car Ar)).
  rewrite Hw_eq.
  exact: linhom_fun_precone_add_E.
exact: (linear_increasing Hder_F_lin Hchain_linhom).
Qed.

Lemma F_arr_ball (n : nat) : cone_norm (F_arr' n) <= 1.
Proof.
rewrite /F_arr.
apply: le_trans (cones_hom_norm_le1 _ _) _.
apply: le_trans (linhom_norm_apply_le _ (one1 : cone_one_car Ar)) _.
  apply: le_trans (cones_hom_norm_le1 _ _) _.
  exact: kleene_arr_ball.
by rewrite cone_norm_one1 mulr1.
Qed.

(** F_arr supremum at the FMeas level. *)
Definition F_arr_sup : FMeas R_obj :=
  fmeas_sup_ball F_arr_chain F_arr_ball.

(** Mass of the sup = 1 (via [fmeas_sup_cvg] + [cvg_unique] with
    [F_arr_mass_cvg]). *)
Local Open Scope ereal_scope.
Lemma F_arr_sup_mass :
  fmeas_mu F_arr_sup [set: ar_carrier Ar R_obj] = 1.
Proof.
rewrite /F_arr_sup.
rewrite (fmeas_sup_ballE F_arr_chain F_arr_ball measurableT).
have Hsupcvg : fmeas_mu (F_arr' n) [set: ar_carrier Ar R_obj]
                 @[n --> \oo]
                 --> fmeas_sup_meas_fun F_arr_chain [set: ar_carrier Ar R_obj].
  by apply: (@fmeas_sup_cvg R _ _ F_arr' F_arr_chain); exact: measurableT.
have := @cvg_unique _ (@ereal_hausdorff R) _ _ _ _ Hsupcvg F_arr_mass_cvg.
move=> ->; reflexivity.
Qed.

Local Close Scope ereal_scope.

End ExGeomArrMassOne.
