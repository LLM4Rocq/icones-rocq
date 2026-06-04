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
From mathcomp.analysis Require Import sequences.

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

(** ** Stage 4 — Headline: target identity (statement only, proof
    deferred)

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
    1. Per-iterate mass identity: [F_n n_arr := Lfun (der (FMeas
       R_obj)) (linhom_fun (Lfun (der L_geom) (kleene_arr n))
       one1)] has mass [1 - (1/2)^n] for every [n].  Base case [n=0]:
       mass 0 (since [kleene_arr 0 = prom 0_L]).  Step: mass-recurrence
       [mass(F_{n+1}) = 1/2 + (1/2)·mass(F_n)] via [add_lift_mass]
       composed with §1's [first_iterate_FMeas_mass_half]-style
       per-branch analysis at each iterate.
    2. Sup of [1 - (1/2)^n] = 1 via [cvg_geometric] (in
       [mathcomp.analysis.sequences]).
    3. [fmeas_sup_cvg] (from [theories/mcones/fmeas.v]) to commute
       mass with sup.

    Substantial infrastructure required at each step; left as
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
