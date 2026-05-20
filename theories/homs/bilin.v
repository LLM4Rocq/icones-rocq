(** * Paper Theorem 6.1 — [Path(X, B) ≃ FMeas(X) ⊸ B]

    Paper reference: §6, lines 2835–3040 of [paper/icones.txt].

    For [X : ar_obj Ar] and [B : ICone.type Ar], the paper builds
    an isomorphism in [MCones] between [path_car Ar X B] and
    [linhom_car Ar (fmeas R (ar_carrier Ar X)) B] via the
    integration operator

      [I^B_X(β)(µ) := icone_integral β _ µ]

    and its inverse

      [K^B_X(f)(r) := f (\d_r)].

    Coverage in this file.

    - [dirac_fmeas r] — paper §6 paragraph 1: the canonically-
      extended Dirac mass on [ar_carrier Ar X] at point [r], packaged
      as an element of the [fmeas R (ar_carrier Ar X)] cone. The
      underlying measure agrees with mathcomp-analysis's [\d_r] on
      measurable sets and is zero off the σ-algebra (the [fmeas]
      canonicality invariant).

    - [dirac_path X] — paper §6 paragraph 1: the path
      [δ_X : ar_carrier X → fmeas R (ar_carrier X)] sending [r] to
      [dirac_fmeas r]. Bounded by [1] and a measurable path, hence
      a [path_car Ar X (fmeas R (ar_carrier Ar X))].

    - [int_to_linhom β] — paper Thm 6.1 forward direction, packaged
      as a full [linhom_car Ar (fmeas R (ar_carrier Ar X)) B].  All
      five [linhom_car] fields are proved:

      * [int_to_linhom_fun_linear]: linearity in [µ] (paper Lemma 4.7).
      * [int_to_linhom_fun_continuous]: ω-continuity in [µ] (paper
        Lemma 4.7); proved by rescaling [β] to the unit ball,
        invoking [integral_omega_cont_meas] on the rescaled path,
        and pulling back through [sup_ball_scaler] / [icone_integral_scaleB].
      * [int_to_linhom_fun_bounded]: operator-norm boundedness
        with constant [M := path_norm β] (paper Lemma 4.2).
      * [int_to_linhom_fun_pres_path]: measurable-path preservation
        in the [fmeas] argument (paper Lemma 4.7, joint measurability).
      * [int_to_linhom_fun_pres_int]: integral preservation
        (paper Thm 4.15 / cone-Fubini), via the kernel-Tonelli
        identity [icone_integral_kernel_tonelli], which packages [β']
        and [µ'] as finite kernels and invokes mathcomp-analysis's
        [integral_kcomp].

    - [linhom_to_int f] — paper Thm 6.1 inverse direction. Takes
      a [linhom_car Ar (fmeas R (ar_carrier Ar X)) B] and produces
      a [path_car Ar X B] via [r ↦ linhom_fun f (dirac_fmeas r)].

    - [icone_integral_dirac_path] — paper Thm 6.1 Dirac
      approximation: every [µ : fmeas R X] equals the integral of
      its Diracs, [icone_integral dirac_path Hδ µ = µ].  Proved by
      [fmeas_eq] checking on every measurable set [U] via the
      Pettis equation against [fmeas_eU U] and [integral_indic].

    - [K_I_int_to_linhom_path_E] — paper Thm 6.1 round-trip
      [K ∘ I = id] at the [path_car] level: [linhom_to_int
      (int_to_linhom β) = β].

    - [I_K_int_to_linhom_E] — paper Thm 6.1 round-trip [I ∘ K = id]
      at the [linhom_car] level: [int_to_linhom (linhom_to_int f) =
      f].  Proved by extensionality, the Dirac approximation, and
      [linhom_pres_int f].

    Deferred to wave 3 / follow-up.

    - [mcones_iso] packaging: build [int_to_linhom] and
      [linhom_to_int] as [mcones_hom] morphisms in [MCones] and
      witness their mutual inverse.  The packaging is non-trivial
      because [cones_hom_norm_le1] requires norm-decrease ([cnorm
      (f x) ≤ cnorm x]) whereas [int_to_linhom β] is bounded by
      [path_norm β], not [1]; a normalization wrapper or a
      relaxation of [cones_hom_norm_le1] is needed for the
      packaging.
    - Naturality in [X] (via pushforward) and in [B] (via
      post-composition). *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals constructive_ereal.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import ereal sequences ereal_normedtype.
From mathcomp.analysis Require Import topology normedtype.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import measure.
From mathcomp.analysis Require Import dirac_measure.
From mathcomp.analysis Require Import lebesgue_integral_definition.
From mathcomp.analysis Require Import lebesgue_integral_nonneg.
From mathcomp.analysis Require Import lebesgue_integral_monotone_convergence.
From mathcomp.analysis Require Import kernel.
Import numFieldTopology.Exports.

Require Import Icones.prelude.classical_extra.
Require Import Icones.prelude.nonneg_extra.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.cone_cat.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.mcones.path.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.pettis.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_integral.
Require Import Icones.icones.examples_icone.
Require Import Icones.icones.fubini.
Require Import Icones.icones.icone_cat.
Require Import Icones.homs.linhom.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** Paper §6 paragraph 1 — the Dirac path [δ_X]

    For each [X : ar_obj Ar] the function [r ↦ \d_r] is a bounded
    measurable path of unit total mass in
    [fmeas R (ar_carrier Ar X)]. mathcomp-analysis's [\d_r] is a
    measure on the entire powerset; we glue it to [0] off the
    σ-algebra so that the [fmeas] canonicality invariant holds. *)

Section DiracPath.
Variables (R : realType) (Ar : MeasSubcat R).
Variable X : ar_obj Ar.

(** Canonical Dirac measure at [r], with [0] off the σ-algebra. *)
Local Definition dirac_canon_fun (r : ar_carrier Ar X) :
    set (ar_carrier Ar X) -> \bar R :=
  fun U => if `[< measurable U >] then (\d_r U : \bar R) else 0%E.

Local Lemma dirac_canon_funE (r : ar_carrier Ar X) U :
  measurable U -> dirac_canon_fun r U = \d_r U.
Proof. by move=> mU; rewrite /dirac_canon_fun asboolT. Qed.

Local Lemma dirac_canon_fun_off (r : ar_carrier Ar X) U :
  ~ measurable U -> dirac_canon_fun r U = 0%E.
Proof. by move=> nmU; rewrite /dirac_canon_fun asboolF. Qed.

Local Lemma dirac_canon_set0 (r : ar_carrier Ar X) :
  dirac_canon_fun r set0 = 0%E.
Proof. by rewrite dirac_canon_funE ?measurable0// dirac0. Qed.

Local Lemma dirac_canon_ge0 (r : ar_carrier Ar X) U :
  (0 <= dirac_canon_fun r U)%E.
Proof.
rewrite /dirac_canon_fun; case: asboolP => _; last exact: lexx.
exact: measure_ge0.
Qed.

Local Lemma dirac_canon_sigma_additive (r : ar_carrier Ar X) :
  semi_sigma_additive (dirac_canon_fun r).
Proof.
move=> F mF tF mUF.
have step : forall n,
  (\sum_(0 <= i < n) dirac_canon_fun r (F i))%E =
  (\sum_(0 <= i < n) (\d_r (F i) : \bar R))%E.
  move=> n; apply: eq_bigr => i _.
  by rewrite dirac_canon_funE//; exact: mF.
rewrite dirac_canon_funE//.
under eq_fun do rewrite step.
exact: measure_semi_sigma_additive.
Qed.

Arguments dirac_canon_set0 : clear implicits.
Arguments dirac_canon_ge0 : clear implicits.
Arguments dirac_canon_sigma_additive : clear implicits.

Section DiracCanonMeasure.
Variable r : ar_carrier Ar X.

HB.instance Definition _ :=
  @isMeasure.Build (ar_disp Ar X) (ar_carrier Ar X) R
    (dirac_canon_fun r)
    (dirac_canon_set0 r) (dirac_canon_ge0 r)
    (dirac_canon_sigma_additive r).

End DiracCanonMeasure.

Local Lemma dirac_canon_finP (r : ar_carrier Ar X) :
  fmeas_finP (R:=R) (dirac_canon_fun r).
Proof.
move=> U _; rewrite /dirac_canon_fun.
case: asboolP => _; last by [].
rewrite diracE; by case: (r \in U).
Qed.

Local Lemma dirac_canon_canon (r : ar_carrier Ar X) :
  fmeas_canon (R:=R) (dirac_canon_fun r).
Proof. exact: dirac_canon_fun_off. Qed.

(** Paper §6 paragraph 1: the canonical [fmeas R X] underlying the
    Dirac mass at [r]. *)
Definition dirac_fmeas (r : ar_carrier Ar X) : fmeas R (ar_carrier Ar X) :=
  MkFmeas [the {measure set _ -> \bar R} of dirac_canon_fun r]
          (dirac_canon_finP r) (dirac_canon_canon r).

(** [dirac_fmeas r] agrees with [\d_r] on measurable sets. *)
Lemma dirac_fmeas_E (r : ar_carrier Ar X) U :
  measurable U -> fmeas_mu (dirac_fmeas r) U = \d_r U.
Proof. by move=> mU; exact: dirac_canon_funE. Qed.

(** [dirac_fmeas r] has unit total mass. *)
Lemma dirac_fmeas_setT_E (r : ar_carrier Ar X) :
  fmeas_mu (dirac_fmeas r) [set: ar_carrier Ar X] = 1%E.
Proof. by rewrite dirac_fmeas_E// diracT. Qed.

Lemma dirac_fmeas_norm (r : ar_carrier Ar X) :
  cone_norm (dirac_fmeas r) = 1.
Proof.
by rewrite /cone_norm/= /fmeas_norm/= dirac_fmeas_setT_E.
Qed.

(** Paper §6 paragraph 1: [r ↦ dirac_fmeas r] is a bounded measurable
    path. Boundedness is immediate; joint test-measurability via the
    [e_U] test family reduces to measurability of [r ↦ \1_U r]. *)
Lemma dirac_fmeas_is_path :
  is_measurable_path (Ar:=Ar) (C:=fmeas R (ar_carrier Ar X))
    (X:=X) dirac_fmeas.
Proof.
split.
  by exists 1 => r; rewrite dirac_fmeas_norm.
move=> Y m mM.
case: mM => [U [mU ->]].
apply: (eq_measurable_fun
  (fun p : ar_carrier Ar Y * ar_carrier Ar X =>
     fine (\d_(p.2) U : \bar R))).
  by move=> p _; rewrite /= /eU_fun/= dirac_fmeas_E.
pose g (r : ar_carrier Ar X) : \bar R := \d_r U.
have g_meas : measurable_fun [set: ar_carrier Ar X] g.
  by apply: measurable_fun_dirac.
have finecomp : measurable_fun [set: ar_carrier Ar X]
                  (fun r : ar_carrier Ar X => fine (g r)).
  by apply: (measurableT_comp (f := fine)) => //; exact: fine_measurable.
exact: (measurableT_comp finecomp measurable_snd).
Qed.

(** Paper §6 paragraph 1: [δ_X] as a [path_car]. *)
Definition dirac_path : path_car Ar X (fmeas R (ar_carrier Ar X)) :=
  MkPath dirac_fmeas_is_path.

End DiracPath.

Arguments dirac_fmeas {R Ar X}.
Arguments dirac_path {R} Ar X.

(** ** Paper Thm 6.1 forward direction (function level) — [int_to_linhom_fun β]

    For [β ∈ Path(X, B)], the function [µ ↦ ∫β dµ]. Linearity in
    [µ] is the only field we deliver at this level; full packaging
    as a [linhom_car] is deferred (see file header). *)

Section IntToLinhomFun.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (X : ar_obj Ar) (B : ICone.type Ar).
Variable β : path_car Ar X B.

Local Notation Hβ := (path_is_path β).
Local Notation βf := (path_fun β).

(** The underlying function: [µ ↦ icone_integral β Hβ µ]. *)
Definition int_to_linhom_fun :
    fmeas R (ar_carrier Ar X) -> B :=
  fun µ => icone_integral βf Hβ µ.

(** Paper Lemma 4.7: [int_to_linhom_fun β] is linear in [µ]. *)
Lemma int_to_linhom_fun_linear : is_linear int_to_linhom_fun.
Proof.
split.
- (* The integral against [fmeas_zero] is [precone_zero]. *)
  apply/esym/icone_integral_eqP => m mM s.
  rewrite test_lin0.
  have -> : fmeas_mu (fmeas_zero (R:=R) (X:=ar_carrier Ar X))
            = mzero :> (_ -> _) by [].
  by rewrite integral_measure_zero.
- by move=> µ1 µ2; rewrite /int_to_linhom_fun; exact: icone_integral_addmu.
- by move=> r µ; rewrite /int_to_linhom_fun; exact: icone_integral_scalemu.
Qed.

(** Paper Lemma 4.2 + Lemma 4.7: boundedness. With [M := path_norm β],
    [‖∫β dµ‖ ≤ path_norm β · fmeas_norm µ ≤ path_norm β · 1]
    when [µ] is in the unit ball. *)
Lemma int_to_linhom_fun_bounded :
  exists M : R,
    forall µ : fmeas R (ar_carrier Ar X),
      cone_norm µ <= 1 -> cone_norm (int_to_linhom_fun µ) <= M.
Proof.
exists (path_norm β) => µ Hµ.
apply: (@le_trans _ _ (path_norm β * fmeas_norm µ)); last first.
  rewrite -[X in _ <= X]mulr1.
  by apply: ler_wpM2l; [exact: path_norm_ge0|exact: Hµ].
apply: (path_integral_norm_le (Mβ := path_norm β)).
- move=> r; exact: path_norm_ub.
- exact: Hβ.
- exact: icone_integralP.
Qed.

(** Paper Lemma 4.7 (ω-continuity in [µ]).

    Rescale [β] to the unit ball via [β_unit := sinv *: β] where
    [s := path_norm β + 1] and [sinv := s^{-1}]. Then
    [integral_omega_cont_meas] applies to [β_unit] (a path with
    [path_norm β_unit ≤ 1]) on any unit-ball measure chain. The
    image scalar [sinv] commutes with [cone_sup_ball] via
    [sup_ball_scaler]; scaling back by [s] recovers the unscaled
    statement, using [icone_integral_scaleB] to compare
    [icone_integral (sinv *: β) _ µ] with
    [precone_scale sinv (icone_integral β _ µ)]. *)
Lemma int_to_linhom_fun_continuous : is_omega_continuous int_to_linhom_fun.
Proof.
move=> µn µn_chain µn_bound fµn_chain fµn_bound.
(* Build [s := path_norm β + 1 > 0] and [sinv := s^{-1}]. *)
pose s_num : R := path_norm β + 1.
have s_pos : 0 < s_num.
  by rewrite /s_num ltr_wpDl ?ltr01 ?path_norm_ge0.
have s_ge0 : 0 <= s_num by exact: ltW.
pose s : {nonneg R} := NngNum s_ge0.
have sinv_ge0 : 0 <= s_num^-1 by rewrite invr_ge0 ltW.
pose sinv : {nonneg R} := NngNum sinv_ge0.
have s_neq0 : s_num != 0 by rewrite gt_eqF.
have s_sinv : s%:num * sinv%:num = 1.
  by rewrite /= mulfV.
have sinv_s : sinv%:num * s%:num = 1.
  by rewrite /= mulVf.
have nng_eq : forall (a b : {nonneg R}), a%:num = b%:num -> a = b.
  by move=> a b /val_inj.
have s_sinv_nng : (s%:num * sinv%:num)%:nng = 1%:nng.
  by apply: nng_eq => /=; exact: s_sinv.
have sinv_s_nng : (sinv%:num * s%:num)%:nng = 1%:nng.
  by apply: nng_eq => /=; exact: sinv_s.
(* The rescaled path [β_unit r := sinv *: β r]. *)
pose β_unit : path_car Ar X B := path_scale sinv β.
have β_unit_norm_le1 : path_norm β_unit <= 1.
  rewrite /β_unit path_normh.
  apply: le_trans (_ : sinv%:num * s_num <= 1); last by rewrite sinv_s.
  apply: ler_wpM2l; first exact: sinv_ge0.
  by rewrite /s_num lerDl.
have β_unit_ptbound : forall r, cone_norm (path_fun β_unit r) <= 1.
  by move=> r; apply: le_trans (path_norm_ub β_unit r) β_unit_norm_le1.
(* The rescaled image chain: integrating [β_unit] against [µn n]. *)
pose int_unit (n : nat) : B :=
  icone_integral (path_fun β_unit) (path_is_path β_unit) (µn n).
have int_unit_E n : int_unit n = precone_scale sinv (int_to_linhom_fun (µn n)).
  rewrite /int_unit /int_to_linhom_fun /β_unit /=.
  exact: icone_integral_scaleB.
have int_unit_chain : forall n, precone_le (int_unit n) (int_unit n.+1).
  move=> n; rewrite (int_unit_E n) (int_unit_E n.+1).
  exact: precone_scale_le (fµn_chain n).
have int_unit_bound : forall n, cone_norm (int_unit n) <= 1.
  move=> n.
  have Hnorm : cone_norm (int_unit n) <= 1 * fmeas_norm (µn n).
    apply: (@path_integral_norm_le _ _ _ _ (path_fun β_unit) _ 1)
                                   β_unit_ptbound
                                   (path_is_path β_unit)
                                   _ (icone_integralP _ _ _).
  apply: le_trans Hnorm _.
  by rewrite mul1r; exact: µn_bound.
(* Apply [integral_omega_cont_meas] on [β_unit] and chain [µn]. The
   lemma uses section-local chain/bound proofs equal to ours up to
   proof irrelevance; we bridge via [precone_le_anti]. *)
have key : cone_sup_ball int_unit int_unit_chain int_unit_bound =
           icone_integral (path_fun β_unit) (path_is_path β_unit)
                          (fmeas_sup_ball µn_chain µn_bound).
  have base := integral_omega_cont_meas
                 (path_is_path β_unit) β_unit_ptbound µn_chain µn_bound.
  (* [base : cone_sup_ball int_µ int_µ_chain int_µ_bound = RHS]. The
     LHS [int_µ] is definitionally [int_unit]; chain/bound proofs are
     swapped via [precone_le_anti]. *)
  set lhs_base := cone_sup_ball _ _ _ in base.
  set lhs_ours := cone_sup_ball int_unit int_unit_chain int_unit_bound.
  have swap : lhs_ours = lhs_base.
    rewrite /lhs_ours /lhs_base.
    apply: precone_le_anti; apply: cone_sup_ball_lub => n;
      exact: cone_sup_ball_ub.
  by rewrite swap.
(* Rewrite the RHS as [precone_scale sinv (int_to_linhom_fun (sup_ball µn))]. *)
have rhs_eq : icone_integral (path_fun β_unit) (path_is_path β_unit)
                             (fmeas_sup_ball µn_chain µn_bound) =
              precone_scale sinv
                (int_to_linhom_fun (fmeas_sup_ball µn_chain µn_bound)).
  rewrite /int_to_linhom_fun /β_unit /=.
  exact: icone_integral_scaleB.
(* Rescale LHS chain via [sup_ball_scaler]. *)
pose sinv_fµn (n : nat) : B := precone_scale sinv (int_to_linhom_fun (µn n)).
have sinv_fµn_E n : int_unit n = sinv_fµn n.
  by rewrite int_unit_E.
have sinv_fµn_chain : forall n,
    precone_le (sinv_fµn n) (sinv_fµn n.+1).
  by move=> n; apply: precone_scale_le (fµn_chain n).
have s_ge1 : 1 <= s_num.
  by rewrite /s_num lerDr; exact: path_norm_ge0.
have sinv_le1 : sinv%:num <= 1.
  by rewrite /= invf_le1 ?s_ge1// s_pos.
have sinv_fµn_bound : forall n,
    cone_norm (sinv_fµn n) <= 1.
  move=> n; rewrite /sinv_fµn cone_normh.
  apply: le_trans
    (ler_pM sinv_ge0 (cone_norm_ge0 _) sinv_le1 (fµn_bound n)) _.
  by rewrite mulr1.
have lhs_swap :
    cone_sup_ball int_unit int_unit_chain int_unit_bound =
    cone_sup_ball sinv_fµn sinv_fµn_chain sinv_fµn_bound.
  apply: precone_le_anti; apply: cone_sup_ball_lub => n.
  - rewrite sinv_fµn_E; exact: cone_sup_ball_ub.
  - rewrite -(sinv_fµn_E n); exact: cone_sup_ball_ub.
(* Apply [sup_ball_scaler] to extract sinv from the LHS sup_ball. *)
have lhs_scaler :
    cone_sup_ball sinv_fµn sinv_fµn_chain sinv_fµn_bound =
    precone_scale sinv
      (cone_sup_ball (int_to_linhom_fun \o µn) fµn_chain fµn_bound).
  exact: (@sup_ball_scaler R B sinv _ fµn_chain fµn_bound).
(* Combine: [sinv * f (sup µn)] = [sinv * (sup f µn)]. Multiply by s. *)
have core :
    precone_scale sinv (int_to_linhom_fun
                          (fmeas_sup_ball µn_chain µn_bound)) =
    precone_scale sinv
      (cone_sup_ball (int_to_linhom_fun \o µn) fµn_chain fµn_bound).
  by rewrite -rhs_eq -key lhs_swap lhs_scaler.
have multiply_s : forall x : B, precone_scale s (precone_scale sinv x) = x.
  by move=> x; rewrite -precone_scale_A s_sinv_nng precone_scale_1.
by rewrite -[LHS]multiply_s core multiply_s.
Qed.

(** ** Kernel-Tonelli identity for [icone_integral β' _ µ'] (paper §6)

    Given a measurable path [β' : ar_carrier Y → fmeas R X] and a
    finite measure [µ' : fmeas R Y], the integrated measure
    [µY := icone_integral β' Hβ' µ'] supports a kernel-Tonelli
    identity for any non-negative measurable integrand
    [g : X → \bar R]:

      [\int[µY] g r = \int[µ'] (\int[β' y] g r) dy].

    We package this by viewing [β'] as a finite kernel
    [Y ~> ar_carrier X] and [µ'] as a finite kernel from the
    [ar_zero] singleton, then invoking [integral_kcomp] from
    mathcomp-analysis. *)

Section KernelTonelli.
Variables (Y : ar_obj Ar) (β' : ar_carrier Ar Y -> fmeas R (ar_carrier Ar X)).
Hypothesis Hβ' : is_measurable_path β'.
Variable µ' : fmeas R (ar_carrier Ar Y).

Local Open Scope ereal_scope.

(** Package [β'] as a finite kernel [Y ~> X] (mathcomp [R.-fker]). *)
Local Definition β'_kfun (y : ar_carrier Ar Y) :
    {measure set (ar_carrier Ar X) -> \bar R} :=
  fmeas_mu (β' y).

Local Lemma β'_kfun_meas U : measurable U ->
  measurable_fun [set: ar_carrier Ar Y] (β'_kfun ^~ U).
Proof. by move=> mU; exact: (fmeas_int_meas_fun Hβ' mU). Qed.

HB.instance Definition _ :=
  isKernel.Build _ _ _ _ R β'_kfun β'_kfun_meas.

Local Lemma β'_kfun_uub : measure_fam_uub β'_kfun.
Proof.
have [[Mβ HMβ] _] := Hβ'.
have HMβge0 : (0 <= Mβ)%R.
  by apply: le_trans (HMβ (ar_point Ar Y)); exact: cone_norm_ge0.
exists (Mβ + 1)%R => y.
have Hfin : fmeas_mu (β' y) [set: ar_carrier Ar X] \is a fin_num.
  exact: fmeas_setT_fin.
rewrite -(fineK Hfin) lte_fin.
apply: (le_lt_trans (HMβ y)).
by rewrite ltrDl.
Qed.

HB.instance Definition _ :=
  Kernel_isFinite.Build _ _ _ _ _ β'_kfun β'_kfun_uub.

(** Repackage [β'] as a kernel from [ar_zero × Y ~> X] by ignoring
    the first coordinate. *)
Local Definition β'_kfun_lift
    (p : ar_carrier Ar (ar_zero Ar) * ar_carrier Ar Y) :
    {measure set (ar_carrier Ar X) -> \bar R} :=
  β'_kfun p.2.

Local Lemma β'_kfun_lift_meas U : measurable U ->
  measurable_fun
    [set: (ar_carrier Ar (ar_zero Ar) * ar_carrier Ar Y)%type]
    (β'_kfun_lift ^~ U).
Proof.
move=> mU.
apply: (measurableT_comp (f := β'_kfun ^~ U)).
- exact: β'_kfun_meas.
- exact: measurable_snd.
Qed.

HB.instance Definition _ :=
  isKernel.Build _ _ _ _ R β'_kfun_lift β'_kfun_lift_meas.

Local Lemma β'_kfun_lift_uub : measure_fam_uub β'_kfun_lift.
Proof. by have [M HM] := β'_kfun_uub; exists M => p; exact: HM. Qed.

HB.instance Definition _ :=
  Kernel_isFinite.Build _ _ _ _ _ β'_kfun_lift β'_kfun_lift_uub.

(** Package [µ'] as a constant kernel from [ar_zero] to [Y]. *)
Local Definition µ'_kfun (_ : ar_carrier Ar (ar_zero Ar)) :
    {measure set (ar_carrier Ar Y) -> \bar R} :=
  fmeas_mu µ'.

Local Lemma µ'_kfun_meas U : measurable U ->
  measurable_fun [set: ar_carrier Ar (ar_zero Ar)] (µ'_kfun ^~ U).
Proof. by move=> _; exact: measurable_cst. Qed.

HB.instance Definition _ :=
  isKernel.Build _ _ _ _ R µ'_kfun µ'_kfun_meas.

Local Lemma µ'_kfun_uub : measure_fam_uub µ'_kfun.
Proof.
exists (fmeas_norm µ' + 1)%R => z.
have Hfin : fmeas_mu µ' [set: ar_carrier Ar Y] \is a fin_num.
  exact: fmeas_setT_fin.
rewrite /µ'_kfun -(fineK Hfin) lte_fin.
by rewrite ltrDl.
Qed.

HB.instance Definition _ :=
  Kernel_isFinite.Build _ _ _ _ _ µ'_kfun µ'_kfun_uub.

(** The Pettis equation identifies [icone_integral β' Hβ' µ'] with
    the kernel-composition measure on every measurable set. *)
Local Lemma icone_integral_set_E U : measurable U ->
  fmeas_mu (icone_integral β' Hβ' µ') U =
  kcomp µ'_kfun β'_kfun_lift (ar_zero_pt Ar) U.
Proof.
move=> mU.
have HµY_pet := icone_integralP β' Hβ' µ'
                  (fmeas_eU (ar_zero Ar) mU)
                  (ex_intro _ U (ex_intro _ mU erefl))
                  (ar_zero_pt Ar).
have HµYUfin : fmeas_mu (icone_integral β' Hβ' µ') U \is a fin_num.
  exact: fmeas_fin.
have intfin :
    \int[fmeas_mu µ']_(y in [set: ar_carrier Ar Y]) fmeas_mu (β' y) U
     \is a fin_num.
  have meas_int :
    measurable_fun [set: ar_carrier Ar Y]
      (fun y => fmeas_mu (β' y) U).
    exact: (fmeas_int_meas_fun Hβ' mU).
  have [[Mβ' HMβ'] _] := Hβ'.
  have Mb_ge0 : (0 <= Mβ')%R.
    by apply: le_trans (HMβ' (ar_point _ _)); exact: cone_norm_ge0.
  have intge0 :
    0 <= \int[fmeas_mu µ']_(y in [set: ar_carrier Ar Y])
            fmeas_mu (β' y) U.
    by apply: integral_ge0 => y _; exact: measure_ge0.
  have intle :
    \int[fmeas_mu µ']_(y in [set: ar_carrier Ar Y])
       fmeas_mu (β' y) U <= Mβ'%:E * fmeas_mu µ' [set: _].
    have -> : Mβ'%:E * fmeas_mu µ' [set: _] =
              \int[fmeas_mu µ']_(y in [set: _]) Mβ'%:E
      by rewrite integral_cst.
    apply: ge0_le_integral.
    - exact: measurableT.
    - by move=> y _; exact: measure_ge0.
    - exact: meas_int.
    - exact: measurable_cst.
    - move=> y _.
      apply: (@le_trans _ _ (fmeas_mu (β' y) [set: ar_carrier Ar X])).
        by apply: le_measure; rewrite ?inE//; exact: measurableT.
      have HfinT : fmeas_mu (β' y) [set: ar_carrier Ar X] \is a fin_num
        by exact: fmeas_setT_fin.
      by rewrite -(fineK HfinT) lee_fin; exact: HMβ' y.
  have HsetTfin : fmeas_mu µ' [set: _] \is a fin_num
    by exact: fmeas_setT_fin.
  rewrite ge0_fin_numE//.
  apply: le_lt_trans intle _.
  by apply: lte_mul_pinfty => //; rewrite ltey_eq HsetTfin.
have HµY_eq : fine (fmeas_mu (icone_integral β' Hβ' µ') U) =
              fine (\int[fmeas_mu µ']_(y in [set: _]) fmeas_mu (β' y) U).
  rewrite [LHS]HµY_pet /fmeas_eU /eU_fun /=.
  congr fine.
  by apply: eq_integral => y _; rewrite fineK//; exact: fmeas_fin.
have -> : kcomp µ'_kfun β'_kfun_lift (ar_zero_pt Ar) U =
          \int[fmeas_mu µ']_(y in [set: ar_carrier Ar Y])
            fmeas_mu (β' y) U by [].
by rewrite -(fineK HµYUfin) -(fineK intfin) HµY_eq.
Qed.

(** Paper Thms 4.5 / 4.15 — kernel-Tonelli identity in
    [fmeas R (ar_carrier Ar X)]. *)
Lemma icone_integral_kernel_tonelli
    (g : ar_carrier Ar X -> \bar R) :
  measurable_fun [set: ar_carrier Ar X] g ->
  (forall r, 0 <= g r) ->
  \int[fmeas_mu (icone_integral β' Hβ' µ')]_(r in [set: ar_carrier Ar X])
    g r =
  \int[fmeas_mu µ']_(y in [set: ar_carrier Ar Y])
    \int[fmeas_mu (β' y)]_(r in [set: ar_carrier Ar X]) g r.
Proof.
move=> gm gge0.
have eq_µY :
    \int[fmeas_mu (icone_integral β' Hβ' µ')]_(r in [set: ar_carrier Ar X])
      g r =
    \int[kcomp µ'_kfun β'_kfun_lift (ar_zero_pt Ar)]_(r in [set:
      ar_carrier Ar X]) g r.
  apply: eq_measure_integral => U mU _; exact: icone_integral_set_E.
rewrite eq_µY.
exact: (integral_kcomp µ'_kfun β'_kfun_lift (ar_zero_pt Ar) (f := g) gge0 gm).
Qed.

End KernelTonelli.

(** Paper Lemma 4.7 + joint measurability: for any measurable path
    [κ : ar_carrier Y -> fmeas R X], the composite
    [r ↦ icone_integral β _ (κ r)] is a measurable path in [B].
    Direct from [icone_integral_joint_measurable] with the
    constant kernel [s ↦ β]. *)
Lemma int_to_linhom_fun_pres_path
    (Y : ar_obj Ar) (κ : ar_carrier Ar Y -> fmeas R (ar_carrier Ar X)) :
  is_measurable_path κ ->
  is_measurable_path (fun r => int_to_linhom_fun (κ r)).
Proof.
move=> Hκ.
have [[Mκ HMκ] Hκj] := Hκ.
have Mκ_ge0 : 0 <= Mκ.
  by apply: le_trans (HMκ (ar_point Ar Y)); exact: cone_norm_ge0.
split.
  exists (path_norm β * Mκ) => r.
  have HnormI : cone_norm (icone_integral βf Hβ (κ r))
                  <= path_norm β * fmeas_norm (κ r).
    apply: (path_integral_norm_le (Mβ := path_norm β)).
    - move=> r'; exact: path_norm_ub.
    - exact: Hβ.
    - exact: icone_integralP.
  apply: le_trans HnormI _.
  apply: ler_wpM2l; [exact: path_norm_ge0|].
  exact: HMκ.
move=> Z m mM.
(* The function [(s, r) ↦ test m s (icone_integral β _ (κ r))]
   is jointly measurable by [icone_integral_joint_measurable]
   with the constant kernel of paths [s ↦ β]. *)
pose βconst : ar_carrier Ar Y -> ar_carrier Ar X -> B := fun _ r => βf r.
have Hβconst : forall s, is_measurable_path (βconst s).
  by move=> s; exact: Hβ.
have κ_meas_perU : forall U, measurable U ->
  measurable_fun [set: ar_carrier Ar Y] (fun s => fmeas_mu (κ s) U).
  move=> U mU.
  have mM_U : mcone_M (Ar:=Ar) (ar_zero Ar)
    (fmeas_eU (ar_zero Ar) mU).
    by exists U, mU.
  have HmU_joint := Hκj _ _ mM_U.
  have meas_fine :
    measurable_fun [set: ar_carrier Ar Y]
      (fun s => fine (fmeas_mu (κ s) U)).
    pose F (p : ar_carrier Ar (ar_zero Ar) * ar_carrier Ar Y) : R :=
      test_fun (fmeas_eU (ar_zero Ar) mU) p.1 (κ p.2).
    have HF : measurable_fun
      [set: (ar_carrier Ar (ar_zero Ar) * ar_carrier Ar Y)%type] F.
      exact: HmU_joint.
    have -> : (fun s => fine (fmeas_mu (κ s) U)) =
              (fun s => F (ar_zero_pt Ar, s)).
      by apply: funext.
    by apply: (measurableT_comp (f := F)).
  have rewE : (fun s => fmeas_mu (κ s) U) =
              (fun s => (fine (fmeas_mu (κ s) U))%:E).
    apply: funext => s; rewrite fineK//; exact: fmeas_fin.
  by rewrite rewE; apply/measurable_EFinP.
have κ_bound : exists M : R, forall s, (fmeas_norm (κ s) <= M)%R.
  by exists Mκ.
have HjointConst :
  measurable_fun
    [set: (ar_carrier Ar Z * (ar_carrier Ar Y * ar_carrier Ar X))%type]
    (fun p => test_fun m p.1 (βconst p.2.1 p.2.2)).
  rewrite /βconst.
  have [_ Hβj] := Hβ.
  have Hβj' := Hβj Z m mM.
  pose ψ (q : (ar_carrier Ar Z *
              (ar_carrier Ar Y * ar_carrier Ar X))%type) :
    ar_carrier Ar Z * ar_carrier Ar X :=
    (q.1, q.2.2).
  have ψ_meas : measurable_fun
    [set: (ar_carrier Ar Z * (ar_carrier Ar Y * ar_carrier Ar X))%type] ψ.
    apply: measurable_fun_pair; first exact: measurable_fst.
    by apply: (measurableT_comp (f := snd));
      [exact: measurable_snd|exact: measurable_snd].
  have -> : (fun q : (ar_carrier Ar Z *
                     (ar_carrier Ar Y * ar_carrier Ar X))%type =>
             test_fun m q.1 (βf q.2.2)) =
            (fun p : ar_carrier Ar Z * ar_carrier Ar X =>
             test_fun m p.1 (βf p.2)) \o ψ.
    by apply: funext.
  exact: (measurableT_comp Hβj' ψ_meas).
have Mβ_bd : exists M : R, forall z s r,
    (test_fun m z (βconst s r) <= M)%R.
  exists (path_norm β) => z s r; rewrite /βconst.
  apply: le_trans (test_norm_le _ _ _) _.
  exact: path_norm_ub.
have main :=
  @icone_integral_joint_measurable R Ar B X _ _ βconst Hβconst κ Z m mM
    κ_meas_perU κ_bound HjointConst Mβ_bd.
apply: (eq_measurable_fun _ _ main).
move=> p _.
rewrite /int_to_linhom_fun.
congr (test_fun m p.1 _).
(* βconst p.2 = βf as functions; by uniqueness of icone_integral. *)
apply/esym/icone_integral_eqP; exact: icone_integralP.
Qed.

(** ** Paper Thm 6.1 — integral preservation in [µ] for [int_to_linhom_fun β]

    For any measurable path [β' : Y → fmeas R X] and finite measure
    [µ' : fmeas R Y]:

      [int_to_linhom_fun β (icone_integral β' Hβ' µ')
         = icone_integral (fun y => int_to_linhom_fun β (β' y))
                          (int_to_linhom_fun_pres_path β' Hβ') µ'].

    Proof: by uniqueness of the integral on [B] ([icone_integral_eqP]),
    show that the RHS satisfies the Pettis equation
    [path_integral_eq βf (icone_integral β' Hβ' µ') (RHS)].  Test
    against any [m ∈ M_{ar_zero}] using [icone_integralP] on both
    levels and the kernel-Tonelli identity
    [icone_integral_kernel_tonelli] to swap the integration order. *)
Lemma int_to_linhom_fun_pres_int
    (Y : ar_obj Ar) (β' : ar_carrier Ar Y -> fmeas R (ar_carrier Ar X))
    (Hβ' : is_measurable_path β')
    (µ' : fmeas R (ar_carrier Ar Y)) :
  int_to_linhom_fun (icone_integral β' Hβ' µ') =
  icone_integral
    (fun r => int_to_linhom_fun (β' r))
    (int_to_linhom_fun_pres_path Hβ') µ'.
Proof.
rewrite /int_to_linhom_fun.
apply/esym/icone_integral_eqP => m mM s.
(* RHS = m s (icone_integral γ_path Hγ µ'). Expand via icone_integralP. *)
rewrite (icone_integralP _ _ µ' m mM s).
(* Inside the µ'-integral, expand test of [int_to_linhom_fun β (β' y)]
   via icone_integralP on β' y. *)
have test_inner y :
    test_fun m s (icone_integral βf Hβ (β' y)) =
    fine (\int[fmeas_mu (β' y)]_(r in [set: ar_carrier Ar X])
            (test_fun m s (βf r))%:E)%E.
  exact: icone_integralP.
(* Tonelli swap via [icone_integral_kernel_tonelli]. *)
pose f0 : ar_carrier Ar X -> \bar R :=
  fun r => (test_fun m s (βf r))%:E.
have f0_meas : measurable_fun [set: ar_carrier Ar X] f0.
  rewrite /f0.
  by apply/measurable_EFinP; exact: (measurable_test_path_section mM Hβ).
have f0_ge0 r : (0 <= f0 r)%E by rewrite /f0 lee_fin; apply: test_ge0.
have tonelli := icone_integral_kernel_tonelli Hβ' µ' f0_meas f0_ge0.
(* Rewrite the outer integrand: replace [test_fun m s (γ_path r)]
   by the inner-integral form, then drop the [fine ∘ (_%:E)] via [fineK]. *)
have inner_fin y :
    (\int[fmeas_mu (β' y)]_(r in [set: _]) f0 r \is a fin_num)%E.
  have HfinT : (fmeas_mu (β' y) [set: _] \is a fin_num)%E
    by exact: fmeas_setT_fin.
  have intge0 :
    (0 <= \int[fmeas_mu (β' y)]_(r in [set: _]) f0 r)%E
    by apply: integral_ge0 => r _; exact: f0_ge0.
  have ub :
    (\int[fmeas_mu (β' y)]_(r in [set: _]) f0 r <=
       (path_norm β)%:E * fmeas_mu (β' y) [set: _])%E.
    have -> : ((path_norm β)%:E * fmeas_mu (β' y) [set: _])%E =
              (\int[fmeas_mu (β' y)]_(r in [set: _]) (path_norm β)%:E)%E
      by rewrite integral_cst.
    apply: ge0_le_integral.
    - exact: measurableT.
    - by move=> r _; exact: f0_ge0.
    - exact: f0_meas.
    - exact: measurable_cst.
    - move=> r _; rewrite /f0 lee_fin.
      apply: le_trans (test_norm_le _ _ _) _; exact: path_norm_ub.
  rewrite ge0_fin_numE//.
  apply: le_lt_trans ub _.
  apply: lte_mul_pinfty => //.
  - exact: path_norm_ge0.
  - by rewrite ltey_eq HfinT.
have rewE :
    (\int[fmeas_mu µ']_(y in [set: ar_carrier Ar Y])
       (test_fun m s (int_to_linhom_fun (β' y)))%:E =
     \int[fmeas_mu µ']_(y in [set: ar_carrier Ar Y])
       \int[fmeas_mu (β' y)]_(r in [set: _]) f0 r)%E.
  apply: eq_integral => y _.
  rewrite /int_to_linhom_fun (test_inner y).
  by rewrite fineK//.
rewrite rewE.
by rewrite -tonelli.
Qed.

End IntToLinhomFun.

Arguments int_to_linhom_fun {R Ar X B} β.
Arguments int_to_linhom_fun_linear {R Ar X B} β.
Arguments int_to_linhom_fun_bounded {R Ar X B} β.
Arguments int_to_linhom_fun_continuous {R Ar X B} β.
Arguments int_to_linhom_fun_pres_path {R Ar X B} β {Y κ}.
Arguments int_to_linhom_fun_pres_int {R Ar X B} β {Y β'} Hβ' µ'.

(** ** Paper Thm 6.1 forward direction — [int_to_linhom β : linhom_car _]

    With all five [linhom_car] fields proved, package
    [int_to_linhom_fun β] as a [linhom_car Ar (fmeas R X) B]. *)

Section IntToLinhom.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (X : ar_obj Ar) (B : ICone.type Ar).
Variable β : path_car Ar X B.

(** The [linhom_pre] structure carries the function, linearity,
    ω-continuity, boundedness, and path-preservation. *)
Definition int_to_linhom_pre :
    linhom_pre Ar (fmeas R (ar_carrier Ar X)) B :=
  MkLinhomPre (int_to_linhom_fun β)
    (int_to_linhom_fun_linear β)
    (int_to_linhom_fun_continuous β)
    (int_to_linhom_fun_bounded β)
    (fun Y κ => int_to_linhom_fun_pres_path β (κ:=κ)).

(** The [linhom_car] structure adds integral preservation. *)
Definition int_to_linhom :
    linhom_car Ar (fmeas R (ar_carrier Ar X)) B :=
  MkLinhom int_to_linhom_pre
    (fun Y β' Hβ' µ' => int_to_linhom_fun_pres_int β Hβ' µ').

End IntToLinhom.

Arguments int_to_linhom_pre {R Ar X B} β.
Arguments int_to_linhom {R Ar X B} β.

(** ** Paper Thm 6.1 inverse direction — [linhom_to_int f]

    For [f : linhom_car Ar (fmeas R (ar_carrier Ar X)) B], the
    inverse path is [r ↦ linhom_fun f (dirac_fmeas r)]. *)

Section LinhomToInt.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (X : ar_obj Ar) (B : ICone.type Ar).
Variable f : linhom_car Ar (fmeas R (ar_carrier Ar X)) B.

(** Paper §6, post-Thm 6.1: the underlying function of [K^B_X(f)]. *)
Definition linhom_to_int_fun : ar_carrier Ar X -> B :=
  fun r => linhom_fun f (dirac_fmeas r).

(** Boundedness of [linhom_to_int_fun]: each value is the image of
    a unit-norm measure, so it is bounded by the operator-norm
    [linhom_norm f]. *)
Lemma linhom_to_int_fun_norm_bound r :
  cone_norm (linhom_to_int_fun r) <= linhom_norm f.
Proof.
rewrite /linhom_to_int_fun.
apply: le_trans (linhom_norm_apply_le (lexx _) (dirac_fmeas r)) _.
by rewrite dirac_fmeas_norm mulr1.
Qed.

(** Paper §6 lines 2952–2968: [r ↦ linhom_fun f (\d_r)] is a
    measurable path. The argument is: precompose [δ_X] (a
    measurable path of [fmeas]) with [f] (a measurable-path-
    preserving map). *)
Lemma linhom_to_int_fun_is_path : is_measurable_path linhom_to_int_fun.
Proof.
have Hδ := @dirac_fmeas_is_path R Ar X.
have Hf := linhom_pre_pres_path (linhom_pre_of f) X dirac_fmeas Hδ.
exact: Hf.
Qed.

(** Paper §6 lines 2952–2968: [K^B_X(f)] as a [path_car]. *)
Definition linhom_to_int : path_car Ar X B :=
  MkPath linhom_to_int_fun_is_path.

(** Compute: [linhom_to_int f r = f (\d_r)]. *)
Lemma linhom_to_int_E (r : ar_carrier Ar X) :
  path_fun linhom_to_int r = linhom_fun f (dirac_fmeas r).
Proof. by []. Qed.

End LinhomToInt.

Arguments linhom_to_int_fun {R Ar X B} f.
Arguments linhom_to_int {R Ar X B} f.

(** ** Paper Thm 6.1 — round-trip identity [K ∘ I = id]

    For [β ∈ Path(X, B)] and [r ∈ X],
    [linhom_to_int (int_to_linhom β) r = int_to_linhom_fun β (\d_r)
                                       = icone_integral β _ (\d_r) = β r].

    The last equality uses [integral_dirac], packaged as the
    Pettis-uniqueness verification below. We deliver this at the
    function level rather than via a full [linhom_car]-valued
    [int_to_linhom], because the latter requires deferred fields.
    The key arithmetic identity is captured by
    [int_to_linhom_fun_dirac]. *)

Section RoundTripKI.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (X : ar_obj Ar) (B : ICone.type Ar).
Variable β : path_car Ar X B.

Local Notation Hβ := (path_is_path β).
Local Notation βf := (path_fun β).

(** Paper Thm 6.1: integrating any measurable path of [B] against
    a Dirac mass returns the integrand. *)
Lemma int_to_linhom_fun_dirac (r : ar_carrier Ar X) :
  int_to_linhom_fun β (dirac_fmeas r) = βf r.
Proof.
rewrite /int_to_linhom_fun.
apply/esym/icone_integral_eqP => m mM s.
(* test_fun m s (β r) = fine (∫[\d_r] (test_fun m s (β r'))%:E dr'). *)
have meas_test : measurable_fun [set: ar_carrier Ar X]
                   (fun r' => (test_fun m s (βf r'))%:E).
  apply/measurable_EFinP.
  exact: (measurable_test_path_section mM Hβ).
have rT : [set: ar_carrier Ar X] r by [].
(* Step 1: [(dirac_fmeas r) U = \d_r U] for measurable U, so the
   integral agrees. *)
have integral_eq :
    (\int[fmeas_mu (dirac_fmeas r)]_(r' in [set: ar_carrier Ar X])
       (test_fun m s (βf r'))%:E)%E =
    (\int[\d_r]_(r' in [set: ar_carrier Ar X])
       (test_fun m s (βf r'))%:E)%E.
  apply: eq_measure_integral => U mU _.
  by rewrite dirac_fmeas_E.
(* Step 2: [∫[\d_r]_(r' in setT) g r' = \d_r setT * g r = g r]. *)
have dirac_int :
    (\int[\d_r]_(r' in [set: ar_carrier Ar X])
       (test_fun m s (βf r'))%:E)%E =
    (test_fun m s (βf r))%:E.
  rewrite integral_dirac//.
  by rewrite diracT mul1e.
by rewrite integral_eq dirac_int.
Qed.

(** Paper Thm 6.1: round-trip [K ∘ I = id]. At the function level:
    [linhom_to_int_fun (int_to_linhom_fun β as a linhom) r = β r].
    We deliver this via [int_to_linhom_fun_dirac] above; a full
    statement at the [path_car] level requires promoting
    [int_to_linhom_fun β] to a [linhom_car], which is deferred. *)
Lemma K_int_to_linhom_E (r : ar_carrier Ar X) :
  int_to_linhom_fun β (dirac_fmeas r) = βf r.
Proof. exact: int_to_linhom_fun_dirac. Qed.

(** Paper Thm 6.1: round-trip [K ∘ I = id] at the [path_car] level.
    With [int_to_linhom β] fully packaged as a [linhom_car], this
    statement reads [linhom_to_int (int_to_linhom β) = β]. *)
Lemma K_I_int_to_linhom_path_E :
  linhom_to_int (int_to_linhom β) = β.
Proof.
apply: path_eq => r /=.
by rewrite /linhom_to_int_fun /linhom_fun /=; exact: K_int_to_linhom_E.
Qed.

End RoundTripKI.

Arguments int_to_linhom_fun_dirac {R Ar X B} β r.
Arguments K_int_to_linhom_E {R Ar X B} β r.
Arguments K_I_int_to_linhom_path_E {R Ar X B} β.

(** ** Paper Thm 6.1 — Dirac approximation of finite measures

    Every finite measure equals the integral of its Diracs:
    [µ = icone_integral dirac_path Hδ µ] in [fmeas R X].

    Proof: by [fmeas_eq], check on every measurable set [U].  Both
    sides agree on [U] via the Pettis equation against [fmeas_eU U],
    using [integral_dirac] inside the integrand. *)
Section DiracApprox.
Variables (R : realType) (Ar : MeasSubcat R).
Variable X : ar_obj Ar.

Lemma icone_integral_dirac_path (µ : fmeas R (ar_carrier Ar X)) :
  icone_integral (dirac_path Ar X)
                 (path_is_path (dirac_path Ar X)) µ =
  µ.
Proof.
apply: fmeas_eq => U mU.
have HU_pet :=
  icone_integralP (dirac_path Ar X)
                  (path_is_path (dirac_path Ar X)) µ
                  (fmeas_eU (ar_zero Ar) mU)
                  (ex_intro _ U (ex_intro _ mU erefl))
                  (ar_zero_pt Ar).
rewrite /fmeas_eU /eU_fun /= in HU_pet.
have Hfin_lhs :
  (fmeas_mu (icone_integral (dirac_path Ar X)
                            (path_is_path (dirac_path Ar X)) µ) U
   \is a fin_num)%E.
  exact: fmeas_fin.
have Hfin_int :
  (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X])
     (fine (fmeas_mu (dirac_fmeas r) U))%:E \is a fin_num)%E.
  have intge0 :
    (0 <= \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X])
            (fine (fmeas_mu (dirac_fmeas r) U))%:E)%E.
    apply: integral_ge0 => r _.
    rewrite lee_fin -lee_fin fineK; first exact: measure_ge0.
    exact: fmeas_fin.
  have intle :
    (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X])
       (fine (fmeas_mu (dirac_fmeas r) U))%:E <= fmeas_mu µ [set: _])%E.
    have -> : (fmeas_mu µ [set: _])%E =
              (\int[fmeas_mu µ]_(r in [set: _]) 1%:E)%E
      by rewrite integral_cst//= mul1e.
    have mf_dirac :
      measurable_fun [set: ar_carrier Ar X]
        (fun r => (fine (fmeas_mu (dirac_fmeas r) U))%:E).
      apply/measurable_EFinP; apply: (measurableT_comp (f := fine)).
        exact: fine_measurable.
      by apply: (fmeas_int_meas_fun
                   (path_is_path (dirac_path Ar X)) mU).
    apply: ge0_le_integral; rewrite ?measurableT//=.
    - move=> r _; rewrite lee_fin.
      have HfinD : (fmeas_mu (dirac_fmeas r) U \is a fin_num)%E
        by exact: fmeas_fin.
      by rewrite -lee_fin fineK//; exact: measure_ge0.
    - move=> r _; rewrite lee_fin.
      have HfinD : (fmeas_mu (dirac_fmeas r) U \is a fin_num)%E
        by exact: fmeas_fin.
      rewrite -lee_fin fineK//.
      have -> : (dirac_canon_fun r U = \d_r U :> \bar R)%E
        by exact: dirac_canon_funE.
      rewrite diracE.
      by case: (r \in U); rewrite ?ler01 ?lexx.
  rewrite ge0_fin_numE//.
  apply: le_lt_trans intle _.
  by rewrite ltey_eq fmeas_setT_fin.
have HfinU : (fmeas_mu µ U \is a fin_num)%E by exact: fmeas_fin.
rewrite -(fineK Hfin_lhs) HU_pet.
(* The integrand [fine (dirac_canon_fun r U)] equals [\1_U r]. *)
have step1 :
    (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X])
       (fine (dirac_canon_fun r U))%:E =
     \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X])
       (numfun.indic U r)%:E)%E.
  apply: eq_integral => r _.
  have -> : (dirac_canon_fun r U = \d_r U :> \bar R)%E
    by exact: dirac_canon_funE.
  by rewrite diracE /numfun.indic; case: (r \in U).
rewrite step1 integral_indic ?setIT//.
by rewrite fineK.
Qed.

End DiracApprox.

Arguments icone_integral_dirac_path {R Ar X} µ.

(** ** Paper Thm 6.1 — round-trip identity [I ∘ K = id]

    For [f : linhom_car Ar (fmeas R X) B]:

      [int_to_linhom (linhom_to_int f) = f].

    Proof: by [linhom_eq] (extensionality), check pointwise:

      [int_to_linhom_fun (linhom_to_int f) µ
         = icone_integral (r ↦ f (dirac_fmeas r)) _ µ      (definition)
         = f (icone_integral dirac_path _ µ)                (linhom_pres_int f)
         = f µ                                              (Dirac approximation)]
*)
Section RoundTripIK.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (X : ar_obj Ar) (B : ICone.type Ar).
Variable f : linhom_car Ar (fmeas R (ar_carrier Ar X)) B.

Lemma I_K_int_to_linhom_E : int_to_linhom (linhom_to_int f) = f.
Proof.
apply: linhom_eq => µ.
have Hδ : is_measurable_path (dirac_fmeas (R:=R) (Ar:=Ar) (X:=X))
  := dirac_fmeas_is_path X.
(* LHS expansion: [int_to_linhom_fun (linhom_to_int f) µ] is by
   definition [icone_integral (fun r => f (dirac_fmeas r)) Hpath µ]
   for some [Hpath]; by uniqueness it agrees with any chosen Hpath. *)
have LHS_E :
    linhom_fun (int_to_linhom (linhom_to_int f)) µ =
    icone_integral (fun r => linhom_fun f (dirac_fmeas r))
                   (linhom_pre_pres_path (linhom_pre_of f) X
                      dirac_fmeas Hδ) µ.
  apply: icone_integral_eqP; exact: icone_integralP.
rewrite LHS_E.
(* By linhom_pres_int f applied to [dirac_path X] and µ. *)
have step :
    linhom_fun f (icone_integral dirac_fmeas Hδ µ) =
    icone_integral
      (fun r => linhom_fun f (dirac_fmeas r))
      (linhom_pre_pres_path (linhom_pre_of f) X dirac_fmeas Hδ) µ.
  exact: (linhom_pres_int f).
rewrite -step.
have Heq : icone_integral dirac_fmeas Hδ µ = µ.
  have Heq0 := icone_integral_dirac_path (X:=X) µ.
  rewrite /dirac_path /= in Heq0.
  by apply: (eq_trans _ Heq0); congr (icone_integral _ _ _);
     exact: Prop_irrelevance.
by rewrite Heq.
Qed.

End RoundTripIK.

Arguments I_K_int_to_linhom_E {R Ar X B} f.

(** ** Sanity checks — paper Thm 6.1 wave 2 deliverables *)

Section BilinSanityCheck.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (X : ar_obj Ar) (B : ICone.type Ar).

(** [dirac_path] is a measurable path of [fmeas]. *)
Check (dirac_path Ar X :
  path_car Ar X (fmeas R (ar_carrier Ar X))).

(** [int_to_linhom] is the full forward map, a [linhom_car]. *)
Check (fun β : path_car Ar X B =>
  int_to_linhom β : linhom_car Ar (fmeas R (ar_carrier Ar X)) B).

(** [linhom_to_int] is the inverse map, a [path_car]. *)
Check (fun f : linhom_car Ar (fmeas R (ar_carrier Ar X)) B =>
  linhom_to_int f : path_car Ar X B).

(** Paper Thm 6.1: round-trip [K ∘ I = id] at the path_car level. *)
Check (fun β : path_car Ar X B =>
  K_I_int_to_linhom_path_E β :
    linhom_to_int (int_to_linhom β) = β).

(** Paper Thm 6.1: round-trip [I ∘ K = id] at the linhom_car level. *)
Check (fun f : linhom_car Ar (fmeas R (ar_carrier Ar X)) B =>
  I_K_int_to_linhom_E f :
    int_to_linhom (linhom_to_int f) = f).

End BilinSanityCheck.
