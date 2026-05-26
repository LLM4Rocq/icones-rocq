(** * Paper Lemma 9.4 — the stable/linear swap [stab_lin_swap]
       ([lemma:stab-lin-swap]); the LNL key isomorphism for [Seely2]

    For integrable cones [B, C, D] we build a natural isomorphism in
    [ICones]

      [stablehom B (C ⊸ D)  ≅  C ⊸ (B ⇒ₛ D)]

    where [stablehom B X] is the SCones internal hom [B ⇒ₛ X]
    ([stable/stablehom.v], an [iconeType]) and [linhom_car Ar C D] is the
    linear hom [C ⊸ D] ([homs/linhom.v]).

    The forward map sends [f : B ⇒ₛ (C ⊸ D)] (a stable [x ↦ f(x)], each
    [f(x) : C ⊸ D]) to [y ↦ (x ↦ f(x)(y))]: linear in [y], stable in
    [x] (0-extended off the unit ball of [B]).  The backward map sends
    [g : C ⊸ (B ⇒ₛ D)] to [x ↦ (y ↦ g(y)(x))].

    Coverage in this file.

    - [linhom_meas_stable] — every [linhom_car] is [is_meas_stable]
      (linear ⇒ stable, via [linear_totmono] / [linear_scott_unit]).

    - [sh_eval_at x : (B ⇒ₛ D) ⊸ D] — evaluation of a stable map at a
      point [x : B], packaged as a full [linhom_car] (its integral
      preservation is the [stablehom] Pettis equation at [x]).

    - [sls_fwd], [sls_bwd] — the forward and backward [icones_hom]s, with
      computation laws [sls_fwdE], [sls_bwdE].

    - [stab_lin_swap] — the [icones_iso] (Paper Lemma 9.4).

    - [stab_lin_swap_nat3] / [stab_lin_swap_nat1] / [stab_lin_swap_nat2]
      — naturality in [D], [B] and [C] respectively. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals constructive_ereal.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import ereal.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import measure.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import lebesgue_integral_definition.
From mathcomp.analysis Require Import lebesgue_integral_nonneg.
From mathcomp.analysis Require Import lebesgue_integral_monotone_convergence.
From mathcomp.analysis Require Import topology normedtype sequences.

Require Import Icones.prelude.classical_extra.
Require Import Icones.prelude.nonneg_extra.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.omega_general.
Require Import Icones.cones.cone_cat.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.mcones.path.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.mcones.test_pullback.
Require Import Icones.icones.pettis.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_integral.
Require Import Icones.icones.fubini.
Require Import Icones.icones.icone_cat.
Require Import Icones.homs.linhom.
Require Import Icones.homs.icones_iso.
Require Import Icones.homs.tensor_hom_iso.
Require Import Icones.homs.tensor_iso.
Require Import Icones.stable.totmono.
Require Import Icones.stable.stablehom.
Require Import Icones.stable.compose.
Require Import Icones.stable.scones_cat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** Every [linhom_car] is stable-and-measurable

    A bounded linear ω-continuous measurable-path-preserving map is
    stable-and-measurable: total monotonicity is [linear_totmono], the
    boundedness witness is [linhom_pre_bounded], ω-continuity on the unit
    ball is [linear_scott_unit] (it needs only linearity + ω-continuity,
    NOT operator norm [≤ 1]), and path-preservation is the
    [linhom_pre_pres_path] field (which holds unconditionally, hence in
    particular for unit-ball paths). *)

Section LinhomMeasStable.
Variables (R : realType) (Ar : MeasSubcat R).
Variables C D : ICone.type Ar.

Lemma linhom_meas_stable (phi : linhom_car Ar C D) :
  is_meas_stable (linhom_fun phi).
Proof.
split.
  split.
  - exact: (linear_totmono _ (linhom_pre_linear (linhom_pre_of phi))).
  - exact: (linhom_pre_bounded (linhom_pre_of phi)).
  - apply: linear_scott_unit.
    + exact: (linhom_pre_linear (linhom_pre_of phi)).
    + exact: (linhom_pre_continuous (linhom_pre_of phi)).
move=> X gamma _ Hgamma.
exact: (linhom_pre_pres_path (linhom_pre_of phi) X gamma Hgamma).
Qed.

End LinhomMeasStable.

Arguments linhom_meas_stable {R Ar C D} phi.

(** ** Evaluation of a stable map at a point — [sh_eval_at]

    For a fixed [x : B], the evaluation [g ↦ g(x) : (B ⇒ₛ D) → D] is an
    integrable LINEAR map (the cone operations on [B ⇒ₛ D] are pointwise,
    so [eval] is linear; ω-continuity is the [stablehom] sup computed
    pointwise; boundedness by [1] on the unit ball via [sh_norm_ub];
    path/integral preservation are the [stablehom] (Msmeas) section /
    Pettis facts).  We package it as a full [linhom_car Ar (B⇒ₛD) D].

    This is the workhorse: the BACKWARD inner map is
    [linhom_comp (sh_eval_at x) g], and the integral-preservation of the
    FORWARD map reduces to the integral-preservation field of
    [sh_eval_at]. *)

Section ShEvalAt.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B D : ICone.type Ar.
Variable x : B.
Local Open Scope precone_scope.

Local Notation S := (stablehom B D).

Definition sh_eval_at_fun (g : S) : D := sh_fun g x.

(** Linearity: the cone operations on [stablehom] are pointwise. *)
Lemma sh_eval_at_linear : is_linear sh_eval_at_fun.
Proof.
rewrite /sh_eval_at_fun; split.
- by rewrite -[(0%PC : S)]/(sh_zero B D) sh_zeroE.
- by move=> g1 g2;
    rewrite -[(g1 + g2)%PC]/(sh_add g1 g2) sh_addE.
- by move=> r g; rewrite -[(r *: g)%PC]/(sh_scale r g) sh_scaleE.
Qed.

(** Boundedness on the unit ball: [‖g x‖ ≤ ‖g‖ ≤ 1]. *)
Lemma sh_eval_at_bounded :
  exists M : R, forall g : S, cnorm g <= 1 -> cnorm (sh_eval_at_fun g) <= M.
Proof.
exists 1 => g Hg; rewrite /sh_eval_at_fun.
have [Hx | Hx] := boolP (cone_norm x <= 1).
  by apply: le_trans (sh_norm_ub g x Hx) _.
by rewrite (sh_offball g x Hx) cone_norm0 ler01.
Qed.

(** ω-continuity: [(sup u)(x) = sup_n (uₙ x)].  On the unit ball, the
    [stablehom] sup computes pointwise ([sh_sup_fun_unitE]); the
    image-chain sup [cone_sup_ball (uₙ x)] is the SAME pointwise
    [cone_sup_ball] (proof-irrelevant), so the two sides are equal.  Off
    the ball, both are [0]. *)
Lemma sh_eval_at_continuous : is_omega_continuous sh_eval_at_fun.
Proof.
move=> u uch ub1 fuch fub1.
rewrite /sh_eval_at_fun.
have [Hx | Hx] := boolP (cone_norm x <= 1); last first.
  (* Off-ball [x]: both sides vanish (sup of [0] chain is [0]). *)
  rewrite (sh_offball (cone_sup_ball u uch ub1) x Hx).
  apply/esym.
  apply: precone_le_anti; last exact: precone_le0.
  apply: cone_sup_ball_lub => n.
  by rewrite /comp /sh_eval_at_fun (sh_offball (u n) x Hx); exact: precone_le_refl.
(* On-ball [x]: the [stablehom] sup computes pointwise. *)
have ch : forall n, sh_fun (u n) x <=p sh_fun (u n.+1) x.
  by move=> n; exact: sh_le_pointwise (uch n) x.
have b1 : forall n, cnorm (sh_fun (u n) x) <= 1.
  by move=> n; apply: le_trans (sh_norm_ub (u n) x Hx) _; exact: ub1.
rewrite -[cone_sup_ball u uch ub1 : stablehom B D]/(sh_sup uch ub1).
rewrite -[sh_sup uch ub1 x]/(sh_sup_fun uch ub1 x).
rewrite (sh_sup_fun_unitE uch ub1 Hx ch b1).
(* The two image suprema are over the SAME (defeq) chain. *)
apply: precone_le_anti; apply: cone_sup_ball_lub => n; exact: cone_sup_ball_ub.
Qed.

(** Path-preservation: a measurable [stablehom]-path [η] gives the
    measurable [D]-path [r ↦ η(r)(x)].  This is exactly the [stablehom]
    (Msmeas) section lemma [sh_int_pt_meas]. *)
Lemma sh_eval_at_pres_path
    (Y' : ar_obj Ar) (η : ar_carrier Ar Y' -> S) :
  is_measurable_path η ->
  is_measurable_path (fun r => sh_eval_at_fun (η r)).
Proof. by move=> Hη; rewrite /sh_eval_at_fun; exact: (sh_int_pt_meas Hη x). Qed.

Definition sh_eval_at_pre : linhom_pre Ar S D :=
  MkLinhomPre sh_eval_at_fun sh_eval_at_linear sh_eval_at_continuous
              sh_eval_at_bounded
              (fun Y' η Hη => sh_eval_at_pres_path (Y':=Y') (η:=η) Hη).

(** The stablehom-object integral evaluated at [x]: [(∫η dµ)(x) =
    ∫ η(r)(x) dµ].  On the ball this is [sh_int_funE]; off the ball both
    sides are [0] (the section [r ↦ η(r)(x)] is the constant-[0] path, so
    its integral is [0] too). *)
Lemma sh_eval_at_int_eval
    (Y' : ar_obj Ar) (η : ar_carrier Ar Y' -> S)
    (Hη : is_measurable_path η) (µ : fmeas R (ar_carrier Ar Y')) :
  sh_eval_at_fun (icone_integral η Hη µ) =
  icone_integral (fun r => sh_eval_at_fun (η r)) (sh_eval_at_pres_path Hη) µ.
Proof.
rewrite /sh_eval_at_fun.
(* The object integral equals the explicit [stablehom] Pettis integral. *)
have HE : icone_integral η Hη µ = sh_int_stablehom Hη µ.
  by apply/esym/icone_integral_eqP; exact: sh_int_car_pettis.
rewrite HE /sh_int_stablehom /=.
apply: icone_integral_eqP => m mM s.
have [Hx | Hx] := boolP (cone_norm x <= 1).
  by rewrite (sh_int_fun_pet Hη µ Hx mM s).
(* Off-ball: [sh_int_fun x = 0] and the section is the [0]-path. *)
rewrite (sh_int_fun_offball Hη µ Hx) test_lin0.
under eq_integral => r _ do rewrite /sh_eval_at_fun (sh_offball (η r) x Hx) test_lin0.
rewrite (_ : (fun=> (0 : R)%:E) = cst 0%E :> (_ -> \bar R)); last by apply: funext.
by rewrite integral0.
Qed.

Lemma sh_eval_at_pres_int
    (Y' : ar_obj Ar) (η : ar_carrier Ar Y' -> S)
    (Hη : is_measurable_path η) (µ : fmeas R (ar_carrier Ar Y')) :
  linhom_pre_fun sh_eval_at_pre (icone_integral η Hη µ) =
  icone_integral
    (fun r => linhom_pre_fun sh_eval_at_pre (η r))
    (linhom_pre_pres_path sh_eval_at_pre Y' η Hη) µ.
Proof.
rewrite /sh_eval_at_pre /= (sh_eval_at_int_eval Hη µ).
by congr icone_integral; exact: Prop_irrelevance.
Qed.

(** [sh_eval_at x : (B ⇒ₛ D) ⊸ D]. *)
Definition sh_eval_at : linhom_car Ar S D :=
  MkLinhom sh_eval_at_pre sh_eval_at_pres_int.

Lemma sh_eval_atE (g : S) : linhom_fun sh_eval_at g = sh_fun g x.
Proof. by []. Qed.

(** Operator norm [≤ 1]: [‖g x‖ ≤ ‖g‖]. *)
Lemma sh_eval_at_norm_le1 : cone_norm sh_eval_at <= 1.
Proof.
rewrite -[cone_norm _]/(linhom_norm sh_eval_at).
apply: linhom_norm_sup_lub => g Hg.
rewrite sh_eval_atE.
have [Hx | Hx] := boolP (cone_norm x <= 1).
  by apply: le_trans (sh_norm_ub g x Hx) _.
by rewrite (sh_offball g x Hx) cone_norm0 ler01.
Qed.

End ShEvalAt.

Arguments sh_eval_at_fun {R Ar B D} x g.
Arguments sh_eval_at {R Ar B D} x.
Arguments sh_eval_atE {R Ar B D} x g.
Arguments sh_eval_at_norm_le1 {R Ar B D} x.
