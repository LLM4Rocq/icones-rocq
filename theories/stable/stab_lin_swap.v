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

(** The tensor swap helpers ([eval_at], [linhom_comp], [icones_to_linhom],
    [linhom_int_eval], …) live inside the file modules
    [Icones_tensor_hom_iso] / [Icones_tensor_iso]; import them to access
    the names unqualified. *)
Import Icones_tensor_hom_iso.
Import Icones_tensor_iso.

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

(** ** Converse pointwise order on [linhom_car] — the difference witness

    If two integrable linear maps [u, v : C ⊸ D] are pointwise ordered
    ([u y ≤p v y] for every [y]), then [u ≤p v] in the cone [C ⊸ D].  The
    [linhom_car] difference [v − u] is built by [linhom_diff_car] (the
    (Normc) machinery), which requires the larger map to be in the unit
    ball; we rescale by [t := ‖v‖ + 1] so that [v/t] is norm-[≤ 1],
    build the difference of [u/t ≤ v/t], and scale the witness back by
    [t].  This is the engine for the total monotonicity of the backward
    transpose (and dually elsewhere): order in the [linhom] cone reduces
    to pointwise order in [D]. *)

Section LinhomLeOfPointwise.
Variables (R : realType) (Ar : MeasSubcat R).
Variables C D : ICone.type Ar.
Local Open Scope precone_scope.

Lemma linhom_le_of_pointwise (u v : linhom_car Ar C D) :
  (forall y : C, precone_le (linhom_fun u y) (linhom_fun v y)) ->
  precone_le u v.
Proof.
move=> Hpw.
have t_ge0 : (0 <= cone_norm v + 1)%R by rewrite addr_ge0 ?cone_norm_ge0 ?ler01.
have t_pos : (0 < cone_norm v + 1)%R by exact: cnorm_succ_pos.
have tinv_ge0 : (0 <= (cone_norm v + 1)^-1)%R by rewrite invr_ge0 ltW.
pose t : {nonneg R} := NngNum t_ge0.
pose tinv : {nonneg R} := NngNum tinv_ge0.
pose v' : linhom_car Ar C D := linhom_scale tinv v.
pose u' : linhom_car Ar C D := linhom_scale tinv u.
have Hv'le1 : linhom_norm v' <= 1.
  rewrite /v' linhom_normh /=.
  by rewrite mulrC -ler_pdivlMr ?invr_gt0 // mul1r invrK lerDl ler01.
have Hle' : forall y : C, exists z : D, linhom_fun v' y = linhom_fun u' y + z.
  move=> y.
  have [z Hz] := precone_scale_le tinv (Hpw y).
  exists z.
  rewrite /v' /u'.
  rewrite -[linhom_fun (linhom_scale tinv v) y]/(linhom_scale_fun tinv v y).
  rewrite -[linhom_fun (linhom_scale tinv u) y]/(linhom_scale_fun tinv u y).
  by rewrite /linhom_scale_fun -Hz.
pose d' : linhom_car Ar C D := linhom_diff_car Hle' Hv'le1.
exists (linhom_scale t d').
apply: linhom_eq => y.
rewrite -[linhom_fun (u + linhom_scale t d')%PC y]
  /(linhom_add_fun u (linhom_scale t d') y).
rewrite /linhom_add_fun.
rewrite -[linhom_fun (linhom_scale t d') y]/(linhom_scale_fun t d' y)
  /linhom_scale_fun.
have Hd'E : linhom_fun v' y = linhom_fun u' y + linhom_fun d' y.
  exact: (linhom_diff_E Hle' y).
rewrite /v' /u' in Hd'E.
rewrite -[linhom_fun (linhom_scale tinv v) y]/(linhom_scale_fun tinv v y) in Hd'E.
rewrite -[linhom_fun (linhom_scale tinv u) y]/(linhom_scale_fun tinv u y) in Hd'E.
rewrite /linhom_scale_fun in Hd'E.
have Hscan : (t%:num * tinv%:num)%:nng = 1%:nng :> {nonneg R}.
  by apply: val_inj => /=; rewrite mulfV// gt_eqF.
have := congr1 (fun w => t *: w) Hd'E.
move=> Hgoal; move: Hgoal.
rewrite precone_scale_DAr -!precone_scale_A Hscan !precone_scale_1.
by move=> ->.
Qed.

End LinhomLeOfPointwise.

Arguments linhom_le_of_pointwise {R Ar C D} u v.

(** ** The backward transpose [sls_bwd]

    For [g : C ⊸ (B ⇒ₛ D)], the backward map sends [g] to [x ↦ (y ↦
    g(y)(x))], i.e. [bwd_inner x := λ y. g(y)(x) : C ⊸ D], assembled as
    [linhom_comp (sh_eval_at x) g].  As a map [B → (C ⊸ D)] it is
    stable-and-measurable (0-extended off [B_B]); the [icones_hom] data
    of [sls_bwd] is then assembled from this [stablehom] together with
    its integral preservation. *)

Section SlsBwd.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C D : ICone.type Ar.
Local Open Scope precone_scope.

Variable g : linhom_car Ar C (stablehom B D).

(** The inner linear map [bwd_inner x : C ⊸ D], [y ↦ g(y)(x)]. *)
Definition bwd_inner (x : B) : linhom_car Ar C D :=
  linhom_comp (sh_eval_at x) g.

Lemma bwd_innerE (x : B) (y : C) :
  linhom_fun (bwd_inner x) y = sh_fun (linhom_fun g y) x.
Proof. by rewrite /bwd_inner linhom_compE sh_eval_atE. Qed.

(** Off [B_B], every [g(y)(x) = 0], so [bwd_inner x] is the zero linhom. *)
Lemma bwd_inner_offball (x : B) :
  ~~ (cone_norm x <= 1) -> bwd_inner x = linhom_zero C D.
Proof.
move=> Hx; apply: linhom_eq => y.
rewrite bwd_innerE.
by rewrite (sh_offball (linhom_fun g y) x Hx)
  -[linhom_fun (linhom_zero C D) y]/(linhom_zero_fun C D y).
Qed.

(** A [linhom_car C D] cone-sum evaluated at [y] is the cone-sum of the
    pointwise values (big-morphism of [linhom_fun ·ʸ]). *)
Lemma linhom_bigE (T : finType) (A : {set T})
    (h : T -> linhom_car Ar C D) (y : C) :
  linhom_fun (\big[precone_add/precone_zero]_(j in A) h j) y =
  \big[precone_add/precone_zero]_(j in A) linhom_fun (h j) y.
Proof.
apply: (big_morph (fun f : linhom_car Ar C D => linhom_fun f y)).
- by move=> f1 f2; rewrite -[linhom_fun (f1 + f2)%PC y]/(linhom_add_fun f1 f2 y).
- by rewrite -[linhom_fun (0%PC : linhom_car Ar C D) y]/(linhom_zero_fun C D y).
Qed.

(** Total monotonicity in [x]: in the [C ⊸ D] cone, reduce to pointwise
    order ([linhom_le_of_pointwise]) and then to total monotonicity of
    each [g(y)] (a stablehom). *)
Lemma bwd_inner_totmono : is_totmono bwd_inner.
Proof.
move=> n x u Hxu.
apply: linhom_le_of_pointwise => y.
rewrite !linhom_bigE.
under eq_bigr => I _ do rewrite bwd_innerE.
under [X in _ <=p X]eq_bigr => I _ do rewrite bwd_innerE.
have [[Htm _ _] _] := sh_meas_stable (linhom_fun g y).
exact: Htm.
Qed.

(** Boundedness on [B_B]: [‖bwd_inner x‖ ≤ ‖g‖], since for [‖y‖ ≤ 1],
    [‖g(y)(x)‖ ≤ ‖g(y)‖ ≤ ‖g‖]. *)
Lemma bwd_inner_bounded :
  exists M : R, forall x : B, cone_norm x <= 1 -> cone_norm (bwd_inner x) <= M.
Proof.
exists (cone_norm g) => x Hx.
rewrite -[cone_norm (bwd_inner x)]/(linhom_norm (bwd_inner x)).
apply: linhom_norm_sup_lub => y Hy.
rewrite bwd_innerE.
apply: le_trans (sh_norm_ub (linhom_fun g y) x Hx) _.
rewrite -[sh_norm (linhom_fun g y)]/(cone_norm (linhom_fun g y)).
apply: le_trans (linhom_norm_apply_le (lexx (cone_norm g)) y) _.
by rewrite -[X in _ <= X]mulr1; apply: ler_wpM2l; [exact: cone_norm_ge0|exact: Hy].
Qed.

(** ω-continuity in [x]: separate the [C ⊸ D] equality through the linhom
    test family ([linhom_mcone_M_sep]); on each test [(γ ▷ m)] the value
    [m s (g(γ s)(·))] is the test of the stablehom [g(γ s)], whose
    Scott-continuity ([sh_meas_stable]) and the radius-aware test-of-sup
    ([test_of_sup_at]) reduce both sides to the same [sup]. *)
Lemma bwd_inner_scott : is_scott_continuous_unit bwd_inner.
Proof.
move=> Mf u uch ub1 fuch fubMf Mfpos.
apply: linhom_mcone_M_sep => p [γ [γub [m [mM Hp]]]].
rewrite Hp /linhom_test /= /linhom_test_fun /=.
set s := ar_zero_pt Ar.
set h := linhom_fun g (γ s).
rewrite [in LHS]bwd_innerE.
rewrite -[m s (linhom_fun (cone_sup_at fuch fubMf Mfpos) (γ s))]
  /(test_fun (linhom_test γ γub m mM) s (cone_sup_at fuch fubMf Mfpos)).
rewrite (test_of_sup_at (linhom_test γ γub m mM) s fuch fubMf Mfpos).
have hch : forall n, sh_fun h (u n) <=p sh_fun h (u n.+1).
  move=> n; have [[Htm _ _] _] := sh_meas_stable h.
  apply: tm_incr_le => //; exact: ub1.
have [[_ [Mh0 HMh0] _] _] := sh_meas_stable h.
have Mh0_ge0 : (0 <= Mh0)%R.
  apply: le_trans (HMh0 0%PC _); first exact: cone_norm_ge0.
  by rewrite cone_norm0.
have Mh_ge0 : (0 <= Mh0 + 1)%R by rewrite addr_ge0 ?ler01.
pose Mh : {nonneg R} := NngNum Mh_ge0.
have Mhpos : (0 < Mh%:num)%R.
  by rewrite /Mh /=; apply: le_lt_trans Mh0_ge0 _; rewrite ltrDl ltr01.
have hubMh : forall n, cnorm (sh_fun h (u n)) <= Mh%:num.
  move=> n; rewrite /Mh /=.
  apply: le_trans (_ : Mh0 <= Mh0 + 1)%R; last by rewrite lerDl ler01.
  by apply: HMh0; exact: ub1.
have [[_ _ Hsc] _] := sh_meas_stable h.
rewrite (Hsc Mh u uch ub1 hch hubMh Mhpos).
rewrite (test_of_sup_at m s hch hubMh Mhpos).
congr (sup _); apply: eq_imagel => n _ /=.
by rewrite /linhom_test_fun bwd_innerE.
Qed.

(** Path-preservation in [x]: a unit-ball [B]-path [δ] maps to a
    measurable [C ⊸ D]-path [r ↦ bwd_inner (δ r)].  The norm bound is
    [‖g‖]; the joint test-measurability tests the measurable
    [B⇒ₛD]-path [s ↦ g(γ s)] (path-preservation of [g]), reindexed to
    [Z × X], against the [stablehom] internal-hom test [(δ∘snd) ▷
    (m∘fst)], then pulls back along the [Z × X] diagonal. *)
Lemma bwd_inner_pres_path
    (X : ar_obj Ar) (δ : ar_carrier Ar X -> B) :
  (forall r, cone_norm (δ r) <= 1) ->
  is_measurable_path (Ar:=Ar) (C:=B) δ ->
  is_measurable_path (Ar:=Ar) (C:=linhom_car Ar C D) (fun r => bwd_inner (δ r)).
Proof.
move=> Hδb Hδ.
split.
  exists (cone_norm g) => r.
  rewrite -[cone_norm (bwd_inner (δ r))]/(linhom_norm (bwd_inner (δ r))).
  apply: linhom_norm_sup_lub => y Hy.
  rewrite bwd_innerE.
  apply: le_trans (sh_norm_ub (linhom_fun g y) (δ r) (Hδb r)) _.
  rewrite -[sh_norm (linhom_fun g y)]/(cone_norm (linhom_fun g y)).
  apply: le_trans (linhom_norm_apply_le (lexx (cone_norm g)) y) _.
  by rewrite -[X0 in _ <= X0]mulr1; apply: ler_wpM2l;
    [exact: cone_norm_ge0|exact: Hy].
move=> Z p [γ [γub [m [mM Hp]]]].
rewrite Hp.
have HrwE : (fun q : (ar_carrier Ar Z * ar_carrier Ar X)%type =>
              linhom_test γ γub m mM q.1 (bwd_inner (δ q.2))) =
            (fun q => test_fun m q.1 (sh_fun (linhom_fun g (path_fun γ q.1)) (δ q.2))).
  by apply: funext => q; rewrite /linhom_test /= /linhom_test_fun bwd_innerE.
rewrite HrwE.
have Hgγ : is_measurable_path (fun s => linhom_fun g (path_fun γ s)).
  exact: (linhom_pre_pres_path (linhom_pre_of g) Z (path_fun γ) (path_is_path γ)).
pose Pfst : ar_carrier Ar (ar_prod Ar Z X) -> stablehom B D
  := fun q => linhom_fun g (path_fun γ (ar_prod_fst Z X q)).
have HPfst : is_measurable_path Pfst.
  exact: (reindex_path_measurable (ar_prod_fst Z X) Hgγ).
pose δsnd : ar_carrier Ar (ar_prod Ar Z X) -> B :=
  fun q => δ (ar_prod_snd Z X q).
have Hδsnd : is_measurable_path δsnd.
  exact: (reindex_path_measurable (ar_prod_snd Z X) Hδ).
pose γB : path_car Ar (ar_prod Ar Z X) B := MkPath Hδsnd.
have γB_ub : cone_norm γB <= 1.
  rewrite /cone_norm /=.
  apply: ge_sup; first exact: path_normset_nonempty.
  by move=> _ [q ->] /=; rewrite /δsnd; exact: Hδb.
pose mfst : test_of Ar (ar_prod Ar Z X) D := test_reindex (ar_prod_fst Z X) m.
have mfstM : mcone_M (ar_prod Ar Z X) mfst by exact: mcone_M_comp.
pose mSh : test_of Ar (ar_prod Ar Z X) (stablehom B D) :=
  sh_test γB γB_ub mfst mfstM.
have mShM : sh_mcone_M (Y := ar_prod Ar Z X) mSh.
  by exists γB, γB_ub, mfst, mfstM.
have [_ HPfstm] := HPfst.
have HPtest := HPfstm (ar_prod Ar Z X) mSh mShM.
pose ψ (sr : (ar_carrier Ar Z * ar_carrier Ar X)%type) :
  (ar_carrier Ar (ar_prod Ar Z X) * ar_carrier Ar (ar_prod Ar Z X))%type :=
  (ar_prod_cast (sr.1, sr.2), ar_prod_cast (sr.1, sr.2)).
have ψ_meas : measurable_fun [set: (ar_carrier Ar Z * ar_carrier Ar X)%type] ψ.
  apply: measurable_fun_pair.
  - apply: (measurableT_comp (ar_prod_cast_meas Ar Z X)).
    by apply: measurable_fun_pair; [exact: measurable_fst|exact: measurable_snd].
  - apply: (measurableT_comp (ar_prod_cast_meas Ar Z X)).
    by apply: measurable_fun_pair; [exact: measurable_fst|exact: measurable_snd].
rewrite (_ : (fun q : (ar_carrier Ar Z * ar_carrier Ar X)%type =>
                m q.1 (linhom_fun g (γ q.1) (δ q.2))) =
             (fun sr : (ar_carrier Ar Z * ar_carrier Ar X)%type =>
                mSh (ψ sr).1 (Pfst (ψ sr).2))); last first.
  apply: funext => sr.
  rewrite /ψ /mSh /Pfst /sh_test /= /sh_test_fun /=.
  rewrite /mfst /test_reindex /test_reindex_fun /=.
  rewrite /ar_prod_fst /ar_prod_fst_fun !ar_prod_castK /=.
  rewrite /δsnd.
  have HsndE : ar_prod_snd Z X (ar_prod_cast (sr.1, sr.2)) = sr.2.
    by rewrite -[ar_prod_snd Z X _]/(ar_prod_snd_fun (ar_prod_cast (sr.1, sr.2)))
       /ar_prod_snd_fun ar_prod_castK.
  by rewrite HsndE.
exact: (measurable_comp (F := setT) measurableT (subsetT _) HPtest ψ_meas).
Qed.

(** [bwd_inner] is stable-and-measurable in [x]. *)
Lemma bwd_inner_meas_stable : is_meas_stable bwd_inner.
Proof.
split.
  split.
  - exact: bwd_inner_totmono.
  - exact: bwd_inner_bounded.
  - exact: bwd_inner_scott.
move=> X δ Hδb Hδ; exact: bwd_inner_pres_path Hδb Hδ.
Qed.

(** The backward transpose as a [stablehom B (C ⊸ D)]. *)
Definition bwd_stablehom : stablehom B (linhom_car Ar C D) :=
  MkStablehom bwd_inner bwd_inner_meas_stable
    (fun x Hx => bwd_inner_offball Hx).

Lemma bwd_stablehomE (x : B) (y : C) :
  linhom_fun (sh_fun bwd_stablehom x) y = sh_fun (linhom_fun g y) x.
Proof. by rewrite -[sh_fun bwd_stablehom x]/(bwd_inner x) bwd_innerE. Qed.

End SlsBwd.

Arguments bwd_inner {R Ar B C D} g x.
Arguments bwd_stablehom {R Ar B C D} g.
Arguments bwd_stablehomE {R Ar B C D} g x y.

(** ** The backward [icones_hom] [sls_bwd]

    The map [g ↦ bwd_stablehom g : (C ⊸ (B⇒ₛD)) → (B ⇒ₛ (C ⊸ D))] is a
    full [icones_hom]: linearity / norm / ω-continuity reduce to the
    pointwise (in [x] and [y]) cone operations; path/integral
    preservation are the Fubini-style swaps. *)

Section SlsBwdHom.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C D : ICone.type Ar.
Local Open Scope precone_scope.

Local Notation Src := (linhom_car Ar C (stablehom B D)).
Local Notation Tgt := (stablehom B (linhom_car Ar C D)).

Lemma sls_bwd_linear : is_linear (fun g : Src => bwd_stablehom g).
Proof.
split.
- apply: stablehom_eq => x; apply: linhom_eq => y.
  rewrite bwd_stablehomE.
  rewrite -[(0%PC : Src)]/(linhom_zero C (stablehom B D)).
  rewrite -[linhom_fun (linhom_zero C (stablehom B D)) y]
    /(linhom_zero_fun C (stablehom B D) y).
  rewrite /linhom_zero_fun.
  rewrite -[sh_fun (0%PC : stablehom B D) x]/(sh_fun (sh_zero B D) x) sh_zeroE.
  rewrite -[(0 : stablehom B (linhom_car Ar C D)) x]
    /(sh_fun (sh_zero B (linhom_car Ar C D)) x) sh_zeroE.
  by rewrite -[linhom_fun (0%PC : linhom_car Ar C D) y]/(linhom_zero_fun C D y).
- move=> g1 g2; apply: stablehom_eq => x; apply: linhom_eq => y.
  rewrite bwd_stablehomE.
  rewrite -[sh_fun (bwd_stablehom g1 + bwd_stablehom g2)%PC x]
    /(sh_add (bwd_stablehom g1) (bwd_stablehom g2) x) sh_addE.
  rewrite -[linhom_fun (sh_fun (bwd_stablehom g1) x + sh_fun (bwd_stablehom g2) x)%PC y]
    /(linhom_add_fun (sh_fun (bwd_stablehom g1) x) (sh_fun (bwd_stablehom g2) x) y).
  rewrite /linhom_add_fun !bwd_stablehomE.
  rewrite -[linhom_fun (g1 + g2)%PC y]/(linhom_add_fun g1 g2 y) /linhom_add_fun.
  rewrite -[(linhom_fun g1 y + linhom_fun g2 y)%PC x]
    /(sh_add (linhom_fun g1 y) (linhom_fun g2 y) x).
  by rewrite sh_addE.
- move=> r g; apply: stablehom_eq => x; apply: linhom_eq => y.
  rewrite bwd_stablehomE.
  rewrite -[sh_fun (r *: bwd_stablehom g)%PC x]/(sh_scale r (bwd_stablehom g) x) sh_scaleE.
  rewrite -[linhom_fun (r *: sh_fun (bwd_stablehom g) x)%PC y]
    /(linhom_scale_fun r (sh_fun (bwd_stablehom g) x) y) /linhom_scale_fun.
  rewrite bwd_stablehomE.
  rewrite -[linhom_fun (r *: g)%PC y]/(linhom_scale_fun r g y) /linhom_scale_fun.
  rewrite -[(r *: linhom_fun g y)%PC x]/(sh_scale r (linhom_fun g y) x).
  by rewrite sh_scaleE.
Qed.

Lemma sls_bwd_norm (g : Src) :
  cone_norm (bwd_stablehom g) <= cone_norm g.
Proof.
rewrite -[cone_norm (bwd_stablehom g)]/(sh_norm (bwd_stablehom g)).
apply: sh_norm_lub => x Hx.
rewrite -[sh_fun (bwd_stablehom g) x]/(bwd_inner g x).
rewrite -[cone_norm (bwd_inner g x)]/(linhom_norm (bwd_inner g x)).
apply: linhom_norm_sup_lub => y Hy.
rewrite bwd_innerE.
apply: le_trans (sh_norm_ub (linhom_fun g y) x Hx) _.
rewrite -[sh_norm (linhom_fun g y)]/(cone_norm (linhom_fun g y)).
apply: le_trans (linhom_norm_apply_le (lexx (cone_norm g)) y) _.
by rewrite -[X in _ <= X]mulr1; apply: ler_wpM2l; [exact: cone_norm_ge0|exact: Hy].
Qed.

(** ω-continuity in [g]: separate the target [B ⇒ₛ (C ⊸ D)] via its
    arity-0 tests [(γ ▷ m)]; decompose [m] (a [C ⊸ D]-test) as
    [(γC ▷ mD)].  Both sides reduce to [sup_n mD s (uₙ(γC s)(γ s))]: the
    LHS via [linhom_sup_fun_test_sup] against the composite stablehom
    test [const_{γ s} ▷ mD]; the RHS via [sh_sup_fun_unitE] (stablehom
    sup at [γ s]) then [linhom_sup_fun_test_sup] again. *)
Lemma sls_bwd_continuous : is_omega_continuous (fun g : Src => bwd_stablehom g).
Proof.
move=> u uch ub1 fuch fub1.
apply: mcone_M_sep => P PM.
case: PM => γ [γub [m [mM HP]]].
rewrite HP /sh_test /= /sh_test_fun /=; clear HP P.
set s := ar_zero_pt Ar.
case: mM => γC [γCub [mD [mDM HmE]]].
rewrite HmE /linhom_test /= /linhom_test_fun /=.
rewrite -[bwd_inner (cone_sup_ball u uch ub1) (γ s)]
  /(bwd_stablehom (cone_sup_ball u uch ub1) (γ s)).
rewrite bwd_stablehomE.
have Hbs : cone_norm (γ s) <= 1.
  by apply: le_trans (path_norm_ub γ s) _; exact: γub.
have Hcs : cone_norm (γC s) <= 1.
  by apply: le_trans (path_norm_ub γC s) _; exact: γCub.
have Hγbs : cone_norm (sh_const_x_path (γ s)) <= 1.
  by rewrite /cone_norm /= sh_const_x_path_normE.
pose mSh : test_of Ar (ar_zero Ar) (stablehom B D) :=
  sh_test (sh_const_x_path (γ s)) Hγbs mD mDM.
have mShM : mcone_M (ar_zero Ar) mSh
  by exists (sh_const_x_path (γ s)), Hγbs, mD, mDM.
have HLrw : mD s (linhom_fun (cone_sup_ball u uch ub1) (γC s) (γ s)) =
            mSh s (linhom_fun (cone_sup_ball u uch ub1) (γC s)).
  by rewrite /mSh /sh_test /= /sh_test_fun /sh_const_x_path /sh_const_x_path_arity /=.
rewrite HLrw.
rewrite -[cone_sup_ball u uch ub1 : linhom_car Ar C (stablehom B D)]
  /(linhom_sup_ball u uch ub1).
rewrite -[linhom_fun (linhom_sup_ball u uch ub1) (γC s)]
  /(linhom_sup_fun uch ub1 (γC s)).
rewrite (linhom_sup_fun_test_sup uch ub1 mSh s (γC s)).
have ch : forall n, sh_fun (bwd_stablehom (u n)) (γ s) <=p
                    sh_fun (bwd_stablehom (u n.+1)) (γ s).
  by move=> n; exact: sh_le_pointwise (fuch n) (γ s).
have b1 : forall n, cnorm (sh_fun (bwd_stablehom (u n)) (γ s)) <= 1.
  by move=> n; apply: le_trans (sh_norm_ub (bwd_stablehom (u n)) (γ s) Hbs) _;
    exact: fub1.
rewrite (sh_sup_fun_unitE fuch fub1 Hbs ch b1).
rewrite -[cone_sup_ball (fun m0 : nat => bwd_stablehom (u m0) (γ s)) ch b1
          : linhom_car Ar C D]/(linhom_sup_ball _ ch b1).
rewrite -[linhom_fun (linhom_sup_ball _ ch b1) (γC s)]
  /(linhom_sup_fun ch b1 (γC s)).
rewrite (linhom_sup_fun_test_sup ch b1 mD s (γC s)).
congr (sup _); apply: eq_imagel => n _ /=.
rewrite /mSh /sh_test /= /sh_test_fun /sh_const_x_path /sh_const_x_path_arity /=.
by rewrite bwd_innerE.
Qed.

(** Path-preservation in [g]: a measurable [C ⊸ (B⇒ₛD)]-path [η] maps to
    a measurable [B ⇒ₛ (C ⊸ D)]-path [r ↦ bwd_stablehom (η r)].  The
    joint test-measurability tests [η] (reindexed to [Z × Y]) against the
    DOUBLY-composed test [γC ▷ (γ ▷ mD)] of [C ⊸ (B⇒ₛD)] and pulls back
    along the [Z × Y] diagonal in [Z]. *)
Lemma sls_bwd_pres_path (Y : ar_obj Ar) (η : ar_carrier Ar Y -> Src) :
  is_measurable_path η ->
  is_measurable_path (Ar:=Ar) (C:=Tgt) (fun r => bwd_stablehom (η r)).
Proof.
move=> Hη.
have [[Mη HMη] Hηm] := Hη.
split.
  exists Mη => r; apply: le_trans (sls_bwd_norm (η r)) _; exact: HMη.
move=> Z P PM.
case: PM => γ [γub [m [mM HP]]].
rewrite HP; clear HP P.
have [γC [γCub [mD [mDM HmE]]]] := mM.
have HrwE : (fun q : (ar_carrier Ar Z * ar_carrier Ar Y)%type =>
              sh_test γ γub m mM q.1 (bwd_stablehom (η q.2))) =
            (fun q => mD q.1 (sh_fun (linhom_fun (η q.2) (γC q.1)) (γ q.1))).
  apply: funext => q.
  rewrite /sh_test /= /sh_test_fun /=.
  rewrite HmE /linhom_test /= /linhom_test_fun /=.
  by rewrite bwd_innerE.
rewrite HrwE.
pose γfst : path_car Ar (ar_prod Ar Z Y) B :=
  MkPath (reindex_path_measurable (ar_prod_fst Z Y) (path_is_path γ)).
have γfstub : cone_norm γfst <= 1.
  rewrite /cone_norm /=; apply: ge_sup; first exact: path_normset_nonempty.
  by move=> _ [q ->] /=; apply: le_trans (path_norm_ub γ _) _; exact: γub.
pose γCfst : path_car Ar (ar_prod Ar Z Y) C :=
  MkPath (reindex_path_measurable (ar_prod_fst Z Y) (path_is_path γC)).
have γCfstub : cone_norm γCfst <= 1.
  rewrite /cone_norm /=; apply: ge_sup; first exact: path_normset_nonempty.
  by move=> _ [q ->] /=; apply: le_trans (path_norm_ub γC _) _; exact: γCub.
pose mDfst : test_of Ar (ar_prod Ar Z Y) D := test_reindex (ar_prod_fst Z Y) mD.
have mDfstM : mcone_M (ar_prod Ar Z Y) mDfst by exact: mcone_M_comp.
pose mBs : test_of Ar (ar_prod Ar Z Y) (stablehom B D) :=
  sh_test γfst γfstub mDfst mDfstM.
have mBsM : sh_mcone_M (Y := ar_prod Ar Z Y) mBs
  by exists γfst, γfstub, mDfst, mDfstM.
pose mLin : test_of Ar (ar_prod Ar Z Y) (linhom_car Ar C (stablehom B D)) :=
  linhom_test γCfst γCfstub mBs mBsM.
have mLinM : mcone_M (ar_prod Ar Z Y) mLin by exists γCfst, γCfstub, mBs, mBsM.
have Hηtest := Hηm (ar_prod Ar Z Y) mLin mLinM.
pose ψ (sr : (ar_carrier Ar Z * ar_carrier Ar Y)%type) :
  (ar_carrier Ar (ar_prod Ar Z Y) * ar_carrier Ar Y)%type :=
  (ar_prod_cast (sr.1, sr.2), sr.2).
have ψ_meas : measurable_fun [set: (ar_carrier Ar Z * ar_carrier Ar Y)%type] ψ.
  apply: measurable_fun_pair; last exact: measurable_snd.
  apply: (measurableT_comp (ar_prod_cast_meas Ar Z Y)).
  by apply: measurable_fun_pair; [exact: measurable_fst|exact: measurable_snd].
rewrite (_ : (fun q : (ar_carrier Ar Z * ar_carrier Ar Y)%type =>
                mD q.1 (linhom_fun (η q.2) (γC q.1) (γ q.1))) =
             (fun sr : (ar_carrier Ar Z * ar_carrier Ar Y)%type =>
                mLin (ψ sr).1 (η (ψ sr).2))); last first.
  apply: funext => sr.
  rewrite /ψ /mLin /linhom_test /= /linhom_test_fun /=.
  rewrite /mBs /sh_test /= /sh_test_fun /=.
  rewrite /mDfst /test_reindex /test_reindex_fun /=.
  by rewrite /γfst /γCfst /= /ar_prod_fst /ar_prod_fst_fun !ar_prod_castK /=.
exact: (measurable_comp (F := setT) measurableT (subsetT _) Hηtest ψ_meas).
Qed.

(** The [cones_hom] / [mcones_hom] data of the backward map. *)
Definition sls_bwd_cones : cones_hom Src Tgt :=
  ConesHom (fun g => bwd_stablehom g) sls_bwd_linear sls_bwd_continuous sls_bwd_norm.

Definition sls_bwd_mcones : mcones_hom Ar Src Tgt :=
  MkMConesHom sls_bwd_cones
    (fun Y η Hη => sls_bwd_pres_path (Y:=Y) (η:=η) Hη).

(** Integral preservation in [g]: a Fubini swap.  At a target test
    [(γ ▷ (γC ▷ mD))] the value of [bwd_stablehom (∫β)] is
    [mD s ((∫β)(γC s)(γ s))]; push the [C ⊸ (B⇒ₛD)]-integral inside via
    [linhom_int_eval] (giving a [B⇒ₛD]-integral), then through the
    point-[γ s] evaluation via [sh_eval_at_int_eval] (giving a [D]-path
    integral), and read off the integral of test-values by
    [icone_integralP]. *)
Lemma sls_bwd_pres_int
    (Y : ar_obj Ar) (β : ar_carrier Ar Y -> Src)
    (Hβ : is_measurable_path β) (µ : fmeas R (ar_carrier Ar Y)) :
  cones_hom_fun (mcones_hom_cones sls_bwd_mcones) (icone_integral β Hβ µ) =
  icone_integral
    (fun r => cones_hom_fun (mcones_hom_cones sls_bwd_mcones) (β r))
    (mcones_hom_pres_path sls_bwd_mcones Y β Hβ) µ.
Proof.
rewrite -[cones_hom_fun _ _]/(bwd_stablehom (icone_integral β Hβ µ)).
apply: icone_integral_eqP => P PM s.
case: PM => γ [γub [m [mM HP]]].
rewrite HP /sh_test /= /sh_test_fun /=.
have [γC [γCub [mD [mDM HmE]]]] := mM.
rewrite HmE /linhom_test /= /linhom_test_fun /=.
rewrite bwd_innerE.
under eq_integral => r _ do rewrite bwd_innerE.
rewrite (linhom_int_eval Hβ µ (γC s)).
rewrite -[sh_fun (icone_integral _ (linhom_int_section_meas Hβ (γC s)) µ) (γ s)]
  /(sh_eval_at_fun (γ s)
      (icone_integral (fun r => linhom_fun (β r) (γC s))
         (linhom_int_section_meas Hβ (γC s)) µ)).
rewrite (sh_eval_at_int_eval (γ s) (linhom_int_section_meas Hβ (γC s)) µ).
rewrite (icone_integralP _
  (sh_eval_at_pres_path (γ s) (linhom_int_section_meas Hβ (γC s))) µ mD mDM s).
by [].
Qed.

(** The backward [icones_hom] [sls_bwd : (C ⊸ (B⇒ₛD)) → (B ⇒ₛ (C ⊸ D))]. *)
Definition sls_bwd : icones_hom Ar Src Tgt :=
  MkIConesHom sls_bwd_mcones sls_bwd_pres_int.

Lemma sls_bwdE (g : Src) (x : B) (y : C) :
  linhom_fun (sh_fun (sls_bwd g) x) y = sh_fun (linhom_fun g y) x.
Proof. by rewrite -[sls_bwd g]/(bwd_stablehom g) bwd_stablehomE. Qed.

End SlsBwdHom.

Arguments sls_bwd {R Ar B C D}.
Arguments sls_bwdE {R Ar B C D} g x y.
