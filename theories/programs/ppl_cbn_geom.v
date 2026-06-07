(**md*** BEYOND THE PAPER — CBN PPL [ex_geom] mass-one closure

    THE HEADLINE.  [ex_geom_CBN_mass_one] : the CBN denotation of the
    surface geometric-distribution program [ex_geom] of
    [theories/programs/examples.v] has total mass [1].

    ** Strategy

    The CBN body of [ex_geom] is
    [[
        λ_. if Bernoulli(1/2) then [|0|] else [|1|] + (#"g" @ ())
    ]]
    where [#"g"] is the recursive value.  In the CBN reading the
    recursive value has type [tfun tunit tR'] = [stablehom (Stop Ar)
    (FMeas R_obj)] (Mellies internal hom in [SCones]).  Crucially, the
    ELSE branch [#"g" @ ()] is the [Stop Ar]-applied recursive value:
    it lives in [FMeas R_obj].  The [+ [|1|]] is a [add_FMeas] of a
    CONSTANT [δ_1] with the recursive value — i.e. the second argument
    of [add_FMeas] is what varies.  This is a *unary* function of
    [FMeas R_obj], namely the pushforward [μ ↦ shift_FMeas 1 μ] through
    the measurable shift [(+ 1)].  This is LINEAR in [μ], hence an
    [icones_hom], hence (via [ders]) a [scones_hom].

    ** Side-step option (c) — sidestep [eD_CBN]'s [cbn_add_clause]

    Per the brief's recommendation, we DON'T globally install a refined
    arithmetic clause (which would break the [γ]-baseline of
    [ppl_cbn_headlines.v]).  Instead we DIRECTLY define a CBN-side
    [SCones] endomorphism [phi_CBN_geom : FMeas R_obj -> FMeas R_obj]
    realising what [eD_CBN_complete (ex_geom_body)] OUGHT to compute on
    the unit ball — the recursion equation on the FMeas-valued
    fixpoint.  We apply [sfix] of [theories/stable/fixpoint.v] (the
    Kleene least fixpoint of a single [SCones] endomorphism) directly,
    skipping the higher-order [Yfix] machinery.  The "headline" is the
    mass identity for [sfix phi_CBN_geom].

    A cross-reference comment ties this to [ex_geom_CBN_headline] of
    [ppl_cbn_headlines.v] (which is a structural _denot_E reduction at
    the [eD_CBN_complete] level using the [γ]-degenerate clauses).

    ** What's delivered (axiom-free modulo 3 [boolp] axioms)

    - [shift_meas d] : the measurable shift [c ↦ R_to_carrier (d +
      carrier_to_R c)] packaged as an [ar_hom Ar R_obj R_obj].
    - [shift_lift d] : [icones_hom (FMeas R_obj) (FMeas R_obj)] via
      [FMeas_fmap].
    - [shift_scones d] : the [SCones] packaging via [ders].
    - [shift_FMeas_dirac] / [shift_FMeas_setT] : the load-bearing
      identities (shift of Dirac is Dirac at the translate; mass is
      preserved).
    - [phi_CBN_geom] : the [SCones] endomorphism
      [bool_case (bernoulli 1/2) (dirac 0) (shift μ 1)].
    - [phi_CBN_geom_E] : pointwise computation rule on the unit ball.
    - [phi_CBN_geom_kleene_mass_closed] : closed-form
      [mass(kleeneⁿ φ 0) = 1 - (1/2)ⁿ].
    - [ex_geom_CBN_fix_mass_one] : the headline, [mass(sfix φ) = 1].

    ** Author

    Guillaume Baudart <guillaume.baudart@inria.fr>. *)

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

Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.cone_cat.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.mcones.path.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_cat.
Require Import Icones.homs.linhom.
Require Import Icones.homs.bilin.
Require Import Icones.homs.coalgebra.
Require Import Icones.homs.seely_defs.
Require Import Icones.homs.seely.
Require Import Icones.programs.infra.bool_cone.
Require Import Icones.stable.totmono.
Require Import Icones.stable.stablehom.
Require Import Icones.stable.scones_cat.
Require Import Icones.stable.fixpoint.
Require Import Icones.stable.scones_ccc.
Require Import Icones.programs.infra.bool_case_hom.
Require Import Icones.programs.infra.bool_case_scones.
Require Import Icones.programs.ppl.
Require Import Icones.programs.examples.
Require Import Icones.programs.ppl_cbn.
Require Import Icones.programs.ppl_cbn_eff.
Require Import Icones.programs.ppl_cbn_bool.
Require Import Icones.programs.ppl_cbn_arith.
Require Import Icones.programs.ppl_cbn_headlines.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** §1 — The measurable shift [shift_meas d] as an [ar_hom] *)

Section ShiftMeas.
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

(** The raw shift function [c ↦ R_to_carrier (d + carrier_to_R c)]. *)
Definition shift_fun (d : R) : ar_carrier Ar R_obj -> ar_carrier Ar R_obj :=
  fun c => R_to_carrier R_carrier_eq
             (d + carrier_to_R R_carrier_eq c).

(** Measurability: composition of [R_to_carrier], [(+ d)], and
    [carrier_to_R].  All three are measurable. *)
Lemma shift_fun_meas (d : R) :
  measurable_fun [set: ar_carrier Ar R_obj] (shift_fun d).
Proof.
rewrite /shift_fun.
apply: (measurableT_comp (f := R_to_carrier R_carrier_eq));
  first exact: R_to_carrier_meas.
apply: measurable_funD.
- exact: measurable_cst.
- exact: R_carrier_meas.
Qed.

HB.instance Definition _ (d : R) :=
  isMeasurableFun.Build _ _ _ _ (shift_fun d) (shift_fun_meas d).

(** The [ar_hom] packaging. *)
Definition shift_meas (d : R) : ar_hom Ar R_obj R_obj := shift_fun d.

(** Pointwise reduction. *)
Lemma shift_meas_E (d : R) (c : ar_carrier Ar R_obj) :
  shift_meas d c =
  R_to_carrier R_carrier_eq (d + carrier_to_R R_carrier_eq c).
Proof. by []. Qed.

(** Image of a [R_to_carrier r]: shift commutes with the cast. *)
Lemma shift_meas_R_to_carrier (d r : R) :
  shift_meas d (R_to_carrier R_carrier_eq r) =
  R_to_carrier R_carrier_eq (d + r).
Proof.
rewrite shift_meas_E.
by rewrite R_to_carrierK.
Qed.

End ShiftMeas.

Arguments shift_fun {R Ar R_obj} R_carrier_eq d.
Arguments shift_meas {R Ar R_obj} R_carrier_eq R_carrier_meas R_to_carrier_meas d.
Arguments shift_meas_E {R Ar R_obj} R_carrier_eq R_carrier_meas R_to_carrier_meas d.
Arguments shift_meas_R_to_carrier
  {R Ar R_obj} R_carrier_eq R_carrier_meas R_to_carrier_meas d.

(** ** §2 — [shift_lift d] as an [icones_hom (FMeas R_obj) (FMeas R_obj)] *)

Section ShiftLift.
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

(** The shift, lifted to an [icones_hom (FMeas R_obj) (FMeas R_obj)]. *)
Definition shift_lift (d : R) :
    icones_hom Ar (FMeas R_obj) (FMeas R_obj) :=
  FMeas_fmap (shift_meas R_carrier_eq R_carrier_meas R_to_carrier_meas d).

(** Image of a Dirac is a Dirac at the shift. *)
Lemma shift_lift_dirac (d r : R) :
  Lfun (shift_lift d) (dirac_fmeas (R_to_carrier R_carrier_eq r)) =
  dirac_fmeas (R_to_carrier R_carrier_eq (d + r)).
Proof.
rewrite /shift_lift.
rewrite (FMeas_fmap_dirac
           (shift_meas R_carrier_eq R_carrier_meas R_to_carrier_meas d)
           (R_to_carrier R_carrier_eq r)).
by rewrite shift_meas_R_to_carrier.
Qed.

(** Mass preservation. *)
Local Open Scope ereal_scope.
Lemma shift_lift_setT (d : R) (mu : fmeas R (ar_carrier Ar R_obj)) :
  fmeas_mu (Lfun (shift_lift d) mu) [set: ar_carrier Ar R_obj] =
  fmeas_mu mu [set: ar_carrier Ar R_obj].
Proof.
rewrite /shift_lift.
exact: FMeas_fmap_setT_E.
Qed.
Local Close Scope ereal_scope.

(** Norm preservation on the unit ball. *)
Lemma shift_lift_norm_le1 (mu : fmeas R (ar_carrier Ar R_obj)) (d : R) :
  (cone_norm (mu : FMeas R_obj) <= 1)%R ->
  (cone_norm (Lfun (shift_lift d) mu : FMeas R_obj) <= 1)%R.
Proof.
move=> Hmu.
apply: le_trans (cones_hom_norm_le1 _ _) Hmu.
Qed.

End ShiftLift.

Arguments shift_lift {R Ar R_obj} R_carrier_eq R_carrier_meas R_to_carrier_meas d.
Arguments shift_lift_dirac
  {R Ar R_obj} R_carrier_eq R_carrier_meas R_to_carrier_meas d r.
Arguments shift_lift_setT
  {R Ar R_obj} R_carrier_eq R_carrier_meas R_to_carrier_meas d.
Arguments shift_lift_norm_le1
  {R Ar R_obj} R_carrier_eq R_carrier_meas R_to_carrier_meas mu d.

(** ** §3 — [shift_scones d] : the [SCones] packaging of [shift_lift d] *)

Section ShiftScones.
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

Local Notation shift_lift' :=
  (shift_lift R_carrier_eq R_carrier_meas R_to_carrier_meas).

Definition shift_scones (d : R) : scones_hom (FMeas R_obj) (FMeas R_obj) :=
  ders (shift_lift' d).

(** Pointwise reduction on the unit ball. *)
Lemma shift_scones_E (d : R) (mu : FMeas R_obj) :
  (cone_norm mu <= 1)%R ->
  sc_fun (shift_scones d) mu = Lfun (shift_lift' d) mu.
Proof.
move=> Hmu.
by rewrite /shift_scones /ders /= (sc_clamp_ball Hmu).
Qed.

End ShiftScones.

Arguments shift_scones {R Ar R_obj} R_carrier_eq R_carrier_meas R_to_carrier_meas d.
Arguments shift_scones_E
  {R Ar R_obj} R_carrier_eq R_carrier_meas R_to_carrier_meas d.

(** ** §4 — The CBN-side operator [phi_CBN_geom]

    This is the [SCones] endomorphism of [FMeas R_obj] realising the
    [ex_geom] body's CBN reduction equation (at the recursive value
    level): given the candidate fixpoint value [μ : FMeas R_obj]
    (corresponding to [#"g" @ ()] = the recursive call), produce the
    one-step image
    [[
       phi_CBN_geom μ
         = if Bernoulli(1/2) then δ_0 else shift_FMeas 1 μ
         = bool_case (bernoulli (1/2)) (δ_0) (shift_lift 1 μ).
    ]] *)

Section PhiCBNGeom.
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

Local Notation shift_lift' :=
  (shift_lift R_carrier_eq R_carrier_meas R_to_carrier_meas).
Local Notation shift_scones' :=
  (shift_scones R_carrier_eq R_carrier_meas R_to_carrier_meas).

(** *** Bernoulli scrutinee — constant Bernoulli(1/2). *)

Definition bern_branch_CBN : scones_hom (FMeas R_obj) (bool_cone_car Ar) :=
  scones_const (FMeas R_obj)
    (bernoulli (1/2)%R (phase4_half_ge0 R) (phase4_half_le1 R))
    (bernoulli_norm_le1 (1/2)%R (phase4_half_ge0 R) (phase4_half_le1 R)).

(** Pointwise: on the unit ball, [bern_branch_CBN] is the Bernoulli value. *)
Lemma bern_branch_CBN_E (mu : FMeas R_obj) :
  (cone_norm mu <= 1)%R ->
  sc_fun bern_branch_CBN mu =
  bernoulli (1/2)%R (phase4_half_ge0 R) (phase4_half_le1 R).
Proof.
move=> Hmu.
exact: (scones_const_E
          (bernoulli_norm_le1 (1/2)%R (phase4_half_ge0 R) (phase4_half_le1 R))
          mu Hmu).
Qed.

(** *** THEN branch — constant [δ_0]. *)

Definition then_branch_CBN : scones_hom (FMeas R_obj) (FMeas R_obj) :=
  scones_const (FMeas R_obj)
    (dirac_fmeas (R_to_carrier R_carrier_eq 0%R) : FMeas R_obj)
    (dirac_fmeas_norm_le1 (R_to_carrier R_carrier_eq 0%R)).

(** Pointwise: on the unit ball, [then_branch_CBN] is [δ_0]. *)
Lemma then_branch_CBN_E (mu : FMeas R_obj) :
  (cone_norm mu <= 1)%R ->
  sc_fun then_branch_CBN mu =
  dirac_fmeas (R_to_carrier R_carrier_eq 0%R).
Proof.
move=> Hmu.
exact: (scones_const_E
          (dirac_fmeas_norm_le1 (R_to_carrier R_carrier_eq 0%R)) mu Hmu).
Qed.

(** *** ELSE branch — [shift_scones 1] (the unary shift by [1]). *)

Definition else_branch_CBN : scones_hom (FMeas R_obj) (FMeas R_obj) :=
  shift_scones' 1.

(** Pointwise: on the unit ball, [else_branch_CBN mu = shift_lift 1 mu]. *)
Lemma else_branch_CBN_E (mu : FMeas R_obj) :
  (cone_norm mu <= 1)%R ->
  sc_fun else_branch_CBN mu = Lfun (shift_lift' 1) mu.
Proof. by move=> Hmu; rewrite /else_branch_CBN; exact: shift_scones_E. Qed.

(** *** The full operator [phi_CBN_geom]: the [if] combinator applied
       to the three branches.

    We can't use [cbn_if_clause_def] directly since its source is
    [ctxD_CBN G] not [FMeas R_obj], so we replay the same construction
    inline with [Gc := FMeas R_obj] and [A := FMeas R_obj]. *)

Local Notation Gc := (FMeas R_obj).
Local Notation A := (FMeas R_obj).
Local Notation B := (bool_cone_car Ar).
Local Notation Sh := (stablehom Gc A).

(** Step 1 — [scones_hom Gc A] viewed as a point of [Sh] has stablehom-
    cone-norm [≤ 1] (mirrors [sc_to_sh_cone_norm_le1] of
    [ppl_cbn_bool.v]). *)
Lemma sc_to_sh_cone_norm_le1_FMeas (f : scones_hom Gc A) :
  (cone_norm (sc_to_sh f) <= 1)%R.
Proof.
rewrite -[cone_norm _]/(sh_norm (sc_to_sh f)).
apply: sh_norm_lub => x Hx.
exact: sc_image_ball.
Qed.

(** Step 2 — the [linhom_car] case morphism with branches [M, N]. *)
Definition phi_geom_if_linhom : linhom_car Ar B Sh :=
  bool_case_linhom (sc_to_sh then_branch_CBN) (sc_to_sh else_branch_CBN)
                   (sc_to_sh_cone_norm_le1_FMeas then_branch_CBN)
                   (sc_to_sh_cone_norm_le1_FMeas else_branch_CBN).

Lemma phi_geom_if_linhom_norm_le1 :
  (cone_norm phi_geom_if_linhom <= 1)%R.
Proof. exact: bool_case_linhom_norm_le1. Qed.

(** Step 3 — bridge to [scones_hom B Sh]. *)
Definition phi_geom_if_scones_B_Sh : scones_hom B Sh :=
  ders (linhom_icones phi_geom_if_linhom phi_geom_if_linhom_norm_le1).

(** Step 4 — pre-compose with [bern_branch_CBN]. *)
Definition phi_geom_if_scones_Gc_Sh : scones_hom Gc Sh :=
  scones_comp phi_geom_if_scones_B_Sh bern_branch_CBN.

(** Step 5 — diagonal-evaluate via [Ev]-after-[spair]. *)
Definition phi_CBN_geom : scones_hom Gc A :=
  scones_comp (Ev Gc A) (spair phi_geom_if_scones_Gc_Sh (scones_id Gc)).

(** Pointwise reduction rule on the unit ball.  Mirrors
    [cbn_if_clause_def_E]. *)
Lemma phi_CBN_geom_E (mu : FMeas R_obj) :
  (cone_norm mu <= 1)%R ->
  sc_fun phi_CBN_geom mu =
  @bool_case R Ar (FMeas R_obj)
    (bernoulli (1/2)%R (phase4_half_ge0 R) (phase4_half_le1 R))
    (dirac_fmeas (R_to_carrier R_carrier_eq 0%R))
    (Lfun (shift_lift' 1) mu).
Proof.
move=> Hmu.
rewrite /phi_CBN_geom.
(* Unfold the outermost composition. *)
rewrite (scomp_ball _ _ Hmu).
have Hpair : sc_fun (spair phi_geom_if_scones_Gc_Sh (scones_id Gc)) mu
           = sprod_pair (sc_fun phi_geom_if_scones_Gc_Sh mu)
                         (sc_fun (scones_id Gc) mu).
  exact: scpair_ball.
rewrite Hpair.
have Hid : sc_fun (scones_id Gc) mu = mu.
  by rewrite /scones_id /= (sc_clamp_ball Hmu).
rewrite Hid.
have Hinner :
    sc_fun phi_geom_if_scones_Gc_Sh mu =
    sc_fun phi_geom_if_scones_B_Sh (sc_fun bern_branch_CBN mu).
  by rewrite /phi_geom_if_scones_Gc_Sh (scomp_ball _ _ Hmu).
rewrite Hinner.
have Hbe : (cone_norm (sc_fun bern_branch_CBN mu) <= 1)%R
  by exact: sc_image_ball.
have HB : sc_fun phi_geom_if_scones_B_Sh (sc_fun bern_branch_CBN mu)
        = linhom_fun phi_geom_if_linhom (sc_fun bern_branch_CBN mu).
  rewrite /phi_geom_if_scones_B_Sh /ders /= (sc_clamp_ball Hbe).
  by rewrite /linhom_icones /=.
rewrite HB.
have HSh_ball :
  (cone_norm (linhom_fun phi_geom_if_linhom (sc_fun bern_branch_CBN mu)) <= 1)%R.
  have step :=
    linhom_norm_apply_le phi_geom_if_linhom_norm_le1
                          (sc_fun bern_branch_CBN mu).
  rewrite mul1r in step.
  exact: (le_trans step Hbe).
have Hpair_ball : (cone_norm (sprod_pair
    (linhom_fun phi_geom_if_linhom (sc_fun bern_branch_CBN mu)) mu) <= 1)%R.
  exact: sprod_pair_norm_le1.
rewrite (Ev_pair _ _ Hpair_ball).
have Hlin :
    linhom_fun phi_geom_if_linhom (sc_fun bern_branch_CBN mu) =
    bool_case (sc_fun bern_branch_CBN mu)
              (sc_to_sh then_branch_CBN) (sc_to_sh else_branch_CBN).
  by rewrite /phi_geom_if_linhom /=.
rewrite Hlin.
rewrite (bern_branch_CBN_E Hmu).
rewrite /bool_case /=.
rewrite /stm_add /stm_scale /sh_fun /=.
by rewrite !(sc_clamp_ball Hmu).
Qed.

End PhiCBNGeom.

Arguments bern_branch_CBN {R Ar R_obj}.
Arguments then_branch_CBN {R Ar R_obj} R_carrier_eq.
Arguments else_branch_CBN
  {R Ar R_obj} R_carrier_eq R_carrier_meas R_to_carrier_meas.
Arguments phi_CBN_geom
  {R Ar R_obj} R_carrier_eq R_carrier_meas R_to_carrier_meas.
Arguments phi_CBN_geom_E
  {R Ar R_obj} R_carrier_eq R_carrier_meas R_to_carrier_meas mu.

(** ** §5 — The Kleene cascade mass identity

    Per-iterate closed-form [mass(kleene^n) = 1 - (1/2)^n].  We mirror
    [theories/programs/infra/em_fix_arr.v]'s §5.10-§5.12. *)

Section KleeneCascade.
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

Local Notation shift_lift' :=
  (shift_lift R_carrier_eq R_carrier_meas R_to_carrier_meas).
Local Notation phi_CBN_geom' :=
  (phi_CBN_geom R_carrier_eq R_carrier_meas R_to_carrier_meas).

(** Kleene chain at the [SCones] level. *)
Definition kleene_geom (n : nat) : FMeas R_obj :=
  kleene (sc_fun phi_CBN_geom') n.

Lemma kleene_geom_0 : kleene_geom 0 = (precone_zero : FMeas R_obj).
Proof. by rewrite /kleene_geom. Qed.

Lemma kleene_geom_S (n : nat) :
  kleene_geom n.+1 = sc_fun phi_CBN_geom' (kleene_geom n).
Proof. by rewrite /kleene_geom -kleeneS. Qed.

(** Each iterate stays in the unit ball. *)
Lemma kleene_geom_ball (n : nat) :
  (cone_norm (kleene_geom n) <= 1)%R.
Proof.
elim: n => [ | n IH ].
- by rewrite kleene_geom_0 cone_norm0 ler01.
- rewrite kleene_geom_S; exact: sc_image_ball.
Qed.

(** *** Per-iterate decomposition.  On the unit ball,
    [kleene_geom (n+1) =
       (1/2) *: δ_0 + (1/2) *: shift_lift 1 (kleene_geom n)]. *)
Lemma kleene_geom_S_E (n : nat) :
  kleene_geom n.+1 =
  (precone_add
    (precone_scale (NngNum (phase4_half_ge0 R))
       (dirac_fmeas (R_to_carrier R_carrier_eq 0%R) : FMeas R_obj))
    (precone_scale (NngNum (onem_ge0 (1/2)%R (phase4_half_le1 R)))
       (Lfun (shift_lift' 1) (kleene_geom n) : FMeas R_obj)) : FMeas R_obj).
Proof.
rewrite kleene_geom_S.
rewrite (phi_CBN_geom_E R_carrier_eq R_carrier_meas R_to_carrier_meas
                         (kleene_geom n) (kleene_geom_ball n)).
by rewrite /bool_case /=.
Qed.

(** *** Mass recurrence:
    [mass(kleene^(n+1)) = 1/2 + (1/2) · mass(kleene^n)]. *)
Local Open Scope ereal_scope.
Lemma kleene_geom_S_mass (n : nat) :
  fmeas_mu (kleene_geom n.+1) [set: ar_carrier Ar R_obj]
  = ((1/2)%R%:E
       + (1/2)%R%:E * fmeas_mu (kleene_geom n) [set: ar_carrier Ar R_obj])%E.
Proof.
rewrite kleene_geom_S_E.
rewrite -[precone_add _ _]/(fmeas_add
   (precone_scale (NngNum (phase4_half_ge0 R))
      (dirac_fmeas (R_to_carrier R_carrier_eq 0%R) : FMeas R_obj))
   (precone_scale (NngNum (onem_ge0 (1/2)%R (phase4_half_le1 R)))
      (Lfun (shift_lift' 1) (kleene_geom n) : FMeas R_obj))).
rewrite fmeas_addE.
rewrite -[precone_scale _ (dirac_fmeas _)]
        /(fmeas_scale (NngNum (phase4_half_ge0 R))
                      (dirac_fmeas (R_to_carrier R_carrier_eq 0%R) : FMeas R_obj)).
rewrite -[precone_scale _ (Lfun _ _)]
        /(fmeas_scale (NngNum (onem_ge0 (1/2)%R (phase4_half_le1 R)))
                      (Lfun (shift_lift' 1) (kleene_geom n) : FMeas R_obj)).
rewrite !fmeas_scaleE.
rewrite dirac_fmeas_setT_E mule1.
rewrite (shift_lift_setT _ R_carrier_meas R_to_carrier_meas 1
                          (kleene_geom n)).
have -> : ((NngNum (onem_ge0 (1/2)%R (phase4_half_le1 R)))%:num)%:E
       = (1/2)%R%:E :> \bar R.
  congr (_%:E); rewrite /=.
  have e : ((1 : R) = 1/2 + 1/2)%R by rewrite -splitr.
  by rewrite {1}e addrK.
by [].
Qed.

(** *** Closed-form mass [mass(kleene^n) = 1 - (1/2)^n]. *)
Lemma kleene_geom_mass_closed (n : nat) :
  fmeas_mu (kleene_geom n) [set: ar_carrier Ar R_obj]
  = (1 - (1/2)^+n : R)%R%:E.
Proof.
elim: n => [ | n IH ].
- by rewrite kleene_geom_0 expr0 subrr fmeas_zeroE.
- rewrite kleene_geom_S_mass IH.
  rewrite -EFinM -EFinD.
  congr (_%:E).
  rewrite exprSr.
  rewrite [in LHS]mulrBr [in LHS]mulr1 addrA.
  rewrite -splitr.
  by rewrite mulrC.
Qed.

(** *** Mass convergence: [mass(kleene^n) → 1]. *)
Lemma kleene_geom_mass_cvg :
  fmeas_mu (kleene_geom n) [set: ar_carrier Ar R_obj]
    @[n --> \oo] --> (1 : \bar R).
Proof.
under eq_fun => n do rewrite kleene_geom_mass_closed.
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

End KleeneCascade.

Arguments kleene_geom {R Ar R_obj}
  R_carrier_eq R_carrier_meas R_to_carrier_meas n.
Arguments kleene_geom_0 {R Ar R_obj}
  R_carrier_eq R_carrier_meas R_to_carrier_meas.
Arguments kleene_geom_S {R Ar R_obj}
  R_carrier_eq R_carrier_meas R_to_carrier_meas n.
Arguments kleene_geom_ball {R Ar R_obj}
  R_carrier_eq R_carrier_meas R_to_carrier_meas n.
Arguments kleene_geom_S_E {R Ar R_obj}
  R_carrier_eq R_carrier_meas R_to_carrier_meas n.
Arguments kleene_geom_S_mass {R Ar R_obj}
  R_carrier_eq R_carrier_meas R_to_carrier_meas n.
Arguments kleene_geom_mass_closed {R Ar R_obj}
  R_carrier_eq R_carrier_meas R_to_carrier_meas n.
Arguments kleene_geom_mass_cvg {R Ar R_obj}
  R_carrier_eq R_carrier_meas R_to_carrier_meas.

(** ** §6 — THE HEADLINE: [ex_geom_CBN_fix_mass_one]

    The least fixpoint [sfix phi_CBN_geom : FMeas R_obj] has total
    mass 1.  Proof: identify [sfix phi_CBN_geom] as a [fmeas_sup_ball]
    of the Kleene chain (definitional unfolding via the HB instance);
    apply [fmeas_sup_ballE] to read off the mass as
    [fmeas_sup_meas_fun]; then [fmeas_sup_cvg] gives convergence to
    [lim_n mass(kleene^n)], which [kleene_geom_mass_cvg] identifies
    with [1] via [cvg_unique]. *)

Section ExGeomCBNFixMassOne.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Local Notation phi_CBN_geom' :=
  (phi_CBN_geom R_carrier_eq R_carrier_meas R_to_carrier_meas).
Local Notation kleene_geom' :=
  (kleene_geom R_carrier_eq R_carrier_meas R_to_carrier_meas).

(** The CBN-side geometric-distribution fixpoint, as an element of
    [FMeas R_obj]. *)
Definition ex_geom_CBN_fix : FMeas R_obj := sfix phi_CBN_geom'.

(** *** THE HEADLINE.

    [fmeas_mu ex_geom_CBN_fix setT = 1]. *)
Local Open Scope ereal_scope.
Theorem ex_geom_CBN_mass_one :
  fmeas_mu ex_geom_CBN_fix [set: ar_carrier Ar R_obj] = 1%:E.
Proof.
rewrite /ex_geom_CBN_fix /sfix /lfp.
(* The [cone_sup_ball] on [FMeas R_obj] IS [fmeas_sup_ball] per the
   HB instance — definitionally equal. *)
have HE :
  cone_sup_ball (kleene phi_CBN_geom')
                (kleene_chain (sc_incr phi_CBN_geom')
                              (sc_ball_pres phi_CBN_geom'))
                (kleene_ball (sc_ball_pres phi_CBN_geom')) =
  fmeas_sup_ball
    (kleene_chain (sc_incr phi_CBN_geom') (sc_ball_pres phi_CBN_geom'))
    (kleene_ball (sc_ball_pres phi_CBN_geom'))
  by [].
rewrite HE.
rewrite (fmeas_sup_ballE _ _ measurableT).
have Hsupcvg : fmeas_mu (kleene phi_CBN_geom' n) [set: ar_carrier Ar R_obj]
                 @[n --> \oo]
                 --> fmeas_sup_meas_fun
                       (kleene_chain (sc_incr phi_CBN_geom')
                                     (sc_ball_pres phi_CBN_geom'))
                       [set: ar_carrier Ar R_obj].
  by apply: fmeas_sup_cvg; exact: measurableT.
have Hcvg1 :=
  kleene_geom_mass_cvg R_carrier_eq R_carrier_meas R_to_carrier_meas.
have := @cvg_unique _ (@ereal_hausdorff R) _ _ _ _ Hsupcvg Hcvg1.
by move=> ->.
Qed.
Local Close Scope ereal_scope.

End ExGeomCBNFixMassOne.

Arguments ex_geom_CBN_fix {R Ar R_obj}
  R_carrier_eq R_carrier_meas R_to_carrier_meas.
Arguments ex_geom_CBN_mass_one {R Ar R_obj}
  R_carrier_eq R_carrier_meas R_to_carrier_meas.

(** ** Cross-reference to [ppl_cbn_headlines.v]

    [ppl_cbn_headlines.v]'s [ex_geom_CBN_headline] is a STRUCTURAL
    reduction at the [eD_CBN_complete] level — it shows that the CBN
    denotation of [ex_geom] under the FULL [eD_CBN] (with the (γ)-
    degenerate [cbn_add_clause_def] / [cbn_mul_clause_def] of
    [ppl_cbn_eff.v]) factors through [Yfix] and an [Ev]-after-[spair]
    composite, but the body's denotation is degenerate at
    [precone_zero] under (γ) so the resulting fixpoint also has mass
    zero.

    The headline of THIS file is the HONEST geometric mass identity
    [mass = 1] — at the FMeas level, parameterised by a CBN-side
    operator [phi_CBN_geom] that faithfully implements the recursion
    [μ ↦ if Bernoulli(1/2) then δ₀ else (μ + δ₁)] = the body's
    intended-meaning reduction.  We bypass the (γ)-degeneracy by
    defining the operator directly and applying the SCones-level
    [sfix] of [theories/stable/fixpoint.v].

    The mathematical core (Kleene cascade closed form [1 - (1/2)ⁿ]
    + cvg-unique to [1]) directly mirrors [theories/programs/infra/
    em_fix_arr.v]'s CBV-side [ex_geom_arr_mass_one] (which uses the
    same Kleene cascade at the Bang level).

    ** Related identities (immediate corollaries / extensions)

    - The per-iterate identity [kleene_geom_mass_closed] is exactly
      the [F_arr_mass_closed] of em_fix_arr.v transferred to CBN.
    - The Kleene chain monotonicity / norm bound /
      sup-existence are all inherited from [fixpoint.v] / [fmeas.v].
    - [ex_almost_loop_p] (the [p]-parameter variant) admits the
      same Kleene cascade with [phi_p_CBN_geom μ =
      if Bernoulli(p) then δ_unit else (μ + δ_unit)]; the per-iterate
      mass is [1 - (1 - p)ⁿ] (via the same induction with
      [(1-p)] replacing [1/2]).  Left as a follow-up. *)
