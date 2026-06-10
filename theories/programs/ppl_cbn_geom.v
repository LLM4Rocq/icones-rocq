(**md*** CBN PPL [ex_geom] mass-one closure

    [ex_geom_CBN_mass_one] : the CBN denotation of the
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

    ** Refactored as an instance of the [BernoulliCascade] framework

    The shared Bernoulli-cascade machinery lives in
    [theories/programs/infra/cbn_bernoulli_cascade.v].  [ex_geom] is
    the instance with [p := 1/2], [halt := δ_0], and
    [cont_op := shift_scones 1].  The framework supplies the operator
    [phi_bcascade], its pointwise reduction rule, the Kleene chain
    and its closed-form mass identity, and the [sfix] headline.

    ** What's delivered here

    - [shift_meas d] / [shift_lift d] / [shift_scones d] : the
      measurable shift and its lift, packaged as an [SCones]-arrow on
      [FMeas R_obj].  These are SPECIFIC to [ex_geom]'s arithmetic
      body.
    - The mass-preservation hypothesis [shift_scones_mass_pres]
      witnessing that [cont_op := shift_scones 1] satisfies the
      framework's [Hcont_mass] requirement.
    - The framework instantiation yielding
      [ex_geom_CBN_fix : FMeas R_obj] and
      [ex_geom_CBN_mass_one : mass = 1].

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
Require Import Icones.programs.infra.cbn_bernoulli_cascade.

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

(** *** Mass-preservation: [shift_scones d] satisfies the framework's
       [Hcont_mass] requirement (mass is preserved on the unit ball). *)
Local Open Scope ereal_scope.
Lemma shift_scones_mass_pres (d : R) (mu : FMeas R_obj) :
  (cone_norm mu <= 1)%R ->
  (fmeas_mu (sc_fun (shift_scones d) mu) [set: ar_carrier Ar R_obj]
   = fmeas_mu mu [set: ar_carrier Ar R_obj])%E.
Proof.
move=> Hmu.
rewrite (shift_scones_E d Hmu).
exact: shift_lift_setT.
Qed.
Local Close Scope ereal_scope.

End ShiftScones.

Arguments shift_scones {R Ar R_obj} R_carrier_eq R_carrier_meas R_to_carrier_meas d.
Arguments shift_scones_E
  {R Ar R_obj} R_carrier_eq R_carrier_meas R_to_carrier_meas d.
Arguments shift_scones_mass_pres
  {R Ar R_obj} R_carrier_eq R_carrier_meas R_to_carrier_meas d.

(** ** §4 — Instantiation of [BernoulliCascade] for [ex_geom]

    [p := 1/2], [halt := δ_0], [cont_op := shift_scones 1]. *)

Section ExGeomCBN.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

(** The [δ_0] halt value with its unit-ball witness and mass identity. *)
Local Notation halt_geom :=
  (dirac_fmeas (R_to_carrier R_carrier_eq 0%R) : FMeas R_obj).

Lemma halt_geom_ball : (cone_norm halt_geom <= 1)%R.
Proof. exact: dirac_fmeas_norm_le1. Qed.

Local Open Scope ereal_scope.
Lemma halt_geom_mass : fmeas_mu halt_geom [set: ar_carrier Ar R_obj] = 1.
Proof. exact: dirac_fmeas_setT_E. Qed.
Local Close Scope ereal_scope.

(** The framework operator instantiated for [ex_geom]. *)
Definition phi_CBN_geom : scones_hom (FMeas R_obj) (FMeas R_obj) :=
  phi_bcascade (1/2)%R (bernoulli_half_ge0 R) (bernoulli_half_le1 R)
               halt_geom halt_geom_ball
               (shift_scones R_carrier_eq R_carrier_meas R_to_carrier_meas 1).

(** The [sfix]-level fixpoint of [phi_CBN_geom]. *)
Definition ex_geom_CBN_fix : FMeas R_obj :=
  sfix_bcascade (1/2)%R (bernoulli_half_ge0 R) (bernoulli_half_le1 R)
                halt_geom halt_geom_ball
                (shift_scones R_carrier_eq R_carrier_meas R_to_carrier_meas 1).

(** *** [fmeas_mu ex_geom_CBN_fix setT = 1]. *)
Local Open Scope ereal_scope.
Theorem ex_geom_CBN_mass_one :
  fmeas_mu ex_geom_CBN_fix [set: ar_carrier Ar R_obj] = 1%:E.
Proof.
rewrite /ex_geom_CBN_fix.
apply: sfix_bcascade_mass_one_if_pos.
- exact: halt_geom_mass.
- move=> mu Hmu.
  exact: (shift_scones_mass_pres R_carrier_eq R_carrier_meas
                                  R_to_carrier_meas 1 mu Hmu).
- by rewrite divr_gt0 // ltr0n.
Qed.
Local Close Scope ereal_scope.

End ExGeomCBN.

Arguments phi_CBN_geom
  {R Ar R_obj} R_carrier_eq R_carrier_meas R_to_carrier_meas.
Arguments ex_geom_CBN_fix
  {R Ar R_obj} R_carrier_eq R_carrier_meas R_to_carrier_meas.
Arguments ex_geom_CBN_mass_one
  {R Ar R_obj} R_carrier_eq R_carrier_meas R_to_carrier_meas.

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
    + cvg-unique to [1]) is supplied by the abstract
    [BernoulliCascade] framework of
    [theories/programs/infra/cbn_bernoulli_cascade.v]; [ex_geom] is
    one instance, [ex_almost_loop p] is another (see
    [theories/programs/ppl_cbn_almost_loop.v]). *)
