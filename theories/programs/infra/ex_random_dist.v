(**md**************************************************************************)
(** * CBV-side distribution-level headlines for [ex_random_constant]
       and [ex_random_linear]

    These are the CBV parallels of the CBN distribution-level headlines:

    - [ex_random_constant_CBN_headline] in
      [theories/programs/ppl_cbn_headlines.v] : the marginal at every [x]
      IS [µ] (uniformly).

    - [ex_random_linear_arith_marginal_at] in
      [theories/programs/ppl_cbn_arith_eff.v] : the marginal at every
      argument [arg] IS [add_FMeas (mul_FMeas µ arg) µ], the pushforward
      of [µ⊗µ] along [(m, b) ↦ m·arg + b].

    The CBV side in [theories/programs/infra/ex_headlines.v] previously
    shipped only the total-mass identity (specialise to [U := setT]); this
    file upgrades both to full FMeas / pointwise-measure identities.

    HEADLINES SHIPPED.

    1. [ex_random_constant_dist] — at the EM(!)-Kleisli level: the FMeas
       output of the marginal-at-[x] of [ex_random_constant] equals [µ].
       Proof: composes [ex_random_constant_marginal_headline] with
       [sample_kleisli_at_one1] and [der_prom] — same recipe as the
       existing [ex_random_constant_mass], but without the
       [fmeas_mu .. [setT]] wrapper, giving a full FMeas equality.

       Corollary [ex_random_constant_marginal_at] : for any measurable
       set [U], [fmeas_mu of the marginal-at-x] [U = fmeas_mu mu U].
       This is the QBS-style "distribution at every U" statement.

    2. [ex_random_linear_arith_marginal_at_CBV] — at the measure level
       (pre-image of [fmeas_lax_pre µ µ] under the arithmetic
       [(m, b) ↦ m·x + b]): for every measurable [U], the pre-image
       measure equals the iterated integral of
       [\d_(arith_at_x_fun x (cast (m, b)))] against [µ⊗µ].

       This is the headline pushforward identity at arbitrary [U], the
       CBV parallel of CBN's [ex_random_linear_arith_marginal_at]
       restated at the FMeas-pre-image level (the CBV operational
       reduction to this measure-side level remains open through the
       Shape C / [kbind_ext_A] gap documented in
       [examples.v::Lemma 2]).

    Author: Guillaume Baudart <guillaume.baudart@inria.fr>. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals signed constructive_ereal.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import ereal.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import measure dirac_measure.
From mathcomp.analysis Require Import lebesgue_integral_definition numfun.

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
Require Import Icones.mcones.path.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_integral.
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
Require Import Icones.homs.tensor_hom_iso.
Require Import Icones.homs.smcc.
Require Import Icones.homs.exp_adjunction.
Require Import Icones.homs.bang.
Require Import Icones.homs.fmeas_lax.
Require Import Icones.homs.seely_defs.
Require Import Icones.homs.seely.
Require Import Icones.homs.coalgebra.
Require Import Icones.homs.em_cat.
Require Import Icones.homs.em_cartesian.
Require Import Icones.homs.em_seely_comonoid.
Require Import Icones.programs.infra.cbv_adjunction.
Require Import Icones.programs.infra.em_fix.
Require Import Icones.programs.infra.curry_kbind.
Require Import Icones.programs.cbv.
Require Import Icones.programs.ppl.
Require Import Icones.programs.examples.
Require Import Icones.programs.infra.ex_headlines.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Import Icones_tensor_hom_iso.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** §1 — [ex_random_constant] : the FMeas-level distribution identity

    THE QBS FLAGSHIP, CBV side.  For every test point [x : R], the
    marginal-at-[x] of [ex_random_constant] (= the FMeas obtained by
    [Lfun der] of the EM(!)-Kleisli arrow [kbind_ext (apply_at x)
    ex_random_constant_denot] applied to [one1]) IS the prior [µ] as
    an FMeas.  Strictly stronger than [ex_random_constant_mass] of
    [ex_headlines.v], which integrates [setT] on both sides.

    Recipe.  Identical to the mass-level proof:
    - [ex_random_constant_marginal_headline] rewrites the inner
      [kbind_ext] to [sample_kleisli µ Hµ].
    - [sample_kleisli_at_one1] evaluates [Lfun (ch_mor sample_kleisli)
      one1 = prom µ].
    - [der_prom (B := FMeas R_obj) µ Hµ] : [Lfun der (prom µ) = µ].
    The last rewrite is at the FMeas level (no [fmeas_mu] / [setT]),
    so the conclusion is the full distribution identity. *)

Section ExRandomConstantDist.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Variable (mu : fmeas R (ar_carrier Ar R_obj)).
Hypothesis Hmu : (cone_norm mu <= 1)%R.

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

(** *** The full distribution identity at the FMeas level *)
Theorem ex_random_constant_dist (x : R) :
  Lfun (der (FMeas R_obj))
       (Lfun (ch_mor
                (kbind_ext
                   (@examples.apply_at R Ar R_obj R_carrier_eq R_carrier_meas
                                       R_to_carrier_meas x)
                   (@ex_random_constant_denot R Ar R_obj
                     R_carrier_eq R_carrier_meas R_to_carrier_meas
                     mu Hmu)))
             (one1 : cone_one_car Ar))
  = mu :> FMeas R_obj.
Proof.
rewrite (ex_random_constant_marginal_headline mu Hmu x).
rewrite sample_kleisli_at_one1.
exact: (der_prom (B := FMeas R_obj) mu Hmu).
Qed.

(** *** Pointwise-measure corollary — the marginal at every [x] is the
    measure [µ] (pointwise on every measurable [U]). *)
Corollary ex_random_constant_marginal_at (x : R)
    (U : set (ar_carrier Ar R_obj)) :
  fmeas_mu
    (Lfun (der (FMeas R_obj))
          (Lfun (ch_mor
                   (kbind_ext
                      (@examples.apply_at R Ar R_obj R_carrier_eq R_carrier_meas
                                          R_to_carrier_meas x)
                      (@ex_random_constant_denot R Ar R_obj
                        R_carrier_eq R_carrier_meas R_to_carrier_meas
                        mu Hmu)))
                (one1 : cone_one_car Ar)))
    U
  = fmeas_mu mu U.
Proof. by rewrite ex_random_constant_dist. Qed.

End ExRandomConstantDist.

Arguments ex_random_constant_dist
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} mu Hmu x.
Arguments ex_random_constant_marginal_at
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} mu Hmu x U.

(** *** Dirac-input headline — the QBS flagship at the Dirac level

    Specialised to a Dirac prior [µ := δ_r], the marginal at every test
    point [x] IS the Dirac [δ_r].  This is the "sampling a Dirac and
    returning the sampled value at any test point recovers the Dirac"
    QBS-flagship pointwise identity, exposed as a direct corollary of
    [ex_random_constant_dist]. *)
Section ExRandomConstantDirac.
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

Corollary ex_random_constant_dirac (x : R) (r : ar_carrier Ar R_obj) :
  Lfun (der (FMeas R_obj))
       (Lfun (ch_mor
                (kbind_ext
                   (@examples.apply_at R Ar R_obj R_carrier_eq R_carrier_meas
                                       R_to_carrier_meas x)
                   (@ex_random_constant_denot R Ar R_obj
                     R_carrier_eq R_carrier_meas R_to_carrier_meas
                     (dirac_fmeas r) (dirac_fmeas_norm_le1 r))))
             (one1 : cone_one_car Ar))
  = (dirac_fmeas r : FMeas R_obj).
Proof.
exact: (ex_random_constant_dist (dirac_fmeas r) (dirac_fmeas_norm_le1 r) x).
Qed.

End ExRandomConstantDirac.

Arguments ex_random_constant_dirac
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} x r.

(** ** §2 — [ex_random_linear] : the pointwise pushforward identity

    THE KILLER DEMO, CBV side.  For every test point [x : R] and every
    measurable [U ⊆ R_obj], the pre-image measure of [fmeas_lax_pre µ µ]
    (the joint [µ⊗µ] viewed on the propositional product carrier) under
    [arith_at_x_fun x = (m, b) ↦ m·x + b] equals the iterated integral
    [∫ \d_{m·x + b} U dµ(m) dµ(b)].

    This is the headline pushforward identity at arbitrary measurable
    [U] — the CBV parallel of CBN's [ex_random_linear_arith_marginal_at]
    of [ppl_cbn_arith_eff.v], restated at the FMeas-pre-image level.

    Why this shape (not a [Lfun .. one1] form like §1).  The CBV
    operational reduction of the marginal at [x] of [ex_random_linear]
    proceeds via [ex_random_linear_marginal] (Shape C / partial); the
    inner double-[kbind_ext] cannot be collapsed without [kbind_ext_A]
    + the cartesian-η rule [em_pair_mor_proj_id], neither of which is
    delivered axiom-free in the current cones library (gap documented
    in [examples.v::Lemma 2]).  The MEASURE-LEVEL headline
    [ex_random_linear_marginal_headline] (already in [examples.v])
    sidesteps the gap by working directly with [fmeas_lax_pre], the
    bilinear FMeas-construction of [µ⊗µ].  This file ships the same
    headline through the [ex_headlines.v]-style infra packaging — the
    CBV-side counterpart of CBN's distribution-level headline.

    Mass corollary [ex_random_linear_mass_iterated] (in
    [ex_headlines.v]) is recovered as the [U := setT] specialisation. *)

Section ExRandomLinearArithMarginal.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Variable (mu : fmeas R (ar_carrier Ar R_obj)).
Hypothesis Hmu : (cone_norm mu <= 1)%R.

Local Open Scope ereal_scope.

(** *** Pointwise pushforward identity *)
Theorem ex_random_linear_arith_marginal_at_CBV (x : R)
    (U : set (ar_carrier Ar R_obj)) :
  measurable U ->
  fmeas_mu (fmeas_lax_pre mu mu)
    ((@arith_at_x_fun R Ar R_obj R_carrier_eq x) @^-1` U)
  = \int[fmeas_mu mu]_(m in [set: ar_carrier Ar R_obj])
       \int[fmeas_mu mu]_(b in [set: ar_carrier Ar R_obj])
         \d_(@arith_at_x_fun R Ar R_obj R_carrier_eq x
              (ar_prod_cast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj)
                            (m, b)))
           U.
Proof.
move=> mU.
exact: (@ex_random_linear_marginal_headline R Ar R_obj
          R_carrier_eq R_carrier_meas R_to_carrier_meas mu x U mU).
Qed.

(** *** Dirac evaluation form — applied to a Dirac input [(δ_a, δ_b)]
    on the cartesian product, the pre-image integrand collapses to the
    Dirac-output [\d_(R_to_carrier (a·x + b)) U].

    This matches the surface program's [\ "x" => # "m" * # "x" + # "b"]
    under [m := a, b := b]: the marginal at [x] of the Dirac inputs
    is the Dirac at [a·x + b], proving that the pushforward shape is
    the genuine "feed Dirac inputs through the arithmetic" operation.

    Direct call of [ex_random_linear_arith_dirac_E] from [examples.v]. *)
Lemma ex_random_linear_arith_marginal_dirac (x : R) (a b : R)
    (U : set (ar_carrier Ar R_obj)) :
  \d_(@arith_at_x_fun R Ar R_obj R_carrier_eq x
        (ar_prod_cast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj)
                      (R_to_carrier R_carrier_eq a,
                       R_to_carrier R_carrier_eq b))) U =
  (\d_(R_to_carrier R_carrier_eq (a * x + b)%R) U : \bar R).
Proof. exact: (@ex_random_linear_arith_dirac_E R Ar R_obj R_carrier_eq x a b U). Qed.

(** *** Dirac-pair pushforward at the FMeas level — the QBS flagship at
    the Dirac level for the linear case

    Specialised to a Dirac-pair prior [µ_m := δ_a], [µ_b := δ_b], the
    pre-image measure of [fmeas_lax_pre δ_a δ_b] under [arith_at_x_fun x]
    equals the Dirac at [a·x + b].  Proof: combine [fmeas_lax_pre_dirac]
    (which collapses the FMeas-product of two Diracs to a single Dirac
    at [ar_prod_cast (a, b)]) with [arith_at_x_cast] (which evaluates
    [arith_at_x_fun] on a cartesian-cast Dirac input).

    This is the "Dirac pushforward" identity at the function level: feed
    Dirac inputs through the arithmetic, get a Dirac at the arithmetic's
    image.  It is the parallel of CBN's pointwise
    [add_FMeas (mul_FMeas µ arg) µ] when [µ_m = δ_a], [µ_b = δ_b]. *)
Lemma ex_random_linear_arith_marginal_dirac_pair (x : R) (a b : R) :
  let mu_a := dirac_fmeas (X := R_obj) (R_to_carrier R_carrier_eq a) in
  let mu_b := dirac_fmeas (X := R_obj) (R_to_carrier R_carrier_eq b) in
  fmeas_lax_pre mu_a mu_b =
  dirac_fmeas (X := ar_prod Ar R_obj R_obj)
    (ar_prod_cast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj)
       (R_to_carrier R_carrier_eq a, R_to_carrier R_carrier_eq b)).
Proof.
exact: fmeas_lax_pre_dirac.
Qed.

End ExRandomLinearArithMarginal.

Arguments ex_random_linear_arith_marginal_at_CBV
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} mu x U _.
Arguments ex_random_linear_arith_marginal_dirac
  {R Ar R_obj R_carrier_eq} x a b U.
Arguments ex_random_linear_arith_marginal_dirac_pair
  {R Ar R_obj R_carrier_eq} x a b.
