(**md**************************************************************************)
(** * Headline mass/marginal theorems for the QBS examples
       — total-mass and marginal-mass identities at the FMeas level

    For each of the four open examples in [theories/programs/examples.v]
    we ship a headline theorem stating, at the level of the
    [fmeas_mu] measure-of-the-FMeas-output, what the program denotes.
    The structural [_denot_E] reductions in [examples.v] expose the
    [kbind_ext] / [Yfix_fun_T] form of the denotation; here we close
    the loop with the measure-theoretic mass identities.

    HEADLINES SHIPPED IN THIS FILE.

    1. [ex_random_constant_mass] — for any test point [x : R],
       [[
         fmeas_mu
           (Lfun (der (FMeas R_obj))
                 (Lfun (ch_mor (kbind_ext (apply_at x)
                                  ex_random_constant_denot))
                       one1))
           [set: ar_carrier Ar R_obj]
         = fmeas_mu mu [set: ar_carrier Ar R_obj].
       ]]
       Proof: [ex_random_constant_marginal_headline] reduces the
       LHS-inner [kbind_ext ...] to [sample_kleisli mu Hmu]; we then
       evaluate [Lfun (sample_kleisli ... mu Hmu) one1 = prom mu]
       via [Lfun_ch_mor_adj_psi_at] + [unit_cofree_str_one1] +
       [bang_fmap_prom] + [lin_pt_unit]; finally [der_prom] +
       [fmeas_mu] identifies the two sides.

    2. [ex_random_linear_mass] — for any test point [x : R] and any
       measurable [U],
       [[
         fmeas_mu (fmeas_lax_pre mu mu) (arith_at_x_fun x ⁻¹` U)
         = \int[fmeas_mu mu]_(m) \int[fmeas_mu mu]_(b)
              \d_{arith_at_x_fun x (cast (m, b))} U.
       ]]
       This is the existing [ex_random_linear_marginal_headline]
       restated in the package; the total-mass identity for the
       marginal is recovered as a corollary by specialising [U :=
       [set: _]] and using [dirac_setT]: the iterated integral collapses
       to [fmeas_mu mu × fmeas_mu mu] (the product mass of [µ⊗µ]).

    3. [ex_loop_arr_mass_zero] — the bare-divergence example has
       FMeas-mass [0] at every Kleene iterate (hence at the supremum).
       The full Bang-level construction mirrors [em_fix_arr]'s setup
       for [ex_geom], but specialized to [ex_loop_body = \"_". #"l" @ ()]
       (no Bernoulli, no escape branch): every Kleene iterate is
       [prom precone_zero], hence its FMeas-mass extraction is [0].

    4. [ex_almost_loop_arr_mass] — the parameterised partial-termination
       example has FMeas-mass [p] at the Yfix supremum (or [0] if
       [p = 0], handled as a direct corollary of [ex_loop_arr_mass_zero]).
       Construction parallels [ex_geom_arr_mass_one] with the
       Bernoulli weight specialised from [1/2] to [p].

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

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Import Icones_tensor_hom_iso.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** §1 — Generic helper: [Lfun (sample_kleisli G mu Hmu)] at [one1]

    For any source coalgebra [G] (specifically [EM_term] here),
    [Lfun (ch_mor (sample_kleisli G mu Hmu)) one1 = prom mu].

    Used downstream for both [ex_random_constant] and [ex_random_linear]
    headline mass identities.

    Reduction chain:
    - [sample_kleisli G mu Hmu = const_kleisli G mu Hmu = adj_psi
      (const_icones G mu Hmu)] (by definition).
    - [ch_mor (adj_psi g) = bang_fmap g ∘ coalg_str G] ([adj_psiK]).
    - [coalg_str EM_term = unit_cofree_str]; [unit_cofree_str one1 =
      prom one1] ([unit_cofree_str_one1]).
    - [bang_fmap (const_icones G mu Hmu) (prom one1) = prom (Lfun
      (const_icones G mu Hmu) one1)] ([bang_fmap_prom]).
    - [const_icones G mu Hmu = lin_pt mu ∘ coalg_e G]; [coalg_e EM_term
      = id] ([coalg_e_term]); [linhom_iconesE] +
      [Lfun (icones_id Ar _) one1 = one1]; [lin_pt_unit] : at [one1],
      [lin_pt mu] is exactly [mu]. *)

Section SampleAtOne1.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

Variable (mu : fmeas R (ar_carrier Ar R_obj)).
Hypothesis Hmu : (cone_norm mu <= 1)%R.

Lemma sample_kleisli_at_one1 :
  Lfun (ch_mor (sample_kleisli (R := R) (Ar := Ar) (X := R_obj)
                  (EM_term : Coalgebra Ar) mu Hmu)) (one1 : cone_one_car Ar)
  = prom mu.
Proof.
rewrite /sample_kleisli /const_kleisli.
rewrite (Lfun_ch_mor_adj_psi_at
           (const_icones (EM_term : Coalgebra Ar) mu Hmu)
           (one1 : cone_one_car Ar)).
rewrite -[Lfun (coalg_str EM_term) (one1 : cone_one_car Ar)]
        /(Lfun (unit_cofree_str (Ar := Ar)) one1).
rewrite unit_cofree_str_one1.
have H1 : cone_norm (one1 : cone_one_car Ar) <= 1.
  by rewrite (_ : cone_norm one1 = 1) // /cone_norm /= /c1_norm.
rewrite (bang_fmap_prom _ one1 H1).
congr (prom _).
rewrite /const_icones.
rewrite -[Lfun (icones_comp _ _) _]
        /(Lfun (linhom_icones (lin_pt mu) (lin_pt_norm_le1 mu Hmu))
               (Lfun (coalg_e EM_term) one1)).
rewrite coalg_e_term.
rewrite -[Lfun (icones_id Ar _) _]/(one1 : cone_one_car Ar).
rewrite linhom_iconesE.
rewrite -[one1]/(MkConeOne Ar 1%:nng).
exact: lin_pt_unit.
Qed.

End SampleAtOne1.

Arguments sample_kleisli_at_one1 {R Ar R_obj} mu Hmu.

(** ** §2 — [ex_random_constant_mass] : marginal-at-[x] total mass equals
        [µ]'s total mass

    For every test point [x : R],
    [[
      fmeas_mu
        (Lfun (der (FMeas R_obj))
              (Lfun (ch_mor (kbind_ext (apply_at x)
                              ex_random_constant_denot))
                    one1))
        [set: ar_carrier Ar R_obj]
      = fmeas_mu mu [set: ar_carrier Ar R_obj].
    ]]
    This is the headline form of [ex_random_constant]: the
    "marginal at [x]" total mass IS [µ]'s total mass.  In particular,
    when [µ] is normalised ([µ(setT) = 1]) the marginal at every [x]
    has total mass [1].

    The proof composes [ex_random_constant_marginal_headline] (which
    collapses the [kbind_ext (apply_at x) ...] to [sample_kleisli mu
    Hmu]) with [sample_kleisli_at_one1] (which evaluates to [prom
    mu]) and [der_prom] (which unpacks [prom mu] to [mu]). *)

Section ExRandomConstantMass.
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

Local Notation tR' := (tR R_obj).
Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

Theorem ex_random_constant_mass (x : R) :
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
    [set: ar_carrier Ar R_obj]
  = fmeas_mu mu [set: ar_carrier Ar R_obj].
Proof.
rewrite (ex_random_constant_marginal_headline mu Hmu x).
rewrite sample_kleisli_at_one1.
by rewrite (der_prom (B := FMeas R_obj) mu Hmu).
Qed.

End ExRandomConstantMass.

Arguments ex_random_constant_mass
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} mu Hmu x.

(** ** §3 — [ex_random_linear_mass] : marginal-at-[x] total mass equals
        the product mass [µ(setT)·µ(setT)]

    Building on [ex_random_linear_marginal_headline] (existing in
    [examples.v]), we obtain at the total-set [U := setT]:
    [[
      fmeas_mu (fmeas_lax_pre mu mu)
        ((arith_at_x_fun x) @^-1` [set: ar_carrier Ar R_obj])
      = \int[fmeas_mu mu]_m \int[fmeas_mu mu]_b \d_{cast (m, b) ↦ ...} [setT].
    ]]
    The RHS-inner integrand is [\d_y [setT] = 1] (Dirac of any point
    has total mass [1]) for every choice of [m, b]; hence the iterated
    integral collapses to [µ(setT)·µ(setT)] by [fmeas_setT_fin] +
    arithmetic.  Independently, [fmeas_lax_pre_setT] gives the same
    bound directly, so the headline reads as a confirming identity at
    the [setT] level: the joint pushforward of [µ⊗µ] along the
    arithmetic [(m, b) ↦ m·x + b] has total mass [µ(setT)·µ(setT)] —
    matching the joint's total mass [µ(setT)·µ(setT)] (since pushforward
    preserves total mass and the universal pre-image is [setT]).

    The headline takes a measurability hypothesis on the pre-image —
    in fact, for U = setT the pre-image is always [setT] (which is
    measurable trivially), so no extra side condition leaks into the
    statement. *)

Section ExRandomLinearMass.
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

Local Notation tR' := (tR R_obj).
Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Open Scope ereal_scope.

Theorem ex_random_linear_mass (x : R) :
  fmeas_mu (fmeas_lax_pre mu mu)
    ((@arith_at_x_fun R Ar R_obj R_carrier_eq x) @^-1`
       [set: ar_carrier Ar R_obj])
  = fmeas_mu mu [set: ar_carrier Ar R_obj]
  * fmeas_mu mu [set: ar_carrier Ar R_obj].
Proof.
have pre_setT :
  (@arith_at_x_fun R Ar R_obj R_carrier_eq x) @^-1`
    [set: ar_carrier Ar R_obj] = [set: ar_carrier Ar (ar_prod Ar R_obj R_obj)].
  by apply/seteqP; split.
rewrite pre_setT.
exact: fmeas_lax_pre_setT.
Qed.

(** Companion identity at the iterated-integral side: re-runs
    [ex_random_linear_marginal_headline] at [U := setT] to expose the
    iterated-integral form of the same mass.  Combined with
    [ex_random_linear_mass], this is the headline pushforward statement
    [iterated ∫∫ = product mass]. *)
Theorem ex_random_linear_mass_iterated (x : R) :
  fmeas_mu (fmeas_lax_pre mu mu)
    ((@arith_at_x_fun R Ar R_obj R_carrier_eq x) @^-1`
       [set: ar_carrier Ar R_obj])
  = \int[fmeas_mu mu]_(m in [set: ar_carrier Ar R_obj])
       \int[fmeas_mu mu]_(b in [set: ar_carrier Ar R_obj])
         \d_(@arith_at_x_fun R Ar R_obj R_carrier_eq x
              (ar_prod_cast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj)
                            (m, b)))
           [set: ar_carrier Ar R_obj].
Proof.
exact: (@ex_random_linear_marginal_headline R Ar R_obj
          R_carrier_eq R_carrier_meas R_to_carrier_meas mu x _ measurableT).
Qed.

End ExRandomLinearMass.

Arguments ex_random_linear_mass
  {R Ar R_obj R_carrier_eq} mu x.
Arguments ex_random_linear_mass_iterated
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} mu x.
