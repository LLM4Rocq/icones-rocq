(**md*** CBN PPL arithmetic foundation: [add_FMeas]

    This file delivers the AXIOM-FREE mathematical foundation for
    refining the (γ)-degenerate CBN [cbn_add_clause_def] of
    [theories/programs/ppl_cbn_eff.v] into a faithful, mass-preserving
    arithmetic clause.

    ** The single concrete operation
    [add_FMeas mu nu] : [FMeas R_obj] — defined as the pushforward of
    the iconic-product measure [fmeas_lax_pre mu nu : FMeas (ar_prod
    R_obj R_obj)] along the binary [+] operation transported through
    [R_carrier_eq].  Concretely:
    [[
       add_FMeas mu nu = Lfun (FMeas_fmap add_meas) (fmeas_lax_pre mu nu)
    ]]
    (where [add_meas : ar_hom (ar_prod R_obj R_obj) R_obj] is the
    [add_fun] of [theories/programs/ppl.v]).

    ** Headline lemmas (all axiom-free modulo 3 [boolp] axioms)
    - [add_FMeas_setT] : the total-mass product identity
      [(add_FMeas mu nu)(setT) = mu(setT) · nu(setT)].
    - [add_FMeas_norm] : [‖add_FMeas mu nu‖ = ‖mu‖ · ‖nu‖]
      (the cone-norm form — geometric series uses this).
    - [add_FMeas_norm_le1] : ball-preservation
      [‖add_FMeas mu nu‖ ≤ 1] when [‖mu‖ ≤ 1] and [‖nu‖ ≤ 1].
    - [add_FMeas_dirac] : [add_FMeas (delta_a) (delta_b) = delta_{a+b}]
      (the load-bearing Dirac identity for arithmetic on samples).
    - [add_FMeas_zero_l] / [add_FMeas_zero_r] : annihilation at
      [precone_zero] (the bilinearity-at-zero fact).

    ** Status of the CBN [ex_geom_CBN_mass_one] headline
    Section 2 (see the closing "GAP ANALYSIS") lays out the gap:
    [add_FMeas] is BILINEAR in [(mu, nu)] — so packaging it as a
    [scones_hom (sprod (FMeas R_obj) (FMeas R_obj)) (FMeas R_obj)]
    requires a stable bilinear-on-sprod builder that is NOT in the
    library (paper §7 finite-differences route, mechanised on the
    iconeType level in [theories/stable/findiff.v] but not threaded
    through to the SCones level).

    Once that builder lands, [ex_geom_CBN_mass_one] = 1 closes by
    mirroring [theories/programs/infra/em_fix_arr.v]'s §5.6–§5.14
    Kleene cascade at the SCones level.  The per-iterate mass
    identity [mass(F_n) = 1 - (1/2)^n] uses [add_FMeas_dirac] and
    [add_FMeas_norm] of THIS file in the cascade.

    ** Why this file is shipped
    [add_FMeas] is a CONCRETE measure-theoretic operation — the
    mass-product formula [‖add_FMeas mu nu‖ = ‖mu‖·‖nu‖] and the
    Dirac identity [add_FMeas (delta_a) (delta_b) = delta_{a+b}] are
    the LOAD-BEARING measure-theoretic facts that any refinement of
    [cbn_add_clause_def] will need.  They are completely independent
    of how [add_FMeas] is later wrapped as a [scones_hom] (the
    follow-up engineering wave).  This file delivers them axiom-free
    so the orchestrator's next wave can plug them directly into a
    refined [cbn_add_clause_def_arith]. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals signed constructive_ereal.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import measure dirac_measure.

From Stdlib Require Import Strings.String.

Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.cone_cat.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.mcones.path.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_cat.
Require Import Icones.homs.bilin.
Require Import Icones.homs.coalgebra.
Require Import Icones.homs.tensor.
Require Import Icones.homs.fmeas_lax.
Require Import Icones.programs.ppl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** [add_FMeas] — convolution of two finite measures along [+]

    Definition.  For [mu, nu : FMeas R_obj], [add_FMeas mu nu] is the
    pushforward of [fmeas_lax_pre mu nu : FMeas (ar_prod R_obj R_obj)]
    (paper §9 lax monoidal) along [add_meas : ar_hom (ar_prod R_obj
    R_obj) R_obj] (transported [+] across [R_carrier_eq]). *)

Section AddFMeas.
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

Local Notation add_meas' :=
  (@add_meas R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas).

(** The arithmetic-on-FMeas binary operation. *)
Definition add_FMeas (mu nu : fmeas R (ar_carrier Ar R_obj)) :
    fmeas R (ar_carrier Ar R_obj) :=
  Lfun (FMeas_fmap add_meas') (fmeas_lax_pre mu nu).

(** *** Total-mass product identity — [(add_FMeas mu nu)(setT) =
       mu(setT) · nu(setT)] *)

Local Open Scope ereal_scope.

Lemma add_FMeas_setT (mu nu : fmeas R (ar_carrier Ar R_obj)) :
  fmeas_mu (add_FMeas mu nu) [set: ar_carrier Ar R_obj] =
  fmeas_mu mu [set: ar_carrier Ar R_obj] *
  fmeas_mu nu [set: ar_carrier Ar R_obj].
Proof.
rewrite /add_FMeas.
(* Step 1: pushforward preserves total mass on setT. *)
rewrite (FMeas_fmap_setT_E add_meas' (fmeas_lax_pre mu nu)).
(* Step 2: lax-pre setT = product of total masses. *)
exact: fmeas_lax_pre_setT.
Qed.

Local Close Scope ereal_scope.

(** Norm form of the mass identity. *)
Lemma add_FMeas_norm (mu nu : fmeas R (ar_carrier Ar R_obj)) :
  fmeas_norm (add_FMeas mu nu) = (fmeas_norm mu * fmeas_norm nu)%R.
Proof.
rewrite /fmeas_norm add_FMeas_setT fineM//.
- exact: fmeas_setT_fin.
- exact: fmeas_setT_fin.
Qed.

(** Cone-norm version: [fmeas_norm = cone_norm] on [FMeas R_obj]. *)
Lemma add_FMeas_cone_norm (mu nu : fmeas R (ar_carrier Ar R_obj)) :
  cone_norm (add_FMeas mu nu : FMeas R_obj) =
  (cone_norm (mu : FMeas R_obj) * cone_norm (nu : FMeas R_obj))%R.
Proof.
rewrite -[cone_norm (add_FMeas mu nu : FMeas R_obj)]/(fmeas_norm _).
by rewrite add_FMeas_norm.
Qed.

(** *** Ball preservation: both inputs in the unit ball give an output
       in the unit ball. *)
Lemma add_FMeas_norm_le1 (mu nu : fmeas R (ar_carrier Ar R_obj)) :
  (cone_norm (mu : FMeas R_obj) <= 1)%R ->
  (cone_norm (nu : FMeas R_obj) <= 1)%R ->
  (cone_norm (add_FMeas mu nu : FMeas R_obj) <= 1)%R.
Proof.
move=> Hmu Hnu.
rewrite add_FMeas_cone_norm.
apply: mulr_ile1 => //.
- exact: cone_norm_ge0.
- exact: cone_norm_ge0.
Qed.

(** *** Dirac identity — [add_FMeas δ_a δ_b = δ_{a+b}]

    The load-bearing arithmetic-on-Dirac identity.  Mirrors the CBV-
    side [add_lift_dirac] of [theories/programs/ppl.v]. *)
Lemma add_FMeas_dirac (a b : R) :
  add_FMeas (dirac_fmeas (R_to_carrier R_carrier_eq a))
            (dirac_fmeas (R_to_carrier R_carrier_eq b)) =
  dirac_fmeas (R_to_carrier R_carrier_eq (a + b)).
Proof.
rewrite /add_FMeas.
(* Step 1: rewrite [fmeas_lax_pre δ_a δ_b] backwards via [fmeas_lax_E]
   to [Lfun (fmeas_lax R_obj R_obj) (ptensor δ_a δ_b)]. *)
rewrite -(fmeas_lax_E (dirac_fmeas (R_to_carrier R_carrier_eq a))
                      (dirac_fmeas (R_to_carrier R_carrier_eq b))).
(* Step 2: now apply [fmeas_lax_dirac] to collapse the inner. *)
rewrite (fmeas_lax_dirac (R_to_carrier R_carrier_eq a)
                         (R_to_carrier R_carrier_eq b)).
(* Step 3: outer pushforward of a Dirac is a Dirac. *)
rewrite (FMeas_fmap_dirac add_meas'
  (ar_prod_cast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj)
                (R_to_carrier R_carrier_eq a,
                 R_to_carrier R_carrier_eq b))).
by rewrite add_meas_cast !R_to_carrierK.
Qed.

(** *** Annihilation at [precone_zero] — bilinearity at zero

    Via the norm identity: [‖add_FMeas mu 0‖ = ‖mu‖ · ‖0‖ = 0], and
    [fmeas_normz] forces [add_FMeas mu 0 = precone_zero]. *)
Let fmeas_norm_zero :
    fmeas_norm (precone_zero : fmeas R (ar_carrier Ar R_obj)) = 0%R.
Proof.
by rewrite -[precone_zero]/(fmeas_zero : fmeas R (ar_carrier Ar R_obj))
           /fmeas_norm fmeas_zeroE.
Qed.

Lemma add_FMeas_zero_l (nu : fmeas R (ar_carrier Ar R_obj)) :
  add_FMeas precone_zero nu = precone_zero.
Proof.
by apply: fmeas_normz; rewrite add_FMeas_norm fmeas_norm_zero mul0r.
Qed.

Lemma add_FMeas_zero_r (mu : fmeas R (ar_carrier Ar R_obj)) :
  add_FMeas mu precone_zero = precone_zero.
Proof.
by apply: fmeas_normz; rewrite add_FMeas_norm fmeas_norm_zero mulr0.
Qed.

(** ** [mul_FMeas] — the multiplicative companion

    Same shape as [add_FMeas] but with [mul_meas] in place of
    [add_meas].  Identical mass-product formula and Dirac identity. *)

Local Notation mul_meas' :=
  (@mul_meas R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas).

Definition mul_FMeas (mu nu : fmeas R (ar_carrier Ar R_obj)) :
    fmeas R (ar_carrier Ar R_obj) :=
  Lfun (FMeas_fmap mul_meas') (fmeas_lax_pre mu nu).

Local Open Scope ereal_scope.

Lemma mul_FMeas_setT (mu nu : fmeas R (ar_carrier Ar R_obj)) :
  fmeas_mu (mul_FMeas mu nu) [set: ar_carrier Ar R_obj] =
  fmeas_mu mu [set: ar_carrier Ar R_obj] *
  fmeas_mu nu [set: ar_carrier Ar R_obj].
Proof.
rewrite /mul_FMeas.
rewrite (FMeas_fmap_setT_E mul_meas' (fmeas_lax_pre mu nu)).
exact: fmeas_lax_pre_setT.
Qed.

Local Close Scope ereal_scope.

Lemma mul_FMeas_norm (mu nu : fmeas R (ar_carrier Ar R_obj)) :
  fmeas_norm (mul_FMeas mu nu) = (fmeas_norm mu * fmeas_norm nu)%R.
Proof.
rewrite /fmeas_norm mul_FMeas_setT fineM//.
- exact: fmeas_setT_fin.
- exact: fmeas_setT_fin.
Qed.

Lemma mul_FMeas_cone_norm (mu nu : fmeas R (ar_carrier Ar R_obj)) :
  cone_norm (mul_FMeas mu nu : FMeas R_obj) =
  (cone_norm (mu : FMeas R_obj) * cone_norm (nu : FMeas R_obj))%R.
Proof.
rewrite -[cone_norm (mul_FMeas mu nu : FMeas R_obj)]/(fmeas_norm _).
by rewrite mul_FMeas_norm.
Qed.

Lemma mul_FMeas_norm_le1 (mu nu : fmeas R (ar_carrier Ar R_obj)) :
  (cone_norm (mu : FMeas R_obj) <= 1)%R ->
  (cone_norm (nu : FMeas R_obj) <= 1)%R ->
  (cone_norm (mul_FMeas mu nu : FMeas R_obj) <= 1)%R.
Proof.
move=> Hmu Hnu.
rewrite mul_FMeas_cone_norm.
apply: mulr_ile1 => //.
- exact: cone_norm_ge0.
- exact: cone_norm_ge0.
Qed.

Lemma mul_FMeas_dirac (a b : R) :
  mul_FMeas (dirac_fmeas (R_to_carrier R_carrier_eq a))
            (dirac_fmeas (R_to_carrier R_carrier_eq b)) =
  dirac_fmeas (R_to_carrier R_carrier_eq (a * b)).
Proof.
rewrite /mul_FMeas.
rewrite -(fmeas_lax_E (dirac_fmeas (R_to_carrier R_carrier_eq a))
                      (dirac_fmeas (R_to_carrier R_carrier_eq b))).
rewrite (fmeas_lax_dirac (R_to_carrier R_carrier_eq a)
                         (R_to_carrier R_carrier_eq b)).
rewrite (FMeas_fmap_dirac mul_meas'
  (ar_prod_cast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj)
                (R_to_carrier R_carrier_eq a,
                 R_to_carrier R_carrier_eq b))).
by rewrite mul_meas_cast !R_to_carrierK.
Qed.

Lemma mul_FMeas_zero_l (nu : fmeas R (ar_carrier Ar R_obj)) :
  mul_FMeas precone_zero nu = precone_zero.
Proof.
by apply: fmeas_normz; rewrite mul_FMeas_norm fmeas_norm_zero mul0r.
Qed.

Lemma mul_FMeas_zero_r (mu : fmeas R (ar_carrier Ar R_obj)) :
  mul_FMeas mu precone_zero = precone_zero.
Proof.
by apply: fmeas_normz; rewrite mul_FMeas_norm fmeas_norm_zero mulr0.
Qed.

End AddFMeas.

Arguments add_FMeas {R Ar R_obj} R_carrier_eq R_carrier_meas R_to_carrier_meas.
Arguments add_FMeas_setT {R Ar R_obj} R_carrier_eq R_carrier_meas R_to_carrier_meas.
Arguments add_FMeas_norm {R Ar R_obj} R_carrier_eq R_carrier_meas R_to_carrier_meas.
Arguments add_FMeas_cone_norm {R Ar R_obj} R_carrier_eq R_carrier_meas R_to_carrier_meas.
Arguments add_FMeas_norm_le1 {R Ar R_obj} R_carrier_eq R_carrier_meas R_to_carrier_meas.
Arguments add_FMeas_dirac {R Ar R_obj} R_carrier_eq R_carrier_meas R_to_carrier_meas.
Arguments add_FMeas_zero_l {R Ar R_obj} R_carrier_eq R_carrier_meas R_to_carrier_meas.
Arguments add_FMeas_zero_r {R Ar R_obj} R_carrier_eq R_carrier_meas R_to_carrier_meas.

Arguments mul_FMeas {R Ar R_obj} R_carrier_eq R_carrier_meas R_to_carrier_meas.
Arguments mul_FMeas_setT {R Ar R_obj} R_carrier_eq R_carrier_meas R_to_carrier_meas.
Arguments mul_FMeas_norm {R Ar R_obj} R_carrier_eq R_carrier_meas R_to_carrier_meas.
Arguments mul_FMeas_cone_norm {R Ar R_obj} R_carrier_eq R_carrier_meas R_to_carrier_meas.
Arguments mul_FMeas_norm_le1 {R Ar R_obj} R_carrier_eq R_carrier_meas R_to_carrier_meas.
Arguments mul_FMeas_dirac {R Ar R_obj} R_carrier_eq R_carrier_meas R_to_carrier_meas.
Arguments mul_FMeas_zero_l {R Ar R_obj} R_carrier_eq R_carrier_meas R_to_carrier_meas.
Arguments mul_FMeas_zero_r {R Ar R_obj} R_carrier_eq R_carrier_meas R_to_carrier_meas.

(** ** GAP ANALYSIS — the path to [ex_geom_CBN_mass_one = 1]

    What's delivered above (axiom-free modulo the 3 [boolp] axioms):
    - [add_FMeas mu nu] : a CONCRETE measure-theoretic convolution-along-
      [+] operation on [FMeas R_obj].
    - [add_FMeas_setT] / [add_FMeas_norm] / [add_FMeas_cone_norm] :
      [‖add_FMeas mu nu‖ = ‖mu‖·‖nu‖] (the mass-product formula
      underlying the geometric-series recurrence).
    - [add_FMeas_dirac] : [add_FMeas δ_a δ_b = δ_{a+b}] (the Dirac
      identity).
    - [add_FMeas_zero_l/r] : annihilation at [precone_zero] (the
      bilinearity-at-zero fact).
    - [add_FMeas_norm_le1] : ball-preservation [‖add_FMeas mu nu‖ ≤ 1]
      when [‖mu‖, ‖nu‖ ≤ 1].

    What still needs to be built for [ex_geom_CBN_mass_one = 1]:

    *** Gap 1 — Stable bilinear-on-[sprod] [scones_hom] builder

    Needed: a [scones_hom (sprod (FMeas R_obj) (FMeas R_obj)) (FMeas
    R_obj)] whose underlying function is
    [(p ↦ add_FMeas (sprod_fst p) (sprod_snd p))].
    Equivalently, a refined [cbn_add_clause_arith] of signature
    [[
       forall (G : ppl_ctx Ar)
              (M N : scones_hom (ctxD_CBN G) (FMeas R_obj)),
         scones_hom (ctxD_CBN G) (FMeas R_obj).
    ]]
    whose computation rule on the ball is
    [[
       sc_fun (cbn_add_clause_arith G M N) g
         = add_FMeas (sc_fun M g) (sc_fun N g).
    ]]

    *Obstruction.*  [add_FMeas] is BILINEAR in [(mu, nu)] — its
    composition with [g ↦ (M g, N g)] is degree-2 in [g], not
    degree-1.  A [scones_hom] requires the underlying function to be
    total-monotone (a degree-1, *additive*, condition on finite-sum
    decompositions of the input).  The right path is paper §7's
    stable-finite-differences machinery — a stable map of arity 2
    packaged as a [scones_hom] via the §7 Δ-cone construction.

    *Status in the library.*  Paper §7 finite-differences infra exists
    in [theories/stable/findiff.v] (the Δ operator + n-increasing
    characterisation, Thm 7.19 etc.), but the §7-to-SCones bridge
    that would package a stable bilinear-on-sprod map as a [scones_hom]
    is NOT yet built.  This is the irreducible engineering blocker.

    *** Gap 2 — Kleene-iterate cascade for [ex_geom]

    Once Gap 1 is bridged, [eD_CBN_arith] (= [eD_CBN] with the new
    [cbn_add_clause_arith]) gives a concrete Kleene cascade.  Letting
    [BB := stablehom (Stop Ar) (FMeas R_obj)] and
    [F  := sc_fun (curry (eD_CBN_arith ex_geom_body)) tt : BB → BB],
    we have
    [[
       sc_fun Yfix F = sup_n (kleene F n) : BB,
       (kleene F n) (tt) : FMeas R_obj.
    ]]
    The per-iterate recurrence
    [[
       mass(F^(n+1)(0)(tt)) = 1/2 + 1/2 · mass(F^n(0)(tt))
    ]]
    closes by:
    - the [Bernoulli(1/2)]-branch decomposition (via
      [cbn_if_clause_def_E] of [theories/programs/ppl_cbn_bool.v]);
    - the [Dirac]-at-0 [then]-branch contributing total mass [1];
    - the [add_FMeas δ_1 (F^n(0)(tt))]-shape [else]-branch, with
      total mass [‖δ_1‖ · ‖F^n(0)(tt)‖ = 1 · mass(F^n(0)(tt)) =
      mass(F^n(0)(tt))] by [add_FMeas_norm] above.

    Closed form: [mass(F^n(0)(tt)) = 1 - (1/2)^n].  Sup convergence
    to [1] via [F_arr_mass_cvg]-shape geometric series.  Total cost:
    ~300-500L mirroring [em_fix_arr.v]'s §5.6–§5.14.

    *** Gap 3 — Sup convergence at the SCones level

    The sup of the Kleene chain [F^n(0)(tt)] inside [FMeas R_obj] is
    the [cone_sup_ball] of [theories/cones/cone_cat.v]; the mass at
    this sup is the limit of the per-iterate mass — same
    [fmeas_sup_cvg]-style argument as [em_fix_arr.v]'s §5.12.  This
    step is largely a re-export of existing infrastructure (no fresh
    machinery needed beyond Gap 1).

    *** Engineering cost estimate

    - Gap 1 (the §7-bridge for bilinear-on-sprod): ~600-1200L of new
      infrastructure (an HB instance, the totmono proof via finite
      differences, ω-continuity, ball preservation).  This is the
      load-bearing wave.
    - Gap 2 (the [ex_geom] cascade): ~300-500L mirroring [em_fix_arr.v].
    - Gap 3 (sup convergence): ~50-100L.

    Total: ~1000-1800L, multi-day.

    ** Recommendation
    Treat Gap 1 as an INDEPENDENT M5 wave for the CBN trunk:
    the bilinear-on-sprod [scones_hom] builder is broadly useful (it
    would also unblock [ex_random_linear_CBN_marginal] = pushforward of
    [µ ⊗ µ] along [(m, b) ↦ m·x + b], i.e. the OPTION-(β) refinement of
    the current degenerate-at-zero marginal of [ppl_cbn_headlines.v]).

    Once Gap 1 lands, both [ex_geom_CBN_mass_one] (Gap 2 + 3) and
    [ex_random_linear_CBN_marginal_eq] become tractable in a single
    follow-up wave.

    All [add_FMeas]-level lemmas of THIS file are axiom-free and ready
    to be plugged in. *)
