(** * Lemmas 4.6 and 4.7 — bilinearity, ω-continuity and measurability of [I^B_X]

    Paper reference: §4, pp. 1:24–1:26, Lemmas 4.6 and 4.7.

    For an integrable cone [B : iconeType Ar] and an [Ar]-object [X],
    the integration operator

        [I^B_X : Path(X, B) × FMeas(X) → B,  (β, µ) ↦ ∫ β(r) µ(dr)]

    is (1) bilinear, (2) ω-continuous in each argument and (3) jointly
    measurable in the sense of paper Lemma 4.7 (last paragraph).

    Coverage in this file:

    - Lemma 4.6 (proved): [kernel_integral_measurable] and
      [kernel_integral_measurable_ereal] — measurability of
      [s ↦ ∫ φ(s, r) κ(s, dr)] for a uniformly bounded kernel
      [κ] and bounded measurable [φ]. Proved by packaging
      [κ : Y -> fmeas R X] as an [R.-fker Y ~> X] via the
      mathcomp-analysis [Kernel_isFinite] factory, then invoking
      [measurable_fun_integral_finite_kernel].

    - Measure-direction MCT (proved): [integral_meas_sup] — for an
      increasing chain of finite measures and a non-negative
      measurable [f], the integrals [∫[µ_n] f] converge to
      [∫[fmeas_sup_ball] f]. Proved via [ge0_integral_measure_series]
      on the [fmeas_dseq] telescoping decomposition.

    - Linearity in [β] (proved):
      * [path_integral_eq_addB] — sum of integrals is an integral of
        the sum, given measurability of both addends.
      * [path_integral_eq_scaleB] — scalar multiple of an integral is
        an integral of the scaled path.
      * [icone_integral_addB] / [icone_integral_scaleB] — corollaries
        in [iconeType Ar].

    - Linearity in [µ] (proved):
      * [path_integral_eq_addmu] — adding measures adds integrals.
      * [path_integral_eq_scalemu] — scaling a measure scales the
        integral.
      * [icone_integral_addmu] / [icone_integral_scalemu] —
        corollaries in [iconeType Ar].

    - Lemma 4.2 (proved): [path_integral_norm_le] — the integral is
      bounded by the path norm times the measure norm.

    - Test-functional monotonicity (proved): [test_fun_le] — tests
      are monotone along the precone order.

    - ω-continuity in [β] / in [µ] / joint measurability of
      [I^B_X ∘ ⟨η, κ⟩]: documented as TODOs (see end of file).
      Lemma 4.6 (= [kernel_integral_measurable]) is the technical
      tool for the joint-measurability sub-claim.

    Design notes.

    - All test-side equations use [test_fun m s (β r)] in [R] then
      lift through [EFin] to feed [\int[fmeas_mu µ]_(r in setT) _].
      The integrand is always finite (an [EFin]) and non-negative
      (by [test_ge0]).

    - We use mathcomp-analysis 1.16.0's
      [ge0_integralD] / [ge0_integralZl] for linearity in the
      integrand, [ge0_integral_measure_add] / [ge0_integral_mscale]
      for linearity in the measure, and [measurable_fun_integral_finite_kernel]
      for Lemma 4.6.
*)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals constructive_ereal.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import ereal sequences ereal_normedtype.
From mathcomp.analysis Require Import normedtype.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import measure.
From mathcomp.analysis Require Import lebesgue_integral_definition.
From mathcomp.analysis Require Import lebesgue_integral_nonneg.
From mathcomp.analysis Require Import lebesgue_integral_monotone_convergence.
From mathcomp.analysis Require Import kernel.

Require Import Icones.prelude.classical_extra.
Require Import Icones.prelude.nonneg_extra.
Require Import Icones.prelude.ereal_extra.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.icones.pettis.
Require Import Icones.icones.icone.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** Auxiliary: measurability of [r ↦ test_fun m s (β r)] for one [s]

    From [is_measurable_path β] one gets joint measurability of
    [(s', r) ↦ test_fun m s' (β r)]. Specialising the first
    coordinate to a fixed [s : ar_carrier Y] yields measurability of
    the section [r ↦ test_fun m s (β r)]. *)

Section MeasurableTestComp.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (B : MCone.type Ar) (X : ar_obj Ar).
Variable β : ar_carrier Ar X -> B.

(** Measurability of the [r]-section of [(s, r) ↦ test_fun m s (β r)]
    at a fixed [s]. Used in every ge0_integralD / ge0_integralZl
    invocation below. *)
Lemma measurable_test_path_section (Y : ar_obj Ar)
    (m : test_of Ar Y B) (mB : mcone_M Y m)
    (Hβ : is_measurable_path β) (s : ar_carrier Ar Y) :
  measurable_fun [set: ar_carrier Ar X]
    (fun r : ar_carrier Ar X => test_fun m s (β r) : R).
Proof.
have [_ Hj] := Hβ.
exact: (measurable_fun_pair2 s (Hj Y m mB)).
Qed.

End MeasurableTestComp.

Arguments measurable_test_path_section {R Ar B X β Y m}.

(** ** Paper Lemma 4.6 — measurability of the kernel integral

    [s ↦ ∫_r φ(s, r) κ(s, dr)] is measurable when [φ] is bounded
    measurable and [κ : Y -> fmeas R X] is "bounded kernel" in the
    sense of paper §3.2.1 — uniformly bounded total mass and
    measurable evaluation against each measurable set.

    Proof strategy: package [κ] as an [R.-fker] (finite kernel) via
    the mathcomp-analysis [Kernel_isFinite] HB factory, then invoke
    [measurable_fun_integral_finite_kernel]. The kernel structure
    is built section-locally; downstream consumers only see the
    propositional statement [kernel_integral_measurable]. *)

Section Lemma46.
Variables (R : realType) (d d' : measure_display).
Variables (X : measurableType d) (Y : measurableType d').
Variable κ : Y -> fmeas R X.
Hypothesis κ_meas :
  forall U, measurable U ->
    measurable_fun [set: Y] (fun s => fmeas_mu (κ s) U).
Hypothesis κ_bound : exists M : R, forall s, (fmeas_norm (κ s) <= M)%R.

Local Open Scope ereal_scope.

(** The underlying [Y -> {measure set X -> \bar R}] view of [κ]. *)
Local Definition kernel46 (s : Y) : {measure set X -> \bar R} :=
  fmeas_mu (κ s).

Local Lemma kernel46E s U : kernel46 s U = fmeas_mu (κ s) U.
Proof. by []. Qed.

Local Lemma kernel46_meas U : measurable U ->
  measurable_fun [set: Y] (kernel46 ^~ U).
Proof. exact: κ_meas. Qed.

HB.instance Definition _ :=
  isKernel.Build _ _ Y X R kernel46 kernel46_meas.

(** Uniform upper bound on the kernel — strict, by bumping [M] by 1. *)
Local Lemma kernel46_uub : measure_fam_uub kernel46.
Proof.
have [M HM] := κ_bound.
have M_ge0 : (0 <= M)%R.
  apply: (le_trans (fmeas_norm_ge0 (κ (point : Y)))).
  exact: HM.
exists (M + 1)%R => s.
have Hfin : fmeas_mu (κ s) [set: X] \is a fin_num.
  exact: fmeas_setT_fin.
rewrite -(fineK Hfin) lte_fin.
apply: (le_lt_trans (HM s)).
by rewrite ltrDl.
Qed.

HB.instance Definition _ :=
  Kernel_isFinite.Build _ _ _ _ _ kernel46 kernel46_uub.

(** Paper Lemma 4.6 — non-negative ereal-valued form.

    For any non-negative bounded measurable [k : Y × X -> \bar R],
    the partial integral [s ↦ ∫[κ s] k(s, r) dr] is measurable. *)
Lemma kernel_integral_measurable_ereal (k : Y * X -> \bar R) :
  (forall p, 0 <= k p) ->
  measurable_fun [set: (Y * X)%type] k ->
  measurable_fun [set: Y]
    (fun s => \int[fmeas_mu (κ s)]_(r in [set: X]) k (s, r)).
Proof.
move=> k0 mk.
have := measurable_fun_integral_finite_kernel k kernel46 k0 mk.
by [].
Qed.

(** Paper Lemma 4.6 — concrete real-valued form, as needed for
    Lemma 4.7's measurability sub-claim.

    For non-negative bounded measurable [φ : Y × X -> R], the
    fine-cast partial integral [s ↦ fine (∫[κ s] (φ (s, r))%:E)] is
    measurable. We use a uniform bound [Mφ] on [φ] (combined with
    the [κ] norm bound) to ensure the [\bar R]-integral is finite,
    so the [fine] cast is faithful. *)
Lemma kernel_integral_measurable (φ : Y * X -> R) (Mφ : R) :
  (forall p, (0 <= φ p)%R) ->
  (forall p, (φ p <= Mφ)%R) ->
  measurable_fun [set: (Y * X)%type] φ ->
  measurable_fun [set: Y]
    (fun s => fine (\int[fmeas_mu (κ s)]_(r in [set: X]) (φ (s, r))%:E)).
Proof.
move=> φ_ge0 φ_le mφ.
have mEφ : measurable_fun [set: (Y * X)%type] (fun p => (φ p)%:E).
  exact/measurable_EFinP.
have k0 (p : Y * X) : (0 <= (φ p)%:E) by rewrite lee_fin.
have main := @kernel_integral_measurable_ereal (fun p => (φ p)%:E) k0 mEφ.
(* The fine cast is measurable because the integrand is finite-valued
   bounded by Mφ and κ s has finite total mass. *)
by apply: (measurableT_comp (f := fine));
  [exact: fine_measurable|exact: main].
Qed.

End Lemma46.

Arguments kernel_integral_measurable_ereal {R d d' X Y} κ.
Arguments kernel_integral_measurable {R d d' X Y} κ.

(** ** Linearity in [β] — Paper Lemma 4.7 (separate linearity, first arg)

    Two strands: additivity ([path_integral_eq_addB]) and scalar
    distribution ([path_integral_eq_scaleB]). Both use the
    linearity field [test_linD] / [test_linZ] of [test_of] on the
    cone side and [ge0_integralD] / [ge0_integralZl] on the
    integral side. The (Mssep) clause of [MCone] is *not* needed
    here — we work directly with the [path_integral_eq] predicate
    and assemble the unique witness later via [icone_integral_eqP]. *)

Section LinearityB.
Local Open Scope ereal_scope.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (B : MCone.type Ar) (X : ar_obj Ar).
Variable µ : fmeas R (ar_carrier Ar X).

(** Helper: the integrand bound for a measurable path through any
    arity-0 test is finite, so integrals never escape to [+oo]. *)
Local Lemma test_int_fin
  (β : ar_carrier Ar X -> B) (m : test_of Ar (ar_zero Ar) B) :
  is_measurable_path β ->
  mcone_M (ar_zero Ar) m ->
  \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X])
    (test_fun m (ar_zero_pt Ar) (β r))%:E \is a fin_num.
Proof.
move=> Hβ mM.
have [[M HM] _] := Hβ.
have intGe0 : 0 <= \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X])
                    (test_fun m (ar_zero_pt Ar) (β r))%:E.
  by apply: integral_ge0 => r _; rewrite lee_fin; apply: test_ge0.
have mf1 : measurable_fun [set: ar_carrier Ar X]
             (fun r => (test_fun m (ar_zero_pt Ar) (β r))%:E).
  by apply/measurable_EFinP; exact: (measurable_test_path_section mM Hβ).
have mf2 : measurable_fun [set: ar_carrier Ar X]
             (fun _ : ar_carrier Ar X => M%:E).
  exact: measurable_cst.
rewrite ge0_fin_numE//.
apply: (@le_lt_trans _ _
  (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X]) M%:E)).
  apply: ge0_le_integral => //.
  - by move=> r _; rewrite lee_fin; apply: test_ge0.
  - move=> r _; rewrite lee_fin.
    by apply: (le_trans (test_norm_le _ _ _)).
rewrite (_ : (fun _ => M%:E) = cst M%:E)//.
rewrite integral_cst//.
have HfT : fmeas_mu µ [set: ar_carrier Ar X] \is a fin_num.
  exact: fmeas_setT_fin.
by rewrite ltey_eq fin_numM.
Qed.

(** Paper Lemma 4.7 (separate linearity in [β], additive part).

    If [β1] and [β2] are measurable paths whose integrals over [µ]
    are [x1] and [x2], then the pointwise sum [r ↦ β1 r + β2 r]
    has integral [x1 + x2]. *)
Lemma path_integral_eq_addB
  (β1 β2 : ar_carrier Ar X -> B) (x1 x2 : B) :
  is_measurable_path β1 -> is_measurable_path β2 ->
  path_integral_eq β1 µ x1 ->
  path_integral_eq β2 µ x2 ->
  path_integral_eq (fun r => precone_add (β1 r) (β2 r))
                    µ (precone_add x1 x2).
Proof.
move=> Hβ1 Hβ2 H1 H2 m mM s.
rewrite test_linD (H1 m mM s) (H2 m mM s).
have m1 : measurable_fun [set: ar_carrier Ar X]
            (fun r => (test_fun m s (β1 r))%:E).
  apply/measurable_EFinP.
  exact: (measurable_test_path_section mM Hβ1).
have m2 : measurable_fun [set: ar_carrier Ar X]
            (fun r => (test_fun m s (β2 r))%:E).
  apply/measurable_EFinP.
  exact: (measurable_test_path_section mM Hβ2).
have F1 : \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X])
            (test_fun m s (β1 r))%:E \is a fin_num.
  by rewrite (_ : s = ar_zero_pt Ar); [exact: test_int_fin|exact: ar_zero_ptE].
have F2 : \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X])
            (test_fun m s (β2 r))%:E \is a fin_num.
  by rewrite (_ : s = ar_zero_pt Ar); [exact: test_int_fin|exact: ar_zero_ptE].
have -> : (fun r => (test_fun m s (precone_add (β1 r) (β2 r)))%:E) =
          (fun r => (test_fun m s (β1 r))%:E + (test_fun m s (β2 r))%:E).
  by apply: funext => r; rewrite test_linD EFinD.
rewrite ge0_integralD//=; first last.
- by move=> r _; rewrite lee_fin; apply: test_ge0.
- by move=> r _; rewrite lee_fin; apply: test_ge0.
by rewrite -fineD.
Qed.

(** Paper Lemma 4.7 (separate linearity in [β], scalar part).

    If [β] is a measurable path with integral [x] over [µ] and
    [r : {nonneg R}] is a scalar, then [r *: β] (pointwise) has
    integral [r *: x]. *)
Lemma path_integral_eq_scaleB
  (r : {nonneg R}) (β : ar_carrier Ar X -> B) (x : B) :
  is_measurable_path β ->
  path_integral_eq β µ x ->
  path_integral_eq (fun u => precone_scale r (β u))
                    µ (precone_scale r x).
Proof.
move=> Hβ Hx m mM s.
rewrite test_linZ (Hx m mM s).
have mE : measurable_fun [set: ar_carrier Ar X]
            (fun u => (test_fun m s (β u))%:E).
  apply/measurable_EFinP.
  exact: (measurable_test_path_section mM Hβ).
have Hfin : \int[fmeas_mu µ]_(u in [set: ar_carrier Ar X])
              (test_fun m s (β u))%:E \is a fin_num.
  by rewrite (_ : s = ar_zero_pt Ar); [exact: test_int_fin|exact: ar_zero_ptE].
have -> : (fun u => (test_fun m s (precone_scale r (β u)))%:E) =
          (fun u => r%:num%:E * (test_fun m s (β u))%:E).
  by apply: funext => u; rewrite test_linZ EFinM.
rewrite ge0_integralZl//; last by move=> u _; rewrite lee_fin; apply: test_ge0.
by rewrite fineM.
Qed.

End LinearityB.

Arguments path_integral_eq_addB {R Ar B X µ β1 β2 x1 x2}.
Arguments path_integral_eq_scaleB {R Ar B X µ} r {β x}.

(** ** Linearity in [β] — wrap-up for [iconeType] *)

Section LinearityBICone.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (B : ICone.type Ar) (X : ar_obj Ar).
Variable µ : fmeas R (ar_carrier Ar X).

(** Paper Lemma 4.7: the integration operator is additive in [β]. *)
Lemma icone_integral_addB
  (β1 β2 : ar_carrier Ar X -> B)
  (Hβ1 : is_measurable_path β1) (Hβ2 : is_measurable_path β2)
  (Hβ12 : is_measurable_path (fun r => precone_add (β1 r) (β2 r))) :
  icone_integral (fun r => precone_add (β1 r) (β2 r)) Hβ12 µ =
  precone_add (icone_integral β1 Hβ1 µ) (icone_integral β2 Hβ2 µ).
Proof.
apply/esym/icone_integral_eqP.
apply: path_integral_eq_addB => //; exact: icone_integralP.
Qed.

(** Paper Lemma 4.7: the integration operator is scalar in [β]. *)
Lemma icone_integral_scaleB
  (r : {nonneg R}) (β : ar_carrier Ar X -> B)
  (Hβ : is_measurable_path β)
  (Hrβ : is_measurable_path (fun u => precone_scale r (β u))) :
  icone_integral (fun u => precone_scale r (β u)) Hrβ µ =
  precone_scale r (icone_integral β Hβ µ).
Proof.
apply/esym/icone_integral_eqP.
apply: (path_integral_eq_scaleB r) => //; exact: icone_integralP.
Qed.

End LinearityBICone.

Arguments icone_integral_addB {R Ar B X µ β1 β2}.
Arguments icone_integral_scaleB {R Ar B X µ} r {β}.

(** ** Linearity in [µ] — Paper Lemma 4.7 (separate linearity, second arg)

    For a fixed measurable path [β], the integration operator is
    additive in the measure and scalar-distributive. The arithmetic
    is on the [fmeas]-side via [fmeas_add] / [fmeas_scale]. *)

Section LinearityMu.
Local Open Scope ereal_scope.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (B : MCone.type Ar) (X : ar_obj Ar).
Variable β : ar_carrier Ar X -> B.

(** Paper Lemma 4.7 (separate linearity in [µ], additive part).

    [I^B_X(β, µ1 + µ2) = I^B_X(β, µ1) + I^B_X(β, µ2)], stated at
    the level of [path_integral_eq] witnesses. *)
Lemma path_integral_eq_addmu
  (µ1 µ2 : fmeas R (ar_carrier Ar X)) (x1 x2 : B) :
  is_measurable_path β ->
  path_integral_eq β µ1 x1 ->
  path_integral_eq β µ2 x2 ->
  path_integral_eq β (fmeas_add µ1 µ2) (precone_add x1 x2).
Proof.
move=> Hβ H1 H2 m mM s.
rewrite test_linD (H1 m mM s) (H2 m mM s).
have mE : measurable_fun [set: ar_carrier Ar X]
            (fun r => (test_fun m s (β r))%:E).
  apply/measurable_EFinP.
  exact: (measurable_test_path_section mM Hβ).
have ge0 r : 0 <= (test_fun m s (β r))%:E.
  by rewrite lee_fin; apply: test_ge0.
have F1 : \int[fmeas_mu µ1]_(r in [set: ar_carrier Ar X])
            (test_fun m s (β r))%:E \is a fin_num.
  by rewrite (_ : s = ar_zero_pt Ar); [exact: test_int_fin|exact: ar_zero_ptE].
have F2 : \int[fmeas_mu µ2]_(r in [set: ar_carrier Ar X])
            (test_fun m s (β r))%:E \is a fin_num.
  by rewrite (_ : s = ar_zero_pt Ar); [exact: test_int_fin|exact: ar_zero_ptE].
have -> : fmeas_mu (fmeas_add µ1 µ2) =
          measure_add (fmeas_mu µ1) (fmeas_mu µ2) :> (_ -> _).
  by [].
by rewrite ge0_integral_measure_add//; first by rewrite -fineD.
Qed.

(** Paper Lemma 4.7 (separate linearity in [µ], scalar part).

    [I^B_X(β, r *: µ) = r *: I^B_X(β, µ)]. *)
Lemma path_integral_eq_scalemu
  (r : {nonneg R}) (µ : fmeas R (ar_carrier Ar X)) (x : B) :
  is_measurable_path β ->
  path_integral_eq β µ x ->
  path_integral_eq β (fmeas_scale r µ) (precone_scale r x).
Proof.
move=> Hβ Hx m mM s.
rewrite test_linZ (Hx m mM s).
have mE : measurable_fun [set: ar_carrier Ar X]
            (fun u => (test_fun m s (β u))%:E).
  apply/measurable_EFinP.
  exact: (measurable_test_path_section mM Hβ).
have ge0 u : 0 <= (test_fun m s (β u))%:E.
  by rewrite lee_fin; apply: test_ge0.
have Hfin : \int[fmeas_mu µ]_(u in [set: ar_carrier Ar X])
              (test_fun m s (β u))%:E \is a fin_num.
  by rewrite (_ : s = ar_zero_pt Ar); [exact: test_int_fin|exact: ar_zero_ptE].
have -> : fmeas_mu (fmeas_scale r µ) =
          mscale r (fmeas_mu µ) :> (_ -> _).
  by [].
rewrite ge0_integral_mscale//.
by rewrite fineM.
Qed.

End LinearityMu.

Arguments path_integral_eq_addmu {R Ar B X β µ1 µ2 x1 x2}.
Arguments path_integral_eq_scalemu {R Ar B X β} r {µ x}.

(** ** Linearity in [µ] — wrap-up for [iconeType] *)

Section LinearityMuICone.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (B : ICone.type Ar) (X : ar_obj Ar).
Variables (β : ar_carrier Ar X -> B) (Hβ : is_measurable_path β).

(** Paper Lemma 4.7: integration is additive in [µ]. *)
Lemma icone_integral_addmu (µ1 µ2 : fmeas R (ar_carrier Ar X)) :
  icone_integral β Hβ (fmeas_add µ1 µ2) =
  precone_add (icone_integral β Hβ µ1) (icone_integral β Hβ µ2).
Proof.
apply/esym/icone_integral_eqP.
apply: path_integral_eq_addmu => //; exact: icone_integralP.
Qed.

(** Paper Lemma 4.7: integration is scalar-distributive in [µ]. *)
Lemma icone_integral_scalemu
  (r : {nonneg R}) (µ : fmeas R (ar_carrier Ar X)) :
  icone_integral β Hβ (fmeas_scale r µ) =
  precone_scale r (icone_integral β Hβ µ).
Proof.
apply/esym/icone_integral_eqP.
apply: (path_integral_eq_scalemu r) => //; exact: icone_integralP.
Qed.

End LinearityMuICone.

Arguments icone_integral_addmu {R Ar B X β Hβ}.
Arguments icone_integral_scalemu {R Ar B X β Hβ} r µ.

(** ** Paper Lemma 4.2 — operator-norm bound on the integral

    For any [β : ar_carrier X → B] bounded in cone-norm by [Mβ] and
    any finite measure [µ] of total mass [Mµ = fmeas_norm µ], the
    integral [x] satisfies

      [cone_norm x ≤ Mβ * fmeas_norm µ].

    This is paper Lemma 4.2 (p. 1:24). Used as a prerequisite for
    the ω-continuity step. The proof uses (Msnorm) plus the
    pointwise [test_norm_le] bound. *)

Section Lemma42.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (B : MCone.type Ar) (X : ar_obj Ar).
Variables (β : ar_carrier Ar X -> B) (µ : fmeas R (ar_carrier Ar X)).
Variable Mβ : R.
Hypothesis Hβ_bound : forall r, (cone_norm (β r) <= Mβ)%R.
Hypothesis Hβ_meas : is_measurable_path β.

(** A small reusable Lemma 4.2 helper: under the bound hypothesis,
    the test-integral is bounded by [Mβ * fmeas_norm µ]. *)
Local Lemma test_int_bound (m : test_of Ar (ar_zero Ar) B) :
  mcone_M (ar_zero Ar) m ->
  (fine (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X])
            (test_fun m (ar_zero_pt Ar) (β r))%:E)
      <= Mβ * fmeas_norm µ)%R.
Proof.
move=> mM.
have IntFin :
  (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X])
     (test_fun m (ar_zero_pt Ar) (β r))%:E \is a fin_num)%E.
  by apply: test_int_fin => //; exists Mβ.
have IntGe0 :
  (0 <= \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X])
          (test_fun m (ar_zero_pt Ar) (β r))%:E)%E.
  by apply: integral_ge0 => r _; rewrite lee_fin; apply: test_ge0.
have mE : measurable_fun [set: ar_carrier Ar X]
            (fun r => (test_fun m (ar_zero_pt Ar) (β r))%:E).
  by apply/measurable_EFinP; exact: (measurable_test_path_section mM Hβ_meas).
have HfT : (fmeas_mu µ [set: ar_carrier Ar X] \is a fin_num)%E.
  exact: fmeas_setT_fin.
rewrite -lee_fin fineK// EFinM /fmeas_norm fineK//.
have mc : measurable_fun [set: ar_carrier Ar X]
            (fun _ : ar_carrier Ar X => Mβ%:E).
  exact: measurable_cst.
apply: (@le_trans _ _
  (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X]) Mβ%:E)%E).
  apply: ge0_le_integral => //.
  - by move=> r _; rewrite lee_fin; apply: test_ge0.
  - move=> r _; rewrite lee_fin.
    by apply: (le_trans (test_norm_le _ _ _)).
by rewrite (_ : (fun _ => Mβ%:E) = cst Mβ%:E)// integral_cst.
Qed.

(** Paper Lemma 4.2 (in elementary [≤] form).

    [‖x‖ ≤ Mβ · fmeas_norm µ] when [x] is an integral of [β]. *)
Lemma path_integral_norm_le (x : B) :
  path_integral_eq β µ x ->
  (cone_norm x <= Mβ * fmeas_norm µ)%R.
Proof.
move=> Hx.
have Mβ_ge0 : (0 <= Mβ)%R.
  by apply: (le_trans (cone_norm_ge0 (β (ar_point _ X)))); apply: Hβ_bound.
have [x_eq0|x_neq0] := pselect (x = precone_zero).
  by rewrite x_eq0 cone_norm0 mulr_ge0// fmeas_norm_ge0.
apply/ler_addgt0Pr => eps eps_pos.
have [m [mM Hm]] := mcone_M_norm x eps x_neq0 eps_pos.
apply: (le_trans Hm).
by rewrite lerD2r (Hx m mM (ar_zero_pt Ar)); exact: test_int_bound.
Qed.

End Lemma42.

Arguments path_integral_norm_le {R Ar B X β µ Mβ}.

(** ** Paper Lemma 4.7 (continued) — monotone convergence in the measure

    A standard fact from measure theory: for an increasing chain of
    finite measures [(µ_n)] with [fmeas]-sup [µ = fmeas_sup_ball
    uch ub1] and a non-negative measurable function [f], the
    sequence [∫_X f dµ_n] is increasing with limit [∫_X f dµ].

    mathcomp-analysis 1.16.0 provides [monotone_convergence] in the
    *function* argument but not directly in the *measure* argument.
    We prove the measure-direction MCT from scratch using
    [ge0_integral_measure_series] applied to the telescoping
    [fmeas_dseq] decomposition of the chain (paper §3.2.1's
    construction of [fmeas_sup_ball]). *)

Section IntegralMeasSup.
Local Open Scope ereal_scope.
Variables (R : realType) (disp : measure_display) (X : measurableType disp).
Variable u : nat -> fmeas R X.
Hypothesis uch : forall n, precone_le (u n) (u n.+1).
Hypothesis ub1 : forall n, (fmeas_norm (u n) <= 1)%R.

(** The integral of a non-negative measurable [f] against the
    [fmeas_sup_ball] of an increasing chain equals the infinite
    series of integrals against the difference measures. *)
Local Lemma integral_fmeas_sup_series (f : X -> \bar R) :
  (forall r, 0 <= f r) -> measurable_fun [set: X] f ->
  \int[fmeas_mu (fmeas_sup_ball uch ub1)]_(r in [set: X]) f r =
  \sum_(i <oo) \int[fmeas_dseq uch i]_(r in [set: X]) f r.
Proof.
move=> f_ge0 mf.
rewrite [LHS](_ : _ = \int[mseries (fmeas_dseq uch) 0]_(r in [set: X]) f r);
  last first.
  apply: eq_measure_integral => /= U mU _.
  rewrite [LHS]/= (fmeas_sup_ballE _ ub1 mU).
  by rewrite /fmeas_sup_meas_fun/=.
by rewrite ge0_integral_measure_series.
Qed.

(** Paper Lemma 4.7 (measure-direction MCT). Integrating [f] against
    [u n] gives the partial sum, hence converges to the series sum
    [∫[fmeas_sup_ball] f]. *)
Lemma integral_meas_sup (f : X -> \bar R) :
  (forall r, 0 <= f r) -> measurable_fun [set: X] f ->
  \int[fmeas_mu (u n)]_(r in [set: X]) f r @[n --> \oo]
    --> \int[fmeas_mu (fmeas_sup_ball uch ub1)]_(r in [set: X]) f r.
Proof.
move=> f_ge0 mf.
rewrite (integral_fmeas_sup_series f_ge0 mf).
(* By induction, \int[u n] f = \sum_(0 <= k < n.+1) \int[dseq k] f. *)
have stepE n :
  \int[fmeas_mu (u n)]_(r in [set: X]) f r =
  \sum_(0 <= k < n.+1) \int[fmeas_dseq uch k]_(r in [set: X]) f r.
  elim: n => [|n IH].
    by rewrite big_nat1.
  rewrite big_nat_recr//= -IH.
  have udiff : u n.+1 = fmeas_add (u n) (fmeas_diff uch n).
    exact: fmeas_diffE.
  rewrite udiff.
  have -> : fmeas_mu (fmeas_add (u n) (fmeas_diff uch n)) =
            measure_add (fmeas_mu (u n)) (fmeas_mu (fmeas_diff uch n))
            :> (_ -> _).
    by [].
  by rewrite ge0_integral_measure_add.
have ge0_g k : 0 <= \int[fmeas_dseq uch k]_(r in [set: X]) f r.
  by apply: integral_ge0 => r _; exact: f_ge0.
(* Rewrite goal to express LHS as the partial-sums sequence. *)
have under_eq :
  (fun n => \int[fmeas_mu (u n)]_(r in [set: X]) f r) =
  (fun n => \sum_(0 <= k < n.+1) \int[fmeas_dseq uch k]_(r in [set: X]) f r).
  by apply: funext; exact: stepE.
rewrite under_eq.
(* The shifted partial sums (a n.+1) converge to the same limit as
   the unshifted (a n), since shifting preserves convergence. *)
have nde : nondecreasing_seq
  (fun n => \sum_(0 <= k < n) \int[fmeas_dseq uch k]_(r in [set: X]) f r).
  apply/nondecreasing_seqP => n.
  by rewrite big_nat_recr//= leeDl//.
have cvg_psum :=
  ereal_nondecreasing_cvgn nde.
have lim_eq :
  ereal_sup (range (fun n => \sum_(0 <= k < n)
    \int[fmeas_dseq uch k]_(r in [set: X]) f r)) =
  \sum_(0 <= i <oo) \int[fmeas_dseq uch i]_(r in [set: X]) f r.
  apply/esym/cvg_lim; first exact: ereal_hausdorff.
  exact: cvg_psum.
rewrite -lim_eq.
rewrite (_ : (fun n => \sum_(0 <= k < n.+1)
              \int[fmeas_dseq uch k]_(r in [set: X]) f r) =
             (fun n => \sum_(0 <= k < n)
              \int[fmeas_dseq uch k]_(r in [set: X]) f r) \o S)//.
by rewrite cvg_shiftS.
Qed.

End IntegralMeasSup.

Arguments integral_meas_sup {R disp X} u uch ub1.

(** ** ω-continuity in [β] — Paper Lemma 4.7 (separate continuity, first arg)

    For an increasing chain of unit-ball measurable paths
    [(β_n)_{n ∈ ℕ}] with pointwise supremum [β], assuming
    additionally that each [β_n] admits an integral [x_n] over [µ],
    that the chain [(x_n)] is increasing and lies in the unit
    ball, the [cone_sup_ball] of [(x_n)] is the integral of the
    sup-path [β = cone_sup_ball ∘ (β_n)].

    The hypotheses on the chain [(x_n)] (monotonicity + unit ball)
    are exactly what would follow automatically from [iconeType]'s
    integrability axiom and Lemma 4.2 under appropriate
    normalization. We expose them as hypotheses to keep this proof
    self-contained: the [iconeType] wrapper [icone_integral_omega_B]
    discharges them on the spot. *)

(** ** Test-functional monotonicity along [precone_le]

    A test [m] is linear and non-negative, so it is monotone along
    the precone order: [precone_le x y → test_fun m s x ≤
    test_fun m s y]. Used in the MCT-based ω-continuity proof. *)

Section TestFunMonotone.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (C : MCone.type Ar) (X : ar_obj Ar).

Lemma test_fun_le (m : test_of Ar X C) (s : ar_carrier Ar X) (x y : C) :
  precone_le x y -> (test_fun m s x <= test_fun m s y)%R.
Proof.
case=> z ->.
rewrite test_linD lerDl; exact: test_ge0.
Qed.

End TestFunMonotone.

(** ** ω-continuity in [β] — Paper Lemma 4.7 (separate continuity, first arg)

    For an increasing chain of unit-ball measurable paths
    [(β_n)_{n ∈ ℕ}] with pointwise supremum [β = cone_sup_ball ∘
    (β_n)], the integrals [x_n] of [β_n] over [µ] form (under our
    additional hypotheses) an increasing unit-ball chain in [B],
    and the [cone_sup_ball] of [(x_n)] is the integral of [β].

    Proof strategy (paper §4, p. 1:25): combine
    [monotone_convergence] applied to the chain
    [(test_fun m s (β_n r))_n] of bounded non-negative measurable
    functions in [r], with the [test_cont] field of each test on
    the [B]-side chain [(x_n)]. The chain-monotonicity of [(x_n)]
    follows from a "residue" lemma on [path_integral_eq] that we
    do not yet have on file.

    TODO M3 wave 4: prove [integral_omega_cont_path] using
    [test_fun_le], [test_cont], [monotone_convergence], and
    [Pettis] on each [β_n]. The proof outline is:
    - Show that the pointwise chain [(test_fun m s (β_n r))_n] is
      nondecreasing and bounded by 1 (uses [test_fun_le] above).
    - The integrals [∫[µ] (test_fun m s (β_n r))%:E dr] form a
      monotone bounded chain.
    - By [monotone_convergence], the integral of
      [test_fun m s (betasup r)] (the pointwise sup) equals the
      [limn] of the [β_n]-integrals.
    - The chain [(test_fun m s (x_n))_n] converges to
      [test_fun m s (cone_sup_ball x_n …)] by [test_cont] +
      monotonicity.
    - By Pettis on each [β_n], [test_fun m s (x_n)
      = fine (∫[µ] (test_fun m s (β_n r))%:E dr)].
    - By [fine_cvg], the [fine] of the limit equals the limit of
      the [fine]s. *)

(** ** ω-continuity in [µ] — Paper Lemma 4.7 (separate continuity, second arg)

    For a fixed measurable path [β], an increasing chain of
    unit-ball finite measures [(µ_n)] has [fmeas_sup_ball µ_n]
    as its sup; the corresponding integrals form a chain in [B]
    whose [cone_sup_ball] is the integral of [β] against
    [fmeas_sup_ball µ_n].

    Proof strategy: apply [integral_meas_sup] (above) to the
    function [r ↦ test_fun m s (β r)] (which is non-negative
    measurable), getting:
    [∫[fmeas_sup_ball µ_n] _ = limn (∫[µ_n] _)]. Combined with
    Pettis and [test_fun_le] (as in the β-side proof above), this
    gives the witness equation.

    TODO M3 wave 4: prove [integral_omega_cont_meas] using
    [integral_meas_sup] and the same fine-cvg + test_cont
    bookkeeping as [integral_omega_cont_path]. *)

(** ** Joint measurability of the integration operator — Paper Lemma 4.7

    "For [Y ∈ Ar], [η ∈ Path(Y, Path(X, B))] and [κ ∈ Path(Y,
    FMeas(X))], the function [β = I^B_X ∘ ⟨η, κ⟩ : Y → B] is a
    measurable path."

    The proof of measurability of [(s', s) ↦ m s' (β s)] reduces,
    by [path_integral_eq], to the measurability of
    [(s', s) ↦ ∫ m(s', η(s, r)) κ(s, dr)], which is the kernel
    integral [s ↦ ∫ φ(s, r) κ(s, dr)] (Lemma 4.6, proved above as
    [kernel_integral_measurable]) with the joint state [(s', s)]
    folded into [s].

    TODO M3 wave 4: instantiate [kernel_integral_measurable] with
    [Y := (ar_carrier Y' * ar_carrier Y)%type] (as a product
    measurable space, via [ar_prod]) and
    [φ := λ (q, r). test_fun m q.1 (η q.2 r)]. The remaining
    bookkeeping is the joint-vs-section measurability of [η] (which
    [is_measurable_path η] provides through the
    [Path(Y, Path(X, B))] structure) and the fmeas-measurability
    of [κ] (from [is_measurable_path κ] applied to the [e_U] test
    family). *)
