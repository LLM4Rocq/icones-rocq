(** * Lemmas 4.6 / 4.7 — bilinearity, ω-continuity, measurability of [I^B_X]

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
      are monotone along the precone order; and
      [test_cone_sup_ball] — a test of a unit-ball sup is the [sup]
      of the tests along the chain (the shared step of both
      ω-continuity proofs below).

    - ω-continuity in [β] (proved): [integral_omega_cont_path] —
      Paper Lemma 4.7, separate continuity in the first argument.
    - ω-continuity in [µ] (proved): [integral_omega_cont_meas] —
      Paper Lemma 4.7, separate continuity in the second argument.
    - Joint measurability of [I^B_X ∘ ⟨η, κ⟩] (proved): see
      Section [JointMeasurability] near the end of the file.
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

Require Import Icones.prelude.nonneg_extra.
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
  measurable_fun setT
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
    measurable_fun setT (fun s => fmeas_mu (κ s) U).
Hypothesis κ_bound : exists M : R, forall s, fmeas_norm (κ s) <= M.

Local Open Scope ereal_scope.

(** The underlying [Y -> {measure set X -> \bar R}] view of [κ]. *)
Local Definition kernel46 (s : Y) : {measure set X -> \bar R} :=
  fmeas_mu (κ s).

Local Lemma kernel46_meas U : measurable U ->
  measurable_fun setT (kernel46 ^~ U).
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
  measurable_fun setT k ->
  measurable_fun setT
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
  measurable_fun setT φ ->
  measurable_fun setT
    (fun s => fine (\int[fmeas_mu (κ s)]_(r in [set: X]) (φ (s, r))%:E)).
Proof.
move=> φ_ge0 φ_le mφ.
have mEφ : measurable_fun setT (fun p => (φ p)%:E).
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
have mf1 : measurable_fun setT
             (fun r => (test_fun m (ar_zero_pt Ar) (β r))%:E).
  by apply/measurable_EFinP; exact: (measurable_test_path_section mM Hβ).
have mf2 : measurable_fun setT
             (fun _ : ar_carrier Ar X => M%:E).
  exact: measurable_cst.
rewrite ge0_fin_numE//.
apply: (le_lt_trans
  (y := \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X]) M%:E)).
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
have m1 : measurable_fun setT
            (fun r => (test_fun m s (β1 r))%:E).
  apply/measurable_EFinP.
  exact: (measurable_test_path_section mM Hβ1).
have m2 : measurable_fun setT
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
have mE : measurable_fun setT
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
have mE : measurable_fun setT
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
have mE : measurable_fun setT
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
have mE : measurable_fun setT
            (fun r => (test_fun m (ar_zero_pt Ar) (β r))%:E).
  by apply/measurable_EFinP; exact: (measurable_test_path_section mM Hβ_meas).
have HfT : (fmeas_mu µ [set: ar_carrier Ar X] \is a fin_num)%E.
  exact: fmeas_setT_fin.
rewrite -lee_fin fineK// EFinM /fmeas_norm fineK//.
have mc : measurable_fun setT
            (fun _ : ar_carrier Ar X => Mβ%:E).
  exact: measurable_cst.
apply: (le_trans
  (y := (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X]) Mβ%:E)%E)).
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
  (forall r, 0 <= f r) -> measurable_fun setT f ->
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
  (forall r, 0 <= f r) -> measurable_fun setT f ->
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

(** ** Tests commute with unit-ball sups

    A test is monotone ([test_fun_le]) and ω-continuous
    ([test_cont]), so its value on [cone_sup_ball u uch ub1] is
    exactly the supremum (in [R]) of its values along the chain. This
    is the single fact behind every "test of a sup-ball = sup of the
    tests" step in the ω-continuity proofs of Lemma 4.7 below. *)

Section TestConeSupBall.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (C : MCone.type Ar) (X : ar_obj Ar).

Lemma test_cone_sup_ball (m : test_of Ar X C) (s : ar_carrier Ar X)
    (u : nat -> C)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, (cone_norm (u n) <= 1)%R) :
  test_fun m s (cone_sup_ball u uch ub1) =
  sup (range (fun n => test_fun m s (u n))).
Proof.
set v : nat -> R := fun n => test_fun m s (u n).
have ub : has_ubound (range v).
  by exists (1%R : R) => y [n _ <-]; apply: test_le1; exact: ub1.
have nonempty : (range v) !=set0 by exists (v 0%N), 0%N.
apply: le_anti; apply/andP; split; last first.
  apply: ge_sup => //.
  move=> _ [n _ <-]; apply: test_fun_le; exact: cone_sup_ball_ub.
apply: test_cont => n.
apply: sup_upper_bound; first by split.
by exists n.
Qed.

End TestConeSupBall.

(** ** Residue extraction along the cone order — used in ω-continuity

    [precone_le x y] unfolds to [∃ z, y = x + z]. By [cid], we extract
    a sigma-type witness which is then used to build a "residue"
    function pointwise along an increasing chain of paths. *)

Section PreconeResidue.
Variables (R : realType) (P : preconeType R).

(** Sigma-type version of [precone_le]: extract the unique-up-to-
    cancellation residue [z] such that [y = x + z]. *)
Lemma precone_residue (x y : P) :
  precone_le x y -> { z : P | y = (x + z)%PC }.
Proof. exact: cid. Qed.

End PreconeResidue.

Arguments precone_residue {R P x y}.

(** ** Test-Pettis for arbitrary arity — Paper Def 4.1 reindexed

    Paper Def 4.1 gives a Pettis equation only for arity-0 tests. By
    (Mscomp), reindexing along a constant ar-hom [const_0Z z :
    ar_zero → Z] turns any [m : test_of Ar Z B] into an arity-0 test
    [test_reindex (const_0Z z) m], whose evaluation at [ar_zero_pt]
    coincides with [test_fun m z]. The reindexed test sits in
    [mcone_M (ar_zero Ar)] by (Mscomp), so [icone_integralP] applies. *)

Section TestPettisGen.
Variables (R : realType) (Ar : MeasSubcat R).

(** A general "constant at [z]" ar_hom from [ar_zero Ar] to any
    [Z ∈ Ar]. *)
Section ConstZeroZ.
Variables (Z : ar_obj Ar) (z : ar_carrier Ar Z).

Let const_0Z_fun : ar_carrier Ar (ar_zero Ar) -> ar_carrier Ar Z :=
  fun _ => z.

Local Lemma const_0Z_measurable :
  measurable_fun setT const_0Z_fun.
Proof. exact: measurable_cst. Qed.

HB.instance Definition _ :=
  isMeasurableFun.Build _ _ _ _ const_0Z_fun const_0Z_measurable.

Definition const_0Z : ar_hom Ar (ar_zero Ar) Z := const_0Z_fun.
End ConstZeroZ.

Variables (B : ICone.type Ar) (X : ar_obj Ar).
Variables (β : ar_carrier Ar X -> B) (Hβ : is_measurable_path β).
Variable µ : fmeas R (ar_carrier Ar X).

(** Paper Def 4.1 + (Mscomp): the Pettis equation lifts to any arity
    [Z] by reindexing the test along [const_0Z z]. *)
Lemma icone_integral_test_pettis (Z : ar_obj Ar)
    (m : test_of Ar Z B) (mM : mcone_M Z m) (z : ar_carrier Ar Z) :
  test_fun m z (icone_integral β Hβ µ) =
  fine (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X])
          (test_fun m z (β r))%:E).
Proof.
have mM0 : mcone_M (ar_zero Ar) (test_reindex (const_0Z z) m).
  exact: mcone_M_comp.
have := icone_integralP β Hβ µ (test_reindex (const_0Z z) m) mM0
                              (ar_zero_pt Ar).
by rewrite /test_reindex /= /test_reindex_fun /=.
Qed.

End TestPettisGen.

Arguments const_0Z {R Ar} Z z.
Arguments icone_integral_test_pettis
  {R Ar B X β} Hβ µ {Z} m mM z.

(** ** Integral chain monotonicity — Paper Lemma 4.7 helper

    If [β1 ≤p β2] pointwise (in the cone order on [B]) and both are
    measurable paths, then their integrals are comparable in the
    cone order: [icone_integral β1 µ ≤p icone_integral β2 µ].

    Proof: extract the pointwise residue [δ r] via [precone_residue],
    show [δ] is itself a measurable path (the joint test measurability
    is built from those of [β1] and [β2] via [test_linD]; the path
    norm of [δ] is bounded by that of [β2] via (Normp)), and apply
    [path_integral_eq_addB] to get
    [icone_integral β2 = icone_integral β1 + icone_integral δ]. *)

Section IntegralMonotone.
Local Open Scope ereal_scope.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (B : ICone.type Ar) (X : ar_obj Ar).
Variables (β1 β2 : ar_carrier Ar X -> B).
Variables (Hβ1 : is_measurable_path β1) (Hβ2 : is_measurable_path β2).
Variable µ : fmeas R (ar_carrier Ar X).
Hypothesis β_le : forall r, precone_le (β1 r) (β2 r).

(** The pointwise residue function: [δ r] is the [z] such that
    [β2 r = β1 r + z]. *)
Local Definition residue_fun : ar_carrier Ar X -> B :=
  fun r => proj1_sig (precone_residue (β_le r)).

Local Lemma residue_funE r : β2 r = (β1 r + residue_fun r)%PC.
Proof. exact: proj2_sig (precone_residue (β_le r)). Qed.

Local Lemma residue_le_β2 r : precone_le (residue_fun r) (β2 r).
Proof.
exists (β1 r); rewrite residue_funE.
by rewrite precone_addC.
Qed.

Local Lemma residue_norm_le r :
  (cone_norm (residue_fun r) <= cone_norm (β2 r))%R.
Proof. exact/cone_normp/residue_le_β2. Qed.

Local Lemma residue_is_path : is_measurable_path residue_fun.
Proof.
have [[M2 HM2] H2j] := Hβ2; split.
  exists M2 => r; apply: le_trans (residue_norm_le r) _; exact: HM2.
move=> Y m mM.
have [_ H1j] := Hβ1.
have m1 := H1j Y m mM.
have m2 := H2j Y m mM.
have eqE p : test_fun m p.1 (residue_fun p.2) =
             (test_fun m p.1 (β2 p.2) - test_fun m p.1 (β1 p.2))%R.
  case: p => s r /=.
  have := residue_funE r.
  move/(congr1 (test_fun m s)).
  rewrite test_linD => ->.
  by rewrite addrAC subrr add0r.
apply: (eq_measurable_fun
  (fun p : ar_carrier Ar Y * ar_carrier Ar X =>
    (test_fun m p.1 (β2 p.2) - test_fun m p.1 (β1 p.2))%R)).
  by move=> p _; rewrite eqE.
exact: measurable_funB.
Qed.

(** Paper Lemma 4.7 helper: integral chain monotonicity. *)
Lemma icone_integral_chain_le :
  precone_le (icone_integral β1 Hβ1 µ) (icone_integral β2 Hβ2 µ).
Proof.
exists (icone_integral residue_fun residue_is_path µ).
apply/esym/icone_integral_eqP.
have Hpie := path_integral_eq_addB Hβ1 residue_is_path
    (icone_integralP β1 Hβ1 µ)
    (icone_integralP residue_fun residue_is_path µ).
move=> m mM s; rewrite (Hpie m mM s).
congr fine; apply: eq_integral => r _.
by rewrite -residue_funE.
Qed.

End IntegralMonotone.

Arguments icone_integral_chain_le {R Ar B X β1 β2} Hβ1 Hβ2 µ.

(** ** Paper Lemma 4.7 (ω-continuity in [β]) — separate continuity, first arg

    For an increasing chain [(β_n)_{n ∈ ℕ}] of measurable paths
    bounded by 1 in cone-norm pointwise, with pointwise supremum
    path [βsup r := cone_sup_ball (β_n r) …] (the unit-ball sup),
    and assuming [βsup] is itself a measurable path, the
    [cone_sup_ball] of the integral chain [x_n := icone_integral
    (β_n) _ µ] coincides with [icone_integral βsup _ µ]. *)

Section OmegaContPath.
Local Open Scope ereal_scope.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (B : ICone.type Ar) (X : ar_obj Ar).
Variable β : nat -> ar_carrier Ar X -> B.
Hypothesis Hβ : forall n, is_measurable_path (β n).
Hypothesis β_chain : forall n r, precone_le (β n r) (β n.+1 r).
Hypothesis β_bound : forall n r, (cone_norm (β n r) <= 1)%R.
Variable µ : fmeas R (ar_carrier Ar X).
Hypothesis µ_norm : (fmeas_norm µ <= 1)%R.

(** The pointwise unit-ball supremum of the chain [β]. *)
Local Definition β_sup_fun : ar_carrier Ar X -> B :=
  fun r => cone_sup_ball (fun n => β n r) (fun n => β_chain n r)
                          (fun n => β_bound n r).

Hypothesis Hβsup : is_measurable_path β_sup_fun.

(** Integrals of each [β n]. *)
Local Definition int_β (n : nat) : B := icone_integral (β n) (Hβ n) µ.

(** Chain monotonicity of the integral sequence (uses
    [icone_integral_chain_le]). *)
Local Lemma int_β_chain n : precone_le (int_β n) (int_β n.+1).
Proof. exact: icone_integral_chain_le. Qed.

(** Unit-ball bound on each integral, using Paper Lemma 4.2. *)
Local Lemma int_β_bound n : (cone_norm (int_β n) <= 1)%R.
Proof.
have H := path_integral_norm_le (Mβ := 1) (β_bound n)
            (Hβ n) (int_β n) (icone_integralP (β n) (Hβ n) µ).
apply: le_trans H _.
by rewrite mul1r.
Qed.

(** Helper: pointwise test-value of the [β]-sup-path equals the sup
    of pointwise test-values along the chain. *)
Local Lemma test_β_sup_pt
    (m : test_of Ar (ar_zero Ar) B) (r : ar_carrier Ar X) :
  test_fun m (ar_zero_pt Ar) (β_sup_fun r) =
  sup (range (fun n => test_fun m (ar_zero_pt Ar) (β n r))).
Proof. exact: test_cone_sup_ball. Qed.

(** Helper: same for the integral chain. *)
Local Lemma test_int_β_sup_pt
    (m : test_of Ar (ar_zero Ar) B) :
  test_fun m (ar_zero_pt Ar) (cone_sup_ball int_β int_β_chain int_β_bound) =
  sup (range (fun n => test_fun m (ar_zero_pt Ar) (int_β n))).
Proof. exact: test_cone_sup_ball. Qed.

(** Paper Lemma 4.7 (ω-continuity in [β]). *)
Lemma integral_omega_cont_path :
  cone_sup_ball int_β int_β_chain int_β_bound =
  icone_integral β_sup_fun Hβsup µ.
Proof.
apply: mcone_M_sep => m mM.
set s0 := ar_zero_pt Ar.
rewrite test_int_β_sup_pt.
rewrite (icone_integral_test_pettis Hβsup µ m mM s0).
pose un (n : nat) (r : ar_carrier Ar X) : \bar R :=
  (test_fun m s0 (β n r))%:E.
pose fsup r : \bar R := (test_fun m s0 (β_sup_fun r))%:E.
have un_meas n : measurable_fun setT (un n).
  by apply/measurable_EFinP;
    exact: (measurable_test_path_section mM (Hβ n)).
have un_ge0 (n : nat) r : 0 <= un n r.
  by rewrite lee_fin; apply: test_ge0.
have un_homo r :
  {homo (un^~ r) : n m0 / (n <= m0)%N >-> n <= m0}.
  apply/nondecreasing_seqP => n; rewrite /un lee_fin.
  apply: test_fun_le; exact: β_chain.
have testβ_cvg_real r :
  (fun n => test_fun m s0 (β n r)) x @[x --> \oo] -->
  (test_fun m s0 (β_sup_fun r) : R^o).
  have nd : {homo (fun n => test_fun m s0 (β n r))
                 : n m0 / (n <= m0)%N >-> (n <= m0)%R}.
    apply/nondecreasing_seqP => n; apply: test_fun_le; exact: β_chain.
  have ub : has_ubound (range (fun n => test_fun m s0 (β n r))).
    exists (1%R : R) => x [n _ <-]; apply: test_le1; exact: β_bound.
  rewrite test_β_sup_pt; exact: nondecreasing_cvgn.
have un_cvg r : (un^~ r) x @[x --> \oo] --> fsup r.
  rewrite /un /fsup.
  apply: cvg_EFin; first by apply: nearW => n; rewrite fin_numE.
  rewrite /=.
  under eq_fun do rewrite /=.
  exact: testβ_cvg_real.
have un_lim r : limn (un^~ r) = fsup r.
  by apply/cvg_lim => //; exact: ereal_hausdorff.
have MCT : \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X]) fsup r =
           limn (fun n => \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X])
                              un n r).
  have HMC := monotone_convergence (fmeas_mu µ) (D := [set: ar_carrier Ar X])
                measurableT un_meas (fun n r _ => un_ge0 n r)
                (fun r _ => un_homo r).
  rewrite -HMC; apply: eq_integral => r _; by rewrite -un_lim.
have pet n : test_fun m s0 (int_β n) =
             fine (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X]) un n r).
  by rewrite /int_β; exact: (icone_integralP (β n) (Hβ n) µ m mM s0).
have intβ_fin n : (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X]) un n r
                  \is a fin_num).
  apply: test_int_fin => //; exists 1%R; exact: β_bound.
have intβsup_fin : (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X]) fsup r
                   \is a fin_num).
  have [[M HM] _] := Hβsup.
  apply: test_int_fin => //; exists M; exact: HM.
have int_β_cvg :
  (fun n => \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X]) un n r) x
   @[x --> \oo] --> \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X]) fsup r.
  have HC := cvg_monotone_convergence (D := [set: ar_carrier Ar X])
               (mu := fmeas_mu µ) measurableT un_meas
               (fun n r _ => un_ge0 n r) (fun r _ => un_homo r).
  have HE : \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X])
              (fun x : ar_carrier Ar X => limn (un^~ x)) r =
            \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X]) fsup r.
    by apply: eq_integral => r _; rewrite -un_lim.
  by rewrite -HE.
have fcvg : (fun n => fine (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X])
                              un n r)) x @[x --> \oo] -->
            (fine (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X]) fsup r)
              : R^o).
  have HEFin : \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X]) fsup r =
               (fine
                  (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X]) fsup r))
                 %:E.
    by rewrite fineK.
  rewrite HEFin in int_β_cvg.
  exact: (fine_cvg int_β_cvg).
have nd_int : {homo (fun n => test_fun m s0 (int_β n))
              : n m0 / (n <= m0)%N >-> (n <= m0)%R}.
  apply/nondecreasing_seqP => n; apply: test_fun_le; exact: int_β_chain.
have ub_int : has_ubound (range (fun n => test_fun m s0 (int_β n))).
  exists (1%R : R) => x [n _ <-]; apply: test_le1; exact: int_β_bound.
have sup_cvg := nondecreasing_cvgn nd_int ub_int.
have sup_eq : sup (range (fun n => test_fun m s0 (int_β n))) =
              fine (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X]) fsup r).
  have aux :
    (fun n => test_fun m s0 (int_β n)) x @[x --> \oo] -->
    (fine (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X]) fsup r) : R^o).
    apply: cvg_trans fcvg.
    by apply: near_eq_cvg; apply: nearW => n; rewrite pet.
  exact: (@cvg_unique R^o (@Rhausdorff R) _ _ _ _ sup_cvg aux).
by rewrite sup_eq.
Qed.

End OmegaContPath.

(** ** Paper Lemma 4.7 (ω-continuity in [µ]) — separate continuity, second arg

    For a fixed measurable path [β] bounded in cone-norm by 1, an
    increasing chain [(µ_n)] of finite measures with [fmeas_norm
    µ_n ≤ 1], the integrals form a chain in [B] whose [cone_sup_ball]
    is the integral of [β] against [fmeas_sup_ball µ_n]. *)

Section OmegaContMeas.
Local Open Scope ereal_scope.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (B : ICone.type Ar) (X : ar_obj Ar).
Variables (β : ar_carrier Ar X -> B) (Hβ : is_measurable_path β).
Hypothesis β_bound : forall r, (cone_norm (β r) <= 1)%R.
Variable µn : nat -> fmeas R (ar_carrier Ar X).
Hypothesis µn_chain : forall n, precone_le (µn n) (µn n.+1).
Hypothesis µn_bound : forall n, (fmeas_norm (µn n) <= 1)%R.

(** Integral of [β] against each [µn n]. *)
Local Definition int_µ (n : nat) : B := icone_integral β Hβ (µn n).

(** Chain monotonicity: integrating against a larger measure gives a
    larger integral. Proved via additivity in [µ]. *)
Local Lemma int_µ_chain n : precone_le (int_µ n) (int_µ n.+1).
Proof.
have [w Hw] := µn_chain n.
exists (icone_integral β Hβ w); apply/esym/icone_integral_eqP.
have Hpe : path_integral_eq β (µn n.+1)
             (precone_add (int_µ n) (icone_integral β Hβ w)).
  rewrite Hw.
  apply: path_integral_eq_addmu => //; exact: icone_integralP.
exact: Hpe.
Qed.

(** Unit-ball bound: using Paper Lemma 4.2 with [µ_n ≤ 1] and
    [β ≤ 1] gives [‖int_µ n‖ ≤ 1]. *)
Local Lemma int_µ_bound n : (cone_norm (int_µ n) <= 1)%R.
Proof.
have H := path_integral_norm_le (Mβ := 1) β_bound Hβ
            (int_µ n) (icone_integralP β Hβ (µn n)).
apply: le_trans H _.
by rewrite mul1r.
Qed.

(** Paper Lemma 4.7 (ω-continuity in [µ]). *)
Lemma integral_omega_cont_meas :
  cone_sup_ball int_µ int_µ_chain int_µ_bound =
  icone_integral β Hβ (fmeas_sup_ball µn_chain µn_bound).
Proof.
apply: mcone_M_sep => m mM.
set s0 := ar_zero_pt Ar.
rewrite (icone_integral_test_pettis Hβ
           (fmeas_sup_ball µn_chain µn_bound) m mM s0).
(* LHS: test of cone_sup_ball — sup of tests of int_µ n *)
have test_sup := test_cone_sup_ball m s0 int_µ_chain int_µ_bound.
rewrite test_sup.
(* Define the test integrand *)
pose f r : \bar R := (test_fun m s0 (β r))%:E.
have f_meas : measurable_fun setT f.
  by apply/measurable_EFinP; exact: (measurable_test_path_section mM Hβ).
have f_ge0 r : 0 <= f r by rewrite lee_fin; apply: test_ge0.
(* Use integral_meas_sup *)
have int_cvg :
  (fun n => \int[fmeas_mu (µn n)]_(r in [set: ar_carrier Ar X]) f r) x
   @[x --> \oo] -->
  \int[fmeas_mu (fmeas_sup_ball µn_chain µn_bound)]_(r in [set: _]) f r.
  exact: (integral_meas_sup µn µn_chain µn_bound f f_ge0 f_meas).
(* finite-num facts *)
have fin_µn n : \int[fmeas_mu (µn n)]_(r in [set: ar_carrier Ar X]) f r
                \is a fin_num.
  apply: test_int_fin => //; exists 1%R; exact: β_bound.
set µsup := fmeas_sup_ball µn_chain µn_bound.
have fin_µsup :
  \int[fmeas_mu µsup]_(r in [set: ar_carrier Ar X]) f r \is a fin_num.
  apply: test_int_fin => //; exists 1%R; exact: β_bound.
(* fine convergence *)
have fcvg : (fun n => fine
              (\int[fmeas_mu (µn n)]_(r in [set: ar_carrier Ar X]) f r)) x
            @[x --> \oo] -->
            (fine (\int[fmeas_mu µsup]_(r in [set: ar_carrier Ar X]) f r)
              : R^o).
  have HE : \int[fmeas_mu µsup]_(r in [set: ar_carrier Ar X]) f r =
            (fine (\int[fmeas_mu µsup]_(r in [set: ar_carrier Ar X]) f r))%:E.
    by rewrite fineK.
  rewrite HE in int_cvg.
  exact: (fine_cvg int_cvg).
(* Pettis on each int_µ n *)
have pet n : test_fun m s0 (int_µ n) =
             fine (\int[fmeas_mu (µn n)]_(r in [set: ar_carrier Ar X]) f r).
  by rewrite /int_µ; exact: (icone_integralP β Hβ (µn n) m mM s0).
have nd_int : {homo (fun n => test_fun m s0 (int_µ n))
              : n m0 / (n <= m0)%N >-> (n <= m0)%R}.
  apply/nondecreasing_seqP => n; apply: test_fun_le; exact: int_µ_chain.
have ub_int : has_ubound (range (fun n => test_fun m s0 (int_µ n))).
  exists (1%R : R) => x [n _ <-]; apply: test_le1; exact: int_µ_bound.
have sup_cvg := nondecreasing_cvgn nd_int ub_int.
have aux :
  (fun n => test_fun m s0 (int_µ n)) x @[x --> \oo] -->
  (fine (\int[fmeas_mu µsup]_(r in [set: ar_carrier Ar X]) f r) : R^o).
  apply: cvg_trans fcvg.
  by apply: near_eq_cvg; apply: nearW => n; rewrite pet.
exact: (@cvg_unique R^o (@Rhausdorff R) _ _ _ _ sup_cvg aux).
Qed.

End OmegaContMeas.

(** ** Paper Lemma 4.7 (joint measurability of the integration operator)

    Given a "kernel" of measurable paths [β : S -> ar_carrier X -> B]
    parameterised by a measurable space [S], a kernel measure-family
    [κ : S -> fmeas R (ar_carrier X)] uniformly bounded, and any
    test [m : test_of Ar Z B], the function

      [(z, s) ↦ test_fun m z (icone_integral (β s) _ (κ s))]

    is jointly measurable on [ar_carrier Z × S], provided the joint
    test-measurability of [(z, s, r) ↦ test_fun m z (β s r)] is
    given.

    Proof: by [icone_integral_test_pettis], the test-value of the
    integral equals [fine (∫[κ s] (test_fun m z (β s r))%:E)], which
    is jointly measurable in [(z, s)] by paper Lemma 4.6
    ([kernel_integral_measurable]) with [Y := Z × S] and
    [φ ((z, s), r) := test_fun m z (β s r)]. *)

Section JointMeasurability.
Local Open Scope ereal_scope.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (B : ICone.type Ar) (X : ar_obj Ar).
Variables (d : measure_display) (S : measurableType d).
Variable β : S -> ar_carrier Ar X -> B.
Hypothesis Hβ : forall s, is_measurable_path (β s).
Variable κ : S -> fmeas R (ar_carrier Ar X).
Variable Z : ar_obj Ar.
Variable m : test_of Ar Z B.
Hypothesis mM : mcone_M Z m.

(** Paper Lemma 4.7 (joint measurability).

    The user provides:
    - [κ_meas]: each set-evaluation of [κ] is measurable in [s].
    - [κ_bound]: a uniform total-mass bound on [κ].
    - [Hjoint]: joint measurability of [(z, s, r) ↦ test_fun m z (β s r)]
      on [Z × S × X].
    - [Mβ_bd]: a uniform pointwise bound for the test integrand
      (typically [cone_norm (β s r) ≤ M] from the path bound). *)
Lemma icone_integral_joint_measurable :
  (forall U, measurable U ->
     measurable_fun setT (fun s => fmeas_mu (κ s) U)) ->
  (exists M : R, forall s, (fmeas_norm (κ s) <= M)%R) ->
  measurable_fun
    [set: (ar_carrier Ar Z * (S * ar_carrier Ar X))%type]
    (fun p => test_fun m p.1 (β p.2.1 p.2.2)) ->
  (exists M : R, forall z s r,
    (test_fun m z (β s r) <= M)%R) ->
  measurable_fun
    [set: (ar_carrier Ar Z * S)%type]
    (fun p => test_fun m p.1 (icone_integral (β p.2) (Hβ p.2) (κ p.2))).
Proof.
move=> κ_meas κ_bound Hjoint [Mβ HMβ].
(* Rewrite the integrand via [icone_integral_test_pettis] *)
pose g (p : ar_carrier Ar Z * S) : R :=
  fine (\int[fmeas_mu (κ p.2)]_(r in [set: ar_carrier Ar X])
          (test_fun m p.1 (β p.2 r))%:E).
have rewE p :
  test_fun m p.1 (icone_integral (β p.2) (Hβ p.2) (κ p.2)) = g p.
  by rewrite /g; exact: icone_integral_test_pettis.
apply: (eq_measurable_fun g); first by move=> p _; rewrite -rewE.
(* Apply [kernel_integral_measurable] with joint state (z, s) *)
pose ρ (p : ar_carrier Ar Z * S) : fmeas R (ar_carrier Ar X) := κ p.2.
have ρ_meas : forall U, measurable U ->
    measurable_fun setT
                   (fun p => fmeas_mu (ρ p) U).
  move=> U mU.
  apply: (measurableT_comp (f := fun s => fmeas_mu (κ s) U)).
  - exact: κ_meas.
  - exact: measurable_snd.
have ρ_bound : exists M : R, forall p, (fmeas_norm (ρ p) <= M)%R.
  have [M HM] := κ_bound.
  by exists M => p; exact: HM.
pose φ (q : (ar_carrier Ar Z * S) * ar_carrier Ar X) : R :=
  test_fun m q.1.1 (β q.1.2 q.2).
have φ_ge0 q : (0 <= φ q)%R by rewrite /φ; exact: test_ge0.
have φ_le_M q : (φ q <= Mβ)%R by rewrite /φ; exact: HMβ.
(* measurability of φ *)
have φ_meas : measurable_fun
  [set: ((ar_carrier Ar Z * S) * ar_carrier Ar X)%type] φ.
  rewrite /φ.
  (* φ = (fun p => test_fun m p.1 (β p.2.1 p.2.2)) composed with
     ((z,s),r) ↦ (z, (s, r)) *)
  pose ψ (q : ((ar_carrier Ar Z * S) * ar_carrier Ar X)) :
    ar_carrier Ar Z * (S * ar_carrier Ar X) :=
    (q.1.1, (q.1.2, q.2)).
  have ψ_meas : measurable_fun
    [set: ((ar_carrier Ar Z * S) * ar_carrier Ar X)%type] ψ.
    rewrite /ψ.
    apply: measurable_fun_pair.
    + apply: (measurableT_comp (f := fst)).
      * exact: measurable_fst.
      * exact: measurable_fst.
    + apply: measurable_fun_pair.
      * apply: (measurableT_comp (f := snd)).
        - exact: measurable_snd.
        - exact: measurable_fst.
      * exact: measurable_snd.
  pose hf (p : ar_carrier Ar Z * (S * ar_carrier Ar X)) : R :=
    test_fun m p.1 (β p.2.1 p.2.2).
  have -> :
    (fun q : ((ar_carrier Ar Z * S) * ar_carrier Ar X)%type =>
       test_fun m q.1.1 (β q.1.2 q.2)) = hf \o ψ.
    by apply: funext => q; rewrite /hf /ψ.
  by apply: measurableT_comp; [exact: Hjoint|exact: ψ_meas].
(* Conclude via kernel_integral_measurable *)
exact: (kernel_integral_measurable ρ ρ_meas ρ_bound φ Mβ φ_ge0 φ_le_M φ_meas).
Qed.

End JointMeasurability.

Arguments icone_integral_joint_measurable
  {R Ar B X d S} β Hβ κ {Z} m mM.
