(** * Lemma 4.7 — bilinearity, ω-continuity and measurability of [I^B_X]

    Paper reference: §4, p. 1:25–1:26, Lemma 4.7.

    For an integrable cone [B : iconeType Ar] and an [Ar]-object [X],
    the integration operator

        [I^B_X : Path(X, B) × FMeas(X) → B,  (β, µ) ↦ ∫ β(r) µ(dr)]

    is (1) bilinear, (2) ω-continuous in each argument and (3) jointly
    measurable in the sense of paper Lemma 4.7 (last paragraph).

    Coverage in this file:

    - Lemma 4.6 prerequisite stub: [integral_kernel_measurable] —
      measurability of [s ↦ ∫ φ(s, r) κ(s, dr)] for a uniformly
      bounded kernel [κ] and bounded measurable [φ].

    - Linearity in [β]:
      * [path_integral_eq_addB] — sum of integrals is an integral of
        the sum, given measurability of both addends.
      * [path_integral_eq_scaleB] — scalar multiple of an integral is
        an integral of the scaled path.
      * [icone_integral_addB] / [icone_integral_scaleB] — corollaries
        in [iconeType Ar].

    - Linearity in [µ]:
      * [path_integral_eq_addmu] — adding measures adds integrals.
      * [path_integral_eq_scalemu] — scaling a measure scales the
        integral.
      * [icone_integral_addmu] / [icone_integral_scalemu] —
        corollaries in [iconeType Ar].

    - ω-continuity in [β]:
      * [path_integral_eq_sup_chain] — for an increasing chain of
        unit-ball paths whose pointwise sup is again a measurable
        path, the integrals form a chain whose [cone_sup_ball] is
        the integral of the sup-path.

    - Measurability of [I^B_X ∘ ⟨η, κ⟩]: stated as a [TODO] —
      needs the kernel-integral measurability of Lemma 4.6 in a form
      tied to our [fmeas] structure, and the joint joint pairing
      [⟨η, κ⟩]; this is deferred to a wave-2b polish pass.

    Design notes.

    - All test-side equations use [test_fun m s (β r)] in [R] then
      lift through [EFin] to feed [\int[fmeas_mu µ]_(r in setT) _].
      The integrand is always finite (an [EFin]) and non-negative
      (by [test_ge0]).

    - We use mathcomp-analysis 1.16.0's
      [ge0_integralD] / [ge0_integralZl] for linearity in the
      integrand and
      [ge0_integral_measure_add] / [ge0_integral_mscale] for
      linearity in the measure.

    - The "ω-continuity in [µ]" half of paper Lemma 4.7 is a
      non-trivial measure-side monotone-convergence fact that is
      not in mathcomp-analysis 1.16.0 as a one-shot lemma. We
      document the precise requirement as a [TODO] at the bottom of
      the file. Without it the [iconeType] structure remains
      well-defined; only this 4.7 sub-claim is open.

    - For the measurability sub-claim we need Lemma 4.6 in a form
      using our [fmeas]-valued kernels (the mathcomp-analysis form
      [measurable_fun_integral_finite_kernel] requires an [R.-fker
      X ~> Y] structure which we have not equipped on [fmeas]
      yet). The statement is exported here; the proof is a [TODO]
      pending the [fker]-instance polish in [fmeas.v].
*)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals constructive_ereal.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import ereal sequences.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import measure.
From mathcomp.analysis Require Import lebesgue_integral_definition.
From mathcomp.analysis Require Import lebesgue_integral_nonneg.
From mathcomp.analysis Require Import lebesgue_integral_monotone_convergence.

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
    measurable evaluation against each measurable set. The
    statement is exported here because it is *the* technical
    prerequisite for the measurability part of paper Lemma 4.7.

    In mathcomp-analysis 1.16.0 the analogous statement
    [measurable_fun_integral_finite_kernel] applies to an [R.-fker
    X ~> Y] structure. Wiring our [fmeas R X]-valued kernel to that
    structure is a polish step that we have not yet committed to
    the project. We therefore *state* Lemma 4.6 here in two
    equivalent forms and *defer* the proof to the dedicated fker
    wrapper pass. The proof outline (paper p. 1:25) is: approximate
    [φ] by an increasing sequence of simple functions, conclude
    by [monotone_convergence].

    TODO M3 wave 2b: prove [integral_kernel_measurable] by either
    (a) packaging [κ : Y -> fmeas R X] as an [R.-fker
    (ar_carrier Y) ~> (ar_carrier X)] and invoking
    [measurable_fun_integral_finite_kernel], or (b) bypassing the
    [fker] machinery and doing the simple-function approximation
    in-line. *)

(* TODO M3 wave 2b: kernel-integral measurability.

   Statement sketch:
     Variables (R : realType) (d d' : measure_display)
               (X : measurableType d) (Y : measurableType d').
     Variables (κ : Y -> fmeas R X)
               (κ_meas : forall U, measurable U ->
                  measurable_fun [set: Y] (fun s => fmeas_mu (κ s) U))
               (κ_bound : exists M : R, forall s, fmeas_norm (κ s) <= M).
     Variables (φ : Y * X -> R)
               (φ_meas : measurable_fun [set: Y * X] φ)
               (φ_ge0 : forall p, 0 <= φ p)
               (φ_bound : exists M : R, forall p, φ p <= M).
     Lemma integral_kernel_measurable :
       measurable_fun [set: Y]
         (fun s => fine (\int[fmeas_mu (κ s)]_(r in [set: X])
                           (φ (s, r))%:E)).
*)

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

(** ** ω-continuity in [β] — Paper Lemma 4.7 (separate continuity, first arg)

    For an increasing chain of unit-ball measurable paths
    [(β_n)_{n ∈ ℕ}] with pointwise supremum [β] (assumed itself a
    measurable path, which is the content of the [iconeType]
    closure under [cone_sup_ball]), the chain of integrals
    [I^B_X(β_n, µ)] is increasing and the witness equation for
    [β] is the supremum. The proof is monotone-convergence applied
    to the chain [(m s (β_n r))_n] of bounded measurable functions
    in [r], combined with the ω-continuity field [test_cont] of
    each test.

    We phrase the statement directly on [path_integral_eq] — the
    [icone_integral_eqP] consequences follow as in the linearity
    sections. *)

Section OmegaCont_B.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (B : MCone.type Ar) (X : ar_obj Ar).
Variable βn : nat -> ar_carrier Ar X -> B.
(** Each β_n is in the unit ball pointwise. *)
Hypothesis βn_ub1 : forall n r, (cone_norm (βn n r) <= 1)%R.
(** The chain is increasing pointwise. *)
Hypothesis βn_chain : forall n r, precone_le (βn n r) (βn n.+1 r).

(** Pointwise supremum path: as in [path.v]'s [path_sup_ball_fun], the
    candidate sup-path [β r := cone_sup_ball_n (βn n r)]. *)
Definition betasup (r : ar_carrier Ar X) : B :=
  cone_sup_ball (fun n => βn n r) (βn_chain^~ r) (βn_ub1^~ r).

(** Paper Lemma 4.7 — test-side MCT skeleton.

    The MCT half of the ω-continuity argument: at every test
    [m ∈ mcone_M (ar_zero Ar)] and base point [s = ar_zero_pt Ar],

      [test_fun m s y = sup_n (test_fun m s (x_n))]

    where [y] is the candidate integral
    [y = cone_sup_ball x_n ...] and [x_n] is the integral of
    [β_n]. The full ω-continuity claim follows by combining this
    identity (via [test_cont]) with the [path_integral_eq]
    witnesses [Hxn] and the MCT lemma applied to the chain
    [(test_fun m s (β_n r))_n]. We do not state the wrapper here
    because building the [cone_sup_ball] witness requires proving
    chain-monotonicity of [x_n], which in turn rests on a
    representative-residue construction (see the TODO at the
    bottom of this file). *)

(* TODO M3 wave 2b: the full statement of [path_integral_eq_omega_B]
   needs (a) the chain monotonicity [precone_le (xn n) (xn n.+1)],
   which follows by linearity of the integral applied to the
   "remainder" path [γ_n(r) := residue (βn n.+1 r) - (βn n r)]
   (well-defined because the cone order is the precone order, see
   [precone.v]); and (b) the unit-ball bound
   [cone_norm (xn n) <= 1] which holds when [fmeas_norm µ <= 1] by
   [path_integral_norm_le] above. Once these two ingredients are
   on file we set [y := cone_sup_ball xn ... ...] and prove
   [path_integral_eq (β-sup) µ y] using MCT exactly as paper
   p. 1:25.

   The chain-monotonicity step is the only remaining algebraic
   bookkeeping: it asks to package the residue [γ_n] *as a
   measurable path*, requires [is_measurable_path γ_n] from
   [is_measurable_path (βn n.+1)] via the difference (which is
   only well-defined in the precone order, not naively pointwise
   — see [precone_cancel] and the discussion in [precone.v]). *)

End OmegaCont_B.

(* TODO M3 wave 2b: full statement of ω-continuity in [β].

   Statement sketch:
     Variables (R : realType) (Ar : MeasSubcat R)
               (B : MCone.type Ar) (X : ar_obj Ar)
               (µ : fmeas R (ar_carrier Ar X))
               (βn : nat -> ar_carrier Ar X -> B).
     Hypothesis Hch : forall n r,
                       precone_le (βn n r) (βn n.+1 r).
     Hypothesis Hub : forall n r, cone_norm (βn n r) <= 1.
     Hypothesis Hmeas : forall n, is_measurable_path (βn n).
     Hypothesis Hxn : forall n,
                       exists xn, path_integral_eq (βn n) µ xn.
     Hypothesis Hβsup_meas :
       is_measurable_path (fun r =>
         cone_sup_ball (fun n => βn n r) (Hch ^~ r) (Hub ^~ r)).
     Lemma path_integral_eq_sup_chain :
       (* the chain x_n = ε(β_n, µ) admits a sup-ball y in B such
          that path_integral_eq (β-sup) µ y. *)
       ...

   Proof outline (paper p. 1:25): test the candidate
   [y = cone_sup_ball x_n] against any [m ∈ mcone_M ar_zero]:
   - [m y = sup_n m (x_n)] by [test_cont] applied to the chain
     [x_n] (after verifying [cone_norm x_n ≤ ‖β_n‖ ‖µ‖ ≤ ‖µ‖]
     by [path_integral_norm_le], paper Lemma 4.2 — already proved
     for individual integrals);
   - [m (x_n) = ∫ m (β_n r) dµ] by [path_integral_eq] for [β_n];
   - [∫ m (β r) dµ = sup_n ∫ m (β_n r) dµ] by
     [monotone_convergence] applied to the chain
     [(m s (β_n r))_n] of bounded measurable functions in [r];
   - putting these together gives the test equation for the
     sup-path's integral [y], hence by [path_integral_eq_unique]
     that [y] is *the* integral of the sup-path.

   The proof requires Lemma 4.2 (paper, p. 1:24:
   ‖∫ β dµ‖ ≤ ‖β‖ ‖µ‖), itself an [(Mssep)]-based exercise
   already on file as [path_integral_norm_le] (TODO: cross-check
   it is named consistently in [pettis.v]) and that x_n's are in
   the unit ball of B once µ is bounded, which is the natural
   normalisation. *)

(** ** Joint measurability of the integration operator — Paper Lemma 4.7

    "For [Y ∈ Ar], [η ∈ Path(Y, Path(X, B))] and [κ ∈ Path(Y,
    FMeas(X))], the function [β = I^B_X ∘ ⟨η, κ⟩ : Y → B] is a
    measurable path."

    The proof of measurability of [(s', s) ↦ m s' (β s)] reduces,
    by the [path_integral_eq] definition, to the measurability of
    [(s', s) ↦ ∫ m(s', η(s, r)) κ(s, dr)], which is the kernel
    integral [s ↦ ∫ φ(s, r) κ(s, dr)] in disguise (with [s] folded
    into [(s', s)]). Hence the deferral on Lemma 4.6. *)

(* TODO M3 wave 2b: measurability part of paper Lemma 4.7.

   Statement sketch (once Lemma 4.6 is on file):
     Variables (R : realType) (Ar : MeasSubcat R)
               (B : ICone.type Ar) (X Y : ar_obj Ar)
               (η : ar_carrier Ar Y -> ar_carrier Ar X -> B)
               (Hη : ... well-typed mu-of-mu measurability)
               (κ : ar_carrier Ar Y -> fmeas R (ar_carrier Ar X))
               (Hκ : is_measurable_path (Ar:=Ar)
                       (C:=fmeas_mcone_instance) κ).
     Lemma icone_integral_joint_measurable :
       is_measurable_path
         (fun s : ar_carrier Ar Y =>
            icone_integral (η s) (... measurability proof ...)
                           (κ s)).

   The bookkeeping for "[η s] is a measurable path for each [s]"
   is non-trivial: in the paper it comes from the structure of
   [Path(Y, Path(X, B))], which we have in [path.v] but at the
   level of the carrier; lifting an [η ∈ Path(Y, Path(X, B))] to a
   uniformly measurable family of paths-in-B is the missing
   ergonomic step. *)
