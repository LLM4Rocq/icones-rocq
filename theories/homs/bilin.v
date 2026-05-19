(** * Paper Theorem 6.1 — [Path(X, B) ≃ FMeas(X) ⊸ B]

    Paper reference: §6, lines 2835–3040 of [paper/icones.txt].

    For [X : ar_obj Ar] and [B : ICone.type Ar], the paper builds
    an isomorphism in [MCones] between [path_car Ar X B] and
    [linhom_car Ar (fmeas R (ar_carrier Ar X)) B] via the
    integration operator

      [I^B_X(β)(µ) := icone_integral β _ µ]

    and its inverse

      [K^B_X(f)(r) := f (\d_r)].

    Coverage in this file.

    - [dirac_fmeas r] — paper §6 paragraph 1: the canonically-
      extended Dirac mass on [ar_carrier Ar X] at point [r], packaged
      as an element of the [fmeas R (ar_carrier Ar X)] cone. The
      underlying measure agrees with mathcomp-analysis's [\d_r] on
      measurable sets and is zero off the σ-algebra (the [fmeas]
      canonicality invariant).

    - [dirac_path X] — paper §6 paragraph 1: the path
      [δ_X : ar_carrier X → fmeas R (ar_carrier X)] sending [r] to
      [dirac_fmeas r]. Bounded by [1] and a measurable path, hence
      a [path_car Ar X (fmeas R (ar_carrier Ar X))].

    - [int_to_linhom_fun β] — paper Thm 6.1 forward direction at
      the function level: [µ ↦ icone_integral β _ µ]. Three of the
      four [linhom_pre] fields are delivered:

      * [int_to_linhom_fun_linear]: linearity in [µ] (paper Lemma 4.7).
      * [int_to_linhom_fun_bounded]: operator-norm boundedness
        with constant [M := path_norm β] (paper Lemma 4.2).
      * [int_to_linhom_fun_pres_path]: measurable-path preservation
        in the [fmeas] argument (paper Lemma 4.7, joint measurability).

      The ω-continuity field is documented but deferred: the proof
      sketch (rescale [β] to unit ball, invoke
      [integral_omega_cont_meas], pull back via [sup_ball_scaler])
      is implemented at draft level but a [cone_sup_ball] proof-
      irrelevance bridge is missing. See the body for the proof
      sketch.

    - [linhom_to_int f] — paper Thm 6.1 inverse direction. Takes
      a [linhom_car Ar (fmeas R (ar_carrier Ar X)) B] and produces
      a [path_car Ar X B] via [r ↦ linhom_fun f (dirac_fmeas r)].

    - [K_int_to_linhom_E] — paper Thm 6.1 round-trip [K ∘ I = id]
      at the function level:
      [path_fun (linhom_to_int_path β _ _ _) r = path_fun β r].
      Direct via [integral_dirac].

    Deferred to wave 2 / follow-up.

    - Full packaging of the forward map as a [linhom_car], hence
      as a [mcones_hom]/[icones_hom]. The bulky proofs are
      ω-continuity in [µ] (via [integral_omega_cont_meas] +
      norm-rescaling through [sup_ball_scaler]),
      measurable-path-preservation (via [icone_integral_joint_measurable]),
      and integral-preservation (the paper's cone-Fubini step,
      requiring a scalar Tonelli identity for [fmeas]-integrated
      kernels on the lines of [mathcomp-analysis]'s [integral_kcomp]).
    - The reverse round-trip [I ∘ K = id], which uses simple-function
      approximation of [µ] (the identity [µ = ∫ \d_r µ(dr)] in
      [FMeas X]) followed by [f]'s integral preservation.
    - Naturality in [X] (via pushforward) and in [B] (via
      post-composition). *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals constructive_ereal.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import ereal sequences ereal_normedtype.
From mathcomp.analysis Require Import topology normedtype.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import measure.
From mathcomp.analysis Require Import dirac_measure.
From mathcomp.analysis Require Import lebesgue_integral_definition.
From mathcomp.analysis Require Import lebesgue_integral_nonneg.
Import numFieldTopology.Exports.

Require Import Icones.prelude.classical_extra.
Require Import Icones.prelude.nonneg_extra.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.cone_cat.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.mcones.path.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.pettis.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_integral.
Require Import Icones.icones.examples_icone.
Require Import Icones.icones.fubini.
Require Import Icones.icones.icone_cat.
Require Import Icones.homs.linhom.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** Paper §6 paragraph 1 — the Dirac path [δ_X]

    For each [X : ar_obj Ar] the function [r ↦ \d_r] is a bounded
    measurable path of unit total mass in
    [fmeas R (ar_carrier Ar X)]. mathcomp-analysis's [\d_r] is a
    measure on the entire powerset; we glue it to [0] off the
    σ-algebra so that the [fmeas] canonicality invariant holds. *)

Section DiracPath.
Variables (R : realType) (Ar : MeasSubcat R).
Variable X : ar_obj Ar.

(** Canonical Dirac measure at [r], with [0] off the σ-algebra. *)
Local Definition dirac_canon_fun (r : ar_carrier Ar X) :
    set (ar_carrier Ar X) -> \bar R :=
  fun U => if `[< measurable U >] then (\d_r U : \bar R) else 0%E.

Local Lemma dirac_canon_funE (r : ar_carrier Ar X) U :
  measurable U -> dirac_canon_fun r U = \d_r U.
Proof. by move=> mU; rewrite /dirac_canon_fun asboolT. Qed.

Local Lemma dirac_canon_fun_off (r : ar_carrier Ar X) U :
  ~ measurable U -> dirac_canon_fun r U = 0%E.
Proof. by move=> nmU; rewrite /dirac_canon_fun asboolF. Qed.

Local Lemma dirac_canon_set0 (r : ar_carrier Ar X) :
  dirac_canon_fun r set0 = 0%E.
Proof. by rewrite dirac_canon_funE ?measurable0// dirac0. Qed.

Local Lemma dirac_canon_ge0 (r : ar_carrier Ar X) U :
  (0 <= dirac_canon_fun r U)%E.
Proof.
rewrite /dirac_canon_fun; case: asboolP => _; last exact: lexx.
exact: measure_ge0.
Qed.

Local Lemma dirac_canon_sigma_additive (r : ar_carrier Ar X) :
  semi_sigma_additive (dirac_canon_fun r).
Proof.
move=> F mF tF mUF.
have step : forall n,
  (\sum_(0 <= i < n) dirac_canon_fun r (F i))%E =
  (\sum_(0 <= i < n) (\d_r (F i) : \bar R))%E.
  move=> n; apply: eq_bigr => i _.
  by rewrite dirac_canon_funE//; exact: mF.
rewrite dirac_canon_funE//.
under eq_fun do rewrite step.
exact: measure_semi_sigma_additive.
Qed.

Arguments dirac_canon_set0 : clear implicits.
Arguments dirac_canon_ge0 : clear implicits.
Arguments dirac_canon_sigma_additive : clear implicits.

Section DiracCanonMeasure.
Variable r : ar_carrier Ar X.

HB.instance Definition _ :=
  @isMeasure.Build (ar_disp Ar X) (ar_carrier Ar X) R
    (dirac_canon_fun r)
    (dirac_canon_set0 r) (dirac_canon_ge0 r)
    (dirac_canon_sigma_additive r).

End DiracCanonMeasure.

Local Lemma dirac_canon_finP (r : ar_carrier Ar X) :
  fmeas_finP (R:=R) (dirac_canon_fun r).
Proof.
move=> U _; rewrite /dirac_canon_fun.
case: asboolP => _; last by [].
rewrite diracE; by case: (r \in U).
Qed.

Local Lemma dirac_canon_canon (r : ar_carrier Ar X) :
  fmeas_canon (R:=R) (dirac_canon_fun r).
Proof. exact: dirac_canon_fun_off. Qed.

(** Paper §6 paragraph 1: the canonical [fmeas R X] underlying the
    Dirac mass at [r]. *)
Definition dirac_fmeas (r : ar_carrier Ar X) : fmeas R (ar_carrier Ar X) :=
  MkFmeas [the {measure set _ -> \bar R} of dirac_canon_fun r]
          (dirac_canon_finP r) (dirac_canon_canon r).

(** [dirac_fmeas r] agrees with [\d_r] on measurable sets. *)
Lemma dirac_fmeas_E (r : ar_carrier Ar X) U :
  measurable U -> fmeas_mu (dirac_fmeas r) U = \d_r U.
Proof. by move=> mU; exact: dirac_canon_funE. Qed.

(** [dirac_fmeas r] has unit total mass. *)
Lemma dirac_fmeas_setT_E (r : ar_carrier Ar X) :
  fmeas_mu (dirac_fmeas r) [set: ar_carrier Ar X] = 1%E.
Proof. by rewrite dirac_fmeas_E// diracT. Qed.

Lemma dirac_fmeas_norm (r : ar_carrier Ar X) :
  cone_norm (dirac_fmeas r) = 1.
Proof.
by rewrite /cone_norm/= /fmeas_norm/= dirac_fmeas_setT_E.
Qed.

(** Paper §6 paragraph 1: [r ↦ dirac_fmeas r] is a bounded measurable
    path. Boundedness is immediate; joint test-measurability via the
    [e_U] test family reduces to measurability of [r ↦ \1_U r]. *)
Lemma dirac_fmeas_is_path :
  is_measurable_path (Ar:=Ar) (C:=fmeas R (ar_carrier Ar X))
    (X:=X) dirac_fmeas.
Proof.
split.
  by exists 1 => r; rewrite dirac_fmeas_norm.
move=> Y m mM.
case: mM => [U [mU ->]].
apply: (eq_measurable_fun
  (fun p : ar_carrier Ar Y * ar_carrier Ar X =>
     fine (\d_(p.2) U : \bar R))).
  by move=> p _; rewrite /= /eU_fun/= dirac_fmeas_E.
pose g (r : ar_carrier Ar X) : \bar R := \d_r U.
have g_meas : measurable_fun [set: ar_carrier Ar X] g.
  by apply: measurable_fun_dirac.
have finecomp : measurable_fun [set: ar_carrier Ar X]
                  (fun r : ar_carrier Ar X => fine (g r)).
  by apply: (measurableT_comp (f := fine)) => //; exact: fine_measurable.
exact: (measurableT_comp finecomp measurable_snd).
Qed.

(** Paper §6 paragraph 1: [δ_X] as a [path_car]. *)
Definition dirac_path : path_car Ar X (fmeas R (ar_carrier Ar X)) :=
  MkPath dirac_fmeas_is_path.

End DiracPath.

Arguments dirac_fmeas {R Ar X}.
Arguments dirac_path {R} Ar X.

(** ** Paper Thm 6.1 forward direction (function level) — [int_to_linhom_fun β]

    For [β ∈ Path(X, B)], the function [µ ↦ ∫β dµ]. Linearity in
    [µ] is the only field we deliver at this level; full packaging
    as a [linhom_car] is deferred (see file header). *)

Section IntToLinhomFun.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (X : ar_obj Ar) (B : ICone.type Ar).
Variable β : path_car Ar X B.

Local Notation Hβ := (path_is_path β).
Local Notation βf := (path_fun β).

(** The underlying function: [µ ↦ icone_integral β Hβ µ]. *)
Definition int_to_linhom_fun :
    fmeas R (ar_carrier Ar X) -> B :=
  fun µ => icone_integral βf Hβ µ.

(** Paper Lemma 4.7: [int_to_linhom_fun β] is linear in [µ]. *)
Lemma int_to_linhom_fun_linear : is_linear int_to_linhom_fun.
Proof.
split.
- (* The integral against [fmeas_zero] is [precone_zero]. *)
  apply/esym/icone_integral_eqP => m mM s.
  rewrite test_lin0.
  have -> : fmeas_mu (fmeas_zero (R:=R) (X:=ar_carrier Ar X)) = mzero :> (_ -> _).
    by [].
  by rewrite integral_measure_zero.
- by move=> µ1 µ2; rewrite /int_to_linhom_fun; exact: icone_integral_addmu.
- by move=> r µ; rewrite /int_to_linhom_fun; exact: icone_integral_scalemu.
Qed.

(** Paper Lemma 4.2 + Lemma 4.7: boundedness. With [M := path_norm β],
    [‖∫β dµ‖ ≤ path_norm β · fmeas_norm µ ≤ path_norm β · 1]
    when [µ] is in the unit ball. *)
Lemma int_to_linhom_fun_bounded :
  exists M : R,
    forall µ : fmeas R (ar_carrier Ar X),
      cone_norm µ <= 1 -> cone_norm (int_to_linhom_fun µ) <= M.
Proof.
exists (path_norm β) => µ Hµ.
apply: (@le_trans _ _ (path_norm β * fmeas_norm µ)); last first.
  rewrite -[X in _ <= X]mulr1.
  by apply: ler_wpM2l; [exact: path_norm_ge0|exact: Hµ].
apply: (path_integral_norm_le (Mβ := path_norm β)).
- move=> r; exact: path_norm_ub.
- exact: Hβ.
- exact: icone_integralP.
Qed.

(** Paper Lemma 4.7 (ω-continuity in [µ]) — *deferred*.

    The proof sketch: rescale [β] to the unit ball via
    [β' := (path_norm β + 1)^-1 *: β], invoke
    [integral_omega_cont_meas] on [β'] (which only applies when
    [β] is unit-bounded), and pull the equation back through
    [sup_ball_scaler] (Paper Lemma 2.9). The pullback step matches
    the [cone_sup_ball] of the unscaled image chain against
    [S *: cone_sup_ball] of the unit-bounded image chain.

    The bridging arithmetic between the two [cone_sup_ball]
    instances (different chain/bound proof terms for the same
    function) is the main obstacle in this wave; a clean form
    requires either exposing [int_µ]/[int_µ_chain]/[int_µ_bound]
    as a public abbreviation in [icone_integral.v] (so we can
    package our [int_βS_n]/chain/bound to match) or proving a
    [cone_sup_ball]-proof-irrelevance lemma in [precone]/[cone]. *)

(** Paper Lemma 4.7 + joint measurability: for any measurable path
    [κ : ar_carrier Y -> fmeas R X], the composite
    [r ↦ icone_integral β _ (κ r)] is a measurable path in [B].
    Direct from [icone_integral_joint_measurable] with the
    constant kernel [s ↦ β]. *)
Lemma int_to_linhom_fun_pres_path
    (Y : ar_obj Ar) (κ : ar_carrier Ar Y -> fmeas R (ar_carrier Ar X)) :
  is_measurable_path κ ->
  is_measurable_path (fun r => int_to_linhom_fun (κ r)).
Proof.
move=> Hκ.
have [[Mκ HMκ] Hκj] := Hκ.
have Mκ_ge0 : 0 <= Mκ.
  by apply: le_trans (HMκ (ar_point Ar Y)); exact: cone_norm_ge0.
split.
  exists (path_norm β * Mκ) => r.
  have HnormI : cone_norm (icone_integral βf Hβ (κ r))
                  <= path_norm β * fmeas_norm (κ r).
    apply: (path_integral_norm_le (Mβ := path_norm β)).
    - move=> r'; exact: path_norm_ub.
    - exact: Hβ.
    - exact: icone_integralP.
  apply: le_trans HnormI _.
  apply: ler_wpM2l; [exact: path_norm_ge0|].
  exact: HMκ.
move=> Z m mM.
(* The function [(s, r) ↦ test m s (icone_integral β _ (κ r))]
   is jointly measurable by [icone_integral_joint_measurable]
   with the constant kernel of paths [s ↦ β]. *)
pose βconst : ar_carrier Ar Y -> ar_carrier Ar X -> B := fun _ r => βf r.
have Hβconst : forall s, is_measurable_path (βconst s).
  by move=> s; exact: Hβ.
have κ_meas_perU : forall U, measurable U ->
  measurable_fun [set: ar_carrier Ar Y] (fun s => fmeas_mu (κ s) U).
  move=> U mU.
  have mM_U : mcone_M (Ar:=Ar) (ar_zero Ar)
    (fmeas_eU (ar_zero Ar) mU).
    by exists U, mU.
  have HmU_joint := Hκj _ _ mM_U.
  have meas_fine :
    measurable_fun [set: ar_carrier Ar Y]
      (fun s => fine (fmeas_mu (κ s) U)).
    pose F (p : ar_carrier Ar (ar_zero Ar) * ar_carrier Ar Y) : R :=
      test_fun (fmeas_eU (ar_zero Ar) mU) p.1 (κ p.2).
    have HF : measurable_fun
      [set: (ar_carrier Ar (ar_zero Ar) * ar_carrier Ar Y)%type] F.
      exact: HmU_joint.
    have -> : (fun s => fine (fmeas_mu (κ s) U)) =
              (fun s => F (ar_zero_pt Ar, s)).
      by apply: funext.
    by apply: (measurableT_comp (f := F)).
  have rewE : (fun s => fmeas_mu (κ s) U) =
              (fun s => (fine (fmeas_mu (κ s) U))%:E).
    apply: funext => s; rewrite fineK//; exact: fmeas_fin.
  by rewrite rewE; apply/measurable_EFinP.
have κ_bound : exists M : R, forall s, (fmeas_norm (κ s) <= M)%R.
  by exists Mκ.
have HjointConst :
  measurable_fun
    [set: (ar_carrier Ar Z * (ar_carrier Ar Y * ar_carrier Ar X))%type]
    (fun p => test_fun m p.1 (βconst p.2.1 p.2.2)).
  rewrite /βconst.
  have [_ Hβj] := Hβ.
  have Hβj' := Hβj Z m mM.
  pose ψ (q : (ar_carrier Ar Z *
              (ar_carrier Ar Y * ar_carrier Ar X))%type) :
    ar_carrier Ar Z * ar_carrier Ar X :=
    (q.1, q.2.2).
  have ψ_meas : measurable_fun
    [set: (ar_carrier Ar Z * (ar_carrier Ar Y * ar_carrier Ar X))%type] ψ.
    apply: measurable_fun_pair; first exact: measurable_fst.
    by apply: (measurableT_comp (f := snd));
      [exact: measurable_snd|exact: measurable_snd].
  have -> : (fun q : (ar_carrier Ar Z *
                     (ar_carrier Ar Y * ar_carrier Ar X))%type =>
             test_fun m q.1 (βf q.2.2)) =
            (fun p : ar_carrier Ar Z * ar_carrier Ar X =>
             test_fun m p.1 (βf p.2)) \o ψ.
    by apply: funext.
  exact: (measurableT_comp Hβj' ψ_meas).
have Mβ_bd : exists M : R, forall z s r,
    (test_fun m z (βconst s r) <= M)%R.
  exists (path_norm β) => z s r; rewrite /βconst.
  apply: le_trans (test_norm_le _ _ _) _.
  exact: path_norm_ub.
have main :=
  @icone_integral_joint_measurable R Ar B X _ _ βconst Hβconst κ Z m mM
    κ_meas_perU κ_bound HjointConst Mβ_bd.
apply: (eq_measurable_fun _ _ main).
move=> p _.
rewrite /int_to_linhom_fun.
congr (test_fun m p.1 _).
(* βconst p.2 = βf as functions; by uniqueness of icone_integral. *)
apply/esym/icone_integral_eqP; exact: icone_integralP.
Qed.

End IntToLinhomFun.

Arguments int_to_linhom_fun {R Ar X B} β.
Arguments int_to_linhom_fun_linear {R Ar X B} β.
Arguments int_to_linhom_fun_bounded {R Ar X B} β.

(** ** Paper Thm 6.1 inverse direction — [linhom_to_int f]

    For [f : linhom_car Ar (fmeas R (ar_carrier Ar X)) B], the
    inverse path is [r ↦ linhom_fun f (dirac_fmeas r)]. *)

Section LinhomToInt.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (X : ar_obj Ar) (B : ICone.type Ar).
Variable f : linhom_car Ar (fmeas R (ar_carrier Ar X)) B.

(** Paper §6, post-Thm 6.1: the underlying function of [K^B_X(f)]. *)
Definition linhom_to_int_fun : ar_carrier Ar X -> B :=
  fun r => linhom_fun f (dirac_fmeas r).

(** Boundedness of [linhom_to_int_fun]: each value is the image of
    a unit-norm measure, so it is bounded by the operator-norm
    [linhom_norm f]. *)
Lemma linhom_to_int_fun_norm_bound r :
  cone_norm (linhom_to_int_fun r) <= linhom_norm f.
Proof.
rewrite /linhom_to_int_fun.
apply: le_trans (linhom_norm_apply_le (lexx _) (dirac_fmeas r)) _.
by rewrite dirac_fmeas_norm mulr1.
Qed.

(** Paper §6 lines 2952–2968: [r ↦ linhom_fun f (\d_r)] is a
    measurable path. The argument is: precompose [δ_X] (a
    measurable path of [fmeas]) with [f] (a measurable-path-
    preserving map). *)
Lemma linhom_to_int_fun_is_path : is_measurable_path linhom_to_int_fun.
Proof.
have Hδ := @dirac_fmeas_is_path R Ar X.
have Hf := linhom_pre_pres_path (linhom_pre_of f) X dirac_fmeas Hδ.
exact: Hf.
Qed.

(** Paper §6 lines 2952–2968: [K^B_X(f)] as a [path_car]. *)
Definition linhom_to_int : path_car Ar X B :=
  MkPath linhom_to_int_fun_is_path.

(** Compute: [linhom_to_int f r = f (\d_r)]. *)
Lemma linhom_to_int_E (r : ar_carrier Ar X) :
  path_fun linhom_to_int r = linhom_fun f (dirac_fmeas r).
Proof. by []. Qed.

End LinhomToInt.

Arguments linhom_to_int_fun {R Ar X B} f.
Arguments linhom_to_int {R Ar X B} f.

(** ** Paper Thm 6.1 — round-trip identity [K ∘ I = id]

    For [β ∈ Path(X, B)] and [r ∈ X],
    [linhom_to_int (int_to_linhom β) r = int_to_linhom_fun β (\d_r)
                                       = icone_integral β _ (\d_r) = β r].

    The last equality uses [integral_dirac], packaged as the
    Pettis-uniqueness verification below. We deliver this at the
    function level rather than via a full [linhom_car]-valued
    [int_to_linhom], because the latter requires deferred fields.
    The key arithmetic identity is captured by
    [int_to_linhom_fun_dirac]. *)

Section RoundTripKI.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (X : ar_obj Ar) (B : ICone.type Ar).
Variable β : path_car Ar X B.

Local Notation Hβ := (path_is_path β).
Local Notation βf := (path_fun β).

(** Paper Thm 6.1: integrating any measurable path of [B] against
    a Dirac mass returns the integrand. *)
Lemma int_to_linhom_fun_dirac (r : ar_carrier Ar X) :
  int_to_linhom_fun β (dirac_fmeas r) = βf r.
Proof.
rewrite /int_to_linhom_fun.
apply/esym/icone_integral_eqP => m mM s.
(* test_fun m s (β r) = fine (∫[\d_r] (test_fun m s (β r'))%:E dr'). *)
have meas_test : measurable_fun [set: ar_carrier Ar X]
                   (fun r' => (test_fun m s (βf r'))%:E).
  apply/measurable_EFinP.
  exact: (measurable_test_path_section mM Hβ).
have rT : [set: ar_carrier Ar X] r by [].
(* Step 1: [(dirac_fmeas r) U = \d_r U] for measurable U, so the
   integral agrees. *)
have integral_eq :
    (\int[fmeas_mu (dirac_fmeas r)]_(r' in [set: ar_carrier Ar X])
       (test_fun m s (βf r'))%:E)%E =
    (\int[\d_r]_(r' in [set: ar_carrier Ar X])
       (test_fun m s (βf r'))%:E)%E.
  apply: eq_measure_integral => U mU _.
  by rewrite dirac_fmeas_E.
(* Step 2: [∫[\d_r]_(r' in setT) g r' = \d_r setT * g r = g r]. *)
have dirac_int :
    (\int[\d_r]_(r' in [set: ar_carrier Ar X])
       (test_fun m s (βf r'))%:E)%E =
    (test_fun m s (βf r))%:E.
  rewrite integral_dirac//.
  by rewrite diracT mul1e.
by rewrite integral_eq dirac_int.
Qed.

(** Paper Thm 6.1: round-trip [K ∘ I = id]. At the function level:
    [linhom_to_int_fun (int_to_linhom_fun β as a linhom) r = β r].
    We deliver this via [int_to_linhom_fun_dirac] above; a full
    statement at the [path_car] level requires promoting
    [int_to_linhom_fun β] to a [linhom_car], which is deferred. *)
Lemma K_int_to_linhom_E (r : ar_carrier Ar X) :
  int_to_linhom_fun β (dirac_fmeas r) = βf r.
Proof. exact: int_to_linhom_fun_dirac. Qed.

End RoundTripKI.

Arguments int_to_linhom_fun_dirac {R Ar X B} β r.
Arguments K_int_to_linhom_E {R Ar X B} β r.

(** ** Sanity checks — paper Thm 6.1 wave 1 deliverables *)

Section BilinSanityCheck.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (X : ar_obj Ar) (B : ICone.type Ar).

(** [dirac_path] is a measurable path of [fmeas]. *)
Check (dirac_path Ar X :
  path_car Ar X (fmeas R (ar_carrier Ar X))).

(** [int_to_linhom_fun] sends a path to a function on measures. *)
Check (fun β : path_car Ar X B =>
  int_to_linhom_fun β : fmeas R (ar_carrier Ar X) -> B).

(** [linhom_to_int] sends a [linhom_car] to a path. *)
Check (fun f : linhom_car Ar (fmeas R (ar_carrier Ar X)) B =>
  linhom_to_int f : path_car Ar X B).

(** Paper Thm 6.1: round-trip [K ∘ I = id] at function level. *)
Check (fun (β : path_car Ar X B) (r : ar_carrier Ar X) =>
  K_int_to_linhom_E β r :
    int_to_linhom_fun β (dirac_fmeas r) = path_fun β r).

End BilinSanityCheck.
