(**md*** Affine Kleene cascades — closed form, limit, and sup-mass bridge

    Scalarised core of the rejection-sampling killer example (plan §M3).

    ** Affine iteration

    Given reals [a, q >= 0] and a real sequence [x] with [x 0 = 0] and
    [x n.+1 = a + q * x n] (the per-iterate mass of an affine Kleene
    chain), we expose:

    - [affine_iter_closed] : the closed form
      [x n = a * (\sum_(i < n) q ^+ i)];
    - [affine_iter_geom] : the geometric form
      [q != 1 -> x n = a * (1 - q ^+ n) / (1 - q)];
    - [affine_iter_cvg_real] / [affine_iter_cvg] : when [q < 1],
      [x n --> a / (1 - q)] (in [R], resp. in [\bar R] via [%:E]);
    - [affine_iter_deg_eq0] : the degenerate case
      [q = 1 -> a = 0 -> x n = 0].

    ** Sup-mass bridge

    For a unit-ball ω-chain [ν : nat -> fmeas R X] (increasing and
    norm-bounded by [1]) and a measurable [U]:

    - [fmeas_kleene_sup_U_cvg] : [fmeas_mu (ν n) U] converges to the
      mass of [cone_sup_ball ν ch ub] at [U];
    - [fmeas_kleene_sup_U_E] : hence any limit [l] of
      [fmeas_mu (ν n) U] *is* that mass (by Hausdorff uniqueness).

    [cone_sup_ball] at [fmeas R X] is definitionally [fmeas_sup_ball]
    (the HB [isCone] instance of [fmeas.v]), so the bridge is
    [fmeas_sup_ballE] + [fmeas_sup_cvg] + [cvg_unique].

    ** Sanity instantiation

    [affine_iter_cvg_half] : at [a := 1/2], [q := 1/2] the limit is [1].

    ** Author

    Guillaume Baudart <guillaume.baudart@inria.fr>. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import ereal.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import measure measure_function.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import topology normedtype sequences.
Import numFieldTopology.Exports.

Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.mcones.fmeas.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** §1 — Affine iteration: closed form and limit *)

Section AffineIter.
Variable R : realType.

Variables (a q : R).
Hypothesis Ha_ge0 : (0 <= a)%R.
Hypothesis Hq_ge0 : (0 <= q)%R.

Variable (x : nat -> R).
Hypothesis Hx0 : x 0%N = 0%R.
Hypothesis HxS : forall n, x n.+1 = (a + q * x n)%R.

(** Closed form: [x n = a * (1 + q + ... + q^(n-1))]. *)
Lemma affine_iter_closed (n : nat) :
  x n = (a * (\sum_(i < n) q ^+ i))%R.
Proof.
elim: n => [ | n IH ].
- by rewrite Hx0 big_ord0 mulr0.
- rewrite HxS IH big_ord_recl expr0 mulrDr mulr1.
  congr (_ + _)%R.
  have qlift (i : 'I_n) : q ^+ lift ord0 i = (q * q ^+ i)%R.
    by rewrite lift0 exprS.
  rewrite (eq_bigr _ (fun i _ => qlift i)).
  by rewrite -mulr_sumr mulrCA.
Qed.

(** The closed form is the partial geometric series [series
    (geometric a q)] of mathcomp-analysis. *)
Lemma affine_iter_seriesE (n : nat) :
  x n = series (geometric a q) n.
Proof.
rewrite affine_iter_closed mulr_sumr /series/= big_mkord.
by [].
Qed.

(** Geometric form away from [q = 1]. *)
Lemma affine_iter_geom (n : nat) :
  q != 1%R -> x n = (a * (1 - q ^+ n) / (1 - q))%R.
Proof.
move=> Hq_neq1.
by rewrite affine_iter_seriesE (geometric_seriesE a Hq_neq1).
Qed.

(** Real-valued limit: [x n --> a / (1 - q)] when [0 <= q < 1]. *)
Lemma affine_iter_cvg_real :
  (q < 1)%R -> x n @[n --> \oo] --> (a / (1 - q))%R.
Proof.
move=> Hq_lt1.
under eq_fun => n do rewrite affine_iter_seriesE.
apply: cvg_geometric_series.
by rewrite ger0_norm.
Qed.

(** Extended-real limit, [\bar R]-house-style form of the same. *)
Local Open Scope ereal_scope.
Lemma affine_iter_cvg :
  (q < 1)%R ->
  (x n)%:E @[n --> \oo] --> ((a / (1 - q))%R%:E : \bar R).
Proof.
move=> Hq_lt1.
apply: cvg_EFin.
  by apply: nearW => n; rewrite //=.
exact: affine_iter_cvg_real.
Qed.
Local Close Scope ereal_scope.

(** Degenerate case [q = 1, a = 0]: every iterate vanishes. *)
Lemma affine_iter_deg_eq0 (n : nat) :
  q = 1%R -> a = 0%R -> x n = 0%R.
Proof.
move=> Hq1 Ha0.
elim: n => [ | n IH ]; first by rewrite Hx0.
by rewrite HxS IH mulr0 addr0 Ha0.
Qed.

End AffineIter.

Arguments affine_iter_closed {R} a q {x} Hx0 HxS n.
Arguments affine_iter_seriesE {R} a q {x} Hx0 HxS n.
Arguments affine_iter_geom {R} a q {x} Hx0 HxS n.
Arguments affine_iter_cvg_real {R} a q Hq_ge0 {x} Hx0 HxS.
Arguments affine_iter_cvg {R} a q Hq_ge0 {x} Hx0 HxS.
Arguments affine_iter_deg_eq0 {R} a q {x} Hx0 HxS n.

(** ** §2 — Sanity instantiation: [a = q = 1/2] has limit [1] *)

Section AffineIterHalf.
Variable R : realType.

Variable (x : nat -> R).
Hypothesis Hx0 : x 0%N = 0%R.
Hypothesis HxS : forall n, x n.+1 = (1 / 2 + (1 / 2) * x n)%R.

Local Open Scope ereal_scope.

(** DoD witness: the [a := 1/2], [q := 1/2] cascade has total mass
    converging to [1]. *)
Lemma affine_iter_cvg_half :
  (x n)%:E @[n --> \oo] --> (1%:E : \bar R).
Proof.
have Hhalf_ge0 : (0 <= 1 / 2 :> R)%R by rewrite divr_ge0.
have Hhalf_lt1 : (1 / 2 < 1 :> R)%R.
  by rewrite ltr_pdivrMr// mul1r ltr1n.
have Hlim : ((1 / 2 : R) / (1 - 1 / 2))%R = 1%R.
  have -> : (1 - 1 / 2 : R)%R = (1 / 2)%R.
    by rewrite {1}(splitr 1) addrK.
  by rewrite divff// div1r invr_eq0 pnatr_eq0.
have := affine_iter_cvg (1 / 2) (1 / 2) Hhalf_ge0 Hx0 HxS Hhalf_lt1.
by rewrite Hlim.
Qed.

End AffineIterHalf.

(** ** §3 — The sup-mass bridge for unit-ball ω-chains in [FMeas] *)

Section FMeasKleeneSup.
Variable R : realType.
Variable disp : measure_display.
Variable X : measurableType disp.

Variable nu : nat -> fmeas R X.
Hypothesis nuch : forall n, precone_le (nu n) (nu n.+1).
Hypothesis nub1 : forall n, (cone_norm (nu n) <= 1)%R.

Local Open Scope ereal_scope.

(** Per-set mass convergence: [fmeas_mu (ν n) U] converges to the mass
    of the ball-sup at [U]. The first step is definitional —
    [cone_sup_ball] at [fmeas R X] *is* [fmeas_sup_ball] (the HB
    [isCone] instance, fmeas.v). *)
Lemma fmeas_kleene_sup_U_cvg (U : set X) :
  measurable U ->
  fmeas_mu (nu n) U @[n --> \oo] -->
  fmeas_mu (cone_sup_ball nu nuch nub1 : fmeas R X) U.
Proof.
move=> mU.
have HE : (cone_sup_ball nu nuch nub1 : fmeas R X)
          = fmeas_sup_ball nuch nub1 by [].
rewrite HE (fmeas_sup_ballE _ nub1 mU).
exact: fmeas_sup_cvg.
Qed.

(** The bridge: any limit of the per-iterate masses at [U] *is* the
    mass of the ball-sup at [U] (by [cvg_unique] in the Hausdorff
    space [\bar R]). *)
Lemma fmeas_kleene_sup_U_E (U : set X) (l : \bar R) :
  measurable U ->
  fmeas_mu (nu n) U @[n --> \oo] --> l ->
  fmeas_mu (cone_sup_ball nu nuch nub1 : fmeas R X) U = l.
Proof.
move=> mU Hcvg.
have Hsup := fmeas_kleene_sup_U_cvg mU.
exact: (@cvg_unique _ (@ereal_hausdorff R) _ _ _ _ Hsup Hcvg).
Qed.

End FMeasKleeneSup.

Arguments fmeas_kleene_sup_U_cvg {R disp X nu} nuch nub1 {U} mU.
Arguments fmeas_kleene_sup_U_E {R disp X nu} nuch nub1 {U l} mU Hcvg.
