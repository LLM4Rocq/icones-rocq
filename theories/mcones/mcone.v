(** * Measurable cones — Paper §3 (Defs 3.2, 3.6, 3.7)

    A measurable cone is a [coneType R] equipped with a "measurability
    structure": a per-arity family [mcone_M X] of *tests* of arity [X]
    satisfying (Msmeas), (Mscomp), (Mssep), and (Msnorm) (paper
    Def 3.2). A test of arity [X] is a function

      [m : ar_carrier X -> C -> R]

    that is jointly measurable in its first argument (uniformly over
    every unit-ball element of [C]), linear and ω-continuous in its
    second argument, and pointwise bounded by [cnorm].

    Paper reference: §3, p. 1:17–1:18, Defs 3.2 / 3.6 / 3.7 and
    Lemmas 3.9 / 3.10.

    Coverage in this file:

    - [test_of Ar X C] — the [Record] of tests of arity [X] on a
      [coneType] [C].
    - [test_reindex] — reindexing of a test along [φ ∈ ar_hom Y X],
      used to state (Mscomp).
    - [test_map] — transport of a test along a linear,
      norm-nonincreasing cone map [f : D -> C] (the combinator behind
      every "pullback of a test" in the development: product
      projections, equaliser inclusions, local-cone inclusions, …).
    - [test_const] — the base test attached to a single linear,
      ω-continuous, norm-bounded functional [φ : C -> R], constant in
      the arity point.
    - [isMCone Ar C] — the HB mixin over [coneType R] declaring the
      family [mcone_M] and the axioms (Mscomp), (Mssep), (Msnorm).
    - [MCone.type Ar] (alias [mconeType Ar]) — the HB structure
      of measurable cones.
    - [is_measurable_path Ar C X γ] — paper Def 3.7.
    - [const_path_measurable] — Lemma 3.9.
    - [reindex_path_measurable] — Lemma 3.10.

    Design notes.

    - Tests are [R]-valued (not [{nonneg R}]-valued). Non-negativity
      and the [0,1]-bound on the unit ball are recorded as separate
      [Prop] fields. This avoids weaving [%:num]/[%:nng] casts in
      every downstream lemma.

    - Linearity / ω-continuity of [λ x. m r x : C -> R] is stated
      *inline* as three equations + an ω-sup inequality, rather than
      via the project's [is_linear]/[is_omega_continuous]
      predicates: those are typed [P -> Q] for two [coneType]s, but
      here the codomain is the [realType] [R]. A cone-theoretic
      reading is "[λ x. m r x] is a [Cones]-morphism to
      [ConeOne.T R]" but we keep the pointwise statements local for
      ergonomics. (Equivalence with [cones_hom C (ConeOne.T R)] is
      a routine wrapping not needed at this layer.)

    - The (Msnorm) axiom is stated in the simplified form

        [forall x, x ≠ 0 → forall ε > 0,
           exists m ∈ mcone_M ar_zero, cone_norm x ≤ m r0 x + ε]

      where [r0 = ar_zero_pt Ar]. Paper's stronger form
      [cnorm x ≤ m(x)/||m|| + ε] is recovered because every test
      satisfies [m r x ≤ cnorm x] (so [||m|| ≤ 1] as an operator-
      norm bound), and hence [m(x)/||m|| ≥ m(x)] when [m ≠ 0]. We
      do not formalize the dual norm in this file; the general dual-
      norm characterisation (paper Prop 3.11) lives in
      [theories/mcones/mcone_cat.v], and the [FMeas] / [Path] cones
      come with explicit dual-norm witnesses on a case-by-case
      basis.
*)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.

Require Import Icones.prelude.nonneg_extra.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.mcones.ar.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** Tests — Paper Def 3.2 (the entries of [M_X])

    [test_of Ar X C] is the type of tests of arity [X] on a [coneType]
    [C]. A test is a function [m : ar_carrier X -> C -> R] together
    with five [Prop] properties. *)
Section TestOf.
Variable R : realType.
Variable Ar : MeasSubcat R.
Variable X : ar_obj Ar.
Variable C : coneType R.

(** Paper Def 3.2: a test of arity [X]. *)
Record test_of : Type := MkTestOf {
  (** The underlying function. *)
  test_fun :> ar_carrier Ar X -> C -> R;
  (** (Msmeas) — Paper Def 3.2: for each unit-ball [x : C], the
      partial application [λ r. m r x] is a measurable function from
      [ar_carrier X] to [R]. *)
  test_meas :
    forall x : C, cone_norm x <= 1 ->
      measurable_fun setT (fun r => test_fun r x);
  (** (Msmeas) — Paper Def 3.2: tests are non-negative on the whole
      cone (a consequence of linearity and monotonicity, made
      structural here for ergonomics). *)
  test_ge0 :
    forall (r : ar_carrier Ar X) (x : C), 0 <= test_fun r x;
  (** (Msmeas) — Paper Def 3.2: [m r x ≤ 1] when [cnorm x ≤ 1].
      Together with [test_ge0] this gives the paper's "lands in
      [[0,1]]" condition. *)
  test_le1 :
    forall (r : ar_carrier Ar X) (x : C),
      cone_norm x <= 1 -> test_fun r x <= 1;
  (** Paper Def 3.2: [λ x. m r x ∈ Cones(C, 1)] (linear). *)
  test_lin0 :
    forall r : ar_carrier Ar X, test_fun r precone_zero = 0;
  test_linD :
    forall (r : ar_carrier Ar X) (x y : C),
      test_fun r (precone_add x y) = test_fun r x + test_fun r y;
  test_linZ :
    forall (r : ar_carrier Ar X) (s : {nonneg R}) (x : C),
      test_fun r (precone_scale s x) = s%:num * test_fun r x;
  (** Paper Def 3.2: [λ x. m r x ∈ Cones(C, 1)] (ω-continuous, in
      the sup-preserving form sufficient for our use). Concretely:
      for an increasing chain [(u_n)] in the unit ball with
      supremum [s = sup_ball u], the value [m r s] is the supremum
      (in [R]) of the increasing chain [(m r (u n))]. We
      state the "least upper bound" half here; the upper-bound
      half [m r (u n) ≤ m r s] follows from monotonicity (Normp). *)
  test_cont :
    forall (r : ar_carrier Ar X)
           (u : nat -> C)
           (uch : forall n, precone_le (u n) (u n.+1))
           (ub1 : forall n, cone_norm (u n) <= 1)
           (N : R),
      (forall n, test_fun r (u n) <= N) ->
      test_fun r (cone_sup_ball u uch ub1) <= N;
  (** Paper Lemma 3.9's morally-equivalent pointwise bound:
      [m r x ≤ cnorm x] for every [x]. Together with [test_lin0]
      etc. this says that [λ x. m r x] is a cones morphism
      [C ⊸ 1]. *)
  test_norm_le :
    forall (r : ar_carrier Ar X) (x : C),
      test_fun r x <= cone_norm x;
}.

End TestOf.

Arguments test_of {R} Ar X C.
Arguments test_fun {R Ar X C} t.

(** ** Equality of tests — extensionality plus [Prop_irrelevance] *)

Section TestEq.
Variables (R : realType) (Ar : MeasSubcat R) (X : ar_obj Ar) (C : coneType R).

(** Two tests are equal as soon as their underlying functions agree
    pointwise (in both arguments). Standard subtype extensionality. *)
Lemma test_eq (m1 m2 : test_of Ar X C) :
  (forall r x, test_fun m1 r x = test_fun m2 r x) -> m1 = m2.
Proof.
case: m1 => f1 me1 g1 l1 z1 a1 s1 c1 n1.
case: m2 => f2 me2 g2 l2 z2 a2 s2 c2 n2 /= Hfun.
have Hf : f1 = f2.
  by apply: funext => r; apply: funext => x; exact: Hfun.
move: me1 g1 l1 z1 a1 s1 c1 n1; rewrite Hf => me1 g1 l1 z1 a1 s1 c1 n1.
by congr MkTestOf; exact: Prop_irrelevance.
Qed.

End TestEq.

(** ** Generalized measurability — drop the unit-ball restriction

    The [test_meas] field of [test_of] only requires measurability of
    [λ r. m r x] for unit-ball [x] (i.e. when [cnorm x ≤ 1]). For
    downstream constructions (e.g. the env-dependent [bool_case]
    cascade) we need measurability for *arbitrary* [x : C].

    The standard scaling argument: if [s = cnorm x > 1], then
    [x' = (1/s) ·: x] satisfies [cnorm x' = 1 ≤ 1] (by [cone_normh]),
    so [test_meas] applies to [x']. By [test_linZ] (linearity of
    [test_fun] in its second argument),
    [test_fun m r x = s · test_fun m r x'], and multiplication by
    the constant [s] preserves measurability. *)

Section TestMeasGen.
Variables (R : realType) (Ar : MeasSubcat R) (X : ar_obj Ar) (C : coneType R).

(** Generalization of [test_meas]: measurability of [λ r. m r x] for
    *every* [x : C], not just unit-ball [x]. *)
Lemma test_meas_gen (m : test_of Ar X C) (x : C) :
  measurable_fun setT (fun r => test_fun m r x).
Proof.
have [Hx1|Hx1] := leP (cone_norm x) 1.
  exact: test_meas.
(* Case [1 < cone_norm x]. Rescale by [1/(cone_norm x)] to land in
   the unit ball, then lift back via [test_linZ]. *)
have cx_pos : 0 < cone_norm x.
  by apply: lt_trans Hx1; exact: ltr01.
have cx_inv_ge0 : 0 <= (cone_norm x)^-1.
  by rewrite invr_ge0 ltW.
pose r : {nonneg R} := NngNum cx_inv_ge0.
have r_num : r%:num = (cone_norm x)^-1 by [].
pose x' : C := precone_scale r x.
have cx' : cone_norm x' = 1.
  by rewrite /x' cone_normh r_num mulVf // gt_eqF.
have cx'_le1 : cone_norm x' <= 1 by rewrite cx'.
have key : forall s, test_fun m s x = cone_norm x * test_fun m s x'.
  move=> s.
  have Hxx' : x = precone_scale (NngNum (ltW cx_pos)) x'.
    rewrite /x' -[LHS]precone_scale_1 -precone_scale_A.
    congr precone_scale.
    by apply: nngnum_inj => /=; rewrite mulfV // gt_eqF.
  by rewrite {1}Hxx' test_linZ.
apply: (eq_measurable_fun (fun s => cone_norm x * test_fun m s x')).
  by move=> s _; rewrite key.
by apply: measurable_funM;
  [exact: measurable_cst|exact: test_meas].
Qed.

End TestMeasGen.

Arguments test_meas_gen {R Ar X C} m x.

(** ** Reindexing a test along an [ar_hom] — Paper Def 3.2 (Mscomp)

    Given [m : test_of Ar X C] and [φ ∈ ar_hom Ar Y X], the
    reindexed test [test_reindex φ m : test_of Ar Y C] is
    [λ s x. m (φ s) x]. The closure (Mscomp) of an [MCone]'s
    test family is stated via this operator. *)

Section TestReindex.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (Y X : ar_obj Ar) (C : coneType R).
Variable φ : ar_hom Ar Y X.
Variable m : test_of Ar X C.

(** Paper Def 3.2 (Mscomp): the reindexed test [m ∘ (φ × C)]. *)
Definition test_reindex_fun : ar_carrier Ar Y -> C -> R :=
  fun s x => test_fun m (φ s) x.

Lemma test_reindex_meas (x : C) :
  cone_norm x <= 1 ->
  measurable_fun setT (fun s => test_reindex_fun s x).
Proof.
move=> Hx; rewrite /test_reindex_fun.
by apply: (measurableT_comp (f := fun r => test_fun m r x));
  [exact: test_meas|exact: measurable_funPT].
Qed.

Lemma test_reindex_ge0 (s : ar_carrier Ar Y) (x : C) :
  0 <= test_reindex_fun s x.
Proof. exact: test_ge0. Qed.

Lemma test_reindex_le1 (s : ar_carrier Ar Y) (x : C) :
  cone_norm x <= 1 -> test_reindex_fun s x <= 1.
Proof. exact: test_le1. Qed.

Lemma test_reindex_lin0 (s : ar_carrier Ar Y) :
  test_reindex_fun s precone_zero = 0.
Proof. exact: test_lin0. Qed.

Lemma test_reindex_linD (s : ar_carrier Ar Y) (x y : C) :
  test_reindex_fun s (precone_add x y) =
  test_reindex_fun s x + test_reindex_fun s y.
Proof. exact: test_linD. Qed.

Lemma test_reindex_linZ (s : ar_carrier Ar Y) (r : {nonneg R}) (x : C) :
  test_reindex_fun s (precone_scale r x) = r%:num * test_reindex_fun s x.
Proof. exact: test_linZ. Qed.

Lemma test_reindex_cont
  (s : ar_carrier Ar Y) (u : nat -> C)
  (uch : forall n, precone_le (u n) (u n.+1))
  (ub1 : forall n, cone_norm (u n) <= 1)
  (N : R) :
  (forall n, test_reindex_fun s (u n) <= N) ->
  test_reindex_fun s (cone_sup_ball u uch ub1) <= N.
Proof. exact: test_cont. Qed.

Lemma test_reindex_norm_le (s : ar_carrier Ar Y) (x : C) :
  test_reindex_fun s x <= cone_norm x.
Proof. exact: test_norm_le. Qed.

(** Paper Def 3.2 (Mscomp): the packaged reindexed test. *)
Definition test_reindex : test_of Ar Y C :=
  MkTestOf test_reindex_meas test_reindex_ge0 test_reindex_le1
           test_reindex_lin0 test_reindex_linD test_reindex_linZ
           test_reindex_cont test_reindex_norm_le.

End TestReindex.

(** ** Transporting a test along a cone map — the [test_map] combinator

    Every "pullback of a test along a structural map of cones" in the
    development (product projections, equaliser inclusions, local-cone
    inclusions, …) repeats the same eight proof obligations of
    [test_of] for a carrier of the shape [λ r x. m r (f x)]. All of
    them are consequences of four properties of the map [f : D -> C] —
    linearity ([f_lin0], [f_linD], [f_linZ]) and norm-nonincreasingness
    ([f_norm]) — plus the transported ω-continuity clause [f_cont],
    which is the only part that genuinely depends on how [D]'s
    sup-ball is built.

    The carrier is passed *explicitly* as [g], together with its
    defining equation [gE : ∀ r x, g r x = m r (f x)] (typically
    [fun _ _ => erefl]). This keeps the client's own carrier constant
    as the first field of the resulting record, so that the usual
    [rewrite /myTest /= /myTest_fun] idiom keeps working downstream. *)

Section TestMap.
Variables (R : realType) (Ar : MeasSubcat R) (Y : ar_obj Ar).
Variables (C D : coneType R).
Variable f : D -> C.
Hypothesis f_lin0 : f precone_zero = precone_zero.
Hypothesis f_linD :
  forall x y : D, f (precone_add x y) = precone_add (f x) (f y).
Hypothesis f_linZ :
  forall (s : {nonneg R}) (x : D),
    f (precone_scale s x) = precone_scale s (f x).
Hypothesis f_norm : forall x : D, cone_norm (f x) <= cone_norm x.

Variable m : test_of Ar Y C.
(** The transported ω-continuity clause. It is stated for the fixed
    test [m], so it can be proved by any argument specific to [D]'s
    sup-ball (e.g. a translation trick); the other seven obligations
    are discharged once and for all below. *)
Hypothesis f_cont :
  forall (r : ar_carrier Ar Y) (u : nat -> D)
         (uch : forall n, precone_le (u n) (u n.+1))
         (ub1 : forall n, cone_norm (u n) <= 1)
         (N : R),
    (forall n, test_fun m r (f (u n)) <= N) ->
    test_fun m r (f (cone_sup_ball u uch ub1)) <= N.

Variable g : ar_carrier Ar Y -> D -> R.
Hypothesis gE : forall r x, g r x = test_fun m r (f x).

Lemma test_map_meas (x : D) :
  cone_norm x <= 1 -> measurable_fun setT (fun r => g r x).
Proof.
move=> Hx.
apply: (eq_measurable_fun (fun r => test_fun m r (f x))); first by move=> r _.
by apply: test_meas; exact: le_trans (f_norm x) Hx.
Qed.

Lemma test_map_ge0 (r : ar_carrier Ar Y) (x : D) : 0 <= g r x.
Proof. by rewrite gE; exact: test_ge0. Qed.

Lemma test_map_le1 (r : ar_carrier Ar Y) (x : D) :
  cone_norm x <= 1 -> g r x <= 1.
Proof.
by move=> Hx; rewrite gE; apply: test_le1; exact: le_trans (f_norm x) Hx.
Qed.

Lemma test_map_lin0 (r : ar_carrier Ar Y) : g r precone_zero = 0.
Proof. by rewrite gE f_lin0 test_lin0. Qed.

Lemma test_map_linD (r : ar_carrier Ar Y) (x y : D) :
  g r (precone_add x y) = g r x + g r y.
Proof. by rewrite !gE f_linD test_linD. Qed.

Lemma test_map_linZ (r : ar_carrier Ar Y) (s : {nonneg R}) (x : D) :
  g r (precone_scale s x) = s%:num * g r x.
Proof. by rewrite !gE f_linZ test_linZ. Qed.

Lemma test_map_cont
    (r : ar_carrier Ar Y) (u : nat -> D)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, cone_norm (u n) <= 1) (N : R) :
  (forall n, g r (u n) <= N) -> g r (cone_sup_ball u uch ub1) <= N.
Proof. by move=> HN; rewrite gE; apply: f_cont => n; rewrite -gE. Qed.

Lemma test_map_norm_le (r : ar_carrier Ar Y) (x : D) :
  g r x <= cone_norm x.
Proof.
by rewrite gE; apply: le_trans (test_norm_le _ _ _) _; exact: f_norm.
Qed.

(** The test [m] of [C] transported to [D] along [f]. *)
Definition test_map : test_of Ar Y D :=
  MkTestOf test_map_meas test_map_ge0 test_map_le1
           test_map_lin0 test_map_linD test_map_linZ
           test_map_cont test_map_norm_le.

Lemma test_mapE (r : ar_carrier Ar Y) (x : D) :
  test_fun test_map r x = test_fun m r (f x).
Proof. exact: gE. Qed.

End TestMap.

Arguments test_map {R Ar Y C D} f f_lin0 f_linD f_linZ f_norm m f_cont g gE.
Arguments test_mapE
  {R Ar Y C D} f f_lin0 f_linD f_linZ f_norm m f_cont g gE.

(** ** Tests that do not depend on the arity point — [test_const]

    A *base* test (one that is not transported from another cone) is
    frequently given by a single linear, ω-continuous, norm-bounded
    functional [φ : C -> R], used at every arity and constant in the
    arity point [r]. In that case (Msmeas) is [measurable_cst] and the
    unit-ball bound [test_le1] follows from [test_norm_le], so only
    the six genuinely cone-theoretic obligations remain.

    As for [test_map], the carrier [g] is passed explicitly together
    with [gE : ∀ r x, g r x = φ x]. *)

Section TestConst.
Variables (R : realType) (Ar : MeasSubcat R) (Y : ar_obj Ar).
Variable C : coneType R.
Variable φ : C -> R.
Hypothesis φ_ge0 : forall x : C, 0 <= φ x.
Hypothesis φ_lin0 : φ precone_zero = 0.
Hypothesis φ_linD : forall x y : C, φ (precone_add x y) = φ x + φ y.
Hypothesis φ_linZ :
  forall (s : {nonneg R}) (x : C), φ (precone_scale s x) = s%:num * φ x.
Hypothesis φ_cont :
  forall (u : nat -> C)
         (uch : forall n, precone_le (u n) (u n.+1))
         (ub1 : forall n, cone_norm (u n) <= 1)
         (N : R),
    (forall n, φ (u n) <= N) -> φ (cone_sup_ball u uch ub1) <= N.
Hypothesis φ_norm_le : forall x : C, φ x <= cone_norm x.

Variable g : ar_carrier Ar Y -> C -> R.
Hypothesis gE : forall r x, g r x = φ x.

Lemma test_const_meas (x : C) :
  cone_norm x <= 1 -> measurable_fun setT (fun r => g r x).
Proof.
move=> _; apply: (eq_measurable_fun (fun=> φ x)); first by move=> r _.
exact: measurable_cst.
Qed.

Lemma test_const_ge0 (r : ar_carrier Ar Y) (x : C) : 0 <= g r x.
Proof. by rewrite gE; exact: φ_ge0. Qed.

Lemma test_const_le1 (r : ar_carrier Ar Y) (x : C) :
  cone_norm x <= 1 -> g r x <= 1.
Proof. by move=> Hx; rewrite gE; exact: le_trans (φ_norm_le x) Hx. Qed.

Lemma test_const_lin0 (r : ar_carrier Ar Y) : g r precone_zero = 0.
Proof. by rewrite gE; exact: φ_lin0. Qed.

Lemma test_const_linD (r : ar_carrier Ar Y) (x y : C) :
  g r (precone_add x y) = g r x + g r y.
Proof. by rewrite !gE; exact: φ_linD. Qed.

Lemma test_const_linZ (r : ar_carrier Ar Y) (s : {nonneg R}) (x : C) :
  g r (precone_scale s x) = s%:num * g r x.
Proof. by rewrite !gE; exact: φ_linZ. Qed.

Lemma test_const_cont
    (r : ar_carrier Ar Y) (u : nat -> C)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, cone_norm (u n) <= 1) (N : R) :
  (forall n, g r (u n) <= N) -> g r (cone_sup_ball u uch ub1) <= N.
Proof. by move=> HN; rewrite gE; apply: φ_cont => n; rewrite -(gE r). Qed.

Lemma test_const_norm_le (r : ar_carrier Ar Y) (x : C) :
  g r x <= cone_norm x.
Proof. by rewrite gE; exact: φ_norm_le. Qed.

(** The arity-constant test attached to [φ]. *)
Definition test_const : test_of Ar Y C :=
  MkTestOf test_const_meas test_const_ge0 test_const_le1
           test_const_lin0 test_const_linD test_const_linZ
           test_const_cont test_const_norm_le.

Lemma test_constE (r : ar_carrier Ar Y) (x : C) :
  test_fun test_const r x = φ x.
Proof. exact: gE. Qed.

End TestConst.

Arguments test_const
  {R Ar Y C} φ φ_ge0 φ_lin0 φ_linD φ_linZ φ_cont φ_norm_le g gE.
Arguments test_constE
  {R Ar Y C} φ φ_ge0 φ_lin0 φ_linD φ_linZ φ_cont φ_norm_le g gE.

(** ** The [isMCone] HB mixin — Paper Def 3.2 / 3.6

    Over a [coneType R] and parameterized by an [MeasSubcat R],
    [isMCone] declares the family [mcone_M] of "selected" tests at
    each arity, plus the four conditions (Msmeas) (which is
    built-in to [test_of]), (Mscomp), (Mssep), (Msnorm). *)

HB.mixin Record isMCone (R : realType) (Ar : MeasSubcat R) C of Cone R C := {
  (** Paper Def 3.2: the family [M = (M_X)_{X ∈ Ar}]. *)
  mcone_M : forall X : ar_obj Ar, set (test_of Ar X C);
  (** Paper Def 3.2 (Mscomp): closure under reindexing by [ar_hom]. *)
  mcone_M_comp :
    forall (Y X : ar_obj Ar) (φ : ar_hom Ar Y X) (m : test_of Ar X C),
      mcone_M X m -> mcone_M Y (test_reindex φ m);
  (** Paper Def 3.2 (Mssep): tests at arity 0 separate points. *)
  mcone_M_sep :
    forall x1 x2 : C,
      (forall m : test_of Ar (ar_zero Ar) C,
        mcone_M (ar_zero Ar) m ->
        test_fun m (ar_zero_pt Ar) x1 = test_fun m (ar_zero_pt Ar) x2) ->
      x1 = x2;
  (** Paper Def 3.2 (Msnorm) (Remark 3.3 form): for non-zero [x]
      and ε > 0, a witness test at arity 0 reaches within ε of
      [cnorm x]. See file header for the simplification we adopt
      (omitting the [/||m||] factor). *)
  mcone_M_norm :
    forall (x : C) (eps : R),
      x <> precone_zero -> 0 < eps ->
      exists m : test_of Ar (ar_zero Ar) C,
        mcone_M (ar_zero Ar) m /\
        cone_norm x <= test_fun m (ar_zero_pt Ar) x + eps;
}.

HB.structure Definition MCone (R : realType) (Ar : MeasSubcat R) :=
  { C of Cone R C & isMCone R Ar C }.

(** Short alias for the structure type. The HB short-name machinery
    sometimes shuffles parameter order in unexpected ways when two
    parameters are present; we expose the alias by hand to control
    the parameter order. *)
Notation mconeType Ar := (MCone.type Ar) (only parsing).

(** ** Measurable paths — Paper Def 3.7

    A measurable path [γ : ar_carrier X -> C] is a *bounded* function
    such that, for every arity [Y ∈ Ar] and every test
    [m ∈ mcone_M Y], the function

      [λ (s, r) : ar_carrier Y × ar_carrier X. m s (γ r)]

    is measurable from [ar_carrier Y × ar_carrier X] to [R]. *)

Section MeasurablePath.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (C : MCone.type Ar) (X : ar_obj Ar).

(** Paper Def 3.7: boundedness + per-test measurability. *)
Definition is_measurable_path (γ : ar_carrier Ar X -> C) : Prop :=
  (exists M : R, forall r : ar_carrier Ar X, cone_norm (γ r) <= M) /\
  forall (Y : ar_obj Ar) (m : test_of Ar Y C),
    mcone_M Y m ->
    measurable_fun
      [set: (ar_carrier Ar Y * ar_carrier Ar X)%type]
      (fun p => test_fun m p.1 (γ p.2)).

End MeasurablePath.

(** ** Paper Lemma 3.9: constant paths are measurable *)

Section Lemma39.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (C : MCone.type Ar) (X : ar_obj Ar).

(** Paper Lemma 3.9: the constant function [γ r := x] is a measurable
    path. *)
Lemma const_path_measurable (x : C) :
  is_measurable_path (fun _ : ar_carrier Ar X => x).
Proof.
split.
  by exists (cone_norm x) => r; exact: lexx.
move=> Y m mM.
(* The map [p ↦ test_fun m p.1 x] is [fun r => test_fun m r x]
   composed with [fst]. The partial application is measurable for an
   *arbitrary* [x] by [test_meas_gen] (which performs the rescaling
   into the unit ball once and for all), and [fst] is measurable. *)
by apply: (measurableT_comp (f := fun r => test_fun m r x));
  [exact: test_meas_gen|exact: measurable_fst].
Qed.

End Lemma39.

(** ** Paper Lemma 3.10: precomposition by an [ar_hom] preserves
       measurability of paths *)

Section Lemma310.
Variables (R : realType) (Ar : MeasSubcat R) (C : MCone.type Ar).
Variables (Y X : ar_obj Ar) (γ : ar_carrier Ar X -> C) (φ : ar_hom Ar Y X).

(** Paper Lemma 3.10: if [γ : X -> C] is a measurable path and
    [φ ∈ ar_hom Ar Y X], then [γ ∘ φ : Y -> C] is a measurable path. *)
Lemma reindex_path_measurable :
  is_measurable_path γ -> is_measurable_path (γ \o φ).
Proof.
case=> [[M HM] Hmeas]; split.
  exists M => r /=; exact: HM.
move=> Y' m mM.
(* We need: [λ p : Y' × Y, m p.1 (γ (φ p.2))] measurable. By
   hypothesis, [λ q : Y' × X, m q.1 (γ q.2)] is measurable. The
   first function is the second composed with [⟨p.1, φ p.2⟩]. *)
have Hbase : measurable_fun
  [set: (ar_carrier Ar Y' * ar_carrier Ar X)%type]
  (fun q : (ar_carrier Ar Y' * ar_carrier Ar X)%type =>
     test_fun m q.1 (γ q.2)).
  exact: Hmeas.
have Hpair : measurable_fun
  [set: (ar_carrier Ar Y' * ar_carrier Ar Y)%type]
  (fun p : ar_carrier Ar Y' * ar_carrier Ar Y => (p.1, φ p.2)).
  apply: measurable_fun_pair; first exact: measurable_fst.
  by apply: (measurableT_comp (f := φ));
    [exact: measurable_funPT|exact: measurable_snd].
pose F (q : ar_carrier Ar Y' * ar_carrier Ar X) := test_fun m q.1 (γ q.2).
have -> : (fun p : ar_carrier Ar Y' * ar_carrier Ar Y =>
            test_fun m p.1 (γ (φ p.2))) = F \o (fun p => (p.1, φ p.2)).
  by apply: funext => p; rewrite /F.
by apply: measurableT_comp; [exact: Hbase|exact: Hpair].
Qed.

End Lemma310.

(** ** A useful consequence: Paper Lemma 3.9 in the [ε / dual-norm]
       form of Remark 3.3 (modulo our simplified (Msnorm))

    Given the [test_norm_le] field of every test (which gives a
    *uniform* operator-norm bound of [1]), the paper's
    [cnorm x ≤ m(x)/||m|| + ε] form is implied by our
    [cnorm x ≤ m(x) + ε]. This lemma is stated for documentation;
    no downstream client needs it as written. *)

