(** * The measurable cone of finite measures — Paper §3.2.1

    For any measurable space [X] (not necessarily in [Ar]), the set
    [FMeas(X)] of finite measures on [X] is a cone (paper Example 2.3
    / §2.2). For each [Y ∈ Ar] and each [U ∈ σ_X] the test
    [e_U(s, µ) = µ(U)] makes [FMeas(X)] a measurable cone (paper
    §3.2.1, top of page 1:20).

    Paper coverage of this file:
    - [fmeas R X] — the carrier of finite measures on a measurable
      space [X]. Paper §2.2 / Example 2.3.
    - [fmeas_zero], [fmeas_add], [fmeas_scale], [fmeas_norm] — the
      precone-and-norm operations.
    - Precone laws (associativity, commutativity, cancellation,
      positivity, scalar-distribution) over [fmeas R X]. Paper §2.1.
    - Cone norm axioms (Normh), (Normz), (Normt), (Normp) over
      [fmeas R X]. Paper §2.1.

    Design notes.

    - The carrier [fmeas R X] is a [Record] wrapping a measure with
      two extra invariants: it is *finite* on every measurable set,
      and it is *canonically extended* by [0] on non-measurable
      sets. Together these mean equality of [fmeas R X] elements
      reduces to equality on the σ-algebra (via [fmeas_eq]), which
      is what every cone-axiom proof actually needs. The
      canonicality invariant is preserved by [fmeas_zero],
      [fmeas_add], [fmeas_scale] by construction.

    - The (Normc) ω-completeness axiom for [fmeas R X] requires a
      construction of the supremum of an increasing chain of
      finite measures with bounded total mass, via a telescoping
      [mseries] of the cone-order differences (extracted via
      classical choice [cid] on the [exists] in [precone_le]). The
      construction of the diff measure has been mechanised but
      bundling it into the (Normc) lemma required deep wrestling
      with HB's section-discharge of [Definition] terms wrapping
      [{measure ...}] structure instances. We deferred the cone
      registration (and hence the [MCone] instance and Lemma 3.17)
      to a follow-up; what is registered here is just the
      [isPrecone] instance, providing all the algebra of finite
      measures plus their pointwise [norm].

    Deferred (clearly demarcated in the file as comments):

    - [isCone] registration on [fmeas R X] (waiting on a clean
      mseries-based (Normc) construction that survives section
      discharge).
    - [isMCone] structure with the family of tests [e_U] (paper
      §3.2.1).
    - Lemma 3.17 (pushforward as morphism in [MCones]) and the
      functor [FMeas : Ar → MCones].
*)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import ereal.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import measure measure_function.

Require Import Icones.prelude.classical_extra.
Require Import Icones.prelude.nonneg_extra.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** The carrier — Paper §2.2 / Example 2.3 *)

Section FMeasDef.
Variable R : realType.
Variable d : measure_display.
Variable X : measurableType d.

(** Paper §2.2 / Example 2.3: a finite measure on [X], packaged as a
    measure together with a finiteness invariant (every measurable
    set has finite measure) and a *canonicality* invariant: the
    underlying function returns [0] on every non-measurable set.
    Both invariants are needed so that equality of [fmeas R X]
    elements reduces to equality on the σ-algebra. *)
Definition fmeas_finP (mu : set X -> \bar R) : Prop :=
  forall U, measurable U -> mu U \is a fin_num.

Definition fmeas_canon (mu : set X -> \bar R) : Prop :=
  forall U, ~ measurable U -> mu U = 0.

Record fmeas : Type := MkFmeas {
  fmeas_mu :> {measure set X -> \bar R};
  fmeas_fin : fmeas_finP fmeas_mu;
  fmeas_canonical : fmeas_canon fmeas_mu;
}.

(** Extensional equality of finite measures: agreement on measurable
    sets suffices, since non-measurable U values are forced to [0]
    by canonicality. *)
Lemma fmeas_eq (m1 m2 : fmeas) :
  (forall U, measurable U -> fmeas_mu m1 U = fmeas_mu m2 U) -> m1 = m2.
Proof.
move=> Hm.
have Hall : forall U, fmeas_mu m1 U = fmeas_mu m2 U.
  move=> U; have [mU|nmU] := pselect (measurable U); first exact: Hm.
  by rewrite (@fmeas_canonical m1 U nmU) (@fmeas_canonical m2 U nmU).
have Eq : fmeas_mu m1 = fmeas_mu m2 :> {measure set X -> \bar R}.
  by apply: eq_measure; apply: funext.
case: m1 m2 Hm Hall Eq => mu1 fin1 can1 [mu2 fin2 can2] /= _ _ Eq.
move: fin1 can1 fin2 can2; rewrite Eq => fin1 can1 fin2 can2.
by congr MkFmeas; exact: Prop_irrelevance.
Qed.

End FMeasDef.

Arguments fmeas R {d} X.
Arguments MkFmeas {R d X}.
Arguments fmeas_mu {R d X}.
Arguments fmeas_fin {R d X}.
Arguments fmeas_canonical {R d X}.

(** ** The cone-algebraic operations *)

Section FMeasCone.
Variable R : realType.
Variable d : measure_display.
Variable X : measurableType d.

Local Open Scope ereal_scope.

(** *** The zero measure — Paper §2.2 *)
Lemma mzero_finP : @fmeas_finP R d X mzero.
Proof. by move=> U _. Qed.

Lemma mzero_canon : @fmeas_canon R d X mzero.
Proof. by move=> U _. Qed.

Definition fmeas_zero : fmeas R X := MkFmeas mzero mzero_finP mzero_canon.

(** *** Addition of finite measures *)
Section AddDef.
Variables m1 m2 : @fmeas R d X.

Lemma measure_add_finP : fmeas_finP (@measure_add _ X R m1 m2).
Proof.
move=> U mU; rewrite measure_addE fin_numD.
by apply/andP; split; exact: fmeas_fin.
Qed.

Lemma measure_add_canon : fmeas_canon (@measure_add _ X R m1 m2).
Proof.
move=> U nmU; rewrite measure_addE.
rewrite (@fmeas_canonical _ _ _ m1 U nmU)
        (@fmeas_canonical _ _ _ m2 U nmU).
by rewrite adde0.
Qed.

Definition fmeas_add : fmeas R X :=
  MkFmeas (measure_add m1 m2) measure_add_finP measure_add_canon.

End AddDef.

(** *** Scalar multiplication *)
Section ScaleDef.
Variables (r : {nonneg R}) (m : @fmeas R d X).

Lemma mscale_finP : fmeas_finP (@mscale _ X R r m).
Proof.
move=> U mU; rewrite /mscale fin_numM//; exact: fmeas_fin.
Qed.

Lemma mscale_canon : fmeas_canon (@mscale _ X R r m).
Proof.
by move=> U nmU; rewrite /mscale (@fmeas_canonical _ _ _ m U nmU) mule0.
Qed.

Definition fmeas_scale : fmeas R X :=
  MkFmeas (mscale r m) mscale_finP mscale_canon.

End ScaleDef.

(** *** Norm — total mass *)
Definition fmeas_norm (m : fmeas R X) : R := fine (m setT).

Lemma fmeas_setT_fin (m : fmeas R X) : m setT \is a fin_num.
Proof. by apply: fmeas_fin; exact: measurableT. Qed.

Lemma fmeas_setT_ge0 (m : fmeas R X) : 0 <= m setT.
Proof. exact: measure_ge0. Qed.

Lemma fmeas_norm_ge0 (m : fmeas R X) : (0 <= fmeas_norm m)%R.
Proof.
by rewrite /fmeas_norm -lee_fin fineK ?fmeas_setT_fin// measure_ge0.
Qed.

End FMeasCone.

Arguments fmeas_zero {R d X}.
Arguments fmeas_add {R d X} m1 m2.
Arguments fmeas_scale {R d X} r m.
Arguments fmeas_norm {R d X} m.

(** ** Precone axioms on [fmeas R X] *)

Section FMeasPrecone.
Variable R : realType.
Variable d : measure_display.
Variable X : measurableType d.

Local Open Scope ereal_scope.

(** Pointwise equation: [(m1 + m2) U = m1 U + m2 U]. *)
Lemma fmeas_addE (m1 m2 : fmeas R X) U :
  fmeas_mu (fmeas_add m1 m2) U = fmeas_mu m1 U + fmeas_mu m2 U.
Proof. exact: measure_addE. Qed.

(** Pointwise equation: [(r *: m) U = r * m U]. *)
Lemma fmeas_scaleE (r : {nonneg R}) (m : fmeas R X) U :
  fmeas_mu (fmeas_scale r m) U = r%:num%:E * fmeas_mu m U.
Proof. by []. Qed.

(** Pointwise equation: [0 U = 0]. *)
Lemma fmeas_zeroE U : fmeas_mu (fmeas_zero : fmeas R X) U = 0.
Proof. by []. Qed.

Lemma fmeas_addA : associative (@fmeas_add R d X).
Proof.
move=> x y z; apply: fmeas_eq => U _; rewrite !fmeas_addE.
by rewrite addeA.
Qed.

Lemma fmeas_addC : commutative (@fmeas_add R d X).
Proof.
move=> x y; apply: fmeas_eq => U _; rewrite !fmeas_addE.
by rewrite addeC.
Qed.

Lemma fmeas_add0 : left_id (fmeas_zero : fmeas R X) fmeas_add.
Proof.
move=> x; apply: fmeas_eq => U _; rewrite fmeas_addE fmeas_zeroE.
by rewrite add0e.
Qed.

Lemma fmeas_scale_DAr (r : {nonneg R}) (x y : fmeas R X) :
  fmeas_scale r (fmeas_add x y) = fmeas_add (fmeas_scale r x) (fmeas_scale r y).
Proof.
apply: fmeas_eq => U _; rewrite !fmeas_scaleE !fmeas_addE fmeas_scaleE.
by rewrite ge0_muleDr// measure_ge0.
Qed.

Lemma fmeas_scale_DAl (r s : {nonneg R}) (x : fmeas R X) :
  fmeas_scale ((r%:num + s%:num)%:nng)%R x =
  fmeas_add (fmeas_scale r x) (fmeas_scale s x).
Proof.
apply: fmeas_eq => U _; rewrite fmeas_addE !fmeas_scaleE/=.
by rewrite EFinD ge0_muleDl.
Qed.

Lemma fmeas_scale_A (r s : {nonneg R}) (x : fmeas R X) :
  fmeas_scale ((r%:num * s%:num)%:nng)%R x =
  fmeas_scale r (fmeas_scale s x).
Proof.
apply: fmeas_eq => U _; rewrite !fmeas_scaleE/=.
by rewrite EFinM muleA.
Qed.

Lemma fmeas_scale_1 (x : fmeas R X) : fmeas_scale (1%:nng)%R x = x.
Proof. by apply: fmeas_eq => U _; rewrite fmeas_scaleE/= mul1e. Qed.

Lemma fmeas_scale_0r (r : {nonneg R}) :
  fmeas_scale r (fmeas_zero : fmeas R X) = fmeas_zero.
Proof.
apply: fmeas_eq => U _; rewrite fmeas_scaleE fmeas_zeroE.
by rewrite mule0.
Qed.

Lemma fmeas_scale_0l (x : fmeas R X) :
  fmeas_scale (0%:nng)%R x = fmeas_zero.
Proof.
apply: fmeas_eq => U _; rewrite fmeas_scaleE fmeas_zeroE/=.
by rewrite mul0e.
Qed.

(** Pointwise inequality: [precone_le] of finite measures implies
    pointwise [≤] on measurable U. *)
Lemma fmeas_le_pointwise (x y : fmeas R X) U :
  measurable U ->
  (exists z : fmeas R X, y = fmeas_add x z) ->
  fmeas_mu x U <= fmeas_mu y U.
Proof.
move=> mU [z ->]; rewrite fmeas_addE.
by rewrite leeDl// measure_ge0.
Qed.

(** (Cancel): from [m + x = m + y] derive [x = y]. *)
Lemma fmeas_cancel : forall x y z : fmeas R X,
  fmeas_add x y = fmeas_add x z -> y = z.
Proof.
move=> x y z Hxyz; apply: fmeas_eq => U mU.
have Hp : fmeas_add x y U = fmeas_add x z U by rewrite Hxyz.
rewrite !fmeas_addE in Hp.
have Hxfin : x U \is a fin_num by exact: fmeas_fin.
have Hyfin : y U \is a fin_num by exact: fmeas_fin.
have Hzfin : z U \is a fin_num by exact: fmeas_fin.
have HfYZ : fine (y U) = fine (z U).
  by apply/(addrI (fine (x U))); rewrite -!fineD//; congr fine.
by rewrite -(fineK Hyfin) -(fineK Hzfin) HfYZ.
Qed.

(** (Pos): from [x + y = 0] derive [x = 0 ∧ y = 0]. *)
Lemma fmeas_pos : forall x y : fmeas R X,
  fmeas_add x y = fmeas_zero ->
  x = fmeas_zero /\ y = fmeas_zero.
Proof.
move=> x y Hxy0.
have H : forall U, measurable U -> fmeas_mu x U + fmeas_mu y U = 0.
  by move=> U mU; rewrite -fmeas_addE Hxy0.
split; apply: fmeas_eq => U mU; rewrite fmeas_zeroE.
- have Hxy := H U mU.
  have xge : 0 <= fmeas_mu x U by exact: measure_ge0.
  have yge : 0 <= fmeas_mu y U by exact: measure_ge0.
  by move/eqP: Hxy; rewrite padde_eq0// => /andP[/eqP-> _].
- have Hxy := H U mU.
  have xge : 0 <= fmeas_mu x U by exact: measure_ge0.
  have yge : 0 <= fmeas_mu y U by exact: measure_ge0.
  by move/eqP: Hxy; rewrite padde_eq0// => /andP[_ /eqP->].
Qed.

End FMeasPrecone.

(** Register the precone instance on [fmeas R X]. *)
HB.instance Definition _ (R : realType) (d : measure_display)
    (X : measurableType d) :=
  isPrecone.Build R (fmeas R X)
    (@fmeas_addA R d X) (@fmeas_addC R d X) (@fmeas_add0 R d X)
    (@fmeas_scale_DAr R d X) (@fmeas_scale_DAl R d X)
    (@fmeas_scale_A R d X)
    (@fmeas_scale_1 R d X) (@fmeas_scale_0r R d X) (@fmeas_scale_0l R d X)
    (@fmeas_cancel R d X) (@fmeas_pos R d X).

(** ** Cone-norm axioms: (Normh), (Normz), (Normt), (Normp)

    The (Normc) ω-completeness axiom and the full [isCone]
    registration are deferred — see the file header. *)

Section FMeasNormLaws.
Variable R : realType.
Variable d : measure_display.
Variable X : measurableType d.

Local Open Scope ereal_scope.

(** (Normh): [‖r *: x‖ = r * ‖x‖]. *)
Lemma fmeas_normh : forall (r : {nonneg R}) (x : fmeas R X),
  fmeas_norm (precone_scale r x) = (r%:num * fmeas_norm x)%R.
Proof.
move=> r x; rewrite /fmeas_norm /precone_scale/= /mscale.
by rewrite fineM//; apply: fmeas_setT_fin.
Qed.

(** (Normz): if [cnorm m = 0] then [m = 0]. *)
Lemma fmeas_normz : forall x : fmeas R X,
  fmeas_norm x = 0%R -> x = precone_zero.
Proof.
move=> x Hx; apply: fmeas_eq => U mU.
have Hfin : fmeas_mu x setT \is a fin_num by apply: fmeas_setT_fin.
have setT_eq0 : fmeas_mu x setT = 0.
  rewrite -(fineK Hfin).
  by rewrite (_ : fine (fmeas_mu x setT) = 0%R)// -Hx.
rewrite fmeas_zeroE.
apply/eqP; rewrite eq_le measure_ge0 andbT.
by rewrite -setT_eq0 le_measure ?inE//; exact: measurableT.
Qed.

(** (Normt): triangle inequality (in fact, equality). *)
Lemma fmeas_normt : forall x y : fmeas R X,
  (fmeas_norm (precone_add x y) <= fmeas_norm x + fmeas_norm y)%R.
Proof.
move=> x y; rewrite /fmeas_norm /precone_add/= fmeas_addE.
have Hx : fmeas_mu x setT \is a fin_num by apply: fmeas_setT_fin.
have Hy : fmeas_mu y setT \is a fin_num by apply: fmeas_setT_fin.
by rewrite fineD// lexx.
Qed.

(** (Normp): order-monotonicity. *)
Lemma fmeas_normp : forall x y : fmeas R X,
  precone_le x y -> (fmeas_norm x <= fmeas_norm y)%R.
Proof.
move=> x y Hxy; rewrite /fmeas_norm.
have Hx : fmeas_mu x setT \is a fin_num by apply: fmeas_setT_fin.
have Hy : fmeas_mu y setT \is a fin_num by apply: fmeas_setT_fin.
rewrite -lee_fin !fineK//.
apply: fmeas_le_pointwise; first exact: measurableT.
exact: Hxy.
Qed.

End FMeasNormLaws.
