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
      [fmeas_add], [fmeas_scale] by construction. Every other
      packaging of a set function as an [fmeas] (the sup measure, the
      two (Normc) difference witnesses, the pushforward) goes through
      the combinator [fmeas_canonize] (and its difference variant
      [fmeas_sub_canon]), which forces the value [0] off the σ-algebra
      and supplies the measure laws and the two invariants once and
      for all.

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
From mathcomp.analysis Require Import ereal.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measure.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import normedtype sequences.
Import numFieldTopology.Exports.

Require Import Icones.prelude.classical_extra.
Require Import Icones.prelude.nonneg_extra.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.cone_cat.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.

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

(** ** Helper: a single ereal-arithmetic identity used in σ-additivity. *)
Lemma efin_sub_add_distr (R : numDomainType) (a b c d : \bar R) :
  a \is a fin_num -> b \is a fin_num ->
  c \is a fin_num -> d \is a fin_num ->
  ((a - b) + (c - d) = (a + c) - (b + d))%E.
Proof.
move: a b c d => [a||] [b||] [c||] [d||] //= _ _ _ _.
rewrite -!EFinD; congr (_%:E).
rewrite -[in RHS]addrA opprD -addrA; congr (_ + _)%R.
by rewrite addrCA.
Qed.

(** ** Canonicalization off the σ-algebra — a reusable combinator

    Every [fmeas R X] must vanish outside the σ-algebra (invariant
    [fmeas_canon]), but the set functions we build below (an [mseries],
    a pushforward, a difference of two measures) do not vanish there in
    general. [fmeas_canonize m] forces the value [0] off the σ-algebra
    and keeps [m] on measurable sets; the lemmas of this section supply,
    once and for all, the measure laws and the two [fmeas] invariants of
    the canonicalized function. Every packaging of a set function as an
    [fmeas] in this file goes through it. *)

Definition fmeas_canonize (R : realType) (disp : measure_display)
    (X : measurableType disp) (m : set X -> \bar R) : set X -> \bar R :=
  fun A => if `[< measurable A >] then m A else 0%E.

Section FMeasCanonize.
Variable R : realType.
Variable disp : measure_display.
Variable X : measurableType disp.

Local Open Scope ereal_scope.

Section CanonizeFun.
Variable m : set X -> \bar R.

Lemma fmeas_canonizeE A : measurable A -> fmeas_canonize m A = m A.
Proof. by move=> mA; rewrite /fmeas_canonize asboolT. Qed.

Lemma fmeas_canonize_off A : ~ measurable A -> fmeas_canonize m A = 0.
Proof. by move=> nmA; rewrite /fmeas_canonize asboolF. Qed.

(** The canonicality invariant is automatic. *)
Lemma fmeas_canonize_canon : fmeas_canon (fmeas_canonize m).
Proof. exact: fmeas_canonize_off. Qed.

(** Finiteness is inherited from finiteness on the σ-algebra. *)
Lemma fmeas_canonize_finP :
  (forall A, measurable A -> m A \is a fin_num) ->
  fmeas_finP (fmeas_canonize m).
Proof. by move=> mfin A mA; rewrite fmeas_canonizeE//; exact: mfin. Qed.

End CanonizeFun.

(** *** Canonicalizing a measure: the measure laws are inherited. *)

Section CanonizeMeas.
Variable m : {measure set X -> \bar R}.

Lemma fmeas_canonize_meas_set0 : fmeas_canonize m set0 = 0.
Proof. by rewrite fmeas_canonizeE ?measurable0// measure0. Qed.

Lemma fmeas_canonize_meas_ge0 A : 0 <= fmeas_canonize m A.
Proof.
rewrite /fmeas_canonize; case: asboolP => mA; last exact: lexx.
exact: measure_ge0.
Qed.

Lemma fmeas_canonize_meas_sigma_additive :
  semi_sigma_additive (fmeas_canonize m).
Proof.
move=> F mF tF mUF.
have eqU : fmeas_canonize m (\bigcup_n F n) = m (\bigcup_n F n).
  by rewrite fmeas_canonizeE.
have eqi i : fmeas_canonize m (F i) = m (F i).
  by rewrite fmeas_canonizeE.
rewrite eqU.
have base := @measure_semi_sigma_additive _ _ R m F mF tF mUF.
have -> :
  (fun n => \sum_(0 <= i < n) fmeas_canonize m (F i)) =
  (fun n => \sum_(0 <= i < n) m (F i)).
  by apply: funext => n; apply: eq_bigr => i _; exact: eqi.
exact: base.
Qed.

End CanonizeMeas.

(** *** Canonicalizing the difference of two finite measures.

    If [m2 ≤ m1] on the σ-algebra and both are finite there, then
    [A ↦ m1 A - m2 A], canonicalized, is again a finite measure. This
    is the construction behind both (Normc) difference witnesses
    ([fmeas_sup_ball_ub] and [fmeas_lub_w]). The three side conditions
    are bundled as [fmeas_sub_wf] so that each law takes exactly one
    hypothesis. *)

Section CanonizeSub.
Variables m1 m2 : {measure set X -> \bar R}.

Definition fmeas_sub_canon : set X -> \bar R :=
  fmeas_canonize (fun A => m1 A - m2 A).

Definition fmeas_sub_wf : Prop :=
  [/\ forall A, measurable A -> m1 A \is a fin_num,
      forall A, measurable A -> m2 A \is a fin_num &
      forall A, measurable A -> m2 A <= m1 A].

Lemma fmeas_sub_canonE A :
  measurable A -> fmeas_sub_canon A = m1 A - m2 A.
Proof. exact: fmeas_canonizeE. Qed.

Lemma fmeas_sub_canon_off A : ~ measurable A -> fmeas_sub_canon A = 0.
Proof. exact: fmeas_canonize_off. Qed.

Lemma fmeas_sub_canon_canon : fmeas_canon fmeas_sub_canon.
Proof. exact: fmeas_canonize_canon. Qed.

Lemma fmeas_sub_canon_set0 : fmeas_sub_canon set0 = 0.
Proof. by rewrite fmeas_sub_canonE ?measurable0// !measure0 sube0. Qed.

Lemma fmeas_sub_canon_ge0 : fmeas_sub_wf -> forall A, 0 <= fmeas_sub_canon A.
Proof.
case=> _ f2 le21 A; rewrite /fmeas_sub_canon /fmeas_canonize.
case: asboolP => mA; last exact: lexx.
rewrite sube_ge0; first exact: le21.
by apply/orP; left; exact: f2.
Qed.

Lemma fmeas_sub_canon_fin :
  fmeas_sub_wf -> forall A, measurable A -> fmeas_sub_canon A \is a fin_num.
Proof.
case=> f1 f2 _ A mA; rewrite fmeas_sub_canonE//.
by rewrite fin_numB f1// f2.
Qed.

Lemma fmeas_sub_canon_finP : fmeas_sub_wf -> fmeas_finP fmeas_sub_canon.
Proof. by move=> wf; exact: fmeas_sub_canon_fin. Qed.

(** σ-additivity of the canonicalized difference: by σ-additivity of
    [m1] and [m2], using finiteness to distribute the subtraction over
    the partial sums. *)
Lemma fmeas_sub_canon_sigma_additive :
  fmeas_sub_wf -> semi_sigma_additive fmeas_sub_canon.
Proof.
move=> wf; have [f1 f2 _] := wf.
move=> F mF tF mUF.
have eqU : fmeas_sub_canon (\bigcup_n F n) =
           m1 (\bigcup_n F n) - m2 (\bigcup_n F n).
  by rewrite fmeas_sub_canonE.
have eqi i : fmeas_sub_canon (F i) = m1 (F i) - m2 (F i).
  by rewrite fmeas_sub_canonE.
rewrite eqU.
have H1 := @measure_semi_sigma_additive _ _ R m1 F mF tF mUF.
have H2 := @measure_semi_sigma_additive _ _ R m2 F mF tF mUF.
have lim1 : limn (fun n => \sum_(0 <= i < n) m1 (F i)) = m1 (\bigcup_n F n).
  exact: cvg_lim H1.
have lim2 : limn (fun n => \sum_(0 <= i < n) m2 (F i)) = m2 (\bigcup_n F n).
  exact: cvg_lim H2.
have cvg1 : cvgn (fun n => \sum_(0 <= i < n) m1 (F i))
  by apply/cvg_ex; exists (m1 (\bigcup_n F n)).
have cvg2 : cvgn (fun n => \sum_(0 <= i < n) m2 (F i))
  by apply/cvg_ex; exists (m2 (\bigcup_n F n)).
have f1F i : m1 (F i) \is a fin_num by exact: f1.
have f2F i : m2 (F i) \is a fin_num by exact: f2.
have sum1fin n : \sum_(0 <= i < n) m1 (F i) \is a fin_num.
  apply/sum_fin_numP => i _ _; exact: f1F.
have sum2fin n : \sum_(0 <= i < n) m2 (F i) \is a fin_num.
  apply/sum_fin_numP => i _ _; exact: f2F.
have step n :
  \sum_(0 <= i < n) fmeas_sub_canon (F i) =
  \sum_(0 <= i < n) m1 (F i) - \sum_(0 <= i < n) m2 (F i).
  elim: n => [|n IH].
    by rewrite !big_nil sube0.
  rewrite !big_nat_recr//= IH eqi.
  exact: efin_sub_add_distr.
have -> :
  (fun n => \sum_(0 <= i < n) fmeas_sub_canon (F i)) =
  (fun n => \sum_(0 <= i < n) m1 (F i) - \sum_(0 <= i < n) m2 (F i)).
  by apply: funext => n; exact: step.
have Hfin1 : m1 (\bigcup_n F n) \is a fin_num by exact: f1.
have Hfin2 : m2 (\bigcup_n F n) \is a fin_num by exact: f2.
rewrite -lim1 -lim2.
apply: cvgeB => //.
have e1 : (\big[+%E/0%R]_(0 <= i <oo) m1 (F i)) = m1 (\bigcup_n F n)
  by exact: lim1.
by rewrite e1 fin_num_adde_defr.
Qed.

End CanonizeSub.

End FMeasCanonize.

(** ** (Normc) ω-completeness via telescoping [mseries] — Paper §2.1
       (footnote on page 1:10) and §3.2.1.

    Given an increasing chain [u : nat -> fmeas R X] in the unit ball
    (i.e. [forall n, fmeas_norm (u n) <= 1]), we build a finite measure
    [fmeas_sup_meas u uch ub1] which is the pointwise supremum of the
    chain. Construction strategy: by [cid] we extract for each [n] a
    "difference" finite measure [δ n] with [u n.+1 = u n + δ n] (in the
    precone sense); then [mseries] of the sequence [u 0 :: δ 0 :: δ 1 :: …]
    is the desired pointwise supremum, by the partial-sum equation
    [u n = u 0 + δ 0 + … + δ n.-1].

    All definitions are kept at the top level (no surrounding [Section]
    that varies [R] / [X]) so that HB structure-discharge does not
    interfere with the resulting [Definition] terms. *)

(** *** Top-level differences and the candidate sup measure *)

(** The cone-order difference witness — Paper §2.1. Given [u n ≤p u n.+1]
    as guaranteed by the chain hypothesis, [fmeas_diff] extracts the
    [fmeas R X] [δ] with [u n.+1 = u n + δ] using [cid]. *)
Definition fmeas_diff (R : realType) (disp : measure_display)
    (X : measurableType disp)
    (u : nat -> fmeas R X)
    (uch : forall n, precone_le (u n) (u n.+1))
    (n : nat) : fmeas R X :=
  projT1 (cid (uch n)).

Lemma fmeas_diffE (R : realType) (disp : measure_display)
    (X : measurableType disp)
    (u : nat -> fmeas R X)
    (uch : forall n, precone_le (u n) (u n.+1))
    (n : nat) :
  u n.+1 = fmeas_add (u n) (fmeas_diff uch n).
Proof. exact: projT2 (cid (uch n)). Qed.

(** The telescoping sequence of measures: [dseq 0 = u 0],
    [dseq n.+1 = δ n]. *)
Definition fmeas_dseq (R : realType) (disp : measure_display)
    (X : measurableType disp)
    (u : nat -> fmeas R X)
    (uch : forall n, precone_le (u n) (u n.+1))
    (n : nat) : {measure set X -> \bar R} :=
  match n with
  | 0 => fmeas_mu (u 0)
  | n.+1 => fmeas_mu (fmeas_diff uch n)
  end.

(** The candidate pointwise-sup measure, as a [{measure set X -> \bar R}]
    instance derived from [mseries]. *)
Definition fmeas_sup_meas_fun (R : realType) (disp : measure_display)
    (X : measurableType disp)
    (u : nat -> fmeas R X)
    (uch : forall n, precone_le (u n) (u n.+1)) :
    {measure set X -> \bar R} :=
  [the {measure set X -> \bar R} of mseries (fmeas_dseq uch) 0].

Section FMeasSupBallTheory.
Variable R : realType.
Variable disp : measure_display.
Variable X : measurableType disp.
Variable u : nat -> fmeas R X.
Variable uch : forall n, precone_le (u n) (u n.+1).
Implicit Type A : set X.

Local Open Scope ereal_scope.

(** Partial sums of the telescoping sequence: [u n A] equals the partial
    sum [\sum_(k < n.+1) dseq k A]. By induction. *)
Lemma fmeas_partial_sum n A :
  fmeas_mu (u n) A = \sum_(k < n.+1) fmeas_dseq uch k A.
Proof.
elim: n => [|n IH].
  by rewrite big_ord_recl big_ord0 adde0/=.
rewrite big_ord_recr/= -IH/=.
have -> : u n.+1 = fmeas_add (u n) (fmeas_diff uch n) by exact: fmeas_diffE.
by rewrite fmeas_addE.
Qed.

(** Partial-sum equality in the [\sum_(0 <= k < m)] form, more useful
    when matching [mseries]. *)
Lemma fmeas_partial_sumE n A :
  fmeas_mu (u n) A = \sum_(0 <= k < n.+1) fmeas_dseq uch k A.
Proof. by rewrite fmeas_partial_sum big_mkord. Qed.

(** Pointwise bound: each [u n A] is bounded by [fmeas_sup_meas_fun]. *)
Lemma fmeas_partial_le_mseries n A :
  fmeas_mu (u n) A <= fmeas_sup_meas_fun uch A.
Proof.
rewrite fmeas_partial_sumE /fmeas_sup_meas_fun /= /mseries ereal_series.
apply: nneseries_lim_ge => i _ _; exact: measure_ge0.
Qed.

(** The candidate sup is the pointwise limit of [u n A]: the sequence
    [u n A] converges (it is non-decreasing and bounded above by
    [fmeas_sup_meas_fun A]). *)
Lemma fmeas_sup_cvg A :
  measurable A ->
  fmeas_mu (u n) A
    @[n --> \oo] --> fmeas_sup_meas_fun uch A.
Proof.
move=> mA.
have nd : forall n, fmeas_mu (u n) A <= fmeas_mu (u n.+1) A.
  move=> n; rewrite [in leRHS](fmeas_diffE uch n) fmeas_addE.
  by rewrite leeDl// measure_ge0.
have homo_u :
    {homo (fun n => fmeas_mu (u n) A) : i j / (i <= j)%N >-> i <= j}.
  apply/nondecreasing_seqP => n; exact: nd.
have := ereal_nondecreasing_cvgn homo_u.
suff -> : ereal_sup (range (fun n => fmeas_mu (u n) A)) =
          fmeas_sup_meas_fun uch A by [].
apply: le_anti; apply/andP; split.
  apply: ge_ereal_sup => _ [n _ <-]; exact: fmeas_partial_le_mseries.
(* mseries dseq 0 A = lim_(n) sum_(k < n) dseq k A
                    = lim_(n) u_(n-1) A    (for n >= 1)
                    ≤ ereal_sup of (u_n A) *)
rewrite /fmeas_sup_meas_fun /= /mseries ereal_series.
have nde : {homo
  (fun n => \sum_(0 <= k < n) fmeas_dseq uch k A) :
    i j / (i <= j)%N >-> i <= j}.
  apply/nondecreasing_seqP => n.
  rewrite big_nat_recr/=; last by [].
  by rewrite leeDl// measure_ge0.
have ndcvg :=
  ereal_nondecreasing_cvgn nde.
apply: lime_le.
  apply/cvg_ex; exists (ereal_sup (range
    (fun n => \sum_(0 <= k < n) fmeas_dseq uch k A))); exact: ndcvg.
apply: nearW => -[|n].
  rewrite big_nil.
  apply: (@le_trans _ _ (fmeas_mu (u 0) A)).
    exact: measure_ge0.
  by apply: ereal_sup_ubound; exists 0%N.
rewrite -fmeas_partial_sumE.
by apply: ereal_sup_ubound; exists n.
Qed.

End FMeasSupBallTheory.

(** *** Packaging as a [fmeas R X] and the cone operation [cone_sup_ball] *)

Section FMeasSupBallPkg.
Variable R : realType.
Variable disp : measure_display.
Variable X : measurableType disp.
Variable u : nat -> fmeas R X.
Variable uch : forall n, precone_le (u n) (u n.+1).
Variable ub1 : forall n, (fmeas_norm (u n) <= 1)%R.

Local Open Scope ereal_scope.

(** [fmeas_sup_meas_fun setT] is bounded by [1]. *)
Lemma fmeas_sup_meas_setT_le1 : fmeas_sup_meas_fun uch [set: X] <= 1.
Proof.
have cvg_setT := @fmeas_sup_cvg R disp X u uch _ (@measurableT _ X).
have lim_eq : limn (fun n => fmeas_mu (u n) [set: X]) =
              fmeas_sup_meas_fun uch [set: X].
  exact: cvg_lim cvg_setT.
rewrite -lim_eq.
apply: lime_le.
  by apply/cvg_ex; exists (fmeas_sup_meas_fun uch [set: X]); exact: cvg_setT.
apply: nearW => n.
have Hfin : fmeas_mu (u n) [set: X] \is a fin_num by exact: fmeas_setT_fin.
rewrite -(fineK Hfin) lee_fin; exact: ub1.
Qed.

(** [fmeas_sup_meas_fun setT] is finite (since bounded by 1 < +∞). *)
Lemma fmeas_sup_meas_setT_fin :
  fmeas_sup_meas_fun uch [set: X] \is a fin_num.
Proof.
rewrite ge0_fin_numE; last exact: measure_ge0.
apply: le_lt_trans fmeas_sup_meas_setT_le1 _.
by rewrite ltry.
Qed.

(** [fmeas_sup_meas_fun] is finite on every measurable set. *)
Lemma fmeas_sup_meas_finP : fmeas_finP (fmeas_sup_meas_fun uch).
Proof.
move=> U mU; rewrite ge0_fin_numE; last exact: measure_ge0.
apply: (@le_lt_trans _ _ (fmeas_sup_meas_fun uch [set: X])).
  by apply: le_measure => //; rewrite inE.
have Hfin : fmeas_sup_meas_fun uch [set: X] \is a fin_num
  by exact: fmeas_sup_meas_setT_fin.
by rewrite ltey_eq Hfin.
Qed.

(** The canonicality invariant for the sup measure: for non-measurable
    sets we *redefine* the value to be [0] via a wrapping, since
    [mseries] of measures doesn't automatically vanish off the
    σ-algebra. *)
Definition fmeas_sup_meas_canon_fun : set X -> \bar R :=
  fmeas_canonize (fmeas_sup_meas_fun uch).

Lemma fmeas_sup_meas_canon_fun_E A :
  measurable A -> fmeas_sup_meas_canon_fun A = fmeas_sup_meas_fun uch A.
Proof. exact: fmeas_canonizeE. Qed.

Lemma fmeas_sup_meas_canon_fun_off A :
  ~ measurable A -> fmeas_sup_meas_canon_fun A = 0.
Proof. exact: fmeas_canonize_off. Qed.

Lemma fmeas_sup_meas_canon_set0 : fmeas_sup_meas_canon_fun set0 = 0.
Proof. exact: fmeas_canonize_meas_set0. Qed.

Lemma fmeas_sup_meas_canon_ge0 A : 0 <= fmeas_sup_meas_canon_fun A.
Proof. exact: fmeas_canonize_meas_ge0. Qed.

Lemma fmeas_sup_meas_canon_sigma_additive :
  semi_sigma_additive fmeas_sup_meas_canon_fun.
Proof. exact: fmeas_canonize_meas_sigma_additive. Qed.

HB.instance Definition _ :=
  isMeasure.Build _ _ _ fmeas_sup_meas_canon_fun
    fmeas_sup_meas_canon_set0 fmeas_sup_meas_canon_ge0
    fmeas_sup_meas_canon_sigma_additive.

(** Canonicality of the candidate sup measure (post-restriction). *)
Lemma fmeas_sup_meas_canon_canon : fmeas_canon fmeas_sup_meas_canon_fun.
Proof. exact: fmeas_canonize_canon. Qed.

(** Finiteness of the canonicalized sup measure. *)
Lemma fmeas_sup_meas_canon_finP : fmeas_finP fmeas_sup_meas_canon_fun.
Proof.
by apply: fmeas_canonize_finP; exact: fmeas_sup_meas_finP.
Qed.

(** The (Normc) witness — Paper §2.1, ω-completeness of the unit ball. *)
Definition fmeas_sup_ball : fmeas R X :=
  MkFmeas
    [the {measure set X -> \bar R} of fmeas_sup_meas_canon_fun]
    fmeas_sup_meas_canon_finP
    fmeas_sup_meas_canon_canon.

Lemma fmeas_sup_ballE U :
  measurable U ->
  fmeas_mu fmeas_sup_ball U = fmeas_sup_meas_fun uch U.
Proof. exact: fmeas_sup_meas_canon_fun_E. Qed.

End FMeasSupBallPkg.

(** *** Cone-order properties of [fmeas_sup_ball] *)

(** The (Normc) [cone_sup_ball_norm] property: [‖fmeas_sup_ball‖ ≤ 1]. *)
Lemma fmeas_sup_ball_norm (R : realType) (disp : measure_display)
    (X : measurableType disp)
    (u : nat -> fmeas R X)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, (fmeas_norm (u n) <= 1)%R) :
  (fmeas_norm (fmeas_sup_ball uch ub1) <= 1)%R.
Proof.
rewrite /fmeas_norm (fmeas_sup_ballE _ ub1 measurableT).
have Hfin : fmeas_sup_meas_fun uch [set: X] \is a fin_num
  by exact: fmeas_sup_meas_setT_fin uch ub1.
rewrite -lee_fin fineK//.
exact: fmeas_sup_meas_setT_le1 uch ub1.
Qed.

(** *** Helper: building the LUB witness [w] such that
       [y = sup_ball + w] *)

(** The LUB difference, as a function set X -> \bar R: [y A - sup A] on
    measurable sets, zero off them. This is non-negative and finite,
    and we will register it as a measure to package as a [fmeas]. *)
Section FMeasSupLUBWitness.
Variable R : realType.
Variable disp : measure_display.
Variable X : measurableType disp.
Variable u : nat -> fmeas R X.
Variable uch : forall n, precone_le (u n) (u n.+1).
Variable ub1 : forall n, (fmeas_norm (u n) <= 1)%R.
Variable y : fmeas R X.
Hypothesis Hy : forall n, precone_le (u n) y.

Local Open Scope ereal_scope.

(** Pointwise: each [u n A ≤ y A] on every measurable A. *)
Lemma fmeas_lub_un_le_y n A :
  measurable A -> fmeas_mu (u n) A <= fmeas_mu y A.
Proof.
move=> mA; apply: fmeas_le_pointwise => //.
exact: Hy.
Qed.

(** Pointwise: [sup A ≤ y A] on every measurable A. *)
Lemma fmeas_lub_sup_le_y A :
  measurable A -> fmeas_sup_meas_fun uch A <= fmeas_mu y A.
Proof.
move=> mA.
have cvg_A := @fmeas_sup_cvg R disp X u uch _ mA.
have lim_eq : limn (fun n => fmeas_mu (u n) A) =
              fmeas_sup_meas_fun uch A.
  exact: cvg_lim cvg_A.
rewrite -lim_eq.
apply: lime_le.
  by apply/cvg_ex; exists (fmeas_sup_meas_fun uch A); exact: cvg_A.
apply: nearW => n; exact: fmeas_lub_un_le_y.
Qed.

(** The LUB witness function: [y A - sup A] on measurable sets,
    [0] on non-measurable. *)
Definition fmeas_lub_w_fun : set X -> \bar R :=
  fmeas_sub_canon (fmeas_mu y) (fmeas_sup_meas_fun uch).

(** The side conditions of the difference construction: both measures
    are finite on the σ-algebra, and [sup ≤ y] there. *)
Lemma fmeas_lub_w_wf : fmeas_sub_wf (fmeas_mu y) (fmeas_sup_meas_fun uch).
Proof.
split.
- by move=> A mA; exact: fmeas_fin.
- by move=> A mA; exact: (fmeas_sup_meas_finP uch ub1).
- by move=> A mA; exact: fmeas_lub_sup_le_y.
Qed.

Lemma fmeas_lub_w_fun_E A :
  measurable A ->
  fmeas_lub_w_fun A = fmeas_mu y A - fmeas_sup_meas_fun uch A.
Proof. exact: fmeas_sub_canonE. Qed.

Lemma fmeas_lub_w_fun_off A :
  ~ measurable A -> fmeas_lub_w_fun A = 0.
Proof. exact: fmeas_sub_canon_off. Qed.

Lemma fmeas_lub_w_set0 : fmeas_lub_w_fun set0 = 0.
Proof. exact: fmeas_sub_canon_set0. Qed.

Lemma fmeas_lub_w_ge0 A : 0 <= fmeas_lub_w_fun A.
Proof. exact: (fmeas_sub_canon_ge0 fmeas_lub_w_wf). Qed.

Lemma fmeas_lub_w_fin A :
  measurable A -> fmeas_lub_w_fun A \is a fin_num.
Proof. exact: (fmeas_sub_canon_fin fmeas_lub_w_wf). Qed.

(** σ-additivity of [fmeas_lub_w_fun]: by σ-additivity of [y] and [sup],
    using finiteness to distribute the subtraction. *)
Lemma fmeas_lub_w_sigma_additive : semi_sigma_additive fmeas_lub_w_fun.
Proof. exact: (fmeas_sub_canon_sigma_additive fmeas_lub_w_wf). Qed.

HB.instance Definition _ :=
  isMeasure.Build _ _ _ fmeas_lub_w_fun
    fmeas_lub_w_set0 fmeas_lub_w_ge0 fmeas_lub_w_sigma_additive.

Lemma fmeas_lub_w_finP : fmeas_finP fmeas_lub_w_fun.
Proof. exact: (fmeas_sub_canon_finP fmeas_lub_w_wf). Qed.

Lemma fmeas_lub_w_canon : fmeas_canon fmeas_lub_w_fun.
Proof. exact: fmeas_sub_canon_canon. Qed.

(** The LUB witness, packaged as a [fmeas R X]. *)
Definition fmeas_lub_w : fmeas R X :=
  MkFmeas
    [the {measure set X -> \bar R} of fmeas_lub_w_fun]
    fmeas_lub_w_finP
    fmeas_lub_w_canon.

(** The key equation: [y = fmeas_sup_ball + fmeas_lub_w]. *)
Lemma fmeas_lub_wE : y = fmeas_add (fmeas_sup_ball uch ub1) fmeas_lub_w.
Proof.
apply: fmeas_eq => U mU.
rewrite fmeas_addE/= fmeas_lub_w_fun_E// (fmeas_sup_ballE _ ub1 mU)/=.
by rewrite addeC subeK// (fmeas_sup_meas_finP uch ub1).
Qed.

End FMeasSupLUBWitness.

Section FMeasSupBallUB.
Local Open Scope ereal_scope.
Variable R : realType.
Variable disp : measure_display.
Variable X : measurableType disp.
Variable u : nat -> fmeas R X.
Variable uch : forall n, precone_le (u n) (u n.+1).
Variable ub1 : forall n, (fmeas_norm (u n) <= 1)%R.

(** *** The (Normc) UB property *)
Lemma fmeas_sup_ball_ub n :
  precone_le (u n) (fmeas_sup_ball uch ub1).
Proof.
(* We need [w : fmeas R X] with [fmeas_sup_ball = u n + w]: it is the
   canonicalized difference [sup - u n], which the generic combinator
   [fmeas_sub_canon] turns into a finite measure. *)
have wf : fmeas_sub_wf (fmeas_sup_meas_fun uch) (fmeas_mu (u n)).
  split.
  - by move=> A mA; exact: (fmeas_sup_meas_finP uch ub1).
  - by move=> A mA; exact: fmeas_fin.
  - by move=> A _; exact: (fmeas_partial_le_mseries uch n A).
pose w_fun := fmeas_sub_canon (fmeas_sup_meas_fun uch) (fmeas_mu (u n)).
have w_fun_E A :
  measurable A -> w_fun A = fmeas_sup_meas_fun uch A - fmeas_mu (u n) A.
  exact: fmeas_sub_canonE.
have w_fun_off A : ~ measurable A -> w_fun A = 0.
  exact: fmeas_sub_canon_off.
have w_set0 : w_fun set0 = 0 by apply: fmeas_sub_canon_set0.
have w_ge0 A : 0 <= w_fun A by apply: fmeas_sub_canon_ge0; exact: wf.
have w_fin A : measurable A -> (w_fun A \is a fin_num).
  by apply: fmeas_sub_canon_fin; exact: wf.
have w_sigma_additive : semi_sigma_additive w_fun.
  by apply: fmeas_sub_canon_sigma_additive; exact: wf.
have wMeas : isMeasure.axioms_ disp X R w_fun :=
  isMeasure.Build disp X R w_fun w_set0 w_ge0 w_sigma_additive.
pose w0 : {measure set X -> \bar R} :=
  HB.pack_for {measure set X -> \bar R} w_fun wMeas.
have w_finP : fmeas_finP w0 by exact: w_fin.
have w_canon : fmeas_canon w0 by exact: w_fun_off.
exists (MkFmeas w0 w_finP w_canon).
apply: fmeas_eq => U mU.
rewrite fmeas_addE/= (fmeas_sup_ballE _ ub1 mU)/=.
rewrite /w0/= w_fun_E// addeC subeK//.
exact: fmeas_fin.
Qed.

End FMeasSupBallUB.

(** *** The (Normc) LUB property *)
Lemma fmeas_sup_ball_lub (R : realType) (disp : measure_display)
    (X : measurableType disp)
    (u : nat -> fmeas R X)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, (fmeas_norm (u n) <= 1)%R)
    (y : fmeas R X) :
  (forall n, precone_le (u n) y) ->
  precone_le (fmeas_sup_ball uch ub1) y.
Proof.
move=> Hy.
exists (fmeas_lub_w uch ub1 Hy).
exact: fmeas_lub_wE.
Qed.

(** ** Register the cone instance on [fmeas R X] — Paper §2.1 *)

HB.instance Definition _ (R : realType) (disp : measure_display)
    (X : measurableType disp) :=
  @isCone.Build R (fmeas R X)
    (@fmeas_norm R disp X)
    (@fmeas_normh R disp X) (@fmeas_normz R disp X)
    (@fmeas_normt R disp X) (@fmeas_normp R disp X)
    (@fmeas_sup_ball R disp X)
    (@fmeas_sup_ball_ub R disp X)
    (@fmeas_sup_ball_lub R disp X)
    (@fmeas_sup_ball_norm R disp X).

(** ** The measurable-cone structure on [fmeas R X] — Paper §3.2.1

    The test family [M_Y(FMeas X)] consists of the tests
    [e_U(s, µ) = µ U] indexed by [U : set X] measurable. These are
    constant in [s], so (Mscomp) is trivial. (Mssep) is [fmeas_eq];
    (Msnorm) is from [cnorm µ = µ setT] (a particular value of the
    sup). *)

Section FMeasMCone.
Variable R : realType.
Variable Ar : MeasSubcat R.
Variable disp : measure_display.
Variable X : measurableType disp.

(** Paper §3.2.1: the test [e_U] for a measurable [U : set X] at any
    arity [Y]. The function is constant in [s], returning
    [fine (µ U)]. *)
Section FMeasEU.
Variable Y : ar_obj Ar.
Variable U : set X.
Hypothesis mU : measurable U.

Definition eU_fun : ar_carrier Ar Y -> fmeas R X -> R :=
  fun _ µ => fine (fmeas_mu µ U).

Lemma eU_meas (µ : fmeas R X) :
  cone_norm µ <= 1 ->
  measurable_fun setT (fun s => eU_fun s µ).
Proof. by move=> _; exact: measurable_cst. Qed.

Lemma eU_ge0 (s : ar_carrier Ar Y) (µ : fmeas R X) :
  (0 <= eU_fun s µ)%R.
Proof.
rewrite /eU_fun -lee_fin fineK.
- exact: measure_ge0.
- exact: fmeas_fin.
Qed.

Lemma eU_le1 (s : ar_carrier Ar Y) (µ : fmeas R X) :
  cone_norm µ <= 1 -> (eU_fun s µ <= 1)%R.
Proof.
move=> Hµ; rewrite /eU_fun.
have Hfin : fmeas_mu µ U \is a fin_num by exact: fmeas_fin.
rewrite -lee_fin fineK//.
apply: (@le_trans _ _ (fmeas_mu µ [set: X])).
  by apply: le_measure => //; rewrite inE.
have HsetTfin : fmeas_mu µ [set: X] \is a fin_num by exact: fmeas_setT_fin.
by rewrite -(fineK HsetTfin) lee_fin.
Qed.

Lemma eU_lin0 (s : ar_carrier Ar Y) :
  eU_fun s (precone_zero : fmeas R X) = 0%R.
Proof. by rewrite /eU_fun /=. Qed.

Lemma eU_linD (s : ar_carrier Ar Y) (µ1 µ2 : fmeas R X) :
  eU_fun s (precone_add µ1 µ2) = (eU_fun s µ1 + eU_fun s µ2)%R.
Proof.
rewrite /eU_fun /precone_add/= fmeas_addE.
by rewrite fineD; first by []; exact: fmeas_fin.
Qed.

Lemma eU_linZ (s : ar_carrier Ar Y) (r : {nonneg R}) (µ : fmeas R X) :
  eU_fun s (precone_scale r µ) = (r%:num * eU_fun s µ)%R.
Proof.
rewrite /eU_fun /precone_scale/= /mscale.
by rewrite fineM//; exact: fmeas_fin.
Qed.

Lemma eU_cont
    (s : ar_carrier Ar Y)
    (u : nat -> fmeas R X)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, cone_norm (u n) <= 1)
    (N : R) :
  (forall n, (eU_fun s (u n) <= N)%R) ->
  (eU_fun s (cone_sup_ball u uch ub1) <= N)%R.
Proof.
move=> HN.
rewrite /eU_fun /=.
rewrite (fmeas_sup_ballE _ ub1 mU).
have cvg_eU := @fmeas_sup_cvg R disp X u uch _ mU.
have Hsfin : fmeas_sup_meas_fun uch U \is a fin_num
  by exact: (fmeas_sup_meas_finP uch ub1).
rewrite -lee_fin fineK//.
have lim_eq : limn (fun n => fmeas_mu (u n) U) = fmeas_sup_meas_fun uch U.
  exact: cvg_lim cvg_eU.
rewrite -lim_eq.
apply: lime_le.
  by apply/cvg_ex; exists (fmeas_sup_meas_fun uch U).
apply: nearW => n.
have Hufin : fmeas_mu (u n) U \is a fin_num by exact: fmeas_fin.
by rewrite -(fineK Hufin) lee_fin; exact: HN.
Qed.

Lemma eU_norm_le (s : ar_carrier Ar Y) (µ : fmeas R X) :
  (eU_fun s µ <= cone_norm µ)%R.
Proof.
rewrite /eU_fun /cone_norm/= /fmeas_norm.
have Hsetfin : fmeas_mu µ [set: X] \is a fin_num by exact: fmeas_setT_fin.
have HUfin : fmeas_mu µ U \is a fin_num by exact: fmeas_fin.
rewrite -lee_fin !fineK//.
by apply: le_measure => //; rewrite inE.
Qed.

(** Paper §3.2.1: the packaged test [e_U]. *)
Definition fmeas_eU : test_of Ar Y (fmeas R X) :=
  MkTestOf eU_meas eU_ge0 eU_le1 eU_lin0 eU_linD eU_linZ eU_cont eU_norm_le.

(** [fmeas_eU] is pointwise [fine (µ U)], constant in [s]. *)
Lemma fmeas_eUE (s : ar_carrier Ar Y) (µ : fmeas R X) :
  test_fun fmeas_eU s µ = fine (fmeas_mu µ U).
Proof. by []. Qed.

End FMeasEU.

(** Paper §3.2.1: the test family [M_Y(FMeas X)] for arity [Y]. *)
Definition fmeas_mcone_M (Y : ar_obj Ar) :
    set (test_of Ar Y (fmeas R X)) :=
  fun p =>
    exists (U : set X) (mU : measurable U),
      p = fmeas_eU Y mU.

(** Paper §3.2.1 (Mscomp). Tests [e_U] are constant in their first
    argument, so [test_reindex φ (e_U) = e_U']. *)
Lemma fmeas_mcone_M_comp
    (Y X' : ar_obj Ar) (φ : ar_hom Ar Y X')
    (p : test_of Ar X' (fmeas R X)) :
  fmeas_mcone_M p ->
  fmeas_mcone_M (test_reindex φ p).
Proof.
case=> U [mU ->].
exists U, mU; apply: test_eq => s µ /=.
by rewrite /test_reindex_fun.
Qed.

(** Paper §3.2.1 (Mssep): tests separate points (use [fmeas_eq]). *)
Lemma fmeas_mcone_M_sep (µ1 µ2 : fmeas R X) :
  (forall p : test_of Ar (ar_zero Ar) (fmeas R X),
    fmeas_mcone_M p ->
    test_fun p (ar_zero_pt Ar) µ1 = test_fun p (ar_zero_pt Ar) µ2) ->
  µ1 = µ2.
Proof.
move=> Hsep.
apply: fmeas_eq => U mU.
have Hin : fmeas_mcone_M (fmeas_eU (ar_zero Ar) mU)
  by exists U, mU.
have := Hsep _ Hin.
rewrite !fmeas_eUE => Hfine.
have H1 : fmeas_mu µ1 U \is a fin_num by exact: fmeas_fin.
have H2 : fmeas_mu µ2 U \is a fin_num by exact: fmeas_fin.
by rewrite -(fineK H1) -(fineK H2) Hfine.
Qed.

(** Paper §3.2.1 (Msnorm): for non-zero [µ] and ε > 0, the test
    [e_setT] gives [cnorm µ ≤ µ setT + ε]. In fact, equality holds
    (e_setT µ = cnorm µ). *)
Lemma fmeas_mcone_M_norm (µ : fmeas R X) (eps : R) :
  µ <> precone_zero -> (0 < eps)%R ->
  exists p : test_of Ar (ar_zero Ar) (fmeas R X),
    fmeas_mcone_M p /\
    (cone_norm µ <= test_fun p (ar_zero_pt Ar) µ + eps)%R.
Proof.
move=> _ eps_pos.
exists (fmeas_eU (ar_zero Ar) (@measurableT _ X)); split.
  by exists [set: X], (@measurableT _ X).
rewrite /cone_norm/= /fmeas_norm/= /eU_fun/=.
by rewrite ltW// ltrDl.
Qed.

(** ** Register the [isMCone] instance on [fmeas R X] — Paper §3.2.1 *)
HB.instance Definition _ :=
  @isMCone.Build R Ar (fmeas R X)
    fmeas_mcone_M
    fmeas_mcone_M_comp
    fmeas_mcone_M_sep
    fmeas_mcone_M_norm.

End FMeasMCone.

(** ** Paper Lemma 3.17: the pushforward functor [FMeas : Ar → MCones]

    Given [φ : ar_hom Ar X Y], the pushforward [µ ↦ pushforward µ φ]
    is a [cones_hom] from [fmeas R (ar_carrier Ar X)] to
    [fmeas R (ar_carrier Ar Y)]. *)

Section FMeasPushforward.
Variable R : realType.
Variable Ar : MeasSubcat R.
Variables X Y : ar_obj Ar.
Variable φ : ar_hom Ar X Y.

Local Open Scope ereal_scope.

(** The underlying function: [µ ↦ pushforward µ φ] as an [fmeas]. *)
Lemma fmeas_push_finP (µ : fmeas R (ar_carrier Ar X)) :
  fmeas_finP (pushforward (fmeas_mu µ) φ).
Proof.
move=> U mU; rewrite /pushforward.
apply: fmeas_fin.
rewrite -[X in measurable X]setTI.
exact: measurable_funP.
Qed.

(** The pushforward of a measure: as a non-canonical function, we pick
    the canonicalized version that vanishes on non-measurable sets. *)
Definition fmeas_push_meas_fun (µ : fmeas R (ar_carrier Ar X)) :
    set (ar_carrier Ar Y) -> \bar R :=
  fmeas_canonize (pushforward (fmeas_mu µ) φ).

Lemma fmeas_push_meas_fun_E (µ : fmeas R (ar_carrier Ar X)) A :
  measurable A ->
  fmeas_push_meas_fun µ A = pushforward (fmeas_mu µ) φ A.
Proof. exact: fmeas_canonizeE. Qed.

Lemma fmeas_push_meas_fun_off (µ : fmeas R (ar_carrier Ar X)) A :
  ~ measurable A -> fmeas_push_meas_fun µ A = 0.
Proof. exact: fmeas_canonize_off. Qed.

Lemma fmeas_push_set0 (µ : fmeas R (ar_carrier Ar X)) :
  fmeas_push_meas_fun µ set0 = 0.
Proof.
rewrite fmeas_push_meas_fun_E ?measurable0//.
rewrite /pushforward preimage_set0; exact: measure0.
Qed.

Lemma fmeas_push_ge0 (µ : fmeas R (ar_carrier Ar X)) A :
  0 <= fmeas_push_meas_fun µ A.
Proof.
rewrite /fmeas_push_meas_fun /fmeas_canonize.
case: asboolP => mA; last exact: lexx.
rewrite /pushforward; apply: measure_ge0.
Qed.

Lemma fmeas_push_sigma_additive (µ : fmeas R (ar_carrier Ar X)) :
  semi_sigma_additive (fmeas_push_meas_fun µ).
Proof.
have measf : measurable_fun setT φ by exact: measurable_funP.
exact: (@fmeas_canonize_meas_sigma_additive _ _ _
          (pushforward (fmeas_mu µ) φ)).
Qed.

Section FMeasPushMeas.
Variable µ : fmeas R (ar_carrier Ar X).

HB.instance Definition _ :=
  isMeasure.Build (ar_disp Ar Y) (ar_carrier Ar Y) R
    (fmeas_push_meas_fun µ)
    (fmeas_push_set0 µ) (fmeas_push_ge0 µ)
    (fmeas_push_sigma_additive (µ := µ)).

Definition fmeas_push_meas :
    {measure set (ar_carrier Ar Y) -> \bar R} :=
  [the {measure set (ar_carrier Ar Y) -> \bar R} of fmeas_push_meas_fun µ].

End FMeasPushMeas.

Lemma fmeas_push_finP_canon (µ : fmeas R (ar_carrier Ar X)) :
  fmeas_finP (fmeas_push_meas µ).
Proof.
move=> U mU; rewrite /fmeas_push_meas/= fmeas_push_meas_fun_E//.
exact: fmeas_push_finP.
Qed.

Lemma fmeas_push_canon (µ : fmeas R (ar_carrier Ar X)) :
  fmeas_canon (fmeas_push_meas µ).
Proof. exact: fmeas_push_meas_fun_off. Qed.

(** Paper Lemma 3.17: the pushforward as an [fmeas]. *)
Definition fmeas_push_fun (µ : fmeas R (ar_carrier Ar X)) :
    fmeas R (ar_carrier Ar Y) :=
  MkFmeas
    (fmeas_push_meas µ)
    (fmeas_push_finP_canon µ)
    (fmeas_push_canon µ).

(** Pointwise pushforward equation on measurable sets. *)
Lemma fmeas_push_funE (µ : fmeas R (ar_carrier Ar X)) U :
  measurable U ->
  fmeas_mu (fmeas_push_fun µ) U = fmeas_mu µ (φ @^-1` U).
Proof.
move=> mU; rewrite /=.
by rewrite (fmeas_push_meas_fun_E _ mU).
Qed.

(** Pushforward preserves [precone_zero]. *)
Lemma fmeas_push_linear0 : fmeas_push_fun precone_zero = precone_zero.
Proof.
apply: fmeas_eq => U mU.
by rewrite /precone_zero/= fmeas_push_funE//.
Qed.

(** Pushforward preserves addition. *)
Lemma fmeas_push_linearD (µ1 µ2 : fmeas R (ar_carrier Ar X)) :
  fmeas_push_fun (precone_add µ1 µ2) =
  precone_add (fmeas_push_fun µ1) (fmeas_push_fun µ2).
Proof.
apply: fmeas_eq => U mU.
rewrite /precone_add/= fmeas_push_funE// /pushforward.
rewrite /msum big_ord_recl big_ord_recl big_ord0 adde0/=.
rewrite /msum big_ord_recl big_ord_recl big_ord0 adde0/=.
by rewrite !fmeas_push_meas_fun_E.
Qed.

(** Pushforward preserves scaling. *)
Lemma fmeas_push_linearZ (r : {nonneg R}) (µ : fmeas R (ar_carrier Ar X)) :
  fmeas_push_fun (precone_scale r µ) =
  precone_scale r (fmeas_push_fun µ).
Proof.
apply: fmeas_eq => U mU.
rewrite /precone_scale/= fmeas_push_funE// /pushforward /mscale.
by rewrite /fmeas_push_meas/= /fmeas_push_meas_fun /fmeas_canonize asboolT.
Qed.

Lemma fmeas_push_is_linear : is_linear fmeas_push_fun.
Proof. split; [exact: fmeas_push_linear0|exact: fmeas_push_linearD
              |exact: fmeas_push_linearZ]. Qed.

(** Pushforward decreases norm (it preserves it, actually). *)
Lemma fmeas_push_norm_le µ :
  (cone_norm (fmeas_push_fun µ) <= cone_norm µ)%R.
Proof.
rewrite /cone_norm/= /fmeas_norm.
rewrite fmeas_push_funE; last exact: measurableT.
rewrite /pushforward.
have -> : φ @^-1` [set: ar_carrier Ar Y] = [set: ar_carrier Ar X].
  by apply/seteqP; split=> // x _.
exact: lexx.
Qed.

(** Pushforward is ω-continuous. *)
Lemma fmeas_push_omega_continuous : is_omega_continuous fmeas_push_fun.
Proof.
rewrite /is_omega_continuous => u uch ub1 fuch fub1.
apply: fmeas_eq => U mU.
have measf : measurable_fun setT φ.
  exact: measurable_funP.
have mφU : measurable (φ @^-1` U).
  rewrite -[X in measurable X]setTI.
  exact: measf.
(* both sides equal [µ_∞ (φ ⁻¹ U)] = lim_n µ_n (φ ⁻¹ U). *)
rewrite fmeas_push_funE//.
have cvg_pre := @fmeas_sup_cvg R _ _ u uch _ mφU.
have lim_pre :
  limn (fun n => fmeas_mu (u n) (φ @^-1` U)) =
  fmeas_sup_meas_fun uch (φ @^-1` U).
  exact: cvg_lim cvg_pre.
rewrite (fmeas_sup_ballE _ ub1 mφU) -lim_pre.
(* The RHS: cone_sup_ball (fmeas_push_fun \o u) ... U =
   fmeas_sup_meas_fun on the pushforward chain U *)
have cvg_post :
  fmeas_mu ((fmeas_push_fun \o u) n) U @[n --> \oo] -->
  fmeas_sup_meas_fun fuch U.
  apply: (@fmeas_sup_cvg R _ (ar_carrier Ar Y) (fmeas_push_fun \o u) fuch).
  exact: mU.
have lim_post :
  limn (fun n => fmeas_mu ((fmeas_push_fun \o u) n) U) =
  fmeas_sup_meas_fun fuch U.
  exact: cvg_lim cvg_post.
rewrite (fmeas_sup_ballE _ fub1 mU) -lim_post.
congr (limn _); apply: funext => n /=.
by rewrite fmeas_push_funE.
Qed.

(** Paper Lemma 3.17: the [cones_hom] packaging. *)
Definition fmeas_push :
  cones_hom (fmeas R (ar_carrier Ar X)) (fmeas R (ar_carrier Ar Y)) :=
  ConesHom fmeas_push_fun fmeas_push_is_linear fmeas_push_omega_continuous
           fmeas_push_norm_le.

(** Paper Lemma 3.17: pointwise [fmeas_push_funE] lifted to
    [cones_hom]. *)
Lemma fmeas_pushE (µ : fmeas R (ar_carrier Ar X)) U :
  measurable U ->
  fmeas_mu (cones_hom_fun fmeas_push µ) U = fmeas_mu µ (φ @^-1` U).
Proof. exact: fmeas_push_funE. Qed.

End FMeasPushforward.

(** ** Functoriality of [fmeas_push] — Paper Lemma 3.17 *)

Section FMeasPushFunctor.
Variable R : realType.
Variable Ar : MeasSubcat R.

(** [fmeas_push id = id]: stated at the level of underlying [fmeas]
    functions. *)
Lemma fmeas_push_id (X : ar_obj Ar) (φid : ar_hom Ar X X) :
  φid =1 idfun ->
  cones_hom_fun (fmeas_push φid) =1 @idfun (fmeas R (ar_carrier Ar X)).
Proof.
move=> Hφ µ; apply: fmeas_eq => U mU.
rewrite fmeas_pushE// /idfun.
have -> : φid @^-1` U = U.
  by apply/seteqP; split=> x /=; rewrite /preimage Hφ.
by [].
Qed.

(** [fmeas_push (g \o f) = fmeas_push g \o fmeas_push f]: stated at the
    level of underlying [fmeas] functions. *)
Lemma fmeas_push_comp (X Y Z : ar_obj Ar)
    (f : ar_hom Ar X Y) (g : ar_hom Ar Y Z) (gf : ar_hom Ar X Z) :
  gf =1 g \o f ->
  cones_hom_fun (fmeas_push gf) =1
  (cones_hom_fun (fmeas_push g)) \o (cones_hom_fun (fmeas_push f)).
Proof.
move=> Hgf µ; apply: fmeas_eq => U mU.
rewrite (fmeas_pushE gf µ mU).
have measg : measurable_fun setT g.
  exact: measurable_funP.
have mgU : measurable (g @^-1` U).
  rewrite -[X in measurable X]setTI; exact: measg.
rewrite /= (fmeas_pushE g (fmeas_push_fun f µ) mU).
rewrite /= (fmeas_pushE f µ mgU).
have -> : gf @^-1` U = f @^-1` (g @^-1` U).
  by apply/seteqP; split=> x /=; rewrite /preimage Hgf.
by [].
Qed.

End FMeasPushFunctor.
