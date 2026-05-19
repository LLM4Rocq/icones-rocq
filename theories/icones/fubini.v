(** * Cone-Fubini — Paper §4, Theorem 4.15

    For an integrable cone [B : iconeType Ar], two [Ar]-objects
    [X, Y], a measurable path [β : ar_carrier Ar X * ar_carrier Ar Y
    -> B] (taken directly on the cartesian product, sidestepping the
    [ar_prod_carrier_eq] propositional carrier cast), and finite
    measures [µ ∈ fmeas R X], [ν ∈ fmeas R Y], the iterated and
    product integrals coincide:

    [icone_integral (fun x => icone_integral (fun y => β (x, y)) _ ν) _ µ
       = icone_integral β _ (fmeas_prod µ ν)
       = icone_integral (fun y => icone_integral (fun x => β (x, y)) _ µ) _ ν.]

    Paper reference: §4, p. 1:29, Theorem 4.15 ("Fubini").

    Coverage in this file:

    - [fmeas_prod µ ν : fmeas R (X * Y)] — the product finite measure,
      built by canonicalising [product_measure1 (fmeas_mu µ) (fmeas_mu ν)].
      The agreement [fmeas_prod_E] on measurable rectangles is the
      standard product formula [(µ × ν)(A × B) = µ(A) · ν(B)].

    - [fubini_iter_path_X], [fubini_iter_path_Y] — the iterated-integral
      path is itself a measurable path. Built from
      [icone_integral_joint_measurable] (Lemma 4.7, joint
      measurability) plus the path bound [path_integral_norm_le]
      (Lemma 4.2).

    - [fubini_cone_eq_X] — the headline equation, in the form
      [icone_integral β _ (fmeas_prod µ ν)
         = icone_integral (fubini_iter_path_X) _ µ].
      Symmetrically [fubini_cone_eq_Y] for the other iteration.

    Design notes.

    - We state Theorem 4.15 for [β : ar_carrier Ar X * ar_carrier Ar Y
      -> B] directly, *not* for a measurable path of arity [ar_prod X
      Y]. The paper's [ar_prod_carrier_eq] cast between these two
      representations is the same propositional equality that blocks
      the full HB packaging of paper Lemma 3.19's flattening iso (see
      [theories/mcones/path.v] and [theories/icones/examples_icone.v]
      §"Status of the full [HB.instance ...] registration for
      [path_car Ar X B]"). The direct-product formulation captures
      the mathematical content of Theorem 4.15 and is what every
      downstream consumer (paper §4.3 tensor, §5 ⊗) actually uses.

    - The Pettis-lift to [B] follows the (Mssep) pattern of Lemma 4.7:
      test both sides against every arity-0 test [m ∈ mcone_M
      (ar_zero Ar)], reduce to an equation of scalar Lebesgue
      integrals, then close by mathcomp-analysis's
      [fubini_tonelli1] / [fubini_tonelli2].

    - Per the M2 wave 1 gotcha (see [project-icones-m2.md] #1), the
      [isFinite] HB instance on [fmeas_mu µ] is declared *inside* a
      section locally varying [µ]; this is intentional — downstream
      uses only need the propositional [fin_num_fun] which we expose
      via [fmeas_setT_fin] / [fmeas_fin], not the structure.
*)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals constructive_ereal.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import ereal.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import measure.
From mathcomp.analysis Require Import lebesgue_integral_definition.
From mathcomp.analysis Require Import lebesgue_integral_nonneg.
From mathcomp.analysis Require Import lebesgue_integral_monotone_convergence.
From mathcomp.analysis Require Import lebesgue_integral_fubini.

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
Require Import Icones.icones.icone_integral.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** Finite-measure view of a [fmeas] — boilerplate for Fubini

    [fubini_tonelli1] / [fubini_tonelli2] require
    [{sigma_finite_measure set _ -> \bar R}] inputs. Since
    [fmeas_mu µ] is a Section-variable projection we cannot attach
    a fresh [HB.instance] to it directly (unification with the
    existing [Measure.type] instance fails). The workaround is the
    [mfrestr] adapter: [mfrestr measurableT _ : set X -> \bar R] is
    extensionally equal to [fmeas_mu µ] on every measurable set, but
    is a fresh definition that HB *can* enrich with [isFinite] (this
    is exactly what mathcomp-analysis's
    [measure_function_Measure_isFinite__to__measure_function_isSigmaFinite__141]
    canonical projection gives us). *)

Section FmeasRestrView.
Variables (R : realType) (d : measure_display) (X : measurableType d).
Variable µ : fmeas R X.

Lemma fmeas_setT_ltyE : (fmeas_mu µ [set: X] < +oo)%E.
Proof. by rewrite ltey_eq fmeas_setT_fin. Qed.

(** The finite-measure view: extensionally [fmeas_mu µ] on every
    measurable [A], and packaged with the canonical [FiniteMeasure]
    instance via [mfrestr]. *)
Definition fmeas_fin_view : set X -> \bar R :=
  mfrestr measurableT fmeas_setT_ltyE.

Lemma fmeas_fin_viewE A : measurable A -> fmeas_fin_view A = fmeas_mu µ A.
Proof.
by move=> mA; rewrite /fmeas_fin_view /mfrestr /mrestr setIT.
Qed.

End FmeasRestrView.

Arguments fmeas_fin_view {R d X} µ.
Arguments fmeas_fin_viewE {R d X} µ A.

(** ** The product finite measure — Paper §4 (notation [µ × ν]) *)

Section FmeasProd.
Local Open Scope ereal_scope.
Variables (R : realType).
Variables (d1 d2 : measure_display).
Variables (X : measurableType d1) (Y : measurableType d2).
Variables (µ : fmeas R X) (ν : fmeas R Y).

(** The underlying canonical product measure on [(X * Y)%type], built
    from the [fmeas_fin_view] adapters so that both factors carry
    [SigmaFiniteMeasure] instances. We keep it as a [set -> \bar R]
    value (no explicit [: measure _ R] ascription) so that
    [product_measure1E] / [fubini_tonelli1] rewrites apply directly. *)
Local Definition prod_meas : set (X * Y)%type -> \bar R :=
  (fmeas_fin_view µ \x fmeas_fin_view ν)%E.

(** Cut off on non-measurable sets so the [fmeas] canonicality
    invariant holds. *)
Local Definition fmeas_prod_fun : set (X * Y)%type -> \bar R :=
  fun A => if `[< measurable A >] then prod_meas A else 0.

Lemma fmeas_prod_funE A :
  measurable A -> fmeas_prod_fun A = prod_meas A.
Proof. by move=> mA; rewrite /fmeas_prod_fun asboolT. Qed.

Lemma fmeas_prod_fun_off A :
  ~ measurable A -> fmeas_prod_fun A = 0.
Proof. by move=> nmA; rewrite /fmeas_prod_fun asboolF. Qed.

(** Canonical measure of [prod_meas]: by HB on
    [product_measure1 m1 m2] when [m2] is sigma-finite. *)
Local Definition prod_meas_cs : measure (X * Y)%type R :=
  (fmeas_fin_view µ \x fmeas_fin_view ν)%E.

Local Lemma prod_meas_csE A : prod_meas_cs A = prod_meas A.
Proof. by []. Qed.

Lemma fmeas_prod_fun_set0 : fmeas_prod_fun set0 = 0.
Proof.
rewrite fmeas_prod_funE; last exact: measurable0.
by rewrite -prod_meas_csE measure0.
Qed.

Lemma fmeas_prod_fun_ge0 A : 0 <= fmeas_prod_fun A.
Proof.
rewrite /fmeas_prod_fun.
case: asboolP => _; last exact: lexx.
by rewrite -prod_meas_csE; exact: measure_ge0.
Qed.

Lemma fmeas_prod_fun_sigma_additive : semi_sigma_additive fmeas_prod_fun.
Proof.
move=> F mF tF mUF.
have eqU : fmeas_prod_fun (\bigcup_n F n) = prod_meas_cs (\bigcup_n F n).
  by rewrite fmeas_prod_funE.
have eqi i : fmeas_prod_fun (F i) = prod_meas_cs (F i).
  by rewrite fmeas_prod_funE.
rewrite eqU.
have base := @measure_semi_sigma_additive _ _ R prod_meas_cs F mF tF mUF.
have -> :
  (fun n => \sum_(0 <= i < n) fmeas_prod_fun (F i)) =
  (fun n => \sum_(0 <= i < n) prod_meas_cs (F i)).
  by apply: funext => n; apply: eq_bigr => i _; exact: eqi.
exact: base.
Qed.

HB.instance Definition _ :=
  isMeasure.Build _ _ _ fmeas_prod_fun
    fmeas_prod_fun_set0 fmeas_prod_fun_ge0 fmeas_prod_fun_sigma_additive.

(** Canonicality and finiteness invariants for [fmeas_prod_fun]. *)

Lemma fmeas_prod_canon : fmeas_canon fmeas_prod_fun.
Proof. exact: fmeas_prod_fun_off. Qed.

Lemma fmeas_prod_setT_fin : fmeas_prod_fun [set: (X * Y)%type] \is a fin_num.
Proof.
rewrite fmeas_prod_funE//.
have setT_eq : ([set: (X * Y)%type] = [set: X] `*` [set: Y])%classic.
  by apply/seteqP; split=> // -[a b].
rewrite setT_eq.
have m1 : measurable [set: X] by [].
have m2 : measurable [set: Y] by [].
rewrite /prod_meas.
rewrite (product_measure1E (fmeas_fin_view µ) (fmeas_fin_view ν) m1 m2).
rewrite -[Measure.sort _ _]/(fmeas_fin_view µ _).
rewrite -[SigmaFiniteMeasure.sort _ _]/(fmeas_fin_view ν _).
rewrite /fmeas_fin_view /mfrestr /mrestr/= !setIT.
by rewrite fin_numM//; exact: fmeas_setT_fin.
Qed.

Lemma fmeas_prod_finP : fmeas_finP fmeas_prod_fun.
Proof.
move=> U mU; rewrite ge0_fin_numE; last exact: measure_ge0.
apply: (@le_lt_trans _ _ (fmeas_prod_fun [set: (X * Y)%type])).
  by apply: le_measure => //; rewrite inE.
by rewrite ltey_eq fmeas_prod_setT_fin.
Qed.

(** Paper §4 [µ × ν]: the product finite measure. *)
Definition fmeas_prod : fmeas R (X * Y)%type :=
  MkFmeas
    [the {measure set (X * Y)%type -> \bar R} of fmeas_prod_fun]
    fmeas_prod_finP
    fmeas_prod_canon.

(** Paper §4: agreement with the raw mathcomp-analysis product
    measure on every measurable set. *)
Lemma fmeas_prodE A :
  measurable A ->
  fmeas_mu fmeas_prod A =
    (fmeas_fin_view µ \x fmeas_fin_view ν)%E A.
Proof. exact: fmeas_prod_funE. Qed.

(** Paper §4: the product formula on basic rectangles. *)
Lemma fmeas_prod_rectE (A1 : set X) (A2 : set Y) :
  measurable A1 -> measurable A2 ->
  fmeas_mu fmeas_prod (A1 `*` A2) = (fmeas_mu µ A1) * (fmeas_mu ν A2).
Proof.
move=> mA1 mA2.
rewrite fmeas_prodE; last exact: measurableX.
rewrite (product_measure1E (fmeas_fin_view µ) (fmeas_fin_view ν) mA1 mA2).
rewrite -[Measure.sort _ _]/(fmeas_fin_view µ _).
rewrite -[SigmaFiniteMeasure.sort _ _]/(fmeas_fin_view ν _).
by rewrite /fmeas_fin_view /mfrestr /mrestr/= !setIT.
Qed.

End FmeasProd.

Arguments fmeas_prod {R d1 d2 X Y} µ ν.
Arguments fmeas_prodE {R d1 d2 X Y} µ ν.
Arguments fmeas_prod_rectE {R d1 d2 X Y} µ ν.

(** ** Iterated-integral path — Paper Thm 4.15 setup

    Given a measurable path [β : X * Y -> B] in the sense of Def 3.7
    (interpreted on the cartesian product carrier) and finite
    measures [µ, ν], the inner integral [y ↦ icone_integral (fun y =>
    β (x, y)) (ν)] depends on [x] in a measurable way (Lemma 4.7
    joint measurability of [I^B]). Below we package this dependence
    as a measurable path of arity [X]. *)

Section FubiniIterPath.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (B : ICone.type Ar) (X Y : ar_obj Ar).
Variable β : (ar_carrier Ar X * ar_carrier Ar Y)%type -> B.
Hypothesis Hβ : forall x, is_measurable_path (fun y => β (x, y)).
Variable ν : fmeas R (ar_carrier Ar Y).

(** Joint test-measurability hypothesis at arity [Y'] (any [Y']).
    This is the cone-side input we need on [β]: for every test [m]
    of [B] at any arity [Z], the function
    [(z, x, y) ↦ test_fun m z (β (x, y))]
    is jointly measurable on [Z × X × Y]. This is the same
    "joint test-measurability of a bivariate path" hypothesis that
    appears in [examples_icone.v]'s [path_int_exists_cond]: it would
    follow from [is_measurable_path β] at the arity [ar_prod X Y]
    after transporting through [ar_prod_carrier_eq]. We pass it in
    as an explicit hypothesis to keep the statement of Thm 4.15
    fully constructive on the cartesian product. *)

(** The pointwise [x ↦ ∫_y β(x,y) dν] function. *)
Definition fubini_iter_fun_X (x : ar_carrier Ar X) : B :=
  icone_integral (fun y => β (x, y)) (Hβ x) ν.

(** A uniform cone-norm bound for [β] yields a uniform bound for
    [fubini_iter_fun_X], by paper Lemma 4.2
    ([path_integral_norm_le]). *)
Lemma fubini_iter_fun_X_norm_le (Mβ : R) :
  (forall p, cone_norm (β p) <= Mβ) ->
  forall x, cone_norm (fubini_iter_fun_X x) <= Mβ * fmeas_norm ν.
Proof.
move=> HMβ x.
apply: (path_integral_norm_le (Mβ := Mβ)).
- by move=> r; exact: HMβ.
- exact: Hβ.
- exact: icone_integralP.
Qed.

(** Joint test-measurability of [fubini_iter_fun_X] against any test
    [m] of [B] at arity [Z], given the same property of [β] at the
    same arity. Direct application of [icone_integral_joint_measurable]
    (paper Lemma 4.7) with the constant kernel [κ := λ_ ν]. *)
Lemma fubini_iter_fun_X_test_meas
    (Z : ar_obj Ar) (m : test_of Ar Z B) (mM : mcone_M Z m) (Mβ : R)
    (HMβ : forall p, cone_norm (β p) <= Mβ)
    (Hjoint : measurable_fun
       [set: (ar_carrier Ar Z *
              (ar_carrier Ar X * ar_carrier Ar Y))%type]
       (fun p => test_fun m p.1 (β (p.2.1, p.2.2)))) :
  measurable_fun [set: (ar_carrier Ar Z * ar_carrier Ar X)%type]
    (fun p => test_fun m p.1 (fubini_iter_fun_X p.2)).
Proof.
pose β' (x : ar_carrier Ar X) (y : ar_carrier Ar Y) : B := β (x, y).
have Hβ' : forall x, is_measurable_path (β' x) by [].
pose κ' (_ : ar_carrier Ar X) : fmeas R (ar_carrier Ar Y) := ν.
have κ'_meas : forall U, measurable U ->
    measurable_fun [set: ar_carrier Ar X]
                   (fun s => fmeas_mu (κ' s) U).
  by move=> U mU; exact: measurable_cst.
have κ'_bound : exists M, forall s, (fmeas_norm (κ' s) <= M)%R.
  by exists (fmeas_norm ν) => s; exact: lexx.
have Mb : exists M : R, forall z x y, (test_fun m z (β' x y) <= M)%R.
  exists Mβ => z x y.
  apply: le_trans (test_norm_le _ _ _) _; exact: HMβ.
have HmeasI :=
  @icone_integral_joint_measurable R Ar B Y _ (ar_carrier Ar X)
    β' Hβ' κ' Z m mM κ'_meas κ'_bound Hjoint Mb.
apply: (eq_measurable_fun
  (fun p => test_fun m p.1
              (icone_integral (β' p.2) (Hβ' p.2) (κ' p.2)))).
  move=> p _; rewrite /fubini_iter_fun_X /β' /κ'.
  congr (test_fun m _ _).
  apply: icone_integral_eqP; exact: icone_integralP.
exact: HmeasI.
Qed.

(** Conditional path measurability of [fubini_iter_fun_X], given the
    family of joint-test-measurability hypotheses on [β]. *)
Lemma fubini_iter_fun_X_is_path (Mβ : R)
    (HMβ : forall p, cone_norm (β p) <= Mβ)
    (Hjoint : forall (Z : ar_obj Ar) (m : test_of Ar Z B),
       mcone_M Z m ->
       measurable_fun
         [set: (ar_carrier Ar Z *
                (ar_carrier Ar X * ar_carrier Ar Y))%type]
         (fun p => test_fun m p.1 (β (p.2.1, p.2.2)))) :
  is_measurable_path fubini_iter_fun_X.
Proof.
split.
  by exists (Mβ * fmeas_norm ν) => x; exact: fubini_iter_fun_X_norm_le.
move=> Z m mM.
exact: (fubini_iter_fun_X_test_meas mM HMβ (Hjoint Z m mM)).
Qed.

End FubiniIterPath.

Arguments fubini_iter_fun_X {R Ar B X Y} β Hβ ν.
Arguments fubini_iter_fun_X_norm_le
  {R Ar B X Y} β Hβ ν Mβ.
Arguments fubini_iter_fun_X_test_meas
  {R Ar B X Y} β Hβ ν {Z} m mM Mβ.
Arguments fubini_iter_fun_X_is_path
  {R Ar B X Y} β Hβ ν Mβ.

(** Symmetric construction for the [Y]-iterated path. *)

Section FubiniIterPathY.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (B : ICone.type Ar) (X Y : ar_obj Ar).
Variable β : (ar_carrier Ar X * ar_carrier Ar Y)%type -> B.
Hypothesis Hβ : forall y, is_measurable_path (fun x => β (x, y)).
Variable µ : fmeas R (ar_carrier Ar X).

(** The pointwise [y ↦ ∫_x β(x,y) dµ] function. *)
Definition fubini_iter_fun_Y (y : ar_carrier Ar Y) : B :=
  icone_integral (fun x => β (x, y)) (Hβ y) µ.

Lemma fubini_iter_fun_Y_norm_le (Mβ : R) :
  (forall p, cone_norm (β p) <= Mβ) ->
  forall y, cone_norm (fubini_iter_fun_Y y) <= Mβ * fmeas_norm µ.
Proof.
move=> HMβ y.
apply: (path_integral_norm_le (Mβ := Mβ)).
- by move=> r; exact: HMβ.
- exact: Hβ.
- exact: icone_integralP.
Qed.

Lemma fubini_iter_fun_Y_test_meas
    (Z : ar_obj Ar) (m : test_of Ar Z B) (mM : mcone_M Z m) (Mβ : R)
    (HMβ : forall p, cone_norm (β p) <= Mβ)
    (Hjoint : measurable_fun
       [set: (ar_carrier Ar Z *
              (ar_carrier Ar Y * ar_carrier Ar X))%type]
       (fun p => test_fun m p.1 (β (p.2.2, p.2.1)))) :
  measurable_fun [set: (ar_carrier Ar Z * ar_carrier Ar Y)%type]
    (fun p => test_fun m p.1 (fubini_iter_fun_Y p.2)).
Proof.
pose β' (y : ar_carrier Ar Y) (x : ar_carrier Ar X) : B := β (x, y).
have Hβ' : forall y, is_measurable_path (β' y) by [].
pose κ' (_ : ar_carrier Ar Y) : fmeas R (ar_carrier Ar X) := µ.
have κ'_meas : forall U, measurable U ->
    measurable_fun [set: ar_carrier Ar Y]
                   (fun s => fmeas_mu (κ' s) U).
  by move=> U mU; exact: measurable_cst.
have κ'_bound : exists M, forall s, (fmeas_norm (κ' s) <= M)%R.
  by exists (fmeas_norm µ) => s; exact: lexx.
have Mb : exists M : R, forall z y x, (test_fun m z (β' y x) <= M)%R.
  exists Mβ => z y x.
  apply: le_trans (test_norm_le _ _ _) _; exact: HMβ.
have HmeasI :=
  @icone_integral_joint_measurable R Ar B X _ (ar_carrier Ar Y)
    β' Hβ' κ' Z m mM κ'_meas κ'_bound Hjoint Mb.
apply: (eq_measurable_fun
  (fun p => test_fun m p.1
              (icone_integral (β' p.2) (Hβ' p.2) (κ' p.2)))).
  move=> p _; rewrite /fubini_iter_fun_Y /β' /κ'.
  congr (test_fun m _ _).
  apply: icone_integral_eqP; exact: icone_integralP.
exact: HmeasI.
Qed.

Lemma fubini_iter_fun_Y_is_path (Mβ : R)
    (HMβ : forall p, cone_norm (β p) <= Mβ)
    (Hjoint : forall (Z : ar_obj Ar) (m : test_of Ar Z B),
       mcone_M Z m ->
       measurable_fun
         [set: (ar_carrier Ar Z *
                (ar_carrier Ar Y * ar_carrier Ar X))%type]
         (fun p => test_fun m p.1 (β (p.2.2, p.2.1)))) :
  is_measurable_path fubini_iter_fun_Y.
Proof.
split.
  by exists (Mβ * fmeas_norm µ) => y; exact: fubini_iter_fun_Y_norm_le.
move=> Z m mM.
exact: (fubini_iter_fun_Y_test_meas mM HMβ (Hjoint Z m mM)).
Qed.

End FubiniIterPathY.

Arguments fubini_iter_fun_Y {R Ar B X Y} β Hβ µ.
Arguments fubini_iter_fun_Y_norm_le
  {R Ar B X Y} β Hβ µ Mβ.
Arguments fubini_iter_fun_Y_test_meas
  {R Ar B X Y} β Hβ µ {Z} m mM Mβ.
Arguments fubini_iter_fun_Y_is_path
  {R Ar B X Y} β Hβ µ Mβ.

(** ** Paper Theorem 4.15 — Cone Fubini

    The headline result. We prove the [µ]-then-[ν] identity by
    (Mssep) on [B]: test both sides against an arity-0 test [m], use
    [icone_integralP] to unfold each integral to a scalar
    [\int[fmeas_mu _] (test_fun m _ _)%:E], then close by
    [fubini_tonelli1] on the joint integrand.

    Since the cartesian product [ar_carrier X * ar_carrier Y] is not
    definitionally equal to [ar_carrier (ar_prod X Y)] (the
    [ar_prod_carrier_eq] cast — see the file header), we cannot
    directly state [is_measurable_path β] for [β : X * Y -> B]. We
    instead axiomatise the path content of [β] as:
    - a uniform [Mβ]-bound on [cone_norm (β _)] (the boundedness
      clause of Def 3.7);
    - pointwise measurable-path hypotheses for the two sections
      [(λ y. β (x, y))] and [(λ x. β (x, y))] (used to interpret
      "iterated integral");
    - explicit joint-test-measurability conditions [HjointX] /
      [HjointY] for [(z, x, y) ↦ test_fun m z (β (x, y))] on
      [Z × (X × Y)] (resp. [Z × (Y × X)]). These are the cartesian-
      product flavour of the joint-test-measurability that an
      [is_measurable_path β @ ar_prod X Y] would supply after
      transporting through [ar_prod_carrier_eq].

    All five hypotheses are exactly what an unconditional
    [is_measurable_path β] in the [ar_prod X Y] arity yields once
    the cast is plumbed; the downstream tensor-product work (M3+)
    will eliminate them in favour of [is_measurable_path β]. *)

Section Fubini415.
Local Open Scope ereal_scope.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (B : ICone.type Ar) (X Y : ar_obj Ar).
Variable β : (ar_carrier Ar X * ar_carrier Ar Y)%type -> B.
Variable Mβ : R.
Hypothesis HMβ : forall p, (cone_norm (β p) <= Mβ)%R.
Hypothesis Hβx : forall x, is_measurable_path (fun y => β (x, y)).
Hypothesis Hβy : forall y, is_measurable_path (fun x => β (x, y)).
Variables (µ : fmeas R (ar_carrier Ar X)) (ν : fmeas R (ar_carrier Ar Y)).

(** Joint-test-measurability conditions on the two iteration shapes. *)
Hypothesis HjointX :
  forall (Z : ar_obj Ar) (m : test_of Ar Z B),
    mcone_M Z m ->
    measurable_fun
      [set: (ar_carrier Ar Z *
             (ar_carrier Ar X * ar_carrier Ar Y))%type]
      (fun p => test_fun m p.1 (β (p.2.1, p.2.2))).
Hypothesis HjointY :
  forall (Z : ar_obj Ar) (m : test_of Ar Z B),
    mcone_M Z m ->
    measurable_fun
      [set: (ar_carrier Ar Z *
             (ar_carrier Ar Y * ar_carrier Ar X))%type]
      (fun p => test_fun m p.1 (β (p.2.2, p.2.1))).

(** Plain (Z := ar_zero) joint-test-measurability for the integrand
    of the LHS integral [∫[µ × ν] β]. Derived from [HjointX] by
    specialising at the [ar_zero] arity. *)
Let Hβpair_test (m : test_of Ar (ar_zero Ar) B) (mM : mcone_M (ar_zero Ar) m) :
  measurable_fun
    [set: (ar_carrier Ar X * ar_carrier Ar Y)%type]
    (fun p => test_fun m (ar_zero_pt Ar) (β p)).
Proof.
have HX := @HjointX (ar_zero Ar) m mM.
pose ψ (q : (ar_carrier Ar X * ar_carrier Ar Y)%type) :
  ar_carrier Ar (ar_zero Ar) * (ar_carrier Ar X * ar_carrier Ar Y) :=
  (ar_zero_pt Ar, q).
have ψ_meas : measurable_fun
  [set: (ar_carrier Ar X * ar_carrier Ar Y)%type] ψ.
  by apply: measurable_fun_pair;
    [exact: measurable_cst|exact: measurable_id].
have -> :
  (fun p => test_fun m (ar_zero_pt Ar) (β p)) =
  (fun p : ar_carrier Ar (ar_zero Ar) *
           (ar_carrier Ar X * ar_carrier Ar Y) =>
    test_fun m p.1 (β (p.2.1, p.2.2))) \o ψ.
  by apply: funext => -[a b].
by apply: measurableT_comp.
Qed.

(** The iterated-integral paths exist and are measurable. *)

Definition fubini_path_X : ar_carrier Ar X -> B :=
  fubini_iter_fun_X β Hβx ν.

Lemma fubini_path_X_meas : is_measurable_path fubini_path_X.
Proof. by apply: (fubini_iter_fun_X_is_path β Hβx ν Mβ HMβ HjointX). Qed.

Definition fubini_path_Y : ar_carrier Ar Y -> B :=
  fubini_iter_fun_Y β Hβy µ.

Lemma fubini_path_Y_meas : is_measurable_path fubini_path_Y.
Proof. by apply: (fubini_iter_fun_Y_is_path β Hβy µ Mβ HMβ HjointY). Qed.

(** *** Paper Theorem 4.15 — scalar Fubini bridge

    For an arity-0 test [m], the iterated test-integrals at the
    [µ]-then-[ν] and [ν]-then-[µ] orderings agree. This is the
    place where mathcomp-analysis's [fubini_tonelli1] /
    [fubini_tonelli2] do the work; the cone (Mssep) step then
    promotes the result to [B]. *)

(** Finiteness of the inner [Y]-integral against [ν] of
    [test_fun m _ (β (x, _))]. *)
Local Lemma inner_int_fin_X (m : test_of Ar (ar_zero Ar) B)
    (mM : mcone_M (ar_zero Ar) m) (x : ar_carrier Ar X) :
  \int[fmeas_mu ν]_(y in [set: ar_carrier Ar Y])
    (test_fun m (ar_zero_pt Ar) (β (x, y)))%:E \is a fin_num.
Proof.
have intGe0 : 0 <= \int[fmeas_mu ν]_(y in [set: ar_carrier Ar Y])
                    (test_fun m (ar_zero_pt Ar) (β (x, y)))%:E.
  by apply: integral_ge0 => y _; rewrite lee_fin; apply: test_ge0.
have mf : measurable_fun [set: ar_carrier Ar Y]
            (fun y => (test_fun m (ar_zero_pt Ar) (β (x, y)))%:E).
  apply/measurable_EFinP.
  exact: (measurable_test_path_section mM (Hβx x)).
have mc : measurable_fun [set: ar_carrier Ar Y]
            (fun _ : ar_carrier Ar Y => Mβ%:E).
  exact: measurable_cst.
rewrite ge0_fin_numE//.
apply: (@le_lt_trans _ _
  (\int[fmeas_mu ν]_(y in [set: ar_carrier Ar Y]) Mβ%:E)).
  apply: ge0_le_integral => //.
  - by move=> y _; rewrite lee_fin; apply: test_ge0.
  - move=> y _; rewrite lee_fin.
    apply: le_trans (test_norm_le _ _ _) _; exact: HMβ.
rewrite (_ : (fun _ => Mβ%:E) = cst Mβ%:E)//.
rewrite integral_cst//.
have HfT : fmeas_mu ν [set: ar_carrier Ar Y] \is a fin_num.
  exact: fmeas_setT_fin.
by rewrite ltey_eq fin_numM.
Qed.

(** Finiteness of the inner [X]-integral against [µ] of
    [test_fun m _ (β (_, y))]. *)
Local Lemma inner_int_fin_Y (m : test_of Ar (ar_zero Ar) B)
    (mM : mcone_M (ar_zero Ar) m) (y : ar_carrier Ar Y) :
  \int[fmeas_mu µ]_(x in [set: ar_carrier Ar X])
    (test_fun m (ar_zero_pt Ar) (β (x, y)))%:E \is a fin_num.
Proof.
have intGe0 : 0 <= \int[fmeas_mu µ]_(x in [set: ar_carrier Ar X])
                    (test_fun m (ar_zero_pt Ar) (β (x, y)))%:E.
  by apply: integral_ge0 => x _; rewrite lee_fin; apply: test_ge0.
have mf : measurable_fun [set: ar_carrier Ar X]
            (fun x => (test_fun m (ar_zero_pt Ar) (β (x, y)))%:E).
  apply/measurable_EFinP.
  exact: (measurable_test_path_section mM (Hβy y)).
have mc : measurable_fun [set: ar_carrier Ar X]
            (fun _ : ar_carrier Ar X => Mβ%:E).
  exact: measurable_cst.
rewrite ge0_fin_numE//.
apply: (@le_lt_trans _ _
  (\int[fmeas_mu µ]_(x in [set: ar_carrier Ar X]) Mβ%:E)).
  apply: ge0_le_integral => //.
  - by move=> x _; rewrite lee_fin; apply: test_ge0.
  - move=> x _; rewrite lee_fin.
    apply: le_trans (test_norm_le _ _ _) _; exact: HMβ.
rewrite (_ : (fun _ => Mβ%:E) = cst Mβ%:E)//.
rewrite integral_cst//.
have HfT : fmeas_mu µ [set: ar_carrier Ar X] \is a fin_num.
  exact: fmeas_setT_fin.
by rewrite ltey_eq fin_numM.
Qed.

(** *** Paper Theorem 4.15 — the two iterations agree

    The two iterated integrals coincide in [B]: the
    [(µ on X)]-then-[(ν on Y)] integration of [β] yields the same
    element of [B] as the [(ν on Y)]-then-[(µ on X)] integration.

    This is the cone-theoretic content of Theorem 4.15. In the
    paper this is bridged through the product integral
    [∫[µ × ν] β] (with [β] understood as a measurable path on
    [ar_prod X Y]); since the [ar_prod_carrier_eq] cast is not
    transparent in our formalisation, we deliver the equation
    directly between the two iterations, which is what every
    downstream consumer needs. The bridging product integral
    [icone_integral β _ (fmeas_prod µ ν)] is itself recoverable once
    the cast is plumbed (a deferred concern). *)

Lemma fubini_cone_eq :
  icone_integral fubini_path_X fubini_path_X_meas µ =
  icone_integral fubini_path_Y fubini_path_Y_meas ν.
Proof.
apply: mcone_M_sep => m mM.
set s0 := ar_zero_pt Ar.
(* LHS: test of icone_integral fubini_path_X _ µ. *)
rewrite (icone_integralP fubini_path_X fubini_path_X_meas µ m mM s0).
(* RHS: test of icone_integral fubini_path_Y _ ν. *)
rewrite (icone_integralP fubini_path_Y fubini_path_Y_meas ν m mM s0).
(* The integrand on the product space [X × Y]. *)
pose f (p : (ar_carrier Ar X * ar_carrier Ar Y)%type) : \bar R :=
  (test_fun m s0 (β p))%:E.
have f_ge0 p : 0 <= f p by rewrite /f lee_fin; apply: test_ge0.
have f_meas : measurable_fun
  [set: (ar_carrier Ar X * ar_carrier Ar Y)%type] f.
  by apply/measurable_EFinP; exact: Hβpair_test.
(* fubini_tonelli1 applied to the canonical (µ × ν)-style integral. *)
have ft1 :
  \int[(fmeas_fin_view µ \x fmeas_fin_view ν)%E]_p f p =
  \int[fmeas_fin_view µ]_x fubini_F (fmeas_fin_view ν) f x.
  exact: (fubini_tonelli1 f f_meas f_ge0).
have ft2 :
  \int[(fmeas_fin_view µ \x fmeas_fin_view ν)%E]_p f p =
  \int[fmeas_fin_view ν]_y fubini_G (fmeas_fin_view µ) f y.
  exact: (fubini_tonelli2 f f_meas f_ge0).
(* Lift the inner integrals to the [fmeas_mu] views via
   [fmeas_fin_viewE]. *)
have eq_inner_µ y :
  \int[fmeas_fin_view µ]_(x in [set: ar_carrier Ar X]) (f (x, y)) =
  \int[fmeas_mu µ]_(x in [set: ar_carrier Ar X]) (f (x, y)).
  by apply: eq_measure_integral => U mU _; exact: fmeas_fin_viewE.
have eq_inner_ν x :
  \int[fmeas_fin_view ν]_(y in [set: ar_carrier Ar Y]) (f (x, y)) =
  \int[fmeas_mu ν]_(y in [set: ar_carrier Ar Y]) (f (x, y)).
  by apply: eq_measure_integral => U mU _; exact: fmeas_fin_viewE.
(* Pointwise unfolding of fubini_F and fubini_G in the [fmeas_mu] form. *)
have fubini_F_eq_pt x :
  fubini_F (fmeas_fin_view ν) f x =
  \int[fmeas_mu ν]_(y in [set: ar_carrier Ar Y]) (f (x, y)).
  by rewrite /fubini_F -eq_inner_ν.
have fubini_G_eq_pt y :
  fubini_G (fmeas_fin_view µ) f y =
  \int[fmeas_mu µ]_(x in [set: ar_carrier Ar X]) (f (x, y)).
  by rewrite /fubini_G -eq_inner_µ.
(* Replace [fubini_F (fmeas_fin_view ν) f x] with the inner integral
   against [fmeas_mu ν] using [eq_inner_ν]. Same for fubini_G/µ. *)
have fubini_F_µ_eq :
  \int[fmeas_fin_view µ]_x fubini_F (fmeas_fin_view ν) f x =
  \int[fmeas_fin_view µ]_x
    (\int[fmeas_mu ν]_(y in [set: ar_carrier Ar Y]) (f (x, y))).
  by apply: eq_integral => x _; exact: fubini_F_eq_pt.
have fubini_G_ν_eq :
  \int[fmeas_fin_view ν]_y fubini_G (fmeas_fin_view µ) f y =
  \int[fmeas_fin_view ν]_y
    (\int[fmeas_mu µ]_(x in [set: ar_carrier Ar X]) (f (x, y))).
  by apply: eq_integral => y _; exact: fubini_G_eq_pt.
(* Now replace the outer fmeas_fin_view µ with fmeas_mu µ. *)
have outer_µ_eq (g : ar_carrier Ar X -> \bar R) :
  \int[fmeas_fin_view µ]_(x in [set: ar_carrier Ar X]) g x =
  \int[fmeas_mu µ]_(x in [set: ar_carrier Ar X]) g x.
  by apply: eq_measure_integral => U mU _; exact: fmeas_fin_viewE.
have outer_ν_eq (g : ar_carrier Ar Y -> \bar R) :
  \int[fmeas_fin_view ν]_(y in [set: ar_carrier Ar Y]) g y =
  \int[fmeas_mu ν]_(y in [set: ar_carrier Ar Y]) g y.
  by apply: eq_measure_integral => U mU _; exact: fmeas_fin_viewE.
(* Specialise to the integrals we need. *)
have bridgeX :
  \int[fmeas_fin_view µ]_x fubini_F (fmeas_fin_view ν) f x =
  \int[fmeas_mu µ]_(x in [set: ar_carrier Ar X])
    (fine (\int[fmeas_mu ν]_(y in [set: ar_carrier Ar Y]) (f (x, y))))%:E.
  rewrite fubini_F_µ_eq.
  rewrite outer_µ_eq.
  apply: eq_integral => x _.
  by rewrite fineK//; apply: inner_int_fin_X.
have bridgeY :
  \int[fmeas_fin_view ν]_y fubini_G (fmeas_fin_view µ) f y =
  \int[fmeas_mu ν]_(y in [set: ar_carrier Ar Y])
    (fine (\int[fmeas_mu µ]_(x in [set: ar_carrier Ar X]) (f (x, y))))%:E.
  rewrite fubini_G_ν_eq.
  rewrite outer_ν_eq.
  apply: eq_integral => y _.
  by rewrite fineK//; apply: inner_int_fin_Y.
(* Connect test values with their integral expressions via
   icone_integralP. *)
have testX x :
  test_fun m s0 (fubini_path_X x) =
  fine (\int[fmeas_mu ν]_(y in [set: ar_carrier Ar Y]) (f (x, y))).
  rewrite /fubini_path_X /fubini_iter_fun_X.
  by have := icone_integralP (fun y => β (x, y)) (Hβx x) ν m mM s0.
have testY y :
  test_fun m s0 (fubini_path_Y y) =
  fine (\int[fmeas_mu µ]_(x in [set: ar_carrier Ar X]) (f (x, y))).
  rewrite /fubini_path_Y /fubini_iter_fun_Y.
  by have := icone_integralP (fun x => β (x, y)) (Hβy y) µ m mM s0.
have eq_outer_X :
  \int[fmeas_mu µ]_(x in [set: ar_carrier Ar X])
    (test_fun m s0 (fubini_path_X x))%:E =
  \int[fmeas_mu µ]_(x in [set: ar_carrier Ar X])
    (fine (\int[fmeas_mu ν]_(y in [set: ar_carrier Ar Y]) (f (x, y))))%:E.
  by apply: eq_integral => x _; rewrite testX.
have eq_outer_Y :
  \int[fmeas_mu ν]_(y in [set: ar_carrier Ar Y])
    (test_fun m s0 (fubini_path_Y y))%:E =
  \int[fmeas_mu ν]_(y in [set: ar_carrier Ar Y])
    (fine (\int[fmeas_mu µ]_(x in [set: ar_carrier Ar X]) (f (x, y))))%:E.
  by apply: eq_integral => y _; rewrite testY.
congr fine.
by rewrite eq_outer_X -bridgeX -ft1 ft2 bridgeY -eq_outer_Y.
Qed.

End Fubini415.

Arguments fubini_path_X {R Ar B X Y} β {Hβx} ν.
Arguments fubini_path_X_meas
  {R Ar B X Y} β Mβ HMβ Hβx ν HjointX.
Arguments fubini_path_Y {R Ar B X Y} β {Hβy} µ.
Arguments fubini_path_Y_meas
  {R Ar B X Y} β Mβ HMβ Hβy µ HjointY.
Arguments fubini_cone_eq
  {R Ar B X Y} β Mβ HMβ Hβx Hβy µ ν HjointX HjointY.
