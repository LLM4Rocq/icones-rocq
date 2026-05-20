(** * The Ar parameter — Paper §3, setup

    A [MeasSubcat R] encodes "a small full subcategory of [Meas]
    closed under cartesian products and containing the one-point
    measurable space, with every object non-empty" (paper §3, p. 1:17).

    The record packages, for an unspecified index type [ar_obj]:

    - a measurable-space carrier [ar_carrier X : measurableType _]
      for each [X : ar_obj];
    - a distinguished inhabitant [ar_point X] of every carrier
      (non-emptiness);
    - a distinguished object [ar_zero] whose carrier is a singleton
      (the terminal object [0] of [Ar]);
    - a binary product [ar_prod X Y] whose carrier is *definitionally*
      [(ar_carrier X * ar_carrier Y)%type] with the standard product
      [measurableType] structure from mathcomp-analysis.

    Morphisms in [Ar] are mathcomp-analysis's measurable-function
    bundle [{mfun aT >-> rT}].

    Paper reference: §3 (page 1:17), the [Ar] paragraph and
    Remark 3.1.

    Design notes.

    - We keep [ar_obj] polymorphic (a [Type], no [eqType] / [choiceType]
      structure assumed). This matches the paper's "small full
      subcategory" framing — the index type is just a name set.
      Downstream files (M2 wave 2's tests-family construction) can
      always re-bundle a specific [ar_obj] with the structure they
      need.

    - The non-emptiness assumption ([ar_point]) gives us a *canonical*
      inhabitant of every [ar_carrier X], not just an existence
      witness; this avoids [cid] when we need a base point (paper
      §3, "We also assume all the objects of Ar to be non-empty
      measurable spaces").

    - For the terminal [0], we use [ar_zero_singleton] rather than
      proving it equivalent to [unit]: the singleton condition is
      what every downstream use of the terminal property needs (it
      is the "essentially one point" condition).

    - The product is encoded by *carrier equality* rather than via an
      external isomorphism witness. This is the cleaner approach
      and uses mathcomp-analysis's existing product
      [measurableType] instance (see [product_salgebra_instance] in
      [measure_theory/measurable_structure.v]).
*)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import measurable_structure measurable_function.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

(** ** Definition — Paper §3, [Ar] paragraph

    A [MeasSubcat R] is a faithful Rocq encoding of the paper's
    [Ar] parameter. [R : realType] is carried along even though
    [Ar] does not depend on it, in order to keep the parameter
    threading uniform with the downstream files that *do* use [R]
    (cones, norms, tests). *)
Record MeasSubcat (R : realType) : Type := MkMeasSubcat {
  (* The set of objects of [Ar]. *)
  ar_obj : Type;

  (* Each object's underlying measurable space. We name the display
     explicitly so that [measurableType] elaboration is unambiguous. *)
  ar_disp : ar_obj -> measure_display;
  ar_carrier : forall X : ar_obj, measurableType (ar_disp X);

  (* Paper §3: all objects of [Ar] are non-empty. We package this as
     a canonical inhabitant. *)
  ar_point : forall X : ar_obj, ar_carrier X;

  (* Paper §3: [Ar] contains the terminal object, called [0] in the
     paper (the one-point measurable space). *)
  ar_zero : ar_obj;
  ar_zero_singleton :
    forall x y : ar_carrier ar_zero, x = y;

  (* Paper §3: [Ar] is closed under cartesian products. The product's
     carrier is *definitionally* the [measurableType] product. *)
  ar_prod : ar_obj -> ar_obj -> ar_obj;
  ar_prod_disp_eq :
    forall X Y, ar_disp (ar_prod X Y) =
                measure_prod_display (ar_disp X, ar_disp Y);
  ar_prod_carrier_eq :
    forall X Y, ar_carrier (ar_prod X Y) =
                (ar_carrier X * ar_carrier Y)%type :> Type;

  (* Paper §3: the projection [ar_prod_uncast] is measurable. This is
     a separate field because the propositional [ar_prod_carrier_eq]
     equality does not imply σ-algebra agreement between
     [ar_carrier (ar_prod X Y)] and [ar_carrier X * ar_carrier Y]. *)
  ar_prod_uncast_meas :
    forall X Y,
      measurable_fun setT
        (fun p : ar_carrier (ar_prod X Y) =>
           eq_rect _ (fun T : Type => T) p _ (ar_prod_carrier_eq X Y));

  (* Paper §3: the cast injection in the reverse direction is also
     measurable. *)
  ar_prod_cast_meas :
    forall X Y,
      measurable_fun setT
        (fun p : (ar_carrier X * ar_carrier Y)%type =>
           eq_rect_r (fun T : Type => T) p (ar_prod_carrier_eq X Y));
}.

(** Disable [Set Implicit Arguments]'s automatic implicit-isation of
    [X] in projections like [ar_carrier]: the variable [X] is not
    inferrable from the codomain in our use sites, so we want it
    explicit. *)
Arguments ar_obj {R} m.
Arguments ar_disp {R} m _.
Arguments ar_carrier {R} m _.
Arguments ar_point {R} m _.
Arguments ar_zero {R} m.
Arguments ar_zero_singleton {R} m _ _.
Arguments ar_prod {R} m _ _.
Arguments ar_prod_disp_eq {R} m _ _.
Arguments ar_prod_carrier_eq {R} m _ _.
Arguments ar_prod_uncast_meas {R} m _ _.
Arguments ar_prod_cast_meas {R} m _ _.

(** ** Morphisms in [Ar] — Paper §3

    A morphism [Y → X] in [Ar] is, by definition, a measurable function
    between the underlying measurable spaces (paper §3, the
    [Ar(Y, X)] notation). We reuse mathcomp-analysis's [{mfun _ >-> _}]
    bundle for this; the resulting type is an HB structure on
    measurable functions, with [measurable_funPT] giving the
    measurability proof. *)
Notation ar_hom Ar Y X :=
  {mfun ar_carrier Ar Y >-> ar_carrier Ar X}.

(** ** Derived constructions

    [ar_zero_pt Ar] — the canonical inhabitant of the terminal
    object's carrier. Equivalent to [ar_point Ar (ar_zero Ar)] but
    named for clarity at every use site (the paper writes [0] for
    this). *)

Section ArDerived.
Variable R : realType.
Variable Ar : MeasSubcat R.

(** The terminal point of [Ar], named after the paper's [0]. *)
Definition ar_zero_pt : ar_carrier Ar (ar_zero Ar) := ar_point Ar (ar_zero Ar).

(** Any two points of the terminal carrier are equal. *)
Lemma ar_zero_ptE (x : ar_carrier Ar (ar_zero Ar)) : x = ar_zero_pt.
Proof. exact: ar_zero_singleton. Qed.

End ArDerived.

Arguments ar_zero_pt {R} Ar.

(** ** Cartesian product helpers — Paper §3 (universal property)

    The record field [ar_prod_carrier_eq] only equates
    [ar_carrier (ar_prod X Y)] with [(ar_carrier X * ar_carrier Y)%type]
    *propositionally at type [Type]*. Downstream files that need to
    move functions and elements across this equality therefore have
    to transport via [eq_rect] / [eq_rect_r]. The helpers below
    package the two casts, their round-trip identities, and the
    categorical product projections, pairing, and universal property
    as measurable functions ([ar_hom]).

    The measurability of the two casts is part of the [MeasSubcat]
    record itself ([ar_prod_uncast_meas], [ar_prod_cast_meas]). Cast
    measurability is not provable from the pure [:> Type] equality
    (the two sides have *a priori* unrelated sigma-algebras); it is
    therefore a constructor obligation of every [MeasSubcat]. For
    every standard realisation (where [ar_prod] is the actual product
    [measurableType], so the equality is [eq_refl]), both fields are
    discharged by [measurable_id]. *)

Section ArProdHelpers.
Variable R : realType.
Variable Ar : MeasSubcat R.
Variables X Y : ar_obj Ar.

(** Forward cast: [ar_carrier (ar_prod X Y) -> ar_carrier X *
    ar_carrier Y]. Defined via [eq_rect] on the propositional
    equality [ar_prod_carrier_eq]. *)
Definition ar_prod_uncast (p : ar_carrier Ar (ar_prod Ar X Y)) :
    (ar_carrier Ar X * ar_carrier Ar Y)%type :=
  eq_rect _ (fun T : Type => T) p _ (ar_prod_carrier_eq Ar X Y).

(** Backward cast: [ar_carrier X * ar_carrier Y -> ar_carrier
    (ar_prod X Y)]. Defined via [eq_rect_r] on the same equality. *)
Definition ar_prod_cast (p : (ar_carrier Ar X * ar_carrier Ar Y)%type) :
    ar_carrier Ar (ar_prod Ar X Y) :=
  eq_rect_r (fun T : Type => T) p (ar_prod_carrier_eq Ar X Y).

(** Round-trip identity: [ar_prod_uncast] is a left inverse of
    [ar_prod_cast]. *)
Lemma ar_prod_castK p : ar_prod_uncast (ar_prod_cast p) = p.
Proof.
rewrite /ar_prod_uncast /ar_prod_cast /eq_rect_r.
generalize (ar_prod_carrier_eq Ar X Y) => e.
move: p.
generalize dependent (Measurable.sort (ar_carrier Ar (ar_prod Ar X Y))).
by move=> a e p; case: _ / e in p *.
Qed.

(** Round-trip identity: [ar_prod_uncast] is a right inverse of
    [ar_prod_cast]. *)
Lemma ar_prod_uncastK x : ar_prod_cast (ar_prod_uncast x) = x.
Proof.
rewrite /ar_prod_uncast /ar_prod_cast /eq_rect_r.
generalize (ar_prod_carrier_eq Ar X Y) => e.
move: x.
generalize dependent (Measurable.sort (ar_carrier Ar (ar_prod Ar X Y))).
by move=> a e p; case: _ / e in p *.
Qed.

(** First projection of the categorical product, packaged as an
    [ar_hom]. Measurability follows from the record field
    [ar_prod_uncast_meas]. *)
Definition ar_prod_fst_fun (p : ar_carrier Ar (ar_prod Ar X Y)) :
    ar_carrier Ar X := (ar_prod_uncast p).1.

Lemma ar_prod_fst_fun_meas :
  measurable_fun setT ar_prod_fst_fun.
Proof.
rewrite /ar_prod_fst_fun /ar_prod_uncast.
exact: (measurableT_comp measurable_fst (ar_prod_uncast_meas Ar X Y)).
Qed.

HB.instance Definition _ :=
  isMeasurableFun.Build _ _ _ _ ar_prod_fst_fun ar_prod_fst_fun_meas.

Definition ar_prod_fst : ar_hom Ar (ar_prod Ar X Y) X := ar_prod_fst_fun.

(** Second projection of the categorical product, packaged as an
    [ar_hom]. *)
Definition ar_prod_snd_fun (p : ar_carrier Ar (ar_prod Ar X Y)) :
    ar_carrier Ar Y := (ar_prod_uncast p).2.

Lemma ar_prod_snd_fun_meas :
  measurable_fun setT ar_prod_snd_fun.
Proof.
rewrite /ar_prod_snd_fun /ar_prod_uncast.
exact: (measurableT_comp measurable_snd (ar_prod_uncast_meas Ar X Y)).
Qed.

HB.instance Definition _ :=
  isMeasurableFun.Build _ _ _ _ ar_prod_snd_fun ar_prod_snd_fun_meas.

Definition ar_prod_snd : ar_hom Ar (ar_prod Ar X Y) Y := ar_prod_snd_fun.

(** Pairing morphism: given [f : Z -> X], [g : Z -> Y] in [Ar],
    [ar_pair f g : Z -> ar_prod X Y] in [Ar]. *)
Section ArPair.
Variable Z : ar_obj Ar.
Variables (f : ar_hom Ar Z X) (g : ar_hom Ar Z Y).

Definition ar_pair_fun : ar_carrier Ar Z ->
    ar_carrier Ar (ar_prod Ar X Y) :=
  fun z => ar_prod_cast (f z, g z).

Lemma ar_pair_fun_meas :
  measurable_fun setT ar_pair_fun.
Proof.
rewrite /ar_pair_fun /ar_prod_cast.
have meas_pair : measurable_fun setT
    (fun z => (f z, g z)).
  by apply: measurable_fun_pair; exact: measurable_funPT.
exact: (measurableT_comp (ar_prod_cast_meas Ar X Y) meas_pair).
Qed.

HB.instance Definition _ :=
  isMeasurableFun.Build _ _ _ _ ar_pair_fun ar_pair_fun_meas.

Definition ar_pair : ar_hom Ar Z (ar_prod Ar X Y) := ar_pair_fun.

(** Paper §3 universal property: [ar_prod_fst ∘ ar_pair f g = f]. *)
Lemma ar_pair_fst z : ar_prod_fst (ar_pair z) = f z.
Proof.
have -> : ar_prod_fst (ar_pair z) = ar_prod_fst_fun (ar_pair_fun z) by [].
by rewrite /ar_prod_fst_fun /ar_pair_fun ar_prod_castK.
Qed.

(** Paper §3 universal property: [ar_prod_snd ∘ ar_pair f g = g]. *)
Lemma ar_pair_snd z : ar_prod_snd (ar_pair z) = g z.
Proof.
have -> : ar_prod_snd (ar_pair z) = ar_prod_snd_fun (ar_pair_fun z) by [].
by rewrite /ar_prod_snd_fun /ar_pair_fun ar_prod_castK.
Qed.

End ArPair.

(** Paper §3 universal property: uniqueness. Any [h : Z -> X × Y]
    in [Ar] is determined pointwise by [ar_prod_fst ∘ h] and
    [ar_prod_snd ∘ h]. *)
Lemma ar_pair_uniqueE (Z : ar_obj Ar)
    (h : ar_hom Ar Z (ar_prod Ar X Y)) (z : ar_carrier Ar Z) :
  ar_prod_cast (ar_prod_fst (h z), ar_prod_snd (h z)) = h z.
Proof.
have eq1 : ar_prod_fst (h z) = (ar_prod_uncast (h z)).1 by [].
have eq2 : ar_prod_snd (h z) = (ar_prod_uncast (h z)).2 by [].
rewrite eq1 eq2 -surjective_pairing.
exact: ar_prod_uncastK.
Qed.

End ArProdHelpers.

Arguments ar_prod_uncast {R Ar X Y} p.
Arguments ar_prod_cast {R Ar X Y} p.
Arguments ar_prod_castK {R Ar X Y} p.
Arguments ar_prod_uncastK {R Ar X Y} x.
