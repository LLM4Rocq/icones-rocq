(**md * Isomorphisms in [ICones]

    A reusable notion of *isomorphism in the category [ICones]* together
    with its basic theory.  This is the categorical packaging needed by
    the tensor milestone, which states its structural equivalence [Φ]
    as an [icones_iso].

    The concrete category [ICones] is built in
    [Icones.icones.icone_cat]: objects are [ICone.type Ar], morphisms are
    [icones_hom Ar B C], with identity [icones_id], composition
    [icones_comp] (where [icones_comp g f] is "[g] after [f]"), and the
    category laws [icones_compIl], [icones_compIr], [icones_compA]
    proved.  Equality of morphisms is pointwise via [icones_hom_eq].

    Coverage in this file.

    - [icones_iso Ar B C] — the isomorphism record, packaging a forward
      [icones_hom Ar B C], a backward [icones_hom Ar C B], and the two
      round-trip equations [icones_comp bwd fwd = icones_id Ar B] and
      [icones_comp fwd bwd = icones_id Ar C].

    - [icones_isoP] — the smart constructor: build an [icones_iso] from a
      forward and backward [icones_hom] plus the two cancellation
      equations.  A "Yoneda-style" companion [icones_iso_of_cancel]
      builds an [icones_iso] from cancellation stated *pointwise*.

    - [icones_iso_refl], [icones_iso_sym], [icones_iso_trans] — the
      groupoid structure of isos: reflexivity (identity iso [B ≅ B]),
      symmetry ([B ≅ C → C ≅ B]) and transitivity (composition of
      isos).

    - [iso_can], [iso_can'] — the underlying forward and backward
      functions are mutually inverse pointwise.

    - [iso_fwd_bij] — the underlying forward function of an [icones_iso]
      is bijective. *)

From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals.

Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.cone_cat.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_cat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** The isomorphism record — an iso in [ICones]

    A morphism [f : icones_hom Ar B C] is an isomorphism when it admits
    a two-sided inverse [g : icones_hom Ar C B].  We package the witness
    and both round-trip equations directly. *)

Section IConesIso.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : ICone.type Ar.

(** An isomorphism [B ≅ C] in [ICones]. *)
Record icones_iso : Type := MkIConesIso {
  iso_fwd : icones_hom Ar B C;
  iso_bwd : icones_hom Ar C B;
  iso_fwdK : icones_comp iso_bwd iso_fwd = icones_id Ar B;
  iso_bwdK : icones_comp iso_fwd iso_bwd = icones_id Ar C;
}.

End IConesIso.

Arguments icones_iso {R} Ar B C.
Arguments MkIConesIso {R Ar B C}.
Arguments iso_fwd {R Ar B C}.
Arguments iso_bwd {R Ar B C}.
Arguments iso_fwdK {R Ar B C}.
Arguments iso_bwdK {R Ar B C}.

(** ** Smart constructors *)

Section IConesIsoBuild.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : ICone.type Ar.

(** Build an [icones_iso] from a forward and backward morphism and the
    two cancellation equations stated at the level of [icones_comp]. *)
Definition icones_isoP
    (fwd : icones_hom Ar B C) (bwd : icones_hom Ar C B)
    (fwdK : icones_comp bwd fwd = icones_id Ar B)
    (bwdK : icones_comp fwd bwd = icones_id Ar C) : icones_iso Ar B C :=
  MkIConesIso fwd bwd fwdK bwdK.

(** "Yoneda-style" companion: build an [icones_iso] from a forward and
    backward morphism whose composites cancel *pointwise*.  By
    [icones_hom_eq] pointwise cancellation upgrades to the equational
    form required by the record. *)
Lemma icones_iso_of_cancel_fwdK
    (fwd : icones_hom Ar B C) (bwd : icones_hom Ar C B) :
  (forall x : B, bwd (fwd x) = x) ->
  icones_comp bwd fwd = icones_id Ar B.
Proof. by move=> fwdK; apply: icones_hom_eq => x; rewrite /= fwdK. Qed.

Lemma icones_iso_of_cancel_bwdK
    (fwd : icones_hom Ar B C) (bwd : icones_hom Ar C B) :
  (forall y : C, fwd (bwd y) = y) ->
  icones_comp fwd bwd = icones_id Ar C.
Proof. by move=> bwdK; apply: icones_hom_eq => y; rewrite /= bwdK. Qed.

Definition icones_iso_of_cancel
    (fwd : icones_hom Ar B C) (bwd : icones_hom Ar C B)
    (fwdK : forall x : B, bwd (fwd x) = x)
    (bwdK : forall y : C, fwd (bwd y) = y) : icones_iso Ar B C :=
  MkIConesIso fwd bwd
    (icones_iso_of_cancel_fwdK fwdK)
    (icones_iso_of_cancel_bwdK bwdK).

End IConesIsoBuild.

Arguments icones_isoP {R Ar B C}.
Arguments icones_iso_of_cancel {R Ar B C}.

(** ** Pointwise cancellation and bijectivity

    From an [icones_iso] we recover the pointwise facts that the
    underlying forward and backward functions cancel, and hence that the
    forward function is bijective. *)

Section IConesIsoCancel.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : ICone.type Ar.
Variable phi : icones_iso Ar B C.

(** The backward map is a left inverse of the forward map. *)
Lemma iso_can (x : B) : iso_bwd phi (iso_fwd phi x) = x.
Proof.
by rewrite -[LHS]/(icones_comp (iso_bwd phi) (iso_fwd phi) x) iso_fwdK.
Qed.

(** The forward map is a left inverse of the backward map. *)
Lemma iso_can' (y : C) : iso_fwd phi (iso_bwd phi y) = y.
Proof.
by rewrite -[LHS]/(icones_comp (iso_fwd phi) (iso_bwd phi) y) iso_bwdK.
Qed.

(** The forward function of an [icones_iso] is injective. *)
Lemma iso_fwd_inj : injective (iso_fwd phi).
Proof. by move=> x1 x2 Hx; rewrite -(iso_can x1) Hx iso_can. Qed.

(** The forward function of an [icones_iso] is bijective (total form):
    [iso_bwd phi] is its two-sided inverse. *)
Lemma iso_fwd_bij : bijective (iso_fwd phi).
Proof. by exists (iso_bwd phi); [exact: iso_can | exact: iso_can']. Qed.

(** The forward function of an [icones_iso] is a bijection from [setT]
    to [setT] (classical-sets form). *)
Lemma iso_fwd_setbij : set_bij setT setT (iso_fwd phi).
Proof.
split.
- by [].
- by apply: in2W; exact: iso_fwd_inj.
- by move=> y _ /=; exists (iso_bwd phi y) => //; rewrite iso_can'.
Qed.

End IConesIsoCancel.

Arguments iso_can {R Ar B C}.
Arguments iso_can' {R Ar B C}.
Arguments iso_fwd_inj {R Ar B C}.
Arguments iso_fwd_bij {R Ar B C}.

(** ** Groupoid structure: reflexivity, symmetry, transitivity *)

Section IConesIsoGroupoid.
Variables (R : realType) (Ar : MeasSubcat R).

(** The identity iso [B ≅ B]. *)
Definition icones_iso_refl (B : ICone.type Ar) : icones_iso Ar B B :=
  icones_isoP (icones_id Ar B) (icones_id Ar B)
    (icones_compIl (icones_id Ar B)) (icones_compIl (icones_id Ar B)).

(** Symmetry: [B ≅ C → C ≅ B], by swapping forward and backward. *)
Definition icones_iso_sym (B C : ICone.type Ar)
    (phi : icones_iso Ar B C) : icones_iso Ar C B :=
  icones_isoP (iso_bwd phi) (iso_fwd phi) (iso_bwdK phi) (iso_fwdK phi).

(** Transitivity: composing two isos [B ≅ C] and [C ≅ D] yields an iso
    [B ≅ D].  The composite forward is [psi ∘ phi], the composite
    backward is [phi⁻¹ ∘ psi⁻¹]; cancellation follows from associativity
    and the round-trip equations of [phi] and [psi]. *)

Section Trans.
Variables B C D : ICone.type Ar.
Variables (phi : icones_iso Ar B C) (psi : icones_iso Ar C D).

Lemma icones_iso_trans_fwdK :
  icones_comp (icones_comp (iso_bwd phi) (iso_bwd psi))
              (icones_comp (iso_fwd psi) (iso_fwd phi)) = icones_id Ar B.
Proof.
apply: icones_hom_eq => x.
by rewrite /= !iso_can.
Qed.

Lemma icones_iso_trans_bwdK :
  icones_comp (icones_comp (iso_fwd psi) (iso_fwd phi))
              (icones_comp (iso_bwd phi) (iso_bwd psi)) = icones_id Ar D.
Proof.
apply: icones_hom_eq => y.
by rewrite /= !iso_can'.
Qed.

Definition icones_iso_trans : icones_iso Ar B D :=
  icones_isoP
    (icones_comp (iso_fwd psi) (iso_fwd phi))
    (icones_comp (iso_bwd phi) (iso_bwd psi))
    icones_iso_trans_fwdK icones_iso_trans_bwdK.

End Trans.

End IConesIsoGroupoid.

Arguments icones_iso_refl {R Ar}.
Arguments icones_iso_sym {R Ar B C}.
Arguments icones_iso_trans {R Ar B C D}.

(** ** Object-Yoneda: a natural hom-bijection induces an iso — Lemma 1.1

    Given, for every object [A], a bijection [psi A : ICones(A, X) →
    ICones(A, Y)] with inverse [psiV A], whose round-trips [psiK]/[psiVK]
    hold and which is *natural in [A]* (the "diagonal" naturality
    [psi (g ∘ f) = (psi g) ∘ f], [psiV (g ∘ f) = (psiV g) ∘ f]), the
    representing object morphisms [psi id_X : X → Y] and
    [psiV id_Y : Y → X] assemble into an iso [X ≅ Y].  Crucially the
    forward and backward morphisms are *outputs of the bijection* (hence
    already [icones_hom]s), so no [icones_hom] structure obligation
    arises here. *)

Section YonedaIso.
Variables (R : realType) (Ar : MeasSubcat R).
Variables X Y : ICone.type Ar.
Variable psi : forall A : ICone.type Ar, icones_hom Ar A X -> icones_hom Ar A Y.
Variable psiV : forall A : ICone.type Ar, icones_hom Ar A Y -> icones_hom Ar A X.
Hypothesis psiK : forall (A : ICone.type Ar) (f : icones_hom Ar A X),
  psiV (psi f) = f.
Hypothesis psiVK : forall (A : ICone.type Ar) (g : icones_hom Ar A Y),
  psi (psiV g) = g.
Hypothesis psi_nat : forall (A A' : ICone.type Ar)
  (f : icones_hom Ar A X) (g : icones_hom Ar A' A),
  psi (icones_comp f g) = icones_comp (psi f) g.
Hypothesis psiV_nat : forall (A A' : ICone.type Ar)
  (f : icones_hom Ar A Y) (g : icones_hom Ar A' A),
  psiV (icones_comp f g) = icones_comp (psiV f) g.

Lemma yoneda_iso_fwdK :
  icones_comp (psiV (icones_id Ar Y)) (psi (icones_id Ar X)) =
  icones_id Ar X.
Proof.
by rewrite -psiV_nat icones_compIl psiK.
Qed.

Lemma yoneda_iso_bwdK :
  icones_comp (psi (icones_id Ar X)) (psiV (icones_id Ar Y)) =
  icones_id Ar Y.
Proof.
by rewrite -psi_nat icones_compIl psiVK.
Qed.

Definition yoneda_iso : icones_iso Ar X Y :=
  icones_isoP (psi (icones_id Ar X)) (psiV (icones_id Ar Y))
    yoneda_iso_fwdK yoneda_iso_bwdK.

End YonedaIso.

Arguments yoneda_iso {R Ar X Y}.

(** ** Co-Yoneda: a CONTRAVARIANT natural hom-bijection induces an iso

    The contravariant dual of [yoneda_iso].  Given, for every object [A],
    a bijection [psi A : ICones(X, A) → ICones(Y, A)] with inverse
    [psiV A], whose round-trips [psiK]/[psiVK] hold and which is *natural
    in [A] by POSTcomposition* ([psi (g ∘ f) = g ∘ psi f], [psiV (g ∘ f) =
    g ∘ psiV f]), the representing object morphisms assemble into an iso
    [X ≅ Y].  Since the representables are contravariant, the FORWARD
    [X → Y] is [psiV id_Y] (a morphism [X → Y]) and the BACKWARD [Y → X]
    is [psi id_X].  As in [yoneda_iso] the morphisms are *outputs of the
    bijection* (already [icones_hom]s), so no structure obligation
    arises.  This is the assembly tool for comparing contravariant
    representables (e.g. the Seely-iso bijection chain in [seely.v]). *)

Section CoYonedaIso.
Variables (R : realType) (Ar : MeasSubcat R).
Variables X Y : ICone.type Ar.
Variable psi : forall A : ICone.type Ar, icones_hom Ar X A -> icones_hom Ar Y A.
Variable psiV : forall A : ICone.type Ar, icones_hom Ar Y A -> icones_hom Ar X A.
Hypothesis psiK : forall (A : ICone.type Ar) (f : icones_hom Ar X A),
  psiV (psi f) = f.
Hypothesis psiVK : forall (A : ICone.type Ar) (g : icones_hom Ar Y A),
  psi (psiV g) = g.
Hypothesis psi_nat : forall (A A' : ICone.type Ar)
  (f : icones_hom Ar X A) (g : icones_hom Ar A A'),
  psi (icones_comp g f) = icones_comp g (psi f).
Hypothesis psiV_nat : forall (A A' : ICone.type Ar)
  (f : icones_hom Ar Y A) (g : icones_hom Ar A A'),
  psiV (icones_comp g f) = icones_comp g (psiV f).

(** [bwd ∘ fwd = id_X], where [fwd = psiV id_Y : X → Y] and
    [bwd = psi id_X : Y → X].  Read off via [psiV] postcomposition
    naturality: [psi id_X ∘ psiV id_Y = psiV (psi id_X ∘ id_Y) =
    psiV (psi id_X) = id_X] (by [psiV_nat], [icones_compIr], [psiK]). *)
Lemma co_yoneda_iso_fwdK :
  icones_comp (psi (icones_id Ar X)) (psiV (icones_id Ar Y)) =
  icones_id Ar X.
Proof.
by rewrite -psiV_nat icones_compIr psiK.
Qed.

Lemma co_yoneda_iso_bwdK :
  icones_comp (psiV (icones_id Ar Y)) (psi (icones_id Ar X)) =
  icones_id Ar Y.
Proof.
by rewrite -psi_nat icones_compIr psiVK.
Qed.

Definition co_yoneda_iso : icones_iso Ar X Y :=
  icones_isoP (psiV (icones_id Ar Y)) (psi (icones_id Ar X))
    co_yoneda_iso_fwdK co_yoneda_iso_bwdK.

End CoYonedaIso.

Arguments co_yoneda_iso {R Ar X Y}.
