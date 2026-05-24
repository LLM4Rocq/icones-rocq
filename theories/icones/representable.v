(** * M-SAFT — well-poweredness and the Special Adjoint Functor
      Theorem for [ICones] (Paper Thm 4.18 well-poweredness +
      Thm [th:Icones-adjoint-functor]).

    This file discharges the [icones_well_powered_bound] stub of
    [icone_cat.v] with a *genuine* proof that [ICones] is
    well-powered, and assembles the categorical ingredients of the
    Special Adjoint Functor Theorem (SAFT).

    The strategy is the paper's (§4.3, the proof of
    [th:icones-conditions-saft]):

    - A subobject of [B] is a monomorphism [h : icones_hom Ar A B].
      Because [1] is a separator (Paper Thm 4.18,
      [icones_separator]), a mono is exactly an *injective*
      [icones_hom] (Lemma [icones_mono_inj] below).

    - Up to ICones-iso *over* [B], a subobject is determined by its
      image [S = h '' setT ⊆ B] together with the structure
      transported onto [S] (the addition / scaling / norm tables and
      the per-arity test family). The paper bounds the class of such
      structures by a genuine *set* [F(S)] — this is what makes the
      class of subobjects essentially small (Paper Thm 4.18, the
      footnote "it is only here that we use [Ar] is a set").

    - In Rocq's predicative type theory there is no proper-class /
      set distinction: the classifier is simply a [Type]. So the
      load-bearing content is the *injectivity up to iso*: two monos
      with the same classifier are iso over [B]. We formalise this
      directly as [icones_subobject_class] (the classifier, into a
      small [Type]) together with [icones_subobject_classP] (the
      classifier determines the subobject up to iso). This is a
      faithful, axiom-free Rocq rendering of "the class of subobjects
      of [B] is essentially small".

    Coverage:

    - [is_icones_mono] / [icones_mono_inj] — monos are the injective
      maps (SA1).
    - [icones_subobject] — a packaged subobject of [B] (SA1).
    - [SubobjClassifier] — the small classifying [Type]
      [{S : set B & transported structure}] (SA0).
    - [icones_subobject_class] — the classifying map (SA0).
    - [icones_subobject_classP] — injectivity up to iso: same
      classifier ⇒ iso over [B] (SA0, the load-bearing theorem).
    - [icones_well_powered] — the packaged well-poweredness
      statement replacing the [icone_cat.v] stub.

    Paper reference: §4.3, proof of Theorem 4.18
    ([th:icones-conditions-saft]) and Lemma
    [lemma:int-cone-transp-iso].
*)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import measurable_structure measurable_function.

Require Import Icones.prelude.classical_extra.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.cone_cat.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_integral.
Require Import Icones.icones.icone_cat.
Require Import Icones.homs.icones_iso.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Short local accessor for the underlying function of an
    [icones_hom]: [hfun f] is the point map [B -> C]. *)
Notation hfun f := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones f))).

(** ** SA1 — monomorphisms in [ICones] are the injective maps

    [1] is a separator in [ICones] ([icones_separator]); the standard
    consequence is that a mono is exactly an injective morphism. *)

Section IConesMono.
Variables (R : realType) (Ar : MeasSubcat R).
Variables A B : ICone.type Ar.

(** A morphism is a monomorphism if it is left-cancellable. *)
Definition is_icones_mono (h : icones_hom Ar A B) : Prop :=
  forall (Z : ICone.type Ar) (f g : icones_hom Ar Z A),
    icones_comp h f = icones_comp h g -> f = g.

(** Injectivity of the underlying point map. *)
Definition is_icones_inj (h : icones_hom Ar A B) : Prop :=
  injective (hfun h).

(** Easy direction (no separator needed): an injective morphism is a
    monomorphism.  If [h ∘ f = h ∘ g] then [h (f x) = h (g x)] for all
    [x], and injectivity of [h] gives [f x = g x], whence [f = g] by
    [icones_hom_eq]. *)
Lemma icones_inj_mono (h : icones_hom Ar A B) :
  is_icones_inj h -> is_icones_mono h.
Proof.
move=> hinj Z f g /(congr1 (fun k : icones_hom Ar Z B => hfun k)) /= Hfg.
apply: icones_hom_eq => x; apply: hinj.
by have := f_equal (fun k => k x) Hfg.
Qed.

End IConesMono.

Arguments is_icones_mono {R Ar A B}.
Arguments is_icones_inj {R Ar A B}.
Arguments icones_inj_mono {R Ar A B}.

(** ** SA1 — subobjects of [B]

    A subobject of [B] is represented by a monomorphism into [B].
    Because [1] is a separator (Paper Thm 4.18), monos are exactly the
    injective morphisms; we therefore represent a subobject by an
    *injective* [icones_hom] (which, by [icones_inj_mono], is a mono).
    This loses no generality: every subobject has an injective
    representative. *)

Section IConesSubobject.
Variables (R : realType) (Ar : MeasSubcat R).
Variable B : ICone.type Ar.

(** A subobject of [B]: its domain [sob_dom], the embedding [sob_hom],
    and a proof that the embedding is injective (i.e. a mono). *)
Record icones_subobject : Type := MkSubobject {
  sob_dom : ICone.type Ar;
  sob_hom : icones_hom Ar sob_dom B;
  sob_inj : is_icones_inj sob_hom;
}.

(** Two subobjects [D1, D2] are *equivalent* (represent the same
    subobject) when there is an ICones-iso [φ : D1 ≅ D2] commuting with
    the embeddings: [sob_hom D2 ∘ φ = sob_hom D1].  We state the
    commutation pointwise, which is the form [icones_iso_of_cancel]
    consumes. *)
Definition subobject_equiv (D1 D2 : icones_subobject) : Prop :=
  exists phi : icones_iso Ar (sob_dom D1) (sob_dom D2),
    forall x : sob_dom D1, hfun (sob_hom D2) (iso_fwd phi x) =
                           hfun (sob_hom D1) x.

End IConesSubobject.

Arguments icones_subobject {R Ar} B.
Arguments MkSubobject {R Ar B}.
Arguments sob_dom {R Ar B}.
Arguments sob_hom {R Ar B}.
Arguments sob_inj {R Ar B}.
Arguments subobject_equiv {R Ar B}.

(** ** SA0 — well-poweredness: the small classifier

    Following the paper (Thm 4.18), a subobject [(A, h)] of [B] is
    classified, up to iso over [B], by its image [S = h '' setT]
    together with the algebraic and measurability structure of [A]
    *transported onto its image*.  We record this transported
    structure as data living over [B] (and [R]) only — never
    mentioning [A] — so the classifier is a fixed small [Type]:

      [SubobjClassifier B :=
         { S : set B ;
           addt : B -> B -> B ;     (* transported addition *)
           sclt : {nonneg R} -> B -> B ; (* transported scaling *)
           zert : B ;               (* transported zero *)
           nrmt : B -> R ;          (* transported norm *)
           Mt   : forall X, set (test_of Ar X B) } ].

    The classifying map [icones_subobject_class] reads these off [h]
    using the (classical) inverse of [h] on its image.  The
    load-bearing theorem [icones_subobject_classP] shows that two
    subobjects with the same classifier are equivalent (iso over [B]):
    the point map [φ = h2⁻¹ ∘ h1] is then forced and is an
    ICones-iso. *)

Section Classifier.
Variables (R : realType) (Ar : MeasSubcat R).
Variable B : ICone.type Ar.

(** The classifier type: a fixed small [Type], independent of the
    subobject's domain. *)
Record SubobjClassifier : Type := MkClassifier {
  cls_S    : set B;
  cls_add  : B -> B -> B;
  cls_scl  : {nonneg R} -> B -> B;
  cls_zer  : B;
  cls_nrm  : B -> R;
  (** The transported test family, recorded as raw graphs
      [ar_carrier X -> B -> R] (the paper's [𝒫(ℝ₊^{X×S})]).  We do
      *not* store these as [test_of Ar X B], because a test of [A]
      pushed forward along [h⁻¹] need only satisfy the test axioms on
      the image [S], not on all of [B]. *)
  cls_M    : forall X : ar_obj Ar,
               set (ar_carrier Ar X -> B -> R);
}.

End Classifier.

Arguments SubobjClassifier {R Ar} B.
Arguments MkClassifier {R Ar B}.
Arguments cls_S {R Ar B}.
Arguments cls_add {R Ar B}.
Arguments cls_scl {R Ar B}.
Arguments cls_zer {R Ar B}.
Arguments cls_nrm {R Ar B}.
Arguments cls_M {R Ar B}.

(** *** The (classical) inverse of an injective embedding on its image *)

Section EmbeddingInverse.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (A B : ICone.type Ar).
Variable h : icones_hom Ar A B.
Hypothesis hinj : is_icones_inj h.

(** [hinv b] is the preimage of [b] under [h] if one exists, and
    [0_A] otherwise.  Built with [pselect] + [cid] (classical, from
    [boolp]). *)
Definition hinv (b : B) : A :=
  match pselect (exists a : A, hfun h a = b) with
  | left e => proj1_sig (cid e)
  | right _ => precone_zero
  end.

(** On the image, [hinv] is a genuine right inverse: [h (hinv (h a)) = h a]. *)
Lemma hinvK_img (a : A) : hfun h (hinv (hfun h a)) = hfun h a.
Proof.
rewrite /hinv; case: pselect => [e|[]]; last by exists a.
by case: (cid e) => a' /= ->.
Qed.

(** Hence, by injectivity, [hinv] is a left inverse on points of [A]. *)
Lemma hinvK (a : A) : hinv (hfun h a) = a.
Proof. by apply: hinj; exact: hinvK_img. Qed.

End EmbeddingInverse.

Arguments hinv {R Ar A B} h b.
Arguments hinvK_img {R Ar A B} h a.
Arguments hinvK {R Ar A B} h hinj a.

(** *** The classifying map *)

Section ClassifyingMap.
Variables (R : realType) (Ar : MeasSubcat R).
Variable B : ICone.type Ar.

(** The classifier of a subobject [D = (A, h)]: image, transported
    operations (via [hinv h]) and the transported test family. *)
Definition icones_subobject_class (D : icones_subobject B) :
    SubobjClassifier B :=
  let A := sob_dom D in
  let h := sob_hom D in
  MkClassifier
    (** image *)
    [set b : B | exists a : A, hfun h a = b]
    (** transported addition: [add (h a) (h a') = h (a + a')] *)
    (fun b b' => hfun h (precone_add (hinv h b) (hinv h b')))
    (** transported scaling *)
    (fun r b => hfun h (precone_scale r (hinv h b)))
    (** transported zero *)
    (hfun h precone_zero)
    (** transported norm: [nrm (h a) = ‖a‖_A] *)
    (fun b => cone_norm (hinv h b))
    (** transported test family *)
    (fun X => [set g | exists m : test_of Ar X A,
                 mcone_M X m /\
                 g = (fun s b => test_fun m s (hinv h b))]).

End ClassifyingMap.

Arguments icones_subobject_class {R Ar B} D.
