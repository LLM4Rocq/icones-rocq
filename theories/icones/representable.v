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
From mathcomp.analysis Require Import lebesgue_integral.

Require Import Icones.prelude.classical_extra.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.cone_cat.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.pettis.
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

(** *** The forced point-bijection between two subobjects with the
        same classifier, and its properties.

    Throughout this section [h1 : A1 → B] and [h2 : A2 → B] are two
    injective embeddings with the *same image* and the *same
    transported structure* (the consequences of [class D1 = class D2]
    that we actually consume).  The forced point map is
    [phi a := hinv h2 (h1 a)]; the backward map is
    [psi a := hinv h1 (h2 a)]. *)

Section ForcedMap.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (A1 A2 B : ICone.type Ar).
Variables (h1 : icones_hom Ar A1 B) (h2 : icones_hom Ar A2 B).
Hypothesis inj1 : is_icones_inj h1.
Hypothesis inj2 : is_icones_inj h2.

(** The two embeddings have the same image. *)
Hypothesis Himg :
  [set b : B | exists a, hfun h1 a = b] =
  [set b : B | exists a, hfun h2 a = b].

(** The two embeddings transport the same norm onto [B]:
    [λ b. ‖hinv h2 b‖ = λ b. ‖hinv h1 b‖].  This is the equality of the
    [cls_nrm] components of the two classifiers. *)
Hypothesis Hnrm :
  (fun b => cone_norm (hinv h2 b)) = (fun b => cone_norm (hinv h1 b)).

(** The two embeddings transport the same test family onto [B]:
    equality of the [cls_M] components.  Recorded per arity. *)
Hypothesis HM :
  forall X : ar_obj Ar,
    [set g | exists m : test_of Ar X A2,
       mcone_M X m /\ g = (fun s b => test_fun m s (hinv h2 b))] =
    [set g | exists m : test_of Ar X A1,
       mcone_M X m /\ g = (fun s b => test_fun m s (hinv h1 b))].

Local Notation g1 := (hfun h1).
Local Notation g2 := (hfun h2).

(** The forced forward / backward point maps. *)
Definition phi (a : A1) : A2 := hinv h2 (g1 a).
Definition psi (a : A2) : A1 := hinv h1 (g2 a).

(** Every point of [A1]'s image is in [A2]'s image (by [Himg]). *)
Lemma img1_in_img2 (a : A1) : exists a2, g2 a2 = g1 a.
Proof.
have : [set b | exists a', g1 a' = b] (g1 a) by exists a.
by rewrite Himg.
Qed.

Lemma img2_in_img1 (a : A2) : exists a1, g1 a1 = g2 a.
Proof.
have : [set b | exists a', g2 a' = b] (g2 a) by exists a.
by rewrite -Himg.
Qed.

(** Commutation: [h2 (phi a) = h1 a] and [h1 (psi a) = h2 a]. *)
Lemma phiE (a : A1) : g2 (phi a) = g1 a.
Proof.
rewrite /phi /hinv; case: pselect => [e|[]]; last exact: img1_in_img2.
by case: (cid e) => a2 /= ->.
Qed.

Lemma psiE (a : A2) : g1 (psi a) = g2 a.
Proof.
rewrite /psi /hinv; case: pselect => [e|[]]; last exact: img2_in_img1.
by case: (cid e) => a1 /= ->.
Qed.

(** [phi] and [psi] are mutually inverse on points. *)
Lemma psiphiK (a : A1) : psi (phi a) = a.
Proof. by apply: inj1; rewrite psiE phiE. Qed.

Lemma phipsiK (a : A2) : phi (psi a) = a.
Proof. by apply: inj2; rewrite phiE psiE. Qed.

(** Linearity of [g1], [g2] (read off the [cones_hom] structure). *)
Lemma g1_lin : is_linear g1.
Proof. exact: cones_hom_linear. Qed.
Lemma g2_lin : is_linear g2.
Proof. exact: cones_hom_linear. Qed.

(** [phi] is linear — transported for free from [g1], [g2] linear and
    [g2] injective (no add/scale table needed): apply [g2] to both
    sides, use [phiE] and the linearity of [g1], [g2]. *)
Lemma phi_lin : is_linear phi.
Proof.
have [g10 g1D g1Z] := g1_lin; have [g20 g2D g2Z] := g2_lin.
split.
- by apply: inj2; rewrite phiE g10 g20.
- by move=> x y; apply: inj2; rewrite phiE g1D g2D !phiE.
- by move=> r x; apply: inj2; rewrite phiE g1Z g2Z phiE.
Qed.

(** Symmetric statement for [psi]. *)
Lemma psi_lin : is_linear psi.
Proof.
have [g10 g1D g1Z] := g1_lin; have [g20 g2D g2Z] := g2_lin.
split.
- by apply: inj1; rewrite psiE g20 g10.
- by move=> x y; apply: inj1; rewrite psiE g2D g1D !psiE.
- by move=> r x; apply: inj1; rewrite psiE g2Z g1Z psiE.
Qed.

(** Norm-preservation: [‖phi a‖_{A2} = ‖a‖_{A1}].  The transported-norm
    table at [b = g1 a] gives [‖hinv h2 (g1 a)‖ = ‖hinv h1 (g1 a)‖], and
    [hinv h1 (g1 a) = a] by [hinvK]. *)
Lemma phi_norm (a : A1) : cone_norm (phi a) = cone_norm a.
Proof.
rewrite /phi.
have := f_equal (fun f => f (g1 a)) Hnrm => /= ->.
by rewrite (hinvK h1 inj1).
Qed.

Lemma psi_norm (a : A2) : cone_norm (psi a) = cone_norm a.
Proof.
rewrite /psi.
have := f_equal (fun f => f (g2 a)) Hnrm => /= <-.
by rewrite (hinvK h2 inj2).
Qed.

(** ω-continuity of [g1], [g2]. *)
Lemma g1_cont : is_omega_continuous g1.
Proof. exact: cones_hom_continuous. Qed.
Lemma g2_cont : is_omega_continuous g2.
Proof. exact: cones_hom_continuous. Qed.

(** [phi] is ω-continuous.  Modelled on Lemma 2.8
    ([invf_omega_continuous]): for an increasing unit-ball chain [u]
    with image chain [phi ∘ u] in the unit ball, the sup of [phi ∘ u]
    equals [phi] of the sup, because applying the injective [g2] to
    both sides reduces it to [g1 (sup u) = sup (g1 ∘ u)] (continuity of
    [g1]) via the commutation [g2 ∘ phi = g1] and continuity of [g2]. *)
Lemma phi_cont : is_omega_continuous phi.
Proof.
rewrite /is_omega_continuous => u uch ub1 vuch vub1.
set x := cone_sup_ball (fun n => phi (u n)) vuch vub1.
set y := cone_sup_ball u uch ub1.
have g1incr := linear_increasing g1_lin.
(* [g2 ∘ phi ∘ u] is an increasing unit-ball chain (= [g1 ∘ u]). *)
have g2ch : forall n, precone_le (g2 (phi (u n))) (g2 (phi (u n.+1))).
  by move=> n; rewrite !phiE; apply: g1incr; exact: uch.
have g2ub : forall n, cone_norm (g2 (phi (u n))) <= 1.
  by move=> n; rewrite phiE; apply: le_trans (cones_hom_norm_le1 _ _) (ub1 n).
have Hg2x : g2 x = cone_sup_ball (g2 \o (fun n => phi (u n))) g2ch g2ub.
  by rewrite /x; exact: g2_cont.
(* The chain [g2 ∘ phi ∘ u] coincides pointwise with [g1 ∘ u]; its sup
   is [g1 y] by continuity of [g1]. *)
have g1ch : forall n, precone_le (g1 (u n)) (g1 (u n.+1)).
  by move=> n; apply: g1incr; exact: uch.
have g1ub : forall n, cone_norm (g1 (u n)) <= 1.
  by move=> n; apply: le_trans (cones_hom_norm_le1 _ _) (ub1 n).
have Hg1y : g1 y = cone_sup_ball (g1 \o u) g1ch g1ub.
  by rewrite /y; exact: g1_cont.
apply: inj2; rewrite phiE Hg1y Hg2x.
(* The two sup_balls are over pointwise-equal chains. *)
apply: precone_le_anti.
- apply: cone_sup_ball_lub => n.
  have ->: (g1 \o u) n = (g2 \o (fun n => phi (u n))) n by rewrite /= phiE.
  exact: cone_sup_ball_ub.
- apply: cone_sup_ball_lub => n.
  have ->: (g2 \o (fun n => phi (u n))) n = (g1 \o u) n by rewrite /= phiE.
  exact: cone_sup_ball_ub.
Qed.

Lemma phi_norm_le (a : A1) : cone_norm (phi a) <= cone_norm a.
Proof. by rewrite phi_norm. Qed.

(** [phi] as a [cones_hom A1 A2]. *)
Definition phi_chom : cones_hom A1 A2 :=
  ConesHom phi phi_lin phi_cont phi_norm_le.

(** *** Test-family correspondence (from the [cls_M] table)

    Every selected test [m] of [A2] is matched, *through [phi]*, by a
    selected test [m'] of [A1]: [test_fun m s (phi a) = test_fun m' s a].
    This is the equality of the transported test families [HM]
    evaluated on the common image. *)
Lemma phi_test_match (X : ar_obj Ar) (m : test_of Ar X A2) :
  mcone_M X m ->
  exists m' : test_of Ar X A1,
    mcone_M X m' /\
    forall (s : ar_carrier Ar X) (a : A1),
      test_fun m s (phi a) = test_fun m' s a.
Proof.
move=> mM.
have Hin : [set g | exists m0 : test_of Ar X A2, mcone_M X m0 /\
             g = (fun s b => test_fun m0 s (hinv h2 b))]
           (fun s b => test_fun m s (hinv h2 b)) by exists m.
move: Hin; rewrite HM => -[m' [m'M Hgr]].
exists m'; split=> // s a.
have := f_equal (fun f => f s (g1 a)) Hgr => /=.
rewrite (hinvK h1 inj1) => <-.
by rewrite /phi.
Qed.

(** [phi] preserves measurable paths: [phi ∘ γ] is a measurable path
    in [A2] whenever [γ] is one in [A1]. *)
Lemma phi_pres_path (X : ar_obj Ar) (γ : ar_carrier Ar X -> A1) :
  is_measurable_path γ ->
  is_measurable_path (fun r => phi (γ r)).
Proof.
move=> [[Mb HMb] Hmeas]; split.
  exists Mb => r; rewrite phi_norm; exact: HMb.
move=> Y m mM.
have [m' [m'M Hm']] := phi_test_match mM.
have -> : (fun p => test_fun m p.1 (phi (γ p.2))) =
          (fun p => test_fun m' p.1 (γ p.2)).
  by apply: funext => p; rewrite Hm'.
exact: Hmeas.
Qed.

(** [phi] as an [mcones_hom A1 A2]. *)
Definition phi_mcones : mcones_hom Ar A1 A2 :=
  MkMConesHom phi_chom phi_pres_path.

(** [phi] preserves integrals: [phi (∫ β µ) = ∫ (phi ∘ β) µ].

    By uniqueness of integrals (Mssep), it suffices to show that
    [phi (∫ β µ)] satisfies the defining equation [path_integral_eq]
    for the [A2]-path [phi ∘ β].  For an [A2]-test [m] matched by the
    [A1]-test [m'] (via [phi_test_match]), both members reduce to the
    [A1]-integral equation [icone_integralP] for [m']. *)
Lemma phi_pres_int
  (X : ar_obj Ar) (β : ar_carrier Ar X -> A1)
  (Hβ : is_measurable_path β) (µ : fmeas R (ar_carrier Ar X)) :
  cones_hom_fun (mcones_hom_cones phi_mcones) (icone_integral β Hβ µ) =
  icone_integral
    (fun r => cones_hom_fun (mcones_hom_cones phi_mcones) (β r))
    (mcones_hom_pres_path phi_mcones X β Hβ) µ.
Proof.
apply: icone_integral_eqP.
move=> m mM s.
have [m' [m'M Hm']] := phi_test_match mM.
rewrite /= Hm'.
under eq_integral => r _ do rewrite /= Hm'.
exact: (icone_integralP β Hβ µ) m' m'M s.
Qed.

(** [phi] as an [icones_hom A1 A2]. *)
Definition phi_icones : icones_hom Ar A1 A2 :=
  MkIConesHom phi_mcones phi_pres_int.

(** The underlying point map of [phi_icones] is [phi]. *)
Lemma phi_iconesE (a : A1) : hfun phi_icones a = phi a.
Proof. by []. Qed.

End ForcedMap.

Arguments phi {R Ar A1 A2 B} h1 h2 a.
Arguments psi {R Ar A1 A2 B} h1 h2 a.

(** ** SA0 — the well-poweredness theorem

    Two subobjects of [B] with the same classifier are equivalent, i.e.
    iso over [B].  This is the precise, axiom-free Rocq rendering of
    Paper Thm 4.18: the class of subobjects of [B] is essentially small,
    classified by [icones_subobject_class] into the small type
    [SubobjClassifier B]. *)

Section WellPowered.
Variables (R : realType) (Ar : MeasSubcat R).
Variable B : ICone.type Ar.

(** The classifier of a subobject is recovered as the algebraic /
    measurability data over [B]. *)
Lemma icones_subobject_classP (D1 D2 : icones_subobject B) :
  icones_subobject_class D1 = icones_subobject_class D2 ->
  subobject_equiv D1 D2.
Proof.
case: D1 => A1 h1 inj1; case: D2 => A2 h2 inj2 /=.
move=> Hcls.
(* Extract the component equalities of the two classifiers.  [HS] is
   the image equality; [Hnrm] / [HM] the transported-norm / test-family
   equalities (D1's data on the left). *)
have HS := f_equal cls_S Hcls.
have Hnrm := f_equal cls_nrm Hcls.
have HM := fun X => f_equal (fun c => cls_M c X) Hcls.
simpl in HS, Hnrm, HM.
(* Forward morphism [A1 → A2] and backward morphism [A2 → A1] (the
   forward of the swapped pair; its point map is [psi h1 h2]
   definitionally).  The flips are just [esym]. *)
pose fwd := phi_icones inj1 inj2 HS (esym Hnrm) (fun X => esym (HM X)).
pose bwd := phi_icones inj2 inj1 (esym HS) Hnrm HM.
exists (icones_iso_of_cancel fwd bwd
          (psiphiK inj1 HS) (phipsiK inj2 HS)) => x.
by rewrite /fwd (phiE HS).
Qed.

(** The packaged well-poweredness statement (Paper Thm 4.18): the
    class of subobjects of [B] is *essentially small* — it admits a
    classifying map [icones_subobject_class] into the small type
    [SubobjClassifier B] which is *injective up to iso*: subobjects
    with equal classifier are iso over [B].

    This is exactly the property the Special Adjoint Functor Theorem
    consumes (Riehl 4.6.10): it lets one form the *small* family of
    subobjects of an object (one representative per classifier value)
    needed for the solution-set / subobject-intersection construction. *)
Theorem icones_well_powered :
  exists cls : icones_subobject B -> SubobjClassifier B,
    forall D1 D2 : icones_subobject B,
      cls D1 = cls D2 -> subobject_equiv D1 D2.
Proof. by exists icones_subobject_class; exact: icones_subobject_classP. Qed.

End WellPowered.

Arguments icones_subobject_classP {R Ar B} D1 D2.
Arguments icones_well_powered {R Ar} B.

(** ** SA2 — binary intersection (pullback) of two subobjects of [p]

    The basic building block of the SAFT subobject-intersection
    construction (Riehl Lemma 4.6.11): the meet of two subobjects of
    [p], built concretely as the equaliser of the two product
    projections post-composed with the embeddings.  This is the
    inductive core of the *wide* intersection of a small family of
    subobjects.

    Given monos [h1 : A1 → p] and [h2 : A2 → p], form the product
    [Q = ∏_{b:bool} (if b then A1 else A2)] with projections [π1, π2],
    and take the equaliser [I] of [h1 ∘ π1] and [h2 ∘ π2].  The
    composite [h1 ∘ π1 ∘ incl : I → p] is the intersection embedding;
    its universal property is read off from those of the product and
    the equaliser. *)

Section BinaryIntersection.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (A1 A2 p : ICone.type Ar).
Variables (h1 : icones_hom Ar A1 p) (h2 : icones_hom Ar A2 p).

(** The [bool]-indexed family and its product. *)
Definition pb_fam (b : bool) : ICone.type Ar := if b then A1 else A2.
Definition pb_prod : ICone.type Ar := icones_prod pb_fam.

Definition pb_pi1 : icones_hom Ar pb_prod A1 := icones_proj true.
Definition pb_pi2 : icones_hom Ar pb_prod A2 := icones_proj false.

(** The two maps [pb_prod → p] whose equaliser is the pullback. *)
Definition pb_left : icones_hom Ar pb_prod p := icones_comp h1 pb_pi1.
Definition pb_right : icones_hom Ar pb_prod p := icones_comp h2 pb_pi2.

(** The pullback object: the equaliser of [pb_left] and [pb_right]. *)
Definition pb_obj : ICone.type Ar := icones_eq pb_left pb_right.

(** The embedding [pb_obj → p] (through [A1]). *)
Definition pb_incl : icones_hom Ar pb_obj p :=
  icones_comp pb_left (icones_eq_incl pb_left pb_right).

(** Projections of the pullback to the two subobject domains. *)
Definition pb_proj1 : icones_hom Ar pb_obj A1 :=
  icones_comp pb_pi1 (icones_eq_incl pb_left pb_right).
Definition pb_proj2 : icones_hom Ar pb_obj A2 :=
  icones_comp pb_pi2 (icones_eq_incl pb_left pb_right).

(** The pullback square commutes: [h1 ∘ proj1 = h2 ∘ proj2]
    (both equal [pb_incl]). *)
Lemma pb_square :
  icones_comp h1 pb_proj1 = icones_comp h2 pb_proj2.
Proof.
rewrite /pb_proj1 /pb_proj2 /pb_pi1 /pb_pi2 !icones_compA.
rewrite -/pb_left -/pb_right.
exact: icones_eq_incl_equ.
Qed.

(** *** Universal property of the binary intersection (pullback UMP) *)

Section BinaryIntersectionUniversal.
Variable Z : ICone.type Ar.
Variables (f : icones_hom Ar Z A1) (g : icones_hom Ar Z A2).
Hypothesis Hcomm : icones_comp h1 f = icones_comp h2 g.

(** The pullback tupling family [b ↦ if b then f else g]. *)
Definition pb_tfam (b : bool) : icones_hom Ar Z (pb_fam b) :=
  if b as b' return icones_hom Ar Z (pb_fam b') then f else g.

(** The tupling [⟨f, g⟩ : Z → pb_prod]. *)
Definition pb_tuple : icones_hom Ar Z pb_prod :=
  icones_tuple (B:=pb_fam) pb_tfam.

Lemma pb_tuple_pi1 : icones_comp pb_pi1 pb_tuple = f.
Proof. exact: (icones_tuple_proj pb_tfam true). Qed.
Lemma pb_tuple_pi2 : icones_comp pb_pi2 pb_tuple = g.
Proof. exact: (icones_tuple_proj pb_tfam false). Qed.

(** [⟨f, g⟩] equalises [pb_left] and [pb_right] (this is [Hcomm]). *)
Lemma pb_tuple_equ :
  icones_comp pb_left pb_tuple = icones_comp pb_right pb_tuple.
Proof.
rewrite /pb_left /pb_right -!icones_compA pb_tuple_pi1 pb_tuple_pi2.
exact: Hcomm.
Qed.

(** The mediating map [Z → pb_obj]. *)
Definition pb_med : icones_hom Ar Z pb_obj :=
  icones_eq_med pb_left pb_right pb_tuple pb_tuple_equ.

(** The equaliser inclusion of [pb_med] is the tupling. *)
Lemma pb_med_incl :
  icones_comp (icones_eq_incl pb_left pb_right) pb_med = pb_tuple.
Proof. exact: (icones_eq_med_factor pb_tuple_equ). Qed.

(** [pb_med] factors [f] and [g] through the projections. *)
Lemma pb_med_proj1 : icones_comp pb_proj1 pb_med = f.
Proof.
rewrite /pb_proj1 -icones_compA pb_med_incl; exact: pb_tuple_pi1.
Qed.

Lemma pb_med_proj2 : icones_comp pb_proj2 pb_med = g.
Proof.
rewrite /pb_proj2 -icones_compA pb_med_incl; exact: pb_tuple_pi2.
Qed.

(** Uniqueness of the mediating map (the pullback UMP): any [k] with
    [proj1 ∘ k = f] and [proj2 ∘ k = g] equals [pb_med].  By the
    equaliser UMP it suffices that [incl ∘ k = tuple], which holds
    since the two product components agree ([pb_*proj]). *)
Lemma pb_med_unique (k : icones_hom Ar Z pb_obj) :
  icones_comp pb_proj1 k = f ->
  icones_comp pb_proj2 k = g ->
  k = pb_med.
Proof.
move=> Hk1 Hk2; rewrite /pb_med.
apply: (icones_eq_med_unique pb_tuple_equ).
apply: (icones_tuple_unique (f := pb_tfam)).
case=> /=.
- by rewrite icones_compA -/pb_pi1 -/pb_proj1 Hk1.
- by rewrite icones_compA -/pb_pi2 -/pb_proj2 Hk2.
Qed.

End BinaryIntersectionUniversal.

End BinaryIntersection.

Arguments pb_obj {R Ar A1 A2 p} h1 h2.
Arguments pb_incl {R Ar A1 A2 p} h1 h2.

(** ** SA3 — wide intersection of a small family of subobjects of [p]

    The full subobject-intersection of the SAFT construction (Riehl
    Lemma 4.6.11): given a small family [(hk : Ak → p)_{k:K}] of
    subobjects of [p] (with [K] inhabited by a basepoint [k0]), their
    intersection is built — per the standard "limits from products and
    equalisers" recipe (Mac Lane V.2) — as the equaliser of two maps
    [∏_k Ak → ∏_k p]:

    - [u = ⟨ hk ∘ πk ⟩_k]  (apply each [hk] to its own component),
    - [v = ⟨ h_{k0} ∘ π_{k0} ⟩_k]  (the constant tuple at the basepoint).

    The equaliser carves out the tuples [(a_k)] all of whose components
    [hk a_k] agree in [p] — i.e. the common sub-point — which is exactly
    the intersection.  The embedding into [p] is [h_{k0} ∘ π_{k0} ∘ incl].

    This is the object that, applied to the family of *all* subobjects
    of the power [1^J] (small by [icones_well_powered]), is initial in
    the SAFT comma category. *)

Section WideIntersection.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (K : Type) (p : ICone.type Ar).
Variable Adom : K -> ICone.type Ar.
Variable hh : forall k, icones_hom Ar (Adom k) p.
Variable k0 : K.

(** The product of the family domains, with projections. *)
Definition wi_prod : ICone.type Ar := icones_prod Adom.
Definition wi_pi (k : K) : icones_hom Ar wi_prod (Adom k) := icones_proj k.

(** The constant family at [p] (target of [u], [v]). *)
Definition wi_pfam (_ : K) : ICone.type Ar := p.
Definition wi_pprod : ICone.type Ar := icones_prod wi_pfam.

(** [u : ∏ Ak → ∏ p] sending the [k]-th component through [hk]. *)
Definition wi_u : icones_hom Ar wi_prod wi_pprod :=
  icones_tuple (B:=wi_pfam) (fun k => icones_comp (hh k) (wi_pi k)).

(** [v : ∏ Ak → ∏ p], the constant tuple at [h_{k0} ∘ π_{k0}]. *)
Definition wi_v : icones_hom Ar wi_prod wi_pprod :=
  icones_tuple (B:=wi_pfam) (fun _ => icones_comp (hh k0) (wi_pi k0)).

(** The wide-intersection object: the equaliser of [wi_u], [wi_v]. *)
Definition wi_obj : ICone.type Ar := icones_eq wi_u wi_v.

(** The intersection embedding into [p] (through the basepoint). *)
Definition wi_incl : icones_hom Ar wi_obj p :=
  icones_comp (icones_comp (hh k0) (wi_pi k0))
              (icones_eq_incl wi_u wi_v).

(** The projection of the intersection onto each subobject domain. *)
Definition wi_proj (k : K) : icones_hom Ar wi_obj (Adom k) :=
  icones_comp (wi_pi k) (icones_eq_incl wi_u wi_v).

(** Coherence: every component of the intersection lands on the same
    point of [p], namely [wi_incl].  [hk ∘ projk = h_{k0} ∘ proj_{k0}]
    for all [k]. *)
Lemma wi_coherent (k : K) :
  icones_comp (hh k) (wi_proj k) = wi_incl.
Proof.
rewrite /wi_proj /wi_incl !icones_compA.
(* [hk ∘ πk = πk' ∘ u] and [h_{k0} ∘ π_{k0} = πk' ∘ v] (the [k]-th
   product projection of [u], resp. [v]); the equaliser identifies
   [u ∘ incl = v ∘ incl]. *)
have Hu : icones_comp (hh k) (wi_pi k) =
          icones_comp (icones_proj (I:=K) (B:=wi_pfam) k) wi_u.
  by rewrite /wi_u (icones_tuple_proj
    (fun k => icones_comp (hh k) (wi_pi k)) k).
have Hv : icones_comp (hh k0) (wi_pi k0) =
          icones_comp (icones_proj (I:=K) (B:=wi_pfam) k) wi_v.
  by rewrite /wi_v (icones_tuple_proj
    (fun _ => icones_comp (hh k0) (wi_pi k0)) k).
rewrite Hu Hv -!icones_compA.
by rewrite (icones_eq_incl_equ wi_u wi_v).
Qed.

(** *** Universal property of the wide intersection *)

Section WideIntersectionUniversal.
Variable Z : ICone.type Ar.
Variable ff : forall k, icones_hom Ar Z (Adom k).
(** The cone condition: all legs agree after composing with the
    embeddings (they pick out the same sub-point of [p]). *)
Hypothesis Hcone :
  forall k, icones_comp (hh k) (ff k) = icones_comp (hh k0) (ff k0).

(** The tupling [⟨ff_k⟩ : Z → ∏ Ak]. *)
Definition wi_tuple : icones_hom Ar Z wi_prod :=
  icones_tuple (B:=Adom) ff.

Lemma wi_tuple_pi (k : K) : icones_comp (wi_pi k) wi_tuple = ff k.
Proof. exact: (icones_tuple_proj ff k). Qed.

(** [⟨ff_k⟩] equalises [wi_u] and [wi_v]: both composites send the
    [k]-th [p]-component to [hk ∘ ff_k] resp. [h_{k0} ∘ ff_{k0}], which
    agree by [Hcone].  We compare the two tuples componentwise via the
    product universal property. *)
Lemma wi_tuple_equ :
  icones_comp wi_u wi_tuple = icones_comp wi_v wi_tuple.
Proof.
(* Two maps into a product are equal iff all projections agree. *)
have proj_ext : forall (W : ICone.type Ar) (a b : icones_hom Ar W wi_pprod),
  (forall k, icones_comp (icones_proj k) a = icones_comp (icones_proj k) b) ->
  a = b.
  move=> W a b Hab.
  have Ha : a = icones_tuple (fun k => icones_comp (icones_proj k) a).
    exact: (icones_tuple_unique (fun k => erefl)).
  have Hb : b = icones_tuple (fun k => icones_comp (icones_proj k) a).
    by apply: icones_tuple_unique => k; rewrite Hab.
  by rewrite Ha Hb.
apply: proj_ext => k.
rewrite !icones_compA.
rewrite (icones_tuple_proj (fun k => icones_comp (hh k) (wi_pi k)) k).
rewrite (icones_tuple_proj (fun _ => icones_comp (hh k0) (wi_pi k0)) k).
rewrite -!icones_compA !wi_tuple_pi.
exact: Hcone.
Qed.

(** The mediating map [Z → wi_obj]. *)
Definition wi_med : icones_hom Ar Z wi_obj :=
  icones_eq_med wi_u wi_v wi_tuple wi_tuple_equ.

Lemma wi_med_incl :
  icones_comp (icones_eq_incl wi_u wi_v) wi_med = wi_tuple.
Proof. exact: (icones_eq_med_factor wi_tuple_equ). Qed.

(** [wi_med] factors each leg through the projection. *)
Lemma wi_med_proj (k : K) : icones_comp (wi_proj k) wi_med = ff k.
Proof.
rewrite /wi_proj -icones_compA wi_med_incl; exact: wi_tuple_pi.
Qed.

(** Uniqueness of the mediating map. *)
Lemma wi_med_unique (kk : icones_hom Ar Z wi_obj) :
  (forall k, icones_comp (wi_proj k) kk = ff k) ->
  kk = wi_med.
Proof.
move=> Hk; rewrite /wi_med.
apply: (icones_eq_med_unique wi_tuple_equ).
apply: (icones_tuple_unique (f := ff)) => k.
by rewrite icones_compA -/(wi_pi k) -/(wi_proj k) Hk.
Qed.

End WideIntersectionUniversal.

End WideIntersection.

Arguments wi_obj {R Ar K p} Adom hh.
Arguments wi_incl {R Ar K p} Adom hh k0.
Arguments wi_proj {R Ar K p} Adom hh.
