(**md**************************************************************************)
(* # Tensor construction — the tensor [B ⊗ C] as the SAFT left adjoint of     *)
(*   [(C ⊸ −)], with the hom-bijection PROVED (Paper §5.4, Thm 5.9 +          *)
(*   [th:Icones-adjoint-functor]).                                            *)
(*                                                                            *)
(* This file builds, as genuine theorems about a concrete construction,       *)
(* the eight tensor-adjunction primitives:                                    *)
(*                                                                            *)
(*   tensor, tensor_curry, tensor_uncurry, tensor_curryK, tensor_uncurryK,    *)
(*   tensor_curry_natural_post, tensor_curry_natural_D, tensor_curry_natural_B *)
(*                                                                            *)
(* It is AXIOM-FREE relative to the classical [boolp] base ([pselect]/[cid]/  *)
(* extensionality) — NO [Axiom]/[Parameter]/[Admitted].  The definitions live *)
(* in their own module [Icones.homs.tensor_construct].                        *)
(*                                                                            *)
(* ## The construction (PLAN §13.1/§13.2, Riehl 4.6.11 with [Φ = {1}])         *)
(*                                                                            *)
(* Fix integrable cones [B], [C].  Write [1 := cone_one_car Ar] (the          *)
(* coseparator).                                                              *)
(*                                                                            *)
(*  1. [J := icones_hom Ar B (C ⊸ 1)] — a [Type] (the homset of [C ⊸ 1]).     *)
(*  2. [p := icones_prod (fun _ : J => 1)] — the coseparator power [1^J].      *)
(*  3. The universal map [e_B : B → C ⊸ p], the tuple of all [J]-elements      *)
(*     transported into [C ⊸ p] through [limpl_preserves_prod]:                *)
(*       [e_B := iso_bwd (limpl_preserves_prod C _) ∘ icones_tuple id_J].      *)
(*  4. [tensor B C := wi_obj] (the wide intersection of [representable.v]),     *)
(*     over the family [K] of all subobjects [(A, h)] of [p] through which     *)
(*     [e_B] factors via [C ⊸ h] (i.e. [∃ eA, (C ⊸ h) ∘ eA = e_B]);            *)
(*     the basepoint [k0] is the identity subobject [p ↪ p] (which factors     *)
(*     [e_B] by [eA := e_B]).  In Rocq's predicative [Type] theory the family  *)
(*     is just a [Type], so [wi_obj] applies directly (well-poweredness        *)
(*     [icones_well_powered] is what makes this small set-theoretically; here  *)
(*     it is automatic).                                                        *)
(*  5. [tau' : B → C ⊸ (B ⊗ C)] — co-restrict [e_B] through [C ⊸ wi_incl],     *)
(*     using that [C ⊸ −] preserves the product-then-equaliser limit           *)
(*     [wi_obj] ([limpl_preserves_prod] + [limpl_eq_med] of                    *)
(*     [limpl_continuous.v]).                                                  *)
(*                                                                            *)
(* ## The shared SAFT engine ([saft_construct.v])                              *)
(*                                                                            *)
(* The SAFT argument itself — the factoring family, the classifier            *)
(* reindexing, the wide intersection, intersection minimality, the             *)
(* universal element and its round-trips — is functor-parametric and is        *)
(* proved ONCE in [Icones.homs.saft_construct] (module                         *)
(* [Icones_saft_construct], aliased [SC] below) against the signature          *)
(* [SC.saft_sig].  This file instantiates that signature with the right        *)
(* functor [(C ⊸ −)] ([tensor_sig]: [tensor_ehom X := ICones(B, C ⊸ X)],       *)
(* [tensor_emap h := (C ⊸ h) ∘ −] via [linhom_post_icones], products via       *)
(* [limpl_preserves_prod], equalisers via [limpl_eq_med_icones]) and           *)
(* re-exports every historical name; the instantiation-specific pointwise      *)
(* lemmas ([tJtupleE]/[eBE]/[eprodE]/[fpick_factE]/[tensor_curryE]/…) are      *)
(* proved here as before.                                                      *)
(*                                                                            *)
(* ## The discharge                                                            *)
(*                                                                            *)
(*  - [tensor_curry f := (C ⊸ f) ∘ tau'] (= [linhom_post_icones f ∘ tau']).    *)
(*  - [tensor_uncurry g] := the SAFT mediator with [(C ⊸ uncurry g) ∘ tau' = g].*)
(*  - [tensor_uncurryK] : DIRECT (the defining equation of [tensor_uncurry]).  *)
(*  - [tensor_curryK]   : from [tensor_curry_inj] (SAFT-uniqueness: equaliser  *)
(*    of the two candidates + intersection minimality) + [tensor_uncurryK].    *)
(*  - the three naturalities : from [linhom_post] functoriality + the          *)
(*    round-trips (naturality in [B] uses [tensor_mor_l]).                      *)
(*                                                                            *)
(* APIs used: [saft_construct.v] — the SAFT engine; [representable.v] —        *)
(* [wi_obj]/[wi_incl]/[wi_proj]; [limpl_continuous.v] —                        *)
(* [limpl_preserves_prod] + its [iso_bwd] and the equaliser co-restriction     *)
(* [limpl_eq_med_icones]/[limpl_eq_med_factor].                                *)
(******************************************************************************)

From HB Require Import structures.
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
Require Import Icones.icones.examples_icone.
Require Import Icones.icones.icone_cat.
Require Import Icones.homs.representable.
Require Import Icones.homs.linhom.
Require Import Icones.homs.linhom_functor.
Require Import Icones.homs.icones_iso.
Require Import Icones.homs.limpl_continuous.
Require Import Icones.homs.saft_construct.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Module Icones_tensor_construct.

Module SC := Icones_saft_construct.

(** ** Functoriality of the post-composition action [C ⊸ −]

    [linhom_post_icones] ([C ⊸ g]) is the action of the hom-functor in
    its covariant (codomain) slot.  We need its identity / composition
    laws as one-sided specialisations of the bifunctor laws
    [linhom_map_icones_id] / [linhom_map_icones_comp] from
    [linhom_functor.v]. *)

Section LinhomPostFunctor.
Variables (R : realType) (Ar : MeasSubcat R).
Variable C : ICone.type Ar.

(** [C ⊸ id_D = id_{C ⊸ D}]. *)
Lemma linhom_post_id (D : ICone.type Ar) :
  linhom_post_icones (C := C) (icones_id Ar D) = icones_id Ar (linhom_car Ar C D).
Proof. exact: linhom_map_icones_id. Qed.

(** [C ⊸ (g ∘ f) = (C ⊸ g) ∘ (C ⊸ f)]. *)
Lemma linhom_post_comp (D1 D2 D3 : ICone.type Ar)
    (f : icones_hom Ar D1 D2) (g : icones_hom Ar D2 D3) :
  linhom_post_icones (C := C) (icones_comp g f) =
  icones_comp (linhom_post_icones (C := C) g) (linhom_post_icones (C := C) f).
Proof.
rewrite /linhom_post_icones.
have := linhom_map_icones_comp (icones_id Ar C) (icones_id Ar C) f g.
by rewrite icones_compIl => ->.
Qed.

End LinhomPostFunctor.

(** [C ⊸ −] preserves monos: if [h] is injective so is
    [linhom_post_icones h].  Pointwise, [(C ⊸ h) f = h ∘ f], so
    [h ∘ f₁ = h ∘ f₂] gives [f₁ = f₂] by injectivity of [h] and
    [linhom_eq].  (Placed early: the [tensor_sig] instantiation below
    consumes it.) *)
Lemma linhom_post_inj (R : realType) (Ar : MeasSubcat R)
    (C D1 D2 : ICone.type Ar) (h : icones_hom Ar D1 D2) :
  is_icones_inj h -> is_icones_inj (linhom_post_icones (C := C) h).
Proof.
move=> hinj f1 f2 /(congr1 (fun w : linhom_car Ar C D2 => linhom_fun w)) /= Hf.
apply: linhom_eq => x; apply: hinj.
by have := f_equal (fun w => w x) Hf.
Qed.

Arguments linhom_post_inj {R Ar C D1 D2} h.

(** ** The SAFT signature of the right functor [(C ⊸ −)]

    The generalised-element functor of the tensor instantiation:
    [tensor_ehom X := ICones(B, C ⊸ X)] with hom-action
    [tensor_emap h := (C ⊸ h) ∘ −].  Products are preserved through the
    Thm 5.9 iso [limpl_preserves_prod] ([tensor_etuple]); equalisers
    through the co-restriction [limpl_eq_med_icones].  [tensor_sig]
    packages these as an [SC.saft_sig], against which the shared SAFT
    engine of [saft_construct.v] delivers the construction. *)

Section TensorSig.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : ICone.type Ar.

Definition tensor_ehom (X : ICone.type Ar) : Type :=
  icones_hom Ar B (linhom_car Ar C X).

Definition tensor_emap (X Y : ICone.type Ar) (h : icones_hom Ar X Y)
    (g : tensor_ehom X) : tensor_ehom Y :=
  icones_comp (linhom_post_icones (C := C) h) g.

Lemma tensor_emap_id (X : ICone.type Ar) (g : tensor_ehom X) :
  tensor_emap (icones_id Ar X) g = g.
Proof. by rewrite /tensor_emap linhom_post_id icones_compIl. Qed.

Lemma tensor_emap_comp (X Y Z : ICone.type Ar)
    (h1 : icones_hom Ar X Y) (h2 : icones_hom Ar Y Z) (g : tensor_ehom X) :
  tensor_emap (icones_comp h2 h1) g = tensor_emap h2 (tensor_emap h1 g).
Proof. by rewrite /tensor_emap linhom_post_comp -icones_compA. Qed.

Lemma tensor_emap_mono (X Y : ICone.type Ar) (h : icones_hom Ar X Y) :
  is_icones_inj h ->
  forall u v : tensor_ehom X, tensor_emap h u = tensor_emap h v -> u = v.
Proof.
move=> hinj u v.
exact: (icones_inj_mono _ (linhom_post_inj (C := C) h hinj) B u v).
Qed.

Definition tensor_etuple (K : Type) (X : K -> ICone.type Ar)
    (g : forall k, tensor_ehom (X k)) : tensor_ehom (icones_prod X) :=
  icones_comp (iso_bwd (limpl_preserves_prod C X)) (icones_tuple g).

Lemma tensor_etuple_proj (K : Type) (X : K -> ICone.type Ar)
    (g : forall k, tensor_ehom (X k)) (k : K) :
  tensor_emap (icones_proj k) (tensor_etuple g) = g k.
Proof.
apply: icones_hom_eq => b /=.
apply: linhom_eq => c.
by rewrite linhom_map_funE /=.
Qed.

(** Joint monicity of the [(C ⊸ π_k)]: two elements of [C ⊸ ∏ X_k] with
    equal projections are equal (pointwise, componentwise). *)
Lemma tensor_eprod_ext (K : Type) (X : K -> ICone.type Ar)
    (a b : tensor_ehom (icones_prod X)) :
  (forall k, tensor_emap (icones_proj k) a = tensor_emap (icones_proj k) b) ->
  a = b.
Proof.
move=> Hab.
apply: icones_hom_eq => x; apply: linhom_eq => c.
apply: cones_prod_eq => k.
have := congr1 (fun w : tensor_ehom (X k) =>
                  linhom_fun ((w : icones_hom _ _ _) x) c) (Hab k).
by rewrite /tensor_emap /= !linhom_map_funE /=.
Qed.

(** The packaged signature. *)
Definition tensor_sig : SC.saft_sig Ar :=
  @SC.MkSaftSig R Ar tensor_ehom tensor_emap tensor_emap_id tensor_emap_comp
    tensor_emap_mono tensor_etuple tensor_etuple_proj tensor_eprod_ext
    (fun X Y u v g H => limpl_eq_med_icones C g H)
    (fun X Y u v g H => limpl_eq_med_factor C g H).

End TensorSig.

(** ** The coseparator power and the universal map [e_B]

    Fix [B], [C].  The coseparator is [1 := cone_one_car Ar].  The
    index type [J := ICones(B, C ⊸ 1)] is the homset of [C ⊸ 1]; the
    power is [p := 1^J = icones_prod (fun _ : J => 1)].

    The universal map [e_B : B → C ⊸ p] is, transported through Thm 5.9
    ([limpl_preserves_prod]), the tuple of all elements of [J]:
      [e_B := iso_bwd (limpl_preserves_prod C _) ∘ ⟨ j ⟩_{j ∈ J}]. *)

Section UniversalMap.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : ICone.type Ar.

Local Notation Cone1 := (cone_one_car Ar).

(** The index type [J = ICones(B, C ⊸ 1)]. *)
Definition tJ : Type := icones_hom Ar B (linhom_car Ar C Cone1).

(** The constant family at [1] and the coseparator power [p = 1^J]. *)
Definition tpfam (_ : tJ) : ICone.type Ar := Cone1.
Definition tp : ICone.type Ar := icones_prod tpfam.

(** Thm 5.9 iso [C ⊸ p ≅ ∏_J (C ⊸ 1)]. *)
Local Notation isoP := (limpl_preserves_prod C tpfam).

(** The tuple of all [J]-elements [⟨ j ⟩_{j ∈ J} : B → ∏_J (C ⊸ 1)]. *)
Definition tJtuple :
    icones_hom Ar B (icones_prod (fun j => linhom_car Ar C (tpfam j))) :=
  icones_tuple (B := fun j => linhom_car Ar C (tpfam j)) (fun j : tJ => j).

(** The universal map [e_B : B → C ⊸ p]. *)
Definition eB : icones_hom Ar B (linhom_car Ar C tp) :=
  icones_comp (iso_bwd isoP) tJtuple.

End UniversalMap.

Arguments tJ {R Ar} B C.
Arguments tp {R Ar} B C.
Arguments eB {R Ar} B C.

(** ** The factoring family and the tensor object [B ⊗ C]

    A member of the family is a subobject-like datum: a domain [fs_dom],
    an embedding [fs_hom : fs_dom → p], and a *factoring witness*
    [fs_eA : B → C ⊸ fs_dom] with [(C ⊸ fs_hom) ∘ fs_eA = e_B].  In
    Rocq's predicative type theory this family is just a [Type]; the
    paper's well-poweredness ([icones_well_powered], [representable.v])
    is what guarantees it is a *set* — automatic here — so the wide
    intersection [wi_obj] applies directly.

    The basepoint [k0] is the identity subobject [(p, id_p, e_B)], which
    factors [e_B] trivially ([(C ⊸ id) ∘ e_B = e_B]).

    [tensor B C := wi_obj] over this family.  The family record, the
    classifier reindexing and the intersection are the shared skeleton's
    ([SC.fsub]/[SC.fpick]/[SC.fAdom]/…, instantiated at [tensor_sig]);
    this section re-exports them under the historical names. *)

Section TensorObject.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : ICone.type Ar.

Local Notation p := (tp B C).
Local Notation Tsig := (tensor_sig B C).

(** The factoring family of subobjects of [p = 1^J] (the skeleton's
    [SC.fsub] at [tensor_sig]): a domain, an *injective* embedding into
    [p] (a subobject, [SA1] of [representable.v]), and a *factoring
    witness* of [e_B] through [C ⊸ −] applied to that embedding. *)
Definition fsub : Type := @SC.fsub R Ar Tsig.

Definition fs_dom (k : fsub) : ICone.type Ar := @SC.fs_dom R Ar Tsig k.
Definition fs_hom (k : fsub) : icones_hom Ar (fs_dom k) p :=
  @SC.fs_hom R Ar Tsig k.
Definition fs_inj (k : fsub) : is_icones_inj (fs_hom k) :=
  @SC.fs_inj R Ar Tsig k.
Definition fs_eA (k : fsub) : icones_hom Ar B (linhom_car Ar C (fs_dom k)) :=
  @SC.fs_eA R Ar Tsig k.
Definition fs_fact (k : fsub) :
    icones_comp (linhom_post_icones (C := C) (fs_hom k)) (fs_eA k) = eB B C :=
  @SC.fs_fact R Ar Tsig k.

(** The underlying subobject of a family member. *)
Definition fs_sub (k : fsub) : icones_subobject p := @SC.fs_sub R Ar Tsig k.

(** A family member's embedding is a mono. *)
Definition fs_hom_inj (k : fsub) : is_icones_inj (fs_hom k) :=
  @SC.fs_hom_inj R Ar Tsig k.

(** The basepoint subobject [(p, id_p, e_B)], which factors [e_B]
    trivially ([C ⊸ id = id]) and is a mono ([id] is injective). *)
Lemma fk0_fact :
  icones_comp (linhom_post_icones (C := C) (icones_id Ar p)) (eB B C) = eB B C.
Proof. by rewrite linhom_post_id icones_compIl. Qed.

Lemma fk0_inj : is_icones_inj (icones_id Ar p).
Proof. by move=> x y. Qed.

Definition fbase : fsub := @SC.fbase R Ar Tsig.

(** *** The small index — well-poweredness

    The family is indexed by the *small* subobject classifier
    [SubobjClassifier p] ([representable.v], well-poweredness Thm 4.18),
    NOT by the proper-class record [fsub] (which packs an
    [ICone.type Ar] and is therefore too large to index the wide
    intersection [wi_obj], whose index [K : Type] lives below the cone
    universe — a hard universe constraint in the frozen [representable.v]).

    For each classifier value [s] we *choose* (classically,
    [pselect]/[cid]) a factoring subobject whose classifier is [s],
    defaulting to the basepoint [fbase] when none exists ([SC.fpick]). *)
Definition fK : Type := SubobjClassifier p.

(** A chosen factoring subobject with classifier value [s] (or [fbase]).
    Every value of [fpick] is a genuine [fsub], hence factors [e_B]. *)
Definition fpick (s : fK) : fsub := @SC.fpick R Ar Tsig s.

(** The family data fed to [wi_obj]: domains and embeddings of the
    chosen representatives. *)
Definition fAdom (s : fK) : ICone.type Ar := fs_dom (fpick s).
Definition fhh (s : fK) : icones_hom Ar (fAdom s) p := fs_hom (fpick s).

(** Each chosen representative's embedding is a mono. *)
Definition fhh_inj (s : fK) : is_icones_inj (fhh s) :=
  @SC.fhh_inj R Ar Tsig s.

(** The basepoint index: the classifier value of [fbase]. *)
Definition fk0 : fK := icones_subobject_class (fs_sub fbase).

(** The tensor object [B ⊗ C] as the wide intersection of the family. *)
Definition tensor : ICone.type Ar := wi_obj fhh fk0.

(** The intersection embedding [B ⊗ C ↪ p]. *)
Definition tensor_incl : icones_hom Ar tensor p := wi_incl fAdom fhh fk0.

(** Each chosen representative factors [e_B] through [C ⊸ (its
    embedding)]: [(C ⊸ fhh s) ∘ fs_eA (fpick s) = e_B]. *)
Lemma fpick_fact (s : fK) :
  icones_comp (linhom_post_icones (C := C) (fhh s)) (fs_eA (fpick s)) = eB B C.
Proof. exact: (@SC.fpick_fact R Ar Tsig s). Qed.

(** *** Pointwise value of [e_B] and of the tuple of factoring witnesses

    [e_B b c . j = j b c] (the [j]-th component of [e_B b c ∈ p = 1^J] is
    [j] applied to [b] then evaluated at [c]). *)

(** [tJtuple]'s [j]-component is [j] itself: [tJtuple b . j = j b]. *)
Lemma tJtupleE (b : B) (j : tJ B C) :
  cones_prod_val ((tJtuple B C : icones_hom _ _ _) b) j = (j : icones_hom _ _ _) b.
Proof.
have := icones_tuple_proj (B := fun j0 : tJ B C => linhom_car Ar C (tpfam j0))
          (fun j0 : tJ B C => j0) j.
by move/(congr1 (fun w : icones_hom Ar B (linhom_car Ar C (tpfam j)) =>
                   (w : icones_hom _ _ _) b)).
Qed.

(** Pointwise value of [e_B]: [e_B b c . j = j b c]. *)
Lemma eBE (b : B) (c : C) (j : tJ B C) :
  cones_prod_val (linhom_fun ((eB B C : icones_hom _ _ _) b) c) j =
  linhom_fun ((j : icones_hom _ _ _) b) c.
Proof. by rewrite /eB /=. Qed.

End TensorObject.

Arguments tJtupleE {R Ar B C}.
Arguments eBE {R Ar B C}.
Arguments fsub {R Ar} B C.
Arguments fs_dom {R Ar B C} k.
Arguments fs_hom {R Ar B C} k.
Arguments fs_inj {R Ar B C} k.
Arguments fs_eA {R Ar B C} k.
Arguments fs_fact {R Ar B C} k.
Arguments fK {R Ar B C}.
Arguments fAdom {R Ar B C}.
Arguments fhh {R Ar B C}.
Arguments fhh_inj {R Ar B C}.
Arguments fk0 {R Ar B C}.
Arguments fs_sub {R Ar B C}.
Arguments fs_hom_inj {R Ar B C}.
Arguments fpick {R Ar B C}.
Arguments fpick_fact {R Ar B C}.
Arguments tensor {R Ar} B C.
Arguments tensor_incl {R Ar} B C.

(** ** Intersection minimality: [tensor_incl] factors through every
       family member

    The SAFT "initial object of the comma category" content (Riehl
    4.6.11): for any factoring-family member [k : fsub B C] — a subobject
    [(fs_dom k, fs_hom k)] of [p] through which [eB] factors — the
    intersection embedding [tensor_incl] factors through its embedding,
    [fs_hom k ∘ r = tensor_incl] for some [r : B ⊗ C → fs_dom k].
    Delivered by the skeleton's classifier transport
    ([SC.ff_factor]/[SC.ff_factorP]). *)

Section FsubFactors.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : ICone.type Ar.

Local Notation p := (tp B C).
Local Notation Tsig := (tensor_sig B C).

Variable k : fsub B C.

(** The classifier of [k]'s subobject. *)
Definition ff_class : @fK R Ar B C := icones_subobject_class (fs_sub k).

(** The two subobjects of [p]: the chosen representative of [ff_class]
    and [k]'s own embedding. *)
Local Notation SubA :=
  (@MkSubobject R Ar p (fAdom ff_class) (fhh ff_class) (fhh_inj ff_class)).
Local Notation SubK :=
  (@MkSubobject R Ar p (fs_dom k) (fs_hom k) (fs_hom_inj k)).

(** [SubA] has classifier [ff_class]: a witness ([k]) exists, so [fpick
    ff_class] picks a subobject with classifier [ff_class]. *)
Lemma ff_SubA_class : icones_subobject_class SubA = ff_class.
Proof. exact: (@SC.ff_SubA_class R Ar Tsig k). Qed.

(** [SubK] is literally [fs_sub k], so it has classifier [ff_class] by
    definition; [SubA] too by [ff_SubA_class].  Hence they are iso over
    [p]. *)
Lemma ff_equiv : subobject_equiv SubA SubK.
Proof. exact: (@SC.ff_equiv R Ar Tsig k). Qed.

(** The iso [φ : fAdom ff_class ≅ fs_dom k] over [p]. *)
Definition ff_phi : icones_iso Ar (fAdom ff_class) (fs_dom k) :=
  @SC.ff_phi R Ar Tsig k.

Lemma ff_phiE (z : fAdom ff_class) :
  (fs_hom k : icones_hom _ _ _) ((iso_fwd ff_phi : icones_hom _ _ _) z) =
  (fhh ff_class : icones_hom _ _ _) z.
Proof. exact: (@SC.ff_phiE R Ar Tsig k z). Qed.

(** The factor [B ⊗ C → fs_dom k]. *)
Definition ff_factor : icones_hom Ar (tensor B C) (fs_dom k) :=
  icones_comp (iso_fwd ff_phi) (wi_proj fAdom fhh fk0 ff_class).

(** [fs_hom k ∘ ff_factor = tensor_incl]. *)
Lemma ff_factorP :
  icones_comp (fs_hom k) ff_factor = tensor_incl B C.
Proof. exact: (@SC.ff_factorP R Ar Tsig k). Qed.

End FsubFactors.

Arguments ff_factor {R Ar B C} k.
Arguments ff_factorP {R Ar B C} k.

(** ** The universal element [tau' : B → C ⊸ (B ⊗ C)]

    [B ⊗ C = wi_obj] is, by construction ([representable.v]), the
    equaliser [icones_eq (wi_u fhh) (wi_v fhh fk0)] of two maps
    [wi_prod fAdom → wi_pprod].  Since [C ⊸ −] preserves this equaliser
    ([limpl_eq_med] of [limpl_continuous.v]), we co-restrict the
    universal map [e_prod : B → C ⊸ wi_prod] — the inverse-transported
    tuple of the factoring witnesses — through [C ⊸ (eq inclusion)],
    obtaining [tau'].  Its defining factorisation
    [(C ⊸ wi_incl) ∘ tau' = e_B] then follows from [fpick_fact].
    ([SC.saft_eprod_equ]/[SC.saft_tau]/[SC.saft_tau_def].) *)

Section Tau.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : ICone.type Ar.

Local Notation p := (tp B C).
Local Notation Tsig := (tensor_sig B C).
Local Notation K := (@fK R Ar B C).
Local Notation Adom := (@fAdom R Ar B C).
Local Notation hh := (@fhh R Ar B C).
Local Notation k0 := (@fk0 R Ar B C).

(** The product of the family domains [wi_prod fAdom = ∏_s fAdom s]. *)
Local Notation Wprod := (wi_prod Adom).

(** The two parallel maps whose equaliser is [B ⊗ C]. *)
Local Notation WU := (wi_u hh).
Local Notation WV := (wi_v hh k0).

(** [B ⊗ C] is the equaliser of [WU], [WV] (definitionally). *)
Lemma tensorE : tensor B C = icones_eq WU WV.
Proof. by []. Qed.

(** The tuple of factoring witnesses [⟨ fs_eA (fpick s) ⟩_s :
    B → ∏_s (C ⊸ fAdom s)]. *)
Definition eAtuple :
    icones_hom Ar B (icones_prod (fun s : K => linhom_car Ar C (Adom s))) :=
  icones_tuple (B := fun s : K => linhom_car Ar C (Adom s))
    (fun s : K => fs_eA (fpick s)).

(** The universal map [e_prod : B → C ⊸ wi_prod], the factoring tuple
    transported back through Thm 5.9 ([limpl_preserves_prod]). *)
Definition eprod : icones_hom Ar B (linhom_car Ar C Wprod) :=
  icones_comp (iso_bwd (limpl_preserves_prod C Adom)) eAtuple.

(** Pointwise component value of [e_prod]:
    [e_prod b c . s = fs_eA (fpick s) b c]. *)
Lemma eprodE (b : B) (c : C) (s : K) :
  cones_prod_val (linhom_fun ((eprod : icones_hom _ _ _) b) c) s =
  linhom_fun ((fs_eA (fpick s) : icones_hom _ _ _) b) c.
Proof. by rewrite /eprod /=. Qed.

(** Pointwise component of [WU] / [WV] (the two product maps).
    [WU x . k = hh k (x . k)] and [WV x . k = hh k0 (x . k0)]. *)
Lemma WUE (x : Wprod) (k : K) :
  cones_prod_val ((WU : icones_hom _ _ _) x) k =
  (hh k : icones_hom _ _ _) (cones_prod_val x k).
Proof.
have := icones_tuple_proj (Q := Wprod)
          (fun k0 => icones_comp (hh k0) (wi_pi Adom k0)) k.
by move/(congr1 (fun w : icones_hom Ar Wprod p => (w : icones_hom _ _ _) x)) => /= ->.
Qed.

Lemma WVE (x : Wprod) (k : K) :
  cones_prod_val ((WV : icones_hom _ _ _) x) k =
  (hh k0 : icones_hom _ _ _) (cones_prod_val x k0).
Proof.
have := icones_tuple_proj (Q := Wprod)
          (fun _ : K => icones_comp (hh k0) (wi_pi Adom k0)) k.
by move/(congr1 (fun w : icones_hom Ar Wprod p => (w : icones_hom _ _ _) x)) => /= ->.
Qed.

(** The factoring witness, evaluated pointwise:
    [hh s (fs_eA (fpick s) b c) = e_B b c]. *)
Lemma fpick_factE (b : B) (c : C) (s : K) :
  (hh s : icones_hom _ _ _) (linhom_fun ((fs_eA (fpick s) : icones_hom _ _ _) b) c) =
  linhom_fun ((eB B C : icones_hom _ _ _) b) c.
Proof.
have := fpick_fact s.
move/(congr1 (fun w : icones_hom Ar B (linhom_car Ar C p) =>
                (w : icones_hom _ _ _) b)).
move/(congr1 (fun f : linhom_car Ar C p => linhom_fun f c)).
by rewrite /= linhom_map_funE /=.
Qed.

(** The equalising condition: [e_prod] equalises [C ⊸ WU] and [C ⊸ WV]
    ([SC.saft_eprod_equ], proved categorically in the skeleton). *)
Lemma eprod_equ :
  icones_comp (linhom_post_icones (C := C) WU) eprod =
  icones_comp (linhom_post_icones (C := C) WV) eprod.
Proof. exact: (@SC.saft_eprod_equ R Ar Tsig). Qed.

(** *** [tau'] by co-restriction through [C ⊸ (eq inclusion)]

    [B ⊗ C = icones_eq WU WV], and [C ⊸ −] preserves this equaliser, so
    [e_prod] (equalising [C ⊸ WU], [C ⊸ WV]) co-restricts uniquely
    ([SC.saft_tau]). *)

Definition tau' : icones_hom Ar B (linhom_car Ar C (tensor B C)) :=
  @SC.saft_tau R Ar Tsig.

(** Factorisation through the equaliser inclusion:
    [(C ⊸ eq_incl) ∘ tau' = e_prod]. *)
Lemma tau'_eq_incl :
  icones_comp (linhom_post_icones (C := C) (icones_eq_incl WU WV)) tau' = eprod.
Proof. exact: (@SC.saft_tau_eq_incl R Ar Tsig). Qed.

(** The DEFINING factorisation of the universal element:
    [(C ⊸ wi_incl) ∘ tau' = e_B].  This is Paper Eq 5.1's universal
    property of [tau'] ([SC.saft_tau_def]). *)
Lemma tau'_def :
  icones_comp (linhom_post_icones (C := C) (tensor_incl B C)) tau' = eB B C.
Proof. exact: (@SC.saft_tau_def R Ar Tsig). Qed.

End Tau.

Arguments tau' {R Ar} B C.
Arguments tau'_def {R Ar B C}.

(** ** The intersection embedding [tensor_incl] is a monomorphism

    [tensor B C = icones_eq WU WV] and [tensor_incl = (hh k0 ∘ π_{k0}) ∘
    eq_incl].  Two points of the intersection are equal iff their
    underlying tuples agree componentwise; the equaliser constraint plus
    [tensor_incl x = tensor_incl y] force [hh k (val x . k) =
    hh k (val y . k)] for every [k], whence componentwise equality by
    [fhh_inj k].  Unlike the generic [wi_incl_inj] (which would need the
    single projection [wi_proj k0] injective — false here), this uses that
    *every* family member [fhh k] is a mono ([SC.saft_incl_inj]). *)

Section TensorInclInj.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : ICone.type Ar.

Local Notation p := (tp B C).
Local Notation Tsig := (tensor_sig B C).
Local Notation K := (@fK R Ar B C).
Local Notation hh := (@fhh R Ar B C).
Local Notation k0 := (@fk0 R Ar B C).
Local Notation WU := (wi_u hh).
Local Notation WV := (wi_v hh k0).

(** Componentwise value of the two product maps (re-derived here, the
    [Tau]-section [WUE]/[WVE] being local to it). *)
Lemma WUE' (x : wi_prod (@fAdom R Ar B C)) (k : K) :
  cones_prod_val ((WU : icones_hom _ _ _) x) k =
  (hh k : icones_hom _ _ _) (cones_prod_val x k).
Proof.
have := icones_tuple_proj (Q := wi_prod (@fAdom R Ar B C))
          (fun k1 => icones_comp (hh k1) (wi_pi (@fAdom R Ar B C) k1)) k.
by move/(congr1 (fun w : icones_hom Ar (wi_prod (@fAdom R Ar B C)) p =>
                   (w : icones_hom _ _ _) x)) => /= ->.
Qed.

Lemma WVE' (x : wi_prod (@fAdom R Ar B C)) (k : K) :
  cones_prod_val ((WV : icones_hom _ _ _) x) k =
  (hh k0 : icones_hom _ _ _) (cones_prod_val x k0).
Proof.
have := icones_tuple_proj (Q := wi_prod (@fAdom R Ar B C))
          (fun _ : K => icones_comp (hh k0) (wi_pi (@fAdom R Ar B C) k0)) k.
by move/(congr1 (fun w : icones_hom Ar (wi_prod (@fAdom R Ar B C)) p =>
                   (w : icones_hom _ _ _) x)) => /= ->.
Qed.

(** [tensor_incl] is a mono ([SC.saft_incl_inj]). *)
Lemma tensor_incl_inj : is_icones_inj (tensor_incl B C).
Proof. exact: (@SC.saft_incl_inj R Ar Tsig). Qed.

End TensorInclInj.

Arguments tensor_incl_inj {R Ar} B C.

(** ** [tensor_curry] and the naturalities not needing [tensor_uncurry]

    [tensor_curry f := (C ⊸ f) ∘ tau'] is the forward hom-map
    [ICones(B ⊗ C, D) → ICones(B, C ⊸ D)] (Paper Thm 5.9 / Eq 5.1).
    Two of its naturalities follow from the functoriality of [C ⊸ −]
    ([linhom_post_comp]) alone, without the inverse [tensor_uncurry]. *)

Section TensorCurry.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : ICone.type Ar.

(** Paper Eq 5.1: the forward currying map. *)
Definition tensor_curry (D : ICone.type Ar) (f : icones_hom Ar (tensor B C) D) :
    icones_hom Ar B (linhom_car Ar C D) :=
  icones_comp (linhom_post_icones (C := C) f) (tau' B C).

(** Naturality of [Φ] in [D] (concrete form, Paper Thm 5.9):
    [Φ (h ∘ f) = (C ⊸ h) ∘ Φ f].  By [linhom_post_comp]
    ([C ⊸ (h ∘ f) = (C ⊸ h) ∘ (C ⊸ f)]) composed with [tau']. *)
Lemma tensor_curry_natural_post (D D' : ICone.type Ar)
    (h : icones_hom Ar D D') (f : icones_hom Ar (tensor B C) D) :
  tensor_curry (icones_comp h f) =
  icones_comp (linhom_post_icones (C := C) h) (tensor_curry f).
Proof.
by rewrite /tensor_curry linhom_post_comp -icones_compA.
Qed.

(** Paper Eq 5.1, pointwise: [Φ(f)(x)(y) = f(τ'(x)(y))].  Direct from
    the definition [tensor_curry f = (C ⊸ f) ∘ tau']. *)
Lemma tensor_curryE (D : ICone.type Ar) (f : icones_hom Ar (tensor B C) D)
    (x : B) (y : C) :
  linhom_fun ((tensor_curry f : icones_hom _ _ _) x) y =
  (f : icones_hom _ _ _) (linhom_fun ((tau' B C : icones_hom _ _ _) x) y).
Proof. by rewrite /tensor_curry /= linhom_map_funE /=. Qed.

(** Naturality of [Φ] in [D] (existential form): the witness is
    [C ⊸ h = linhom_post_icones h]. *)
Lemma tensor_curry_natural_D (D D' : ICone.type Ar)
    (h : icones_hom Ar D D') :
  exists hstar : icones_hom Ar (linhom_car Ar C D) (linhom_car Ar C D'),
    forall f : icones_hom Ar (tensor B C) D,
      tensor_curry (icones_comp h f) = icones_comp hstar (tensor_curry f).
Proof.
exists (linhom_post_icones (C := C) h) => f.
exact: tensor_curry_natural_post.
Qed.

End TensorCurry.

Arguments tensor_curry {R Ar B C D}.
Arguments tensor_curryE {R Ar B C D}.
Arguments tensor_curry_natural_post {R Ar B C D D'}.
Arguments tensor_curry_natural_D {R Ar B C D D'}.

(** ** [tensor_uncurry] — the SAFT comma-category mediator (Riehl 4.6.11)

    Given [g : B → C ⊸ D], we build the unique [tensor_uncurry g :
    B ⊗ C → D] with [(C ⊸ uncurry g) ∘ tau' = g] by the
    coseparator-power reindexing of PLAN §13.2 — the skeleton's
    [SC.saft_uncurry] at [tensor_sig].

    Write [1 = cone_one_car Ar].  Form the coseparator power of [D],
    [q D := 1^{ICones(D,1)}], with its canonical mono
    [GammaD : D ↪ q D] ([GammaD d . n = n d], a mono since [1]
    cogenerates — [icones_coseparator_inj]).  Reindex the
    power [p = 1^J] of [B ⊗ C] to [q D] along
    [θ : ICones(D,1) → J, n ↦ (C ⊸ n) ∘ g], giving [P : p → q D] with
    [P x . n = x . (θ n)].  The square
    [(C ⊸ P) ∘ eB = (C ⊸ GammaD) ∘ g] commutes — this is the pullback
    datum.

    Pull [GammaD] back along [P]: [Dsub := pb_obj P GammaD] (the
    equaliser [{(x,d) | P x = GammaD d}]), with embedding [pb_incl :
    Dsub → p] and projection [pb_proj2 : Dsub → D].  The square lets
    [eB], [g] co-restrict (through [C ⊸ −], which preserves the
    pullback equaliser) to [eA : B → C ⊸ Dsub] with
    [(C ⊸ pb_incl) ∘ eA = eB] — so [(Dsub, pb_incl, eA)] is a member
    of the factoring family.  Hence the intersection embedding
    [tensor_incl] factors through it; the [D]-leg of that factor is the
    point map of [tensor_uncurry g]. *)

Section TensorUncurry.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C D : ICone.type Ar.

Local Notation Cone1 := (cone_one_car Ar).
Local Notation p := (tp B C).
Local Notation Tsig := (tensor_sig B C).

Variable g : icones_hom Ar B (linhom_car Ar C D).

(** The index of [q D]: the homset [ICones(D, 1)]. *)
Definition tN : Type := icones_hom Ar D Cone1.

(** The coseparator power [q D = 1^{ICones(D,1)}]. *)
Definition tqfam (_ : tN) : ICone.type Ar := Cone1.
Definition tq : ICone.type Ar := icones_prod tqfam.

(** The canonical mono [GammaD : D → q D], [GammaD d . n = n d]. *)
Definition GammaD : icones_hom Ar D tq :=
  icones_tuple (B := tqfam) (fun n : tN => n).

Lemma GammaDE (d : D) (n : tN) :
  cones_prod_val ((GammaD : icones_hom _ _ _) d) n = (n : icones_hom _ _ _) d.
Proof.
have := icones_tuple_proj (B := tqfam) (fun n0 : tN => n0) n.
by move/(congr1 (fun w : icones_hom Ar D Cone1 => (w : icones_hom _ _ _) d)).
Qed.

(** [GammaD] is a mono ([1] cogenerates). *)
Lemma GammaD_inj : is_icones_inj GammaD.
Proof.
move=> x y /(congr1 (fun z : tq => cones_prod_val z)) /= Hxy.
apply: icones_coseparator_inj => n.
by have := f_equal (fun w => w n) Hxy.
Qed.

(** The reindexing map [θ : ICones(D,1) → J = ICones(B, C ⊸ 1)],
    [θ n = (C ⊸ n) ∘ g]. *)
Definition tθ (n : tN) : tJ B C :=
  icones_comp (linhom_post_icones (C := C) n) g.

(** The reindex projection [P : p → q D], [P x . n = x . (θ n)]. *)
Definition tP : icones_hom Ar p tq :=
  icones_tuple (B := tqfam) (fun n : tN => icones_proj (tθ n)).

Lemma tPE (x : p) (n : tN) :
  cones_prod_val ((tP : icones_hom _ _ _) x) n = cones_prod_val x (tθ n).
Proof. by []. Qed.

(** The pullback datum — the commuting square
    [(C ⊸ P) ∘ eB = (C ⊸ GammaD) ∘ g] ([SC.saft_P_square]). *)
Lemma tP_square :
  icones_comp (linhom_post_icones (C := C) tP) (eB B C) =
  icones_comp (linhom_post_icones (C := C) GammaD) g.
Proof. exact: (@SC.saft_P_square R Ar Tsig D g). Qed.

(** *** The pullback [Dsub = pb_obj P GammaD] and its [p]-subobject *)

Local Notation Dsub := (pb_obj tP GammaD).

(** [Dsub ↪ p] is [pb_proj1] (the [p]-leg of the pullback of the mono
    [GammaD]); [pb_proj2 : Dsub → D] is the other leg. *)
Local Notation Dincl := (pb_proj1 tP GammaD).
Local Notation Dpr := (pb_proj2 tP GammaD).

(** [Dincl] is a mono ([SC.saft_Gincl_inj]). *)
Lemma Dincl_inj : is_icones_inj Dincl.
Proof. exact: (@SC.saft_Gincl_inj R Ar Tsig D g). Qed.

(** *** Co-restricting [eB] and [g] to [C ⊸ Dsub]

    [Dsub] is the equaliser of [pb_left = P ∘ π₁] and
    [pb_right = GammaD ∘ π₂] on [pb_prod = p ×_bool D].  As [C ⊸ −]
    preserves it, the map [eAprod : B → C ⊸ pb_prod] tupling [eB]
    (at [true]) and [g] (at [false]) — built through
    [limpl_preserves_prod] — co-restricts to [eA : B → C ⊸ Dsub]. *)

(** The [bool]-family tuple [⟨ eB, g ⟩ : B → ∏_b (C ⊸ pb_fam b)]. *)
Definition eAtupfam (b : bool) :
    icones_hom Ar B (linhom_car Ar C (pb_fam p D b)) :=
  if b as b' return icones_hom Ar B (linhom_car Ar C (pb_fam p D b'))
  then eB B C else g.

Definition eAtup :
    icones_hom Ar B (icones_prod (fun b => linhom_car Ar C (pb_fam p D b))) :=
  icones_tuple (B := fun b => linhom_car Ar C (pb_fam p D b)) eAtupfam.

(** Transport back to [C ⊸ pb_prod] through Thm 5.9. *)
Definition eAprod : icones_hom Ar B (linhom_car Ar C (pb_prod p D)) :=
  icones_comp (iso_bwd (limpl_preserves_prod C (pb_fam p D))) eAtup.

(** [(C ⊸ π_b) ∘ eAprod = eAtupfam b]: the [true]/[false] components
    of [eAprod] are [eB] / [g]. *)
Lemma eAprod_pi (b' : bool) :
  icones_comp (linhom_post_icones (C := C) (icones_proj (B := pb_fam p D) b'))
              eAprod = eAtupfam b'.
Proof.
apply: icones_hom_eq => b /=.
apply: linhom_eq => c.
by rewrite linhom_map_funE /=.
Qed.

(** [eAprod] equalises [C ⊸ pb_left] and [C ⊸ pb_right]
    ([SC.saft_gprod_equ]). *)
Lemma eAprod_equ :
  icones_comp (linhom_post_icones (C := C) (pb_left D tP)) eAprod =
  icones_comp (linhom_post_icones (C := C) (pb_right p GammaD)) eAprod.
Proof. exact: (@SC.saft_gprod_equ R Ar Tsig D g). Qed.

(** The co-restriction [eA : B → C ⊸ Dsub] ([SC.saft_gA]). *)
Definition eA : icones_hom Ar B (linhom_car Ar C Dsub) :=
  @SC.saft_gA R Ar Tsig D g.

(** [(C ⊸ eq_incl) ∘ eA = eAprod]. *)
Lemma eA_eq_incl :
  icones_comp (linhom_post_icones (C := C)
                 (icones_eq_incl (pb_left D tP) (pb_right p GammaD))) eA =
  eAprod.
Proof. exact: (@SC.saft_gA_eq_incl R Ar Tsig D g). Qed.

(** The factoring witness of the family member [(Dsub, Dincl, eA)]:
    [(C ⊸ Dincl) ∘ eA = eB]. *)
Lemma eA_fact :
  icones_comp (linhom_post_icones (C := C) Dincl) eA = eB B C.
Proof. exact: (@SC.saft_gA_fact R Ar Tsig D g). Qed.

(** The family member [(Dsub, Dincl, eA)] as an [fsub]
    ([SC.saft_gfsub]). *)
Definition Dfsub : fsub B C := @SC.saft_gfsub R Ar Tsig D g.

(** *** [tensor_uncurry g] via the intersection's factoring property

    Let [s := class(Dsub, Dincl)].  The chosen representative
    [fpick s] has the same classifier, hence is iso *over [p]* to
    [(Dsub, Dincl)] ([icones_subobject_classP]): an iso [φ : fAdom s ≅
    Dsub] with [Dincl ∘ φ = fhh s].  The intersection embedding
    [tensor_incl] factors through [fhh s] ([wi_factors_each]); composing
    with [φ] then [pb_proj2] gives the [D]-valued point map.  This is
    exactly [ff_factor]/[ff_factorP] at the member [Dfsub]. *)

Definition Ds : fK := icones_subobject_class (fs_sub Dfsub).

(** The subobjects (in [fs_dom]-projection form): the chosen
    representative [(fAdom Ds, fhh Ds)] and the pullback [(Dsub, Dincl)]. *)
Local Notation SubA :=
  (@MkSubobject R Ar p (fAdom Ds) (fhh Ds) (fhh_inj Ds)).
Local Notation SubDp :=
  (@MkSubobject R Ar p Dsub Dincl Dincl_inj).

(** Both have classifier [Ds] ([SC.ff_SubA_class] at [Dfsub]). *)
Lemma SubA_class : icones_subobject_class SubA = Ds.
Proof. exact: (@SC.ff_SubA_class R Ar Tsig Dfsub). Qed.

(** The two subobjects are iso *over [p]* ([SC.ff_equiv] at [Dfsub]). *)
Lemma Ds_equiv : subobject_equiv SubA SubDp.
Proof. exact: (@SC.ff_equiv R Ar Tsig Dfsub). Qed.

(** The iso [φ : fAdom Ds ≅ Dsub] over [p]
    ([Dincl ∘ iso_fwd φ = fhh Ds]). *)
Definition Dphi : icones_iso Ar (fAdom Ds) Dsub := @SC.ff_phi R Ar Tsig Dfsub.

Lemma DphiE (z : fAdom Ds) :
  (Dincl : icones_hom _ _ _) ((iso_fwd Dphi : icones_hom _ _ _) z) =
  (fhh Ds : icones_hom _ _ _) z.
Proof. exact: (@SC.ff_phiE R Ar Tsig Dfsub z). Qed.

(** The factor of [tensor_incl] through [Dincl]:
    [tensor B C → Dsub], [= iso_fwd φ ∘ wi_proj Ds]. *)
Definition tu_factor : icones_hom Ar (tensor B C) Dsub :=
  icones_comp (iso_fwd Dphi) (wi_proj fAdom fhh fk0 Ds).

(** [Dincl ∘ tu_factor = tensor_incl] ([SC.ff_factorP] at [Dfsub]). *)
Lemma tu_factorP :
  icones_comp Dincl tu_factor = tensor_incl B C.
Proof. exact: (@SC.ff_factorP R Ar Tsig Dfsub). Qed.

(** The SAFT mediator [tensor_uncurry g : B ⊗ C → D]. *)
Definition tensor_uncurry : icones_hom Ar (tensor B C) D :=
  icones_comp Dpr tu_factor.

(** The [D]-leg factoring witness: [(C ⊸ Dpr) ∘ eA = g]
    ([SC.saft_gA_pr_fact]). *)
Lemma eA_pr_fact :
  icones_comp (linhom_post_icones (C := C) Dpr) eA = g.
Proof. exact: (@SC.saft_gA_pr_fact R Ar Tsig D g). Qed.

(** *** [tensor_uncurryK] : [tensor_curry (tensor_uncurry g) = g]

    The defining factorisation ([SC.saft_uncurryK]): via [C ⊸ Dincl]
    mono, the transported element [(C ⊸ tu_factor) ∘ tau'] coincides
    with [eA], whence the round trip by [eA_pr_fact]. *)
Lemma tensor_uncurryK : tensor_curry tensor_uncurry = g.
Proof. exact: (@SC.saft_uncurryK R Ar Tsig D g). Qed.

End TensorUncurry.

Arguments tensor_uncurry {R Ar B C D}.
Arguments tensor_uncurryK {R Ar B C D}.

(** ** [tensor_curry] is injective, hence [tensor_curryK]

    The SAFT-uniqueness argument (equaliser of the two candidates +
    intersection minimality), NOT joint-epicness of [tau'] — the
    skeleton's [SC.sci_*] machinery at [tensor_sig].

    Let [f1 f2 : B ⊗ C → D] with [tensor_curry f1 = tensor_curry f2],
    i.e. [(C ⊸ f1) ∘ tau' = (C ⊸ f2) ∘ tau'].  Form the equaliser
    [E := icones_eq f1 f2] with inclusion [e := icones_eq_incl f1 f2]
    ([f1 ∘ e = f2 ∘ e], [e] a mono).  Since [C ⊸ −] preserves equalisers,
    [tau'] (equalising [C ⊸ f1], [C ⊸ f2]) co-restricts to
    [tauE : B → C ⊸ E] with [(C ⊸ e) ∘ tauE = tau'].

    The composite [m_E := tensor_incl ∘ e : E ↪ p] is a mono, and [eB]
    factors through [C ⊸ m_E]; so [(E, m_E, tauE)] is a factoring-family
    member.  By intersection minimality ([ff_factorP]) the embedding
    [tensor_incl] factors through [m_E]: [r : B ⊗ C → E] with
    [m_E ∘ r = tensor_incl]; as [tensor_incl] is a mono, [e ∘ r = id];
    so [e] is a split epi, and [f1 ∘ e = f2 ∘ e] gives [f1 = f2]. *)

Section TensorCurryInj.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C D : ICone.type Ar.

Local Notation Tsig := (tensor_sig B C).

Variables f1 f2 : icones_hom Ar (tensor B C) D.
Hypothesis Hcurry : tensor_curry f1 = tensor_curry f2.

Local Notation E := (icones_eq f1 f2).
Local Notation e := (icones_eq_incl f1 f2).

(** [tau'] equalises [C ⊸ f1] and [C ⊸ f2] — that is exactly the
    hypothesis [tensor_curry f1 = tensor_curry f2] unfolded. *)
Lemma tci_equ :
  icones_comp (linhom_post_icones (C := C) f1) (tau' B C) =
  icones_comp (linhom_post_icones (C := C) f2) (tau' B C).
Proof. exact: Hcurry. Qed.

(** The co-restriction [tauE : B → C ⊸ E] ([SC.sci_tauE]). *)
Definition tauE : icones_hom Ar B (linhom_car Ar C E) :=
  @SC.sci_tauE R Ar Tsig D f1 f2 Hcurry.

Lemma tauE_factor :
  icones_comp (linhom_post_icones (C := C) e) tauE = tau' B C.
Proof. exact: (@SC.sci_tauE_factor R Ar Tsig D f1 f2 Hcurry). Qed.

(** The composite embedding [m_E := tensor_incl ∘ e : E ↪ p]. *)
Definition tci_mE : icones_hom Ar E (tp B C) := icones_comp (tensor_incl B C) e.

(** [m_E] is a mono (composite of the injective [tensor_incl] and the
    injective equaliser inclusion [e]). *)
Lemma tci_mE_inj : is_icones_inj tci_mE.
Proof. exact: (@SC.sci_mE_inj R Ar Tsig D f1 f2). Qed.

(** [eB] factors through [C ⊸ m_E] via [tauE]:
    [(C ⊸ m_E) ∘ tauE = eB]. *)
Lemma tci_fact :
  icones_comp (linhom_post_icones (C := C) tci_mE) tauE = eB B C.
Proof. exact: (@SC.sci_fact R Ar Tsig D f1 f2 Hcurry). Qed.

(** The factoring-family member [(E, m_E, tauE)] ([SC.sci_fsub]). *)
Definition tci_fsub : fsub B C := @SC.sci_fsub R Ar Tsig D f1 f2 Hcurry.

(** Intersection minimality: [tensor_incl] factors through [m_E]. *)
Definition tci_r : icones_hom Ar (tensor B C) E := ff_factor tci_fsub.

Lemma tci_rP : icones_comp tci_mE tci_r = tensor_incl B C.
Proof. exact: (@SC.sci_rP R Ar Tsig D f1 f2 Hcurry). Qed.

(** [e] is a split epi: [e ∘ r = id_{B ⊗ C}]. *)
Lemma tci_split : icones_comp e tci_r = icones_id Ar (tensor B C).
Proof. exact: (@SC.sci_split R Ar Tsig D f1 f2 Hcurry). Qed.

(** Hence [f1 = f2] ([SC.sci_eq]). *)
Lemma tci_eq : f1 = f2.
Proof. exact: (@SC.sci_eq R Ar Tsig D f1 f2 Hcurry). Qed.

End TensorCurryInj.

(** Injectivity of [tensor_curry] (Paper Thm 5.9: [Φ] is a bijection,
    forward part is mono). *)
Lemma tensor_curry_inj (R : realType) (Ar : MeasSubcat R)
    (B C D : ICone.type Ar) (f1 f2 : icones_hom Ar (tensor B C) D) :
  tensor_curry f1 = tensor_curry f2 -> f1 = f2.
Proof. exact: tci_eq. Qed.

Arguments tensor_curry_inj {R Ar B C D} f1 f2.

(** [tensor_curryK] : [tensor_uncurry (tensor_curry f) = f].  By
    [tensor_uncurryK], [tensor_curry (tensor_uncurry (tensor_curry f)) =
    tensor_curry f]; injectivity of [tensor_curry] ([tensor_curry_inj])
    then collapses the round trip. *)
Lemma tensor_curryK (R : realType) (Ar : MeasSubcat R)
    (B C D : ICone.type Ar) (f : icones_hom Ar (tensor B C) D) :
  tensor_uncurry (tensor_curry f) = f.
Proof.
apply: tensor_curry_inj.
exact: tensor_uncurryK.
Qed.

Arguments tensor_curryK {R Ar B C D} f.

(** ** Naturality of [Φ] in [B] (existential form)

    With both round-trips in hand, naturality in [B] is routine: for
    [u : B' → B], the functorial action on objects is
      [tensor_mor_l u := tensor_uncurry ((C ⊸ ?) …)]
    — concretely the uncurry of [tau' B C ∘ u : B' → C ⊸ (B ⊗ C)] — a map
    [B' ⊗ C → B ⊗ C].  Then
      [tensor_curry (f ∘ tensor_mor_l u) = tensor_curry f ∘ u]
    by [tensor_curry_natural_post] ([tensor_curry (f ∘ −) = (C ⊸ f) ∘
    tensor_curry −]) together with [tensor_uncurryK]
    ([tensor_curry (tensor_uncurry g) = g]). *)

Section TensorNaturalB.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B B' C : ICone.type Ar.
Variable u : icones_hom Ar B' B.

(** The functorial action [tensor_mor_l u : B' ⊗ C → B ⊗ C]: the uncurry
    of [tau' ∘ u]. *)
Definition tensor_mor_l : icones_hom Ar (tensor B' C) (tensor B C) :=
  tensor_uncurry (icones_comp (tau' B C) u).

(** [tensor_curry] of [tensor_mor_l u] recovers [tau' ∘ u]
    ([tensor_uncurryK]). *)
Lemma tensor_mor_lK :
  tensor_curry tensor_mor_l = icones_comp (tau' B C) u.
Proof. exact: tensor_uncurryK. Qed.

(** Naturality in [B], concrete form:
    [tensor_curry (f ∘ tensor_mor_l u) = tensor_curry f ∘ u]. *)
Lemma tensor_curry_natural_B_post (D : ICone.type Ar)
    (f : icones_hom Ar (tensor B C) D) :
  tensor_curry (icones_comp f tensor_mor_l) =
  icones_comp (tensor_curry f) u.
Proof.
rewrite (tensor_curry_natural_post f tensor_mor_l).
rewrite tensor_mor_lK.
(* [(C ⊸ f) ∘ (tau' ∘ u) = ((C ⊸ f) ∘ tau') ∘ u = tensor_curry f ∘ u]. *)
by rewrite /tensor_curry icones_compA.
Qed.

End TensorNaturalB.

Arguments tensor_mor_l {R Ar B B' C} u.
Arguments tensor_curry_natural_B_post {R Ar B B' C} u {D} f.

(** Naturality of [Φ] in [B] (existential form): the witness is
    [tensor_mor_l u]. *)
Lemma tensor_curry_natural_B (R : realType) (Ar : MeasSubcat R)
    (B B' C D : ICone.type Ar) (u : icones_hom Ar B' B) :
  exists utens : icones_hom Ar (tensor B' C) (tensor B C),
    forall f : icones_hom Ar (tensor B C) D,
      tensor_curry (icones_comp f utens) = icones_comp (tensor_curry f) u.
Proof.
exists (tensor_mor_l u) => f.
exact: tensor_curry_natural_B_post.
Qed.

Arguments tensor_curry_natural_B {R Ar B B' C D} u.

(**md**************************************************************************)
(* # STATUS — 8 TENSOR-ADJUNCTION PRIMITIVES, AXIOM-FREE                        *)
(*                                                                            *)
(* This file builds, as genuine theorems about the concrete [wi_obj]          *)
(* construction, the eight tensor-adjunction primitives:                      *)
(*                                                                            *)
(*   tensor, tensor_curry, tensor_uncurry, tensor_curryK, tensor_uncurryK,    *)
(*   tensor_curry_natural_post, tensor_curry_natural_D, tensor_curry_natural_B *)
(*                                                                            *)
(* Axiom-clean: [Print Assumptions] on [tensor_curryK], [tensor_curry_inj]    *)
(* and [tensor_curry_natural_B] yields ONLY the three classical [boolp]       *)
(* axioms — {propositional_extensionality, functional_extensionality_dep,     *)
(* constructive_indefinite_description} — and NO project                       *)
(* [Axiom]/[Parameter]/[Admitted].                                            *)
(*                                                                            *)
(* ## Division of labour with [saft_construct.v]                               *)
(*                                                                            *)
(* The functor-generic SAFT engine — the factoring family [fsub], the         *)
(* classifier reindexing [fK]/[fpick], the wide intersection [tensor :=       *)
(* wi_obj fhh fk0] with [tensor_incl], intersection minimality [ff_factor]/   *)
(* [ff_factorP], the universal element [tau'] + [tau'_def], the mono          *)
(* [tensor_incl_inj], the mediator [tensor_uncurry] + [tensor_uncurryK], and  *)
(* the SAFT-uniqueness [tensor_curry_inj]/[tensor_curryK] — is proved ONCE in  *)
(* [Icones.homs.saft_construct] (module [Icones_saft_construct], alias [SC])  *)
(* and instantiated here at [tensor_sig] (the [(C ⊸ −)] right functor:        *)
(* [linhom_post_icones] + [limpl_preserves_prod] + [limpl_eq_med_icones]).    *)
(* This file re-exports every historical name — the definitions are           *)
(* definitionally the same terms as before — and keeps the                    *)
(* instantiation-specific pointwise lemmas ([tJtupleE]/[eBE]/[eprodE]/        *)
(* [WUE]/[WVE]/[WUE']/[WVE']/[fpick_factE]/[tensor_curryE]/[GammaDE]/[tPE])   *)
(* proved concretely as before.                                               *)
(*                                                                            *)
(* ## [tensor_curryK] via SAFT-uniqueness (equaliser of candidates +           *)
(*    intersection minimality) — NOT joint-epicness of [tau']                  *)
(*                                                                            *)
(* [tensor_curry_inj] uses the standard SAFT-uniqueness argument               *)
(* ([SC.sci_*]): given [f1 f2 : B ⊗ C → D] with [tensor_curry f1 =            *)
(* tensor_curry f2], form the equaliser [E := icones_eq f1 f2]; [tau']        *)
(* co-restricts to [tauE] ([tauE_factor]); [(E, tensor_incl ∘ e, tauE)] is a  *)
(* factoring-family member [tci_fsub]; intersection minimality gives          *)
(* [tci_r] with [tci_rP]; [tensor_incl] mono gives [tci_split] ([e] split     *)
(* epi); whence [tci_eq] : [f1 = f2].  [tensor_curryK] then follows from      *)
(* [tensor_uncurryK] + [tensor_curry_inj].                                     *)
(*                                                                            *)
(* ## [tensor_curry_natural_B]                                                 *)
(*                                                                            *)
(* Routine, given both round-trips: [tensor_mor_l u := tensor_uncurry          *)
(* (tau' B C ∘ u) : B' ⊗ C → B ⊗ C]; then [tensor_curry (f ∘ tensor_mor_l u) = *)
(* tensor_curry f ∘ u] by [tensor_curry_natural_post] + [tensor_uncurryK]      *)
(* ([tensor_curry_natural_B_post]).  The existential witness is               *)
(* [tensor_mor_l u].                                                          *)
(******************************************************************************)

End Icones_tensor_construct.
