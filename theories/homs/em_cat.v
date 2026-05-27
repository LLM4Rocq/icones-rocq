(**md**************************************************************************)
(** * The Eilenberg–Moore category [EM(!)] and the cofree adjunction — CBV §1

    Step 1 of the call-by-value roadmap
    ([/home/rocq/prime_gap/icones-cbv-plan.md], Phase A1).  We package the
    Eilenberg–Moore category of the exponential comonad [!] ([bang.v]) as a
    usable category on top of the minimal coalgebra layer of
    [coalgebra.v], and we exhibit the cofree/forgetful adjunction
    [U ⊣ !̃] : [IC ⇄ EM(!)].

    This is pure "abstract nonsense from Theorem 9.5": every law below is a
    diagram chase from the comonad laws ([comonad_counitL]/
    [comonad_counitR]/[comonad_coassoc], [der_nat]/[dig_nat],
    [bang_fmap_id]/[bang_fmap_comp]) and the coalgebra laws ([coalg_counit]/
    [coalg_coassoc]) of [coalgebra.v].  No new analysis.

    Contents:
    - [coalg_hom P Q] — a bundled morphism of [!]-coalgebras (an
      [icones_hom] together with the [is_coalg_mor] side-condition),
      with [coalg_homE] (pointwise reading) and [coalg_hom_eqP].
    - [coalg_id]/[coalg_comp] — the identity and composition of bundled
      coalgebra morphisms, and the CATEGORY LAWS [coalg_compIl]/
      [coalg_compIr]/[coalg_compA].
    - [EM_Cat] / [ICones_EM] — the EM-category bundle (objects, morphisms,
      id, composition, laws), mirroring the [SeelyCategory]/[Comonad]
      record-with-witness convention.
    - [bang_cofree B] — the COFREE coalgebra [(!B, dig B)] (a [Coalgebra]
      by [comonad_counitL]/[comonad_coassoc]); [bang_cofree_fmap f = !f]
      (a coalgebra morphism by [dig_nat]); functoriality
      [bang_cofree_fmap_id]/[bang_cofree_fmap_comp]; the bundled functor
      [bang_cofree_hom].
    - [U_obj]/[U_mor] — the FORGETFUL functor [U : EM(!) → IC].
    - the cofree/forgetful ADJUNCTION [U ⊣ !̃]: the unit [adj_unit]
      ([= coalg_str], natural by [is_coalg_mor]), the counit [adj_counit]
      ([= der]), the bijection [adj_phi]/[adj_psi] of hom-sets
      [EM(!)(γ, !̃B) ≅ IC(U γ, B)] with both round-trips [adj_phiK]/
      [adj_psiK] and naturality [adj_phi_natL]/[adj_phi_natR], and the
      triangle identities [adj_triangleL]/[adj_triangleR].

    Step 3 (the cartesian structure on [EM(!)], Melliès Prop 28 / Cor 20)
    is NOT attempted here. *)

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
Require Import Icones.icones.icone_cat.
Require Import Icones.stable.scones_cat.
Require Import Icones.homs.exp_adjunction.
Require Import Icones.homs.bang.
Require Import Icones.homs.coalgebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section EMCat.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Bg := (@Bang R Ar).

(** ** Bundled coalgebra morphisms

    A morphism of [!]-coalgebras [(A,a) → (B,b)] is an [icones_hom A → B]
    together with the proof that it commutes with the structure maps
    ([is_coalg_mor]).  We bundle them so that [EM(!)] is a category with a
    single morphism type (matching the project's concrete-category
    style). *)
Record coalg_hom (P Q : Coalgebra Ar) : Type := MkCoalgHom {
  ch_mor : icones_hom Ar (coalg_obj P) (coalg_obj Q);
  ch_is_mor : is_coalg_mor P Q ch_mor;
}.

(** Two bundled coalgebra morphisms are equal once their underlying
    [icones_hom]s agree (the side-condition is a [Prop]). *)
Lemma coalg_hom_eqP (P Q : Coalgebra Ar) (f g : coalg_hom P Q) :
  ch_mor f = ch_mor g -> f = g.
Proof.
case: f => fm fp; case: g => gm gp /= Hfg.
move: fp; rewrite Hfg => fp.
by congr MkCoalgHom; exact: Prop_irrelevance.
Qed.

(** The identity coalgebra morphism. *)
Definition coalg_id (P : Coalgebra Ar) : coalg_hom P P :=
  MkCoalgHom (coalg_mor_id P).

(** Composition of coalgebra morphisms. *)
Definition coalg_comp (P Q S : Coalgebra Ar)
    (g : coalg_hom Q S) (f : coalg_hom P Q) : coalg_hom P S :=
  MkCoalgHom (coalg_mor_comp (ch_mor g) (ch_mor f) (ch_is_mor g) (ch_is_mor f)).

(** The underlying [icones_hom] of a composite is the composite of the
    underlying [icones_hom]s. *)
Lemma coalg_comp_mor (P Q S : Coalgebra Ar)
    (g : coalg_hom Q S) (f : coalg_hom P Q) :
  ch_mor (coalg_comp g f) = icones_comp (ch_mor g) (ch_mor f).
Proof. by []. Qed.

(** ** The category laws for [EM(!)]

    Inherited from the [ICones] category laws ([icones_compIl]/
    [icones_compIr]/[icones_compA]) since [ch_mor] is faithful. *)
Lemma coalg_compIl (P Q : Coalgebra Ar) (f : coalg_hom P Q) :
  coalg_comp (coalg_id Q) f = f.
Proof. by apply: coalg_hom_eqP; rewrite coalg_comp_mor /= icones_compIl. Qed.

Lemma coalg_compIr (P Q : Coalgebra Ar) (f : coalg_hom P Q) :
  coalg_comp f (coalg_id P) = f.
Proof. by apply: coalg_hom_eqP; rewrite coalg_comp_mor /= icones_compIr. Qed.

Lemma coalg_compA (P Q S T : Coalgebra Ar)
    (h : coalg_hom S T) (g : coalg_hom Q S) (f : coalg_hom P Q) :
  coalg_comp h (coalg_comp g f) = coalg_comp (coalg_comp h g) f.
Proof. by apply: coalg_hom_eqP; rewrite !coalg_comp_mor icones_compA. Qed.

End EMCat.

Arguments coalg_hom {R Ar} P Q.
Arguments MkCoalgHom {R Ar P Q ch_mor} ch_is_mor.
Arguments ch_mor {R Ar P Q}.
Arguments ch_is_mor {R Ar P Q}.
Arguments coalg_hom_eqP {R Ar P Q} f g.
Arguments coalg_id {R Ar} P.
Arguments coalg_comp {R Ar P Q S} g f.
Arguments coalg_comp_mor {R Ar P Q S} g f.
Arguments coalg_compIl {R Ar P Q} f.
Arguments coalg_compIr {R Ar P Q} f.
Arguments coalg_compA {R Ar P Q S T} h g f.

(** ** The Eilenberg–Moore category bundle

    Package the EM-category of [!] as a [Record] of data + laws over the
    bundled coalgebra morphisms, mirroring [ICones_SMCC]/[Bang_comonad]/
    [SeelyCategory].  Objects are [Coalgebra Ar], morphisms are
    [coalg_hom], identity [coalg_id], composition [coalg_comp]. *)
Record EM_Cat (R : realType) (Ar : MeasSubcat R) : Type := MkEMCat {
  em_obj : Type;
  em_hom : em_obj -> em_obj -> Type;
  em_id : forall P : em_obj, em_hom P P;
  em_comp : forall P Q S : em_obj, em_hom Q S -> em_hom P Q -> em_hom P S;
  em_compIl : forall (P Q : em_obj) (f : em_hom P Q), em_comp (em_id Q) f = f;
  em_compIr : forall (P Q : em_obj) (f : em_hom P Q), em_comp f (em_id P) = f;
  em_compA : forall (P Q S T : em_obj)
    (h : em_hom S T) (g : em_hom Q S) (f : em_hom P Q),
    em_comp h (em_comp g f) = em_comp (em_comp h g) f;
}.

Arguments EM_Cat {R} Ar.

(** The canonical EM-category structure on [EM(!)]. *)
Definition ICones_EM (R : realType) (Ar : MeasSubcat R) : EM_Cat Ar :=
  {| em_obj := Coalgebra Ar;
     em_hom := @coalg_hom R Ar;
     em_id := @coalg_id R Ar;
     em_comp := @coalg_comp R Ar;
     em_compIl := @coalg_compIl R Ar;
     em_compIr := @coalg_compIr R Ar;
     em_compA := @coalg_compA R Ar |}.

(** ** The cofree coalgebra functor [!̃ : IC → EM(!)] *)

Section Cofree.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Bg := (@Bang R Ar).

(** The cofree coalgebra [!̃B = (!B, dig_B)].  Its counit law is the comonad
    left-counit [comonad_counitL] ([der_{!B} ∘ dig_B = id]); its coassoc
    law is the comonad coassociativity [comonad_coassoc] ([dig_{!B} ∘ dig_B
    = !(dig_B) ∘ dig_B]). *)
Definition bang_cofree (B : ICone.type Ar) : Coalgebra Ar :=
  MkCoalgebra (comonad_counitL B) (comonad_coassoc B).

(** Its carrier is [!B] and its structure map is [dig B] (definitional). *)
Lemma bang_cofree_obj (B : ICone.type Ar) : coalg_obj (bang_cofree B) = Bg B.
Proof. by []. Qed.

Lemma bang_cofree_str (B : ICone.type Ar) : coalg_str (bang_cofree B) = dig B.
Proof. by []. Qed.

(** The functorial action [!̃f = !f] is a coalgebra morphism
    [!̃B → !̃C]: the requirement [dig_C ∘ !f = !(!f) ∘ dig_B] is exactly the
    naturality of [dig] ([dig_nat]). *)
Lemma bang_cofree_fmap_is_mor (B C : ICone.type Ar) (f : icones_hom Ar B C) :
  is_coalg_mor (bang_cofree B) (bang_cofree C) (bang_fmap f).
Proof. by rewrite /is_coalg_mor /= (dig_nat f). Qed.

Definition bang_cofree_hom (B C : ICone.type Ar) (f : icones_hom Ar B C) :
    coalg_hom (bang_cofree B) (bang_cofree C) :=
  MkCoalgHom (bang_cofree_fmap_is_mor f).

(** Functoriality of [!̃] (inherited from [!]'s functor laws). *)
Lemma bang_cofree_fmap_id (B : ICone.type Ar) :
  bang_cofree_hom (icones_id Ar B) = coalg_id (bang_cofree B).
Proof. by apply: coalg_hom_eqP; rewrite /= bang_fmap_id. Qed.

Lemma bang_cofree_fmap_comp (B C D : ICone.type Ar)
    (g : icones_hom Ar C D) (f : icones_hom Ar B C) :
  bang_cofree_hom (icones_comp g f) =
  coalg_comp (bang_cofree_hom g) (bang_cofree_hom f).
Proof.
by apply: coalg_hom_eqP; rewrite coalg_comp_mor /= (bang_fmap_comp g f).
Qed.

(** ** The forgetful functor [U : EM(!) → IC]

    [U(A,a) = A] on objects; [U h = ch_mor h] on morphisms.  Functoriality
    is immediate ([ch_mor] preserves [coalg_id]/[coalg_comp]
    definitionally). *)
Definition U_obj (P : Coalgebra Ar) : ICone.type Ar := coalg_obj P.

Definition U_mor (P Q : Coalgebra Ar) (h : coalg_hom P Q) :
    icones_hom Ar (U_obj P) (U_obj Q) := ch_mor h.

Lemma U_mor_id (P : Coalgebra Ar) :
  U_mor (coalg_id P) = icones_id Ar (U_obj P).
Proof. by []. Qed.

Lemma U_mor_comp (P Q S : Coalgebra Ar)
    (g : coalg_hom Q S) (f : coalg_hom P Q) :
  U_mor (coalg_comp g f) = icones_comp (U_mor g) (U_mor f).
Proof. by []. Qed.

End Cofree.

Arguments bang_cofree {R Ar} B.
Arguments bang_cofree_obj {R Ar} B.
Arguments bang_cofree_str {R Ar} B.
Arguments bang_cofree_fmap_is_mor {R Ar B C} f.
Arguments bang_cofree_hom {R Ar B C} f.
Arguments bang_cofree_fmap_id {R Ar} B.
Arguments bang_cofree_fmap_comp {R Ar B C D} g f.
Arguments U_obj {R Ar} P.
Arguments U_mor {R Ar P Q} h.
Arguments U_mor_id {R Ar} P.
Arguments U_mor_comp {R Ar P Q S} g f.

(** ** The cofree/forgetful adjunction [U ⊣ !̃]

    The adjunction bijection
      [EM(!)(γ, !̃B) ≅ IC(U γ, B)]
    for a coalgebra [γ = (A,a)] and an object [B]:
    - forward [adj_phi : coalg_hom γ (!̃B) → icones_hom (U γ) B],
      [adj_phi h = der_B ∘ (U h)] (postcompose with the counit/dereliction);
    - backward [adj_psi : icones_hom (U γ) B → coalg_hom γ (!̃B)],
      [adj_psi g = !g ∘ a] (a coalgebra morphism, [adj_psi_is_mor]).

    Both round-trips ([adj_phiK]/[adj_psiK]) and naturality follow from the
    comonad laws + the coalgebra laws of [γ].  The counit of the adjunction
    is [der]; the unit is [coalg_str] (the structure map of every
    coalgebra, natural by [is_coalg_mor]). *)

Section CofreeAdjunction.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Bg := (@Bang R Ar).

(** *** The counit [ε = der] and the unit [η = coalg_str] *)

(** The counit [ε_B = der_B : U(!̃B) → B], i.e. [der_B : !B → B]. *)
Definition adj_counit (B : ICone.type Ar) : icones_hom Ar (U_obj (bang_cofree B)) B :=
  der B.

(** The unit [η_γ = coalg_str γ : γ → !̃(U γ)] is a coalgebra morphism: the
    requirement [dig_A ∘ a = !a ∘ a] is exactly [coalg_coassoc]. *)
Lemma adj_unit_is_mor (P : Coalgebra Ar) :
  is_coalg_mor P (bang_cofree (U_obj P)) (coalg_str P).
Proof. by rewrite /is_coalg_mor /= (coalg_coassoc P). Qed.

Definition adj_unit (P : Coalgebra Ar) :
    coalg_hom P (bang_cofree (U_obj P)) :=
  MkCoalgHom (adj_unit_is_mor P).

(** *** The hom-bijection *)

(** Forward [Φ : coalg_hom γ (!̃B) → IC(U γ, B)], [Φ h = der_B ∘ (U h)]. *)
Definition adj_phi (P : Coalgebra Ar) (B : ICone.type Ar)
    (h : coalg_hom P (bang_cofree B)) : icones_hom Ar (U_obj P) B :=
  icones_comp (adj_counit B) (U_mor h).

(** Backward [Ψ : IC(U γ, B) → coalg_hom γ (!̃B)], [Ψ g = !g ∘ a].  This is
    a coalgebra morphism [γ → !̃B = (!B, dig_B)]: we must show
    [dig_B ∘ (!g ∘ a) = !(!g ∘ a) ∘ a].  Chase:
      [dig_B ∘ !g ∘ a = !!g ∘ dig_A ∘ a]   (dig naturality [dig_nat])
                      [= !!g ∘ !a ∘ a]       (coalgebra [coalg_coassoc])
                      [= !(!g ∘ a) ∘ a]      ([bang_fmap_comp]). *)
Lemma adj_psi_is_mor (P : Coalgebra Ar) (B : ICone.type Ar)
    (g : icones_hom Ar (U_obj P) B) :
  is_coalg_mor P (bang_cofree B) (icones_comp (bang_fmap g) (coalg_str P)).
Proof.
rewrite /is_coalg_mor /= icones_compA -(dig_nat g) -icones_compA.
by rewrite (coalg_coassoc P) icones_compA -(bang_fmap_comp (bang_fmap g) (coalg_str P)).
Qed.

Definition adj_psi (P : Coalgebra Ar) (B : ICone.type Ar)
    (g : icones_hom Ar (U_obj P) B) : coalg_hom P (bang_cofree B) :=
  MkCoalgHom (adj_psi_is_mor g).

(** [adj_phi (adj_psi g) = g].  [Φ(Ψ g) = der_B ∘ !g ∘ a = g ∘ der_A ∘ a]
    (counit naturality [der_nat]) [= g ∘ id = g] (coalgebra
    [coalg_counit]). *)
Lemma adj_phiK (P : Coalgebra Ar) (B : ICone.type Ar)
    (g : icones_hom Ar (U_obj P) B) :
  adj_phi (adj_psi g) = g.
Proof.
rewrite /adj_phi /adj_counit /U_mor /= icones_compA -(der_nat g).
by rewrite -icones_compA (coalg_counit P) icones_compIr.
Qed.

(** [adj_psi (adj_phi h) = h].  [Ψ(Φ h) = !(der_B ∘ U h) ∘ a =
    !der_B ∘ !(U h) ∘ a].  Since [h] is a coalgebra morphism,
    [dig_B ∘ U h = !(U h) ∘ a], hence [!der_B ∘ !(U h) ∘ a =
    !der_B ∘ dig_B ∘ U h = U h] (comonad right-counit [comonad_counitR]). *)
Lemma adj_psiK (P : Coalgebra Ar) (B : ICone.type Ar)
    (h : coalg_hom P (bang_cofree B)) :
  adj_psi (adj_phi h) = h.
Proof.
apply: coalg_hom_eqP.
rewrite /adj_psi /adj_phi /adj_counit /U_mor /=.
rewrite (bang_fmap_comp (der B) (ch_mor h)) -icones_compA.
have Hh := ch_is_mor h; rewrite /is_coalg_mor /= in Hh.
rewrite -Hh icones_compA (comonad_counitR B) icones_compIl.
by [].
Qed.

(** *** Naturality of the bijection

    [adj_phi] is natural in the coalgebra argument (precomposition by a
    coalgebra morphism [k : P' → P]) and in the object argument
    (postcomposition by [f : B → B']). *)

(** Naturality in [P] (contravariant): [Φ(h ∘ k) = Φ(h) ∘ U(k)]. *)
Lemma adj_phi_natL (P P' : Coalgebra Ar) (B : ICone.type Ar)
    (h : coalg_hom P (bang_cofree B)) (k : coalg_hom P' P) :
  adj_phi (coalg_comp h k) = icones_comp (adj_phi h) (U_mor k).
Proof.
by rewrite /adj_phi /U_mor coalg_comp_mor /= icones_compA.
Qed.

(** Naturality in [B] (covariant): [Φ(!̃f ∘ h) = f ∘ Φ(h)].
    [Φ(!f ∘ h) = der_{B'} ∘ !f ∘ U h = f ∘ der_B ∘ U h = f ∘ Φ(h)]
    (counit naturality [der_nat]). *)
Lemma adj_phi_natR (P : Coalgebra Ar) (B B' : ICone.type Ar)
    (h : coalg_hom P (bang_cofree B)) (f : icones_hom Ar B B') :
  adj_phi (coalg_comp (bang_cofree_hom f) h) =
  icones_comp f (adj_phi h).
Proof.
rewrite /adj_phi /adj_counit /U_mor coalg_comp_mor /=.
by rewrite icones_compA (der_nat f) -!icones_compA.
Qed.

(** *** The triangle identities of the adjunction [U ⊣ !̃]

    [adj_triangleR] : [ε_{U(!̃B)} ∘ U(η_{!̃B})]-flavoured — the [!̃]-triangle
    [U(adj_unit) post-composed by adj_counit = id], reading
    [der_B ∘ ... ]; concretely [adj_phi (adj_unit (!̃B)) = id_{!B}] would be
    circular, so we record the two genuine triangle equations directly.

    Triangle 1 (the [U]-side): for every coalgebra [P],
      [adj_phi (adj_unit P) = id_{U P}],
    i.e. [der_A ∘ a = id] — this is exactly [coalg_counit]. *)
Lemma adj_triangleL (P : Coalgebra Ar) :
  adj_phi (adj_unit P) = icones_id Ar (U_obj P).
Proof.
by rewrite /adj_phi /adj_counit /adj_unit /U_mor /= (coalg_counit P).
Qed.

(** Triangle 2 (the [!̃]-side): for every object [B],
      [adj_psi (adj_counit B) = coalg_id (!̃B)],
    i.e. [!(der_B) ∘ dig_B = id_{!B}] — this is exactly [comonad_counitR]. *)
Lemma adj_triangleR (B : ICone.type Ar) :
  adj_psi (adj_counit B) = coalg_id (bang_cofree B).
Proof.
apply: coalg_hom_eqP.
by rewrite /adj_psi /adj_counit /= (comonad_counitR B).
Qed.

End CofreeAdjunction.

Arguments adj_counit {R Ar} B.
Arguments adj_unit_is_mor {R Ar} P.
Arguments adj_unit {R Ar} P.
Arguments adj_phi {R Ar P B} h.
Arguments adj_psi_is_mor {R Ar P B} g.
Arguments adj_psi {R Ar P B} g.
Arguments adj_phiK {R Ar P B} g.
Arguments adj_psiK {R Ar P B} h.
Arguments adj_phi_natL {R Ar P P' B} h k.
Arguments adj_phi_natR {R Ar P B B'} h f.
Arguments adj_triangleL {R Ar} P.
Arguments adj_triangleR {R Ar} B.
