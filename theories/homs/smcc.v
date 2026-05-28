(**md**************************************************************************)
(* # The symmetric monoidal closed structure of [ICones] — Paper §5.5         *)
(*                                                                            *)
(*   This file assembles the symmetric monoidal (closed) structure of         *)
(*   [ICones] (paper Thm 5.15) on top of the tensor [⊗] of [tensor.v].        *)
(*   The structural isos are the natural isos [tensor_assoc_iso] /            *)
(*   [tensor_lunit_iso] / [tensor_runit_iso] / [tensor_braid_iso] (built in   *)
(*   [tensor_iso.v], Thm 5.12 / Lemma 5.5, paper Eqs 5.2–5.4), [Export]ed     *)
(*   through [tensor.v] together with their pure-tensor computation laws.    *)
(*   Everything here is a real proof.                                         *)
(*                                                                            *)
(*   Deliverables (paper references):                                         *)
(*   - [tensor_assoc] / [tensor_lunit] / [tensor_runit] / [tensor_braid] :    *)
(*     the four structural [icones_iso]s, re-exported under their paper       *)
(*     names with the pure-tensor computation lemmas [tensor_assocEp],        *)
(*     [tensor_lunitEp], [tensor_runitEp], [tensor_braidEp] (Eqs 5.2–5.4).    *)
(*   - [tensor_braid_invol] : the symmetry law [σ ∘ σ = id], derived from     *)
(*     Eq 5.4 via [tensor_ext].                                               *)
(*   - [tensor_triangle] : the triangle coherence, derived via               *)
(*     [tensor_ext] from Eqs 5.2/5.3.                                         *)
(*   - [tensor_pentagon] : the pentagon coherence, derived via                *)
(*     [tensor_ext3]/[tensor_ext] from Eq 5.2.                                *)
(*   - [tensor_hexagon] : the braiding hexagon coherence, derived via         *)
(*     [tensor_ext3] from Eqs 5.2/5.4.                                        *)
(*   - [ICones_SMCC] : the bundle (Thm 5.15) packaging [⊗], the unit [1],     *)
(*     [α]/[λ]/[ρ]/[σ] and the coherence laws.                                *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference.

Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.cone_cat.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.icone.
Require Import Icones.icones.examples_icone.
Require Import Icones.icones.icone_cat.
Require Import Icones.homs.linhom.
Require Import Icones.homs.linhom_functor.
Require Import Icones.homs.icones_iso.

(** [tensor.v] [Export]s the tensor symbols
    ([tensor]/[tensor_curry]/[tensor_uncurry]/[tensor_curryK]/[tensor_normM],
    the Thm 5.12 iso [tensor_hom_iso] and the structural isos
    [tensor_assoc_iso]/[tensor_lunit_iso]/[tensor_runit_iso]/
    [tensor_braid_iso] with their pure-tensor [...E] laws), so importing it
    suffices.  [tensor.v]'s own [tau]/[ptensor]/[tensor_mor] shadow the
    underlying modules' homonyms, so the [⊗]/[⊗p] notations and
    [ptensorE]/[tensor_morE] rewrites all refer to the same symbols. *)
Require Import Icones.homs.tensor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section SMCC.
Variables (R : realType) (Ar : MeasSubcat R).

(** Local mirror of the paper's tensor [⊗], pure tensor [⊗p] and unit
    [1] (the [cone_one_car]). *)
Local Notation "B '⊗' C" := (tensor Ar B C)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.
Local Notation "'one'" := (cone_one_car Ar).

(** ** Bifunctor action on pure tensors — Paper §5.4

    The computation law for [tensor_mor]: [(f ⊗ g)(x ⊗ y) = f x ⊗ g y].
    By [tensor_uncurryK] the curry of [f ⊗ g] is the displayed
    composite [(g ⊸) ∘ τ ∘ f]; evaluating it through Eq 5.1
    ([tensor_curryE]) and the precomposition law [linhom_pre_iconesE]
    yields the pointwise value [f x ⊗ g y]. *)
Lemma tensor_morE (B1 B2 C1 C2 : ICone.type Ar)
    (f : icones_hom Ar B1 B2) (g : icones_hom Ar C1 C2)
    (x : B1) (y : C1) :
  tensor_mor f g (x ⊗p y) = (f x) ⊗p (g y).
Proof.
rewrite (ptensorE (f x) (g y)).
rewrite -(tensor_curryE (tensor_mor f g) x y) /tensor_mor tensor_uncurryK.
by rewrite linhom_map_funE.
Qed.

(** ** Bilinearity of the pure tensor — Paper §5.4

    The pure tensor [x ⊗ y = τ(x)(y)] is linear in each argument, so a
    nonnegative scalar commutes through either slot.  Linearity in [y]
    is the linearity of the linhom [τ(x)]; linearity in [x] uses that
    [τ] is itself a linear morphism, scaling the linhom [τ(x)]
    pointwise. *)

(** Pointwise scaling of a linhom: [(r •: h)(y) = r •: h(y)]. *)
Lemma linhom_funZ (C D : ICone.type Ar) (r : {nonneg R})
    (h : linhom_car Ar C D) (y : C) :
  linhom_fun (precone_scale r h) y = precone_scale r (linhom_fun h y).
Proof. by []. Qed.

(** Scaling in the right slot: [x ⊗ (r •: y) = r •: (x ⊗ y)]. *)
Lemma ptensorZr (B C : ICone.type Ar) (r : {nonneg R}) (x : B) (y : C) :
  x ⊗p (precone_scale r y) = precone_scale r (x ⊗p y).
Proof.
rewrite /ptensor /linhom_fun.
by have [_ _ ->] := linhom_pre_linear (linhom_pre_of (tau B C x)).
Qed.

(** Scaling in the left slot: [(r •: x) ⊗ y = r •: (x ⊗ y)]. *)
Lemma ptensorZl (B C : ICone.type Ar) (r : {nonneg R}) (x : B) (y : C) :
  (precone_scale r x) ⊗p y = precone_scale r (x ⊗p y).
Proof.
rewrite /ptensor /tau.
have [_ _ HZ] := cones_hom_linear (mcones_hom_cones (icones_hom_mcones
  (tensor_curry (icones_id Ar (tensor Ar B C))))).
by rewrite HZ linhom_funZ.
Qed.

(** ** The structural isos — Paper §5.5, Eqs 5.2–5.4

    The associator [α], unitors [λ]/[ρ] and braiding [σ], re-exported
    from the proved [tensor_iso.v] isos under their paper names, with
    their pure-tensor computation laws. *)

Definition tensor_assoc (A B C : ICone.type Ar) :
  icones_iso Ar ((A ⊗ B) ⊗ C) (A ⊗ (B ⊗ C)) :=
  tensor_assoc_iso A B C.

Definition tensor_lunit (A : ICone.type Ar) :
  icones_iso Ar (one ⊗ A) A := tensor_lunit_iso A.

Definition tensor_runit (A : ICone.type Ar) :
  icones_iso Ar (A ⊗ one) A := tensor_runit_iso A.

Definition tensor_braid (A B : ICone.type Ar) :
  icones_iso Ar (A ⊗ B) (B ⊗ A) := tensor_braid_iso A B.

(** Paper Eq 5.2: [α((x ⊗ y) ⊗ z) = x ⊗ (y ⊗ z)]. *)
Lemma tensor_assocEp (A B C : ICone.type Ar) (x : A) (y : B) (z : C) :
  iso_fwd (tensor_assoc A B C) ((x ⊗p y) ⊗p z) = x ⊗p (y ⊗p z).
Proof. exact: tensor_assocE. Qed.

(** Paper Eq 5.3: [λ(u ⊗ x) = u · x]. *)
Lemma tensor_lunitEp (A : ICone.type Ar) (u : one) (x : A) :
  iso_fwd (tensor_lunit A) (u ⊗p x) = precone_scale (c1_val u) x.
Proof. exact: tensor_lunitE. Qed.

(** Paper Eq 5.3: [ρ(x ⊗ u) = u · x]. *)
Lemma tensor_runitEp (A : ICone.type Ar) (x : A) (u : one) :
  iso_fwd (tensor_runit A) (x ⊗p u) = precone_scale (c1_val u) x.
Proof. exact: tensor_runitE. Qed.

(** Paper Eq 5.4: [σ(x ⊗ y) = y ⊗ x]. *)
Lemma tensor_braidEp (A B : ICone.type Ar) (x : A) (y : B) :
  iso_fwd (tensor_braid A B) (x ⊗p y) = y ⊗p x.
Proof. exact: tensor_braidE. Qed.

(** Seal the tensor data so a bare [/=]/[simpl] in the coherence proofs
    below does not unfold the [tensor_construct] internals (which would
    break the [...Ep]/[tensor_morE] rewrites).  [conversion] still
    computes the [...E] values, so the proofs go through verbatim. *)
Opaque tensor_mor tensor_assoc tensor_lunit tensor_runit tensor_braid
       ptensor tau.

(** ** The symmetry law — Paper §5.5, Eq 5.4

    [σ_{B,A} ∘ σ_{A,B} = id_{A ⊗ B}], derived from Eq 5.4 by pure-tensor
    extensionality: [σ(σ(x ⊗ y)) = σ(y ⊗ x) = x ⊗ y]. *)
Lemma tensor_braid_invol (A B : ICone.type Ar) :
  icones_comp (iso_fwd (tensor_braid B A)) (iso_fwd (tensor_braid A B)) =
  icones_id Ar (A ⊗ B).
Proof.
apply: tensor_ext => x y /=.
by rewrite !tensor_braidEp.
Qed.

(** ** Quaternary tree extensionality — Paper Proposition 5.14

    The instance of Prop 5.14 for the left tree [⟨⟨⟨∗,∗⟩,∗⟩,∗⟩], i.e.
    [((A ⊗ B) ⊗ C) ⊗ D], needed to verify the pentagon by agreement on
    pure tensors.  One more currying layer than [tensor_ext3]. *)
Lemma tensor_ext4 (A B C D E : ICone.type Ar)
    (f g : icones_hom Ar (((A ⊗ B) ⊗ C) ⊗ D) E) :
  (forall (w : A) (x : B) (y : C) (z : D),
     f (((w ⊗p x) ⊗p y) ⊗p z) = g (((w ⊗p x) ⊗p y) ⊗p z)) -> f = g.
Proof.
move=> Hfg.
apply: tensor_curry_inj.
apply: tensor_ext3 => w x y.
apply: linhom_eq => z.
by rewrite !tensor_curryE Hfg.
Qed.

(** ** Triangle coherence — Paper §5.5, Thm 5.15

    [(id_A ⊗ λ_B) ∘ α_{A,1,B} = ρ_A ⊗ id_B] as maps [(A ⊗ 1) ⊗ B →
    A ⊗ B].  Derived by [tensor_ext] from Eqs 5.2/5.3 and the
    bilinearity of [⊗]: on [(x ⊗ u) ⊗ y] both sides equal [u · (x ⊗ y)]
    (LHS through the right slot, RHS through the left slot). *)
Lemma tensor_triangle (A B : ICone.type Ar) :
  icones_comp (tensor_mor (icones_id Ar A) (iso_fwd (tensor_lunit B)))
              (iso_fwd (tensor_assoc A one B)) =
  tensor_mor (iso_fwd (tensor_runit A)) (icones_id Ar B).
Proof.
apply: tensor_ext3 => x u y /=.
rewrite tensor_assocEp tensor_morE tensor_lunitEp ptensorZr.
by rewrite tensor_morE tensor_runitEp ptensorZl.
Qed.

(** ** Pentagon coherence — Paper §5.5, Thm 5.15

    The pentagon identity for the associator, as maps
    [(((A ⊗ B) ⊗ C) ⊗ D) → A ⊗ (B ⊗ (C ⊗ D))].  Derived by
    [tensor_ext4] from Eq 5.2 and the bifunctor law [tensor_morE]: on
    [(((w ⊗ x) ⊗ y) ⊗ z)] both composites equal [w ⊗ (x ⊗ (y ⊗ z))]. *)
Lemma tensor_pentagon (A B C D : ICone.type Ar) :
  icones_comp
    (iso_fwd (tensor_assoc A B (C ⊗ D)))
    (iso_fwd (tensor_assoc (A ⊗ B) C D)) =
  icones_comp
    (tensor_mor (icones_id Ar A) (iso_fwd (tensor_assoc B C D)))
    (icones_comp
       (iso_fwd (tensor_assoc A (B ⊗ C) D))
       (tensor_mor (iso_fwd (tensor_assoc A B C)) (icones_id Ar D))).
Proof.
apply: tensor_ext4 => w x y z /=.
rewrite !tensor_assocEp.
rewrite tensor_morE tensor_assocEp tensor_assocEp.
by rewrite tensor_morE tensor_assocEp.
Qed.

(** ** Braiding hexagon — Paper §5.5, Thm 5.15

    The hexagon identity for the braiding, as maps
    [(A ⊗ B) ⊗ C → B ⊗ (C ⊗ A)].  Derived by [tensor_ext3] from
    Eqs 5.2/5.4 and [tensor_morE]: on [(x ⊗ y) ⊗ z] both composites
    equal [y ⊗ (z ⊗ x)]. *)
Lemma tensor_hexagon (A B C : ICone.type Ar) :
  icones_comp
    (iso_fwd (tensor_assoc B C A))
    (icones_comp
       (iso_fwd (tensor_braid A (B ⊗ C)))
       (iso_fwd (tensor_assoc A B C))) =
  icones_comp
    (tensor_mor (icones_id Ar B) (iso_fwd (tensor_braid A C)))
    (icones_comp
       (iso_fwd (tensor_assoc B A C))
       (tensor_mor (iso_fwd (tensor_braid A B)) (icones_id Ar C))).
Proof.
apply: tensor_ext3 => x y z /=.
rewrite !tensor_assocEp tensor_braidEp tensor_assocEp.
rewrite tensor_morE tensor_braidEp tensor_assocEp.
by rewrite tensor_morE tensor_braidEp.
Qed.

End SMCC.

Arguments tensor_morE {R Ar B1 B2 C1 C2}.
Arguments linhom_funZ {R Ar C D}.
Arguments ptensorZr {R Ar B C}.
Arguments ptensorZl {R Ar B C}.
Arguments tensor_assoc {R Ar} A B C.
Arguments tensor_lunit {R Ar} A.
Arguments tensor_runit {R Ar} A.
Arguments tensor_braid {R Ar} A B.
Arguments tensor_assocEp {R Ar A B C}.
Arguments tensor_lunitEp {R Ar A}.
Arguments tensor_runitEp {R Ar A}.
Arguments tensor_braidEp {R Ar A B}.
Arguments tensor_braid_invol {R Ar} A B.
Arguments tensor_ext4 {R Ar A B C D E}.
Arguments tensor_triangle {R Ar} A B.
Arguments tensor_pentagon {R Ar} A B C D.
Arguments tensor_hexagon {R Ar} A B C.

(** ** Paper Theorem 5.15 — [ICones] is a symmetric monoidal closed category

    We bundle the symmetric monoidal closed structure of [ICones] into a
    single record [ICones_SMCC R Ar].  Its fields are exactly the data
    and laws established above:

    - the monoidal product [⊗] (object map [tensor] and bifunctor action
      [tensor_mor] with its identity law [tensor_mor_id]) and unit [1]
      ([cone_one_car]);
    - the structural natural isos [α]/[λ]/[ρ]/[σ]
      ([tensor_assoc]/[tensor_lunit]/[tensor_runit]/[tensor_braid]) with
      their pure-tensor computation laws (Eqs 5.2–5.4);
    - the symmetry law [σ ∘ σ = id], and the triangle, pentagon and
      braiding-hexagon coherence diagrams;
    - closedness: the internal hom [⊸] together with the Thm 5.12 iso
      [(B ⊗ C) ⊸ D ≅ B ⊸ (C ⊸ D)] (here [tensor_hom_iso]).

    The canonical witness [ICones_smcc] populates every field with the
    proved lemmas.  [ICones_smcc] is AXIOM-FREE: it depends on nothing
    beyond the three classical [boolp] axioms. *)

Record ICones_SMCC (R : realType) (Ar : MeasSubcat R) : Type :=
  MkIConesSMCC {
  (* monoidal product and unit *)
  smcc_tensor : ICone.type Ar -> ICone.type Ar -> ICone.type Ar;
  smcc_unit : ICone.type Ar;
  smcc_mor : forall B1 B2 C1 C2 : ICone.type Ar,
    icones_hom Ar B1 B2 -> icones_hom Ar C1 C2 ->
    icones_hom Ar (smcc_tensor B1 C1) (smcc_tensor B2 C2);
  smcc_mor_id : forall B C : ICone.type Ar,
    smcc_mor (icones_id Ar B) (icones_id Ar C) =
    icones_id Ar (smcc_tensor B C);
  (* structural isos *)
  smcc_assoc : forall A B C : ICone.type Ar,
    icones_iso Ar (smcc_tensor (smcc_tensor A B) C)
                  (smcc_tensor A (smcc_tensor B C));
  smcc_lunit : forall A : ICone.type Ar,
    icones_iso Ar (smcc_tensor smcc_unit A) A;
  smcc_runit : forall A : ICone.type Ar,
    icones_iso Ar (smcc_tensor A smcc_unit) A;
  smcc_braid : forall A B : ICone.type Ar,
    icones_iso Ar (smcc_tensor A B) (smcc_tensor B A);
  (* symmetry and coherence *)
  smcc_braid_invol : forall A B : ICone.type Ar,
    icones_comp (iso_fwd (smcc_braid B A)) (iso_fwd (smcc_braid A B)) =
    icones_id Ar (smcc_tensor A B);
  smcc_triangle : forall A B : ICone.type Ar,
    icones_comp (smcc_mor (icones_id Ar A) (iso_fwd (smcc_lunit B)))
                (iso_fwd (smcc_assoc A smcc_unit B)) =
    smcc_mor (iso_fwd (smcc_runit A)) (icones_id Ar B);
  smcc_pentagon : forall A B C D : ICone.type Ar,
    icones_comp
      (iso_fwd (smcc_assoc A B (smcc_tensor C D)))
      (iso_fwd (smcc_assoc (smcc_tensor A B) C D)) =
    icones_comp
      (smcc_mor (icones_id Ar A) (iso_fwd (smcc_assoc B C D)))
      (icones_comp
         (iso_fwd (smcc_assoc A (smcc_tensor B C) D))
         (smcc_mor (iso_fwd (smcc_assoc A B C)) (icones_id Ar D)));
  smcc_hexagon : forall A B C : ICone.type Ar,
    icones_comp
      (iso_fwd (smcc_assoc B C A))
      (icones_comp
         (iso_fwd (smcc_braid A (smcc_tensor B C)))
         (iso_fwd (smcc_assoc A B C))) =
    icones_comp
      (smcc_mor (icones_id Ar B) (iso_fwd (smcc_braid A C)))
      (icones_comp
         (iso_fwd (smcc_assoc B A C))
         (smcc_mor (iso_fwd (smcc_braid A B)) (icones_id Ar C)));
  (* closedness: the internal hom and the Thm 5.12 iso *)
  smcc_hom : ICone.type Ar -> ICone.type Ar -> ICone.type Ar;
  smcc_closed : forall B C D : ICone.type Ar,
    icones_iso Ar (smcc_hom (smcc_tensor B C) D)
                  (smcc_hom B (smcc_hom C D));
}.

Arguments ICones_SMCC {R} Ar.

(** Paper Thm 5.15: the canonical symmetric monoidal closed structure on
    [ICones], every field populated by a proved lemma. *)
Definition ICones_smcc (R : realType) (Ar : MeasSubcat R) :
    ICones_SMCC Ar :=
  {| smcc_tensor := @tensor R Ar;
     smcc_unit := cone_one_car Ar;
     smcc_mor := @tensor_mor R Ar;
     smcc_mor_id := @tensor_mor_id R Ar;
     smcc_assoc := @tensor_assoc R Ar;
     smcc_lunit := @tensor_lunit R Ar;
     smcc_runit := @tensor_runit R Ar;
     smcc_braid := @tensor_braid R Ar;
     smcc_braid_invol := @tensor_braid_invol R Ar;
     smcc_triangle := @tensor_triangle R Ar;
     smcc_pentagon := @tensor_pentagon R Ar;
     smcc_hexagon := @tensor_hexagon R Ar;
     smcc_hom := @linhom_car R Ar;
     smcc_closed := @tensor_hom_iso R Ar |}.
