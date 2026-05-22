(**md**************************************************************************)
(* # STAGING CONTRACT — the tensor / SAFT interface (Paper §5.4)             *)
(*                                                                            *)
(* PLAN.md §13 builds the symmetric monoidal tensor [⊗] on [ICones] from a    *)
(* PROVED Special Adjoint Functor Theorem (SAFT).  We use a *staged* layout:  *)
(*                                                                            *)
(*   1. (THIS FILE) declare the SAFT/tensor universal property as a small,    *)
(*      temporary INTERFACE — a handful of [Parameter]s, exactly the §12      *)
(*      axioms the tensor milestone consumes.                                 *)
(*   2. build the tensor and its coherence against this interface;            *)
(*   3. DISCHARGE the interface by proving SAFT (milestone M-SAFT, §13.1),    *)
(*      after which every [Parameter] below is replaced by a theorem and      *)
(*      THIS FILE IS DELETED.                                                  *)
(*                                                                            *)
(* Every [Parameter] here is therefore an INTENTIONAL, TEMPORARY AXIOM,       *)
(* flagged with `STAGING: discharge via M-SAFT, PLAN §13.1; then delete`.     *)
(* Nothing else in the project is left unproved, and there are no [Admitted]. *)
(*                                                                            *)
(* The internal linear hom `C ⊸ D` is the concrete integrable cone           *)
(* [linhom_car Ar C D] from [theories/homs/linhom.v] (registered as an        *)
(* [iconeType Ar], hence usable as an [ICone.type Ar]).  There is no `⊸`      *)
(* notation in the codebase, so we introduce a [Local Notation] mirroring the *)
(* paper's `⊸` for readability inside this section only.                      *)
(*                                                                            *)
(* The hom-bijection [Φ] of paper Thm 5.9 / Eq 5.1 would naturally be stated  *)
(* through an `icones_iso` record, but no such record exists yet; we state it *)
(* with the raw maps [tensor_curry] / [tensor_uncurry] plus the two           *)
(* round-trip cancellation [Parameter]s.                                      *)
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
Require Import Icones.homs.linhom.
Require Import Icones.homs.linhom_functor.
Require Import Icones.homs.icones_iso.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section TensorInterface.
Variables (R : realType) (Ar : MeasSubcat R).

(** Local mirror of the paper's `⊸` for the internal linear hom
    [linhom_car Ar C D] (paper §5.1).  Notation only; the underlying
    object is unchanged. *)
Local Notation "C '⊸' D" := (linhom_car Ar C D)
  (at level 99, right associativity) : ring_scope.

(** ** The representing object — Paper §5.4, Remark 5.1

    The tensor [B ⊗ C] is the object representing the functor
    [D ↦ ICones(B, C ⊸ D)].  Remark 5.1 gives no explicit carrier,
    so the interface exposes [tensor] as an opaque object former. *)

(* STAGING: discharge via M-SAFT, PLAN §13.1; then delete *)
Parameter tensor :
  ICone.type Ar -> ICone.type Ar -> ICone.type Ar.

Local Notation "B '⊗' C" := (tensor B C)
  (at level 40, left associativity) : ring_scope.

(** ** The natural hom-bijection [Φ] — Paper Thm 5.9 / Eq 5.1

    For all [B C D], [Φ] is a bijection
      [ICones(B ⊗ C, D)  ≃  ICones(B, C ⊸ D)].
    We expose it as the forward map [tensor_curry], the inverse
    [tensor_uncurry], and the two round-trip equations.  (An
    [icones_iso] record does not yet exist, so we use raw maps plus
    cancellation.) *)

(* STAGING: discharge via M-SAFT, PLAN §13.1; then delete *)
Parameter tensor_curry :
  forall B C D : ICone.type Ar,
    icones_hom Ar (B ⊗ C) D -> icones_hom Ar B (C ⊸ D).

(* STAGING: discharge via M-SAFT, PLAN §13.1; then delete *)
Parameter tensor_uncurry :
  forall B C D : ICone.type Ar,
    icones_hom Ar B (C ⊸ D) -> icones_hom Ar (B ⊗ C) D.

(* STAGING: discharge via M-SAFT, PLAN §13.1; then delete *)
Parameter tensor_curryK :
  forall (B C D : ICone.type Ar) (f : icones_hom Ar (B ⊗ C) D),
    tensor_uncurry (tensor_curry f) = f.

(* STAGING: discharge via M-SAFT, PLAN §13.1; then delete *)
Parameter tensor_uncurryK :
  forall (B C D : ICone.type Ar) (g : icones_hom Ar B (C ⊸ D)),
    tensor_curry (tensor_uncurry g) = g.

(** ** Naturality of [Φ] in [D] — Paper Thm 5.9 / Eq 5.1

    Postcomposing the result of [tensor_curry] by [h : D → D'] equals
    currying the postcomposition of [h] on [B ⊗ C → D].  Here the
    action on the hom-object is [linhom_postcomp h : (C ⊸ D) → (C ⊸ D')]
    — postcomposition by [h].  Since [linhom.v] does not (yet) export
    a named [icones_hom] for this functorial action, we state the
    naturality square via [icones_comp] together with an existential
    witness for that action, keeping the contract self-contained. *)

(* STAGING: discharge via M-SAFT, PLAN §13.1; then delete *)
Parameter tensor_curry_natural_D :
  forall (B C D D' : ICone.type Ar) (h : icones_hom Ar D D'),
  exists hstar : icones_hom Ar (C ⊸ D) (C ⊸ D'),
    forall f : icones_hom Ar (B ⊗ C) D,
      tensor_curry (icones_comp h f) = icones_comp hstar (tensor_curry f).

(** ** Naturality of [Φ] in [B] and [C] — Paper Thm 5.9 / Eq 5.1

    Naturality in [B]: precomposing the curried map by [u : B' → B]
    equals currying the precomposition of [tensor u C] on [B ⊗ C].
    The functorial action [tensor u C : (B' ⊗ C) → (B ⊗ C)] is itself
    derived from the universal property, so we package it existentially. *)

(* STAGING: discharge via M-SAFT, PLAN §13.1; then delete *)
Parameter tensor_curry_natural_B :
  forall (B B' C D : ICone.type Ar) (u : icones_hom Ar B' B),
  exists utens : icones_hom Ar (B' ⊗ C) (B ⊗ C),
    forall f : icones_hom Ar (B ⊗ C) D,
      tensor_curry (icones_comp f utens) = icones_comp (tensor_curry f) u.

(* TODO (M-SAFT, PLAN §13.1): naturality in the [C] slot.  This needs
   the functorial action of [⊸] in its left (contravariant) argument,
   i.e. [linhom_precomp v : (C ⊸ D) → (C' ⊸ D)] for [v : C' → C], which
   [linhom.v] does not yet export under a stable name.  When that action
   lands, add the analogous [tensor_curry_natural_C] square here.  The
   tensor milestone (§13) consumes naturality in [D] and [B]; naturality
   in [C] is only needed for the symmetry coherence, derived later. *)

(** ** Concrete naturality of [Φ] in [D] — Paper Thm 5.9 / Eq 5.1

    The CONCRETE form of [tensor_curry_natural_D]: the witness [hstar]
    of the existential naturality square is the hom-functor action
    [C ⊸ h = linhom_post_icones h] (postcomposition by [h]).  This is
    exactly the paper's "naturality of [Φ] in [D]": [Φ(h ∘ f) =
    (C ⊸ h) ∘ Φ(f)].  Specialising [f := id (B ⊗ C)] yields Eq 5.1,
    [Φ(f) = (C ⊸ f) ∘ τ], in the pointwise form
    [Φ(f)(x)(y) = f(x ⊗ y)] used by Prop 5.14. *)

(* STAGING: discharge via M-SAFT, PLAN §13.1; then delete *)
Parameter tensor_curry_natural_post :
  forall (B C D D' : ICone.type Ar) (h : icones_hom Ar D D')
         (f : icones_hom Ar (B ⊗ C) D),
    tensor_curry (icones_comp h f) =
    icones_comp (linhom_post_icones h) (tensor_curry f).

(** ** Thm 5.12 — [Φ] as an iso of integrable cones

    Paper Thm 5.12: [Φ_{B,C,D}] is an isomorphism of integrable cones
    [(B ⊗ C) ⊸ D ≃ B ⊸ (C ⊸ D)].  This is the ELEMENT-level packaging
    of [tensor_curry] (which the minimal contract exposes only at the
    morphism level): an [icones_iso] between the two internal-hom cones,
    where [B ⊸ (C ⊸ D) = linhom_car Ar B (linhom_car Ar C D)]. *)

(* STAGING: discharge via M-SAFT, PLAN §13.1; then delete *)
Parameter tensor_hom_iso :
  forall B C D : ICone.type Ar,
    icones_iso Ar (linhom_car Ar (B ⊗ C) D)
                  (linhom_car Ar B (linhom_car Ar C D)).

(** ** Thm 5.13 — multiplicativity of the tensor norm

    Paper Thm 5.13: [‖x ⊗ y‖ = ‖x‖ · ‖y‖].  The [≤] direction is
    derived in [tensor.v] from norm-decrease of [τ]; the converse [≥]
    needs the dual-separation Prop 3.11 together with the element-level
    inverse [Φ⁻¹] of Thm 5.12, both supplied by the SAFT discharge.
    We stage the full equality. *)

(* STAGING: discharge via M-SAFT, PLAN §13.1; then delete *)
Parameter tensor_normM :
  forall (B C : ICone.type Ar) (x : B) (y : C),
    cone_norm (linhom_fun (tensor_curry (icones_id Ar (B ⊗ C)) x) y)
    = cone_norm x * cone_norm y.

(** Local mirror of [tensor.v]'s pure tensor [x ⊗p y := τ_{B,C}(x)(y)],
    written here through the contract's primitives (the very idiom used
    by [tensor_normM] above).  Needed to state the pure-tensor
    computation laws (paper Eqs 5.2–5.4) of the structural isos below. *)
Local Notation "x '⊗p' y" :=
  (linhom_fun (tensor_curry (icones_id Ar (_ ⊗ _)) x) y)
  (at level 40, left associativity) : ring_scope.

(** ** Paper §5.5, Eq 5.2 — the associator [α]

    Paper Thm 5.15: from the two natural bijections built out of
    [Φ] and Thm 5.12 ([tensor_hom_iso]), Yoneda (Lemma 1.1) yields a
    natural iso [α_{A,B,C} : (A ⊗ B) ⊗ C ≅ A ⊗ (B ⊗ C)] in [ICones],
    characterised by [α((x ⊗ y) ⊗ z) = x ⊗ (y ⊗ z)] (Eq 5.2).

    The Yoneda construction needs representable-functor machinery the
    minimal contract does not expose; we therefore stage the iso
    together with its pure-tensor computation law.  All coherence
    (pentagon, triangle, hexagon) is then *derived* in [smcc.v] from
    these computation laws via the ternary extensionality [tensor_ext3]
    (Prop 5.14), exactly as in the paper. *)

(* STAGING: discharge via M-SAFT, PLAN §13.1; then delete (Eq 5.2) *)
Parameter tensor_assoc_iso :
  forall A B C : ICone.type Ar,
    icones_iso Ar ((A ⊗ B) ⊗ C) (A ⊗ (B ⊗ C)).

(* STAGING: discharge via M-SAFT, PLAN §13.1; then delete (Eq 5.2) *)
Parameter tensor_assocE :
  forall (A B C : ICone.type Ar) (x : A) (y : B) (z : C),
    iso_fwd (tensor_assoc_iso A B C) ((x ⊗p y) ⊗p z) = x ⊗p (y ⊗p z).

(** ** Paper §5.5, Eq 5.3 — the left and right unitors [λ], [ρ]

    Paper Thm 5.15: the obvious natural bijection [ICones(1, B ⊸ C) ≃
    ICones(B, C)] (resp. the natural iso [1 ⊸ C ≅ C]) yields natural
    isos [λ_B : 1 ⊗ B ≅ B] and [ρ_B : B ⊗ 1 ≅ B], characterised by
    [λ_B(u ⊗ x) = u · x = ρ_B(x ⊗ u)] (Eq 5.3), where [u ∈ 1 = R≥0]
    acts by scaling.  Staged with their computation laws; the unit is
    [cone_one_car Ar]. *)

(* STAGING: discharge via M-SAFT, PLAN §13.1; then delete (Eq 5.3) *)
Parameter tensor_lunit_iso :
  forall A : ICone.type Ar, icones_iso Ar (cone_one_car Ar ⊗ A) A.

(* STAGING: discharge via M-SAFT, PLAN §13.1; then delete (Eq 5.3) *)
Parameter tensor_lunitE :
  forall (A : ICone.type Ar) (u : cone_one_car Ar) (x : A),
    iso_fwd (tensor_lunit_iso A) (u ⊗p x) = precone_scale (c1_val u) x.

(* STAGING: discharge via M-SAFT, PLAN §13.1; then delete (Eq 5.3) *)
Parameter tensor_runit_iso :
  forall A : ICone.type Ar, icones_iso Ar (A ⊗ cone_one_car Ar) A.

(* STAGING: discharge via M-SAFT, PLAN §13.1; then delete (Eq 5.3) *)
Parameter tensor_runitE :
  forall (A : ICone.type Ar) (x : A) (u : cone_one_car Ar),
    iso_fwd (tensor_runit_iso A) (x ⊗p u) = precone_scale (c1_val u) x.

(** ** Paper §5.5, Eq 5.4 — the braiding [σ]

    Paper Thm 5.15: the natural iso of Lemma 5.5 yields a natural iso
    [σ_{A,B} : A ⊗ B ≅ B ⊗ A], characterised by [σ(x ⊗ y) = y ⊗ x]
    (Eq 5.4).  The involutivity [σ ∘ σ = id] and the symmetry hexagon
    are *derived* in [smcc.v] from this computation law. *)

(* STAGING: discharge via M-SAFT, PLAN §13.1; then delete (Eq 5.4) *)
Parameter tensor_braid_iso :
  forall A B : ICone.type Ar, icones_iso Ar (A ⊗ B) (B ⊗ A).

(* STAGING: discharge via M-SAFT, PLAN §13.1; then delete (Eq 5.4) *)
Parameter tensor_braidE :
  forall (A B : ICone.type Ar) (x : A) (y : B),
    iso_fwd (tensor_braid_iso A B) (x ⊗p y) = y ⊗p x.

End TensorInterface.

(** [tensor] and its data should print with [B] [C] explicit. *)
Arguments tensor {R} Ar B C.
Arguments tensor_curry {R Ar B C D}.
Arguments tensor_uncurry {R Ar B C D}.
Arguments tensor_curry_natural_post {R Ar B C D D'}.
Arguments tensor_hom_iso {R Ar} B C D.
Arguments tensor_normM {R Ar B C}.
Arguments tensor_assoc_iso {R Ar} A B C.
Arguments tensor_assocE {R Ar A B C}.
Arguments tensor_lunit_iso {R Ar} A.
Arguments tensor_lunitE {R Ar A}.
Arguments tensor_runit_iso {R Ar} A.
Arguments tensor_runitE {R Ar A}.
Arguments tensor_braid_iso {R Ar} A B.
Arguments tensor_braidE {R Ar A B}.
