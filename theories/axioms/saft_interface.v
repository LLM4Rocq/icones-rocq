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
Require Import Icones.icones.icone_cat.
Require Import Icones.homs.linhom.

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

End TensorInterface.

(** [tensor] and its data should print with [B] [C] explicit. *)
Arguments tensor {R} Ar B C.
Arguments tensor_curry {R Ar B C D}.
Arguments tensor_uncurry {R Ar B C D}.
