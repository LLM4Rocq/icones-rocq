(**md**************************************************************************)
(* # The exponential / SAFT adjunction (Paper §9)                              *)
(*                                                                            *)
(* This file exposes the linear/non-linear adjunction [E ⊣ Der] in its         *)
(* universal-arrow form as five symbols ([Bang], [nl], [lin], [lin_beta],     *)
(* [lin_unique]) — the §13.4 content the comonad milestone                    *)
(* [theories/exp/bang.v] consumes.                                           *)
(*                                                                            *)
(* The data are AXIOM-FREE theorems, supplied by the concrete SAFT             *)
(* construction [Icones.exp.bang_construct] (the exponential analog of the   *)
(* tensor's [tensor_construct.v], with the limit-preserving functor [Der] in  *)
(* place of [(C ⊸ −)]; Der's limit preservation is                             *)
(* [theories/stable/der_continuous.v], paper Thm 7.34).                        *)
(*                                                                            *)
(* The re-exported data is sealed [Strategy never], so the comonad / Seely    *)
(* proofs — calibrated to opaque symbols — go through unchanged under [/=].   *)
(*                                                                            *)
(* ## The universal-arrow presentation of [E ⊣ Der]                           *)
(*                                                                            *)
(*   - [Bang B = E B = !B] : the object map of [E] (= [wi_obj] over the       *)
(*     coseparator power [1^{SCones(B,1)}], [bang_construct.v]).               *)
(*   - [nl B : B → !B] in [SCones] : the unit [η_B], the universal nonlinear  *)
(*     map (the co-restriction of the universal tuple, via Der's equaliser    *)
(*     preservation).                                                          *)
(*   - [lin f : !B → C] in [ICones] : the unique linear factoriser (the SAFT  *)
(*     comma-category mediator, the coseparator-power reindex + pullback).     *)
(*                                                                            *)
(*   [lin_beta] (existence) and [lin_unique] (uniqueness) are the two halves  *)
(*   of the universal property of [nl_B], the natural bijection               *)
(*   [Θ : icones_hom (Bang B) C ≃ scones_hom B C].                            *)
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
Require Import Icones.stable.scones_cat.
Require Import Icones.exp.bang_construct.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section ExpInterface.
Variables (R : realType) (Ar : MeasSubcat R).

(** ** The exponential object former — Paper §9, [\Estab]/[\Excls]

    [Bang B = E B = !B], the SAFT construction of [bang_construct.v]. *)
Definition Bang (B : ICone.type Ar) : ICone.type Ar :=
  Icones_bang_construct.Bang B.

(** ** The unit / universal nonlinear map — Paper §9, [\Unistab_B] *)
Definition nl (B : ICone.type Ar) : scones_hom B (Bang B) :=
  Icones_bang_construct.nl B.

(** ** The linear factoriser — Paper §9, [Θ⁻¹]

    The unique [icones_hom (Bang B) C] factoring an [f : scones_hom B C]
    through [nl B]. *)
Definition lin (B C : ICone.type Ar) (f : scones_hom B C) :
    icones_hom Ar (Bang B) C :=
  Icones_bang_construct.lin f.

(** ** Universal property of [nl_B] (existence half) — Paper §9

    [ders (lin f) ∘ nl_B = f] in [SCones]. *)
Lemma lin_beta (B C : ICone.type Ar) (f : scones_hom B C) :
  scones_comp (ders (lin f)) (nl B) = f.
Proof. exact: (Icones_bang_construct.lin_beta_construct f). Qed.

(** ** Universal property of [nl_B] (uniqueness half) — Paper §9

    Any linear [h : !B → C] factoring [f] through the unit equals [lin f]. *)
Lemma lin_unique (B C : ICone.type Ar) (f : scones_hom B C)
    (h : icones_hom Ar (Bang B) C) :
  scones_comp (ders h) (nl B) = f -> h = lin f.
Proof. exact: (Icones_bang_construct.lin_unique_construct f h). Qed.

End ExpInterface.

(** [Bang] and the universal-property data print with their object
    arguments explicit. *)
Arguments Bang {R} Ar B.
Arguments nl {R Ar} B.
Arguments lin {R Ar B C}.
Arguments lin_beta {R Ar B C}.
Arguments lin_unique {R Ar B C}.

(** Seal the adjunction data so [simpl]/[/=] never unfolds it into the
    [wi_obj] SAFT construction underneath.  Both [Strategy never]
    (δ-priority) and [simpl never] (the [simpl] flag) are set, on the
    re-exports here AND on the underlying [bang_construct] constants, so
    the comonad ([bang.v]) and Seely ([seely.v]) proofs — calibrated to
    opaque symbols — build unchanged under [coqc]. *)
Strategy opaque
  [Bang nl lin
   Icones_bang_construct.Bang Icones_bang_construct.nl
   Icones_bang_construct.lin].
Arguments Bang {R} Ar B : simpl never.
Arguments nl {R Ar} B : simpl never.
Arguments lin {R Ar B C} f : simpl never.
Arguments Icones_bang_construct.Bang {R Ar} B : simpl never.
Arguments Icones_bang_construct.nl {R Ar} B : simpl never.
Arguments Icones_bang_construct.lin {R Ar B C} f : simpl never.
