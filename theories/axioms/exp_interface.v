(**md**************************************************************************)
(* # STAGING CONTRACT — the exponential / SAFT interface (Paper §9)          *)
(*                                                                            *)
(* PLAN.md §13.4 builds the exponential comonad [! = E ∘ Der] on [ICones]     *)
(* from the linear/non-linear adjunction [E ⊣ Der], itself a consequence of   *)
(* a PROVED Special Adjoint Functor Theorem (SAFT, §13.1).  We use the same   *)
(* *staged* layout as the tensor ([theories/axioms/saft_interface.v]):        *)
(*                                                                            *)
(*   1. (THIS FILE) declare the adjunction [E ⊣ Der] in its UNIVERSAL-ARROW   *)
(*      form — a handful of temporary [Parameter]s/[Axiom]s, exactly the      *)
(*      content the comonad milestone consumes;                               *)
(*   2. build the comonad [!] and its laws against this interface             *)
(*      ([theories/homs/bang.v]) — all as THEOREMS modulo this contract;      *)
(*   3. DISCHARGE the interface by proving SAFT (milestone M-SAFT, §13.1):    *)
(*      [E] is the left adjoint of [Der], after which every [Parameter]/      *)
(*      [Axiom] below becomes a theorem and THIS FILE IS DELETED.             *)
(*                                                                            *)
(* Every declaration here is therefore an INTENTIONAL, TEMPORARY AXIOM,       *)
(* flagged `STAGING: discharge via M-SAFT (E = left adjoint of Der by SAFT),  *)
(* PLAN §13.4; then delete`.  Nothing else in the project is left unproved,   *)
(* and there are no [Admitted].  In particular Theorem 6.5 (Skern → ICones    *)
(* fully faithful) is INDEPENDENT of this interface.                          *)
(*                                                                            *)
(* ## The universal-arrow presentation of [E ⊣ Der]                          *)
(*                                                                            *)
(* The functor [Der : ICones → SCones] is the dereliction inclusion [ders]    *)
(* of [theories/stable/scones_cat.v] — the identity on objects and on         *)
(* underlying functions, clamped off the unit ball.  Its left adjoint [E]     *)
(* exists by SAFT.  We present [E ⊣ Der] by its universal arrows:             *)
(*                                                                            *)
(*   - [Bang B = E B = !B] : the object map of [E] (the SAFT output; no       *)
(*     concrete carrier, mirroring Remark 5.1 for the tensor).                *)
(*   - [nl B : B → !B] in [SCones] : the unit [η_B] of the adjunction, the    *)
(*     "universal nonlinear map" on [B] (paper [\Unistab_B]).                  *)
(*   - [lin f : !B → C] in [ICones] : for each stable map [f : B → C], the    *)
(*     UNIQUE linear map factoring [f] through [nl_B] (paper [Θ⁻¹ f]).        *)
(*                                                                            *)
(* Together [lin_beta] (existence) and [lin_unique] (uniqueness) say that      *)
(* [lin f] is THE unique linear [h : !B → C] with [ders h ∘ nl_B = f], i.e.   *)
(* the natural bijection                                                      *)
(*                                                                            *)
(*   [Θ : icones_hom (Bang B) C  ≃  scones_hom B C],                          *)
(*   [Θ h := scones_comp (ders h) (nl B)],   inverse [lin].                   *)
(*                                                                            *)
(* This is exactly the §9 data the comonad [!] is built from in [bang.v].     *)
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

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section ExpInterface.
Variables (R : realType) (Ar : MeasSubcat R).

(** ** The exponential object former — Paper §9, [\Estab]/[\Excls]

    [Bang B = E B = !B] is the object map of the left adjoint [E] of the
    dereliction inclusion [Der = ders].  SAFT guarantees its existence but
    gives no concrete carrier (cf. Remark 5.1 for the tensor). *)

(* STAGING: discharge via M-SAFT (E = left adjoint of Der by SAFT),
   PLAN §13.4; then delete *)
Parameter Bang : ICone.type Ar -> ICone.type Ar.

(** ** The unit / universal nonlinear map — Paper §9, [\Unistab_B]

    [nl B : B → !B] in [SCones] is the unit [η_B] of [E ⊣ Der], the
    "universal nonlinear map" on [B]. *)

(* STAGING: discharge via M-SAFT (E = left adjoint of Der by SAFT),
   PLAN §13.4; then delete *)
Parameter nl : forall B : ICone.type Ar, scones_hom B (Bang B).

(** ** The linear factoriser — Paper §9, [Θ⁻¹]

    For each stable map [f : B → C], [lin f : !B → C] is the unique LINEAR
    map factoring [f] through [nl_B]. *)

(* STAGING: discharge via M-SAFT (E = left adjoint of Der by SAFT),
   PLAN §13.4; then delete *)
Parameter lin :
  forall B C : ICone.type Ar, scones_hom B C -> icones_hom Ar (Bang B) C.

(** ** Universal property of [nl_B] (existence half) — Paper §9

    [ders (lin f) ∘ nl_B = f] in [SCones]: the linear map [lin f] does
    factor the stable map [f] through the unit. *)

(* STAGING: discharge via M-SAFT (E = left adjoint of Der by SAFT),
   PLAN §13.4; then delete *)
Axiom lin_beta :
  forall (B C : ICone.type Ar) (f : scones_hom B C),
    scones_comp (ders (lin f)) (nl B) = f.

(** ** Universal property of [nl_B] (uniqueness half) — Paper §9

    Any linear [h : !B → C] factoring [f] through the unit equals [lin f].
    Together with [lin_beta] this is the natural bijection
    [Θ : icones_hom (Bang B) C ≃ scones_hom B C]. *)

(* STAGING: discharge via M-SAFT (E = left adjoint of Der by SAFT),
   PLAN §13.4; then delete *)
Axiom lin_unique :
  forall (B C : ICone.type Ar) (f : scones_hom B C)
         (h : icones_hom Ar (Bang B) C),
    scones_comp (ders h) (nl B) = f -> h = lin f.

End ExpInterface.

(** [Bang] and the universal-property data should print with their object
    arguments explicit. *)
Arguments Bang {R} Ar B.
Arguments nl {R Ar} B.
Arguments lin {R Ar B C}.
Arguments lin_beta {R Ar B C}.
Arguments lin_unique {R Ar B C}.
