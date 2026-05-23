(**md**************************************************************************)
(* # STAGING CONTRACT — the Seely isomorphisms (Paper §9)                     *)
(*                                                                            *)
(* PLAN.md §13.4 makes the exponential comonad [! = E ∘ Der] a *strong        *)
(* monoidal* comonad, turning [ICones] into a Seely category (Melliès).  The  *)
(* heart of this is the family of *Seely isomorphisms*                        *)
(*                                                                            *)
(*   Seely2_{B1,B2} : !B1 ⊗ !B2  ≅  !(B1 & B2)     (paper [\Seelyt])          *)
(*   Seely0         :        1   ≅  !⊤             (paper [\Seelyz])          *)
(*                                                                            *)
(* The paper (lines 7452–7513) CONSTRUCTS these isos via a chain of natural   *)
(* bijections [STAB/ICONES(...)≅...] and the representable-functor Yoneda     *)
(* lemma (Lemma [functor-yoneda-iso]) — exactly the Special-Adjoint-Functor   *)
(* / Yoneda machinery we do not yet expose at the element level.  We use the  *)
(* same *staged* layout as the tensor ([theories/axioms/saft_interface.v])    *)
(* and the exponential ([theories/axioms/exp_interface.v]):                   *)
(*                                                                            *)
(*   1. (THIS FILE) declare the EXISTENCE of [Seely2]/[Seely0] together with  *)
(*      their characterising equations on promotions of pure tensors — a      *)
(*      handful of temporary [Parameter]s/[Axiom]s, exactly the §13.4 content *)
(*      the Seely milestone consumes;                                         *)
(*   2. DERIVE the Seely-category coherence ([theories/homs/seely.v]) — all    *)
(*      as THEOREMS modulo this contract, via the [n=2] promotion             *)
(*      extensionality [tens_excl_charact] (paper Lemma                       *)
(*      [tens-excl-equal-charact]), exactly as [smcc.v] derives the SMC        *)
(*      coherence from the pure-tensor extensionality [tensor_ext];           *)
(*   3. DISCHARGE the interface by proving SAFT + the Yoneda construction      *)
(*      (M-SAFT, PLAN §13.1/§13.4), after which every [Parameter]/[Axiom]      *)
(*      below becomes a theorem and THIS FILE IS DELETED.                      *)
(*                                                                            *)
(* Every declaration here is therefore an INTENTIONAL, TEMPORARY AXIOM,       *)
(* flagged `STAGING: discharge via M-SAFT + Yoneda, PLAN §13.4; then delete`. *)
(*                                                                            *)
(* ## What is staged, and why it is the right contract                        *)
(*                                                                            *)
(* The paper itself stresses (line 7505): the equation                        *)
(*   [Seely2_{B1,B2}(x1! ⊗ x2!) = ⟨x1,x2⟩!]                                   *)
(* FULLY CHARACTERISES [Seely2] by Lemma [tens-excl-equal-charact] (the [n=2] *)
(* promotion extensionality, proved as [tens_excl_charact] in [seely.v]).     *)
(* So we stage exactly the data the paper keeps after Yoneda: the iso itself  *)
(* and its action on [x1! ⊗ x2!] (resp. [Seely0] and its action on [t]).      *)
(* Naturality of [Seely2] in both slots is part of the staged Yoneda output.  *)
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
Require Import Icones.stable.scones_cat.
Require Import Icones.stable.scones_ccc.
Require Import Icones.homs.linhom.
Require Import Icones.homs.icones_iso.
Require Import Icones.axioms.saft_interface.
Require Import Icones.homs.tensor.
Require Import Icones.axioms.exp_interface.
Require Import Icones.homs.bang.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section SeelyInterface.
Variables (R : realType) (Ar : MeasSubcat R).

(** Local mirror of the paper's tensor [⊗], pure tensor [⊗p], the
    exponential [!], the promotion [x!] and the binary product [&]. *)
Local Notation "B '⊗' C" := (tensor Ar B C)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '!'" := (prom x) (at level 2, format "x '!'").

(** ** Paper §9 — the binary Seely isomorphism [\Seelyt]

    From the chain of natural bijections (paper lines 7479–7492) ending
    in [ICONES(!B1 ⊗ !B2, !(B1 & B2))] and the Yoneda Lemma
    [functor-yoneda-iso], one obtains a natural iso

      [Seely2_{B1,B2} : !B1 ⊗ !B2 ≅ !(B1 & B2)]

    characterised (paper line 7501) by

      [Seely2(x1! ⊗ x2!) = ⟨x1,x2⟩!].

    SAFT/Yoneda is what we STAGE; we keep the iso and its
    characterisation, which by [tens_excl_charact] pins it down. *)

(* STAGING: discharge via M-SAFT + Yoneda, PLAN §13.4; then delete *)
Parameter Seely2 :
  forall B1 B2 : ICone.type Ar,
    icones_iso Ar (Bang Ar B1 ⊗ Bang Ar B2) (Bang Ar (sprod B1 B2)).

(** Paper line 7501: the characterising equation of [Seely2] on
    promotions of pure tensors.  By [tens_excl_charact] (the [n=2]
    promotion extensionality, paper Lemma [tens-excl-equal-charact])
    this single equation fully determines [Seely2]. *)

(* STAGING: discharge via M-SAFT + Yoneda, PLAN §13.4; then delete *)
Axiom Seely2E :
  forall (B1 B2 : ICone.type Ar) (x1 : B1) (x2 : B2),
    cone_norm x1 <= 1 -> cone_norm x2 <= 1 ->
    iso_fwd (Seely2 B1 B2) (x1! ⊗p x2!) = (sprod_pair x1 x2)!.

(** ** The binary-product bifunctor action [f1 & f2] — Paper §7.4

    The cartesian product [&] of [scones_ccc.v] acts on morphisms by
    [f1 & f2 = ⟨f1 ∘ π1, f2 ∘ π2⟩ : (B1 & B2) → (B1' & B2')], the
    pairing of the two projections post-composed with [f1]/[f2].  This
    is the action used in the Seely naturality square below; it is built
    from the already-exported [icones_proj]/[icones_tuple]. *)
Definition sprod_mor (B1 B2 B1' B2' : ICone.type Ar)
    (f1 : icones_hom Ar B1 B1') (f2 : icones_hom Ar B2 B2') :
    icones_hom Ar (sprod B1 B2) (sprod B1' B2') :=
  icones_tuple
    (fun b : bool =>
       if b as b0 return icones_hom Ar (sprod B1 B2) (sprod_fam B1' B2' b0)
       then icones_comp f1 (icones_proj true)
       else icones_comp f2 (icones_proj false)).

(** ** Naturality of [Seely2] — Paper §9, line 7494 (the Yoneda output)

    [Seely2] is a natural transformation in both arguments: the square

      [!B1 ⊗ !B2  --Seely2-->  !(B1 & B2)]
      [   |!f1 ⊗ !f2              |!(f1 & f2)]
      [!B1' ⊗ !B2' --Seely2--> !(B1' & B2')]

    commutes, i.e. [!(f1 & f2) ∘ Seely2_{B1,B2} = Seely2_{B1',B2'} ∘
    (!f1 ⊗ !f2)].  This is exactly the naturality the Yoneda lemma
    delivers (paper line 7494); we stage it in morphism form.  The
    bifunctor [!f1 ⊗ !f2] is the tensor action [tensor_mor]. *)

(* STAGING: discharge via M-SAFT + Yoneda, PLAN §13.4; then delete *)
Axiom Seely2_natural :
  forall (B1 B2 B1' B2' : ICone.type Ar)
         (f1 : icones_hom Ar B1 B1') (f2 : icones_hom Ar B2 B2'),
    icones_comp (bang_fmap (sprod_mor f1 f2)) (iso_fwd (Seely2 B1 B2)) =
    icones_comp (iso_fwd (Seely2 B1' B2'))
                (tensor_mor (bang_fmap f1) (bang_fmap f2)).

End SeelyInterface.

(** [Seely2] and its characterisation should print with the object
    arguments explicit. *)
Arguments Seely2 {R Ar} B1 B2.
Arguments Seely2E {R Ar B1 B2}.
Arguments sprod_mor {R Ar B1 B2 B1' B2'}.
Arguments Seely2_natural {R Ar B1 B2 B1' B2'}.
