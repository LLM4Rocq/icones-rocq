(**md**************************************************************************)
(* # Seely-structure definitions (Paper §9)                                    *)
(*                                                                            *)
(* PLAN.md §13.4 makes the exponential comonad [! = E ∘ Der] a *strong        *)
(* monoidal* comonad, turning [ICones] into a Seely category (Melliès).  The  *)
(* heart of this is the family of *Seely isomorphisms*                        *)
(*                                                                            *)
(*   Seely2_{B1,B2} : !B1 ⊗ !B2  ≅  !(B1 & B2)     (paper [\Seelyt])          *)
(*   Seely0         :        1   ≅  !⊤             (paper [\Seelyz])          *)
(*                                                                            *)
(* Both isos are PROVED in [theories/homs/seely.v]:                            *)
(*                                                                            *)
(*   - [Seely0] / [Seely0E] (the unit iso, paper [\Seelyz]) is built by the   *)
(*     contravariant Yoneda lemma [co_yoneda_iso] on the natural             *)
(*     hom-bijection [ICones(1, C) ≃ ICones(!⊤, C)];                          *)
(*   - [Seely2] / [Seely2E] / [Seely2_natural] (the binary iso, paper        *)
(*     [\Seelyt]) is built by the paper's chain of natural-in-[C] bijections  *)
(*     (content.tex ~7482–7506), realized at the element level via the       *)
(*     [E ⊣ Der] adjunction [Θ]/[lin], the [SCones] CCC [curry]/[Ev], the    *)
(*     tensor–hom iso / braiding, and — at exactly ONE step — paper Lemma 9.4 *)
(*     [stab_lin_swap].  Bijectivity is the [n=2] promotion extensionality    *)
(*     [tens_excl_charact]; [Seely2E] is the chain's pure-tensor computation; *)
(*     [Seely2_natural] follows from [Seely2E] + [tens_excl_charact].         *)
(*                                                                            *)
(* What this file provides are the bare definitions the Seely structure       *)
(* needs: the terminal cone [⊤ = Stop] (and its terminality) and the           *)
(* binary-product bifunctor action [f1 & f2 = sprod_mor].                     *)
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
Require Import Icones.homs.tensor.
Require Import Icones.homs.exp_adjunction.
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

    The iso and its characterisation are PROVED in [theories/homs/seely.v]
    (the paper's natural-in-[C] bijection chain of content.tex ~7482,
    folded to the element level via the [E ⊣ Der] adjunction [Θ]/[lin],
    the [SCones] CCC [curry]/[Ev], [tensor_hom_iso] / the braiding, and —
    at exactly one step — paper Lemma 9.4 [stab_lin_swap]); by
    [tens_excl_charact] the characterisation pins the iso down. *)

(** ** The terminal integrable cone [⊤] — Paper §9 ([\Stop])

    The Seely *unit* iso relates the monoidal unit [1] to [!⊤], where
    [⊤] is the TERMINAL object of [ICones].  The terminal object is the
    empty product [icones_prod] over [Empty_set]: a point is a (vacuous)
    section [forall e : Empty_set, _], so by [cones_prod_eq] any two
    points are equal — there is a single point, the product zero, and a
    unique morphism into [⊤] from every object. *)
Definition Stop : ICone.type Ar :=
  icones_prod (fun e : Empty_set => match e return ICone.type Ar with end).

(** [⊤] is terminal *as a cone*: any two of its points are equal (the
    section quantifier ranges over [Empty_set]). *)
Lemma Stop_eq (s t : Stop) : s = t.
Proof. by apply: cones_prod_eq => -[]. Qed.

(** Hence every point of [⊤] is its zero. *)
Lemma Stop_is0 (s : Stop) : s = (precone_zero : Stop).
Proof. exact: Stop_eq. Qed.

(** The unique morphism into [⊤] from any object: the empty tuple. *)
Definition Stop_mor (B : ICone.type Ar) : icones_hom Ar B Stop :=
  icones_tuple (fun e : Empty_set => match e return icones_hom Ar B _ with end).

(** Its uniqueness: any [h : B → ⊤] equals [Stop_mor] (both land in the
    single point of [⊤]). *)
Lemma Stop_mor_unique (B : ICone.type Ar) (h : icones_hom Ar B Stop) :
  h = Stop_mor B.
Proof. by apply: icones_hom_eq => x; exact: Stop_eq. Qed.

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

(** ** Naturality of [Seely2] — Paper §9, line 7494

    [Seely2] is a natural transformation in both arguments; the square
    [!(f1 & f2) ∘ Seely2_{B1,B2} = Seely2_{B1',B2'} ∘ (!f1 ⊗ !f2)] is
    PROVED as [Seely2_natural] in [theories/homs/seely.v] (directly from
    [Seely2E] via the [n=2] promotion extensionality [tens_excl_charact]). *)

(** ** Paper §9 — the unit Seely isomorphism [\Seelyz]

    The unit Seely iso [Seely0 : 1 ≅ !⊤] and its characterisation
    [Seely0(t) = t·(0!)] are PROVED in [theories/homs/seely.v] (via the
    contravariant Yoneda lemma [co_yoneda_iso] on the natural
    hom-bijection [ICones(1,C) ≃ ICones(!⊤,C)]). *)

End SeelyInterface.

Arguments sprod_mor {R Ar B1 B2 B1' B2'}.
Arguments Stop {R} Ar.
Arguments Stop_eq {R Ar}.
Arguments Stop_is0 {R Ar}.
Arguments Stop_mor {R Ar} B.
Arguments Stop_mor_unique {R Ar B}.
