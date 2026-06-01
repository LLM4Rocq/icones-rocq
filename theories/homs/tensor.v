(**md**************************************************************************)
(* # The tensor product on [ICones] — Paper §5.4–§5.5                         *)
(*                                                                            *)
(*   This file derives the tensor theory on [ICones].  The SAFT/tensor        *)
(*   universal property is delivered by the proved modules                    *)
(*   [tensor_construct.v]/[tensor_hom_iso.v]/[tensor_iso.v] (modules           *)
(*   [Icones_tensor_construct]/[..._hom_iso]/[..._iso]); these are [Export]ed *)
(*   below.  Everything here is a real proof; there are no unproved tensor    *)
(*   facts.                                                                   *)
(*                                                                            *)
(*   Deliverables (paper references):                                         *)
(*   - [tau B C] : the universal map [B → (C ⊸ B ⊗ C)] (Paper §5.4), and      *)
(*     the pure tensor [x ⊗ y := τ(x)(y)] with its computation lemma          *)
(*     [tensorE].                                                             *)
(*   - [tensor_curryE] : Paper Eq 5.1, [Φ(f)(x)(y) = f(x ⊗ y)], derived       *)
(*     from the concrete naturality [tensor_curry_natural_post].              *)
(*   - [tensor_mor f g] : the bifunctor action on morphisms (Paper §5.4),     *)
(*     with the identity law [tensor_mor_id].                                 *)
(*   - [tensor_hom_iso] re-exported as Thm 5.12; [tensor_curryK_inj] the      *)
(*     injectivity of [Φ].                                                    *)
(*   - [tensor_norm_le] : the [≤] half of Thm 5.13 (derived); [tensor_normM]  *)
(*     the full equality (Thm 5.13, proved in [tensor_hom_iso.v]).            *)
(*   - [tensor_ext] : Prop 5.14, pure-tensor extensionality (binary case).    *)
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
Require Import Icones.homs.linhom_functor.
Require Import Icones.homs.icones_iso.
Require Import Icones.homs.tensor_construct.
Require Import Icones.homs.tensor_hom_iso.
Require Import Icones.homs.tensor_iso.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

(** [Export] (not merely [Import]) the tensor symbols, so that every
    downstream consumer of [tensor.v] inherits them automatically:
    [tensor]/[tensor_curry]/[tensor_uncurry]/[tensor_curryK]/
    [tensor_curry_natural_post] from [Icones_tensor_construct],
    [tensor_normM] from [Icones_tensor_hom_iso], and the Thm 5.12 iso
    [tensor_hom_iso] together with the structural isos
    [tensor_assoc_iso]/[tensor_lunit_iso]/[tensor_runit_iso]/
    [tensor_braid_iso] (and their pure-tensor [...E] laws) from
    [Icones_tensor_iso].  [tensor.v]'s own [ptensor]/[tau]/[tensor_mor]
    are defined BELOW these [Export]s, so they shadow the modules'
    homonyms (notably the [ptensor] of [Icones_tensor_hom_iso]) in
    [tensor.v] and in every consumer. *)
Export Icones_tensor_construct.
Export Icones_tensor_hom_iso.
Export Icones_tensor_iso.

(** The exported [tensor] has [Ar] implicit; this file (and its downstream
    consumers) write [tensor Ar B C], so re-assert the signature with [Ar]
    explicit. *)
Arguments tensor {R} Ar B C.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section Tensor.
Variables (R : realType) (Ar : MeasSubcat R).

(** Local mirror of the paper's internal-hom [⊸] and tensor [⊗]. *)
Local Notation "C '⊸' D" := (linhom_car Ar C D)
  (at level 99, right associativity) : ring_scope.
Local Notation "B '⊗' C" := (tensor Ar B C)
  (at level 40, left associativity) : ring_scope.

(** ** The universal map [τ] and the pure tensor [⊗] — Paper §5.4

    [τ_{B,C} = Φ_{B,C,B⊗C}(Id_{B⊗C}) ∈ ICones(B, C ⊸ B ⊗ C)] is the
    image of the tensor identity under the hom-bijection.  The pure
    tensor of [x ∈ B] and [y ∈ C] is [x ⊗ y = τ_{B,C}(x)(y) ∈ B ⊗ C]. *)

Definition tau (B C : ICone.type Ar) : icones_hom Ar B (C ⊸ B ⊗ C) :=
  tensor_curry (icones_id Ar (B ⊗ C)).

(** The pure tensor [x ⊗ y ∈ B ⊗ C]. *)
Definition ptensor (B C : ICone.type Ar) (x : B) (y : C) : B ⊗ C :=
  linhom_fun (tau B C x) y.

Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.

(** Basic computation: the pure tensor is exactly [τ] applied. *)
Lemma ptensorE (B C : ICone.type Ar) (x : B) (y : C) :
  x ⊗p y = linhom_fun (tau B C x) y.
Proof. by []. Qed.

(** ** Paper Eq 5.1 — [Φ] factors through [τ]

    From the concrete naturality of [Φ] in [D]
    ([tensor_curry_natural_post]) with [h := f] and [f₀ := Id_{B⊗C}],
    [Φ(f) = Φ(f ∘ Id) = (C ⊸ f) ∘ Φ(Id) = (C ⊸ f) ∘ τ].  Pointwise this
    reads [Φ(f)(x)(y) = f(x ⊗ y)] (Eq 5.1). *)

Lemma tensor_curry_factor (B C D : ICone.type Ar)
    (f : icones_hom Ar (B ⊗ C) D) :
  tensor_curry f = icones_comp (linhom_post_icones f) (tau B C).
Proof.
rewrite /tau -[in LHS](icones_compIr f).
exact: (tensor_curry_natural_post f (icones_id Ar (B ⊗ C))).
Qed.

(** Paper Eq 5.1, pointwise: [Φ(f)(x)(y) = f(x ⊗ y)]. *)
Lemma tensor_curryE (B C D : ICone.type Ar)
    (f : icones_hom Ar (B ⊗ C) D) (x : B) (y : C) :
  linhom_fun (tensor_curry f x) y = f (x ⊗p y).
Proof.
rewrite (tensor_curry_factor f) /=.
by rewrite linhom_map_funE /ptensor /=.
Qed.

(** ** Bifunctoriality of [⊗] on morphisms — Paper §5.4

    Given [f : B1 → B2] and [g : C1 → C2], the bifunctor action
    [f ⊗ g : B1 ⊗ C1 → B2 ⊗ C2] is the uncurrying of
    [B1 →ᶠ B2 →ᵗ (C2 ⊸ B2 ⊗ C2) →ᵍ⊸ (C1 ⊸ B2 ⊗ C2)], i.e. precompose
    [τ_{B2,C2} ∘ f] in the hom-slot by [g]. *)

Definition tensor_mor (B1 B2 C1 C2 : ICone.type Ar)
    (f : icones_hom Ar B1 B2) (g : icones_hom Ar C1 C2) :
    icones_hom Ar (B1 ⊗ C1) (B2 ⊗ C2) :=
  tensor_uncurry
    (icones_comp (linhom_pre_icones g)
                 (icones_comp (tau B2 C2) f)).

(** Paper §5.4 (identity law): [Id_B ⊗ Id_C = Id_{B⊗C}]. *)
Lemma tensor_mor_id (B C : ICone.type Ar) :
  tensor_mor (icones_id Ar B) (icones_id Ar C) = icones_id Ar (B ⊗ C).
Proof.
rewrite /tensor_mor /tau.
rewrite (icones_compIr (tensor_curry (icones_id Ar (B ⊗ C)))).
rewrite (_ : linhom_pre_icones (icones_id Ar C) =
             icones_id Ar (C ⊸ B ⊗ C)); last first.
  by rewrite /linhom_pre_icones linhom_map_icones_id.
rewrite (icones_compIl (tensor_curry (icones_id Ar (B ⊗ C)))).
exact: tensor_curryK.
Qed.

(** ** Paper Theorem 5.12 — [Φ] is an iso of integrable cones

    [Φ_{B,C,D}] is an isomorphism [(B ⊗ C) ⊸ D ≃ B ⊸ (C ⊸ D)].  This
    is the element-level packaging [tensor_hom_iso] of [Φ], supplied by
    the contract; we re-export it under the paper name and record its
    forward/backward maps. *)

Definition tensor_hom_Phi (B C D : ICone.type Ar) :
    icones_iso Ar ((B ⊗ C) ⊸ D) (B ⊸ (C ⊸ D)) :=
  tensor_hom_iso B C D.

(** Forward and backward maps of the Thm 5.12 iso. *)
Definition tensor_hom_fwd (B C D : ICone.type Ar) :
    icones_hom Ar ((B ⊗ C) ⊸ D) (B ⊸ (C ⊸ D)) :=
  iso_fwd (tensor_hom_Phi B C D).

Definition tensor_hom_bwd (B C D : ICone.type Ar) :
    icones_hom Ar (B ⊸ (C ⊸ D)) ((B ⊗ C) ⊸ D) :=
  iso_bwd (tensor_hom_Phi B C D).

(** The forward map is bijective (Thm 5.12). *)
Lemma tensor_hom_fwd_bij (B C D : ICone.type Ar) :
  bijective (tensor_hom_fwd B C D).
Proof. exact: iso_fwd_bij. Qed.

(** ** Injectivity of [Φ] at the morphism level

    [Φ = tensor_curry] is injective because [tensor_uncurry] is a left
    inverse ([tensor_curryK]). *)
Lemma tensor_curry_inj (B C D : ICone.type Ar) :
  injective (@tensor_curry R Ar B C D).
Proof.
move=> f g Hfg.
by rewrite -(tensor_curryK f) Hfg tensor_curryK.
Qed.

(** ** Paper Theorem 5.13 — multiplicativity of the tensor norm

    The [≤] direction [‖x ⊗ y‖ ≤ ‖x‖ · ‖y‖] is derived from
    norm-decrease of [τ] (an [icones_hom], hence a [cones_hom]):
    [‖τ(x)‖ ≤ ‖x‖] and [‖τ(x)(y)‖ ≤ ‖τ(x)‖ · ‖y‖].  The full equality
    is the proved [tensor_normM] (from [tensor_hom_iso.v]; its converse
    needs the dual separation Prop 3.11 and the [Φ⁻¹] of Thm 5.12). *)

Lemma tensor_norm_le (B C : ICone.type Ar) (x : B) (y : C) :
  cone_norm (x ⊗p y) <= cone_norm x * cone_norm y.
Proof.
rewrite ptensorE.
apply: (@le_trans _ _ (cone_norm (tau B C x) * cone_norm y)).
  exact: (linhom_norm_apply_le (lexx (cone_norm (tau B C x))) y).
rewrite ler_wpM2r ?cone_norm_ge0 //.
exact: (cones_hom_norm_le1 (tau B C) x).
Qed.

(** Paper Theorem 5.13: [‖x ⊗ y‖ = ‖x‖ · ‖y‖] (via the proved
    [tensor_normM]). *)
Lemma tensor_normME (B C : ICone.type Ar) (x : B) (y : C) :
  cone_norm (x ⊗p y) = cone_norm x * cone_norm y.
Proof. exact: tensor_normM. Qed.

(** ** Paper Proposition 5.14 — pure-tensor extensionality (binary case)

    Two morphisms [f, g : B ⊗ C → D] that agree on every pure tensor
    [x ⊗ y] are equal.  Proof: it suffices to show [Φ(f) = Φ(g)] since
    [Φ = tensor_curry] is injective; and [Φ(f)(x)(y) = f(x ⊗ y) =
    g(x ⊗ y) = Φ(g)(x)(y)] by Eq 5.1 ([tensor_curryE]), so [Φ(f) =
    Φ(g)] by extensionality of [icones_hom] and [linhom]. *)

Lemma tensor_ext (B C D : ICone.type Ar)
    (f g : icones_hom Ar (B ⊗ C) D) :
  (forall (x : B) (y : C), f (x ⊗p y) = g (x ⊗p y)) -> f = g.
Proof.
move=> Hfg.
apply: tensor_curry_inj.
apply: icones_hom_eq => x /=.
apply: linhom_eq => y.
by rewrite !tensor_curryE Hfg.
Qed.

(** ** Paper Proposition 5.14 — ternary tree extensionality

    The instance of Prop 5.14 for the tree [⟨⟨∗,∗⟩,∗⟩], i.e. the left
    ternary tensor [(A ⊗ B) ⊗ C].  Two morphisms [f, g : (A ⊗ B) ⊗ C →
    D] that agree on every iterated pure tensor [(x ⊗ y) ⊗ z] are equal.

    Proof (paper's induction unfolded to depth two): by injectivity of
    [Φ] it suffices that [Φ(f) = Φ(g) : A ⊗ B → (C ⊸ D)]; by the binary
    [tensor_ext] it suffices these agree on pure tensors [x ⊗ y]; by
    [linhom_eq] it suffices they agree at every [z : C]; and by Eq 5.1
    ([tensor_curryE]) [Φ(f)(x ⊗ y)(z) = f((x ⊗ y) ⊗ z)], which equals
    the [g]-side by hypothesis. *)
Lemma tensor_ext3 (A B C D : ICone.type Ar)
    (f g : icones_hom Ar ((A ⊗ B) ⊗ C) D) :
  (forall (x : A) (y : B) (z : C),
     f ((x ⊗p y) ⊗p z) = g ((x ⊗p y) ⊗p z)) -> f = g.
Proof.
move=> Hfg.
apply: tensor_curry_inj.
apply: tensor_ext => x y.
apply: linhom_eq => z.
by rewrite !tensor_curryE Hfg.
Qed.

End Tensor.

Arguments tau {R Ar} B C.
Arguments ptensor {R Ar B C}.
Arguments tensor_mor {R Ar B1 B2 C1 C2}.
Arguments tensor_hom_Phi {R Ar} B C D.
Arguments tensor_hom_fwd {R Ar} B C D.
Arguments tensor_hom_bwd {R Ar} B C D.
Arguments tensor_curry_inj {R Ar B C D}.
Arguments tensor_ext {R Ar B C D}.
Arguments tensor_ext3 {R Ar A B C D}.

(** ** Bridge: [tensor_mor u id_C = tensor_mor_l u]

    The [tensor_construct.v] file defines [tensor_mor_l u :=
    tensor_uncurry (tau' B C ∘ u) : B' ⊗ C → B ⊗ C], used to express
    the naturality of [tensor_curry] in [B] ([tensor_curry_natural_B_post]).
    The [tensor.v] file defines [tensor_mor u id_C] via the bifunctor
    [tensor_mor f g := tensor_uncurry ((C₂ ⊸ g) ∘ τ ∘ f)] with [g := id_C].
    Both produce the same icones_hom; the equality is the one-step
    [linhom_pre_icones (icones_id _) = id] reduction plus the observation
    that [tau B C = tau' B C] (since [tau B C = tensor_curry (icones_id _)
    = (linhom_post_icones id) ∘ tau' B C = tau' B C]).

    This bridge is what lets the surface β-rule on [eD] route through the
    tensor-uncurry naturality of [tensor_construct.v]. *)
Section TensorMorIdEqMorL.
Variables (R : realType) (Ar : MeasSubcat R).

(** Concrete bridge: [tau = tau'] (the [tensor.v] universal map equals
    the [tensor_construct.v] SAFT-equaliser universal element). *)
Lemma tau_eq_tau' (B C : ICone.type Ar) :
  tau B C = tau' B C.
Proof.
rewrite /tau /tensor_curry linhom_post_id icones_compIl.
by [].
Qed.

(** [tensor_mor u id_C = tensor_mor_l u] for any [u : B' → B] and [C].
    Proof: both sides are uncurries; their curries coincide. *)
Lemma tensor_mor_id_eq_tensor_mor_l
    (B B' C : ICone.type Ar) (u : icones_hom Ar B' B) :
  tensor_mor u (icones_id Ar C) = tensor_mor_l u.
Proof.
apply: tensor_curry_inj.
rewrite tensor_mor_lK.
rewrite /tensor_mor.
rewrite (_ : linhom_pre_icones (icones_id Ar C) =
             icones_id Ar (linhom_car Ar C (tensor Ar B C))); last first.
  by rewrite /linhom_pre_icones linhom_map_icones_id.
rewrite icones_compIl.
rewrite tensor_uncurryK.
by rewrite tau_eq_tau'.
Qed.

End TensorMorIdEqMorL.

Arguments tau_eq_tau' {R Ar} B C.
Arguments tensor_mor_id_eq_tensor_mor_l {R Ar B B' C} u.

(** ** [tensor_uncurry] naturality in the LEFT (uncurried-domain) factor

    Companion to [tensor_curry_natural_B_post] (the curry side).  For
    [g : B → C ⊸ D] and [u : B' → B], pre-composing the uncurried map
    by [tensor_mor u id_C] is the same as uncurrying [g ∘ u]:
    [[
        tensor_uncurry g ∘ (u ⊗ id_C) = tensor_uncurry (g ∘ u).
    ]]
    Proof: by [tensor_curry_inj].  The curry of the LHS is
    [tensor_curry (tensor_uncurry g ∘ tensor_mor_l u)]
      [= tensor_curry (tensor_uncurry g) ∘ u]   ([tensor_curry_natural_B_post])
      [= g ∘ u]                                  ([tensor_uncurryK]);
    the curry of the RHS is [tensor_uncurryK].  Use
    [tensor_mor_id_eq_tensor_mor_l] to bridge [u ⊗ id_C] and [tensor_mor_l u]. *)
Lemma tensor_uncurry_natL (R : realType) (Ar : MeasSubcat R)
    (B B' C D : ICone.type Ar)
    (u : icones_hom Ar B' B) (g : icones_hom Ar B (linhom_car Ar C D)) :
  icones_comp (tensor_uncurry g)
              (tensor_mor u (icones_id Ar C)) =
  tensor_uncurry (icones_comp g u).
Proof.
apply: tensor_curry_inj.
rewrite tensor_mor_id_eq_tensor_mor_l.
rewrite (tensor_curry_natural_B_post u (tensor_uncurry g)).
by rewrite !tensor_uncurryK.
Qed.

Arguments tensor_uncurry_natL {R Ar B B' C D} u g.
