(** * Precones — Paper §2.1

    A precone is an [R≥0]-semimodule satisfying the cancellation and
    positivity axioms (Cancel), (Pos). The induced order
    [x ≤ y ⇔ ∃ z, y = x + z] is shown to be a partial order.

    Paper reference: §2.1 (page 1:9), Definition of precone.

    Design notes.
    - [R : realType] is a [Section] variable. The scalar type for the
      precone action is [{nonneg R}] (mathcomp's "non-negative real
      numbers" interval-inference type).
    - We chose to encode the algebraic axioms as their *bound-variable*
      forms (e.g. [precone_addA : associative precone_add]) rather than
      as universally quantified equalities, because this lets us reuse
      the mathcomp ssreflect lemmas about [associative], [commutative],
      [left_id] when proving instances.
    - We register *no* [Order.POrder] instance on [precone]: the cone
      order is a [Prop]-valued, non-decidable relation in general, while
      mathcomp's [Order.POrder] is built on a [bool]-valued [le]. We
      keep the derived order as a plain [Prop] relation [precone_le];
      M2+ may upgrade this in a classical-logic enrichment.
*)
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference.
From HB Require Import structures.

Require Import Icones.prelude.classical_extra.
Require Import Icones.prelude.nonneg_extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(** ** Precone mixin and structure *)

(** [isPrecone R P] bundles the [{nonneg R}]-semimodule operations plus
    (Cancel) and (Pos). All algebraic axioms are *equational* — only
    (Cancel) and (Pos) are conditional. *)
HB.mixin Record isPrecone (R : realType) (P : Type) := {
  precone_zero  : P;
  precone_add   : P -> P -> P;
  precone_scale : {nonneg R} -> P -> P;
  (* Algebraic axioms — Paper §2.1 (R≥0-semimodule structure) *)
  precone_addA : associative precone_add;
  precone_addC : commutative precone_add;
  precone_add0 : left_id precone_zero precone_add;
  precone_scale_DAr :
    forall r x y, precone_scale r (precone_add x y) =
                  precone_add (precone_scale r x) (precone_scale r y);
  precone_scale_DAl :
    forall (r s : {nonneg R}) x,
      precone_scale (r%:num + s%:num)%:nng x =
      precone_add (precone_scale r x) (precone_scale s x);
  precone_scale_A :
    forall (r s : {nonneg R}) x,
      precone_scale (r%:num * s%:num)%:nng x =
      precone_scale r (precone_scale s x);
  precone_scale_1 : forall x, precone_scale 1%:nng x = x;
  precone_scale_0r : forall r, precone_scale r precone_zero = precone_zero;
  precone_scale_0l : forall x, precone_scale 0%:nng x = precone_zero;
  (* (Cancel) — Paper §2.1 *)
  precone_cancel :
    forall x y z, precone_add x y = precone_add x z -> y = z;
  (* (Pos) — Paper §2.1 *)
  precone_pos :
    forall x y, precone_add x y = precone_zero ->
                x = precone_zero /\ y = precone_zero;
}.

#[short(type="preconeType")]
HB.structure Definition Precone (R : realType) := { P of isPrecone R P }.

(** ** Notation *)

Declare Scope precone_scope.
Delimit Scope precone_scope with PC.
Local Open Scope precone_scope.

Notation "0" := precone_zero : precone_scope.
Notation "x + y" := (precone_add x y) : precone_scope.
Notation "r *: x" := (precone_scale r x) (at level 40) : precone_scope.

(** ** Algebraic lemmas (derived) *)

Section PreconeLemmas.
Variable R : realType.
Variable P : preconeType R.
Implicit Types (x y z : P) (r s : {nonneg R}).

(** Commuted unit: [x + 0 = x]. *)
Lemma precone_addr0 x : x + 0 = x.
Proof. by rewrite precone_addC precone_add0. Qed.

(** (Pos) "left half": if [x + y = 0] then [x = 0]. *)
Lemma precone_posl x y : x + y = 0 -> x = 0.
Proof. by move/precone_pos => -[]. Qed.

(** Right cancellation, derived from [precone_cancel] via commutativity. *)
Lemma precone_cancelr x y z : y + x = z + x -> y = z.
Proof.
move=> H; apply: (@precone_cancel _ _ x y z).
by rewrite (precone_addC x y) (precone_addC x z) H.
Qed.

End PreconeLemmas.

(** ** The cone order — Paper §2.1 *)

Section PreconeOrder.
Variable R : realType.
Variable P : preconeType R.
Implicit Types (x y z : P).

(** Cone order: [x ≤ y] iff there exists [z] with [y = x + z].
    Paper §2.1: this is the *cone order* of [P]. *)
Definition precone_le (x y : P) : Prop := exists z : P, y = x + z.

(** Paper Lemma 2.9 (in spirit): reflexivity of the cone order. *)
Lemma precone_le_refl : forall x, precone_le x x.
Proof. by move=> x; exists 0; rewrite precone_addr0. Qed.

(** Paper Lemma 2.9 (in spirit): transitivity of the cone order. *)
Lemma precone_le_trans : forall y x z,
  precone_le x y -> precone_le y z -> precone_le x z.
Proof.
move=> y x z [u Huy] [v Hvz].
by exists (u + v); rewrite Hvz Huy precone_addA.
Qed.

(** Paper §2.1: by (Cancel) and (Pos), the cone order is antisymmetric.
    This is the statement that the derived order is a *partial* order. *)
Lemma precone_le_anti : forall x y,
  precone_le x y -> precone_le y x -> x = y.
Proof.
move=> x y [u Hxy] [v Hyx].
(* [x = y + v = (x + u) + v = x + (u + v)], so by (Cancel), [u + v = 0]. *)
have Hsum : x + (u + v) = x + 0.
  by rewrite precone_addA -Hxy -Hyx precone_addr0.
have /precone_posl Huz : u + v = 0 by exact: precone_cancel Hsum.
by rewrite Hxy Huz precone_addr0.
Qed.

(** Paper §2.1: addition is monotone on the right (and, by commutativity,
    on the left). *)
Lemma precone_add_le_r x y z :
  precone_le x y -> precone_le (x + z) (y + z).
Proof.
move=> [u Huy]; exists u.
by rewrite Huy -precone_addA (precone_addC u z) precone_addA.
Qed.

Lemma precone_add_le_l x y z :
  precone_le x y -> precone_le (z + x) (z + y).
Proof.
by move/(precone_add_le_r z); rewrite ![_ + z]precone_addC.
Qed.

(** Zero is the least element of the cone order. *)
Lemma precone_le0 x : precone_le 0 x.
Proof. by exists x; rewrite precone_add0. Qed.

(** Scalar multiplication is monotone in the vector argument. *)
Lemma precone_scale_le (r : {nonneg R}) x y :
  precone_le x y -> precone_le (r *: x) (r *: y).
Proof.
move=> [u Huy]; exists (r *: u).
by rewrite Huy precone_scale_DAr.
Qed.

End PreconeOrder.

(** ** Notation for the cone order *)

Notation "x <=p y" := (precone_le x y)
  (at level 70, no associativity) : precone_scope.
