(** * Cones — Paper §2.1

    A cone is a precone equipped with a norm satisfying (Normh)
    homogeneity, (Normz) zero-detection, (Normt) sub-additivity,
    (Normp) order-monotonicity, and (Normc) ω-completeness of the unit
    ball.

    Paper reference: §2.1 (page 1:9), Definition of cone.

    Design notes.
    - The norm is valued in [R], not in [{nonneg R}]. We require
      [cone_norm0] (positivity at 0) implicitly via (Normh) with
      [r = 0]; non-negativity at every point follows as
      [cone_norm_ge0] below from (Normh) and (Normp).
    - (Normc) is encoded as a concrete [cone_sup_ball] operator (not as
      a sigma-type) for the same reason discussed in
      [Icones.prelude.omegacpo]: downstream proofs need direct access
      to the supremum. The operator takes a sequence [u : nat -> P], a
      monotonicity witness in the cone order, and a norm-bound witness;
      it returns an element [sup_ball u … : P] with the three
      characterising properties.
*)
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference.
From HB Require Import structures.

Require Import Icones.prelude.classical_extra.
Require Import Icones.prelude.nonneg_extra.
Require Import Icones.prelude.omegacpo.
Require Import Icones.cones.precone.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(** ** Cone mixin and structure *)

(** [isCone R P] adds a norm to a [preconeType R], plus the five norm
    axioms. The "ω-completeness of the unit ball" condition (Normc) is
    materialised as an operator [cone_sup_ball] plus its three
    characterising lemmas.

    We deliberately do *not* open [precone_scope] at the top level of
    this file: the bare [0] inside [cone_norm x = 0] must resolve in
    [ring_scope] (as [0 : R]), not in [precone_scope] (where it would
    be [precone_zero]). We write [precone_add] / [precone_scale]
    explicitly here in the mixin and switch to the notation inside
    lemma bodies as needed. *)
HB.mixin Record isCone (R : realType) P of Precone R P := {
  cone_norm : P -> R;
  (* (Normh) — Paper §2.1: ‖λ·x‖ = λ·‖x‖, scalar homogeneity *)
  cone_normh : forall (r : {nonneg R}) (x : P),
    cone_norm (precone_scale r x) = r%:num * cone_norm x;
  (* (Normz) — Paper §2.1: ‖x‖ = 0 ⇒ x = 0, zero-detection.
     The converse direction follows from (Normh) with r = 0
     — see [cone_norm0] below — and is repackaged as
     [cone_normz_iff] *)
  cone_normz : forall (x : P), cone_norm x = 0 -> x = precone_zero;
  (* (Normt) — Paper §2.1: ‖x + y‖ ≤ ‖x‖ + ‖y‖, sub-additivity *)
  cone_normt : forall (x y : P),
    cone_norm (precone_add x y) <= cone_norm x + cone_norm y;
  (* (Normp) — Paper §2.1: x ≤ y ⇒ ‖x‖ ≤ ‖y‖, order-monotonicity *)
  cone_normp : forall (x y : P),
    precone_le x y -> cone_norm x <= cone_norm y;
  (* (Normc) — Paper §2.1, ω-completeness of the unit ball.
     [cone_sup_ball u uch ub1] is the supremum of an increasing chain
     [u] in [B_P]; its three characterising properties below say it is
     an upper bound, the least one, and its norm is ≤ 1. *)
  cone_sup_ball :
    forall (u : nat -> P),
      (forall n, precone_le (u n) (u n.+1)) ->
      (forall n, cone_norm (u n) <= 1) ->
      P;
  cone_sup_ball_ub :
    forall (u : nat -> P)
           (uch : forall n, precone_le (u n) (u n.+1))
           (ub1 : forall n, cone_norm (u n) <= 1) n,
      precone_le (u n) (cone_sup_ball u uch ub1);
  cone_sup_ball_lub :
    forall (u : nat -> P)
           (uch : forall n, precone_le (u n) (u n.+1))
           (ub1 : forall n, cone_norm (u n) <= 1) y,
      (forall n, precone_le (u n) y) ->
      precone_le (cone_sup_ball u uch ub1) y;
  cone_sup_ball_norm :
    forall (u : nat -> P)
           (uch : forall n, precone_le (u n) (u n.+1))
           (ub1 : forall n, cone_norm (u n) <= 1),
      cone_norm (cone_sup_ball u uch ub1) <= 1;
}.

#[short(type="coneType")]
HB.structure Definition Cone (R : realType) :=
  { P of isCone R P & Precone R P }.

(** ** Abbreviation *)

(** [cnorm] is a short alias for [cone_norm].  We deliberately do *not*
    introduce a notation like [‖x‖] or [`|x|]: the former has fragile
    parser interaction in scopes (we hit "Syntax error: term level 99
    expected after '‖'"), the latter collides with mathcomp-analysis's
    absolute-value notation, and any project-local notation would have
    to live inside its own scope which a downstream user must then
    remember to open.  [cnorm] is a single-token abbreviation that
    composes with existing scopes without surprises. *)
Notation cnorm := cone_norm.

(** ** Derived lemmas *)

Section ConeLemmas.
Variable R : realType.
Variable P : coneType R.
Implicit Types (x y z : P).

(** Paper §2.1, (Normh) at [r = 0]: [cone_norm 0 = 0]. *)
Lemma cone_norm0 : cnorm (precone_zero : P) = 0.
Proof.
have H := cone_normh 0%:nng (precone_zero : P).
rewrite /= mul0r in H.
by rewrite -H precone_scale_0l.
Qed.

(** Paper §2.1, (Normh) + (Normp): [cone_norm x >= 0] for every [x].
    Indeed [0 ≤p x] always (Lemma [precone_le0]), so by (Normp)
    [cone_norm 0 ≤ cone_norm x]; and [cone_norm 0 = 0] by
    [cone_norm0]. *)
Lemma cone_norm_ge0 x : 0 <= cnorm x.
Proof.
have H : precone_le precone_zero x by exact: precone_le0.
by have := cone_normp _ _ H; rewrite cone_norm0.
Qed.

(** Paper §2.1: (Normz) packaged as an "if and only if". *)
Lemma cone_normz_iff x : cnorm x = 0 <-> x = precone_zero.
Proof.
split=> [/cone_normz//|->]; exact: cone_norm0.
Qed.

(** The unit ball [B_P] of a cone: characterised by [cone_norm x <= 1]. *)
Definition cone_unit_ball : pred P := fun x => cnorm x <= 1.

Lemma cone_unit_ball0 : cone_unit_ball (precone_zero : P).
Proof. by rewrite /cone_unit_ball cone_norm0 ler01. Qed.

(** [cone_sup_ball] lives in the unit ball. *)
Lemma cone_sup_ball_in_unit
  (u : nat -> P)
  (uch : forall n, precone_le (u n) (u n.+1))
  (ub1 : forall n, cnorm (u n) <= 1) :
  cone_unit_ball (cone_sup_ball u uch ub1).
Proof. exact: cone_sup_ball_norm. Qed.

End ConeLemmas.
