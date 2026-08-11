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
    - (Normc) is encoded exactly as in the paper: a pure *existence*
      axiom [cone_normc] (every norm-bounded increasing chain has a
      least upper bound of norm ≤ 1).  The supremum itself is the
      TOTAL operator [cone_sup : (nat -> P) -> P], defined classically
      via [pselect]/[cid] on the least-upper-bound predicate
      [cone_lub] — garbage off-spec, exactly like mathcomp-analysis'
      [lim]/[sup]/[integral].  Chain-ness and norm-boundedness enter
      the theory as *lemma hypotheses* ([cone_lub_sup],
      [cone_norm_sup_ball], and the general-radius family of
      [omega_general.v]), never as operator arguments.  Because
      [cone_sup u] is characterised by its spec, rewriting between two
      suprema goes through [cone_supE] (uniqueness of the lub) instead
      of proof-irrelevance juggling on operator arguments.
    - The historical operator [cone_sup_ball u uch ub1] (which took
      the chain/bound *proofs* as arguments) is kept as a compatibility
      wrapper [:= cone_sup u], together with its three characterising
      lemmas [cone_sup_ball_ub] / [cone_sup_ball_lub] /
      [cone_sup_ball_norm] in their historical statements.
    - Instances are built through the [Cone_ofWitnessSup] factory,
      which has exactly the historical [isCone] field list (norm + four
      norm laws in their [Prop]-order shapes + witness-style
      [cone_sup_ball] operator + its three laws): existing instance
      constructions feed through it unchanged.

    We deliberately do *not* open [precone_scope] at the top level of
    this file: the bare [0] inside [cone_norm x = 0] must resolve in
    [ring_scope] (as [0 : R]), not in [precone_scope] (where it would
    be [precone_zero]). We write [precone_add] / [precone_scale]
    explicitly here in the mixin and switch to the notation inside
    lemma bodies as needed. *)
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference.
From HB Require Import structures.

Require Import Icones.prelude.nonneg_extra.
Require Import Icones.cones.precone.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(** ** Least upper bounds of chains, and the total supremum operator

    Defined over a bare [preconeType]: only the order is involved.
    [cone_sup] is total; its spec-side laws live below ([cone_supP],
    [cone_supE]) and in [omega_general.v]. *)

Section ChainSup.
Variable R : realType.
Variable P : preconeType R.
Implicit Types (u v : nat -> P) (x y : P).

(** Upper bounds of the range of a sequence. *)
Definition cone_ub u x : Prop := forall n, (u n <= x)%O.

(** Least upper bounds. *)
Definition cone_lub u x : Prop :=
  cone_ub u x /\ forall y, cone_ub u y -> (x <= y)%O.

(** A sequence *has* a supremum when the lub predicate is inhabited. *)
Definition has_cone_sup u : Prop := exists x, cone_lub u x.

(** The total supremum operator: the least upper bound when one
    exists, [0] otherwise. *)
Definition cone_sup u : P :=
  if pselect (has_cone_sup u) is left e then sval (cid e) else precone_zero.

(** Least upper bounds are unique (antisymmetry). *)
Lemma cone_lub_uniq u x y : cone_lub u x -> cone_lub u y -> x = y.
Proof.
move=> [xub xle] [yub yle]; apply: le_anti.
by rewrite xle// yle.
Qed.

(** [cone_sup u] satisfies the spec whenever the spec is satisfiable. *)
Lemma cone_supP u : has_cone_sup u -> cone_lub u (cone_sup u).
Proof.
move=> e; rewrite /cone_sup; case: pselect => [e'|//].
exact: (svalP (cid e')).
Qed.

(** The workhorse identification lemma: any concrete least upper bound
    IS [cone_sup u].  This is what replaces the historical
    proof-irrelevance juggling on [cone_sup_ball] arguments. *)
Lemma cone_supE u x : cone_lub u x -> cone_sup u = x.
Proof.
move=> lx; apply: (cone_lub_uniq _ lx); apply: cone_supP.
exact: (ex_intro _ x lx).
Qed.

(** [cone_sup] only depends on the sequence pointwise. *)
Lemma eq_cone_sup u v : u =1 v -> cone_sup u = cone_sup v.
Proof. by move/funext->. Qed.

End ChainSup.

Arguments cone_ub {R P} u x.
Arguments cone_lub {R P} u x.
Arguments has_cone_sup {R P} u.
Arguments cone_sup {R P} u.

(** ** Cone mixin and structure *)

(** [isCone R P] adds a norm to a [preconeType R], plus the five norm
    axioms. The "ω-completeness of the unit ball" condition (Normc) is
    the pure existence axiom [cone_normc], stated in mathcomp house
    style: chains are [{homo u : n m / (n <= m)%N >-> (n <= m)%O}],
    all side conditions are hypotheses. *)
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
  (* (Normp) — Paper §2.1: x ≤ y ⇒ ‖x‖ ≤ ‖y‖, order-monotonicity,
     with the boolean cone order as hypothesis.  The [Prop]-order
     form is the derived view [cone_normp] below. *)
  cone_norm_le : forall (x y : P),
    (x <= y)%O -> cone_norm x <= cone_norm y;
  (* (Normc) — Paper §2.1, ω-completeness of the unit ball: every
     increasing chain in the unit ball has a least upper bound, of
     norm ≤ 1.  A pure existence statement, as in the paper. *)
  cone_normc : forall (u : nat -> P),
    {homo u : n m / (n <= m)%N >-> (n <= m)%O} ->
    (forall n, cone_norm (u n) <= 1) ->
    exists2 x : P, cone_lub u x & cone_norm x <= 1;
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

(** (Normp) in its historical [Prop]-order shape, as a derived view. *)
Lemma cone_normp x y : precone_le x y -> cnorm x <= cnorm y.
Proof. by move=> /precone_leP/cone_norm_le. Qed.

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
by have := cone_normp H; rewrite cone_norm0.
Qed.

(** Paper §2.1: (Normz) packaged as an "if and only if". *)
Lemma cone_normz_iff x : cnorm x = 0 <-> x = precone_zero.
Proof.
split=> [/cone_normz//|->]; exact: cone_norm0.
Qed.

End ConeLemmas.

(** [cone_normp] keeps its historical argument profile: the two
    operands stay explicit ([cone_normp _ _ H] call sites). *)
Arguments cone_normp {R P} x y.

(** ** The unit-ball supremum laws

    (Normc), unpacked onto the total operator [cone_sup]: for a
    unit-ball chain, [cone_sup u] is the least upper bound and has
    norm ≤ 1.  The general-radius forms (bound [M] instead of [1])
    live in [omega_general.v]. *)

Section ConeSupBallLaws.
Variable R : realType.
Variable P : coneType R.
Implicit Types u : nat -> P.

Lemma cone_lub_sup u :
  {homo u : n m / (n <= m)%N >-> (n <= m)%O} ->
  (forall n, cnorm (u n) <= 1) ->
  cone_lub u (cone_sup u).
Proof.
move=> uch ub1; apply: cone_supP.
have [x xlub _] := cone_normc _ uch ub1.
exact: (ex_intro _ x xlub).
Qed.

Lemma cone_norm_sup_ball u :
  {homo u : n m / (n <= m)%N >-> (n <= m)%O} ->
  (forall n, cnorm (u n) <= 1) ->
  cnorm (cone_sup u) <= 1.
Proof.
move=> uch ub1; have [x xlub xn] := cone_normc _ uch ub1.
by rewrite (cone_supE xlub).
Qed.

End ConeSupBallLaws.

(** ** Historical interface: [cone_sup_ball] and its laws

    The pre-rework mixin materialised (Normc) as an operator taking
    the chain/bound *proofs* as arguments.  We keep it as a wrapper
    around [cone_sup] (the proofs are phantom), with the three
    characterising lemmas in their historical statements — so all
    existing consumers keep compiling, and any two [cone_sup_ball]s
    on the same chain are now *definitionally* equal. *)

Section ConeSupBallCompat.
Variable R : realType.
Variable P : coneType R.
Implicit Types u : nat -> P.

Definition cone_sup_ball u
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, cnorm (u n) <= 1) : P := cone_sup u.

Lemma cone_sup_ball_ub u
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, cnorm (u n) <= 1) n :
  precone_le (u n) (cone_sup_ball uch ub1).
Proof.
apply/precone_leP.
exact: (proj1 (cone_lub_sup (precone_chain_homo uch) ub1)).
Qed.

Lemma cone_sup_ball_lub u
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, cnorm (u n) <= 1) y :
  (forall n, precone_le (u n) y) ->
  precone_le (cone_sup_ball uch ub1) y.
Proof.
move=> uy; apply/precone_leP.
apply: (proj2 (cone_lub_sup (precone_chain_homo uch) ub1)) => n.
exact/precone_leP.
Qed.

Lemma cone_sup_ball_norm u
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, cnorm (u n) <= 1) :
  cnorm (cone_sup_ball uch ub1) <= 1.
Proof. exact: cone_norm_sup_ball (precone_chain_homo uch) ub1. Qed.

(** The canonical bridge to the new interface: [cone_sup_ball] is the
    total operator [cone_sup] — the witnesses are phantom.  Migrating
    a call site to the new lemma shapes starts with this rewrite. *)
Lemma cone_sup_ball_supE u
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, cnorm (u n) <= 1) :
  cone_sup_ball uch ub1 = cone_sup u.
Proof. by []. Qed.

(** The [Prop]-shaped identification lemma: [cone_sup_ball] equals any
    concrete least upper bound.  Under the historical encoding the
    operator *reduced* to the instance's concrete construction; that
    definitional link is gone (the operator is now spec-based), and
    every proof that relied on it instead rewrites with this lemma,
    fed with the concrete construction's ub/lub laws. *)
Lemma cone_sup_ballE u
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, cnorm (u n) <= 1) (s : P) :
  (forall n, precone_le (u n) s) ->
  (forall y, (forall n, precone_le (u n) y) -> precone_le s y) ->
  cone_sup_ball uch ub1 = s.
Proof.
move=> sub slub; apply: cone_supE; split=> [n|y uby].
  exact/precone_leP.
apply/precone_leP; apply: slub => n; exact/precone_leP.
Qed.

End ConeSupBallCompat.

Arguments cone_sup_ball {R P} u uch ub1.
Arguments cone_sup_ball_supE {R P} u uch ub1.
Arguments cone_sup_ballE {R P} u uch ub1 s.
Arguments cone_sup_ball_ub {R P} u uch ub1 n.
Arguments cone_sup_ball_lub {R P} u uch ub1 y.
Arguments cone_sup_ball_norm {R P} u uch ub1.

(** ** The [Cone_ofWitnessSup] factory — the historical interface

    Builds [isCone] from the pre-rework field list: the four norm laws
    in their historical shapes ((Normp) with the [Prop] order) plus a
    witness-style supremum operator [cone_sup_ball] with its three
    characterising laws.  Existing instance sites keep their concrete
    constructions and proofs, and only rename [isCone.Build] to
    [Cone_ofWitnessSup.Build]. *)
HB.factory Record Cone_ofWitnessSup (R : realType) P of Precone R P := {
  cone_norm : P -> R;
  cone_normh : forall (r : {nonneg R}) (x : P),
    cone_norm (precone_scale r x) = r%:num * cone_norm x;
  cone_normz : forall (x : P), cone_norm x = 0 -> x = precone_zero;
  cone_normt : forall (x y : P),
    cone_norm (precone_add x y) <= cone_norm x + cone_norm y;
  cone_normp : forall (x y : P),
    precone_le x y -> cone_norm x <= cone_norm y;
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

HB.builders Context R P of Cone_ofWitnessSup R P.

Local Lemma norm_le (x y : P) :
  (x <= y)%O -> cone_norm x <= cone_norm y.
Proof. by move=> /precone_leP/cone_normp. Qed.

Local Lemma normc (u : nat -> P) :
  {homo u : n m / (n <= m)%N >-> (n <= m)%O} ->
  (forall n, cone_norm (u n) <= 1) ->
  exists2 x : P, cone_lub u x & cone_norm x <= 1.
Proof.
move=> uch ub1.
have uchp := homo_precone_chain uch.
exists (cone_sup_ball uchp ub1); last exact: cone_sup_ball_norm.
split=> [n|y uby].
  exact/precone_leP/cone_sup_ball_ub.
apply/precone_leP; apply: cone_sup_ball_lub => n.
exact/precone_leP.
Qed.

HB.instance Definition _ :=
  isCone.Build R P cone_normh cone_normz cone_normt norm_le normc.

HB.end.
