(** * Precones — Paper §2.1

    A precone is an [R≥0]-semimodule satisfying the cancellation and
    positivity axioms (Cancel), (Pos). The induced order
    [x ≤ y ⇔ ∃ z, y = x + z] is a partial order, registered as a
    mathcomp [Order.POrder] instance on the dedicated display
    [precone_display].

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
    - The cone order is registered as a boolean [Order.POrder] on the
      dedicated display [precone_display], via boolp classical
      reflection: [(x <= y)%O = `[< exists z, y = x + z >]] (field
      [precone_le_def] of the mixin).  This makes the whole mathcomp
      order theory ([lexx], [le_trans], [le_anti], …) available on any
      [preconeType].  The [Prop]-valued relation [precone_le]
      (notation [x <=p y]) is kept as the definitional form, connected
      to the boolean order by the reflect view [precone_leP].
    - Instances are built through the [isPrecone] factory, which has
      exactly the historical field list (three operations + eleven
      axioms): it derives the [Order.POrder] instance from (Cancel) /
      (Pos).  The factory requires a [Choice] structure on the carrier
      (mathcomp partial orders sit above [choiceType]); carriers
      without a canonical one get it classically via boolp's
      [gen_eqMixin] / [gen_choiceMixin].
*)
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference.
From HB Require Import structures.

Require Import Icones.prelude.nonneg_extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(** ** The precone display *)

(** Dedicated display for the cone-order hierarchy, in the style of
    mathcomp-analysis' [ereal_display]. *)
Fact precone_display : Order.disp_t. Proof. by []. Qed.

(** ** Precone mixin and structure *)

(** [POrder_isPrecone R P] bundles the [{nonneg R}]-semimodule
    operations plus (Cancel) and (Pos), over a partial order on
    [precone_display] that is pinned to the cone order by
    [precone_le_def]. All algebraic axioms are *equational* — only
    (Cancel) and (Pos) are conditional.  Instances should go through
    the [isPrecone] factory below, which has the historical field
    list and derives the order. *)
HB.mixin Record POrder_isPrecone (R : realType) P
    of Order.POrder precone_display P := {
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
  (* The boolean order is the cone order — Paper §2.1 *)
  precone_le_def :
    forall x y : P,
      (x <= y)%O = `[< exists z, y = precone_add x z >];
}.

#[short(type="preconeType")]
HB.structure Definition Precone (R : realType) :=
  { P of POrder_isPrecone R P & Order.POrder precone_display P }.

(** ** The [isPrecone] factory — the historical interface

    Exactly the pre-Order field list (operations + algebra + (Cancel)
    + (Pos)); the [Order.POrder] instance and [precone_le_def] are
    derived.  This keeps every existing [isPrecone.Build] site
    compiling unchanged (up to a [Choice] structure on the carrier). *)
HB.factory Record isPrecone (R : realType) P of Choice P := {
  precone_zero  : P;
  precone_add   : P -> P -> P;
  precone_scale : {nonneg R} -> P -> P;
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
  precone_cancel :
    forall x y z, precone_add x y = precone_add x z -> y = z;
  precone_pos :
    forall x y, precone_add x y = precone_zero ->
                x = precone_zero /\ y = precone_zero;
}.

HB.builders Context R P of isPrecone R P.

(** The boolean cone order, by classical reflection. *)
Local Definition ple (x y : P) : bool :=
  `[< exists z, y = precone_add x z >].

Local Lemma ple_refl : reflexive ple.
Proof.
move=> x; apply/asboolP; exists precone_zero.
by rewrite precone_addC precone_add0.
Qed.

Local Lemma ple_anti : antisymmetric ple.
Proof.
move=> x y /andP[/asboolP[u yE] /asboolP[v xE]].
(* [x = y + v = (x + u) + v = x + (u + v)], so by (Cancel), [u + v = 0]. *)
have Hsum : precone_add x (precone_add u v) = precone_add x precone_zero.
  by rewrite precone_addA -yE -xE precone_addC precone_add0.
have /precone_cancel uv0 := Hsum.
have [u0 _] := precone_pos uv0.
by rewrite yE u0 precone_addC precone_add0.
Qed.

Local Lemma ple_trans : transitive ple.
Proof.
move=> y x z /asboolP[u yE] /asboolP[v zE]; apply/asboolP.
by exists (precone_add u v); rewrite zE yE precone_addA.
Qed.

HB.instance Definition _ :=
  Order.Le_isPOrder.Build precone_display P ple_refl ple_anti ple_trans.

HB.instance Definition _ :=
  POrder_isPrecone.Build R P precone_addA precone_addC precone_add0
    precone_scale_DAr precone_scale_DAl precone_scale_A
    precone_scale_1 precone_scale_0r precone_scale_0l
    precone_cancel precone_pos (fun x y => erefl).

HB.end.

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

(** ** The cone order — Paper §2.1

    [precone_le] is the [Prop]-valued definitional form of the cone
    order; the boolean form is the [Order.POrder] operation
    [(x <= y)%O].  The two are connected by the reflect view
    [precone_leP] below, and all the historical [precone_le*] lemmas
    are kept in their original [Prop] shapes. *)

Section PreconeOrder.
Variable R : realType.
Variable P : preconeType R.
Implicit Types (x y z : P).

(** Cone order: [x ≤ y] iff there exists [z] with [y = x + z].
    Paper §2.1: this is the *cone order* of [P]. *)
Definition precone_le (x y : P) : Prop := exists z : P, y = x + z.

(** The boolean order is the (asbool of the) cone order. *)
Lemma precone_leE x y : (x <= y)%O = `[< precone_le x y >].
Proof. exact: precone_le_def. Qed.

(** The reflect view connecting the boolean and [Prop] forms. *)
Lemma precone_leP x y : reflect (precone_le x y) (x <= y)%O.
Proof. by rewrite precone_leE; exact: asboolP. Qed.

(** Paper Lemma 2.9 (in spirit): reflexivity of the cone order. *)
Lemma precone_le_refl : forall x, precone_le x x.
Proof. by move=> x; apply/precone_leP; rewrite lexx. Qed.

(** Paper Lemma 2.9 (in spirit): transitivity of the cone order. *)
Lemma precone_le_trans : forall y x z,
  precone_le x y -> precone_le y z -> precone_le x z.
Proof.
by move=> y x z /precone_leP xy /precone_leP yz; apply/precone_leP;
  exact: le_trans xy yz.
Qed.

(** Paper §2.1: by (Cancel) and (Pos), the cone order is antisymmetric.
    This is the statement that the derived order is a *partial* order
    (mathcomp's [le_anti] on [precone_display]). *)
Lemma precone_le_anti : forall x y,
  precone_le x y -> precone_le y x -> x = y.
Proof.
move=> x y /precone_leP xy /precone_leP yx.
by apply: le_anti; rewrite xy yx.
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

(** Left-cancellation for the cone order: [x + y ≤p x + z ⇒ y ≤p z].
    The converse of [precone_add_le_l]; a pure (Cancel) fact, so it
    lives here rather than in the cone layer.  Subsumes the two
    identical copies [precone_le_addlI] of [stable/findiff.v]
    (Section ConeHelpers) and [stable/stablehom.v]. *)
Lemma precone_le_addlI x y z :
  precone_le (x + y) (x + z) -> precone_le y z.
Proof.
move=> [w Hw]; exists w.
by apply: (@precone_cancel _ _ x); rewrite Hw precone_addA.
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

(** ** Chains: bridging the [Prop] step form and the mathcomp
    [{homo}] form

    The mathcomp house style for "increasing chain" is
    [{homo u : n m / (n <= m)%N >-> (n <= m)%O}]; the historical
    form is the pointwise successor step [forall n, u n <=p u n.+1].
    The two bridges below convert in each direction. *)

Lemma precone_chain_homo (u : nat -> P) :
  (forall n, precone_le (u n) (u n.+1)) ->
  {homo u : n m / (n <= m)%N >-> (n <= m)%O}.
Proof.
move=> uch; apply: homo_leq => [x|y x z|n]; first by rewrite lexx.
  exact: le_trans.
exact/precone_leP/uch.
Qed.

Lemma homo_precone_chain (u : nat -> P) :
  {homo u : n m / (n <= m)%N >-> (n <= m)%O} ->
  forall n, precone_le (u n) (u n.+1).
Proof. by move=> uh n; apply/precone_leP; exact: uh (leqnSn n). Qed.

End PreconeOrder.

(** The cancelled summand [x] is kept explicit: consumers apply this
    lemma as [precone_le_addlI (a + b)] to say *which* left summand is
    being cancelled — the shape the subsumed copies were used in. *)
Arguments precone_le_addlI {R P} x y z.

(** ** Notation for the cone order *)

Notation "x <=p y" := (precone_le x y)
  (at level 70, no associativity) : precone_scope.
