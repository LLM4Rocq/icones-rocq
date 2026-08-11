(** * Concrete cone examples — Paper §2.3

    Two paper-faithful examples of cones:

    - [ConeBot.T] (Paper symbol [top], the *zero-dimensional* cone). The
      one-element cone whose carrier has a single inhabitant. Every
      structural axiom is discharged by exhaustive case analysis.

    - [ConeOne.T] (Paper symbol [bot], the *one-dimensional* cone, also
      written [R≥0] in the paper). The carrier is a thin one-field
      [Record] wrapping mathcomp's [{nonneg R}], with [+], [*:] and the
      norm given by the underlying ring operations and the projection
      [_%:num] of the wrapped value.

    The module names mirror the paper's symbols deliberately so that
    downstream code can [Import ConeBot.] / [Import ConeOne.] without
    colliding with mathcomp's lattice notation for [top] / [bot].

    Both carriers are *fresh keys*: [ConeBot.T] is a one-constructor
    [Inductive], [ConeOne.T] a one-field [Record].  This is not
    cosmetic — the [isPrecone] factory installs an [Order.POrder]
    instance on its carrier, so a carrier that is literally
    [{nonneg R}] would register that instance on mathcomp's own
    [Itv.nonneg] key and take precedence over [Num]'s order for every
    user-written [{nonneg R}], silently disabling [Num.Theory] order
    lemmas ([num_le] & co) downstream of an [Import ConeOne].  Every
    other carrier of the tower ([bool_cone_car], [cone_one_car],
    [path_car], [linhom_car], [cones_prod_car], …) is a fresh key for
    the same reason.
*)
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference.
From HB Require Import structures.

Require Import Icones.prelude.nonneg_extra.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** Example 1: the zero-dimensional cone [top]

    Paper §2.3, ⊤ example. A cone with a single element. All operations
    are constantly the unique inhabitant; the norm is constantly 0; the
    ω-supremum of any chain is the unique inhabitant. *)

Module ConeBot.
Section ConeBot.
Variable R : realType.

(** Paper §2.3, ⊤ example: a one-element type to serve as carrier. *)
Inductive T : Type := zero_top : T.

(** Boilerplate: an [eqType] structure for [T]. The cone HB structure
    does not require [eqType] per se, but bundling it is harmless and
    downstream files (M2: measurable cones) will eventually need it. *)
Definition T_eq (x y : T) : bool := true.

Lemma T_eqP : Equality.axiom T_eq.
Proof. by move=> [] []; constructor. Qed.

HB.instance Definition _ := hasDecEq.Build T T_eqP.

(** A [Choice] structure (required by the precone partial order),
    obtained classically. *)
HB.instance Definition _ := gen_choiceMixin T.

(** Paper §2.3, ⊤ example: the precone operations. All are constant. *)
Definition add (_ _ : T) : T := zero_top.
Definition scale (_ : {nonneg R}) (_ : T) : T := zero_top.

(** A handy collapsing lemma: every inhabitant of [T] equals [zero_top].
    Used everywhere to discharge the algebraic axioms. *)
Lemma all_zero (x : T) : x = zero_top.
Proof. by case: x. Qed.

(** Paper §2.3, ⊤ example: algebraic axioms. *)
Lemma addA : associative add.
Proof. by move=> x y z; rewrite /add. Qed.

Lemma addC : commutative add.
Proof. by move=> x y; rewrite /add. Qed.

Lemma add0l : left_id zero_top add.
Proof. by move=> x; rewrite /add (all_zero x). Qed.

Lemma scale_DAr : forall r x y, scale r (add x y) = add (scale r x) (scale r y).
Proof. by []. Qed.

Lemma scale_DAl : forall (r s : {nonneg R}) x,
  scale (r%:num + s%:num)%:nng x = add (scale r x) (scale s x).
Proof. by []. Qed.

Lemma scale_A : forall (r s : {nonneg R}) x,
  scale (r%:num * s%:num)%:nng x = scale r (scale s x).
Proof. by []. Qed.

Lemma scale_1 : forall x, scale 1%:nng x = x.
Proof. by move=> x; rewrite /scale (all_zero x). Qed.

Lemma scale_0r : forall r, scale r zero_top = zero_top.
Proof. by []. Qed.

Lemma scale_0l : forall x, scale 0%:nng x = zero_top.
Proof. by []. Qed.

Lemma cancel : forall x y z, add x y = add x z -> y = z.
Proof. by move=> x y z _; rewrite (all_zero y) (all_zero z). Qed.

Lemma pos : forall x y, add x y = zero_top -> x = zero_top /\ y = zero_top.
Proof. by move=> x y _; rewrite (all_zero x) (all_zero y). Qed.

(** Paper §2.3, ⊤ example: [isPrecone] instance. *)
HB.instance Definition _ := isPrecone.Build R T
  addA addC add0l scale_DAr scale_DAl scale_A
  scale_1 scale_0r scale_0l cancel pos.

(** Paper §2.3, ⊤ example: the norm is constantly 0. *)
Definition norm (_ : T) : R := 0.

(** Paper §2.3, ⊤ example: (Normh), scalar homogeneity. *)
Lemma normh : forall (r : {nonneg R}) (x : T),
  norm (scale r x) = r%:num * norm x.
Proof. by move=> r x; rewrite /norm mulr0. Qed.

(** Paper §2.3, ⊤ example: (Normz), zero-detection (vacuous). *)
Lemma normz : forall x : T, norm x = 0 -> x = zero_top.
Proof. by move=> x _; rewrite (all_zero x). Qed.

(** Paper §2.3, ⊤ example: (Normt), sub-additivity. *)
Lemma normt : forall x y : T, norm (add x y) <= norm x + norm y.
Proof. by move=> x y; rewrite /norm addr0 lexx. Qed.

(** Paper §2.3, ⊤ example: (Normp), order-monotonicity. *)
Lemma normp : forall x y : T, precone_le x y -> norm x <= norm y.
Proof. by move=> x y _; rewrite /norm lexx. Qed.

(** Paper §2.3, ⊤ example: (Normc), ω-completeness of the unit ball.
    The supremum of any chain is the unique inhabitant [zero_top]. *)
Definition sup_ball
  (u : nat -> T)
  (_ : forall n, precone_le (u n) (u n.+1))
  (_ : forall n, norm (u n) <= 1) : T := zero_top.

Lemma sup_ball_ub
  (u : nat -> T) (uch : forall n, precone_le (u n) (u n.+1))
  (ub1 : forall n, norm (u n) <= 1) n :
  precone_le (u n) (sup_ball uch ub1).
Proof. by exists zero_top. Qed.

Lemma sup_ball_lub
  (u : nat -> T) (uch : forall n, precone_le (u n) (u n.+1))
  (ub1 : forall n, norm (u n) <= 1) (y : T) :
  (forall n, precone_le (u n) y) ->
  precone_le (sup_ball uch ub1) y.
Proof. by move=> _; exists zero_top; rewrite (all_zero y). Qed.

Lemma sup_ball_norm
  (u : nat -> T) (uch : forall n, precone_le (u n) (u n.+1))
  (ub1 : forall n, norm (u n) <= 1) :
  norm (sup_ball uch ub1) <= 1.
Proof. by rewrite /norm ler01. Qed.

(** Paper §2.3, ⊤ example: cone instance, through the witness-style
    factory. *)
HB.instance Definition _ := Cone_ofWitnessSup.Build R T
  normh normz normt normp
  sup_ball_ub sup_ball_lub sup_ball_norm.

End ConeBot.
End ConeBot.

(** ** Example 2: the one-dimensional cone [bot]

    Paper §2.3, ⊥ example. The cone is [R≥0] (mathcomp's [{nonneg R}]),
    the canonical 1-dimensional cone, wrapped in a thin one-field
    [Record] so that the cone structure gets a carrier key of its own.
    Operations: ordinary addition and multiplication on the underlying
    reals; norm is the projection [_%:num] of the wrapped value. *)

Module ConeOne.
Section ConeOne.
Variable R : realType.

(** Paper §2.3, ⊥ example: the carrier is a thin [Record] wrapper
    around [{nonneg R}].

    Why a wrapper and not [{nonneg R}] itself: the [isPrecone] factory
    installs an [Order.POrder] instance (on [precone_display]) on its
    carrier.  Installed on the bare [{nonneg R}] — i.e. on mathcomp's
    own [Itv.nonneg] key — that instance takes precedence over [Num]'s
    order for every user-written [{nonneg R}], so [(x <= y)%O] on
    non-negative reals stops being the [Num] order and the whole
    [Num.Theory] order toolkit ([num_le] & co) silently stops applying
    downstream of an [Import ConeOne].  The two relations do coincide
    extensionally (that is exactly [precone_leE] below), so nothing was
    ever unsound; but the wrapper is what keeps the two *instances*
    apart.  It mirrors [cone_one_car] of [icones/examples_icone.v],
    which wraps [{nonneg R}] the same way to carry the [Ar]-indexed
    measurable structure. *)
Record T : Type := MkOne { one_val : {nonneg R} }.

(** Extensionality for the wrapper. *)
Lemma one_val_inj (x y : T) : one_val x = one_val y -> x = y.
Proof. by case: x; case: y => /= ? ? ->. Qed.

(** Classical [Equality] / [Choice] structures on the carrier
    (the latter is required by the precone partial order). *)
HB.instance Definition _ := gen_eqMixin T.
HB.instance Definition _ := gen_choiceMixin T.

(** Paper §2.3, ⊥ example: precone operations. The scalar action and
    the cone addition are *both* the underlying ring operations of [R]
    (lifted back through [%:nng] and the wrapper). *)
Definition add (x y : T) : T := MkOne (nng_add (one_val x) (one_val y)).
Definition scale (r : {nonneg R}) (x : T) : T :=
  MkOne (nng_mul r (one_val x)).

(** Paper §2.3, ⊥ example: algebraic axioms. All reduce to [R] via
    [one_val_inj] and [nngnum_inj]. *)

Lemma addA : associative add.
Proof.
move=> x y z; apply: one_val_inj; apply: nngnum_inj.
by rewrite !nng_addE addrA.
Qed.

Lemma addC : commutative add.
Proof.
move=> x y; apply: one_val_inj; apply: nngnum_inj.
by rewrite !nng_addE addrC.
Qed.

Lemma add0l : left_id (MkOne 0%:nng) add.
Proof.
move=> x; apply: one_val_inj; apply: nngnum_inj.
by rewrite !nng_addE add0r.
Qed.

Lemma scale_DAr : forall r x y, scale r (add x y) = add (scale r x) (scale r y).
Proof.
move=> r x y; apply: one_val_inj; apply: nngnum_inj.
by rewrite !nng_mulE !nng_addE !nng_mulE mulrDr.
Qed.

Lemma scale_DAl : forall (r s : {nonneg R}) x,
  scale (r%:num + s%:num)%:nng x = add (scale r x) (scale s x).
Proof.
move=> r s x; apply: one_val_inj; apply: nngnum_inj.
by rewrite !nng_addE !nng_mulE mulrDl.
Qed.

Lemma scale_A : forall (r s : {nonneg R}) x,
  scale (r%:num * s%:num)%:nng x = scale r (scale s x).
Proof.
move=> r s x; apply: one_val_inj; apply: nngnum_inj.
by rewrite !nng_mulE mulrA.
Qed.

Lemma scale_1 : forall x, scale 1%:nng x = x.
Proof.
move=> x; apply: one_val_inj; apply: nngnum_inj.
by rewrite nng_mulE mul1r.
Qed.

Lemma scale_0r : forall r, scale r (MkOne 0%:nng) = MkOne 0%:nng.
Proof.
move=> r; apply: one_val_inj; apply: nngnum_inj.
by rewrite nng_mulE mulr0.
Qed.

Lemma scale_0l : forall x, scale 0%:nng x = MkOne 0%:nng.
Proof.
move=> x; apply: one_val_inj; apply: nngnum_inj.
by rewrite nng_mulE mul0r.
Qed.

(** (Cancel): reduces to [R]-cancellation via [nngnum_inj]. *)
Lemma cancel : forall x y z, add x y = add x z -> y = z.
Proof.
move=> x y z /(congr1 one_val) /= /(congr1 (@Itv.r _ _ _)).
rewrite !nng_addE => H.
by apply: one_val_inj; apply: nngnum_inj; apply: (addrI (one_val x)%:num).
Qed.

(** (Pos): reduces to [paddr_eq0] via the helper [nonneg_addr0]. *)
Lemma pos : forall x y,
  add x y = MkOne 0%:nng -> x = MkOne 0%:nng /\ y = MkOne 0%:nng.
Proof.
move=> x y /(congr1 one_val) /= /nonneg_addr0[x0 y0].
by split; apply: one_val_inj; rewrite /= ?x0 ?y0.
Qed.

(** Paper §2.3, ⊥ example: [isPrecone] instance. *)
HB.instance Definition _ := isPrecone.Build R T
  addA addC add0l scale_DAr scale_DAl scale_A
  scale_1 scale_0r scale_0l cancel pos.

(** Paper §2.3, ⊥ example: the norm is the underlying real projection. *)
Definition norm (x : T) : R := (one_val x)%:num.

(** Paper §2.3, ⊥ example: (Normh). [‖r *: x‖ = r * ‖x‖] is the
    definitional equation [(r%:num * x%:num)%:nng %:num = r%:num * x%:num]. *)
Lemma normh : forall (r : {nonneg R}) (x : T),
  norm (precone_scale r x) = r%:num * norm x.
Proof. by move=> r x; rewrite /precone_scale/= /norm/= nng_mulE. Qed.

(** Paper §2.3, ⊥ example: (Normz). [‖x‖ = 0 ⇒ x = 0]. *)
Lemma normz : forall x : T, norm x = 0 -> x = precone_zero.
Proof.
move=> x x0; rewrite /precone_zero/=; apply: one_val_inj.
exact: nonneg_eq0.
Qed.

(** Paper §2.3, ⊥ example: (Normt). Triangle inequality on [R≥0]
    is *equality* once we project to [R]. *)
Lemma normt : forall x y : T,
  norm (precone_add x y) <= norm x + norm y.
Proof. by move=> x y; rewrite /precone_add/= /norm/= nng_addE lexx. Qed.

(** A key technical lemma: the cone order on [T] coincides with the
    [R]-order on the underlying reals. This is used both for (Normp)
    and for the (Normc) sup proof. *)
(** Step 1: on the concrete carrier [T], [precone_add] reduces to [add]
    (which is [nng_add] under the wrapper). This is a definitional fact
    under the HB instance declared above. *)
Lemma precone_add_E (x y : T) : precone_add x y = add x y.
Proof. by []. Qed.

Lemma precone_leE (x y : T) :
  precone_le x y <-> (one_val x)%:num <= (one_val y)%:num.
Proof.
split=> [[z Hxy]|le_xy].
  by rewrite Hxy precone_add_E nng_addE lerDl nngnum_ge0.
have d_ge0 : 0 <= (one_val y)%:num - (one_val x)%:num by rewrite subr_ge0.
exists (MkOne (NngNum d_ge0)).
apply: one_val_inj; apply: nngnum_inj.
by rewrite precone_add_E nng_addE/= addrC subrK.
Qed.

(** Paper §2.3, ⊥ example: (Normp). *)
Lemma normp : forall x y : T, precone_le x y -> norm x <= norm y.
Proof. by move=> x y /precone_leE. Qed.

(** Paper §2.3, ⊥ example: (Normc), ω-completeness of the unit ball.
    Construct the supremum of an increasing chain of [T] elements
    bounded by 1 as the mathcomp-real-analysis [sup] of the set of
    underlying reals, wrapped back as [T] via [NngNum] and [MkOne]. *)

(** The non-negativity of the sup, parameterised over the data. *)
Lemma sup_S_ge0
  (u : nat -> T) (ub1 : forall n, norm (u n) <= 1) :
  0 <= sup [set (one_val (u n))%:num | n in [set: nat]].
Proof.
set S : set R := [set _ | _ in _].
have S_nonempty : S !=set0 by exists (one_val (u 0))%:num; exists 0%N.
have S_has_ubound : has_ubound S by exists 1 => x [n _ <-]; exact: ub1.
have ub_sup : ubound S (sup S) by exact: ub_le_sup.
apply: le_trans (nngnum_ge0 (one_val (u 0%N))) _.
by apply: ub_sup; exists 0%N.
Qed.

(** Paper §2.3, ⊥ example: the (Normc) supremum operator.
    Construct the supremum of an increasing chain bounded by 1 as the
    [sup] of the set of underlying reals, wrapped back as [T] via
    [NngNum] (with the non-negativity proof [sup_S_ge0]) and [MkOne].
    The chain hypothesis [uch] is *not* needed for the existence of the
    sup — only [ub1] is — but we keep it in the signature to match
    [Cone_ofWitnessSup.Build]. *)
Definition sup_ball
  (u : nat -> T)
  (_ : forall n, precone_le (u n) (u n.+1))
  (ub1 : forall n, norm (u n) <= 1) : T :=
  MkOne (NngNum (sup_S_ge0 ub1)).

(** Helper: spell out the underlying-value of [sup_ball]. *)
Lemma sup_ball_E
  (u : nat -> T)
  (uch : forall n, precone_le (u n) (u n.+1))
  (ub1 : forall n, norm (u n) <= 1) :
  (one_val (sup_ball uch ub1))%:num =
  sup [set (one_val (u n))%:num | n in [set: nat]].
Proof. by []. Qed.

(** Paper §2.3, ⊥ example: (Normc) upper-bound property. *)
Lemma sup_ball_ub :
  forall (u : nat -> T)
         (uch : forall n, precone_le (u n) (u n.+1))
         (ub1 : forall n, norm (u n) <= 1) n,
    precone_le (u n) (sup_ball uch ub1).
Proof.
move=> u uch ub1 n; apply/precone_leE.
rewrite sup_ball_E.
set S : set R := [set _ | _ in _].
have S_has_ubound : has_ubound S by exists 1 => x [m _ <-]; exact: ub1.
have ub_sup : ubound S (sup S) by exact: ub_le_sup.
by apply: ub_sup; exists n.
Qed.

(** Paper §2.3, ⊥ example: (Normc) least-upper-bound property. *)
Lemma sup_ball_lub :
  forall (u : nat -> T)
         (uch : forall n, precone_le (u n) (u n.+1))
         (ub1 : forall n, norm (u n) <= 1) y,
    (forall n, precone_le (u n) y) ->
    precone_le (sup_ball uch ub1) y.
Proof.
move=> u uch ub1 y H; apply/precone_leE.
rewrite sup_ball_E.
set S : set R := [set _ | _ in _].
have S_nonempty : S !=set0 by exists (one_val (u 0))%:num; exists 0%N.
apply: ge_sup; first exact: S_nonempty.
by move=> x [n _ <-]; have /precone_leE := H n.
Qed.

(** Paper §2.3, ⊥ example: (Normc) sup is in the unit ball. *)
Lemma sup_ball_norm :
  forall (u : nat -> T)
         (uch : forall n, precone_le (u n) (u n.+1))
         (ub1 : forall n, norm (u n) <= 1),
    norm (sup_ball uch ub1) <= 1.
Proof.
move=> u uch ub1; rewrite /norm sup_ball_E.
apply: ge_sup; first by exists (one_val (u 0))%:num; exists 0%N.
by move=> x [n _ <-]; exact: ub1.
Qed.

(** Paper §2.3, ⊥ example: cone instance, through the witness-style
    factory. *)
HB.instance Definition _ := Cone_ofWitnessSup.Build R T
  normh normz normt normp
  sup_ball_ub sup_ball_lub sup_ball_norm.

End ConeOne.
End ConeOne.
