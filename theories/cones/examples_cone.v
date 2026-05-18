(** * Concrete cone examples — Paper §2.3

    Two paper-faithful examples of cones:

    - [ConeBot.T] (Paper symbol [top], the *zero-dimensional* cone). The
      one-element cone whose carrier has a single inhabitant. Every
      structural axiom is discharged by exhaustive case analysis.

    - [ConeOne.T] (Paper symbol [bot], the *one-dimensional* cone, also
      written [R≥0] in the paper). The carrier is mathcomp's [{nonneg R}],
      with [+], [*:] and the norm given by the underlying ring operations
      and the projection [_%:num].

    The module names mirror the paper's symbols deliberately so that
    downstream code can [Import ConeBot.] / [Import ConeOne.] without
    colliding with mathcomp's lattice notation for [top] / [bot]. See
    PLAN.md §M1f for the naming rationale.
*)
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference.
From HB Require Import structures.

Require Import Icones.prelude.classical_extra.
Require Import Icones.prelude.nonneg_extra.
Require Import Icones.prelude.omegacpo.
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

(** Paper §2.3, ⊤ example: [isCone] instance. *)
HB.instance Definition _ := isCone.Build R T
  normh normz normt normp
  sup_ball_ub sup_ball_lub sup_ball_norm.

End ConeBot.
End ConeBot.

(** ** Example 2: the one-dimensional cone [bot]

    Paper §2.3, ⊥ example. The cone is [R≥0] (mathcomp's [{nonneg R}]),
    the canonical 1-dimensional cone. Operations: ordinary addition and
    multiplication on the underlying reals; norm is the projection
    [_%:num]. *)

Module ConeOne.
Section ConeOne.
Variable R : realType.

(** Paper §2.3, ⊥ example: the carrier is [{nonneg R}]. *)
Local Notation T := {nonneg R}.

(** Paper §2.3, ⊥ example: precone operations. The scalar action and
    the cone addition are *both* the underlying ring operations of [R]
    (lifted back through [%:nng]). *)
Definition add (r s : T) : T := nng_add r s.
Definition scale (r : T) (x : T) : T := nng_mul r x.

(** Paper §2.3, ⊥ example: algebraic axioms. All reduce to [R] via
    [nngnum_inj]. *)

Lemma addA : associative add.
Proof.
by move=> x y z; apply: nngnum_inj; rewrite !nng_addE addrA.
Qed.

Lemma addC : commutative add.
Proof.
by move=> x y; apply: nngnum_inj; rewrite !nng_addE addrC.
Qed.

Lemma add0l : left_id 0%:nng add.
Proof.
by move=> x; apply: nngnum_inj; rewrite !nng_addE add0r.
Qed.

Lemma scale_DAr : forall r x y, scale r (add x y) = add (scale r x) (scale r y).
Proof.
by move=> r x y; apply: nngnum_inj;
  rewrite !nng_mulE !nng_addE !nng_mulE mulrDr.
Qed.

Lemma scale_DAl : forall (r s : T) x,
  scale (r%:num + s%:num)%:nng x = add (scale r x) (scale s x).
Proof.
by move=> r s x; apply: nngnum_inj;
  rewrite !nng_addE !nng_mulE mulrDl.
Qed.

Lemma scale_A : forall (r s : T) x,
  scale (r%:num * s%:num)%:nng x = scale r (scale s x).
Proof.
by move=> r s x; apply: nngnum_inj; rewrite !nng_mulE mulrA.
Qed.

Lemma scale_1 : forall x, scale 1%:nng x = x.
Proof.
by move=> x; apply: nngnum_inj; rewrite nng_mulE mul1r.
Qed.

Lemma scale_0r : forall r, scale r 0%:nng = 0%:nng.
Proof.
by move=> r; apply: nngnum_inj; rewrite nng_mulE mulr0.
Qed.

Lemma scale_0l : forall x, scale 0%:nng x = 0%:nng.
Proof.
by move=> x; apply: nngnum_inj; rewrite nng_mulE mul0r.
Qed.

(** (Cancel): reduces to [R]-cancellation via [nngnum_inj]. *)
Lemma cancel : forall x y z, add x y = add x z -> y = z.
Proof.
move=> x y z /(congr1 (@Itv.r _ _ _)); rewrite !nng_addE => H.
by apply: nngnum_inj; apply: (addrI x%:num).
Qed.

(** (Pos): reduces to [paddr_eq0] via the helper [nonneg_addr0]. *)
Lemma pos : forall x y, add x y = 0%:nng -> x = 0%:nng /\ y = 0%:nng.
Proof. exact: nonneg_addr0. Qed.

(** Paper §2.3, ⊥ example: [isPrecone] instance. *)
HB.instance Definition _ := isPrecone.Build R T
  addA addC add0l scale_DAr scale_DAl scale_A
  scale_1 scale_0r scale_0l cancel pos.

(** Paper §2.3, ⊥ example: the norm is the underlying real projection. *)
Definition norm (x : T) : R := x%:num.

(** Paper §2.3, ⊥ example: (Normh). [‖r *: x‖ = r * ‖x‖] is the
    definitional equation [(r%:num * x%:num)%:nng %:num = r%:num * x%:num]. *)
Lemma normh : forall (r : {nonneg R}) (x : T),
  norm (precone_scale r x) = r%:num * norm x.
Proof. by move=> r x; rewrite /precone_scale/= /norm nng_mulE. Qed.

(** Paper §2.3, ⊥ example: (Normz). [‖x‖ = 0 ⇒ x = 0%:nng]. *)
Lemma normz : forall x : T, norm x = 0 -> x = precone_zero.
Proof. by move=> x x0; rewrite /precone_zero/=; exact: nonneg_eq0. Qed.

(** Paper §2.3, ⊥ example: (Normt). Triangle inequality on [R≥0]
    is *equality* once we project to [R]. *)
Lemma normt : forall x y : T,
  norm (precone_add x y) <= norm x + norm y.
Proof. by move=> x y; rewrite /precone_add/= /norm nng_addE lexx. Qed.

(** A key technical lemma: the cone order on [{nonneg R}] coincides
    with the [R]-order on the underlying reals. This is used both for
    (Normp) and for the (Normc) sup proof. *)
(** Step 1: on the concrete carrier [{nonneg R}], [precone_add] reduces
    to [add] (which is [nng_add]). This is a definitional fact under
    the HB instance declared above. *)
Lemma precone_add_E (x y : T) : precone_add x y = add x y.
Proof. by []. Qed.

Lemma precone_leE (x y : T) : precone_le x y <-> x%:num <= y%:num.
Proof.
split=> [[z Hxy]|le_xy].
  by rewrite Hxy precone_add_E nng_addE lerDl nngnum_ge0.
have d_ge0 : 0 <= y%:num - x%:num by rewrite subr_ge0.
exists (NngNum d_ge0); apply: nngnum_inj.
by rewrite precone_add_E nng_addE/= addrC subrK.
Qed.

(** Paper §2.3, ⊥ example: (Normp). *)
Lemma normp : forall x y : T, precone_le x y -> norm x <= norm y.
Proof. by move=> x y /precone_leE. Qed.

(** Paper §2.3, ⊥ example: (Normc), ω-completeness of the unit ball.
    Construct the supremum of an increasing chain of [{nonneg R}]
    elements bounded by 1 as the mathcomp-real-analysis [sup] of the
    set of underlying reals, wrapped back as [{nonneg R}] via [NngNum]. *)

(** The non-negativity of the sup, parameterised over the data. *)
Lemma sup_S_ge0
  (u : nat -> T) (ub1 : forall n, norm (u n) <= 1) :
  0 <= sup [set (u n)%:num | n in [set: nat]].
Proof.
set S : set R := [set _ | _ in _].
have S_nonempty : S !=set0 by exists (u 0)%:num; exists 0%N.
have S_has_ubound : has_ubound S by exists 1 => x [n _ <-]; exact: ub1.
have ub_sup : ubound S (sup S) by exact: ub_le_sup.
apply: le_trans (nngnum_ge0 (u 0%N)) _.
by apply: ub_sup; exists 0%N.
Qed.

(** Paper §2.3, ⊥ example: the (Normc) supremum operator.
    Construct the supremum of an increasing chain bounded by 1 as the
    [sup] of the set of underlying reals, wrapped back as [{nonneg R}]
    via [NngNum] with the non-negativity proof [sup_S_ge0]. The chain
    hypothesis [uch] is *not* needed for the existence of the sup — only
    [ub1] is — but we keep it in the signature to match [isCone.Build]. *)
Definition sup_ball
  (u : nat -> T)
  (_ : forall n, precone_le (u n) (u n.+1))
  (ub1 : forall n, norm (u n) <= 1) : T :=
  NngNum (sup_S_ge0 ub1).

(** Helper: spell out the underlying-value of [sup_ball]. *)
Lemma sup_ball_E
  (u : nat -> T)
  (uch : forall n, precone_le (u n) (u n.+1))
  (ub1 : forall n, norm (u n) <= 1) :
  (sup_ball uch ub1)%:num = sup [set (u n)%:num | n in [set: nat]].
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
have S_nonempty : S !=set0 by exists (u 0)%:num; exists 0%N.
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
apply: ge_sup; first by exists (u 0)%:num; exists 0%N.
by move=> x [n _ <-]; exact: ub1.
Qed.

(** Paper §2.3, ⊥ example: [isCone] instance. *)
HB.instance Definition _ := isCone.Build R T
  normh normz normt normp
  sup_ball_ub sup_ball_lub sup_ball_norm.

End ConeOne.
End ConeOne.
