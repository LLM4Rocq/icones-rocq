(** * Extended-real plumbing

    Helpers for crossing the [\bar R] / [R] boundary that appears whenever
    a measure value is fed into a cone operation.
*)
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.reals Require Import reals constructive_ereal.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import ereal.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Section EFinNotation.

(** A [bool] predicate "[x] is finite", aliased from mathcomp-analysis's
    [fin_num] qualifier so client files can write [is_finite µX] and read
    naturally without having to remember the [\is a fin_num] syntax. *)
Definition is_finite {R : numDomainType} (x : \bar R) : bool := x \is a fin_num.

(** [is_finite] reduces by definition to [fin_num] membership;  exposed
    so clients can rewrite it away when the qualifier form is preferred. *)
Lemma is_finiteE {R : numDomainType} (x : \bar R) :
  is_finite x = (x \is a fin_num).
Proof. by []. Qed.

End EFinNotation.

Section EFinExtra.
Context {R : numDomainType}.

Implicit Types (x y : \bar R) (r s : R).

(** Re-export of [EFin_inj] under a memorable name: the [EFin] embedding
    [R -> \bar R] is injective.  This is the workhorse for promoting an
    [\bar R] equality back into an [R] equality whenever we know both
    sides are finite. *)
Lemma EFin_eq r s : (r%:E = s%:E) <-> (r = s).
Proof. by split => [|->//]; exact: EFin_inj. Qed.

(** Bool-equality form, useful when the goal is under [==]. *)
Lemma eqe_fin r s : (r%:E == s%:E) = (r == s).
Proof. by apply/eqP/eqP => [|->//]; exact: EFin_inj. Qed.

(** A finite [\bar R] equals the [EFin]-lift of its [fine].  Direct
    re-export of [fineK] with the [is_finite] hypothesis name we use
    throughout the project. *)
Lemma EFin_fine x : is_finite x -> (fine x)%:E = x.
Proof. exact: fineK. Qed.

(** [fine] is a morphism for addition on finite values: re-export of
    [fineD]. *)
Lemma fine_add : {in (@fin_num R) &,
  {morph fine : x y / x + y >-> (x + y)%R}}.
Proof. exact: fineD. Qed.

(** [fine] is a morphism for multiplication on finite values: re-export
    of [fineM]. *)
Lemma fine_mul : {in (@fin_num R) &,
  {morph fine : x y / x * y >-> (x * y)%R}}.
Proof. exact: fineM. Qed.

End EFinExtra.

Section EFinFinite.
Context {R : numDomainType}.

Implicit Types (x y : \bar R).

(** Finiteness propagates through sum, re-export of [fin_numD]. *)
Lemma is_finite_add x y :
  is_finite (x + y) = is_finite x && is_finite y.
Proof. exact: fin_numD. Qed.

(** Finiteness propagates through difference, re-export of [fin_numB]. *)
Lemma is_finite_sub x y :
  is_finite (x - y) = is_finite x && is_finite y.
Proof. exact: fin_numB. Qed.

(** Constants are finite. *)
Lemma is_finite_EFin (r : R) : is_finite (r%:E).
Proof. by []. Qed.

(** Zero is finite. *)
Lemma is_finite0 : is_finite (0 : \bar R).
Proof. by []. Qed.

(** [+oo] is not finite. *)
Lemma is_finite_pinftyF : is_finite (+oo : \bar R) = false.
Proof. by []. Qed.

(** [-oo] is not finite. *)
Lemma is_finite_ninftyF : is_finite (-oo : \bar R) = false.
Proof. by []. Qed.

End EFinFinite.

Section EFineNonneg.
Context {R : numDomainType}.

Implicit Types (x : \bar R).

(** A nonnegative finite [\bar R] casts to a nonnegative [R].
    Combination of [fine_ge0] with the [is_finite] hypothesis we
    standardise on. *)
Lemma fine_ge0_finite x : is_finite x -> 0 <= x -> (0 <= fine x)%R.
Proof. by move=> _ /fine_ge0. Qed.

(** If [µ X] is finite and nonneg, its [fine] cast packs as a
    [{nonneg R}].  This is the recurring move in §4 when a measure
    value is fed into a cone scalar action. *)
Definition fine_nonneg x (xfin : is_finite x) (xge0 : 0 <= x) : {nonneg R} :=
  NngNum (fine_ge0_finite xfin xge0).

(** The [%:num] cast of [fine_nonneg] recovers [fine x]. *)
Lemma fine_nonnegE x (xfin : is_finite x) (xge0 : 0 <= x) :
  (fine_nonneg xfin xge0)%:num = fine x.
Proof. by []. Qed.

End EFineNonneg.
