(** * [{nonneg R}] arithmetic helpers

    Develops the bits of [R≥0] arithmetic we need for cone scalar
    multiplication, beyond what mathcomp-analysis provides out of the box.
*)
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.algebra Require Import interval_inference.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Section NonnegExtra.
Context {R : numDomainType}.

Implicit Types (r s : {nonneg R}).

(** Underlying-coercion injectivity: equality of [{nonneg R}] elements
    reduces to equality of their [R]-values.  Specialisation of
    [val_inj] from the [isSub] HB instance on [Itv.def]. *)
Lemma nngnum_inj : injective (fun r : {nonneg R} => r%:num).
Proof. exact: val_inj. Qed.

(** A [{nonneg R}] with zero underlying value is the zero of
    [{nonneg R}].  Useful for the (Pos) axiom in cones, which forbids
    sums equal to zero unless each summand is zero. *)
Lemma nonneg_eq0 r : r%:num = 0 -> r = 0%:nng.
Proof. by move=> r0; apply: nngnum_inj; rewrite r0. Qed.

(** Underlying value of a [{nonneg R}] is non-negative.  This is the
    [%:num]-side companion of the canonical [num_spec] machinery and is
    cheaper to invoke than going through [ge0]. *)
Lemma nngnum_ge0 r : 0 <= r%:num.
Proof. exact: ge0. Qed.

(** Underlying values of [0%:nng] and [1%:nng] reduce to the ring
    zero and one.  These hold definitionally but are useful as named
    rewrite rules so callers do not have to unfold [widen_itv]. *)
Lemma nngnum0 : (0%:nng : {nonneg R})%:num = 0.
Proof. by []. Qed.

End NonnegExtra.

Section NonnegAddMul.
Context {R : numDomainType}.

Implicit Types (r s : {nonneg R}).

(** The sum [r%:num + s%:num : R] is canonically a [{nonneg R}] via the
    [add_inum] instance, so [(r%:num + s%:num)%:nng] type-checks.  We
    expose it as a convenience wrapper so client code can speak of "the
    sum of two nonneg reals" without re-deriving the closure proof. *)
Definition nng_add r s : {nonneg R} := (r%:num + s%:num)%:nng.

(** The product [r%:num * s%:num : R] is canonically a [{nonneg R}]
    via [mul_inum].  Same packaging as [nng_add]. *)
Definition nng_mul r s : {nonneg R} := (r%:num * s%:num)%:nng.

(** Sanity rewrite: the underlying value of [nng_add r s] is the
    plain ring sum.  Holds definitionally. *)
Lemma nng_addE r s : (nng_add r s)%:num = r%:num + s%:num.
Proof. by []. Qed.

(** Sanity rewrite: the underlying value of [nng_mul r s] is the
    plain ring product.  Holds definitionally. *)
Lemma nng_mulE r s : (nng_mul r s)%:num = r%:num * s%:num.
Proof. by []. Qed.

End NonnegAddMul.

Section NonnegPos.
Context {R : numDomainType}.

Implicit Types (r s : {nonneg R}).

(** The (Pos) scalar axiom: a sum of two nonneg reals is zero only if
    both summands are zero.  This is the scalar incarnation of the
    cone (Pos) axiom and reduces to [paddr_eq0]. *)
Lemma nonneg_addr0 r s :
  nng_add r s = 0%:nng -> r = 0%:nng /\ s = 0%:nng.
Proof.
move=> /(congr1 (@Itv.r _ _ _)); rewrite nng_addE nngnum0 => /eqP.
rewrite paddr_eq0 ?nngnum_ge0// => /andP[/eqP r0 /eqP s0].
by split; apply: nonneg_eq0.
Qed.

End NonnegPos.
