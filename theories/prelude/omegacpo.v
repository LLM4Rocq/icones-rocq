(** * ω-cpo HB structure — Paper §2.1, condition (Normc)

    A partial order [T] equipped with an explicit supremum operator
    [sup : forall (u : nat -> T), (forall n, u n <= u n.+1) -> T] for
    every monotone (ω-)chain, characterised by being an upper bound
    ([sup_ub]) and the least one ([sup_lub]).

    Design note. We expose [sup] as a *concrete operation* rather than
    bundling a sigma-type "least upper bound exists". This is the
    recommendation flagged in PLAN.md §3.1 Cons: downstream proofs in
    [cone.v] need to *use* the supremum element, and chasing existential
    witnesses everywhere is more painful than calling [sup] directly.

    The structure is parametric over a [disp_t] (the mathcomp order
    display) and a [porderType disp]. This lets us instantiate it on
    arbitrary partial orders; in particular, on the cone order of the
    unit ball of a cone (Paper Def 2.2, condition (Normc)).
*)
From mathcomp Require Import all_ssreflect ssralg.
From mathcomp.order Require Import preorder order.
From mathcomp.classical Require Import boolp.
From HB Require Import structures.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory.

Local Open Scope order_scope.

(** ** ω-chains *)

Section Chain.
Context (disp : Order.disp_t) (T : porderType disp).

(** [omegacpo_chain u] expresses that the sequence [u : nat -> T] is
    monotone in the partial order of [T]. This is the input shape of
    [sup] in our ω-cpo mixin. *)
Definition omegacpo_chain (u : nat -> T) : Prop :=
  forall n, u n <= u n.+1.

Lemma omegacpo_chain_le (u : nat -> T) :
  omegacpo_chain u -> forall m n, (m <= n)%N -> u m <= u n.
Proof.
move=> uch m n; elim: n => [|n IH] mlen.
  by move: mlen; rewrite leqn0 => /eqP ->.
have [/eqP -> //|mltSn] := boolP (m == n.+1).
have mlen' : (m <= n)%N.
  by move: mlen mltSn; rewrite leq_eqVlt ltnS => /orP[->//|//].
exact: (le_trans (IH mlen') (uch n)).
Qed.

End Chain.

(** ** ω-cpo HB mixin *)

(** [isOmegaCpo disp T] equips a [porderType disp] with an ω-suprema
    operator. The two axioms encode "[sup u h] is an upper bound" and
    "[sup u h] is the least one". *)
#[key="T", primitive]
HB.mixin Record isOmegaCpo (disp : Order.disp_t) T of Order.POrder disp T := {
  ocpo_sup    : forall (u : nat -> T), omegacpo_chain u -> T;
  ocpo_sup_ub : forall (u : nat -> T) (uch : omegacpo_chain u) (n : nat),
                  u n <= ocpo_sup u uch;
  ocpo_sup_lub : forall (u : nat -> T) (uch : omegacpo_chain u) (y : T),
                  (forall n, u n <= y) -> ocpo_sup u uch <= y;
}.

#[short(type="omegacpoType")]
HB.structure Definition OmegaCpo (disp : Order.disp_t) :=
  { T of Order.POrder disp T & isOmegaCpo disp T }.

(** ** Basic lemmas *)

Section OmegaCpoTheory.
Context (disp : Order.disp_t) (T : omegacpoType disp).
Implicit Types (u v : nat -> T).

(** [sup_ub] is the upper-bound property of [ocpo_sup]. *)
Lemma sup_ub (u : nat -> T) (uch : omegacpo_chain u) (n : nat) :
  u n <= ocpo_sup u uch.
Proof. exact: ocpo_sup_ub. Qed.

(** [sup_lub] is the least-upper-bound property of [ocpo_sup]. *)
Lemma sup_lub (u : nat -> T) (uch : omegacpo_chain u) (y : T) :
  (forall n, u n <= y) -> ocpo_sup u uch <= y.
Proof. exact: ocpo_sup_lub. Qed.

(** The supremum is independent of the chain proof: any two proofs of
    monotonicity for the same sequence yield the same supremum. *)
Lemma sup_irrelevant (u : nat -> T) (uch1 uch2 : omegacpo_chain u) :
  ocpo_sup u uch1 = ocpo_sup u uch2.
Proof.
by apply/le_anti/andP; split; apply: sup_lub => n; exact: sup_ub.
Qed.

End OmegaCpoTheory.
