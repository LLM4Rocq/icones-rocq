(**md**************************************************************************)
(* # Test-pullback infrastructure — the dual characterisation of an           *)
(*   [mcones_hom] (Paper Def 3.13, §5.3)                                       *)
(*                                                                            *)
(*   This file packages the *test-side* facts about morphisms in [MCones]    *)
(*   that are needed to show that post-composition by an [mcones_hom] /       *)
(*   [icones_hom] preserves measurable paths.  Concretely, Def 3.13's         *)
(*   "equivalently" bullet says a [cones_hom] [g : B → C] is in [MCones]      *)
(*   iff, for every test [m ∈ M^C_Z] and every measurable path               *)
(*   [φ : W → B], the function [λ(p : Z × W). m(p.1, g(φ p.2))] is            *)
(*   measurable.  The "forward" direction of this equivalence is what we      *)
(*   make reusable here, in two forms:                                        *)
(*                                                                            *)
(*   - [test_pullback_meas]: the basic section, for a single path argument    *)
(*     [φ].  This is the §5.3 statement [g ∘ φ ∈ Path], read through a test   *)
(*     [m] on the target.                                                     *)
(*                                                                            *)
(*   - [test_pullback_meas_bivar]: the bivariate version where the path       *)
(*     argument is folded out of a pair [(s, r) : Z × W] via [ar_prod].       *)
(*     This is the precise shape arising in §5.3's measurability of           *)
(*     [φ(s, r) = m(s, g(δ(s, r)))] for a bivariate path [δ].                 *)
(*                                                                            *)
(*   Both reduce to [measurable_test_path_section] (from [icone_integral.v])  *)
(*   applied to the path [g ∘ -], whose measurability is exactly              *)
(*   [mcones_hom_pres_path g].  They reuse the same [ar_prod_cast] /          *)
(*   [test_reindex] folding pattern used in [bilin.v] and the                 *)
(*   [linhom_int_fun_joint_meas] lemma of [linhom.v].                         *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.

Require Import Icones.prelude.classical_extra.
Require Import Icones.prelude.nonneg_extra.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.cone_cat.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.path.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.pettis.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_integral.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** Test-pullback along an [mcones_hom] — Paper Def 3.13 *)

Section TestPullback.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (B C : MCone.type Ar).
Variable g : mcones_hom Ar B C.

(** The path obtained by post-composing a measurable path [φ : W → B]
    with [g].  This is the witness invoked by Def 3.13's
    measurable-path-preservation field. *)
Lemma test_pullback_path (W : ar_obj Ar) (φ : ar_carrier Ar W -> B) :
  is_measurable_path φ ->
  is_measurable_path (fun r => cones_hom_fun (mcones_hom_cones g) (φ r)).
Proof. exact: (mcones_hom_pres_path g W φ). Qed.

(** Paper Def 3.13 ("equivalently" bullet), forward direction — the
    basic section.  For a test [m] on the *target* [C] and a measurable
    path [φ] into the *source* [B], the function
    [λ(p : Z × W). m(p.1, g(φ p.2))] is measurable.  This is the
    test-side characterisation of [g] being an [mcones_hom]: pulling a
    [C]-test back along [g] lands in the measurability structure of
    [B]. *)
Lemma test_pullback_meas
    (Z W : ar_obj Ar) (m : test_of Ar Z C) (mM : mcone_M Z m)
    (φ : ar_carrier Ar W -> B) (Hφ : is_measurable_path φ) :
  measurable_fun
    [set: (ar_carrier Ar Z * ar_carrier Ar W)%type]
    (fun p => test_fun m p.1 (cones_hom_fun (mcones_hom_cones g) (φ p.2))).
Proof.
have Hgφ : is_measurable_path
    (fun r => cones_hom_fun (mcones_hom_cones g) (φ r)).
  exact: test_pullback_path Hφ.
by have [_ Hj] := Hgφ; exact: (Hj Z m mM).
Qed.

(** Section at a fixed test index [s], i.e. the [r]-marginal of
    [test_pullback_meas].  Mirrors [measurable_test_path_section]. *)
Lemma test_pullback_section
    (Z W : ar_obj Ar) (m : test_of Ar Z C) (mM : mcone_M Z m)
    (φ : ar_carrier Ar W -> B) (Hφ : is_measurable_path φ)
    (s : ar_carrier Ar Z) :
  measurable_fun setT
    (fun r : ar_carrier Ar W =>
       test_fun m s (cones_hom_fun (mcones_hom_cones g) (φ r))).
Proof.
exact: (measurable_test_path_section mM (test_pullback_path Hφ)).
Qed.

(** Paper §5.3 / Def 3.13 — bivariate test-pullback.  The path
    argument is a bivariate measurable path [δ : (Z × W) → B], i.e. a
    family [(s, r) ↦ δ(s, r)] which is a measurable path of [B] when
    viewed at the product arity [ar_prod Z W].  The function
    [λ(p : Z × W). m(p.1, g(δ(p.1, p.2)))] is measurable.  This is the
    exact shape of §5.3's [φ(s, r) = m(s, g(δ1(s)(r)))] once the index
    pair is folded into [ar_prod Z W].

    [δar] is [δ] presented at the single arity [ar_prod Z W] (the
    caller supplies the measurability witness [Hδ]); [δarE] records
    that [δar] agrees with [δ] after the [ar_prod_cast] / uncast
    round-trip. *)
Lemma test_pullback_meas_bivar
    (Z W : ar_obj Ar) (m : test_of Ar Z C) (mM : mcone_M Z m)
    (δar : ar_carrier Ar (ar_prod Ar Z W) -> B)
    (Hδ : is_measurable_path δar) :
  measurable_fun
    [set: (ar_carrier Ar Z * ar_carrier Ar W)%type]
    (fun p => test_fun m p.1
                (cones_hom_fun (mcones_hom_cones g) (δar (ar_prod_cast p)))).
Proof.
(* Reindex [m] along [ar_prod_fst] to a test at arity [ar_prod Z W],
   then apply the basic section and cast the pair back. *)
pose mZW : test_of Ar (ar_prod Ar Z W) C :=
  test_reindex (ar_prod_fst Z W) m.
have mZWM : mcone_M (ar_prod Ar Z W) mZW by exact: mcone_M_comp.
have Hbase :
  measurable_fun
    [set: (ar_carrier Ar (ar_prod Ar Z W) *
           ar_carrier Ar (ar_prod Ar Z W))%type]
    (fun q => test_fun mZW q.1
                (cones_hom_fun (mcones_hom_cones g) (δar q.2))).
  exact: (test_pullback_meas mZWM Hδ).
(* Fold the input pair [(s, r)] into the product arity via the
   diagonal-ish map [p ↦ (cast p, cast p)]. *)
pose ψ (p : (ar_carrier Ar Z * ar_carrier Ar W)%type) :
    (ar_carrier Ar (ar_prod Ar Z W) *
     ar_carrier Ar (ar_prod Ar Z W))%type :=
  (ar_prod_cast p, ar_prod_cast p).
have ψ_meas : measurable_fun
    [set: (ar_carrier Ar Z * ar_carrier Ar W)%type] ψ.
  apply: measurable_fun_pair; exact: (ar_prod_cast_meas Ar Z W).
apply: (eq_measurable_fun
  (fun p => (fun q => test_fun mZW q.1
              (cones_hom_fun (mcones_hom_cones g) (δar q.2))) (ψ p))).
  move=> p _ /=.
  rewrite /mZW /test_reindex /test_reindex_fun /=.
  by rewrite /ar_prod_fst /ar_prod_fst_fun ar_prod_castK.
exact: (measurableT_comp Hbase ψ_meas).
Qed.

End TestPullback.

Arguments test_pullback_path {R Ar B C} g {W φ}.
Arguments test_pullback_meas {R Ar B C} g {Z W m} mM {φ} Hφ.
Arguments test_pullback_section {R Ar B C} g {Z W m} mM {φ} Hφ s.
Arguments test_pullback_meas_bivar {R Ar B C} g {Z W m} mM {δar} Hδ.

(** ** Test commutes with cone-suprema — the ω-continuity half of a test

    A test [m] on an [MCone] is ω-continuous by [test_cont] (lub) and
    monotone by [test_fun_le] (upper-bound).  Hence its value at a
    [cone_sup_ball] of a unit-ball chain is the real supremum of the
    chain of test-values.  This is exactly the [test_β_sup_pt] pattern
    from [icone_integral.v], factored out as a reusable lemma. *)

Section TestOfSup.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (C : MCone.type Ar) (Z : ar_obj Ar).
Variable m : test_of Ar Z C.

Lemma test_of_sup
    (s : ar_carrier Ar Z) (a : nat -> C)
    (ach : forall n, precone_le (a n) (a n.+1))
    (aub : forall n, cone_norm (a n) <= 1) :
  test_fun m s (cone_sup_ball a ach aub) =
  sup (range (fun n => test_fun m s (a n))).
Proof.
set v : nat -> R := fun n => test_fun m s (a n).
have ub : has_ubound (range v).
  by exists 1 => _ [n _ <-]; apply: test_le1; exact: aub.
have nonempty : (range v) !=set0 by exists (v 0%N), 0%N.
apply: le_anti; apply/andP; split; last first.
  apply: ge_sup => //.
  by move=> _ [n _ <-]; apply: test_fun_le; exact: cone_sup_ball_ub.
apply: test_cont => n.
apply: sup_upper_bound; first by split.
by exists n.
Qed.

End TestOfSup.

Arguments test_of_sup {R Ar C Z} m s {a} ach aub.

(** ** Test-pullback continuity — Paper §5.3 / Def 3.13 (continuity)

    A pulled-back test [z ↦ m(s, g(z))] inherits the ω-continuity of
    [m] through the ω-continuity of the [cones_hom] [g]: the value at a
    cone-sup is the real supremum of the values along the chain.  This
    is the test-side fact behind ω-continuity of post/pre-composition
    on the internal hom. *)

Section TestPullbackCont.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (D1 D2 : MCone.type Ar).
Variable g : cones_hom D1 D2.
Variables (Z : ar_obj Ar) (m : test_of Ar Z D2).

(** The [g]-image of a unit-ball increasing chain is again a unit-ball
    increasing chain — [g] is linear (hence increasing) and
    norm-decreasing. *)
Lemma cones_hom_image_chain
    (a : nat -> D1) (ach : forall n, precone_le (a n) (a n.+1)) :
  forall n, precone_le (cones_hom_fun g (a n)) (cones_hom_fun g (a n.+1)).
Proof.
move=> n.
exact: (linear_increasing (cones_hom_linear g)) _ _ (ach n).
Qed.

Lemma cones_hom_image_ub1
    (a : nat -> D1) (aub : forall n, cone_norm (a n) <= 1) :
  forall n, cone_norm (cones_hom_fun g (a n)) <= 1.
Proof.
by move=> n; apply: le_trans (cones_hom_norm_le1 g _) _; exact: aub.
Qed.

Lemma test_pullback_cont
    (s : ar_carrier Ar Z) (a : nat -> D1)
    (ach : forall n, precone_le (a n) (a n.+1))
    (aub : forall n, cone_norm (a n) <= 1) :
  test_fun m s (cones_hom_fun g (cone_sup_ball a ach aub)) =
  sup (range (fun n => test_fun m s (cones_hom_fun g (a n)))).
Proof.
rewrite (cones_hom_continuous ach aub
           (cones_hom_image_chain ach) (cones_hom_image_ub1 aub)).
exact: (test_of_sup m s _ _).
Qed.

End TestPullbackCont.

Arguments cones_hom_image_chain {R Ar D1 D2} g {a} ach.
Arguments cones_hom_image_ub1 {R Ar D1 D2} g {a} aub.
Arguments test_pullback_cont {R Ar D1 D2} g {Z} m s {a} ach aub.
(* [a] is inferable from [ach]/[aub]; the directives above keep [g]
   explicit for the morphism and leave [a] implicit. *)
