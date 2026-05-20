(** * Paper §6.1 — the substochastic-kernel category [Skern]

    Paper reference: §6.1 (arXiv:2212.02371).

    For [X, Y : ar_obj Ar], a *substochastic kernel* from [X] to [Y] is
    an element of [B_{Path(X, FMeas(Y))}], i.e. a measurable path
    [κ : X → FMeas(Y)] of unit-ball norm. [Skern] is the category whose

    - objects are those of [Ar];
    - morphisms [X → Y] are substochastic kernels;
    - identity is the Dirac path [δ_X];
    - composition is Kleisli (Panangaden-monad) composition,
      [(κ ∘ λ)(r1)(U3) := ∫ κ(r2, U3) λ(r1, dr2)], or equivalently
      [(κ ∘ λ)(r1) := I^{FMeas Y}_X(κ)(λ(r1))], i.e. integrating
      [κ] against the [FMeas]-valued kernel [λ(r1)].

    Coverage in this file:

    - [Skern_hom Ar X Y] — a record packaging a [path_car X (fmeas Y)]
      with [path_norm ≤ 1].
    - [Skern_id X] — the identity at [X], the Dirac path [δ_X]
      ([dirac_path] from [bilin.v]).
    - [Skern_comp κ λ] — Kleisli composition.
    - [Skern_compIl] / [Skern_compIr] / [Skern_compA] — category laws,
      established via the [int_to_linhom] machinery from [bilin.v]:
      the Skern composition is exactly the Kleisli composition of
      [int_to_linhom]-image arrows, and the round-trip identities
      [K ∘ I = id] / [I ∘ K = id] then deliver the unit laws and
      associativity. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals constructive_ereal.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import ereal sequences.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measure.
From mathcomp.analysis Require Import lebesgue_integral_definition.
Import numFieldTopology.Exports.

Require Import Icones.prelude.classical_extra.
Require Import Icones.prelude.nonneg_extra.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.cone_cat.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.mcones.path.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.pettis.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_integral.
Require Import Icones.icones.examples_icone.
Require Import Icones.icones.fubini.
Require Import Icones.icones.icone_cat.
Require Import Icones.homs.linhom.
Require Import Icones.homs.bilin.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** Paper §6.1 — the type of substochastic kernels *)

Section SkernHom.
Variables (R : realType) (Ar : MeasSubcat R).

(** Paper §6.1, line 3039: [Skern(X, Y) = B_{Path(X, FMeas(Y))}], i.e.
    measurable paths of unit-ball norm. *)
Record Skern_hom (X Y : ar_obj Ar) : Type := MkSkernHom {
  skern_path : path_car Ar X (fmeas R (ar_carrier Ar Y));
  skern_norm_le1 : path_norm skern_path <= 1;
}.

End SkernHom.

Arguments Skern_hom {R} Ar X Y.
Arguments MkSkernHom {R Ar X Y}.
Arguments skern_path {R Ar X Y}.
Arguments skern_norm_le1 {R Ar X Y}.

(** Equality of Skern morphisms reduces to equality of underlying
    paths, by [Prop_irrelevance] on the norm-bound proof. *)
Lemma Skern_hom_eq (R : realType) (Ar : MeasSubcat R) (X Y : ar_obj Ar)
    (κ1 κ2 : Skern_hom Ar X Y) :
  skern_path κ1 = skern_path κ2 -> κ1 = κ2.
Proof.
case: κ1 => p1 H1; case: κ2 => p2 H2 /= Hp.
move: H1; rewrite Hp => H1.
by congr MkSkernHom; exact: Prop_irrelevance.
Qed.

(** ** Paper §6.1 line 3042 — identity is the Dirac path *)

Section SkernId.
Variables (R : realType) (Ar : MeasSubcat R).
Variable X : ar_obj Ar.

(** [dirac_path X] has norm exactly [1] (every value has norm [1]),
    hence [≤ 1]. *)
Lemma dirac_path_norm_le1 : path_norm (dirac_path Ar X) <= 1.
Proof.
apply: ge_sup; first exact: path_normset_nonempty.
move=> _ [r ->] /=.
by rewrite dirac_fmeas_norm.
Qed.

(** Paper §6.1, line 3042: identity in [Skern]. *)
Definition Skern_id : Skern_hom Ar X X :=
  MkSkernHom (dirac_path Ar X) dirac_path_norm_le1.

End SkernId.

Arguments Skern_id {R} Ar X.

(** ** Paper §6.1 lines 3043–3050 — Kleisli composition

    [(κ ∘ λ)(r1) := I^{FMeas Y}_X(κ)(λ(r1)) = int_to_linhom_fun κ (λ r1)].

    Path-preservation uses [int_to_linhom_fun_pres_path] from
    [bilin.v]. The norm bound is the composite-norm bound
    [path_norm (κ ∘ λ) ≤ path_norm κ * path_norm λ ≤ 1]. *)

Section SkernComp.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (X Y Z : ar_obj Ar).

(** The underlying path of the Kleisli composite. *)
Definition Skern_comp_path (λ : Skern_hom Ar X Y) (κ : Skern_hom Ar Y Z) :
    path_car Ar X (fmeas R (ar_carrier Ar Z)) :=
  MkPath (int_to_linhom_fun_pres_path (skern_path κ)
            (path_is_path (skern_path λ))).

(** Norm bound: composite of unit-ball paths is in the unit ball. *)
Lemma Skern_comp_norm_le1
    (λ : Skern_hom Ar X Y) (κ : Skern_hom Ar Y Z) :
  path_norm (Skern_comp_path λ κ) <= 1.
Proof.
apply: ge_sup; first exact: path_normset_nonempty.
move=> _ [r ->] /=.
rewrite /int_to_linhom_fun.
(* [cone_norm (icone_integral κ _ (λ r)) <= path_norm κ * fmeas_norm (λ r)]
   then [path_norm κ <= 1] and [fmeas_norm (λ r) <= 1]. *)
apply: le_trans
  (@path_integral_norm_le _ _ _ _ (path_fun (skern_path κ)) (skern_path λ r)
                          (path_norm (skern_path κ))
                          (@path_norm_ub _ _ _ _ (skern_path κ))
                          (path_is_path (skern_path κ))
                          _ (icone_integralP _ _ _)) _.
apply: le_trans (_ : 1 * 1 <= 1); last by rewrite mulr1.
apply: ler_pM.
- exact: path_norm_ge0.
- exact: cone_norm_ge0.
- exact: skern_norm_le1.
- have := path_norm_ub (skern_path λ) r.
  by move/le_trans; apply; exact: skern_norm_le1.
Qed.

(** Paper §6.1, line 3050 — Kleisli composite as a [Skern_hom]. *)
Definition Skern_comp (λ : Skern_hom Ar X Y) (κ : Skern_hom Ar Y Z) :
    Skern_hom Ar X Z :=
  MkSkernHom (Skern_comp_path λ κ) (Skern_comp_norm_le1 λ κ).

End SkernComp.

Arguments Skern_comp_path {R Ar X Y Z}.
Arguments Skern_comp {R Ar X Y Z}.

(** ** Paper §6.1 — category laws

    The unit laws reduce to:
    - left identity: [int_to_linhom_fun (dirac_path Y) (λ r) = λ r],
      by the Dirac approximation [icone_integral_dirac_path].
    - right identity: [int_to_linhom_fun κ (dirac_fmeas r) = κ r],
      by [int_to_linhom_fun_dirac].

    Associativity is the integral-preservation identity for
    [int_to_linhom_fun κ_3]: applying it to
    [int_to_linhom_fun κ_2 (κ_1 r)] equals integrating it against
    the inner path. *)

Section SkernLaws.
Variables (R : realType) (Ar : MeasSubcat R).

(** Paper §6.1: left identity, [Skern_comp λ (Skern_id Y) = λ]. *)
Lemma Skern_compIl (X Y : ar_obj Ar) (λ : Skern_hom Ar X Y) :
  Skern_comp λ (Skern_id Ar Y) = λ.
Proof.
apply: Skern_hom_eq.
apply: path_eq => r /=.
rewrite /Skern_comp_path /Skern_id /=.
rewrite /int_to_linhom_fun.
have Heq := icone_integral_dirac_path (X:=Y) (skern_path λ r).
rewrite /dirac_path /= in Heq.
by apply: (eq_trans _ Heq); congr (icone_integral _ _ _).
Qed.

(** Paper §6.1: right identity, [Skern_comp (Skern_id X) λ = λ]. *)
Lemma Skern_compIr (X Y : ar_obj Ar) (λ : Skern_hom Ar X Y) :
  Skern_comp (Skern_id Ar X) λ = λ.
Proof.
apply: Skern_hom_eq.
apply: path_eq => r /=.
exact: (int_to_linhom_fun_dirac (skern_path λ) r).
Qed.

(** Paper §6.1: associativity. The key identity is

    [int_to_linhom_fun κ₃ (int_to_linhom_fun κ₂ (κ₁ r))
       = int_to_linhom_fun (fun s => int_to_linhom_fun κ₃ (κ₂ s)) (κ₁ r)],

    which is [int_to_linhom_fun_pres_int] for [κ₃] applied to [κ₂] and
    [κ₁ r]. *)
Lemma Skern_compA (X1 X2 X3 X4 : ar_obj Ar)
    (κ1 : Skern_hom Ar X1 X2) (κ2 : Skern_hom Ar X2 X3)
    (κ3 : Skern_hom Ar X3 X4) :
  Skern_comp κ1 (Skern_comp κ2 κ3) = Skern_comp (Skern_comp κ1 κ2) κ3.
Proof.
apply: Skern_hom_eq.
apply: path_eq => r /=.
have Hpres :=
  int_to_linhom_fun_pres_int (skern_path κ3)
    (path_is_path (skern_path κ2)) (skern_path κ1 r).
rewrite /int_to_linhom_fun in Hpres |- *.
rewrite /Skern_comp_path /=.
symmetry.
apply: (eq_trans Hpres).
by congr (icone_integral _ _ _).
Qed.

End SkernLaws.

(** ** Sanity checks *)

Section SkernSanity.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (X Y Z : ar_obj Ar).

Check (Skern_id Ar X : Skern_hom Ar X X).
Check (fun (λ : Skern_hom Ar X Y) (κ : Skern_hom Ar Y Z) =>
         Skern_comp λ κ : Skern_hom Ar X Z).
Check (fun (λ : Skern_hom Ar X Y) =>
         Skern_compIl λ : Skern_comp λ (Skern_id Ar Y) = λ).
Check (fun (λ : Skern_hom Ar X Y) =>
         Skern_compIr λ : Skern_comp (Skern_id Ar X) λ = λ).

End SkernSanity.
