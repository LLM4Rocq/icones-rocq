(** * The [bool_case] morphism in ICones (Step 3c + Step 4 + Step 5)

    This file packages the [bool_case] co-pairing as a [linhom_car]
    ([bool_case_linhom]) and then as a full [icones_hom]
    ([bool_case_icones_hom]) via the [linhom_icones] bridge of
    [theories/homs/seely.v].  It also constructs the
    EM-Kleisli-level "case" combinator [case_em] used by the
    PPL's [ne_if] clause.

    Placement.  [bool_cone.v] precedes [linhom.v] / [seely.v] in
    [_CoqProject], so the [linhom_car] / [icones_hom] packaging
    cannot live in [bool_cone.v] itself.  This file is loaded after
    [seely.v] so all the bridges are in scope.

    Headlines:
    - [bool_case_linhom a b Ha Hb : linhom_car Ar (bool_cone_car Ar) A]
    - [bool_case_icones_hom a b Ha Hb : icones_hom Ar (bool_cone_car Ar) A]
    - [case_em G A a b : coalg_hom (EM_prod G (bang_cofree (bool_cone_car Ar)))
                                     (Tobj A)]
      (Step 5; signatures finalised below.)
*)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals constructive_ereal.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import ereal.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import measure.

Require Import Icones.prelude.classical_extra.
Require Import Icones.prelude.nonneg_extra.
Require Import Icones.prelude.omegacpo.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.icones.pettis.
Require Import Icones.icones.icone.
Require Import Icones.cones.bool_cone.
Require Import Icones.icones.icone_cat.
Require Import Icones.homs.linhom.
Require Import Icones.homs.seely.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** Step 3c — [bool_case . a b] as a [linhom_car] *)

Section BoolCaseLinhom.
Variables (R : realType) (Ar : MeasSubcat R) (A : ICone.type Ar).
Variables (a b : A).
Hypotheses (Ha : (cone_norm a <= 1)%R) (Hb : (cone_norm b <= 1)%R).

Local Notation T := (bool_cone_car Ar).

(** Linearity of [x ↦ bool_case x a b] is already in [bool_cone.v]
    as [bool_case_linear], which takes the [a, b] as section
    arguments and returns an [is_linear]. *)
Definition bool_case_pre_linear : is_linear (fun x : T => bool_case x a b) :=
  bool_case_linear Ar a b.

(** ω-continuity — substep 2b in [bool_cone.v]. *)
Definition bool_case_pre_continuous :
    is_omega_continuous (fun x : T => bool_case x a b) :=
  bool_case_omega_continuous Ha Hb.

(** Operator-norm bound at [≤ 1]: from [bool_case_norm_le1]. *)
Lemma bool_case_pre_bounded :
  exists M : R,
    forall x : T, cone_norm x <= 1 -> cone_norm (bool_case x a b) <= M.
Proof.
exists 1 => x Hx.
exact: le_trans (bool_case_norm_le1 Ha Hb x) Hx.
Qed.

(** Path preservation — substep 3a in [bool_cone.v]. *)
Definition bool_case_pre_pres_path :
    forall (X : ar_obj Ar) (γ : ar_carrier Ar X -> T),
      is_measurable_path γ ->
      is_measurable_path (fun r => bool_case (γ r) a b) :=
  fun X γ Hγ => bool_case_pres_path a b Ha Hb γ Hγ.

(** Package: the [linhom_pre Ar (bool_cone_car Ar) A] half. *)
Definition bool_case_pre : linhom_pre Ar T A :=
  MkLinhomPre (fun x : T => bool_case x a b)
              bool_case_pre_linear
              bool_case_pre_continuous
              bool_case_pre_bounded
              bool_case_pre_pres_path.

(** Integral preservation — substep 3b in [bool_cone.v]. *)
Lemma bool_case_pres_int_packaged
    (X : ar_obj Ar) (β : ar_carrier Ar X -> T)
    (Hβ : is_measurable_path β)
    (µ : fmeas R (ar_carrier Ar X)) :
  linhom_pre_fun bool_case_pre (icone_integral β Hβ µ) =
  icone_integral
    (fun r => linhom_pre_fun bool_case_pre (β r))
    (linhom_pre_pres_path bool_case_pre X β Hβ) µ.
Proof.
rewrite /bool_case_pre /=.
have H := bool_case_pres_int Ha Hb Hβ µ.
rewrite H.
by congr icone_integral; exact: Prop_irrelevance.
Qed.

(** Step 3c output: the [linhom_car] packaging. *)
Definition bool_case_linhom : linhom_car Ar T A :=
  MkLinhom bool_case_pre bool_case_pres_int_packaged.

(** Norm-≤1 of the packaged linhom (needed for the [linhom_icones]
    bridge in Step 4). The operator norm of a sub-probability-eliminator
    into the unit ball is bounded by 1. *)
Lemma bool_case_linhom_norm_le1 :
  cone_norm bool_case_linhom <= 1.
Proof.
apply: (linhom_norm_sup_lub bool_case_linhom 1).
move=> x Hx.
rewrite /linhom_fun /= /bool_case_pre /=.
exact: (le_trans (bool_case_norm_le1 Ha Hb x) Hx).
Qed.

End BoolCaseLinhom.

Arguments bool_case_linhom {R Ar A} a b Ha Hb.
Arguments bool_case_linhom_norm_le1 {R Ar A} a b Ha Hb.

(** ** Step 4 — promote to [icones_hom] via [linhom_icones] *)

Section BoolCaseIConesHom.
Variables (R : realType) (Ar : MeasSubcat R) (A : ICone.type Ar).
Variables (a b : A).
Hypotheses (Ha : (cone_norm a <= 1)%R) (Hb : (cone_norm b <= 1)%R).

Definition bool_case_icones_hom :
    icones_hom Ar (bool_cone_car Ar) A :=
  linhom_icones (bool_case_linhom a b Ha Hb)
                (bool_case_linhom_norm_le1 a b Ha Hb).

End BoolCaseIConesHom.

Arguments bool_case_icones_hom {R Ar A} a b Ha Hb.
