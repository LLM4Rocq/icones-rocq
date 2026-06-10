(**md *** PPL CBV chapter infrastructure

    This file is NOT part of the Ehrhard-Geoffroy 2025 formalization
    (paper §2-§9). It packages the [bool_case] co-pairing of
    [theories/programs/infra/bool_cone.v] (paper §4.4 / Theorem 4.24 coproduct
    [cone_one ⊕ cone_one]) as a [linhom_car] and a full [icones_hom],
    with the unit-ball-free generalisation [bool_case_linhom_gen] and
    the α/β decomposition into separately-bilinear pieces. Together
    with [theories/programs/ppl.v]'s [case_em] combinator, this is
    what the [ne_if] (boolean elimination) clause of the CBV PPL
    consumes.

    See also: [theories/programs/infra/bool_cone.v] (the 2-point ICone and the
    universal co-pairing), [theories/programs/ppl.v] (tbool, ne_true,
    ne_false, ne_bernoulli, ne_if, case_em). *)

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
Require Import Icones.programs.infra.bool_cone.
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

(** ** [bool_case_linhom_gen] — UNIT-BALL-FREE packaging

    Drop the [‖a‖ ≤ 1], [‖b‖ ≤ 1] hypotheses on the branches.
    The branches [a, b : A] are arbitrary; only the chain inputs
    need to live on the unit ball (this is automatic for the chain
    field of [linhom_pre], so the unit-ball restriction on the
    branches drops out).

    Uses the generalized lemmas of [bool_cone.v]:
    - [bool_case_linear] (already general; no unit-ball needed),
    - [bool_case_omega_continuous_gen] (drops unit-ball on a, b),
    - [bool_case_norm_le_max] for the operator bound (with
      [M := max(‖a‖, ‖b‖) ∨ 0]),
    - [bool_case_pres_path_gen],
    - [bool_case_pres_int_gen]. *)

Section BoolCaseLinhomGen.
Variables (R : realType) (Ar : MeasSubcat R) (A : ICone.type Ar).
Variables (a b : A).

Local Notation T := (bool_cone_car Ar).

(** Linearity is unconditional (already in [bool_cone.v]). *)
Definition bool_case_pre_linear_gen :
    is_linear (fun x : T => bool_case x a b) :=
  bool_case_linear Ar a b.

(** ω-continuity without unit-ball restriction on [a, b]. *)
Definition bool_case_pre_continuous_gen :
    is_omega_continuous (fun x : T => bool_case x a b) :=
  bool_case_omega_continuous_gen (a:=a) (b:=b).

(** Operator-norm bound with the [‖a‖ + ‖b‖] threshold (using
    [bool_case_norm_le_max] at [M := max(‖a‖, ‖b‖) ∨ 0]).  Note the
    "≤ 1 → ≤ M" form of [linhom_pre_bounded] only needs a single
    [M], so we pick [M := max(‖a‖, ‖b‖) ∨ 0]. *)
Lemma bool_case_pre_bounded_gen :
  exists M : R,
    forall x : T, cone_norm x <= 1 -> cone_norm (bool_case x a b) <= M.
Proof.
pose M : R := Num.max (Num.max (cone_norm a) (cone_norm b)) 0%R.
exists M => x Hx.
have HM0 : 0 <= M by rewrite le_max lexx orbT.
have HMa : cone_norm a <= M
  by apply: le_trans (_ : Num.max (cone_norm a) (cone_norm b) <= _);
     [rewrite le_max lexx|rewrite le_max lexx].
have HMb : cone_norm b <= M
  by apply: le_trans (_ : Num.max (cone_norm a) (cone_norm b) <= _);
     [rewrite le_max lexx orbT|rewrite le_max lexx].
apply: le_trans (bool_case_norm_le_max HMa HMb HM0 x) _.
by rewrite -[X in _ <= X]mul1r; apply: ler_wpM2r => //; rewrite mulrC.
Qed.

(** Path preservation, no unit-ball assumption. *)
Definition bool_case_pre_pres_path_gen :
    forall (X : ar_obj Ar) (γ : ar_carrier Ar X -> T),
      is_measurable_path γ ->
      is_measurable_path (fun r => bool_case (γ r) a b) :=
  fun X γ Hγ => bool_case_pres_path_gen a b γ Hγ.

(** Package: the [linhom_pre] half. *)
Definition bool_case_pre_gen : linhom_pre Ar T A :=
  MkLinhomPre (fun x : T => bool_case x a b)
              bool_case_pre_linear_gen
              bool_case_pre_continuous_gen
              bool_case_pre_bounded_gen
              bool_case_pre_pres_path_gen.

(** Integral preservation, no unit-ball assumption. *)
Lemma bool_case_pres_int_packaged_gen
    (X : ar_obj Ar) (β : ar_carrier Ar X -> T)
    (Hβ : is_measurable_path β)
    (µ : fmeas R (ar_carrier Ar X)) :
  linhom_pre_fun bool_case_pre_gen (icone_integral β Hβ µ) =
  icone_integral
    (fun r => linhom_pre_fun bool_case_pre_gen (β r))
    (linhom_pre_pres_path bool_case_pre_gen X β Hβ) µ.
Proof.
rewrite /bool_case_pre_gen /=.
have H := bool_case_pres_int_gen a b β Hβ µ.
rewrite H.
by congr icone_integral; exact: Prop_irrelevance.
Qed.

(** Target 1: unit-ball-free linhom_car packaging. *)
Definition bool_case_linhom_gen : linhom_car Ar T A :=
  MkLinhom bool_case_pre_gen bool_case_pres_int_packaged_gen.

(** Operator-norm bound on [bool_case_linhom_gen]:
    [‖bool_case_linhom_gen a b‖ ≤ max(‖a‖, ‖b‖) ∨ 0].  This follows
    from [bool_case_norm_le_max] via [linhom_norm_sup_lub]. *)
Lemma bool_case_linhom_gen_norm_le :
  cone_norm bool_case_linhom_gen <= Num.max (Num.max (cone_norm a) (cone_norm b)) 0%R.
Proof.
apply: (linhom_norm_sup_lub bool_case_linhom_gen _).
move=> x Hx.
rewrite /linhom_fun /= /bool_case_pre_gen /=.
pose M : R := Num.max (Num.max (cone_norm a) (cone_norm b)) 0%R.
have HM0 : 0 <= M by rewrite le_max lexx orbT.
have HMa : cone_norm a <= M
  by apply: le_trans (_ : Num.max (cone_norm a) (cone_norm b) <= _);
     [rewrite le_max lexx|rewrite le_max lexx].
have HMb : cone_norm b <= M
  by apply: le_trans (_ : Num.max (cone_norm a) (cone_norm b) <= _);
     [rewrite le_max lexx orbT|rewrite le_max lexx].
apply: le_trans (bool_case_norm_le_max HMa HMb HM0 x) _.
by rewrite -[X in _ <= X]mul1r; apply: ler_wpM2r => //; rewrite mulrC.
Qed.

End BoolCaseLinhomGen.

Arguments bool_case_linhom_gen {R Ar A} a b.
Arguments bool_case_linhom_gen_norm_le {R Ar A} a b.

(** ** Step 1 — [alpha_linhom] / [beta_linhom] — the bilinear pieces

    [bool_case x a b = bc_t(x)·a + bc_f(x)·b] does NOT make [bool_case]
    bilinear in [(a, b)] (cf. the structural finding documented in the
    [case_em] plan: adding in the second slot creates a [bc_f·b]
    discrepancy).  The decomposition that DOES work is the sum of two
    SEPARATELY bilinear pieces:
    [[
      bool_case x a b = α(x, a) + β(x, b)
        where α(x, a) := bc_t(x) · a   [bilinear in (x, a)]
              β(x, b) := bc_f(x) · b   [bilinear in (x, b)].
    ]]

    Each of [α], [β] is bilinear in its TWO variables, and each is the
    specialisation of [bool_case_linhom_gen] with the OTHER branch set to
    [precone_zero]:
    [[
      α(x, a) = bool_case x a 0   (the [b = 0] specialisation)
      β(x, b) = bool_case x 0 b   (the [a = 0] specialisation).
    ]]
    The corresponding [linhom_car]s ([linhom_car (bool_cone_car Ar) A], for
    fixed [a] / [b]) are immediate restrictions of [bool_case_linhom_gen].
    Their pointwise images are
    [[
      α(x, a) = precone_scale (bc_t x) a,
      β(x, b) = precone_scale (bc_f x) b.
    ]]
    The sum-decomposition lemma [bool_case_linhom_gen_alpha_beta] reads
    off [bool_case_addD] / [bool_case_zero] at the [linhom_car] level. *)

Section AlphaBetaLinhom.
Variables (R : realType) (Ar : MeasSubcat R) (A : ICone.type Ar).

Local Notation T := (bool_cone_car Ar).

(** [alpha_linhom a] — the [bc_t · a] half, as a [linhom_car T A]. *)
Definition alpha_linhom (a : A) : linhom_car Ar T A :=
  bool_case_linhom_gen a precone_zero.

(** [beta_linhom b] — the [bc_f · b] half, as a [linhom_car T A]. *)
Definition beta_linhom (b : A) : linhom_car Ar T A :=
  bool_case_linhom_gen precone_zero b.

(** Pointwise reading: [alpha_linhom a] is exactly [x ↦ bc_t(x) · a].

    Indeed [bool_case x a 0 = bc_t(x)·a + bc_f(x)·0 = bc_t(x)·a + 0
    = bc_t(x)·a] by [precone_scale_0r] and [precone_addC]/[precone_add0]. *)
Lemma alpha_linhomE (a : A) (x : T) :
  linhom_fun (alpha_linhom a) x = precone_scale (bc_t x) a.
Proof.
rewrite /alpha_linhom /=.
rewrite -[linhom_fun _ _]/(bool_case x a precone_zero).
rewrite /bool_case.
by rewrite precone_scale_0r precone_addC precone_add0.
Qed.

(** Pointwise reading: [beta_linhom b] is exactly [x ↦ bc_f(x) · b]. *)
Lemma beta_linhomE (b : A) (x : T) :
  linhom_fun (beta_linhom b) x = precone_scale (bc_f x) b.
Proof.
rewrite /beta_linhom /=.
rewrite -[linhom_fun _ _]/(bool_case x precone_zero b).
rewrite /bool_case.
by rewrite precone_scale_0r precone_add0.
Qed.

(** [bool_case x a b = α(x, a) + β(x, b)] — the sum-decomposition lemma,
    read pointwise on [linhom_car].  This is the operative identity
    behind Step 2: [bool_case_linhom_gen a b] factors as a SUM of two
    BILINEAR pieces, even though [bool_case] itself is not bilinear in
    [(a, b)]. *)
Lemma bool_case_linhom_gen_alpha_beta (a b : A) (x : T) :
  linhom_fun (bool_case_linhom_gen a b) x =
  precone_add (linhom_fun (alpha_linhom a) x) (linhom_fun (beta_linhom b) x).
Proof.
by rewrite alpha_linhomE beta_linhomE.
Qed.

(** Operator-norm bounds:
    - [‖α(·, a)‖ ≤ max(‖a‖, 0)] (the [b = 0] specialisation of
      [bool_case_linhom_gen_norm_le], using [cone_norm0]),
    - [‖β(·, b)‖ ≤ max(‖b‖, 0)] (symmetrically). *)
Lemma alpha_linhom_norm_le (a : A) :
  cone_norm (alpha_linhom a) <= Num.max (cone_norm a) 0%R.
Proof.
have H := bool_case_linhom_gen_norm_le a (precone_zero : A).
rewrite cone_norm0 in H.
by rewrite -maxA maxxx in H.
Qed.

Lemma beta_linhom_norm_le (b : A) :
  cone_norm (beta_linhom b) <= Num.max (cone_norm b) 0%R.
Proof.
have H := bool_case_linhom_gen_norm_le (precone_zero : A) b.
rewrite cone_norm0 in H.
rewrite [Num.max 0%R _]maxC in H.
by rewrite -maxA maxxx in H.
Qed.

End AlphaBetaLinhom.

Arguments alpha_linhom {R Ar A} a.
Arguments beta_linhom {R Ar A} b.
Arguments alpha_linhomE {R Ar A} a x.
Arguments beta_linhomE {R Ar A} b x.
Arguments bool_case_linhom_gen_alpha_beta {R Ar A} a b x.
Arguments alpha_linhom_norm_le {R Ar A} a.
Arguments beta_linhom_norm_le {R Ar A} b.
