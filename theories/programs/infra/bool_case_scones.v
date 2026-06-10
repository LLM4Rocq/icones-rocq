(**md*** CBN PPL chapter infrastructure

    This file is NOT part of the Ehrhard-Geoffroy 2025 formalization
    (paper §2-§9). It packages the constant SCones-arrow at an arbitrary
    unit-ball point and the [bool_case]-by-an-icones-hom SCones-arrow,
    the two combinators consumed by the CBN PPL's M4 (boolean) clauses
    in [theories/programs/ppl_cbn_bool.v].

    See also: [theories/programs/infra/bool_cone.v] (the 2-point
    [bool_cone_car Ar] and the universal co-pairing [bool_case]),
    [theories/programs/infra/bool_case_hom.v] (the icones_hom packaging
    of [bool_case] for FIXED branches), [theories/programs/ppl_cbn.v]
    (the CBN PPL trunk parameterised by the boolean stubs), and
    [theories/stable/scones_cat.v] (the SCones category and [ders]
    inclusion). *)

(** * Constant SCones-arrows and the bool_case bridge

    Two combinators:

    - [scones_const c Hc] : for [c : A] in the unit ball (witness [Hc]),
      the constant SCones-arrow [scones_hom B A] mapping every ball
      point to [c] and every off-ball point to [precone_zero].
      Constructed by hand from [MkSconesHom] using the cone-sum of a
      constant ([big_const]) for total monotonicity, the trivial
      bound for boundedness, and [const_path_measurable] for path
      preservation.  The constant clauses [cbn_true_clause],
      [cbn_false_clause], [cbn_bernoulli_clause] of [ppl_cbn_bool.v]
      are immediate specializations to [c := bool_dirac_true]/
      [bool_dirac_false]/[bernoulli p Hp_ge0 Hp_le1].

    - [bool_case_fixed_scones a b Ha Hb] : for [a, b : A] in the unit
      ball, the SCones-arrow [scones_hom (bool_cone_car Ar) A] arising
      as [ders (bool_case_icones_hom a b Ha Hb)].  Pure post-composition
      of [bool_case_icones_hom] of [bool_case_hom.v] with the [ders]
      bridge of [scones_cat.v]; the soundness lemmas
      [bool_case_fixed_scones_true_E] / [bool_case_fixed_scones_false_E]
      follow definitionally on the unit ball.

    The variable-branch [if]-combinator
    [bool_case_scones : scones_hom (sprod B (sprod A A)) A]
    is NOT delivered as a universal combinator here.  The
    bilinearity-in-[(a, b)] of [bool_case] (cf. [theories/programs/ppl.v]'s
    [case_em] comment block, lines around 2466) — [bool_case x (a₁+a₂) b
    ≠ bool_case x a₁ b + bool_case x a₂ b] — means there is no direct
    [is_meas_stable] proof for a tri-argument [bool_case] viewed as a
    map from [sprod B (sprod A A)] to [A].  The CBN [ne_if] clause of
    [ppl_cbn_bool.v]'s [cbn_if_clause_def] sidesteps this obstruction
    by promoting the branches [M, N] to POINTS of the SCones internal
    hom [stablehom (ctxD_CBN G) (tyD_CBN t)] (via [sc_to_sh] of
    [theories/homs/seely.v]), where [bool_case_linhom] of
    [bool_case_hom.v] applies verbatim with the per-branch
    operator-norm bounds.  This is the [case_em] strategy of [ppl.v]
    adapted to the SCones layer (NO bang, NO SAFT). *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import measurable_structure measurable_function.

Require Import Icones.prelude.classical_extra.
Require Import Icones.prelude.nonneg_extra.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.omega_general.
Require Import Icones.cones.cone_cat.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.path.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_cat.
Require Import Icones.stable.totmono.
Require Import Icones.stable.scones_cat.
Require Import Icones.programs.infra.bool_cone.
Require Import Icones.homs.linhom.
Require Import Icones.homs.seely.
Require Import Icones.programs.infra.bool_case_hom.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** [scones_const c Hc] — constant SCones-arrow at a unit-ball point

    For [c : A] in the unit ball, the constant map [fun _ => c] is
    stable-and-measurable (totmono by the cone-sum of a constant
    [big_const] + [big_Pneg_le_Ppos]; boundedness with witness
    [cone_norm c]; Scott-continuity since the image chain is constant;
    path preservation via [const_path_measurable]).  The 0-extension
    off the unit ball is enforced by the record-level [sc_clamp]. *)

Section SconesConst.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (B A : ICone.type Ar).
Variable c : A.
Hypothesis Hc : (cone_norm c <= 1)%R.

Local Open Scope precone_scope.

(** The bare constant function. *)
Definition scones_const_fun : B -> A := fun _ => c.

(** Total monotonicity of a constant: both (7.1) sums equal
    [cardinality *: c], and [#|Pneg n| <= #|Ppos n|] for [n >= 1]
    (and the [n = 0] case is trivial). *)
Lemma scones_const_totmono : is_totmono scones_const_fun.
Proof.
move=> n x u _; rewrite /scones_const_fun.
exact: big_Pneg_le_Ppos.
Qed.

(** Boundedness: constant norm [cone_norm c <= 1]. *)
Lemma scones_const_bounded :
  exists M : R, forall x : B,
    cone_norm x <= 1 -> cone_norm (scones_const_fun x) <= M.
Proof. by exists 1 => x _; rewrite /scones_const_fun; exact: Hc. Qed.

(** Scott continuity on the unit ball: image chain is constant [c]. *)
Lemma scones_const_scott : is_scott_continuous_unit scones_const_fun.
Proof.
move=> Mf u uch ub1 fuch fubMf Mfpos.
rewrite /scones_const_fun.
apply: precone_le_anti.
- have := cone_sup_at_ub fuch fubMf Mfpos 0%N.
  by rewrite /scones_const_fun.
- apply: cone_sup_at_lub => n /=; rewrite /scones_const_fun.
  exact: precone_le_refl.
Qed.

Lemma scones_const_stable : is_stable scones_const_fun.
Proof.
split.
- exact: scones_const_totmono.
- exact: scones_const_bounded.
- exact: scones_const_scott.
Qed.

(** Path preservation: a constant path is measurable. *)
Lemma scones_const_pres_path
    (X : ar_obj Ar) (γ : ar_carrier Ar X -> B) :
  (forall r, cone_norm (γ r) <= 1) ->
  is_measurable_path γ ->
  is_measurable_path (fun r => scones_const_fun (γ r)).
Proof. by move=> _ _; exact: const_path_measurable. Qed.

Lemma scones_const_meas_stable : is_meas_stable scones_const_fun.
Proof.
split; first exact: scones_const_stable.
exact: scones_const_pres_path.
Qed.

(** Stability under [sc_clamp]: the clamped constant is meas-stable. *)
Lemma scones_const_clamp_meas_stable :
  is_meas_stable (sc_clamp scones_const_fun).
Proof. exact: sc_clamp_meas_stable scones_const_meas_stable. Qed.

(** Operator-norm bound: on the ball the image norm is [cone_norm c <= 1]. *)
Lemma scones_const_norm_le1 : sc_norm (sc_clamp scones_const_fun) <= 1.
Proof.
apply: sc_norm_lub => x Hx.
by rewrite (sc_clamp_ball Hx) /scones_const_fun; exact: Hc.
Qed.

(** The constant SCones-arrow at [c]. *)
Definition scones_const : scones_hom B A :=
  MkSconesHom (sc_clamp scones_const_fun) scones_const_clamp_meas_stable
              scones_const_norm_le1 (sc_clamp_offball_field _).

(** On the unit ball, [scones_const] computes to [c]. *)
Lemma scones_const_E (x : B) :
  cone_norm x <= 1 -> sc_fun scones_const x = c.
Proof. by move=> Hx; rewrite /= (sc_clamp_ball Hx). Qed.

End SconesConst.

Arguments scones_const_fun {R Ar B A} c.
Arguments scones_const {R Ar} B {A} c Hc.
Arguments scones_const_E {R Ar B A c} Hc x.

(** ** [bool_case_fixed_scones] — [bool_case]-by-a-pair-of-fixed-points

    For [a, b : A] in the unit ball, the [bool_case_icones_hom] of
    [bool_case_hom.v] is an [icones_hom Ar (bool_cone_car Ar) A]; we
    lift it to [scones_hom (bool_cone_car Ar) A] by [ders] of
    [scones_cat.v].

    This delivers the cone-level [if]-then-else combinator at FIXED
    branches.  The variable-branch CBN [ne_if] clause is handled at
    the per-context application level in [ppl_cbn_bool.v]: rather
    than a universal combinator from [sprod B (sprod A A)] (which is
    obstructed by [bool_case]'s non-bilinearity in [(a, b)] — see the
    file header), the clause assembles the result pointwise. *)

Section BoolCaseFixedScones.
Variables (R : realType) (Ar : MeasSubcat R) (A : ICone.type Ar).
Variables (a b : A).
Hypotheses (Ha : (cone_norm a <= 1)%R) (Hb : (cone_norm b <= 1)%R).

Local Notation T := (bool_cone_car Ar).

(** The SCones-side [bool_case]-by-fixed-points morphism. *)
Definition bool_case_fixed_scones : scones_hom T A :=
  ders (bool_case_icones_hom a b Ha Hb).

(** General-purpose computation on the unit ball: [bool_case_fixed_scones x =
    bool_case x a b]. *)
Lemma bool_case_fixed_scones_E (x : T) :
  cone_norm x <= 1 -> sc_fun bool_case_fixed_scones x = bool_case x a b.
Proof.
move=> Hx; rewrite /bool_case_fixed_scones /ders /= (sc_clamp_ball Hx).
by rewrite /bool_case_icones_hom /linhom_icones /=.
Qed.

(** Soundness on the true Dirac:
    [bool_case_fixed_scones bool_dirac_true = a]. *)
Lemma bool_case_fixed_scones_true_E :
  sc_fun bool_case_fixed_scones bool_dirac_true = a.
Proof.
have Hbt : cone_norm (bool_dirac_true : T) <= 1
  by rewrite bool_dirac_true_norm.
by rewrite (bool_case_fixed_scones_E Hbt); exact: bool_case_true.
Qed.

(** Soundness on the false Dirac:
    [bool_case_fixed_scones bool_dirac_false = b]. *)
Lemma bool_case_fixed_scones_false_E :
  sc_fun bool_case_fixed_scones bool_dirac_false = b.
Proof.
have Hbf : cone_norm (bool_dirac_false : T) <= 1
  by rewrite bool_dirac_false_norm.
by rewrite (bool_case_fixed_scones_E Hbf); exact: bool_case_false.
Qed.

End BoolCaseFixedScones.

Arguments bool_case_fixed_scones {R Ar A} a b Ha Hb.
Arguments bool_case_fixed_scones_true_E {R Ar A} a b Ha Hb.
Arguments bool_case_fixed_scones_false_E {R Ar A} a b Ha Hb.
Arguments bool_case_fixed_scones_E {R Ar A} a b Ha Hb x.
