(**md*** CBN PPL [ex_almost_loop p] mass closure

    [ex_almost_loop_p_CBN_mass_one_if_pos] (when
    [p > 0]) and [ex_almost_loop_p_CBN_mass_zero_if_zero] (when
    [p = 0]): the CBN-side fixpoint of the parameterised partial-
    termination operator [phi_almost_loop_p] has the expected mass.

    ** Refactored as an instance of the [BernoulliCascade] framework

    The shared Bernoulli-cascade machinery lives in
    [theories/programs/infra/cbn_bernoulli_cascade.v].
    [ex_almost_loop p] is the instance with [p := p],
    [halt := δ_0], [cont_op := scones_id (FMeas R_obj)].

    Per-iterate decomposition:
    [[
       phi_almost_loop_p μ
         = if Bernoulli(p) then δ_0 else μ
         = p *: δ_0 + (1 - p) *: μ.
    ]]
    Hence [mass(kleene^n) = 1 - (1 - p)^n].

    - When [p > 0]: [(1 - p) < 1], so [(1 - p)^n → 0] and
      [mass → 1].
    - When [p = 0]: [(1 - p)^n = 1] for all [n], so
      [mass = 0] uniformly.

    ** Author

    Guillaume Baudart <guillaume.baudart@inria.fr>. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals signed constructive_ereal.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import measure dirac_measure.
From mathcomp.analysis Require Import sequences ereal normedtype topology.

From Stdlib Require Import Strings.String.

Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.cone_cat.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.mcones.path.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_cat.
Require Import Icones.homs.linhom.
Require Import Icones.homs.bilin.
Require Import Icones.homs.coalgebra.
Require Import Icones.homs.seely_defs.
Require Import Icones.homs.seely.
Require Import Icones.programs.infra.bool_cone.
Require Import Icones.stable.totmono.
Require Import Icones.stable.stablehom.
Require Import Icones.stable.scones_cat.
Require Import Icones.stable.fixpoint.
Require Import Icones.stable.scones_ccc.
Require Import Icones.programs.infra.bool_case_hom.
Require Import Icones.programs.infra.bool_case_scones.
Require Import Icones.programs.ppl.
Require Import Icones.programs.examples.
Require Import Icones.programs.ppl_cbn.
Require Import Icones.programs.ppl_cbn_eff.
Require Import Icones.programs.ppl_cbn_bool.
Require Import Icones.programs.ppl_cbn_arith.
Require Import Icones.programs.ppl_cbn_headlines.
Require Import Icones.programs.infra.cbn_bernoulli_cascade.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** §1 — Instantiation of [BernoulliCascade] for [ex_almost_loop p]

    [halt := δ_0], [cont_op := scones_id]. *)

Section ExAlmostLoopPCBN.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.

Variable (p : R).
Hypothesis Hp_ge0 : (0 <= p)%R.
Hypothesis Hp_le1 : (p <= 1)%R.

(** The [δ_0] halt value with its unit-ball witness and mass identity. *)
Local Notation halt_alp :=
  (dirac_fmeas (R_to_carrier R_carrier_eq 0%R) : FMeas R_obj).

Lemma halt_alp_ball : (cone_norm halt_alp <= 1)%R.
Proof. exact: dirac_fmeas_norm_le1. Qed.

Local Open Scope ereal_scope.
Lemma halt_alp_mass : fmeas_mu halt_alp [set: ar_carrier Ar R_obj] = 1.
Proof. exact: dirac_fmeas_setT_E. Qed.
Local Close Scope ereal_scope.

(** Mass preservation by the identity continuation. *)
Local Open Scope ereal_scope.
Lemma scones_id_mass_pres (mu : FMeas R_obj) :
  (cone_norm mu <= 1)%R ->
  (fmeas_mu (sc_fun (scones_id (FMeas R_obj)) mu) [set: ar_carrier Ar R_obj]
   = fmeas_mu mu [set: ar_carrier Ar R_obj])%E.
Proof.
move=> Hmu.
by rewrite /scones_id /= (sc_clamp_ball Hmu).
Qed.
Local Close Scope ereal_scope.

(** The framework operator for [ex_almost_loop p]. *)
Definition phi_almost_loop_p : scones_hom (FMeas R_obj) (FMeas R_obj) :=
  phi_bcascade p Hp_ge0 Hp_le1 halt_alp halt_alp_ball
               (scones_id (FMeas R_obj)).

(** The [sfix]-level fixpoint. *)
Definition ex_almost_loop_p_CBN_fix : FMeas R_obj :=
  sfix_bcascade p Hp_ge0 Hp_le1 halt_alp halt_alp_ball
                (scones_id (FMeas R_obj)).

Local Open Scope ereal_scope.

(** *** Headline 1 — when [p > 0], the fixpoint has mass 1. *)
Theorem ex_almost_loop_p_CBN_mass_one_if_pos :
  (0 < p)%R ->
  fmeas_mu ex_almost_loop_p_CBN_fix [set: ar_carrier Ar R_obj] = 1%:E.
Proof.
move=> Hp_pos.
rewrite /ex_almost_loop_p_CBN_fix.
apply: sfix_bcascade_mass_one_if_pos.
- exact: halt_alp_mass.
- exact: scones_id_mass_pres.
- exact: Hp_pos.
Qed.

(** *** Headline 2 — when [p = 0], the fixpoint has mass 0. *)
Theorem ex_almost_loop_p_CBN_mass_zero_if_zero :
  p = 0%R ->
  fmeas_mu ex_almost_loop_p_CBN_fix [set: ar_carrier Ar R_obj] = 0%E.
Proof.
move=> Hp_zero.
rewrite /ex_almost_loop_p_CBN_fix.
apply: sfix_bcascade_mass_zero_if_zero.
- exact: halt_alp_mass.
- exact: scones_id_mass_pres.
- exact: Hp_zero.
Qed.
Local Close Scope ereal_scope.

End ExAlmostLoopPCBN.

Arguments phi_almost_loop_p {R Ar R_obj} R_carrier_eq p Hp_ge0 Hp_le1.
Arguments ex_almost_loop_p_CBN_fix {R Ar R_obj} R_carrier_eq p Hp_ge0 Hp_le1.
Arguments ex_almost_loop_p_CBN_mass_one_if_pos
  {R Ar R_obj} R_carrier_eq p Hp_ge0 Hp_le1.
Arguments ex_almost_loop_p_CBN_mass_zero_if_zero
  {R Ar R_obj} R_carrier_eq p Hp_ge0 Hp_le1.
