(**md**************************************************************************)
(** * Headline PPL examples — three QBS-style probabilistic programs in
       direct-style named surface syntax, with structural reduction lemmas

    Three end-to-end examples for the DIRECT-STYLE named-variable PPL
    of [theories/programs/ppl.v], each written in the [ppl_named]
    custom entry and paired with a [_denot_E] structural reduction
    lemma exposing the outer [kbind_ext]-shape of its denotation.

    Direct style: the source language exposes no probability-monad
    marker.  The function type [tfun tR tR] (NOT [tprob (tfun tR tR)])
    is itself the Kleisli exponential at the semantic level (its
    interpretation [tyD (tfun A B) = !̃(U A ⊸ U(T B))] carries the
    monad in the codomain).  All effects are implicit; the [kbind_ext]
    structure surfaces only at the level of [eD].

    - [ex_random_constant mu Hmu]: [let "c" := sample mu in λx. c]
      of type [tfun tR tR] — the QBS-paper-flagship "distribution over
      a function space" example.  The reduction lemma
      [ex_random_constant_denot_E] exposes [kbind_ext lam_denot
      sample_denot].
    - [ex_random_linear mu Hmu]: [let "m" := sample mu in
      let "b" := sample mu in λx. m * x + b] of type [tfun tR tR] —
      exercises [ne_add] and [ne_mul]; the reduction lemma exposes
      the nested [kbind_ext] form.
    - [ex_bayes_linear mu Hmu f Hf_…]: [let "m" := sample mu in
      let "_" := score { f, … } #"m" in #"m"] of type [tR] — the
      textbook prior/score/return shape, the only example exercising
      [ne_score].  The reduction [ex_bayes_linear_denot_E] exposes
      the outer [kbind_ext score_then_return_denot sample_denot]
      form.  This is the UNNORMALISED posterior (no [qbs_normalize]);
      we claim only that the denotation matches the expected
      joint-pushforward-then-density reduction. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import measure dirac_measure.

From Stdlib Require Import Strings.String.

Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.cone_cat.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.icones.icone.
Require Import Icones.homs.coalgebra.
Require Import Icones.homs.em_cat.
Require Import Icones.programs.cbv.
Require Import Icones.programs.ppl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** Example 1 — [ex_random_constant] *)

Section RandomConstant.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Variable (mu : fmeas R (ar_carrier Ar R_obj)).
Hypothesis Hmu : (cone_norm mu <= 1)%R.

Local Notation tR' := (tR R_obj).

(** The PPL term: [let "c" := sample mu in λ x. c] in surface syntax. *)
Definition ex_random_constant :
    @named_expr R Ar R_obj nil (tfun tR' tR') :=
  [ let "c" := Sample (mu , Hmu) in \ "x" ::: tR' => # "c" ].

(** Its denotation — a Kleisli arrow [⟦[]⟧ ⇝ ⟦tfun tR tR⟧]. *)
Definition ex_random_constant_denot :
    coalg_hom (ctxD (drop_names nil)) (Tobj (tyD (tfun tR' tR'))) :=
  @eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas
      nil (tfun tR' tR') ex_random_constant.

(** The lambda body extracted as a named-syntax sub-term, in the
    extended context [("c", tR) :: nil]. *)
Definition ex_rc_lam :
    @named_expr R Ar R_obj (("c"%string, tR') :: nil) (tfun tR' tR') :=
  [ \ "x" ::: tR' => # "c" ].

(** The structural reduction: [eD_let] is [kbind_ext]; the trailing
    pure expression's eD is the kreturn-wrapped value, automatically
    consumed by the outer [kbind_ext].  The denotation reads as
    [kbind_ext (eD ex_rc_lam) (eD (ne_sample mu Hmu))]. *)
Lemma ex_random_constant_denot_E :
  ex_random_constant_denot =
  kbind_ext
    (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _ ex_rc_lam)
    (sample_kleisli (ctxD (drop_names nil)) mu Hmu).
Proof.
rewrite /ex_random_constant_denot /ex_random_constant.
rewrite eD_let eD_sample.
by [].
Qed.

End RandomConstant.

Arguments ex_rc_lam {R Ar R_obj}.
Arguments ex_random_constant {R Ar R_obj} mu Hmu.
Arguments ex_random_constant_denot
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} mu Hmu.
Arguments ex_random_constant_denot_E
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} mu Hmu.

(** ** Example 2 — [ex_random_linear] *)

Section RandomLinear.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Variable (mu : fmeas R (ar_carrier Ar R_obj)).
Hypothesis Hmu : (cone_norm mu <= 1)%R.

Local Notation tR' := (tR R_obj).

(** The PPL term:
    [let "m" := sample mu in let "b" := sample mu in λx. m*x + b]. *)
Definition ex_random_linear :
    @named_expr R Ar R_obj nil (tfun tR' tR') :=
  [ let "m" := Sample (mu , Hmu) in
    let "b" := Sample (mu , Hmu) in
    \ "x" ::: tR' => # "m" * # "x" + # "b" ].

(** The inner ([("m", tR) :: nil]-context) continuation
    after the outer [m]-bind: [let "b" := sample mu in λx. m*x+b]. *)
Definition ex_rl_inner :
    @named_expr R Ar R_obj
      (("m"%string, tR') :: nil) (tfun tR' tR') :=
  [ let "b" := Sample (mu , Hmu) in
    \ "x" ::: tR' => # "m" * # "x" + # "b" ].

(** The lambda closure: in context [("b", tR) :: ("m", tR) :: nil], the
    function [λx. m*x + b]. *)
Definition ex_rl_lam :
    @named_expr R Ar R_obj
      (("b"%string, tR') :: ("m"%string, tR') :: nil) (tfun tR' tR') :=
  [ \ "x" ::: tR' => # "m" * # "x" + # "b" ].

(** Its denotation. *)
Definition ex_random_linear_denot :
    coalg_hom (ctxD (drop_names nil)) (Tobj (tyD (tfun tR' tR'))) :=
  @eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas
      nil (tfun tR' tR') ex_random_linear.

(** Structural reduction — exposes the nested-[kbind_ext] form.

    [ex_random_linear_denot
       = kbind_ext (kbind_ext (eD ex_rl_lam) (sample_kleisli mu))
                   (sample_kleisli mu)].
    The outer [kbind_ext] is the [m]-draw; its continuation is the
    [b]-draw's [kbind_ext] continued by [eD ex_rl_lam], the lambda
    closure denotation. *)
Lemma ex_random_linear_denot_E :
  ex_random_linear_denot =
  kbind_ext
    (kbind_ext
       (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _
            ex_rl_lam)
       (sample_kleisli
          (ctxD (drop_names (("m"%string, tR') :: nil))) mu Hmu))
    (sample_kleisli (ctxD (drop_names nil)) mu Hmu).
Proof.
rewrite /ex_random_linear_denot /ex_random_linear.
rewrite eD_let eD_let !eD_sample.
by [].
Qed.

End RandomLinear.

Arguments ex_rl_inner {R Ar R_obj} mu Hmu.
Arguments ex_rl_lam {R Ar R_obj}.
Arguments ex_random_linear {R Ar R_obj} mu Hmu.
Arguments ex_random_linear_denot
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} mu Hmu.
Arguments ex_random_linear_denot_E
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} mu Hmu.

(** ** Example 3 — [ex_bayes_linear] *)

Section BayesLinear.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Variable (mu : fmeas R (ar_carrier Ar R_obj)).
Hypothesis Hmu : (cone_norm mu <= 1)%R.

Variable (f : R -> R).
Hypothesis Hf_meas : measurable_fun [set: R] f.
Hypothesis Hf_ge0 : forall r : R, (0 <= f r)%R.
Hypothesis Hf_le1 : forall r : R, (f r <= 1)%R.

Local Notation tR' := (tR R_obj).

(** The PPL term in surface syntax:
    [let "m" := sample mu in let "_" := score { f, … } #"m" in #"m"]. *)
Definition ex_bayes_linear :
    @named_expr R Ar R_obj nil tR' :=
  [ let "m" := Sample (mu , Hmu) in
    let "_" := Score { f , Hf_meas , Hf_ge0 , Hf_le1 } # "m" in
    # "m" ].

(** The continuation under the prior bind, in context [("m", tR) :: nil]:
    [let "_" := score { f, … } #"m" in #"m"]. *)
Definition ex_bl_cont :
    @named_expr R Ar R_obj (("m"%string, tR') :: nil) tR' :=
  [ let "_" := Score { f , Hf_meas , Hf_ge0 , Hf_le1 } # "m" in
    # "m" ].

(** Its denotation. *)
Definition ex_bayes_linear_denot :
    coalg_hom (ctxD (drop_names nil)) (Tobj (tyD tR')) :=
  @eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas
      nil tR' ex_bayes_linear.

(** Structural reduction.

    [ex_bayes_linear_denot
       = kbind_ext (eD ex_bl_cont) (sample_kleisli mu Hmu)].

    The outer-most layer is the prior bind, exposed by [eD_let] and
    [eD_sample].  The inner continuation [eD ex_bl_cont] is itself a
    [kbind_ext] of the score-then-pure-variable shape, but the
    headline asserts only the OUTER reduction (the inner one follows
    by re-applying [eD_let] / [eD_score] — the [score_lift_dirac]
    identity is what would give a Dirac-input point-reduction, but
    we do not commit to that here). *)
Lemma ex_bayes_linear_denot_E :
  ex_bayes_linear_denot =
  kbind_ext
    (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas
         _ _ ex_bl_cont)
    (sample_kleisli (ctxD (drop_names nil)) mu Hmu).
Proof.
rewrite /ex_bayes_linear_denot /ex_bayes_linear.
rewrite eD_let eD_sample.
by [].
Qed.

End BayesLinear.

Arguments ex_bl_cont {R Ar R_obj} f Hf_meas Hf_ge0 Hf_le1.
Arguments ex_bayes_linear {R Ar R_obj} mu Hmu f Hf_meas Hf_ge0 Hf_le1.
Arguments ex_bayes_linear_denot
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}
  mu Hmu f Hf_meas Hf_ge0 Hf_le1.
Arguments ex_bayes_linear_denot_E
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}
  mu Hmu f Hf_meas Hf_ge0 Hf_le1.
