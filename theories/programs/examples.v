(**md**************************************************************************)
(** * Headline PPL examples — surface programs in direct-style named syntax

    Eleven surface programs for the named-variable PPL of
    [theories/programs/ppl.v], each written in the [ppl_named] custom
    entry [[ … ]].  This file is now the SHARED SURFACE PROGRAM POOL
    for both CBN ([theories/programs/ppl_cbn*.v]) and CBV
    ([theories/programs/ppl_cbv.v]); the denotational machinery and
    structural reduction lemmas previously living here against the
    OLD CBV [eD] have been retired and are being re-grown at the
    linhom level inside the new [ppl_cbv.v].

    ** QBS-headline examples (1–3)
    - [ex_random_constant]   : [let "c" := sample mu in λx. c]
    - [ex_random_linear]     : [let "m" := sample mu in
                                let "b" := sample mu in
                                λx. m * x + b]
    - [ex_bayes_linear]      : [let "m" := sample mu in
                                let "_" := score(f) #"m" in
                                #"m"]

    ** Recursive partial-termination examples (4–6)
    - [ex_loop]              : [(let rec l = λ_. l ()) ()]
    - [ex_geom]              : geometric counter (mass 1)
    - [ex_almost_loop p]     : parameterised partial divergence (mass p)

    ** Boolean / if-then-else sanity checks
    - [ex_true], [ex_false], [ex_fair_coin], [ex_if_demo] *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals constructive_ereal.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import ereal.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import measure dirac_measure.
From mathcomp.analysis Require Import lebesgue_integral_definition numfun.

From Stdlib Require Import Strings.String.

Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.cone_cat.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.mcones.path.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_integral.
Require Import Icones.icones.icone_cat.
Require Import Icones.homs.linhom.
Require Import Icones.homs.bilin.
Require Import Icones.homs.tensor_hom_iso.
Require Import Icones.homs.exp_adjunction.
Require Import Icones.homs.bang.
Require Import Icones.homs.fmeas_lax.
Require Import Icones.homs.coalgebra.
Require Import Icones.homs.em_cat.
Require Import Icones.homs.em_seely_comonoid.
Require Import Icones.homs.em_cartesian.
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

Variable (mu : fmeas R (ar_carrier Ar R_obj)).
Hypothesis Hmu : (cone_norm mu <= 1)%R.

Local Notation tR' := (tR R_obj).

(** The PPL term: [let "c" := sample mu in λ x. c] in surface syntax. *)
Definition ex_random_constant :
    @named_expr R Ar R_obj nil (tfun tR' tR') :=
  [ let "c" := Sample (mu , Hmu) in \ "x" ::: tR' => # "c" ].

(** The lambda body extracted as a named-syntax sub-term, in the
    extended context [("c", tR) :: nil]. *)
Definition ex_rc_lam :
    @named_expr R Ar R_obj (("c"%string, tR') :: nil) (tfun tR' tR') :=
  [ \ "x" ::: tR' => # "c" ].

End RandomConstant.

Arguments ex_rc_lam {R Ar R_obj}.
Arguments ex_random_constant {R Ar R_obj} mu Hmu.

(** ** Example 2 — [ex_random_linear] *)

Section RandomLinear.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).

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

(** The inner continuation after the outer [m]-bind. *)
Definition ex_rl_inner :
    @named_expr R Ar R_obj
      (("m"%string, tR') :: nil) (tfun tR' tR') :=
  [ let "b" := Sample (mu , Hmu) in
    \ "x" ::: tR' => # "m" * # "x" + # "b" ].

(** The lambda closure body, in context [("b", tR) :: ("m", tR) :: nil]. *)
Definition ex_rl_lam :
    @named_expr R Ar R_obj
      (("b"%string, tR') :: ("m"%string, tR') :: nil) (tfun tR' tR') :=
  [ \ "x" ::: tR' => # "m" * # "x" + # "b" ].

End RandomLinear.

Arguments ex_rl_inner {R Ar R_obj} mu Hmu.
Arguments ex_rl_lam {R Ar R_obj}.
Arguments ex_random_linear {R Ar R_obj} mu Hmu.

(** ** Example 3 — [ex_bayes_linear] *)

Section BayesLinear.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).

Variable (mu : fmeas R (ar_carrier Ar R_obj)).
Hypothesis Hmu : (cone_norm mu <= 1)%R.

Variable (f : R -> R).
Hypothesis Hf_meas : measurable_fun [set: R] f.
Hypothesis Hf_ge0 : forall r : R, (0 <= f r)%R.
Hypothesis Hf_le1 : forall r : R, (f r <= 1)%R.

Local Notation tR' := (tR R_obj).

(** The PPL term:
    [let "m" := sample mu in let "_" := score(f) #"m" in #"m"]. *)
Definition ex_bayes_linear :
    @named_expr R Ar R_obj nil tR' :=
  [ let "m" := Sample (mu , Hmu) in
    let "_" := Score { f , Hf_meas , Hf_ge0 , Hf_le1 } # "m" in
    # "m" ].

(** The continuation under the prior bind. *)
Definition ex_bl_cont :
    @named_expr R Ar R_obj (("m"%string, tR') :: nil) tR' :=
  [ let "_" := Score { f , Hf_meas , Hf_ge0 , Hf_le1 } # "m" in
    # "m" ].

End BayesLinear.

Arguments ex_bl_cont {R Ar R_obj} f Hf_meas Hf_ge0 Hf_le1.
Arguments ex_bayes_linear {R Ar R_obj} mu Hmu f Hf_meas Hf_ge0 Hf_le1.

(** ** Example 4 — [ex_loop] — bare divergence *)

Section ExLoopDemo.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).

(** The divergence example.  Source: [(let rec l = λ _. l ()) ()]. *)
Definition ex_loop :
    @named_expr R Ar R_obj nil tunit :=
  [ (fix "l" ::: tfun tunit tunit in \ "_" ::: tunit => # "l" @ ()) @ () ].

End ExLoopDemo.

Arguments ex_loop {R Ar R_obj}.

(** ** Boolean primitives sanity check — [True], [False], [Bernoulli p] *)

Section ExBoolDemo.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).

Definition ex_true : @named_expr R Ar R_obj nil tbool := [ True ].

Definition ex_false : @named_expr R Ar R_obj nil tbool := [ False ].

Lemma half_ge0 : (0 <= 1 / 2 :> R)%R.
Proof. by rewrite divr_ge0// ler01. Qed.

Lemma half_le1 : (1 / 2 <= 1 :> R)%R.
Proof. by rewrite ler_pdivrMr ?mul1r ?ler1n. Qed.

Definition ex_fair_coin : @named_expr R Ar R_obj nil tbool :=
  [ Bernoulli { (1 / 2 : R), half_ge0, half_le1 } ].

End ExBoolDemo.

Arguments ex_true {R Ar R_obj}.
Arguments ex_false {R Ar R_obj}.
Arguments ex_fair_coin {R Ar R_obj}.

(** ** Example — [ex_if_demo] — if-then-else sanity check *)

Section ExIfDemo.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).

Lemma if_demo_half_ge0 : (0 <= 1 / 2 :> R)%R.
Proof. by rewrite divr_ge0// ler01. Qed.

Lemma if_demo_half_le1 : (1 / 2 <= 1 :> R)%R.
Proof. by rewrite ler_pdivrMr ?mul1r ?ler1n. Qed.

(** The closed [tbool]-typed [if-then-else] term:
    [if Bernoulli { 1/2 } then True else False]. *)
Definition ex_if_demo :
    @named_expr R Ar R_obj nil tbool :=
  [ if Bernoulli { (1 / 2 : R), if_demo_half_ge0, if_demo_half_le1 }
    then True else False ].

End ExIfDemo.

Arguments ex_if_demo {R Ar R_obj}.

(** ** Recursive partial-termination examples *)

Section RecExamples.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).

(** Witnesses [0 ≤ 1/2 ≤ 1] for the geometric example's fair-coin
    Bernoulli scrutinee. *)
Lemma bernoulli_half_ge0 : (0 <= 1 / 2 :> R)%R.
Proof. by rewrite divr_ge0// ler01. Qed.

Lemma bernoulli_half_le1 : (1 / 2 <= 1 :> R)%R.
Proof. by rewrite ler_pdivrMr ?mul1r ?ler1n. Qed.

Local Notation tR' := (tR R_obj).

(** *** [ex_geom] — geometric distribution
    Source: [(let rec g = λ_. if Bernoulli(½) then 0
                                            else 1 + g ()) ()]. *)

Definition ex_geom : @named_expr R Ar R_obj nil tR' :=
  [ (fix "g" ::: tfun tunit tR' in
       \ "_" ::: tunit =>
         (if Bernoulli { (1 / 2 : R), bernoulli_half_ge0, bernoulli_half_le1 }
          then [| 0%R |]
          else [| 1%R |] + # "g" @ ())) @ () ].

(** The body of the fixed-point lambda. *)
Definition ex_geom_body :
    @named_expr R Ar R_obj
      (("g"%string, tfun tunit tR') :: nil)
      (tfun tunit tR') :=
  [ \ "_" ::: tunit =>
      (if Bernoulli { (1 / 2 : R), bernoulli_half_ge0, bernoulli_half_le1 }
       then [| 0%R |]
       else [| 1%R |] + # "g" @ ()) ].

(** *** [ex_almost_loop p Hp_ge0 Hp_le1] — parameterised divergence
    Source: [(let rec l = λ_. if Bernoulli(p) then ()
                                              else l ()) ()]. *)
Definition ex_almost_loop (p : R)
    (Hp_ge0 : (0 <= p)%R) (Hp_le1 : (p <= 1)%R) :
    @named_expr R Ar R_obj nil tunit :=
  [ (fix "l" ::: tfun tunit tunit in
       \ "_" ::: tunit =>
         (if Bernoulli { p, Hp_ge0, Hp_le1 }
          then ()
          else # "l" @ ())) @ () ].

(** Its lambda body, in the extended context
    [("l", tfun tunit tunit) :: nil]. *)
Definition ex_almost_loop_body (p : R)
    (Hp_ge0 : (0 <= p)%R) (Hp_le1 : (p <= 1)%R) :
    @named_expr R Ar R_obj
      (("l"%string, tfun tunit tunit) :: nil)
      (tfun tunit tunit) :=
  [ \ "_" ::: tunit =>
      (if Bernoulli { p, Hp_ge0, Hp_le1 }
       then ()
       else # "l" @ ()) ].

End RecExamples.

Arguments ex_geom {R Ar R_obj}.
Arguments ex_geom_body {R Ar R_obj}.
Arguments ex_almost_loop {R Ar R_obj} p Hp_ge0 Hp_le1.
Arguments ex_almost_loop_body {R Ar R_obj} p Hp_ge0 Hp_le1.
