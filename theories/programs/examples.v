(**md**************************************************************************)
(** * Headline PPL examples — surface programs in direct-style named syntax

    Twelve surface programs for the named-variable PPL of
    [theories/programs/ppl.v], each written in the [ppl_named] custom
    entry [[ … ]].  This file is the SURFACE PROGRAM POOL for the CBV
    stack ([theories/programs/ppl_cbv.v]); the denotational machinery and
    structural reduction lemmas previously living here against the
    OLD CBV [eD] have been retired and are being re-grown at the
    linhom level inside the new [ppl_cbv.v].

    ** Basic sampling/scoring examples (1–3)
    - [ex_random_constant]   : [let "c" := sample mu in λx. c]
    - [ex_random_linear]     : [let "m" := sample mu in
                                let "b" := sample mu in
                                λx. m * x + b]
    - [ex_score_posterior]   : [let "m" := sample mu in
                                let "_" := score(f) #"m" in
                                #"m"]
      (sample-score-return: the unnormalised one-parameter posterior)

    ** Higher-order Bayesian linear regression
    - [ex_bayes_linear l]    : sample a FUNCTION [λx. s·x+b]
      (slope [s] and intercept [b] from the prior), score one
      observation per [o ∈ l] of the function's value at a known
      input point, and return the function — the posterior over
      functions (arXiv 1701.02547 §2.1 shape); 3-observation
      instance [ex_bayes_linear3]

    ** Recursive partial-termination examples (4–6)
    - [ex_loop]              : [(let rec l = λ_. l ()) ()]
    - [ex_geom]              : geometric counter (mass 1)
    - [ex_almost_loop p]     : parameterised partial divergence (mass p)

    ** Boolean / if-then-else sanity checks
    - [ex_true], [ex_false], [ex_fair_coin], [ex_if_demo]

    ** Mutual recursion (product-of-functions fixpoint)
    - [ex_even_odd_pair]     : [fix_mr p : (1→1) × (1→1).
                                 (λn. snd p n, λn. fst p n)]
      with projections [ex_even] / [ex_odd] — the [ne_fix_mr]
      elaboration witness for the Seely-transported value-fixpoint

    ** Rejection sampling (the killer example)
    - [ex_reject]            : [(let rec rs = λaccept.
                                   let x = sample µ in
                                   if Bernoulli_f{f} x then accept x
                                   else rs accept) (λy. y)] *)

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
Require Import Icones.programs.ppl_cbv.

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

(** ** Example 3 — [ex_score_posterior]

    Sample one parameter, score it by a soft observation density [f],
    return it: the unnormalised one-parameter posterior.  (This program
    was historically misnamed "bayes_linear" — it is NOT a linear
    regression; the genuine higher-order Bayesian linear regression is
    [ex_bayes_linear] below.) *)

Section ScorePosterior.
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
Definition ex_score_posterior :
    @named_expr R Ar R_obj nil tR' :=
  [ let "m" := Sample (mu , Hmu) in
    let "_" := Score { f , Hf_meas , Hf_ge0 , Hf_le1 } # "m" in
    # "m" ].

(** The continuation under the prior bind. *)
Definition ex_sp_cont :
    @named_expr R Ar R_obj (("m"%string, tR') :: nil) tR' :=
  [ let "_" := Score { f , Hf_meas , Hf_ge0 , Hf_le1 } # "m" in
    # "m" ].

End ScorePosterior.

Arguments ex_sp_cont {R Ar R_obj} f Hf_meas Hf_ge0 Hf_le1.
Arguments ex_score_posterior {R Ar R_obj} mu Hmu f Hf_meas Hf_ge0 Hf_le1.

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

(** ** Example — [ex_even_odd] — mutual recursion at a product of functions

    The [ne_fix_mr] constructor binds ONE recursive name [p] at the
    free-coalgebra type [tprod (tfun tunit tunit) (tfun tunit tunit)] —
    a PAIR of functions; each component calls the other via the
    [fst]/[snd] projections of the rec-bound product.  This is the
    classic even/odd mutual-recursion SHAPE (each component immediately
    delegates to the other, so operationally it diverges — the point
    here is the elaboration smoke test for the genuine
    Seely-transported [fix_mr_comb] path of [ppl_cbv.v::fix_mr_clause];
    mass identities are out of scope). *)

Section ExEvenOdd.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).

Local Notation pair_ty := (tprod (tfun tunit tunit) (tfun tunit tunit)).

(** The two components, pre-named in the context extended with the rec
    name [p : pair_ty] (the lambda notation sits at a level above the
    pair-component level, so inline lambdas cannot syntactically be
    pair components — we splice them via the [{...}] escape). *)
Definition ex_even_odd_lam_a :
    @named_expr R Ar R_obj (("p"%string, pair_ty) :: nil)
                           (tfun tunit tunit) :=
  [ \ "n" ::: tunit => snd # "p" @ # "n" ].

Definition ex_even_odd_lam_b :
    @named_expr R Ar R_obj (("p"%string, pair_ty) :: nil)
                           (tfun tunit tunit) :=
  [ \ "n" ::: tunit => fst # "p" @ # "n" ].

(** The mutually-recursive function PAIR, bound under the single
    recursive name [p] (free-coalgebra witness: [erefl]). *)
Definition ex_even_odd_pair :
    @named_expr R Ar R_obj nil pair_ty :=
  [ fix_mr "p" as pair_ty by erefl
       in ({ex_even_odd_lam_a}, {ex_even_odd_lam_b}) ].

(** The two projections. *)
Definition ex_even :
    @named_expr R Ar R_obj nil (tfun tunit tunit) :=
  [ fst {ex_even_odd_pair} ].

Definition ex_odd :
    @named_expr R Ar R_obj nil (tfun tunit tunit) :=
  [ snd {ex_even_odd_pair} ].

(** The body of the [fix_mr] (for stating reduction lemmas). *)
Definition ex_even_odd_body :
    @named_expr R Ar R_obj (("p"%string, pair_ty) :: nil) pair_ty :=
  [ ({ex_even_odd_lam_a}, {ex_even_odd_lam_b}) ].

End ExEvenOdd.

Arguments ex_even_odd_lam_a {R Ar R_obj}.
Arguments ex_even_odd_lam_b {R Ar R_obj}.
Arguments ex_even_odd_pair {R Ar R_obj}.
Arguments ex_even {R Ar R_obj}.
Arguments ex_odd {R Ar R_obj}.
Arguments ex_even_odd_body {R Ar R_obj}.

(** ** Example — [ex_reject] — rejection sampling (THE killer example)

    Normalised-posterior rejection sampling: sample [x ~ µ], accept
    with probability [f x] (the value-dependent Bernoulli
    [ne_bernoulli_f]), and on rejection RECURSE.  The recursive
    function abstracts over the acceptance continuation [accept], and
    the headline instantiates it at the identity [λy. y] (so the
    program returns the accepted sample itself):
    [[
       (let rec rs = λ accept.
           let x = sample µ in
           if Bernoulli_f { f } x then accept x else rs accept)
         (λ y. y)
    ]]
    Expected denotation (the M4 headline): the sub-probability
    [ν] with [∫f dµ · ν(U) = ∫_U f dµ] — the normalised posterior,
    graceful at [∫f dµ = 0]. *)

Section RejectSampling.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).

Variable (mu : fmeas R (ar_carrier Ar R_obj)).
Hypothesis Hmu : (cone_norm mu <= 1)%R.

Variable (f : R -> R).
Hypothesis Hf_meas : measurable_fun [set: R] f.
Hypothesis Hf_ge0 : forall r : R, (0 <= f r)%R.
Hypothesis Hf_le1 : forall r : R, (f r <= 1)%R.

Local Notation tR' := (tR R_obj).

(** The full surface program: the recursive sampler applied to the
    identity acceptance continuation. *)
Definition ex_reject : @named_expr R Ar R_obj nil tR' :=
  [ (fix "rs" ::: tfun (tfun tR' tR') tR' in
       \ "accept" ::: (tfun tR' tR') =>
         (let "x" := Sample (mu , Hmu) in
          if Bernoulli_f { f , Hf_meas , Hf_ge0 , Hf_le1 } # "x"
          then # "accept" @ # "x"
          else # "rs" @ # "accept"))
    @ (\ "y" ::: tR' => # "y") ].

(** The body of the fixed-point lambda, in the extended context
    [("rs", (tR' -> tR') -> tR') :: nil] (the [ex_geom_body]
    pattern). *)
Definition ex_reject_body :
    @named_expr R Ar R_obj
      (("rs"%string, tfun (tfun tR' tR') tR') :: nil)
      (tfun (tfun tR' tR') tR') :=
  [ \ "accept" ::: (tfun tR' tR') =>
      (let "x" := Sample (mu , Hmu) in
       if Bernoulli_f { f , Hf_meas , Hf_ge0 , Hf_le1 } # "x"
       then # "accept" @ # "x"
       else # "rs" @ # "accept") ].

(** The sample-then-test inner expression under both binders, in
    context [("accept", tR' -> tR') :: ("rs", …) :: nil]. *)
Definition ex_reject_inner :
    @named_expr R Ar R_obj
      (("accept"%string, tfun tR' tR') ::
       ("rs"%string, tfun (tfun tR' tR') tR') :: nil)
      tR' :=
  [ let "x" := Sample (mu , Hmu) in
    if Bernoulli_f { f , Hf_meas , Hf_ge0 , Hf_le1 } # "x"
    then # "accept" @ # "x"
    else # "rs" @ # "accept" ].

End RejectSampling.

Arguments ex_reject {R Ar R_obj} mu Hmu f Hf_meas Hf_ge0 Hf_le1.
Arguments ex_reject_body {R Ar R_obj} mu Hmu f Hf_meas Hf_ge0 Hf_le1.
Arguments ex_reject_inner {R Ar R_obj} mu Hmu f Hf_meas Hf_ge0 Hf_le1.

(** ** CBV denotations — [ppl_cbv.v]'s [eD] applied to every closed example

    One definition per closed surface program above: these are the
    CBV-side entry points for the headline lemmas to come, and they
    double as a compile-time smoke test of the interpreter — together
    they exercise EVERY constructor of the language
    ([ne_let]/[ne_sample]/[ne_lam]/[ne_var] in Examples 1–3, [ne_score]
    in Example 3, [ne_add]/[ne_mul] in Example 2,
    [ne_fix]/[ne_app]/[ne_tt] in the recursive examples,
    [ne_true]/[ne_false]/[ne_bernoulli]/[ne_if] in the boolean checks,
    [ne_bernoulli_f] in the rejection-sampling example,
    [ne_fix_mr]/[ne_pair]/[ne_fst]/[ne_snd] in the even/odd
    mutual-recursion example).

    Each denotation is a norm-[≤1] linear morphism
    [linhom_car Ar (coalg_obj (ctxD_cbv nil)) (coalg_obj (tyD_cbv t))]
    — the context cone is [EM_term]'s carrier, so evaluating at [one1]
    yields the program's denotation as a single element of [⟦t⟧]. *)

Section CBVDenotations.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Local Notation eDv M :=
  (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _ M).

Definition ex_random_constant_cbv
    (mu : fmeas R (ar_carrier Ar R_obj))
    (Hmu : (cone_norm mu <= 1)%R) :=
  eDv (ex_random_constant mu Hmu).

Definition ex_random_linear_cbv
    (mu : fmeas R (ar_carrier Ar R_obj))
    (Hmu : (cone_norm mu <= 1)%R) :=
  eDv (ex_random_linear mu Hmu).

Definition ex_score_posterior_cbv
    (mu : fmeas R (ar_carrier Ar R_obj))
    (Hmu : (cone_norm mu <= 1)%R)
    (f : R -> R)
    (Hf_meas : measurable_fun [set: R] f)
    (Hf_ge0 : forall r : R, (0 <= f r)%R)
    (Hf_le1 : forall r : R, (f r <= 1)%R) :=
  eDv (ex_score_posterior mu Hmu f Hf_meas Hf_ge0 Hf_le1).

Definition ex_loop_cbv := eDv (ex_loop : @named_expr R Ar R_obj nil tunit).

Definition ex_true_cbv := eDv (ex_true : @named_expr R Ar R_obj nil tbool).

Definition ex_false_cbv :=
  eDv (ex_false : @named_expr R Ar R_obj nil tbool).

Definition ex_fair_coin_cbv :=
  eDv (ex_fair_coin : @named_expr R Ar R_obj nil tbool).

Definition ex_if_demo_cbv :=
  eDv (ex_if_demo : @named_expr R Ar R_obj nil tbool).

Definition ex_geom_cbv :=
  eDv (ex_geom : @named_expr R Ar R_obj nil (tR R_obj)).

Definition ex_almost_loop_cbv (p : R)
    (Hp_ge0 : (0 <= p)%R) (Hp_le1 : (p <= 1)%R) :=
  eDv (ex_almost_loop p Hp_ge0 Hp_le1).

(** The mutual-recursion smoke test: [ne_fix_mr] at a PRODUCT of
    function types elaborates through the genuine Seely-transported
    [fix_mr_comb] path of [fix_mr_clause]. *)
Definition ex_even_odd_pair_cbv :=
  eDv (ex_even_odd_pair
         : @named_expr R Ar R_obj nil
             (tprod (tfun tunit tunit) (tfun tunit tunit))).

Definition ex_even_cbv :=
  eDv (ex_even : @named_expr R Ar R_obj nil (tfun tunit tunit)).

Definition ex_odd_cbv :=
  eDv (ex_odd : @named_expr R Ar R_obj nil (tfun tunit tunit)).

(** The rejection-sampling denotation — also the compile-time smoke
    test for [ne_bernoulli_f]'s elaboration under three binders
    (canonical-structure variable lookup for ["x"], ["accept"],
    ["rs"]). *)
Definition ex_reject_cbv
    (mu : fmeas R (ar_carrier Ar R_obj))
    (Hmu : (cone_norm mu <= 1)%R)
    (f : R -> R)
    (Hf_meas : measurable_fun [set: R] f)
    (Hf_ge0 : forall r : R, (0 <= f r)%R)
    (Hf_le1 : forall r : R, (f r <= 1)%R) :=
  eDv (ex_reject mu Hmu f Hf_meas Hf_ge0 Hf_le1).

End CBVDenotations.
