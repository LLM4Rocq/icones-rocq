(**md**************************************************************************)
(** * Headline PPL examples — surface programs in direct-style named syntax

    Twelve surface programs for the named-variable PPL of
    [theories/programs/ppl.v], each written in the [ppl_named] custom
    entry [[ … ]].  This file is the SURFACE PROGRAM POOL for the CBV
    stack ([theories/programs/ppl_cbv.v]); the denotational machinery and
    structural reduction lemmas previously living here against the
    OLD CBV [eD] have been retired and are being re-grown at the
    linhom level inside the new [ppl_cbv.v].

    All programs are written in the MODERN surface layer: bundled
    sub-probabilities [m : pmeas] consumed by [sample m], the bundled
    [Bernoulli p] / [Bernoulli d e] coins (the probability [p : prob]
    or density [d : udensity] is [[0,1]]-valued BY CONSTRUCTION — no
    clamp, no loose witnesses), and OCaml-style [let rec] for the
    recursive examples.

    ** Basic sampling/scoring examples (1–3)
    - [ex_random_constant]   : [let "c" := sample m in λx. c]
    - [ex_random_linear]     : [let "m" := sample m in
                                let "b" := sample m in
                                λx. m * x + b]
    - [ex_score_posterior]   : [let "m" := sample m in
                                let "_" := score(f) #"m" in
                                #"m"]
      (sample-score-return: the unnormalised one-parameter posterior)

    ** Higher-order Bayesian linear regression — ITERATED CONDITIONING
    - [ex_bayes_linear l]    : sample a FUNCTION [λx. s·x+b]
      (slope [s] and intercept [b] from the prior), then for each
      Gaussian observation [o ∈ l] [observe Gaussian{1/2, obs_y o}]
      the model's prediction [(# "f" @ obs_x o)] in turn
      ([iter_condition]) and return the function — the posterior over
      functions (arXiv 1701.02547 §2.1 shape); 3-observation instance
      [ex_bayes_linear3]; the raw observe-fold shape is the derived
      reading [ex_bayes_linear_obs_fold]

    ** Recursive partial-termination examples (4–6)
    - [ex_loop]              : [let rec l _ := l () in l ()]
    - [ex_geom]              : geometric counter (mass 1)
    - [ex_almost_loop p]     : parameterised partial divergence (mass p)

    ** Boolean / if-then-else sanity checks
    - [ex_true], [ex_false], [ex_fair_coin], [ex_if_demo]

    ** Mutual recursion (product-of-functions fixpoint)
    - [ex_even_odd_pair]     : [fix_mr p : (1→1) × (1→1).
                                 (λn. snd p n, λn. fst p n)]
      with projections [ex_even] / [ex_odd] — the [ne_fix_mr]
      elaboration witness for the Seely-transported value-fixpoint

    ** Runtime-parameter distributions (the kernel surface)
    - [ex_gaussian_walk]     : [let s = Gaussian(0,1) in Gaussian(s,1)]
      — the two-level Gaussian hierarchy: the parameter of the second
      draw is the SAMPLED value of the first ([ne_gaussian]);
      [ex_unit_interval] is the uniform smoke test

    ** Rejection sampling
    - [ex_reject]            : [let rec rs accept :=
                                   let x = sample m in
                                   if Bernoulli (Meas{f} x) then accept x
                                   else rs accept
                                 in rs (λy. y)] *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp Require Import lra.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals constructive_ereal.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import ereal.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import measure dirac_measure.
From mathcomp.analysis Require Import lebesgue_integral_definition numfun.
From mathcomp.analysis Require Import probability.

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

Variable (m : pmeas Ar R_obj).

Local Notation tR' := (tR R_obj).

(** The PPL term: [let "c" := sample m in λ x. c] in surface syntax. *)
Definition ex_random_constant :
    @named_expr R Ar R_obj nil (tfun tR' tR') :=
  [ let "c" := sample m in \ "x" ::: tR' => # "c" ].

(** The lambda body extracted as a named-syntax sub-term, in the
    extended context [("c", tR) :: nil]. *)
Definition ex_rc_lam :
    @named_expr R Ar R_obj (("c"%string, tR') :: nil) (tfun tR' tR') :=
  [ \ "x" ::: tR' => # "c" ].

End RandomConstant.

Arguments ex_rc_lam {R Ar R_obj}.
Arguments ex_random_constant {R Ar R_obj} m.

(** ** Example 2 — [ex_random_linear] *)

Section RandomLinear.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).

Variable (m : pmeas Ar R_obj).

Local Notation tR' := (tR R_obj).

(** The PPL term:
    [let "m" := sample m in let "b" := sample m in λx. m*x + b]. *)
Definition ex_random_linear :
    @named_expr R Ar R_obj nil (tfun tR' tR') :=
  [ let "m" := sample m in
    let "b" := sample m in
    \ "x" ::: tR' => # "m" * # "x" + # "b" ].

(** The inner continuation after the outer [m]-bind. *)
Definition ex_rl_inner :
    @named_expr R Ar R_obj
      (("m"%string, tR') :: nil) (tfun tR' tR') :=
  [ let "b" := sample m in
    \ "x" ::: tR' => # "m" * # "x" + # "b" ].

(** The lambda closure body, in context [("b", tR) :: ("m", tR) :: nil]. *)
Definition ex_rl_lam :
    @named_expr R Ar R_obj
      (("b"%string, tR') :: ("m"%string, tR') :: nil) (tfun tR' tR') :=
  [ \ "x" ::: tR' => # "m" * # "x" + # "b" ].

End RandomLinear.

Arguments ex_rl_inner {R Ar R_obj} m.
Arguments ex_rl_lam {R Ar R_obj}.
Arguments ex_random_linear {R Ar R_obj} m.

(** ** Example 3 — [ex_score_posterior]

    Sample one parameter, score it by a soft observation density [f],
    return it: the unnormalised one-parameter posterior.  (This program
    was historically misnamed "bayes_linear" — it is NOT a linear
    regression; the genuine higher-order Bayesian linear regression is
    [ex_bayes_linear] below.)

    This example scores by an ARBITRARY user density [f], not the
    likelihood of a built-in distribution; it is therefore NOT an
    [observe] (which is specialised to the bundled, envelope-normalised
    density of a named distribution) but the general [Score]/[Meas]
    combination — left as is. *)

Section ScorePosterior.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (P : probObj Ar).

Variable (m : pmeas Ar (po_robj P)).

(** The soft-conditioning density as a BUNDLED [[0,1]] record — no
    loose witnesses. *)
Variable (d : udensity R).

Local Notation tR' := (tR (po_robj P)).

(** The bundle factoring of the soft [[0,1]] density [d] into the
    probability object [po_obj P]. *)
Local Notation sp_phi :=
  (po_into P (ud_f d) (ud_meas d) (ud_ge0 d) (ud_le1 d)).

(** The PPL term:
    [let "m" := sample m in let "_" := Sc (ToProb d #"m") in #"m"].
    The clean [tProb] score [Sc] weighs by [po_density P] of the
    factored value, which [po_into_E] reads back as [ud_f d] of the
    sampled real — the same soft-evidence weight as the legacy
    [Score d #"m"]. *)
Definition ex_score_posterior :
    @named_expr R Ar (po_robj P) nil tR' :=
  [ let "m" := sample m in
    let "_" := Sc (ToProb {sp_phi} # "m") in
    # "m" ].

(** The continuation under the prior bind. *)
Definition ex_sp_cont :
    @named_expr R Ar (po_robj P) (("m"%string, tR') :: nil) tR' :=
  [ let "_" := Sc (ToProb {sp_phi} # "m") in
    # "m" ].

End ScorePosterior.

Arguments ex_sp_cont {R Ar P} d.
Arguments ex_score_posterior {R Ar P} m d.

(** ** Example — [ex_bayes_linear] — higher-order Bayesian linear regression

    The paper-faithful Bayesian linear-regression example (the shape of
    Staton–Yang–Heunen–Kammar–Wood, arXiv 1701.02547 §2.1): the program
    samples a FUNCTION — the random affine map [λx. m*x + b] of
    Example 2 ([ex_random_linear]; slope [m] and intercept [b] both
    drawn from the prior [µ]) — binds it to the name ["f"], then scores
    a SERIES of observations: for each observation [o] in the
    meta-level list [l], the model's value [f(obs_x o)] at the known
    input point [obs_x o] is scored by the observation density
    [obs_d o].  The program RETURNS ["f"]: the denotation is the
    unnormalised posterior over FUNCTIONS.
    [[
       let "f" := (let "m" := Sample µ in
                   let "b" := Sample µ in
                   \ "x" ::: tR => # "m" * # "x" + # "b") in
       let "_" := Score (Meas { d₁ } (# "f" @ [| x₁ |])) in
       …
       let "_" := Score (Meas { dₙ } (# "f" @ [| xₙ |])) in
       # "f"
    ]]
    The observation fold [obs_fold] is a Rocq [Fixpoint] producing raw
    constructors (the [ppl_named] custom entry cannot recurse over a
    meta-level [seq]); the context grows by one [("_", tunit)] slot per
    observation and the [named_var] witness [v] locating ["f"] is
    extended by [nv_tail] in lock-step.  The 2-observation sanity
    [Check] below confirms the fold agrees definitionally with the
    surface-syntax sugar. *)

Section Obs.
Variable (R : realType).

(** One Gaussian observation = a known input point [obs_x] and an
    observed datum [obs_y].  Following the paper (arXiv:1701.02547) every
    observation shares the SAME fixed likelihood deviation [σ = 1/2]; the
    observation scores the model's value [r] at the input by the
    ENVELOPE-NORMALISED Gaussian likelihood of the datum, [obs_d o r =
    gauss_obs_density (1/2) obs_y r = normal_pdf r (1/2) obs_y /
    normal_peak (1/2) ∈ [0,1]] ([ppl.v]) — the [observe Gaussian{1/2,
    obs_y}] surface form.  The [[0,1]] bound is intrinsic to the
    distribution (the peak is bundled in [gauss_obs_density]); no clamp
    and no user-supplied envelope are needed.  The derived projections
    [obs_d]/[obs_meas]/[obs_ge0]/[obs_le1] expose the score-density
    interface ([ne_score]'s witness layout). *)
Record obs := MkObs {
  obs_x : R;                       (* the input point *)
  obs_y : R }.                     (* the observed datum *)

Definition obs_d (o : obs) : R -> R := gauss_obs_density (1 / 2) (obs_y o).

(** The score-density witnesses, TRANSPARENT (definitionally the bundled
    Gaussian witnesses) so the [observe Gaussian{·} ·] surface form and the
    [condition_at]/[obs_fold] folds elaborate to the SAME [ne_score]. *)
Definition obs_meas (o : obs) : measurable_fun [set: R] (obs_d o) :=
  gauss_obs_density_meas (1 / 2) (obs_y o).

Definition obs_ge0 (o : obs) (r : R) : (0 <= obs_d o r)%R :=
  gauss_obs_density_ge0 (1 / 2) (obs_y o) r.

Definition obs_le1 (o : obs) (r : R) : (obs_d o r <= 1)%R :=
  gauss_obs_density_le1 (1 / 2) (obs_y o) r.

End Obs.

Arguments obs_d {R} o.
Arguments obs_meas {R} o.
Arguments obs_ge0 {R} o r.
Arguments obs_le1 {R} o r.

(** ** Soft conditioning, one observation at a time

    One observation step IS a soft conditioning of the model's value
    at the observation point: scoring [f(obs_x o)] by the observation
    density [obs_d o] is exactly the score clause of [condition]
    ([ex_condition_comb] below) at the model [#"f"] and the input
    [obs_x o] — the only difference is A-normal form: [condition]
    first binds the model's value ([let x = m a in
    let _ = Score{f} x in x], returning the value), while the
    regression scores the application directly and continues with the
    rest of the observations, returning the FUNCTION at the end (the
    two shapes agree semantically by the general let-law
    [let_sample_law.v::eD_let_int]).

    [condition_at o] packages one such observation-conditioning step;
    [iter_condition] is its fold, and the Bayesian linear regression
    [ex_bayes_linear] below is DEFINED as the model bound once, then
    [iter_condition] over the observation list. *)

Section IteratedConditioning.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (P : probObj Ar).

Local Notation tR' := (tR (po_robj P)).

(** The bundle factoring of one observation's Gaussian likelihood
    [obs_d o] into the probability object, the clean [tProb]-score map
    behind [Sc (Gausslik{1/2, obs_y o} (#"f" @ [|obs_x o|]))]. *)
Local Notation obs_phi o :=
  (po_into P (obs_d o) (obs_meas o) (obs_ge0 o) (obs_le1 o)).

(** One observation-conditioning step: [observe Gaussian{1/2, obs_y o}]
    the model's prediction at the input point [obs_x o], then continue
    with [K].  [v] locates the model in the context.  The step scores
    the model's value through the clean [tProb] score [Sc]: push the
    model's prediction through the bundle factoring [po_into (obs_d o)]
    of the envelope-normalised Gaussian likelihood, which [po_into_E]
    reads back as [obs_d o] of the prediction. *)
Definition condition_at (G : named_ctx Ar)
    (v : named_var G (tfun tR' tR')) (o : obs R) (t : ppl_type Ar)
    (K : @named_expr R Ar (po_robj P) (("_"%string, tunit) :: G) t) :
    @named_expr R Ar (po_robj P) G t :=
  ne_let "_"%string
    (ne_score_p (po_density P) (po_density_meas P) (po_ge0 P) (po_le1 P)
       (ne_to_prob (obs_phi o)
          (ne_app (ne_var v) (ne_real (obs_x o)))))
    K.

(** The iterated-conditioning fold: condition the model on each
    observation in turn, then return the model.  Parameterised by the
    [named_var] witness [v] locating the model in the current context
    [G]; each conditioning step extends [G] by a [("_", tunit)] slot
    and [v] by [nv_tail]. *)
Fixpoint iter_condition (G : named_ctx Ar)
    (v : named_var G (tfun tR' tR')) (l : seq (obs R)) :
    @named_expr R Ar (po_robj P) G (tfun tR' tR') :=
  match l with
  | nil => ne_var v
  | o :: l' =>
      condition_at v o (iter_condition (nv_tail "_"%string tunit _ v) l')
  end.

End IteratedConditioning.

Arguments condition_at {R Ar P G} v o {t} K.
Arguments iter_condition {R Ar P G} v l.

Section BayesLinear.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (P : probObj Ar).

Variable (m : pmeas Ar (po_robj P)).

Local Notation tR' := (tR (po_robj P)).

(** The program: the model is exactly Example 2's [ex_random_linear]
    (the sampled affine function), bound at the head of the context
    (witness [nv_head]), then CONDITIONED on each observation in
    turn. *)
Definition ex_bayes_linear (l : seq (obs R)) :
    @named_expr R Ar (po_robj P) nil (tfun tR' tR') :=
  ne_let "f"%string (ex_random_linear m)
    (iter_condition (nv_head "f"%string (tfun tR' tR') nil) l).

(** The raw observation fold — the historical shape of the program:
    for each [o] in [l], score the model's value at [obs_x o] through
    the clean [tProb] score [Sc (Gausslik{·} ·)]; when the list is
    exhausted, return the model. *)
Fixpoint obs_fold (G : named_ctx Ar) (v : named_var G (tfun tR' tR'))
    (l : seq (obs R)) : @named_expr R Ar (po_robj P) G (tfun tR' tR') :=
  match l with
  | nil => ne_var v
  | o :: l' =>
      ne_let "_"%string
        (ne_score_p (po_density P) (po_density_meas P) (po_ge0 P) (po_le1 P)
           (ne_to_prob
              (po_into P (obs_d o) (obs_meas o) (obs_ge0 o) (obs_le1 o))
              (ne_app (ne_var v) (ne_real (obs_x o)))))
        (obs_fold (nv_tail "_"%string tunit _ v) l')
  end.

(** The observation fold IS the iterated conditioning. *)
Lemma obs_fold_is_iter_condition (G : named_ctx Ar)
    (v : named_var G (tfun tR' tR')) (l : seq (obs R)) :
  obs_fold v l = iter_condition v l.
Proof. by elim: l G v => [ | o l IH] G v //=; rewrite IH. Qed.

(** The agreement, now definitional — the named anchor of the
    iterated-conditioning reading: Bayesian linear regression = the
    random affine model, conditioned on each observation in turn. *)
Theorem ex_bayes_linear_is_iter_condition (l : seq (obs R)) :
  ex_bayes_linear l =
  ne_let "f"%string (ex_random_linear m)
    (iter_condition (nv_head "f"%string (tfun tR' tR') nil) l).
Proof. by []. Qed.

(** The derived raw-fold reading: the regression unfolds to the
    score-per-observation fold. *)
Lemma ex_bayes_linear_obs_fold (l : seq (obs R)) :
  ex_bayes_linear l =
  ne_let "f"%string (ex_random_linear m)
    (obs_fold (nv_head "f"%string (tfun tR' tR') nil) l).
Proof. by rewrite obs_fold_is_iter_condition. Qed.

Variables (o1 o2 o3 : obs R).

(** Surface-syntax sanity: on a concrete 2-observation list the
    iterated conditioning agrees DEFINITIONALLY with the [ppl_named]
    sugar — the [#"f"] lookups resolve through the [("_", tunit)]
    slots by canonical-structure search, building exactly the
    [nv_tail] chain that [iter_condition] constructs. *)
Check (erefl : ex_bayes_linear [:: o1; o2] =
  [ let "f" := (let "m" := sample m in
                let "b" := sample m in
                \ "x" ::: tR' => # "m" * # "x" + # "b") in
    let "_" := Sc (Gausslik { 1 / 2 , obs_y o1 }
                        (# "f" @ [| obs_x o1 |])) in
    let "_" := Sc (Gausslik { 1 / 2 , obs_y o2 }
                        (# "f" @ [| obs_x o2 |])) in
    # "f" ]).

(** The 1-observation case: one observation = one conditioning step
    (definitional). *)
Check (erefl : ex_bayes_linear [:: o1] =
  ne_let "f"%string (ex_random_linear m)
    (condition_at (nv_head "f"%string (tfun tR' tR') nil) o1
       (ne_var (nv_tail "_"%string tunit _
                  (nv_head "f"%string (tfun tR' tR') nil))))).

(** The concrete 3-observation instance (for the docs to quote). *)
Definition ex_bayes_linear3 :
    @named_expr R Ar (po_robj P) nil (tfun tR' tR') :=
  ex_bayes_linear [:: o1; o2; o3].

End BayesLinear.

Arguments obs_fold {R Ar P G} v l.
Arguments ex_bayes_linear {R Ar P} m l.
Arguments ex_bayes_linear3 {R Ar P} m o1 o2 o3.

(** ** Example 4 — [ex_loop] — bare divergence *)

Section ExLoopDemo.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).

(** The divergence example.  Source: [let rec l _ = l () in l ()]
    (annotated [let rec]: the binder ["_"] is unused, so its type
    cannot be inferred from the body). *)
Definition ex_loop :
    @named_expr R Ar R_obj nil tunit :=
  [ let rec "l" "_" ::: tunit ==> tunit := # "l" @ ()
    in # "l" @ () ].

End ExLoopDemo.

Arguments ex_loop {R Ar R_obj}.

(** Witnesses [0 ≤ 1/2 ≤ 1] for the fair coin, and the bundled
    probability [prob_half : prob] built from them — the constant
    Bernoulli surface form [Bernoulli prob_half] carries its [[0,1]]
    bounds through the bundle (no clamp). *)
Lemma bernoulli_half_ge0 (R : realType) : (0 <= 1 / 2 :> R)%R.
Proof. by rewrite divr_ge0// ler01. Qed.

Lemma bernoulli_half_le1 (R : realType) : (1 / 2 <= 1 :> R)%R.
Proof. by rewrite ler_pdivrMr ?mul1r ?ler1n. Qed.

Definition prob_half (R : realType) : prob R :=
  mk_prob (1 / 2 : R) (bernoulli_half_ge0 R) (bernoulli_half_le1 R).

Arguments prob_half {R}.

(** ** Boolean primitives sanity check — [True], [False], [Bernoulli p] *)

Section ExBoolDemo.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (P : probObj Ar).

Definition ex_true : @named_expr R Ar (po_robj P) nil tbool := [ True ].

Definition ex_false : @named_expr R Ar (po_robj P) nil tbool := [ False ].

(** The fair coin, in the clean constant-literal form
    [Bernoulli [| (1/2 : R) |]]: the success probability [1/2] is a bare
    real literal whose [[0,1]] bounds are discharged on the spot by
    [lra] — no [prob_half] bundle, no [Const], no loose witnesses. *)
Definition ex_fair_coin : @named_expr R Ar (po_robj P) nil tbool :=
  [ Bernoulli [| (1 / 2 : R) |] ].

End ExBoolDemo.

Arguments ex_true {R Ar P}.
Arguments ex_false {R Ar P}.
Arguments ex_fair_coin {R Ar P}.

(** ** Example — [ex_if_demo] — if-then-else sanity check *)

Section ExIfDemo.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (P : probObj Ar).

(** The closed [tbool]-typed [if-then-else] term:
    [if Bernoulli [| (1/2 : R) |] then True else False]. *)
Definition ex_if_demo :
    @named_expr R Ar (po_robj P) nil tbool :=
  [ if Bernoulli [| (1 / 2 : R) |]
    then True else False ].

End ExIfDemo.

Arguments ex_if_demo {R Ar P}.

(** ** Recursive partial-termination examples *)

Section RecExamples.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (P : probObj Ar).

Local Notation tR' := (tR (po_robj P)).

(** *** [ex_geom] — geometric distribution
    Source: [let rec g _ = if Bernoulli(½) then 0
                                           else 1 + g () in g ()].
    The fair coin is the clean constant-literal form
    [Bernoulli [| (1/2 : R) |]] — the success probability [1/2] is a
    bare real literal, its [[0,1]] bounds discharged by [lra]; no
    [prob_half] bundle, no [Const], no loose witnesses. *)

Definition ex_geom : @named_expr R Ar (po_robj P) nil tR' :=
  [ let rec "g" "_" ::: tunit ==> tR' :=
      (if Bernoulli [| (1 / 2 : R) |]
       then [| 0%R |]
       else [| 1%R |] + # "g" @ ())
    in # "g" @ () ].

(** The body of the fixed-point lambda. *)
Definition ex_geom_body :
    @named_expr R Ar (po_robj P)
      (("g"%string, tfun tunit tR') :: nil)
      (tfun tunit tR') :=
  [ \ "_" ::: tunit =>
      (if Bernoulli [| (1 / 2 : R) |]
       then [| 0%R |]
       else [| 1%R |] + # "g" @ ()) ].

(** *** [ex_almost_loop pr] — parameterised divergence
    Source: [let rec l _ = if Bernoulli(p) then ()
                                           else l () in l ()].
    The parameter is a BUNDLED probability [pr : prob]; the clean coin
    is [Bern (Const pr [|0|])] — the constant value-coin over [P]. *)
Definition ex_almost_loop (pr : prob R) :
    @named_expr R Ar (po_robj P) nil tunit :=
  [ let rec "l" "_" ::: tunit ==> tunit :=
      (if Bern (Const pr [| 0%R |])
       then ()
       else # "l" @ ())
    in # "l" @ () ].

(** Its lambda body, in the extended context
    [("l", tfun tunit tunit) :: nil]. *)
Definition ex_almost_loop_body (pr : prob R) :
    @named_expr R Ar (po_robj P)
      (("l"%string, tfun tunit tunit) :: nil)
      (tfun tunit tunit) :=
  [ \ "_" ::: tunit =>
      (if Bern (Const pr [| 0%R |])
       then ()
       else # "l" @ ()) ].

End RecExamples.

Arguments ex_geom {R Ar P}.
Arguments ex_geom_body {R Ar P}.
Arguments ex_almost_loop {R Ar P} pr.
Arguments ex_almost_loop_body {R Ar P} pr.

(** ** Example — [ex_even_odd] — mutual recursion at a product of functions

    The [ne_fix_mr] constructor binds ONE recursive name [p] at the
    free-coalgebra type [tprod (tfun tunit tunit) (tfun tunit tunit)] —
    a PAIR of functions; each component calls the other via the
    [fst]/[snd] projections of the rec-bound product.  This is the
    classic even/odd mutual-recursion SHAPE (each component immediately
    delegates to the other with no base case, so operationally it
    diverges).  The denotation elaborates through the genuine
    Seely-transported [fix_mr_comb] path of [ppl_cbv.v::fix_mr_clause],
    and the operational identity is discharged in
    [ex_reject_headline.v], Section [ExEvenOddRider]:
    [ex_even_cbv_diverges] / [ex_odd_cbv_diverges] pin the projection
    runs [ex_even @ ()] / [ex_odd @ ()] to the unit-cone zero (mass
    [0]), while the pair value itself is [0! ⊗p 0!]
    ([ex_even_odd_pair_cbv_value]), never the cone-zero. *)

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

(** ** Example — [ex_reject] — rejection sampling

    Normalised-posterior rejection sampling: sample [x ~ µ], accept
    with probability [f x] (the value-dependent Bernoulli
    [ne_bernoulli_f]), and on rejection RECURSE.  The recursive
    function abstracts over the acceptance continuation [accept], and
    the headline instantiates it at the identity [λy. y] (so the
    program returns the accepted sample itself):
    [[
       let rec rs accept :=
         let x = sample m in
         if Bernoulli (Meas{f} x) then accept x else rs accept
       in rs (λ y. y)
    ]]
    Expected denotation (the M4 headline): the sub-probability
    [ν] with [∫f dµ · ν(U) = ∫_U f dµ] — the normalised posterior,
    graceful at [∫f dµ = 0]. *)

Section RejectSampling.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (P : probObj Ar).

Variable (m : pmeas Ar (po_robj P)).

(** The acceptance density as a BUNDLED [[0,1]] record — its
    measurability and bounds are carried by [d], no loose witnesses,
    no clamp. *)
Variable (d : udensity R).

Local Notation tR' := (tR (po_robj P)).

(** The bundle factoring of the acceptance density [d] into the
    probability object [po_obj P] — the clean [tProb]-coin map behind
    [Bern (ToProb d #"x")]. *)
Local Notation rj_phi :=
  (po_into P (ud_f d) (ud_meas d) (ud_ge0 d) (ud_le1 d)).

(** The full surface program: the recursive sampler, applied to the
    identity acceptance continuation in the [let rec] continuation. *)
Definition ex_reject : @named_expr R Ar (po_robj P) nil tR' :=
  [ let rec "rs" "accept" :=
      (let "x" := sample m in
       if Bern (ToProb {rj_phi} # "x")
       then # "accept" @ # "x"
       else # "rs" @ # "accept")
    in # "rs" @ (\ "y" ::: tR' => # "y") ].

(** The body of the fixed-point lambda, in the extended context
    [("rs", (tR' -> tR') -> tR') :: nil] (the [ex_geom_body]
    pattern). *)
Definition ex_reject_body :
    @named_expr R Ar (po_robj P)
      (("rs"%string, tfun (tfun tR' tR') tR') :: nil)
      (tfun (tfun tR' tR') tR') :=
  [ \ "accept" ::: (tfun tR' tR') =>
      (let "x" := sample m in
       if Bern (ToProb {rj_phi} # "x")
       then # "accept" @ # "x"
       else # "rs" @ # "accept") ].

(** The sample-then-test inner expression under both binders, in
    context [("accept", tR' -> tR') :: ("rs", …) :: nil]. *)
Definition ex_reject_inner :
    @named_expr R Ar (po_robj P)
      (("accept"%string, tfun tR' tR') ::
       ("rs"%string, tfun (tfun tR' tR') tR') :: nil)
      tR' :=
  [ let "x" := sample m in
    if Bern (ToProb {rj_phi} # "x")
    then # "accept" @ # "x"
    else # "rs" @ # "accept" ].

End RejectSampling.

Arguments ex_reject {R Ar P} m d.
Arguments ex_reject_body {R Ar P} m d.
Arguments ex_reject_inner {R Ar P} m d.

(** ** Example — [ex_reject_comb] — rejection sampling as a COMBINATOR

    The higher-order generalisation of [ex_reject]: rejection sampling
    as a function of the MODEL.  A model is any function value
    [m : ta → tR] (a lambda-written probabilistic program — itself free
    to contain samples, scores, recursion, …); [ex_reject_comb] takes
    the model and an input [a : ta], runs the model at the input, and
    accepts the produced value [x] with probability [f x], recursing
    (at the SAME model and input) on rejection:
    [[
       fix rs = λ m. λ a.
         let x = m a in
         if Bernoulli (Meas{f} x) then x else rs m a
    ]]
    The recursion is at the function type
    [(ta → tR) → (ta → tR)] — the fixpoint VALUE is itself the
    combinator, and the model/input are carried through the recursion
    as ordinary lambda parameters.

    Expected denotation (proved in
    [theories/programs/ex_reject_model.v]): writing
    [ν_M := ⟦m⟧(a)] for the model's output distribution at the input
    (a SUB-probability: the model may itself diverge),
    [m₀ := ν_M(setT)] its total mass and [If := ∫ f dν_M], the
    combinator's output [ν] satisfies the sub-probability-honest
    master identity [(1 - m₀ + If) · ν(U) = ∫_U f dν_M]. *)

Section RejectCombinator.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (P : probObj Ar).

(** The model's INPUT type is an arbitrary PPL type. *)
Variable (ta : ppl_type Ar).

(** The acceptance density as a BUNDLED [[0,1]] record — no clamp, no
    loose witnesses. *)
Variable (d : udensity R).

Local Notation tR' := (tR (po_robj P)).

(** The bundle factoring of the acceptance density [d] into the
    probability object [po_obj P] — the clean [tProb]-coin map behind
    [Bern (ToProb d #"x")]. *)
Local Notation rc_phi :=
  (po_into P (ud_f d) (ud_meas d) (ud_ge0 d) (ud_le1 d)).

(** The combinator itself: a closed program of type
    [(ta → tR) → (ta → tR)]. *)
Definition ex_reject_comb :
    @named_expr R Ar (po_robj P) nil (tfun (tfun ta tR') (tfun ta tR')) :=
  [ fix "rs" ::: tfun (tfun ta tR') (tfun ta tR') in
      \ "m" ::: (tfun ta tR') =>
        \ "a" ::: ta =>
          (let "x" := # "m" @ # "a" in
           if Bern (ToProb {rc_phi} # "x")
           then # "x"
           else # "rs" @ # "m" @ # "a") ].

(** The body of the fixpoint lambda (the [λm.λa.…] under the rec
    binder), in the extended context [("rs", (ta→tR)→(ta→tR)) :: nil]. *)
Definition ex_reject_comb_body :
    @named_expr R Ar (po_robj P)
      (("rs"%string, tfun (tfun ta tR') (tfun ta tR')) :: nil)
      (tfun (tfun ta tR') (tfun ta tR')) :=
  [ \ "m" ::: (tfun ta tR') =>
      \ "a" ::: ta =>
        (let "x" := # "m" @ # "a" in
         if Bern (ToProb {rc_phi} # "x")
         then # "x"
         else # "rs" @ # "m" @ # "a") ].

(** The partially-applied stage [λa.…], in context
    [("m", ta→tR) :: ("rs", …) :: nil]. *)
Definition ex_reject_comb_fun :
    @named_expr R Ar (po_robj P)
      (("m"%string, tfun ta tR') ::
       ("rs"%string, tfun (tfun ta tR') (tfun ta tR')) :: nil)
      (tfun ta tR') :=
  [ \ "a" ::: ta =>
      (let "x" := # "m" @ # "a" in
       if Bern (ToProb {rc_phi} # "x")
       then # "x"
       else # "rs" @ # "m" @ # "a") ].

(** The run-test-recurse inner expression under all three binders. *)
Definition ex_reject_comb_inner :
    @named_expr R Ar (po_robj P)
      (("a"%string, ta) :: ("m"%string, tfun ta tR') ::
       ("rs"%string, tfun (tfun ta tR') (tfun ta tR')) :: nil)
      tR' :=
  [ let "x" := # "m" @ # "a" in
    if Bern (ToProb {rc_phi} # "x")
    then # "x"
    else # "rs" @ # "m" @ # "a" ].

End RejectCombinator.

Arguments ex_reject_comb {R Ar P} ta d.
Arguments ex_reject_comb_body {R Ar P} ta d.
Arguments ex_reject_comb_fun {R Ar P} ta d.
Arguments ex_reject_comb_inner {R Ar P} ta d.

(** ** Example — [ex_condition_comb] — Pyro-style soft conditioning

    The [condition] operator of Pyro-style probabilistic programming:
    take a MODEL [m : ta → tR] and return the CONDITIONED MODEL — the
    function that runs the model at the input, SCORES the produced
    value [x] by the soft observation density [f] (the likelihood of
    the observation given [x]), and returns [x]:
    [[
       condition = λ m. λ a.
         let x = m a in
         let _ = Score (Meas{f} x) in
         x
    ]]
    [ex_condition_comb] is the combinator (a closed program of type
    [(ta → tR) → (ta → tR)], the same type as [ex_reject_comb]);
    [ex_condition M] is the conditioned model [condition M f].

    Expected denotation (proved in
    [theories/programs/ex_reject_model.v::condition_model_E]): writing
    [ν_M := ⟦m⟧(a)] for the model's output distribution at the input,
    the conditioned model's output at [a] is the REWEIGHTED measure
    [U ↦ ∫_U f dν_M] — unnormalised soft conditioning.  THE
    EQUIVALENCE ([ex_reject_model.v::reject_normalises_condition]):
    rejection sampling over the same model and density computes
    exactly this measure, normalised —
    [Z · ⟦reject_comb m a⟧ = ⟦condition_comb m a⟧] with
    [Z := 1 - ν_M(setT) + ∫ f dν_M]. *)

Section ConditionCombinator.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (P : probObj Ar).

(** The model's INPUT type is an arbitrary PPL type. *)
Variable (ta : ppl_type Ar).

(** The soft observation density (the likelihood) as a BUNDLED [[0,1]]
    record — no clamp, no loose witnesses. *)
Variable (d : udensity R).

Local Notation tR' := (tR (po_robj P)).

(** The bundle factoring of the likelihood [d] into the probability
    object [po_obj P] — the clean [tProb]-score map behind
    [Sc (ToProb d #"x")]. *)
Local Notation cc_phi :=
  (po_into P (ud_f d) (ud_meas d) (ud_ge0 d) (ud_le1 d)).

(** The combinator itself: a closed program of type
    [(ta → tR) → (ta → tR)]. *)
Definition ex_condition_comb :
    @named_expr R Ar (po_robj P) nil (tfun (tfun ta tR') (tfun ta tR')) :=
  [ \ "m" ::: (tfun ta tR') =>
      \ "a" ::: ta =>
        (let "x" := # "m" @ # "a" in
         let "_" := Sc (ToProb {cc_phi} # "x") in
         # "x") ].

(** The partially-applied stage [λa.…], in context
    [("m", ta→tR) :: nil]. *)
Definition ex_condition_fun :
    @named_expr R Ar (po_robj P)
      (("m"%string, tfun ta tR') :: nil) (tfun ta tR') :=
  [ \ "a" ::: ta =>
      (let "x" := # "m" @ # "a" in
       let "_" := Sc (ToProb {cc_phi} # "x") in
       # "x") ].

(** The run-score-return inner expression under both binders. *)
Definition ex_condition_inner :
    @named_expr R Ar (po_robj P)
      (("a"%string, ta) :: ("m"%string, tfun ta tR') :: nil) tR' :=
  [ let "x" := # "m" @ # "a" in
    let "_" := Sc (ToProb {cc_phi} # "x") in
    # "x" ].

(** The applied form — [condition M f]: the combinator at a closed
    model program [M] is the conditioned MODEL, again a closed program
    of type [ta → tR]. *)
Definition ex_condition (M : @named_expr R Ar (po_robj P) nil (tfun ta tR')) :
    @named_expr R Ar (po_robj P) nil (tfun ta tR') :=
  [ {ex_condition_comb} @ {M} ].

End ConditionCombinator.

Arguments ex_condition_comb {R Ar P} ta d.
Arguments ex_condition_fun {R Ar P} ta d.
Arguments ex_condition_inner {R Ar P} ta d.
Arguments ex_condition {R Ar P ta} d M.

(** Surface form — [Condition { d } M]: the conditioned model, written
    directly in the [ppl_named] custom entry from a BUNDLED density
    [d : udensity] (no loose witnesses, no clamp).  Elaborates to
    [ne_app (ex_condition_comb _ d) M]; the ambient context must be
    CLOSED ([nil]) since the combinator is a closed program. *)
Notation "'Condition' '{' d '}' M" :=
  (ne_app (ex_condition_comb _ d) M)
  (in custom ppl_named at level 20,
   M custom ppl_named at level 19,
   d constr).

(** ** Example — [ex_sampler] — the simplest model for the combinator

    The lambda-written model [λ_. sample µ] of type [tunit → tR]: ignore
    the input, draw from the prior.  Feeding it to [ex_reject_comb]
    recovers exactly the [ex_reject] headline semantics
    ([theories/programs/ex_reject_model.v], instance section). *)

Section SamplerModel.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).

Variable (m : pmeas Ar R_obj).

Local Notation tR' := (tR R_obj).

Definition ex_sampler : @named_expr R Ar R_obj nil (tfun tunit tR') :=
  [ \ "_" ::: tunit => sample m ].

(** The sample expression under the (discarded) binder. *)
Definition ex_sampler_body :
    @named_expr R Ar R_obj (("_"%string, tunit) :: nil) tR' :=
  [ sample m ].

End SamplerModel.

Arguments ex_sampler {R Ar R_obj} m.
Arguments ex_sampler_body {R Ar R_obj} m.

(** Smoke test for the [Condition] surface form: conditioning the
    sampler model and running the result parses, types, and pins to
    the [ex_condition] combinator application. *)

Section ConditionSmoke.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (P : probObj Ar).

Variable (m : pmeas Ar (po_robj P)).

Variable (d : udensity R).

Check [ Condition { d } { ex_sampler m } @ () ].

Check (erefl :
  [ Condition { d } { ex_sampler m } ] =
  ex_condition d (ex_sampler m)).

End ConditionSmoke.

(** ** Named distributions — [gaussian] / [uniform] as [pmeas] values

    mathcomp-analysis ships the normal distribution [normal_prob m s]
    and the uniform distribution [uniform_prob ab] as probability
    measures on [R] (module [probability]).  The generic transport
    [ppl.v::prob_pmeas] (pushforward along the measurable carrier cast
    [R_to_carrier], canonically extended by [0] off the σ-algebra)
    turns ANY such probability into a bundled sub-probability
    [pmeas Ar R_obj], ready for the [sample] surface form:
    [[
        let "m" := sample (gaussian 0 1) in …
    ]] *)

Section NamedDistributions.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Local Notation toC := (R_to_carrier R_carrier_eq).

(** *** Generic glue: a mathcomp-analysis probability on [R] is a
    [pmeas].  The probability measures of [probability.v] are typed at
    the [g_sigma_algebraType] structure on [R] generated by the
    half-open intervals; the four measure facts transfer to the
    transport's hypotheses by unification (the canonical measurable
    structure on [Real.sort R] is generated the same way). *)

Section ProbToPmeas.
Variable P : probability
  (g_sigma_algebraType ((R.-ocitv).-measurable : set (set (ocitv_type R))))
  R.

Let nuP : set R -> \bar R := fun U => P U.

Local Lemma nuP0 : nuP set0 = 0%E.
Proof. exact: measure0. Qed.

Local Lemma nuP_ge0 (U : set R) : (0 <= nuP U)%E.
Proof. exact: measure_ge0. Qed.

Local Lemma nuP_sigma : semi_sigma_additive nuP.
Proof.
move=> F mF tF mUF.
have H := @measure_semi_sigma_additive _ _ R P F.
apply: H => //.
Qed.

Local Lemma nuP_le1 (U : set (ar_carrier Ar R_obj)) :
  measurable U -> (nuP (toC @^-1` U) <= 1)%E.
Proof.
move=> mU.
have Hpre := prob_push_pre_meas R_to_carrier_meas mU.
apply: probability_le1.
exact: Hpre.
Qed.

Definition pmeas_of_prob : pmeas Ar R_obj :=
  prob_pmeas R_carrier_eq R_to_carrier_meas nuP nuP0 nuP_ge0 nuP_sigma nuP_le1.

End ProbToPmeas.

(** The normal distribution with mean [m] and deviation [s], as a
    bundled sub-probability ready for [sample]. *)
Definition gaussian (m s : R) : pmeas Ar R_obj :=
  pmeas_of_prob [the probability _ _ of normal_prob m s].

(** The uniform distribution on [[a, b]] ([ab : a < b]). *)
Definition uniform (a b : R) (ab : (a < b)%R) : pmeas Ar R_obj :=
  pmeas_of_prob [the probability _ _ of uniform_prob ab].

End NamedDistributions.

Arguments pmeas_of_prob {R Ar R_obj} R_carrier_eq R_to_carrier_meas P.
Arguments gaussian {R Ar R_obj} R_carrier_eq R_to_carrier_meas m s.
Arguments uniform {R Ar R_obj} R_carrier_eq R_to_carrier_meas {a b} ab.

(** ** Example — [ex_gaussian_walk] — a two-level Gaussian hierarchy

    The previously-inexpressible hierarchical model: the runtime
    parameter of the second draw is the SAMPLED VALUE of the first.
    [[
        let s = Gaussian(0, 1) in Gaussian(s, 1)
    ]]
    Both [Gaussian(e1,e2)] sites are the runtime-parameter constructor
    [ne_gaussian] (no witnesses; the kernel family is total) — the
    constant-parameter first draw is just the kernel surface at real
    literals ([eD_gaussian_sample_agree] in
    [theories/programs/infra/kernel_anchors.v] pins it to the old
    [sample (gaussian 0 1)] form).  The denotation reduction
    [ex_gaussian_walk_E] and the mass-1 corollary
    [ex_gaussian_walk_mass] live in the same anchors file (they consume
    the general let-law of [infra/let_sample_law.v], which sits after
    this file). *)

Section GaussianWalk.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).

Local Notation tR' := (tR R_obj).

Definition ex_gaussian_walk : @named_expr R Ar R_obj nil tR' :=
  [ let "s" := Gaussian( [| 0%R |] , [| 1%R |] ) in
    Gaussian( # "s" , [| 1%R |] ) ].

(** The second-stage draw under the binder (for stating reduction
    lemmas), in context [("s", tR') :: nil]. *)
Definition ex_gaussian_walk_body :
    @named_expr R Ar R_obj (("s"%string, tR') :: nil) tR' :=
  [ Gaussian( # "s" , [| 1%R |] ) ].

(** Elaboration pin: the surface program is the let of two
    [ne_gaussian] nodes. *)
Lemma ex_gaussian_walk_decomp :
  ex_gaussian_walk =
  ne_let "s" (ne_gaussian (ne_real 0) (ne_real 1)) ex_gaussian_walk_body.
Proof. by []. Qed.

(** Uniform smoke test: the runtime-parameter uniform draw on
    [[0, 1]]. *)
Definition ex_unit_interval : @named_expr R Ar R_obj nil tR' :=
  [ Uniform( [| 0%R |] , [| 1%R |] ) ].

End GaussianWalk.

Arguments ex_gaussian_walk {R Ar R_obj}.
Arguments ex_gaussian_walk_body {R Ar R_obj}.
Arguments ex_unit_interval {R Ar R_obj}.

(** ** [ex_surface_demo] — the new surface forms, end to end

    The user-level program
    [[
        let rec model x =
          let m = gaussian 0 1 in
          if m > 0 then true else false
        in model ()
    ]]
    written verbatim in the [ppl_named] surface: [let rec] sugar
    (annotated form — the binder [x] is unused, so its type cannot be
    inferred from the body), [sample] of the bundled [gaussian 0 1],
    and the comparison coin [>].  A second program exercises the
    annotation-free [let rec] (the binder appears in the body) and the
    unified [Bernoulli e] / [Score e] forms.

    What the sugar elaborates to (checked by the [_decomp] lemmas):
    [let rec f x := M in K] is [ne_let f (ne_fix f (ne_lam x M)) K];
    [e1 > e2] is [ne_bernoulli_f] at [gt0_ind] on [e1 + Meas { negr } e2];
    [sample m] is [ne_sample (pm_meas m) (pm_ball m)]. *)

Section SurfaceDemo.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (P : probObj Ar).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier (po_robj_eq P)).

Local Notation tR' := (tR (po_robj P)).
Local Notation gaussian01 :=
  (gaussian (po_robj_eq P) R_to_carrier_meas 0 1).

(** The user's program, verbatim.  The comparison coin [m > 0] is the
    clean [tProb] coin [Bern (Gt0 (m - 0))]: the strict-positivity
    indicator [gt0_ind] pushed through the bundle factoring [po_into]
    of the difference [m + (-0)]. *)
Definition ex_surface_demo : @named_expr R Ar (po_robj P) nil tbool :=
  [ let rec "model" "x" ::: tunit ==> tbool :=
      (let "m" := sample gaussian01 in
       if Bern (Gt0 (# "m" + Meas {negr, negr_meas} [| 0%R |]))
       then True else False)
    in # "model" @ () ].

(** Annotation-free [let rec] + the clean value-dependent [tProb]
    [Bern]/[Sc] forms: the binder ["x"] occurs in the body, so its type
    is inferred.  [Gt0] is the strict-positivity indicator pushed
    through the bundle factoring [po_into gt0_ind]. *)
Definition ex_surface_walk : @named_expr R Ar (po_robj P) nil tR' :=
  [ let rec "walk" "x" :=
      (let "b" := Bern (Gt0 # "x") in
       let "_" := Sc (Gt0 # "x") in
       if # "b" then # "x" else # "walk" @ # "x" * [| 1 / 2 |])
    in # "walk" @ [| 1 |] ].

(** Elaboration pins. *)
Lemma ex_surface_demo_decomp :
  ex_surface_demo =
  ne_let "model"
    (ne_fix "model"
       (ne_lam "x"
          (ne_let "m"
             (ne_sample (pm_meas gaussian01) (pm_ball gaussian01))
             (ne_if tbool
                (ne_bernoulli_p (po_density P) (po_density_meas P)
                   (po_ge0 P) (po_le1 P)
                   (ne_to_prob
                      (po_into P gt0_ind gt0_ind_meas gt0_ind_ge0 gt0_ind_le1)
                      (ne_add (ne_var' "m" _)
                         (ne_meas negr negr_meas (ne_real 0)))))
                ne_true ne_false))))
    (ne_app (ne_var' "model" _) ne_tt).
Proof. by []. Qed.

End SurfaceDemo.

Arguments ex_surface_demo {R Ar P} R_to_carrier_meas.
Arguments ex_surface_walk {R Ar P}.

(** ** CBV denotations — [ppl_cbv.v]'s [eD] applied to every closed example

    One definition per closed surface program above: these are the
    CBV-side entry points for the headline lemmas to come, and they
    double as a compile-time smoke test of the interpreter — together
    they exercise EVERY constructor of the language
    ([ne_let]/[ne_sample]/[ne_lam]/[ne_var] in Examples 1–3, [ne_score]
    in Example 3, [ne_add]/[ne_mul] in Example 2,
    [ne_fix]/[ne_app]/[ne_tt] in the recursive examples,
    [ne_true]/[ne_false]/[ne_if] and the bundled constant coin
    ([ne_bernoulli] via [prob]) in the boolean checks,
    [ne_bernoulli_f] in the rejection-sampling example, [ne_meas] in
    the surface demos, [ne_fix_mr]/[ne_pair]/[ne_fst]/[ne_snd] in the
    even/odd mutual-recursion example).

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

Definition ex_random_constant_cbv (m : pmeas Ar R_obj) :=
  eDv (ex_random_constant m).

Definition ex_random_linear_cbv (m : pmeas Ar R_obj) :=
  eDv (ex_random_linear m).

Definition ex_loop_cbv := eDv (ex_loop : @named_expr R Ar R_obj nil tunit).

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

(** The sampler-model denotation (the combinator's simplest input). *)
Definition ex_sampler_cbv (m : pmeas Ar R_obj) :=
  eDv (ex_sampler m).

(** The Gaussian-hierarchy denotation — the runtime-parameter
    [ne_gaussian] smoke test; the denotation reduction
    [ex_gaussian_walk_E] / mass-1 corollary [ex_gaussian_walk_mass]
    live in [theories/programs/infra/kernel_anchors.v]. *)
Definition ex_gaussian_walk_cbv :=
  eDv (ex_gaussian_walk : @named_expr R Ar R_obj nil (tR R_obj)).

(** The runtime-parameter uniform smoke test. *)
Definition ex_unit_interval_cbv :=
  eDv (ex_unit_interval : @named_expr R Ar R_obj nil (tR R_obj)).


End CBVDenotations.

(** ** CBV denotations for the [probObj]-parameterised recursive examples

    [ex_geom] / [ex_almost_loop] are now defined over a bundled
    [P : probObj Ar] (their fair / parameterised coin is the clean
    [tProb] constant value-coin [Bern (Const pr [|0|])]); their CBV
    pins therefore live over [po_robj P], with the carrier casts read
    from the bundle ([po_robj_eq P] / [po_robj_meas P]). *)
Section RecCBVDenotations.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (P : probObj Ar).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier (po_robj_eq P)).

Local Notation eDvP M :=
  (@eD R Ar (po_robj P) (po_robj_eq P) (po_robj_meas P) R_to_carrier_meas _ _ M).

Definition ex_geom_cbv :=
  eDvP (ex_geom : @named_expr R Ar (po_robj P) nil (tR (po_robj P))).

Definition ex_almost_loop_cbv (pr : prob R) :=
  eDvP (ex_almost_loop pr).

Definition ex_score_posterior_cbv
    (m : pmeas Ar (po_robj P))
    (d : udensity R) :=
  eDvP (ex_score_posterior m d).

(** The rejection-sampling denotation — also the compile-time smoke
    test for the value-coin [Bern (ToProb d #"x")] under three binders
    (canonical-structure variable lookup for ["x"], ["accept"],
    ["rs"]). *)
Definition ex_reject_cbv
    (m : pmeas Ar (po_robj P))
    (d : udensity R) :=
  eDvP (ex_reject m d).

(** The rejection-sampling COMBINATOR denotation: the closed program of
    type [(ta → tR) → (ta → tR)] denotes a (promoted) function VALUE —
    the headline theorems of [ex_reject_model.v] quantify over the
    model/input it is applied to. *)
Definition ex_reject_comb_cbv
    (ta : ppl_type Ar)
    (d : udensity R) :=
  eDvP (ex_reject_comb ta d).

(** The soft-conditioning COMBINATOR denotation ([ex_condition_comb]):
    a closed program of type [(ta → tR) → (ta → tR)], like the
    rejection combinator — the conditioning law of
    [ex_reject_model.v::condition_model_E] quantifies over the
    model/input it is applied to. *)
Definition ex_condition_comb_cbv
    (ta : ppl_type Ar)
    (d : udensity R) :=
  eDvP (ex_condition_comb ta d).

(** The conditioned-model denotation: [condition M f] at a closed
    model [M]. *)
Definition ex_condition_cbv
    (ta : ppl_type Ar)
    (d : udensity R)
    (M : @named_expr R Ar (po_robj P) nil (tfun ta (tR (po_robj P)))) :=
  eDvP (ex_condition d M).

(** The surface-demo denotations — compile-time smoke tests for the
    clean surface layer: [let rec] sugar, [sample] of a bundled
    [gaussian], the comparison coin [Bern (Gt0 (m - 0))], and the
    [Bern]/[Sc] value forms over [Gt0]. *)
Definition ex_surface_demo_cbv :=
  eDvP (ex_surface_demo R_to_carrier_meas).

Definition ex_surface_walk_cbv :=
  eDvP (ex_surface_walk : @named_expr R Ar (po_robj P) nil (tR (po_robj P))).

(** The Bayesian-linear-regression elaboration smoke test.  The shared
    ["f"] is consulted once per observation AND returned at the end:
    every access goes through the comonoid duplication [coalg_d] of the
    let-clause diagonal AT THE FUNCTION-TYPE CONE [!(U⟦tR⟧ ⊸ U⟦tR⟧)]
    (a [bang_cofree] coalgebra) — duplicating a sampled FUNCTION value
    is exactly what the [!]-comonoid machinery is for. *)
Definition ex_bayes_linear_cbv
    (m : pmeas Ar (po_robj P))
    (l : seq (obs R)) :=
  eDvP (ex_bayes_linear m l).

(** The boolean-primitive smoke tests (the [tProb] constant coin
    [Bern (Const prob_half [|0|])] in [ex_fair_coin] / [ex_if_demo]). *)
Definition ex_true_cbv :=
  eDvP (ex_true : @named_expr R Ar (po_robj P) nil tbool).

Definition ex_false_cbv :=
  eDvP (ex_false : @named_expr R Ar (po_robj P) nil tbool).

Definition ex_fair_coin_cbv :=
  eDvP (ex_fair_coin : @named_expr R Ar (po_robj P) nil tbool).

Definition ex_if_demo_cbv :=
  eDvP (ex_if_demo : @named_expr R Ar (po_robj P) nil tbool).

End RecCBVDenotations.

Arguments ex_geom_cbv {R Ar} P R_to_carrier_meas.
Arguments ex_almost_loop_cbv {R Ar} P R_to_carrier_meas pr.
Arguments ex_score_posterior_cbv {R Ar} P R_to_carrier_meas m d.
Arguments ex_reject_cbv {R Ar} P R_to_carrier_meas m d.
Arguments ex_reject_comb_cbv {R Ar} P R_to_carrier_meas ta d.
Arguments ex_condition_comb_cbv {R Ar} P R_to_carrier_meas ta d.
Arguments ex_condition_cbv {R Ar} P R_to_carrier_meas ta d M.
Arguments ex_surface_demo_cbv {R Ar} P R_to_carrier_meas.
Arguments ex_surface_walk_cbv {R Ar} P R_to_carrier_meas.
Arguments ex_bayes_linear_cbv {R Ar} P R_to_carrier_meas m l.
Arguments ex_true_cbv {R Ar} P R_to_carrier_meas.
Arguments ex_false_cbv {R Ar} P R_to_carrier_meas.
Arguments ex_fair_coin_cbv {R Ar} P R_to_carrier_meas.
Arguments ex_if_demo_cbv {R Ar} P R_to_carrier_meas.

(** ** Example — [ex_tprob_demo] — the clean [tProb] surface end-to-end
       (STAGE T1, ADDITIVE smoke test — the CANONICAL [probObj] ACCEPTANCE
       TEST)

    A closed program exercising the new probability type [tProb] over a
    SINGLE bundled [P : probObj Ar] — NO threaded witnesses:
    [[
       let "x" := sample m in
       if Bern (Sigmoid #"x") then [|1|] else [|0|]
    ]]
    — sample a real [x], push it through the logistic sigmoid into the
    [[0,1]] object [po_obj P] (a [tProb P] value), flip a [tProb]-Bernoulli
    on it, and branch.  The point of the redesign: [Sigmoid #"x"] and
    [Bern (..)] carry NO density / inclusion / factoring witnesses — the
    bundle [P] is recovered by inference from the FOLDED types [tProb P] /
    [tProb_robj P].  This is the acceptance test for the canonical
    [probObj] structure.  [ex_tprob_demo2] is the constant-coin variant
    [Bern (Const prob_half #"x")]. *)

Section TProbDemo.
Variables (R : realType) (Ar : MeasSubcat R).

(* The whole [[0,1]] interface is now ONE bundle. *)
Variable (P : probObj Ar).

(* The only remaining standing hypothesis is the [sample]-transport
   measurability of the carrier cast — an [eD] requirement, unrelated to
   the [probObj] bundle. *)
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier (po_robj_eq P)).

Variable (m : pmeas Ar (po_robj P)).

(** The clean surface program — [P] inferred everywhere, no witnesses. *)
Definition ex_tprob_demo
    : @named_expr R Ar (po_robj P) nil (tProb_robj P) :=
  [ let "x" := sample m in
    if Bern (Sigmoid # "x") then [| 1 |] else [| 0 |] ].

(** The constant-coin variant: [Bern (Const prob_half #"x")]. *)
Definition ex_tprob_demo2
    : @named_expr R Ar (po_robj P) nil (tProb_robj P) :=
  [ let "x" := sample m in
    if Bern (Const prob_half # "x") then [| 1 |] else [| 0 |] ].

(** The CBV denotations — the end-to-end elaboration smoke tests. *)
Definition ex_tprob_demo_cbv :=
  @eD R Ar (po_robj P) (po_robj_eq P) (po_robj_meas P) R_to_carrier_meas _ _
      ex_tprob_demo.

Definition ex_tprob_demo2_cbv :=
  @eD R Ar (po_robj P) (po_robj_eq P) (po_robj_meas P) R_to_carrier_meas _ _
      ex_tprob_demo2.

End TProbDemo.

Arguments ex_tprob_demo {R Ar} P m.
Arguments ex_tprob_demo2 {R Ar} P m.
Arguments ex_tprob_demo_cbv {R Ar} P R_to_carrier_meas m.
Arguments ex_tprob_demo2_cbv {R Ar} P R_to_carrier_meas m.
