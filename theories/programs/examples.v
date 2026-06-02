(**md**************************************************************************)
(** * Headline PPL examples — six probabilistic programs in direct-style
       named surface syntax, with structural reduction lemmas

    Six end-to-end examples for the DIRECT-STYLE named-variable PPL
    of [theories/programs/ppl.v], each written in the [ppl_named]
    custom entry [[ … ]] and paired with a [_denot_E] structural
    reduction lemma exposing the outer [kbind_ext]-shape of its
    denotation.  The file is split into two groups:

    - **QBS headlines (1–3)** — total-mass programs.  Pure
      sample-and-score, no recursion.  Each is paired with its
      [_denot_E] reduction and, where landed, a Law-3-reduced
      [_marginal] / [_is_weighted] form.  See "Headline status" below.
    - **Phase 4 partial-termination examples (4–6)** — combine
      [ne_fix] (the CBV value-fixpoint of
      [theories/programs/infra/em_fix.v]) with [ne_if] / [ne_bernoulli]
      to demonstrate divergence and sub-probability mass at the
      denotational level.

    Direct style: the source language exposes no probability-monad
    marker.  The function type [tfun tR tR] (NOT [tprob (tfun tR tR)])
    is itself the Kleisli exponential at the semantic level (its
    interpretation [tyD (tfun A B) = !̃(U A ⊸ U(T B))] carries the
    monad in the codomain).  All effects are implicit; the [kbind_ext]
    structure surfaces only at the level of [eD].

    ** QBS headlines **
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
      joint-pushforward-then-density reduction.

    ** Phase 4 partial-termination examples (beyond the paper) **
    - [ex_loop]: [(let rec l = λ_. l ()) ()] : [tunit] — bare
      divergence; total mass 0.  [ex_loop_denot] is the Kleene
      supremum of [Phi_fun] (no closed form claimed).
    - [ex_geom]: [(let rec g = λ_.
      if Bernoulli(1/2) then 0 else 1 + g ()) ()] : [tR] — geometric
      counter; total mass 1 (almost-surely terminating).
      [ex_geom_denot_E] exposes the structural
      [kcomp (app_pair _ _) (bang_m ∘ em_pair (Yfix_fun_T body) ne_tt)]
      form.
    - [ex_almost_loop p Hp_ge0 Hp_le1]:
      [(let rec l = λ_. if Bernoulli(p) then () else l ()) ()] :
      [tunit] — parameterised partial termination; total mass [p].
      [ex_almost_loop_denot_E] is the analogous structural reduction.
      At [p = 0] we recover [ex_loop]; at [p > 0] the program is
      almost-surely terminating.

    ** Headline status ** (closed-form identification of the
    denotation with a "standard distribution")

    | Example | Headline identity | What is landed here |
    | --- | --- | --- |
    | [ex_random_constant] | marginal at [x] = [µ] | **CLOSED-FORM** [ex_random_constant_marginal_headline] (kbind_ext (apply_at x) ex_random_constant_denot = sample_kleisli µ Hµ); intermediate Law-3 shape kept as [ex_random_constant_marginal] |
    | [ex_random_linear] | marginal at [x] = pushforward of [µ⊗µ] along [(m,b)↦m·x+b] | Outermost Law-3 collapse [ex_random_linear_marginal] |
    | [ex_bayes_linear] | denotation = [f·µ] (unnormalised posterior) | Law-3 collapse + score-return identifies as [∫ prom(f(r)·δ_r) dµ] ([ex_bayes_linear_is_weighted_kscore] / [ex_bayes_linear_is_weighted]) |
    | [ex_loop] / [ex_geom] / [ex_almost_loop] | (no closed form claimed) | typechecking + structural [_denot_E] for the latter two |

    The remaining gaps to the closed-form identification of the QBS
    headlines (named-syntax β / [kbind_ext]–[fmeas_lax] commutativity /
    Law 2) are documented in detail above each [_marginal] /
    [_is_weighted] lemma below. *)

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
From mathcomp.analysis Require Import lebesgue_integral_definition.

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
Require Import Icones.programs.infra.cbv_adjunction.
Require Import Icones.programs.infra.em_fix.
Require Import Icones.programs.cbv.
Require Import Icones.programs.ppl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Import Icones_tensor_hom_iso.

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

(** ** Lemma 1 — [ex_random_constant_marginal]

    Evaluating the random constant function at any point recovers the
    prior [µ]: [E[ (λx. c)(x) ] = E[c]] when [c ∼ µ].

    The [apply_at x] helper is the named-syntax sugar for the
    "given a computation of a function, apply it to the literal [x]"
    Kleisli continuation, in the singleton context
    [[("f", tfun tR tR)]].  It is the [eD] image of the surface term
    [#"f" @ [|x|]].  The lemma's LHS
    [kbind_ext (apply_at x) ex_random_constant_denot] is exactly
    [eD] of [let "f" := ex_random_constant in #"f" @ [|x|]] (by
    [eD_let]).

    HEADLINE NOT YET CLOSED.  The marginal identity itself awaits
    the [kbind_ext_etaR] / [kbind_ext_A] monad laws on [ppl.v]'s
    [kbind_ext]; only the [apply_at] helper is landed. *)
Section LemmaOneMarginalConstant.
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
Local Notation eD' :=
  (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas).

(** [apply_at x]: the Kleisli continuation "given a function value
    bound under the name [\"f\"], apply it to the literal [x]".
    Defined via the named-syntax surface expression [#"f" @ [|x|]],
    which by [eD_app] denotes the appropriate [kcomp ∘ app_pair ∘
    bang_m ∘ em_pair] composite. *)
Local Definition apply_at (x : R) :
    coalg_hom (ctxD (drop_names [:: ("f"%string, tfun tR' tR')]))
              (Tobj (tyD tR')) :=
  eD' [ # "f" @ [| x |] ].

(** *** Lemma 1 (Law-3-reduced form) — the marginal-at-[x] denotation
    as a [kcomp]-chain.

    The denotation of [let f := (let c := sample µ in λ_. c) in f(x)],
    obtained as [kbind_ext (apply_at x) ex_random_constant_denot],
    reduces under Law 3 ([kbind_ext_terminal_source]) to a
    [kcomp]-composition through the canonical iso [EM_prod EM_term A
    ≅ A], applied to BOTH the outer [f]-bind and the inner [c]-bind
    whose sources are [EM_term = ctxD nil].

    What this lemma delivers (axiom-free, 3 boolp).
    The shape directly mirrors the reduced form of Lemma 3
    ([ex_bayes_linear_is_weighted]) on commit [6541828]: the two
    nested [kbind_ext]s collapse, via Law 3 twice and one
    re-association by [kcomp_A], into a single [kcomp ... sample].
    The headline-target form [= sample_kleisli µ Hµ] additionally
    requires the merged [kcomp K_outer K_inner] to reduce to
    [tunit_eta (tyD tR')] (the β-rule for [#"f" @ [|x|]] specialised
    to the constant-lambda value [λ_. c]).

    Headline status.  The full headline-closed form
    [= sample_kleisli µ Hµ] is delivered as
    [ex_random_constant_marginal_headline] below.  This
    intermediate Law-3-reduced shape is kept because it is a useful
    stepping stone (the headline proof rewrites against it). *)
Lemma ex_random_constant_marginal (x : R) :
  kbind_ext (apply_at x)
    (@ex_random_constant_denot R Ar R_obj R_carrier_eq R_carrier_meas
       R_to_carrier_meas mu Hmu)
  = kcomp
      (coalg_comp (apply_at x)
                  (em_pair (em_term_mor (tyD (tfun tR' tR')))
                           (coalg_id (tyD (tfun tR' tR')))))
      (kcomp
        (coalg_comp (eD' ex_rc_lam)
                    (em_pair (em_term_mor (tyD tR'))
                             (coalg_id (tyD tR'))))
        (sample_kleisli (ctxD (drop_names (R:=R) (Ar:=Ar) [::]))
                        mu Hmu)).
Proof.
rewrite (@ex_random_constant_denot_E R Ar R_obj
           R_carrier_eq R_carrier_meas R_to_carrier_meas mu Hmu).
rewrite (kbind_ext_terminal_source
           (eD' ex_rc_lam)
           (sample_kleisli (ctxD (drop_names [::])) mu Hmu)).
by rewrite kbind_ext_terminal_source.
Qed.

(** *** Lemma 1 (headline-closed form) — marginal at [x] IS [sample µ]

    The headline equation: evaluating the random-constant program at
    any point [x : R] recovers the prior [µ].  This is the
    QBS-paper-flagship identity for [ex_random_constant].

    Proof strategy.  Start from [ex_random_constant_marginal] (Law-3-
    reduced shape), then collapse the merged [kcomp K_outer K_inner]
    to [tunit_eta (tyD tR') ∘ V] for some value [V : EM_term → tyD tR']
    using:
    - [kcomp_A] to re-associate;
    - [kcomp_eta_natR] to absorb the [tunit_eta] coming out of
      [eD ex_rc_lam = η ∘ lam_coalg (eD [#"c"])];
    - the value-form β rule [eD_app_lam_subst] applied to the
      lambda body [#"c"] and the [em_term_mor]-collapsed argument;
    - [em_proj2_pair] to collapse the projection on the paired
      argument (the body [#"c"] semantically projects onto the
      second component);
    - [kcomp_etaL] (= [kcomp η f = f]) to discharge the outer
      [tunit_eta] composite and recover [sample_kleisli µ Hmu]. *)
(** Helper — terminal uniqueness lifted to [coalg_hom]: any
    [coalg_hom Q P] composed with [em_term_mor P] equals [em_term_mor Q].
    Two-line proof via [coalg_hom_eqP] + [coalg_mor_e]. *)
Local Lemma em_term_mor_natL_aux (Q P : Coalgebra Ar)
    (h : coalg_hom Q P) :
  coalg_comp (em_term_mor P) h = em_term_mor Q.
Proof.
apply: coalg_hom_eqP.
rewrite coalg_comp_mor /=.
apply: (coalg_mor_e (ch_mor h)).
exact: ch_is_mor.
Qed.

(** Helpers — cartesian β at [coalg_hom] level (the [em_proj{1,2}_pair]
    of [em_cartesian.v] are stated at the icones level, with explicit
    [is_coalg_mor] side conditions).  At the [coalg_hom] level the side
    conditions are automatic. *)
Local Lemma em_proj1_pair_coalg (Z P Q : Coalgebra Ar)
    (f : coalg_hom Z P) (g : coalg_hom Z Q) :
  coalg_comp (em_proj1 P Q) (em_pair f g) = f.
Proof.
apply: coalg_hom_eqP.
rewrite coalg_comp_mor /=.
apply: em_proj1_pair.
exact: ch_is_mor.
Qed.

Local Lemma em_proj2_pair_coalg (Z P Q : Coalgebra Ar)
    (f : coalg_hom Z P) (g : coalg_hom Z Q) :
  coalg_comp (em_proj2 P Q) (em_pair f g) = g.
Proof.
apply: coalg_hom_eqP.
rewrite coalg_comp_mor /=.
apply: em_proj2_pair.
exact: ch_is_mor.
Qed.

Lemma ex_random_constant_marginal_headline (x : R) :
  kbind_ext (apply_at x)
    (@ex_random_constant_denot R Ar R_obj R_carrier_eq R_carrier_meas
       R_to_carrier_meas mu Hmu)
  = sample_kleisli (ctxD (drop_names (R:=R) (Ar:=Ar) [::])) mu Hmu.
Proof.
(* Start from the Law-3-reduced shape of [ex_random_constant_marginal]. *)
rewrite (ex_random_constant_marginal x).
rewrite -kcomp_A.
(* Suffices: [kcomp K_outer K_inner = tunit_eta tR'].  Then by
   [kcomp_etaL] the whole thing reduces to [sample_kleisli µ Hmu]. *)
suff Hbeta :
  kcomp
    (coalg_comp (apply_at x)
                (em_pair (em_term_mor (tyD (tfun tR' tR')))
                         (coalg_id (tyD (tfun tR' tR')))))
    (coalg_comp (eD' ex_rc_lam)
                (em_pair (em_term_mor (tyD tR'))
                         (coalg_id (tyD tR'))))
  = tunit_eta (tyD tR').
{ rewrite Hbeta. exact: kcomp_etaL. }
(* Unfold [eD ex_rc_lam = η ∘ lam_coalg (eD body)] and identify the body. *)
rewrite /ex_rc_lam eD_lam.
set Mbody :=
  @eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas
      (("x"%string, tR') :: ("c"%string, tR') :: nil)%list tR'
      [# "c"].
(* Pull the [η] out of the K_inner composite. *)
rewrite -(coalg_compA (tunit_eta (tyD (tfun tR' tR')))
                      (lam_coalg Mbody)
                      (em_pair (em_term_mor (tyD tR'))
                               (coalg_id (tyD tR')))).
rewrite kcomp_eta_natR.
(* Goal: [coalg_comp K_outer V_value = η] where
   [V_value = coalg_comp (lam_coalg Mbody) P1] and
   [K_outer = coalg_comp (apply_at x) P2]. *)
(* Re-associate to expose the inner [P2 ∘ lam_coalg ∘ P1]. *)
rewrite -coalg_compA.
rewrite (coalg_compA (em_pair (em_term_mor (tyD (tfun tR' tR')))
                              (coalg_id (tyD (tfun tR' tR'))))
                     (lam_coalg Mbody)
                     (em_pair (em_term_mor (tyD tR'))
                              (coalg_id (tyD tR')))).
(* [P2 ∘ lam_coalg = em_pair (em_term_mor ∘ lam_coalg) (lam_coalg)]. *)
rewrite (em_pair_coalg_comp (lam_coalg Mbody)
          (em_term_mor (tyD (tfun tR' tR')))
          (coalg_id (tyD (tfun tR' tR')))).
rewrite coalg_compIl em_term_mor_natL_aux.
(* Now: [apply_at x ∘ (em_pair em_term_mor (lam_coalg Mbody) ∘ P1) = η].
   Re-associate so [apply_at x ∘ em_pair em_term_mor (lam_coalg Mbody)]
   becomes the next focus. *)
rewrite coalg_compA.
(* Goal: [(apply_at x ∘ em_pair em_term_mor (lam_coalg Mbody)) ∘ P1 = η].
   Inner: reduce [apply_at x ∘ em_pair em_term_mor (lam_coalg Mbody)]
   to [η ∘ em_proj2 EM_term (tyD tR')] using [eD_app_lam_subst_const]. *)
have Hinner :
  coalg_comp (apply_at x)
             (em_pair (em_term_mor (EM_prod EM_term (tyD tR')))
                      (lam_coalg Mbody))
  = coalg_comp (tunit_eta (tyD tR'))
               (em_proj2 EM_term (tyD tR')).
{ (* Unfold apply_at x. *)
  rewrite /apply_at eD_app eD_var eD_real /=.
  (* Now the inner is kcomp app_pair (bang_m ∘ em_pair F X) postcomposed
     by em_pair em_term_mor (lam_coalg Mbody).  Push the postcomposition
     through kcomp and bang_m. *)
  rewrite kcomp_coalg_compR -coalg_compA.
  (* Show that, in the named-PPL surface, eD' [#"f"] in ctx [("f", tfun)]
     unfolds to η ∘ em_proj2 EM_term (tyD (tfun tR' tR')) — via the
     canonical-structure-driven [ne_var'] resolution. *)
  (* eD' [#"f"] = η ∘ em_proj2; eD' [|x|] = real_kleisli x at the
     appropriate context (canonical-structure resolution gives these). *)
  (* Apply em_pair_coalg_comp to push em_pair em_term_mor (lam_coalg Mbody)
     into the em_pair (η ∘ em_proj2, real_kleisli x). *)
  rewrite (em_pair_coalg_comp
            (em_pair (em_term_mor (EM_prod EM_term (tyD tR')))
                     (lam_coalg Mbody))
            (coalg_comp (tunit_eta (tyD (tfun tR' tR')))
                        (em_proj2 EM_term (tyD (tfun tR' tR'))))
            (real_kleisli (EM_prod EM_term (tyD (tfun tR' tR'))) x)).
  (* First arg: η ∘ em_proj2 ∘ em_pair em_term_mor lam_coalg = η ∘ lam_coalg.
     Second arg: real_kleisli x ∘ em_pair = real_kleisli x (at new source). *)
  rewrite -coalg_compA.
  rewrite (em_proj2_pair_coalg
            (em_term_mor (EM_prod EM_term (tyD tR')))
            (lam_coalg Mbody)).
  rewrite (_ : coalg_comp (real_kleisli (EM_prod EM_term (tyD (tfun tR' tR'))) x)
                          (em_pair (em_term_mor (EM_prod EM_term (tyD tR')))
                                   (lam_coalg Mbody))
             = real_kleisli (EM_prod EM_term (tyD tR')) x); last first.
  { rewrite /real_kleisli.
    exact: const_kleisli_natL. }
  (* The β rule fires. *)
  rewrite (eD_app_lam_subst_const Mbody
            (dirac_Hprom_str (R_to_carrier R_carrier_eq x)
                             (dirac_fmeas_norm_le1 _))).
  (* RHS of eD_app_lam_subst_const = Mbody ∘ em_pair coalg_id const_value.
     Mbody = η ∘ (em_proj2 ∘ em_proj1) — the var_lookup of "c". *)
  rewrite /Mbody.
  have HMbody :
    @eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas
        [:: ("x"%string, tR'); ("c"%string, tR')] tR' [# "c"]
    = coalg_comp (tunit_eta (tyD tR'))
                 (coalg_comp (em_proj2 EM_term (tyD tR'))
                             (em_proj1 (EM_prod EM_term (tyD tR'))
                                       (tyD tR'))) by [].
  rewrite HMbody.
  rewrite -!coalg_compA.
  rewrite (em_proj1_pair_coalg (coalg_id (EM_prod EM_term (tyD tR')))
                               (const_value
                                  (dirac_Hprom_str
                                     (R_to_carrier R_carrier_eq x)
                                     (dirac_fmeas_norm_le1 _))
                                  (EM_prod EM_term (tyD tR')))).
  by rewrite coalg_compIr. }
(* Now use [Hinner] to close. *)
rewrite Hinner.
(* Goal: [(η ∘ em_proj2) ∘ P1 = η]. *)
rewrite -coalg_compA.
rewrite (em_proj2_pair_coalg
          (em_term_mor (tyD tR'))
          (coalg_id (tyD tR'))).
by rewrite coalg_compIr.
Qed.

End LemmaOneMarginalConstant.

Arguments apply_at
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} x.
Arguments ex_random_constant_marginal
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} mu Hmu x.
Arguments ex_random_constant_marginal_headline
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} mu Hmu x.

(** ** Lemma 2 — marginal-at-[x] of [ex_random_linear] (Shape C / partial)

    The denotation of
    [let m := sample µ in let b := sample µ in λ_. m·_+b],
    APPLIED at [x] via [apply_at x] (so the whole closed program is
    [let f := (let m := sample µ in let b := sample µ in λ_. m·_+b)
              in f(x)]), reduces — via Law 3 ([kbind_ext_terminal_source])
    on the OUTERMOST [kbind_ext] (the [f]-bind, source [EM_term =
    ctxD nil]) — to a [kcomp]-form.

    This is Shape C of the prompt's three options.  The inner
    nested-double-bind [kbind_ext (kbind_ext (eD ex_rl_lam)
    sample_m_at_ctxD_m) sample_nil] is left INTACT (the [b]-bind's
    source is [ctxD ((m,tR)::nil) = EM_prod EM_term (tyD tR)], which
    is NOT [EM_term], so Law 3 does NOT apply to it).

    What is NOT delivered.
    - Shape A — pushforward via [fmeas_lax_pre_fubini] of [µ⊗µ] —
      requires the arithmetic-Dirac lifts ([add_lift_dirac],
      [mul_lift_dirac]) chained with [fmeas_lax]/[fubini] to expose
      the joint-pushforward form [(m,b) ↦ µ⊗µ-pushforward of
      m·x+b]; this needs additional infrastructure on the integration
      side (a [kbind_ext]/[fmeas_lax] interaction lemma) that the
      cones library does not currently expose at the [kbind_ext]
      level.
    - Shape B — double-bind chain
      [kbind_ext arith_kleisli (fmeas_lax_pre mu mu)] — same blocker:
      the [kbind_ext]/[fmeas_lax] commutativity is missing.

    Why the inner cannot be further reduced.
    Both inner [kbind_ext]s have non-terminal sources: the
    [b]-bind's source is [EM_prod EM_term (tyD tR)]; the [m]-bind's
    source is [EM_term] but its continuation [eD ex_rl_lam ∘ ...]
    needs a "named-syntax β" identity to collapse the [\ "x"] lambda
    against the literal [|x|] (same blocker as for Lemma 1's full
    form). *)
Section LemmaTwoMarginalLinear.
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
Local Notation eD' :=
  (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas).

(** *** Lemma 2 (Law-3-outer-unwrap form / Shape C) *)
Lemma ex_random_linear_marginal (x : R) :
  kbind_ext (@apply_at R Ar R_obj R_carrier_eq R_carrier_meas
                       R_to_carrier_meas x)
    (@ex_random_linear_denot R Ar R_obj R_carrier_eq R_carrier_meas
       R_to_carrier_meas mu Hmu)
  = kcomp
      (coalg_comp (@apply_at R Ar R_obj R_carrier_eq R_carrier_meas
                             R_to_carrier_meas x)
                  (em_pair (em_term_mor (tyD (tfun tR' tR')))
                           (coalg_id (tyD (tfun tR' tR')))))
      (kbind_ext
        (kbind_ext
           (eD' ex_rl_lam)
           (sample_kleisli
              (ctxD (drop_names (("m"%string, tR') :: nil))) mu Hmu))
        (sample_kleisli (ctxD (drop_names (R:=R) (Ar:=Ar) [::]))
                        mu Hmu)).
Proof.
rewrite (@ex_random_linear_denot_E R Ar R_obj
           R_carrier_eq R_carrier_meas R_to_carrier_meas mu Hmu).
by rewrite kbind_ext_terminal_source.
Qed.

End LemmaTwoMarginalLinear.

Arguments ex_random_linear_marginal
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} mu Hmu x.

(** ** Lemma 2 (headline pushforward form) — Gap C application

    Building on [fmeas_lax_pre_preimage] ([theories/homs/fmeas_lax.v],
    Gap C piece 1) and the arithmetic-Dirac lifts [add_lift_dirac] /
    [mul_lift_dirac] ([theories/programs/ppl.v]), we deliver the
    HEADLINE PUSHFORWARD form of the [ex_random_linear] marginal at
    [x] as a measure-theoretic identity.

    Mathematical content.  The headline target of the marginal of
    [let m := sample µ in let b := sample µ in λx. m·x + b] at [x] is

      [∀ measurable U ⊆ R_obj,
       fmeas_mu (fmeas_lax_pre µ µ) (arith_at_x_fun x ⁻¹ U)
       = ∫µ ∫µ \d_{m·x + b} U.]

    The LHS is the pushforward of [µ ⊗ µ] (joint measure on
    [ar_prod R_obj R_obj]) along the linear-in-[(m,b)] arithmetic
    [(m, b) ↦ m·x + b] (encoded as [arith_at_x_fun x]).  Its
    iterated form on the RHS exposes the natural shape downstream
    consumers (QBS-style pushforward statements) expect.

    On top of this measure identity, the arithmetic-Dirac collapse
    [arith_at_x_dirac] computes the headline pointwise:

      [arith_at_x_fun x (ar_prod_cast (R_to_carrier m, R_to_carrier b))
       = R_to_carrier (m·x + b)]

    which converts a Dirac product input [(δ_m, δ_b)] into a Dirac
    output [δ_(m·x+b)], matching the Dirac evaluation laws
    [add_lift_dirac] / [mul_lift_dirac].

    Honesty caveats.
    - This lemma does NOT collapse the [kbind_ext]/[kbind_ext] chain
      in [ex_random_linear_marginal] above to the single
      [sample (fmeas_lax µ µ)] form.  The full Kleisli-arrow upgrade
      requires both (i) the named-syntax β rule (documented as
      blocking the headline form of Lemma 1) and (ii) the cartesian-
      η rule [em_pair_mor (em_proj1, em_proj2) = id] (documented in
      [theories/programs/ppl.v] above [Section KbindExtLaws]), neither
      of which is axiom-free in the current cones library.
    - What IS delivered is the MEASURE-LEVEL headline identity that
      the marginal SHOULD satisfy: the joint measure
      [fmeas_lax_pre µ µ] pre-image-tested at the arithmetic
      [(m, b) ↦ m·x + b] decomposes as the iterated integral of
      Dirac-at-(m·x+b)-evaluations — exactly the shape that
      [ex_random_linear]'s marginal at [x] is supposed to denote. *)
Section LemmaTwoMarginalLinearHeadline.
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

Local Notation cR := (carrier_to_R R_carrier_eq).

(** *** The arithmetic-at-[x] function [(m, b) ↦ m·x + b]

    Packaged as a measurable function on the propositional product
    carrier [ar_carrier (ar_prod R_obj R_obj)]. *)

Section ArithAtX.
Variable (x : R).

Definition arith_at_x_fun
    (p : ar_carrier Ar (ar_prod Ar R_obj R_obj)) :
    ar_carrier Ar R_obj :=
  R_to_carrier R_carrier_eq
    ((cR (ar_prod_uncast p).1 * x + cR (ar_prod_uncast p).2)%R).

Lemma arith_at_x_fun_meas :
  measurable_fun
    [set: ar_carrier Ar (ar_prod Ar R_obj R_obj)] arith_at_x_fun.
Proof.
rewrite /arith_at_x_fun.
apply: (measurableT_comp (f := R_to_carrier R_carrier_eq));
  first exact: R_to_carrier_meas.
have meas_unc : measurable_fun [set: _]
    (ar_prod_uncast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj))
  by exact: (ar_prod_uncast_meas Ar R_obj R_obj).
have meas_fst :
  measurable_fun [set: ar_carrier Ar (ar_prod Ar R_obj R_obj)]
    (fun p => (ar_prod_uncast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj) p).1)
  by exact: (measurableT_comp measurable_fst meas_unc).
have meas_snd :
  measurable_fun [set: ar_carrier Ar (ar_prod Ar R_obj R_obj)]
    (fun p => (ar_prod_uncast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj) p).2)
  by exact: (measurableT_comp measurable_snd meas_unc).
have meas_fst_R :
  measurable_fun [set: _]
    (fun p => cR (ar_prod_uncast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj) p).1)
  by exact: (measurableT_comp R_carrier_meas meas_fst).
have meas_snd_R :
  measurable_fun [set: _]
    (fun p => cR (ar_prod_uncast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj) p).2)
  by exact: (measurableT_comp R_carrier_meas meas_snd).
have meas_fst_R_mul_x :
  measurable_fun [set: _]
    (fun p => (cR (ar_prod_uncast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj) p).1
              * x)%R)
  by exact: (measurable_funM meas_fst_R (measurable_cst x)).
exact: measurable_funD.
Qed.

(** *** Dirac evaluation rule for [arith_at_x_fun]

    On a cartesian-cast pair of [R]-to-carrier reals [(a, b)]:

      [arith_at_x_fun x (ar_prod_cast (R_to_carrier a, R_to_carrier b))
       = R_to_carrier (a·x + b).]

    This is the headline DIRAC-INPUT EVALUATION RULE: matches the
    surface program's [\ "x" :: tR => # "m" · # "x" + # "b"] under
    [m := a, b := b]. *)
Lemma arith_at_x_cast (a b : R) :
  arith_at_x_fun
    (ar_prod_cast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj)
       (R_to_carrier R_carrier_eq a, R_to_carrier R_carrier_eq b)) =
  R_to_carrier R_carrier_eq (a * x + b)%R.
Proof.
by rewrite /arith_at_x_fun ar_prod_castK /= !R_to_carrierK.
Qed.

Section HeadlinePushforward.
Local Open Scope ereal_scope.

(** *** Headline pushforward identity — Gap C application

    For every measurable [U ⊆ ar_carrier R_obj], the pre-image
    measure of [fmeas_lax_pre µ µ] under [arith_at_x_fun x]
    decomposes as the iterated integral

      [∫µ ∫µ \d_(R_to_carrier (cR m · x + cR b)) U.]

    This is the headline form of the marginal-at-[x] measure for
    [ex_random_linear].  Proved by direct application of
    [fmeas_lax_pre_preimage] (Gap C piece 1 in
    [theories/homs/fmeas_lax.v]) with [φ := arith_at_x_fun x]. *)
Lemma ex_random_linear_marginal_headline
    (U : set (ar_carrier Ar R_obj)) :
  measurable U ->
  fmeas_mu (fmeas_lax_pre mu mu) (arith_at_x_fun @^-1` U) =
    \int[fmeas_mu mu]_(m in [set: ar_carrier Ar R_obj])
      \int[fmeas_mu mu]_(b in [set: ar_carrier Ar R_obj])
        \d_(arith_at_x_fun
              (ar_prod_cast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj)
                            (m, b))) U.
Proof.
move=> mU.
exact: (fmeas_lax_pre_preimage arith_at_x_fun arith_at_x_fun_meas
          mu mu U mU).
Qed.

(** *** Dirac evaluation form of the headline

    Specialised to [m = R_to_carrier a] and [b = R_to_carrier b']:
    the integrand [\d_(arith_at_x_fun (ar_prod_cast (m, b))) U]
    equals [\d_(R_to_carrier (a·x + b)) U], the "Dirac-output"
    form that one expects from feeding Dirac inputs through the
    arithmetic.  This is the bridge between the iterated form on
    the RHS above and the [add_lift_dirac]/[mul_lift_dirac] Dirac
    laws for [add_lift]/[mul_lift]. *)
Lemma ex_random_linear_arith_dirac_E (a b : R)
    (U : set (ar_carrier Ar R_obj)) :
  \d_(arith_at_x_fun
        (ar_prod_cast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj)
                      (R_to_carrier R_carrier_eq a,
                       R_to_carrier R_carrier_eq b))) U =
  (\d_(R_to_carrier R_carrier_eq (a * x + b)%R) U : \bar R).
Proof. by rewrite arith_at_x_cast. Qed.

End HeadlinePushforward.

End ArithAtX.

End LemmaTwoMarginalLinearHeadline.

Arguments arith_at_x_fun
  {R Ar R_obj} R_carrier_eq x p.
Arguments arith_at_x_fun_meas
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} x.
Arguments arith_at_x_cast
  {R Ar R_obj R_carrier_eq} x a b.
Arguments ex_random_linear_marginal_headline
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} mu x U _.
Arguments ex_random_linear_arith_dirac_E
  {R Ar R_obj R_carrier_eq} x a b U.

(** ** Lemma 3 — the Bayesian posterior denotes a weighted sub-probability

    THE PARTIAL DELIVERABLE.  This section delivers the
    integration-side machinery for the headline QBS identity:

    - [weighted_dirac_path] : the measurable path [r ↦ f(cR r) · δ_r]
      in [path_car Ar R_obj (FMeas R_obj)].

    - [weighted_mu] : the weighted measure
      [int_to_linhom_fun weighted_dirac_path µ] (the cones-side
      [f · µ]), with norm bound [≤ 1] ([weighted_mu_norm_le1]).

    - [K_score] : the EM-Kleisli arrow
      [FMeas_coalgebra R_obj ⇝ Tobj (FMeas_coalgebra R_obj)] that on
      a Dirac [δ_r] returns the promoted weighted Dirac
      [prom (f(cR r) · δ_r)] ([K_score_dirac]).

    - [ex_bayes_linear_is_weighted_kscore] : the integration
      identity [Lfun (ch_mor K_score) µ
      = int_to_linhom_fun (path: r ↦ prom(f(cR r) · δ_r)) µ],
      proved by direct application of [kleisli_dirac_to_integral].

    WHAT IS NOT DELIVERED.  The headline equation
    [ex_bayes_linear_denot = sample_kleisli (ctxD nil) weighted_µ
    weighted_mu_norm_le1] (or its [Lfun_..._one1] reflection) requires
    a [kbind_ext]/[kcomp] reformulation lemma — specifically,
    [kbind_ext k (sample_kleisli µ Hµ) = kcomp K (sample_kleisli µ
    Hµ)] for the [K] obtained by precomposing [k] with the canonical
    iso [FMeas_coalgebra R_obj ≅ EM_prod EM_term (FMeas_coalgebra
    R_obj)] — which the codebase does not currently expose.  Adding
    it would naturally belong to [ppl.v] or [em_cartesian.v]; the
    cones-side and homs-side files would not need to be touched. *)

Section LemmaThreeBayesWeighted.
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
Local Notation cR := (carrier_to_R R_carrier_eq).
Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

(** *** The weighted-Dirac path [r ↦ f(cR r) · δ_r] *)

Local Definition weighted_dirac_fun (r : ar_carrier Ar R_obj) :
    fmeas R (ar_carrier Ar R_obj) :=
  fmeas_scale (NngNum (Hf_ge0 (cR r))) (dirac_fmeas r).

(** Norm bound on each path value: [f(cR r) ≤ 1] gives [‖f(cR r) · δ_r‖ ≤ 1]. *)
Local Lemma weighted_dirac_fun_norm_le1 (r : ar_carrier Ar R_obj) :
  (cone_norm (weighted_dirac_fun r : FMeas R_obj) <= 1)%R.
Proof.
rewrite /weighted_dirac_fun.
rewrite -[fmeas_scale _ _]/(precone_scale _ (dirac_fmeas r)) cone_normh.
rewrite dirac_fmeas_norm mulr1 /=.
exact: Hf_le1.
Qed.

(** Measurability of the path: per-test [e_U U] (the only kind of
    test on [FMeas R_obj]), the joint map
    [(s,r) ↦ test_fun (e_U U) s (f(cR r) · δ_r)] reduces to
    [(s,r) ↦ f(cR r) · 1_U(r)], measurable since [f ∘ cR] and [1_U]
    are measurable. *)
Local Lemma weighted_dirac_is_path :
  is_measurable_path (Ar:=Ar) (C:=FMeas R_obj) (X:=R_obj)
    weighted_dirac_fun.
Proof.
split.
  by exists 1%R => r; exact: weighted_dirac_fun_norm_le1.
move=> Y m mM.
case: mM => [U [mU ->]].
(* Per-test reduction: [test_fun (e_U U) s (f(cR r) · δ_r)
   = f(cR r) · fine(δ_r(U)) = f(cR r) · 1_U(r)]. *)
apply: (eq_measurable_fun
  (fun p : ar_carrier Ar Y * ar_carrier Ar R_obj =>
     (f (cR p.2) * fine (\d_(p.2) U : \bar R))%R)).
  move=> p _ /=.
  rewrite /weighted_dirac_fun.
  rewrite -[fmeas_scale _ _]
    /(precone_scale (NngNum (Hf_ge0 (cR p.2))) (dirac_fmeas p.2)).
  rewrite eU_linZ /= /eU_fun /=.
  by rewrite dirac_fmeas_E.
exact: mU.
have meas_f_cR :
    measurable_fun [set: ar_carrier Ar R_obj] (fun r => f (cR r)).
  apply: (measurableT_comp (f := f)); first exact: Hf_meas.
  exact: R_carrier_meas.
have meas_fst_f_cR :
    measurable_fun
      [set: (ar_carrier Ar Y * ar_carrier Ar R_obj)%type]
      (fun p => f (cR p.2)).
  exact: (measurableT_comp meas_f_cR measurable_snd).
have meas_dirac_self :
    measurable_fun [set: ar_carrier Ar R_obj]
      (fun r => fine (\d_r U : \bar R)).
  apply: (measurableT_comp (f := fine)); first exact: fine_measurable.
  exact: measurable_fun_dirac.
have meas_fst_dirac :
    measurable_fun
      [set: (ar_carrier Ar Y * ar_carrier Ar R_obj)%type]
      (fun p => fine (\d_(p.2) U : \bar R)).
  exact: (measurableT_comp meas_dirac_self measurable_snd).
exact: measurable_funM.
Qed.

Local Definition weighted_dirac_path :
    path_car Ar R_obj (FMeas R_obj) :=
  MkPath weighted_dirac_is_path.

(** Path norm bound: [path_norm weighted_dirac_path ≤ 1]. *)
Local Lemma weighted_dirac_path_norm_le1 :
  (path_norm weighted_dirac_path <= 1)%R.
Proof.
apply: ge_sup; first exact: path_normset_nonempty.
by move=> _ [r ->] /=; exact: weighted_dirac_fun_norm_le1.
Qed.

(** The integral [∫_{r∼µ} f(r)·δ_r] is in the unit ball. *)
Local Definition weighted_mu : fmeas R (ar_carrier Ar R_obj) :=
  int_to_linhom_fun weighted_dirac_path mu.

Local Lemma weighted_mu_norm_le1 : (cone_norm weighted_mu <= 1)%R.
Proof.
rewrite /weighted_mu.
apply: (@le_trans _ _ (path_norm weighted_dirac_path * fmeas_norm mu)%R).
  apply: (path_integral_norm_le (Mβ := path_norm weighted_dirac_path)).
  - move=> r; exact: path_norm_ub.
  - exact: path_is_path.
  - have := @icone_integralP _ _ _ _
              weighted_dirac_path (path_is_path weighted_dirac_path) mu.
    exact.
rewrite -[1%R]mul1r.
apply: ler_pM.
- exact: path_norm_ge0.
- exact: fmeas_norm_ge0.
- exact: weighted_dirac_path_norm_le1.
- exact: Hmu.
Qed.

(** *** The headline statement — Lemma 3

    The Bayesian posterior denotes the sample from the weighted
    measure [f · µ].  Reading.  The [const_kleisli]-wrapped form
    [sample_kleisli (ctxD nil) weighted_µ Hbnd] makes the QBS reading
    explicit: "sample from [int_to_linhom_fun weighted_dirac_path µ]",
    which is the weighted measure [f · µ] in cones-side notation. *)

(** *** The score-and-return Kleisli arrow on [FMeas_coalgebra R_obj]

    [K_score] is the FMeas-source Kleisli arrow such that on a Dirac
    [δ_r] in [FMeas R_obj] it returns the promoted weighted Dirac
    [prom (f(cR r) · δ_r)] in [Bang (FMeas R_obj) = coalg_obj (Tobj
    (FMeas R_obj))].  It is the EM-side encoding of "given [m], score
    by [f(m)] and return [m]".

    Built as [adj_psi K_under] where [K_under] is the linhom
    [int_to_linhom weighted_dirac_path] viewed as an [icones_hom]
    [FMeas R_obj → FMeas R_obj]. *)

Local Lemma K_under_norm_le1 :
  (cone_norm (int_to_linhom weighted_dirac_path) <= 1)%R.
Proof.
apply: le_trans (int_to_linhom_norm_le weighted_dirac_path) _.
rewrite -[cone_norm weighted_dirac_path]/(path_norm weighted_dirac_path).
exact: weighted_dirac_path_norm_le1.
Qed.

Local Definition K_under :
    icones_hom Ar (FMeas R_obj) (FMeas R_obj) :=
  seely.linhom_icones (int_to_linhom weighted_dirac_path) K_under_norm_le1.

Local Definition K_score :
    coalg_hom (FMeas_coalgebra R_obj) (Tobj (FMeas_coalgebra R_obj)) :=
  @adj_psi _ _ (FMeas_coalgebra R_obj) (FMeas R_obj) K_under.

(** On a Dirac [δ_r], [K_under] returns the weighted Dirac
    [f(cR r) · δ_r] (this is [int_to_linhom_fun_dirac] specialised
    to our path). *)
Local Lemma K_under_dirac (r : ar_carrier Ar R_obj) :
  Lfun K_under (dirac_fmeas r) = weighted_dirac_fun r.
Proof.
rewrite /K_under.
rewrite (seely.linhom_iconesE _ K_under_norm_le1 (dirac_fmeas r)).
exact: (int_to_linhom_fun_dirac weighted_dirac_path r).
Qed.

(** On a Dirac [δ_r], the [K_score] Kleisli arrow returns
    [prom (f(cR r) · δ_r)]: it scores the input and returns it. *)
Local Lemma K_score_dirac (r : ar_carrier Ar R_obj) :
  Lfun (ch_mor K_score) (dirac_fmeas r) =
  prom (weighted_dirac_fun r : FMeas R_obj).
Proof.
rewrite /K_score /=.
have Hball : cone_norm (dirac_fmeas r : FMeas R_obj) <= 1.
  rewrite dirac_fmeas_norm; exact: lexx.
have HC : Lfun (Coalg R_obj) (dirac_fmeas r) = prom (dirac_fmeas r : FMeas R_obj).
  exact: (Coalg_dirac R_obj r).
rewrite -[linhom_fun _ _]/(Lfun (Coalg R_obj) (dirac_fmeas r)) HC.
by rewrite (bang_fmap_prom K_under (dirac_fmeas r : FMeas R_obj) Hball)
           K_under_dirac.
Qed.

(** *** Headline — Lemma 3 (integration form, via Lemma C)

    Apply [kleisli_dirac_to_integral] to [K_score]: a Kleisli arrow
    that matches [r ↦ prom(weighted_dirac_fun r)] on every Dirac
    integrates against any [µ] to the integral of this path.  For our
    specific [µ] this is the headline identity in integration form:
    the action of the score-return Kleisli arrow on [µ] equals the
    integral [∫_{r ∼ µ} prom(f(cR r) · δ_r)]. *)

(** The [prom]-weighted-Dirac path [r ↦ prom (f(cR r) · δ_r)] is a
    measurable path: it is the composite of [weighted_dirac_fun]
    (unit-ball measurable) with the icones-level [Coalg R_obj] (=
    [prom] on the unit ball), packaged into a measurable path. *)
Local Lemma prom_weighted_dirac_is_path :
  is_measurable_path (Ar:=Ar) (C:=Bang Ar (FMeas R_obj)) (X:=R_obj)
    (fun r => Lfun (ch_mor K_score) (dirac_fmeas r)).
Proof.
exact: (path_is_path
          (linhom_to_int (icones_to_linhom (ch_mor K_score)))).
Qed.

Lemma ex_bayes_linear_is_weighted_kscore : forall mu',
  Lfun (ch_mor K_score) mu'
  = int_to_linhom_fun
      (MkPath prom_weighted_dirac_is_path) mu'.
Proof.
move=> mu'.
exact: (kleisli_dirac_to_integral K_score
          (fun r => Lfun (ch_mor K_score) (dirac_fmeas r))
          prom_weighted_dirac_is_path
          (fun r => erefl)
          mu').
Qed.

(** *** Lemma 3 (headline structural reduction)

    The Bayesian posterior denotation reduces to a Kleisli composition
    [kcomp K' (sample_kleisli µ Hµ)], where [K'] is the score-then-return
    continuation moved through the canonical iso
    [EM_prod EM_term A ≅ A].  This is the [kcomp] form of the headline
    QBS identity, obtained by Law 3 (terminal-source collapse of
    [kbind_ext]) applied to the outer prior-bind exposed by
    [ex_bayes_linear_denot_E].

    To pass from this [kcomp] form to the "the denotation IS [f·µ]"
    integration-side form would additionally require — Law 2
    ([kbind_ext_A]) and the cartesian η rule
    [em_pair_mor(em_proj1_mor, em_proj2_mor) = id] (see the gap
    documented in [theories/programs/ppl.v] above
    [Section KbindExtLaws]).  Neither is delivered axiom-free in the
    current cones library: cartesian uniqueness in [EM(!)] is not
    exposed at the [icones_hom] level by any record/lemma here, so
    only the Law-3-reachable shape closes. *)
Lemma ex_bayes_linear_is_weighted :
  @ex_bayes_linear_denot R Ar R_obj R_carrier_eq R_carrier_meas
    R_to_carrier_meas mu Hmu f Hf_meas Hf_ge0 Hf_le1
  = kcomp (coalg_comp (@eD R Ar R_obj R_carrier_eq R_carrier_meas
                            R_to_carrier_meas _ _
                            (ex_bl_cont f Hf_meas Hf_ge0 Hf_le1))
                      (em_pair (em_term_mor (tyD tR'))
                               (coalg_id (tyD tR'))))
          (sample_kleisli (ctxD (drop_names (R:=R) (Ar:=Ar) [::]))
                          mu Hmu).
Proof.
by rewrite (ex_bayes_linear_denot_E mu Hmu f Hf_meas Hf_ge0 Hf_le1)
           kbind_ext_terminal_source.
Qed.

End LemmaThreeBayesWeighted.

(** ** Example 4 — [ex_loop] : divergence via the CBV value-fixpoint

    The canonical divergence example: [(let rec l = λ_. l ()) ()].  In
    surface PPL syntax, using the [ne_fix] constructor and the
    [fix _ ::: tfun A B in _] notation introduced in [ppl.v]:
    [[
      ex_loop := [ (fix "l" ::: tfun tunit tunit in
                     \ "_" ::: tunit => # "l" @ ()) @ () ]
    ]]

    The body is [λ _. l ()], i.e. invoke the recursive [l] on the unit
    argument; the outer application then fires [l] once on [()].  At
    the denotational level [eD ex_loop : coalg_hom EM_term (Tobj EM_term)]
    converges to the Kleene fixpoint of [Φ_fun] on the unit-ball of
    [linhom_car (coalg_obj EM_term) (coalg_obj (Tobj (tyD (tfun tunit tunit))))].
    Crucially, no [Yfix_fun_T]-level computation is performed for the
    typechecking goal of this demonstration; we only verify that the
    syntax [ex_loop] type-checks and that its denotation [ex_loop_denot]
    is well-typed. *)

Section ExLoopDemo.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

(** The divergence example.  Source: [(let rec l = λ _. l ()) ()]. *)
Definition ex_loop :
    @named_expr R Ar R_obj nil tunit :=
  [ (fix "l" ::: tfun tunit tunit in \ "_" ::: tunit => # "l" @ ()) @ () ].

(** Its denotation, a Kleisli arrow [⟦[]⟧ ⇝ ⟦tunit⟧]. *)
Definition ex_loop_denot :
    coalg_hom (ctxD (drop_names nil)) (Tobj (tyD tunit)) :=
  @eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas
      nil tunit ex_loop.

End ExLoopDemo.

Arguments ex_loop {R Ar R_obj}.
Arguments ex_loop_denot {R Ar R_obj}
  R_carrier_eq R_carrier_meas R_to_carrier_meas.

(** ** Boolean primitives sanity check — [True], [False], [Bernoulli p]
       as bool-typed expressions in the empty context

    A minimal demonstration that the boolean primitives [True],
    [False], and [Bernoulli p Hp_ge0 Hp_le1] parse correctly in the
    [ppl_named] surface syntax and yield well-typed
    [named_expr nil tbool] terms whose denotations are coalgebra
    morphisms [⟦[]⟧ ⇝ ⟦tbool⟧].  No reduction lemma — we only check
    that the syntax + the [eD] interpretation typecheck. *)

Section ExBoolDemo.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

(** [True] : the boolean constant of type [tbool], in the empty context. *)
Definition ex_true : @named_expr R Ar R_obj nil tbool := [ True ].

(** [False] : the boolean constant of type [tbool], in the empty context. *)
Definition ex_false : @named_expr R Ar R_obj nil tbool := [ False ].

(** [Bernoulli { 1/2, Hge0, Hle1 }] : a fair-coin sample of type
    [tbool].  The two side-conditions are passed in braces, matching
    the [Score { ... }] convention. *)
Lemma half_ge0 : (0 <= 1 / 2 :> R)%R.
Proof. by rewrite divr_ge0// ler01. Qed.

Lemma half_le1 : (1 / 2 <= 1 :> R)%R.
Proof. by rewrite ler_pdivrMr ?mul1r ?ler1n. Qed.

Definition ex_fair_coin : @named_expr R Ar R_obj nil tbool :=
  [ Bernoulli { (1 / 2 : R), half_ge0, half_le1 } ].

(** Each example's denotation as a Kleisli arrow. *)
Definition ex_true_denot :
    coalg_hom (ctxD (drop_names nil)) (Tobj (tyD tbool)) :=
  @eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas
      nil tbool ex_true.

Definition ex_false_denot :
    coalg_hom (ctxD (drop_names nil)) (Tobj (tyD tbool)) :=
  @eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas
      nil tbool ex_false.

Definition ex_fair_coin_denot :
    coalg_hom (ctxD (drop_names nil)) (Tobj (tyD tbool)) :=
  @eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas
      nil tbool ex_fair_coin.

End ExBoolDemo.

Arguments ex_true {R Ar R_obj}.
Arguments ex_false {R Ar R_obj}.
Arguments ex_fair_coin {R Ar R_obj}.
Arguments ex_true_denot {R Ar R_obj}
  R_carrier_eq R_carrier_meas R_to_carrier_meas.
Arguments ex_false_denot {R Ar R_obj}
  R_carrier_eq R_carrier_meas R_to_carrier_meas.
Arguments ex_fair_coin_denot {R Ar R_obj}
  R_carrier_eq R_carrier_meas R_to_carrier_meas.

(** ** Example — [ex_if_demo] (Step 4)

    Sanity check for the [if-then-else] PPL constructor (Step 3, [ne_if]):
    typecheck a closed [tbool]-typed program
    [[
      if Bernoulli { 1/2, _, _ } then True else False
    ]]
    in the empty context.  No correctness lemma is claimed here; this is
    purely an elaboration sanity check exercising the [ne_if]/[case_em]
    eD clause and the [if e then M else N] surface notation. *)
Section ExIfDemo.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).

(** Witnesses [0 ≤ 1/2 ≤ 1] for the Bernoulli scrutinee — re-derived
    locally so [ExIfDemo] is standalone (the section [ExBoolDemo] above
    introduces them under hypotheses on [R_carrier_eq] etc., which this
    section does not need). *)
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

(** ** Phase 4 — productive partial-termination examples

    End-to-end probabilistic recursive programs in the named PPL
    surface syntax, combining [ne_fix] (the CBV value-fixpoint of
    [theories/programs/infra/em_fix.v]) with the [ne_if] / [ne_bernoulli]
    boolean cascade (steps 1–4 of the §9 work) to exhibit
    productive partial termination.

    - [ex_geom] : the geometric distribution
      [(let rec g = λ_. if Bernoulli(½) then 0 else 1 + g ()) ()] of
      type [tR'].  Each recursive call halts with probability ½ and
      contributes one unit to the returned real; total mass is 1, so
      this is almost-surely terminating.

    - [ex_almost_loop p _ _] : a parameterised partial-termination
      example [(let rec l = λ_. if Bernoulli(p) then () else l ()) ()]
      of type [tunit].  With continuation probability [1 - p], the
      recursive call diverges; total mass is [p · Σ (1-p)^k = 1] when
      [p > 0]. *)

Section Phase4Examples.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

(** Witnesses [0 ≤ 1/2 ≤ 1] for the geometric example's fair-coin
    Bernoulli scrutinee.  Re-derived locally so [Phase4Examples] is
    self-contained. *)
Lemma phase4_half_ge0 : (0 <= 1 / 2 :> R)%R.
Proof. by rewrite divr_ge0// ler01. Qed.

Lemma phase4_half_le1 : (1 / 2 <= 1 :> R)%R.
Proof. by rewrite ler_pdivrMr ?mul1r ?ler1n. Qed.

Local Notation tR' := (tR R_obj).

(** *** [ex_geom] — geometric distribution via [ne_fix] + [ne_if]

    Source: [(let rec g = λ_. if Bernoulli(½) then 0
                                            else 1 + g ()) ()].

    A fair-coin geometric counter: each recursive call halts with
    probability ½ and adds 1 to the running total; the outer
    application fires the closure on [()].  The denotation lives in
    [coalg_hom EM_term (Tobj (tyD tR'))]. *)

Definition ex_geom : @named_expr R Ar R_obj nil tR' :=
  [ (fix "g" ::: tfun tunit tR' in
       \ "_" ::: tunit =>
         (if Bernoulli { (1 / 2 : R), phase4_half_ge0, phase4_half_le1 }
          then [| 0%R |]
          else [| 1%R |] + # "g" @ ())) @ () ].

(** The body of the fixed-point lambda — used as the [body] argument to
    [Yfix_fun_T] when stating the structural reduction lemma. *)
Definition ex_geom_body :
    @named_expr R Ar R_obj
      (("g"%string, tfun tunit tR') :: nil)
      (tfun tunit tR') :=
  [ \ "_" ::: tunit =>
      (if Bernoulli { (1 / 2 : R), phase4_half_ge0, phase4_half_le1 }
       then [| 0%R |]
       else [| 1%R |] + # "g" @ ()) ].

(** Its denotation, a Kleisli arrow [⟦[]⟧ ⇝ ⟦tR'⟧]. *)
Definition ex_geom_denot :
    coalg_hom (ctxD (drop_names nil)) (Tobj (tyD tR')) :=
  @eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas
      nil tR' ex_geom.

(** Structural reduction — exposes the outer [ne_app] of the
    [ne_fix]/[ne_tt] pair.  Applying [eD_app] to the surface form
    [(ne_fix _ body) @ ()] and unfolding the [ne_fix] branch of [eD]
    to [Yfix_fun_T] (no separate [eD_fix] lemma is published) gives

      [ex_geom_denot = kcomp (app_pair _ _)
                             (coalg_comp (bang_m _ _)
                                         (em_pair (Yfix_fun_T (eD ex_geom_body))
                                                  (eD ne_tt)))].

    The trailing [eD ne_tt] is the singleton-from-terminal Kleisli
    return.  This is a STRUCTURAL rewrite, NOT a semantic-content
    lemma: no closed form for the [Yfix_fun_T] iterate is claimed. *)
Lemma ex_geom_denot_E :
  ex_geom_denot =
  kcomp (app_pair (tyD tunit) (tyD tR'))
    (coalg_comp
       (bang_m (coalg_obj (tyD (tfun tunit tR'))) (coalg_obj (tyD tunit)))
       (em_pair
          (Yfix_fun_T
             (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas
                  _ _ ex_geom_body))
          (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas
               _ _ (ne_tt (R_obj := R_obj) (G := nil))))).
Proof.
rewrite /ex_geom_denot /ex_geom.
rewrite eD_app.
by [].
Qed.

(** *** [ex_almost_loop p Hp_ge0 Hp_le1] — partial-termination with
       continuation probability [1 - p]

    Source: [(let rec l = λ_. if Bernoulli(p) then ()
                                              else l ()) ()].

    On each call the recursion halts with probability [p] (returning
    [()]) and recurses with probability [1 - p].  When [p > 0] the
    function terminates almost surely.

    Note on the [@ex_almost_loop] call in [ex_almost_loop_denot]: the
    section setting [Set Implicit Arguments] makes [p] auto-implicit
    (because [Hp_ge0] / [Hp_le1] reference it in their types), so the
    re-binding needs an explicit [@] here.  The final [Arguments]
    directive below restores [p] to explicit at the file's top
    level. *)

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

(** Its denotation, a Kleisli arrow [⟦[]⟧ ⇝ ⟦tunit⟧]. *)
Definition ex_almost_loop_denot (p : R)
    (Hp_ge0 : (0 <= p)%R) (Hp_le1 : (p <= 1)%R) :
    coalg_hom (ctxD (drop_names nil)) (Tobj (tyD tunit)) :=
  @eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas
      nil tunit (@ex_almost_loop p Hp_ge0 Hp_le1).

(** Structural reduction — the [tunit]-typed analogue of
    [ex_geom_denot_E].  Applies [eD_app] to the outer [ne_app] and
    unfolds the [ne_fix] branch of [eD] to [Yfix_fun_T]:

      [ex_almost_loop_denot p _ _ =
         kcomp (app_pair _ _)
               (coalg_comp (bang_m _ _)
                           (em_pair
                              (Yfix_fun_T (eD (ex_almost_loop_body p _ _)))
                              (eD ne_tt)))].

    STRUCTURAL rewrite only; no closed form for the [Yfix_fun_T]
    iterate is claimed (and indeed the operational behaviour
    depends on [p] in a non-trivial way: when [p = 0] the program
    diverges almost surely; when [p > 0] it terminates almost
    surely). *)
Lemma ex_almost_loop_denot_E (p : R)
    (Hp_ge0 : (0 <= p)%R) (Hp_le1 : (p <= 1)%R) :
  @ex_almost_loop_denot p Hp_ge0 Hp_le1 =
  kcomp (app_pair (tyD tunit) (tyD tunit))
    (coalg_comp
       (bang_m (coalg_obj (tyD (tfun tunit tunit))) (coalg_obj (tyD tunit)))
       (em_pair
          (Yfix_fun_T
             (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas
                  _ _ (@ex_almost_loop_body p Hp_ge0 Hp_le1)))
          (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas
               _ _ (ne_tt (R_obj := R_obj) (G := nil))))).
Proof.
rewrite /ex_almost_loop_denot /ex_almost_loop.
rewrite eD_app.
by [].
Qed.

End Phase4Examples.

Arguments ex_geom {R Ar R_obj}.
Arguments ex_geom_body {R Ar R_obj}.
Arguments ex_geom_denot {R Ar R_obj}
  R_carrier_eq R_carrier_meas R_to_carrier_meas.
Arguments ex_geom_denot_E {R Ar R_obj}
  R_carrier_eq R_carrier_meas R_to_carrier_meas.
Arguments ex_almost_loop {R Ar R_obj} p Hp_ge0 Hp_le1.
Arguments ex_almost_loop_body {R Ar R_obj} p Hp_ge0 Hp_le1.
Arguments ex_almost_loop_denot {R Ar R_obj}
  R_carrier_eq R_carrier_meas R_to_carrier_meas p Hp_ge0 Hp_le1.
Arguments ex_almost_loop_denot_E {R Ar R_obj}
  R_carrier_eq R_carrier_meas R_to_carrier_meas p Hp_ge0 Hp_le1.
