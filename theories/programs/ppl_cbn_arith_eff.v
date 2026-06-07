(**md*** BEYOND THE PAPER — CBN arithmetic effect-clauses [via the bridge]

    The companion to [ppl_cbn_arith_scones.v]: the honest CBN
    arithmetic clauses (the "(beta)" refinement of the (γ)-degenerate
    [cbn_add_clause_def] / [cbn_mul_clause_def] of [ppl_cbn_eff.v]),
    built by precomposing the bilinear [add_FMeas_scones] /
    [mul_FMeas_scones] of [ppl_cbn_arith_scones.v] with the standard
    [spair] of two [scones_hom]s.

    ** What this file delivers (all axiom-free)

    1. [cbn_add_clause_arith G M N] :
       [scones_hom (ctxD_CBN G) (FMeas R_obj)] —
       the honest add clause defined as
       [[
          scones_comp add_FMeas_scones (spair M N).
       ]]
       Pointwise on the unit ball:
       [[
          sc_fun (cbn_add_clause_arith G M N) g
            = add_FMeas (sc_fun M g) (sc_fun N g).
       ]]

    2. [cbn_mul_clause_arith G M N] : ditto for [mul_FMeas_scones].

    3. [eD_CBN_full_arith] : the CBN denotation pipeline with the arith
       clauses substituted for the (γ)-degenerate add/mul.  Wired with
       the SAME boolean/sample/real/score clauses as [eD_CBN_full] of
       [ppl_cbn_eff.v].

    4. [ex_rl_lam_arith_pointwise] : the honest pointwise computation
       of the lambda body of [ex_random_linear] under the arith pipeline.

    ** Why this file matters

    With the bridge of [diag_bilinear_tensor.v] and the
    [add_FMeas_scones] of [ppl_cbn_arith_scones.v], the CBN arithmetic
    primitives now have a faithful semantic interpretation.  The
    [ex_random_linear_CBN_arith_marginal] is the corresponding
    follow-up headline (the genuine pushforward identity at the
    [eD_CBN_full_arith] level, replacing the degenerate-at-zero of
    [ex_random_linear_CBN_marginal_zero] in [ppl_cbn_headlines.v]).

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
Require Import Icones.stable.totmono.
Require Import Icones.stable.stablehom.
Require Import Icones.stable.scones_cat.
Require Import Icones.stable.scones_ccc.
Require Import Icones.stable.fixpoint.
Require Import Icones.programs.ppl.
Require Import Icones.programs.examples.
Require Import Icones.programs.ppl_cbn.
Require Import Icones.programs.ppl_cbn_eff.
Require Import Icones.programs.ppl_cbn_arith.
Require Import Icones.programs.ppl_cbn_arith_scones.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** §1 — The arith add and mul clauses *)

Section ArithClauses.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Local Notation tR' := (tR R_obj).
Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

Local Notation add_FMeas_scones' :=
  (add_FMeas_scones R_carrier_eq R_carrier_meas R_to_carrier_meas).
Local Notation mul_FMeas_scones' :=
  (mul_FMeas_scones R_carrier_eq R_carrier_meas R_to_carrier_meas).

(** Honest CBN add clause: composition of the bilinear bridge
    [add_FMeas_scones] with the [spair] of the two arguments. *)
Definition cbn_add_clause_arith
    (G : ppl_ctx Ar)
    (M N : scones_hom (ctxD_CBN G) (tyD_CBN tR')) :
    scones_hom (ctxD_CBN G) (tyD_CBN tR') :=
  scones_comp add_FMeas_scones' (spair M N).

(** Honest CBN mul clause: composition of [mul_FMeas_scones] with
    [spair]. *)
Definition cbn_mul_clause_arith
    (G : ppl_ctx Ar)
    (M N : scones_hom (ctxD_CBN G) (tyD_CBN tR')) :
    scones_hom (ctxD_CBN G) (tyD_CBN tR') :=
  scones_comp mul_FMeas_scones' (spair M N).

(** Pointwise computation on the unit ball: the add clause computes to
    [add_FMeas (M g) (N g)]. *)
Lemma cbn_add_clause_arith_E
    (G : ppl_ctx Ar)
    (M N : scones_hom (ctxD_CBN G) (tyD_CBN tR'))
    (g : ctxD_CBN G) :
  (cone_norm g <= 1)%R ->
  sc_fun (cbn_add_clause_arith M N) g =
  add_FMeas R_carrier_eq R_carrier_meas R_to_carrier_meas
            (sc_fun M g) (sc_fun N g).
Proof.
move=> Hg.
rewrite /cbn_add_clause_arith.
rewrite (scomp_ball _ _ Hg).
have Hpair : sc_fun (spair M N) g = sprod_pair (sc_fun M g) (sc_fun N g).
  exact: scpair_ball.
rewrite Hpair.
have Hball_pair :
    (cone_norm (sprod_pair (sc_fun M g : FMeas R_obj)
                            (sc_fun N g : FMeas R_obj))
     <= 1)%R.
  apply: sprod_pair_norm_le1; exact: sc_image_ball.
rewrite (add_FMeas_scones_E R_carrier_eq R_carrier_meas R_to_carrier_meas _
                            Hball_pair).
by rewrite sprod_fstE sprod_sndE.
Qed.

(** Pointwise computation on the unit ball for mul. *)
Lemma cbn_mul_clause_arith_E
    (G : ppl_ctx Ar)
    (M N : scones_hom (ctxD_CBN G) (tyD_CBN tR'))
    (g : ctxD_CBN G) :
  (cone_norm g <= 1)%R ->
  sc_fun (cbn_mul_clause_arith M N) g =
  mul_FMeas R_carrier_eq R_carrier_meas R_to_carrier_meas
            (sc_fun M g) (sc_fun N g).
Proof.
move=> Hg.
rewrite /cbn_mul_clause_arith.
rewrite (scomp_ball _ _ Hg).
have Hpair : sc_fun (spair M N) g = sprod_pair (sc_fun M g) (sc_fun N g).
  exact: scpair_ball.
rewrite Hpair.
have Hball_pair :
    (cone_norm (sprod_pair (sc_fun M g : FMeas R_obj)
                            (sc_fun N g : FMeas R_obj))
     <= 1)%R.
  apply: sprod_pair_norm_le1; exact: sc_image_ball.
rewrite (mul_FMeas_scones_E R_carrier_eq R_carrier_meas R_to_carrier_meas _
                            Hball_pair).
by rewrite sprod_fstE sprod_sndE.
Qed.

End ArithClauses.

Arguments cbn_add_clause_arith {R Ar R_obj}
  R_carrier_eq R_carrier_meas R_to_carrier_meas G M N.
Arguments cbn_mul_clause_arith {R Ar R_obj}
  R_carrier_eq R_carrier_meas R_to_carrier_meas G M N.
Arguments cbn_add_clause_arith_E {R Ar R_obj}
  R_carrier_eq R_carrier_meas R_to_carrier_meas G M N g.
Arguments cbn_mul_clause_arith_E {R Ar R_obj}
  R_carrier_eq R_carrier_meas R_to_carrier_meas G M N g.

(** ** §2 — [eD_CBN_full_arith] — the honest-arith CBN pipeline *)

Section EDCBNFullArith.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

(** The arith pipeline uses the SAME boolean clauses as [eD_CBN_full].
    The boolean clauses are accepted as variables — typically wired
    with the [ppl_cbn_bool.v] M4 set. *)
Variable cbn_true_clause :
  forall (G : ppl_ctx Ar), scones_hom (ctxD_CBN G) (tyD_CBN tbool).
Variable cbn_false_clause :
  forall (G : ppl_ctx Ar), scones_hom (ctxD_CBN G) (tyD_CBN tbool).
Variable cbn_bernoulli_clause :
  forall (G : ppl_ctx Ar) (p : R)
         (Hp_ge0 : (0 <= p)%R) (Hp_le1 : (p <= 1)%R),
    scones_hom (ctxD_CBN G) (tyD_CBN tbool).
Variable cbn_if_clause :
  forall (G : ppl_ctx Ar) (t : ppl_type Ar)
         (e : scones_hom (ctxD_CBN G) (tyD_CBN tbool))
         (M N : scones_hom (ctxD_CBN G) (tyD_CBN t)),
    scones_hom (ctxD_CBN G) (tyD_CBN t).

(** The arith CBN denotation: identical to [eD_CBN_full] except for
    the add/mul clauses which are the [cbn_add_clause_arith] /
    [cbn_mul_clause_arith] of §1. *)
Definition eD_CBN_full_arith (G : named_ctx Ar) (t : ppl_type Ar)
    (M : @named_expr R Ar R_obj G t) :
    scones_hom (ctxD_CBN (drop_names G)) (tyD_CBN t) :=
  @eD_CBN R Ar R_obj
    (@cbn_sample_clause_def R Ar R_obj)
    (@cbn_real_clause_def R Ar R_obj R_carrier_eq)
    (@cbn_score_clause_def R Ar R_obj)
    (cbn_add_clause_arith R_carrier_eq R_carrier_meas R_to_carrier_meas)
    (cbn_mul_clause_arith R_carrier_eq R_carrier_meas R_to_carrier_meas)
    cbn_true_clause cbn_false_clause cbn_bernoulli_clause cbn_if_clause
    G t M.

(** *** Reduction lemmas for the new arith case — mirror the (γ)
    [eD_CBN_full_*] reductions of [ppl_cbn_eff.v]. *)

Lemma eD_CBN_full_arith_add_E
    (G : named_ctx Ar)
    (M N : @named_expr R Ar R_obj G (tR R_obj)) :
  eD_CBN_full_arith (ne_add M N) =
  cbn_add_clause_arith R_carrier_eq R_carrier_meas R_to_carrier_meas
    (drop_names G) (eD_CBN_full_arith M) (eD_CBN_full_arith N).
Proof. by []. Qed.

Lemma eD_CBN_full_arith_mul_E
    (G : named_ctx Ar)
    (M N : @named_expr R Ar R_obj G (tR R_obj)) :
  eD_CBN_full_arith (ne_mul M N) =
  cbn_mul_clause_arith R_carrier_eq R_carrier_meas R_to_carrier_meas
    (drop_names G) (eD_CBN_full_arith M) (eD_CBN_full_arith N).
Proof. by []. Qed.

(** Reduction for the unchanged clauses (sample, real, score). *)

Lemma eD_CBN_full_arith_sample_E
    (G : named_ctx Ar)
    (mu : fmeas R (ar_carrier Ar R_obj))
    (Hmu : (cone_norm mu <= 1)%R) :
  eD_CBN_full_arith (ne_sample (R_obj := R_obj) (G := G) mu Hmu) =
  cbn_sample_clause_def (drop_names G) mu Hmu.
Proof. by []. Qed.

Lemma eD_CBN_full_arith_real_E
    (G : named_ctx Ar) (r : R) :
  eD_CBN_full_arith (ne_real (G := G) (R_obj := R_obj) r) =
  cbn_real_clause_def R_carrier_eq (drop_names G) r.
Proof. by []. Qed.

End EDCBNFullArith.

Arguments eD_CBN_full_arith {R Ar R_obj}
  R_carrier_eq R_carrier_meas R_to_carrier_meas
  cbn_true_clause cbn_false_clause cbn_bernoulli_clause cbn_if_clause
  {G t} M.
Arguments eD_CBN_full_arith_add_E {R Ar R_obj}
  R_carrier_eq R_carrier_meas R_to_carrier_meas
  cbn_true_clause cbn_false_clause cbn_bernoulli_clause cbn_if_clause
  G M N.
Arguments eD_CBN_full_arith_mul_E {R Ar R_obj}
  R_carrier_eq R_carrier_meas R_to_carrier_meas
  cbn_true_clause cbn_false_clause cbn_bernoulli_clause cbn_if_clause
  G M N.

(** ** §3 — [ex_rl_lam_arith_pointwise] : the HONEST lambda body

    The pointwise evaluation of the lambda body of [ex_random_linear]
    under [eD_CBN_full_arith].  Drops the (γ)-degenerate identity of
    [ex_rl_lam_pointwise_zero] of [ppl_cbn_headlines.v] in favour of
    the genuine arithmetic computation.

    Given environment [env = (((), m), b, x)] with [m, b, x : FMeas
    R_obj] in the unit ball, the body [#"m" * #"x" + #"b"] evaluates
    to [add_FMeas (mul_FMeas m x) b]. *)

Section ExRlLamArithPointwise.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Variable cbn_true_clause :
  forall (G : ppl_ctx Ar), scones_hom (ctxD_CBN G) (tyD_CBN tbool).
Variable cbn_false_clause :
  forall (G : ppl_ctx Ar), scones_hom (ctxD_CBN G) (tyD_CBN tbool).
Variable cbn_bernoulli_clause :
  forall (G : ppl_ctx Ar) (p : R)
         (Hp_ge0 : (0 <= p)%R) (Hp_le1 : (p <= 1)%R),
    scones_hom (ctxD_CBN G) (tyD_CBN tbool).
Variable cbn_if_clause :
  forall (G : ppl_ctx Ar) (t : ppl_type Ar)
         (e : scones_hom (ctxD_CBN G) (tyD_CBN tbool))
         (M N : scones_hom (ctxD_CBN G) (tyD_CBN t)),
    scones_hom (ctxD_CBN G) (tyD_CBN t).

Local Notation tR' := (tR R_obj).
Local Notation eD'CBNa' :=
  (@eD_CBN_full_arith R Ar R_obj R_carrier_eq R_carrier_meas
     R_to_carrier_meas cbn_true_clause cbn_false_clause
     cbn_bernoulli_clause cbn_if_clause).

(** The CBN body of [ex_rl_lam]: [# "m" * # "x" + # "b"], in context
    [("x", tR') :: ("b", tR') :: ("m", tR') :: nil].

    Under the arith pipeline, the body computes pointwise to
    [add_FMeas (mul_FMeas m x) b] for any unit-ball environment
    [(((g, m), b), x)] (here [g : Stop Ar = ctxD_CBN nil]). *)
Lemma ex_rl_lam_arith_pointwise
    (env : sprod (sprod (sprod (Stop Ar)
                               (FMeas R_obj))
                        (FMeas R_obj))
                 (FMeas R_obj))
    (Henv : (cone_norm env <= 1)%R) :
  sc_fun (eD'CBNa' (G := [:: ("x"%string, tR'); ("b"%string, tR');
                          ("m"%string, tR')]) (t := tR')
            [# "m" * # "x" + # "b"]) env =
  add_FMeas R_carrier_eq R_carrier_meas R_to_carrier_meas
    (mul_FMeas R_carrier_eq R_carrier_meas R_to_carrier_meas
       (sc_fun (eD'CBNa' (G := [:: ("x"%string, tR'); ("b"%string, tR');
                              ("m"%string, tR')]) (t := tR') [# "m"]) env)
       (sc_fun (eD'CBNa' (G := [:: ("x"%string, tR'); ("b"%string, tR');
                              ("m"%string, tR')]) (t := tR') [# "x"]) env))
    (sc_fun (eD'CBNa' (G := [:: ("x"%string, tR'); ("b"%string, tR');
                           ("m"%string, tR')]) (t := tR') [# "b"]) env).
Proof.
rewrite (@cbn_add_clause_arith_E R Ar R_obj R_carrier_eq R_carrier_meas
          R_to_carrier_meas [:: tR'; tR'; tR'] _ _ _ Henv).
by rewrite (@cbn_mul_clause_arith_E R Ar R_obj R_carrier_eq R_carrier_meas
          R_to_carrier_meas [:: tR'; tR'; tR'] _ _ _ Henv).
Qed.

End ExRlLamArithPointwise.

Arguments ex_rl_lam_arith_pointwise {R Ar R_obj}
  R_carrier_eq R_carrier_meas R_to_carrier_meas
  cbn_true_clause cbn_false_clause cbn_bernoulli_clause cbn_if_clause
  env.
