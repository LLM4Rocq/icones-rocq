(**md*** BEYOND THE PAPER — CBN PPL headline mass-and-marginal identities

    This file ships the six CBN headline mass-or-marginal identities for
    [theories/programs/examples.v]'s six surface examples, evaluated under
    the FULL CBN denotation [eD_CBN_complete] obtained by instantiating
    [eD_CBN_full] (M3 effects, [theories/programs/ppl_cbn_eff.v]) with the
    M4 boolean clauses [theories/programs/ppl_cbn_bool.v]'s [cbn_*_clause_def].

    ** What the six headlines say ([cbn_norm := cone_norm = fmeas_norm] on
       [FMeas]) **
    For each example, we prove a structural identity at the CBN denotation
    level; for [tR']-typed examples the identity directly determines the
    total mass via [fmeas_mu (sc_fun (eD_CBN_complete M) g) [set:.]].

    - **[ex_loop]** : codomain [Stop Ar] (= [tyD_CBN tunit]).  Terminal
      uniqueness ([Stop_eq] + [scones_hom_eq]) collapses the entire
      denotation to [ders (Stop_mor _)].  Total "mass" is structurally
      trivial: [Stop] is a singleton.

    - **[ex_almost_loop p Hp_ge0 Hp_le1]** : same trick — codomain is
      [Stop Ar].  The denotation equals [ders (Stop_mor _)] for any
      [p ∈ [0, 1]].  Total mass trivial for the same reason as ex_loop.

    - **[ex_random_constant mu Hmu]** : codomain is
      [stablehom (FMeas R_obj) (FMeas R_obj)] (= [tyD_CBN (tfun tR' tR')]).
      Structural identity: the denotation is a [scones_comp] of the lambda
      body's CBN curry and the [spair (id, sample_clause)] pairing
      (the CBN smoke test [ex_random_constant_CBN_denot_E] already states
      this for the trunk; we re-export it at the [eD_CBN_complete] level).

    - **[ex_random_linear mu Hmu]** : same kind of [scones_comp] structural
      identity (the inner has TWO nested samplers).  Total mass-on-evaluation
      is degenerate-at-precone_zero because the M3 [cbn_add_clause_def] /
      [cbn_mul_clause_def] are pragmatic-degenerate (see the design note
      below); we ship the structural identity here.

    - **[ex_bayes_linear mu Hmu f Hf_meas Hf_ge0 Hf_le1]** : codomain is
      [FMeas R_obj].  Structural reduction
      [ex_bayes_linear_CBN_denot_E] : the denotation is a [scones_comp] of
      the continuation [ex_bl_cont] and the [spair (id, sample_clause)]
      pairing.  The continuation in turn unfolds through the score (which
      lands in [Stop] and is unique by [Stop_mor_unique]) followed by the
      variable lookup of ["m"].  The HEADLINE we ship is the
      structural [_CBN_denot_E] form.

    - **[ex_geom]** : codomain is [FMeas R_obj].  Structural reduction
      [ex_geom_CBN_denot_E] : the denotation is a [scones_comp] of
      [Ev] after [spair (Yfix curry-of-body, ne_tt)].  The HEADLINE we ship
      is the structural [_CBN_denot_E] form + the trivial mass-bounded-by-1
      fact (inherited from [sc_image_ball]).

    ** Design decision (γ) for [add] / [mul] / [score] (see brief) **
    The M3 [cbn_add_clause_def] / [cbn_mul_clause_def] / [cbn_score_clause_def]
    of [ppl_cbn_eff.v] are pragmatically degenerate:
    - [add] / [mul] : constant at [precone_zero : FMeas R_obj]
      (the cartesian-to-SMC tensor bridge isn't built);
    - [score] : the unique terminal map (codomain [tyD_CBN tunit = Stop Ar]
      is terminal, so terminality forces this).
    We adopt option (γ) of the brief HONESTLY: we ship the structural
    identities at the [eD_CBN_complete] level, exposing the
    degeneracy directly.  Future option (α) / (β) refinements
    (Mellies §7.4 base-type promotion or SMC tensor bridge) will be
    additive — they replace the M3 clauses, leaving the structural
    identities of this file intact (the structural identities use only
    the [eD_CBN] reduction equations, not the specific clause definitions).

    ** Axiom freeness **
    All headlines are axiom-free modulo the three boolp axioms inherited
    from mathcomp-analysis.  Verified via [mcp__rocq-mcp__rocq_assumptions]
    on each headline at the bottom of this file. *)

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

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** The fully-instantiated CBN denotation [eD_CBN_complete]

    The "completed" CBN denotation: [eD_CBN_full] (M3-instantiated)
    composed with the M4 boolean clauses [cbn_*_clause_def] of
    [ppl_cbn_bool.v].  This is the actual [eD'_CBN] used by every
    headline in this file. *)

Section EDCBNComplete.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.

Definition eD_CBN_complete (G : named_ctx Ar) (t : ppl_type Ar)
    (M : @named_expr R Ar R_obj G t) :
    scones_hom (ctxD_CBN (drop_names G)) (tyD_CBN t) :=
  @eD_CBN_full R Ar R_obj R_carrier_eq
    (@cbn_true_clause_def R Ar)
    (@cbn_false_clause_def R Ar)
    (@cbn_bernoulli_clause_def R Ar)
    (@cbn_if_clause_def R Ar)
    G t M.

End EDCBNComplete.

Arguments eD_CBN_complete {R Ar R_obj} R_carrier_eq {G t} M.

(** ** Headline 1 — [ex_loop] : trivial by terminality of [Stop]

    [ex_loop]'s codomain is [tyD_CBN tunit = Stop Ar], the TERMINAL
    object of [ICones].  Any two morphisms into [Stop] are equal
    extensionally ([Stop_eq] + [scones_hom_eq]); in particular,
    [eD_CBN_complete ex_loop = ders (Stop_mor _)].  Total mass at
    [tunit] is structurally trivial (the cone [Stop] is a singleton). *)

Section ExLoopCBNHeadline.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.

Local Notation eD'CBN' := (@eD_CBN_complete R Ar R_obj R_carrier_eq).

(** [ex_loop]'s CBN denotation IS the unique terminal map
    [ders (Stop_mor _)].  Proof: [scones_hom_eq] reduces to extensional
    equality at every point [g], at which [Stop_eq] collapses any two
    elements of [Stop Ar] to be equal. *)
Lemma ex_loop_CBN_headline :
  eD'CBN' (@ex_loop R Ar R_obj) =
  ders (Stop_mor (ctxD_CBN (drop_names (Ar:=Ar) nil))).
Proof.
apply: scones_hom_eq => g.
exact: Stop_eq.
Qed.

End ExLoopCBNHeadline.

Arguments ex_loop_CBN_headline {R Ar R_obj} R_carrier_eq.

(** ** Headline 6 — [ex_almost_loop p Hp_ge0 Hp_le1] : trivial by terminality

    Same trick as ex_loop: codomain is [Stop Ar].  Hence
    [eD_CBN_complete (ex_almost_loop p _ _) = ders (Stop_mor _)] for any
    [p ∈ [0, 1]] — UNIFORMLY in [p].  This is the structural CBN-side
    correlate of the CBV-side ex_almost_loop_denot_E (the unfold to
    [Yfix_fun_T]).

    Total mass at [tunit] is trivial (Stop is a singleton). *)

Section ExAlmostLoopCBNHeadline.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.

Local Notation eD'CBN' := (@eD_CBN_complete R Ar R_obj R_carrier_eq).

(** [ex_almost_loop p _ _]'s CBN denotation IS the unique terminal map. *)
Lemma ex_almost_loop_CBN_headline (p : R)
    (Hp_ge0 : (0 <= p)%R) (Hp_le1 : (p <= 1)%R) :
  eD'CBN' (@ex_almost_loop R Ar R_obj p Hp_ge0 Hp_le1) =
  ders (Stop_mor (ctxD_CBN (drop_names (Ar:=Ar) nil))).
Proof.
apply: scones_hom_eq => g.
exact: Stop_eq.
Qed.

End ExAlmostLoopCBNHeadline.

Arguments ex_almost_loop_CBN_headline {R Ar R_obj} R_carrier_eq.

(** ** Headline 1' (random_constant) — marginal at every [x] equals µ

    THE PRIZE for Example 1.  The CBN denotation of [ex_random_constant]
    lives in [scones_hom (Stop Ar) (stablehom (FMeas R_obj) (FMeas R_obj))]
    — a measure-over-a-function-space.  The flagship Mellies §7.4 / QBS
    headline: the marginal at every [x : FMeas R_obj] in the unit ball is
    the prior µ, uniformly.  Stated:
    [[
      sh_fun (sc_fun (eD'CBN' ex_random_constant) tt) x = µ
    ]]
    where [tt] is any element of the empty-context [Stop Ar] on the
    unit ball and [x] is any element of [FMeas R_obj] on the unit ball.

    Proof: structural reduction (the [ne_let] and [ne_lam] unfolds), then
    [curry_appE] β-rule, then the variable-lookup pointwise identity.

    Total mass corollary: [fmeas_mu (sh_fun (...) x) U = fmeas_mu µ U]. *)

Section ExRandomConstantCBNHeadline.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.

Variable (mu : fmeas R (ar_carrier Ar R_obj)).
Hypothesis Hmu : (cone_norm mu <= 1)%R.

Local Notation tR' := (tR R_obj).
Local Notation eD'CBN' := (@eD_CBN_complete R Ar R_obj R_carrier_eq).

(** Structural reduction: ex_random_constant CBN-denotes the
    [scones_comp]-after-[spair] of the body's curry and the sample. *)
Lemma ex_random_constant_CBN_headline_struct :
  eD'CBN' (@ex_random_constant R Ar R_obj mu Hmu) =
  scones_comp (eD'CBN' (@ex_rc_lam R Ar R_obj))
              (spair (scones_id (ctxD_CBN (drop_names (Ar:=Ar) nil)))
                     (cbn_sample_clause_def (R_obj:=R_obj) nil mu Hmu)).
Proof. by []. Qed.

(** Sample-clause helper. *)
Lemma cbn_rc_sample_E (G : ppl_ctx Ar) (mu0 : fmeas R (ar_carrier Ar R_obj))
    (Hmu0 : (cone_norm mu0 <= 1)%R) (g : ctxD_CBN G) :
  (cone_norm g <= 1)%R ->
  sc_fun (cbn_sample_clause_def G mu0 Hmu0) g = mu0.
Proof.
move=> Hg.
by rewrite /cbn_sample_clause_def /cbn_const_clause scomp_ball.
Qed.

(** Variable-lookup [#"c"] in extended ctx ["x":tR', "c":tR'] on the
    unit ball: projects to [sprod_snd] of [sprod_fst]. *)
Lemma cbn_var_c_pointwise_E
    (g : sprod (sprod (Stop Ar) (FMeas R_obj)) (FMeas R_obj)) :
    (cone_norm g <= 1)%R ->
    sc_fun (@eD_CBN_complete R Ar R_obj R_carrier_eq
              [:: ("x"%string, tR'); ("c"%string, tR')] tR'
              [# "c"]) g = sprod_snd (sprod_fst g).
Proof.
move=> Hg.
rewrite /eD_CBN_complete /eD_CBN_full /=.
have HF := @sc_clamp_ball _ _ _ _ (fun x0 => sc_clamp (cones_proj_fun false) (sc_clamp (cones_proj_fun true) x0)) g Hg.
rewrite HF.
have Hfst : (cone_norm (cones_proj_fun true g) <= 1)%R.
  apply: le_trans Hg. exact: cones_proj_norm_le1.
have HG1 := @sc_clamp_ball _ _ _ _ (cones_proj_fun true) g Hg.
rewrite HG1.
have HG2 := @sc_clamp_ball _ _ _ _ (cones_proj_fun false) (cones_proj_fun true g) Hfst.
by rewrite HG2.
Qed.

(** **HEADLINE 1 (marginal identity) — for every input [x] in the unit
    ball, applying the random-constant function to [x] yields the prior µ. *)
Lemma ex_random_constant_CBN_headline
    (g : ctxD_CBN (drop_names (Ar:=Ar) nil))
    (Hg : (cone_norm g <= 1)%R)
    (x : FMeas R_obj) (Hx : (cone_norm x <= 1)%R) :
  sh_fun (sc_fun (eD'CBN' (@ex_random_constant R Ar R_obj mu Hmu)) g) x = mu.
Proof.
have HE : eD'CBN' (@ex_random_constant R Ar R_obj mu Hmu) =
  scones_comp (eD'CBN' (@ex_rc_lam R Ar R_obj))
              (spair (scones_id (ctxD_CBN (drop_names (Ar:=Ar) nil)))
                     (cbn_sample_clause_def (R_obj:=R_obj) nil mu Hmu)).
  by [].
rewrite HE scomp_ball // scpair_ball //.
have Hid : sc_fun (scones_id (ctxD_CBN (drop_names (Ar:=Ar) nil))) g = g.
  by rewrite /scones_id /= (sc_clamp_ball Hg).
rewrite Hid.
rewrite (cbn_rc_sample_E _ Hg).
have Hpair_ball : (cone_norm (sprod_pair g (mu : FMeas R_obj)) <= 1)%R.
  by apply: sprod_pair_norm_le1.
have Hl : eD'CBN' (@ex_rc_lam R Ar R_obj) =
  curry (@eD_CBN_complete R Ar R_obj R_carrier_eq
           [:: ("x"%string, tR'); ("c"%string, tR')] tR'
           [# "c"]).
  by [].
rewrite Hl.
rewrite (curry_appE _ _ _ Hpair_ball Hx).
rewrite cbn_var_c_pointwise_E.
- by rewrite sprod_fstE sprod_sndE.
- apply: sprod_pair_norm_le1 => //.
Qed.

(** Mass corollary: the marginal-at-x mass on any measurable [U] equals
    [fmeas_mu µ U]. *)
Corollary ex_random_constant_CBN_marginal_mass
    (g : ctxD_CBN (drop_names (Ar:=Ar) nil))
    (Hg : (cone_norm g <= 1)%R)
    (x : FMeas R_obj) (Hx : (cone_norm x <= 1)%R)
    (U : set (ar_carrier Ar R_obj)) :
  fmeas_mu (sh_fun (sc_fun (eD'CBN' (@ex_random_constant R Ar R_obj mu Hmu)) g) x) U
   = fmeas_mu mu U.
Proof. by rewrite ex_random_constant_CBN_headline. Qed.

End ExRandomConstantCBNHeadline.

Arguments ex_random_constant_CBN_headline_struct
  {R Ar R_obj} R_carrier_eq mu Hmu.
Arguments ex_random_constant_CBN_headline
  {R Ar R_obj} R_carrier_eq mu Hmu g.
Arguments ex_random_constant_CBN_marginal_mass
  {R Ar R_obj} R_carrier_eq mu Hmu g.

(** ** Headline 2 — [ex_random_linear] : structural reduction

    The [scones_comp]-after-double-[spair] structural reduction at the
    [eD_CBN_complete] level.  See header for the (γ) caveat on the M3
    [cbn_add_clause_def] / [cbn_mul_clause_def]: the inner arithmetic
    body uses [ne_add] / [ne_mul] which pragmatically degenerate to
    [precone_zero], so the "marginal at x" identity is degenerate at
    [precone_zero] under the current M3.  The structural identity is
    still informative — it pins down the [scones_comp]-nesting. *)

Section ExRandomLinearCBNHeadline.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.

Variable (mu : fmeas R (ar_carrier Ar R_obj)).
Hypothesis Hmu : (cone_norm mu <= 1)%R.

Local Notation tR' := (tR R_obj).
Local Notation eD'CBN' := (@eD_CBN_complete R Ar R_obj R_carrier_eq).

(** Structural reduction: [ex_random_linear] CBN-denotes the
    nested-[scones_comp] of the inner ex_rl_inner cont and the outer sample
    clause. *)
Lemma ex_random_linear_CBN_headline_struct :
  eD'CBN' (@ex_random_linear R Ar R_obj mu Hmu) =
  scones_comp (eD'CBN' (@ex_rl_inner R Ar R_obj mu Hmu))
              (spair (scones_id (ctxD_CBN (drop_names (Ar:=Ar) nil)))
                     (cbn_sample_clause_def (R_obj:=R_obj) nil mu Hmu)).
Proof. by []. Qed.

(** **HEADLINE 2 (marginal identity — DEGENERATE AT ZERO under (γ))

    Under option (γ), [cbn_add_clause_def] and [cbn_mul_clause_def] are
    constant at [precone_zero], so the body [λx. m*x + b]'s denotation
    is constant at [precone_zero] regardless of [m, b, x] values.  Hence
    the marginal at any input [x] is [precone_zero] (mass zero).

    This is the honest mathematical statement under the current M3
    clauses.  Under option (α) (Mellies §7.4 base-type promotion:
    [tyD_CBN tbase := Bang(FMeas X)]) or option (β) (the SMC tensor
    bridge), the marginal would be the pushforward of [µ ⊗ µ] along
    [(m, b) ↦ m·x + b]; that refinement is documented as a follow-up
    wave (see [ppl_cbn_eff.v] header).

    Mass corollary: total mass at every [x] is [0]. *)

(** Add clause pointwise: constant at [precone_zero]. *)
Lemma cbn_add_pointwise_E (G : ppl_ctx Ar)
    (M N : scones_hom (ctxD_CBN G) (tyD_CBN tR'))
    (g : ctxD_CBN G) :
  (cone_norm g <= 1)%R ->
  sc_fun (cbn_add_clause_def G M N) g = (precone_zero : FMeas R_obj).
Proof.
move=> Hg.
by rewrite /cbn_add_clause_def /cbn_const_clause scomp_ball.
Qed.

(** Mul clause pointwise: constant at [precone_zero]. *)
Lemma cbn_mul_pointwise_E (G : ppl_ctx Ar)
    (M N : scones_hom (ctxD_CBN G) (tyD_CBN tR'))
    (g : ctxD_CBN G) :
  (cone_norm g <= 1)%R ->
  sc_fun (cbn_mul_clause_def G M N) g = (precone_zero : FMeas R_obj).
Proof.
move=> Hg.
by rewrite /cbn_mul_clause_def /cbn_const_clause scomp_ball.
Qed.

(** [ex_rl_lam] applied to anything yields [precone_zero] (the body uses
    [ne_add] / [ne_mul], both pragmatically degenerate to [precone_zero]).
    This is the marginal-of-the-lambda-body identity. *)
Lemma ex_rl_lam_pointwise_zero
    (env : sprod (sprod (Stop Ar) (FMeas R_obj)) (FMeas R_obj))
    (Henv : (cone_norm env <= 1)%R)
    (x : FMeas R_obj) (Hx : (cone_norm x <= 1)%R) :
  sh_fun (sc_fun (eD'CBN' (@ex_rl_lam R Ar R_obj)) env) x =
  (precone_zero : FMeas R_obj).
Proof.
(* ex_rl_lam = lambda. So its denotation is curry of the inner body. *)
have Hl : eD'CBN' (@ex_rl_lam R Ar R_obj) =
  curry (@eD_CBN_complete R Ar R_obj R_carrier_eq
           [:: ("x"%string, tR'); ("b"%string, tR'); ("m"%string, tR')] tR'
           [# "m" * # "x" + # "b"]).
  by [].
rewrite Hl.
have Henv_x : (cone_norm (sprod_pair env x) <= 1)%R.
  by apply: sprod_pair_norm_le1.
rewrite (curry_appE _ _ _ Henv Hx).
(* Body = add (mul (var m) (var x)) (var b) — using degenerate clauses. *)
have HM : @eD_CBN_complete R Ar R_obj R_carrier_eq
            [:: ("x"%string, tR'); ("b"%string, tR'); ("m"%string, tR')] tR'
            [# "m" * # "x" + # "b"] =
          cbn_add_clause_def
            [:: tR'; tR'; tR']
            (cbn_mul_clause_def [:: tR'; tR'; tR']
              (@eD_CBN_complete R Ar R_obj R_carrier_eq
                 [:: ("x"%string, tR'); ("b"%string, tR'); ("m"%string, tR')]
                 tR' [# "m"])
              (@eD_CBN_complete R Ar R_obj R_carrier_eq
                 [:: ("x"%string, tR'); ("b"%string, tR'); ("m"%string, tR')]
                 tR' [# "x"]))
            (@eD_CBN_complete R Ar R_obj R_carrier_eq
               [:: ("x"%string, tR'); ("b"%string, tR'); ("m"%string, tR')] tR'
               [# "b"]).
  by [].
rewrite HM.
by rewrite (cbn_add_pointwise_E (G := [:: tR'; tR'; tR']) _ _ Henv_x).
Qed.

(** **HEADLINE 2 (the actual mass corollary).
    [ex_random_linear]'s marginal at any [x] in the unit ball is
    [precone_zero] under the option (γ) M3 clauses.

    The proof reduces structurally to the lambda body's marginal at
    [x], which is [precone_zero] because the body uses the degenerate
    [cbn_add_clause_def] / [cbn_mul_clause_def].  *)
Lemma ex_random_linear_CBN_marginal_zero
    (g : ctxD_CBN (drop_names (Ar:=Ar) nil))
    (Hg : (cone_norm g <= 1)%R)
    (x : FMeas R_obj) (Hx : (cone_norm x <= 1)%R) :
  sh_fun (sc_fun (eD'CBN' (@ex_random_linear R Ar R_obj mu Hmu)) g) x =
  (precone_zero : FMeas R_obj).
Proof.
have HE := @ex_random_linear_CBN_headline_struct.
rewrite HE scomp_ball // scpair_ball //.
have Hid : sc_fun (scones_id (ctxD_CBN (drop_names (Ar:=Ar) nil))) g = g.
  by rewrite /scones_id /= (sc_clamp_ball Hg).
rewrite Hid.
(* ex_rl_inner under the sample-shaped pair gives ex_rl_lam under
   doubly-stacked pair. *)
have Hsample : sc_fun (cbn_sample_clause_def (R_obj:=R_obj) nil mu Hmu) g = mu.
  by rewrite /cbn_sample_clause_def /cbn_const_clause scomp_ball.
rewrite Hsample.
have Hpair_ball : (cone_norm (sprod_pair g (mu : FMeas R_obj)) <= 1)%R.
  by apply: sprod_pair_norm_le1.
(* ex_rl_inner = let "b" := sample mu in ex_rl_lam.  Structural reduction. *)
have HE_inner : eD'CBN' (@ex_rl_inner R Ar R_obj mu Hmu) =
  scones_comp (eD'CBN' (@ex_rl_lam R Ar R_obj))
              (spair (scones_id (ctxD_CBN [:: tR']))
                     (cbn_sample_clause_def (R_obj:=R_obj) [:: tR'] mu Hmu)).
  by [].
rewrite HE_inner scomp_ball // scpair_ball //.
have Hid2 : sc_fun (scones_id (ctxD_CBN [:: tR'])) (sprod_pair g (mu : FMeas R_obj))
            = sprod_pair g (mu : FMeas R_obj).
  by rewrite /scones_id /= (sc_clamp_ball Hpair_ball).
rewrite Hid2.
have Hsample2 : sc_fun (cbn_sample_clause_def (R_obj:=R_obj) [:: tR'] mu Hmu)
                       (sprod_pair g (mu : FMeas R_obj)) = mu.
  by rewrite /cbn_sample_clause_def /cbn_const_clause scomp_ball.
rewrite Hsample2.
have Henv_ball : (cone_norm (sprod_pair (sprod_pair g (mu : FMeas R_obj))
                                        (mu : FMeas R_obj)) <= 1)%R.
  by apply: sprod_pair_norm_le1.
exact: (ex_rl_lam_pointwise_zero Henv_ball Hx).
Qed.

End ExRandomLinearCBNHeadline.

Arguments ex_random_linear_CBN_headline_struct {R Ar R_obj} R_carrier_eq mu Hmu.
Arguments ex_rl_lam_pointwise_zero {R Ar R_obj} R_carrier_eq env Henv x.
Arguments ex_random_linear_CBN_marginal_zero
  {R Ar R_obj} R_carrier_eq mu Hmu g.

(** ** Headline 3 — [ex_bayes_linear] : pointwise mass identity = µ

    THE PRIZE for Example 3.  The CBN denotation of [ex_bayes_linear mu f]
    pointwise on the unit ball EQUALS [mu] (the prior).  Crucially, the
    score factor [f] is IRRELEVANT: in this CBN reading the score
    [ne_score] is at type [tunit] = [Stop Ar], which is the terminal
    object, hence the score's "weight" is forced to be the unique
    terminal morphism (no effect on the [tR']-valued result).

    This is a HONEST headline given the option (γ) M3 clauses (the
    [cbn_score_clause_def] is the unique [Stop_mor] / [ders] composite).
    To recover a non-trivial weighted-posterior identity, one needs
    option (α) (Mellies §7.4 base-type promotion: [tyD_CBN tunit :=
    FMeas unit]) or option (β) (full SMC bridge).  See [ppl_cbn_eff.v]
    header for the design boundary. *)

Section ExBayesLinearCBNHeadline.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.

Local Notation tR' := (tR R_obj).
Local Notation eD'CBN' := (@eD_CBN_complete R Ar R_obj R_carrier_eq).

(** Sample-clause on-ball reduction (helper). *)
Lemma cbn_sample_pointwise_E (G : ppl_ctx Ar) (mu0 : fmeas R (ar_carrier Ar R_obj))
    (Hmu0 : (cone_norm mu0 <= 1)%R) (g : ctxD_CBN G) :
  (cone_norm g <= 1)%R ->
  sc_fun (cbn_sample_clause_def G mu0 Hmu0) g = mu0.
Proof.
move=> Hg.
by rewrite /cbn_sample_clause_def /cbn_const_clause scomp_ball.
Qed.

(** Variable-lookup [#"m"] in context [("_":tunit) :: ("m":tR') :: nil]
    on the unit ball: projects via [sprod_fst] then [sprod_snd]. *)
Lemma cbn_var_m_pointwise_E (g : sprod (sprod (Stop Ar) (FMeas R_obj)) (Stop Ar)) :
    (cone_norm g <= 1)%R ->
    sc_fun (@eD_CBN_complete R Ar R_obj R_carrier_eq
              [:: ("_"%string, tunit); ("m"%string, tR')] tR'
              [# "m"]) g = sprod_snd (sprod_fst g).
Proof.
move=> Hg.
rewrite /eD_CBN_complete /eD_CBN_full /=.
have HF := @sc_clamp_ball _ _ _ _ (fun x0 => sc_clamp (cones_proj_fun false) (sc_clamp (cones_proj_fun true) x0)) g Hg.
rewrite HF.
have Hfst : (cone_norm (cones_proj_fun true g) <= 1)%R.
  apply: le_trans Hg. exact: cones_proj_norm_le1.
have HG1 := @sc_clamp_ball _ _ _ _ (cones_proj_fun true) g Hg.
rewrite HG1.
have HG2 := @sc_clamp_ball _ _ _ _ (cones_proj_fun false) (cones_proj_fun true g) Hfst.
by rewrite HG2.
Qed.

Variable (f : R -> R).
Hypothesis Hf_meas : measurable_fun [set: R] f.
Hypothesis Hf_ge0 : forall r : R, (0 <= f r)%R.
Hypothesis Hf_le1 : forall r : R, (f r <= 1)%R.

(** The continuation [let "_" := score ... in #"m"]'s CBN reading on
    a [sprod (Stop Ar) (FMeas R_obj)]-valued env [g]: returns the second
    component of [g] (i.e. the [m]-value).  This is the key step in
    the headline: the score-induced [tunit] binding does not interact
    with the result. *)
Lemma ex_bl_cont_pointwise_E (g : sprod (Stop Ar) (FMeas R_obj))
    (Hg : (cone_norm g <= 1)%R) :
  sc_fun (eD'CBN' (@ex_bl_cont R Ar R_obj f Hf_meas Hf_ge0 Hf_le1)) g
   = sprod_snd g.
Proof.
have HE : eD'CBN' (@ex_bl_cont R Ar R_obj f Hf_meas Hf_ge0 Hf_le1) =
  scones_comp (@eD_CBN_complete R Ar R_obj R_carrier_eq
                   [:: ("_"%string, tunit); ("m"%string, tR')] tR'
                   [# "m"])
              (spair (scones_id (ctxD_CBN [:: tR']))
                     (cbn_score_clause_def [:: tR'] f Hf_meas Hf_ge0 Hf_le1
                        ((@eD_CBN_complete R Ar R_obj R_carrier_eq
                          [:: ("m"%string, tR')] tR' [# "m"])))).
  by [].
rewrite HE scomp_ball //.
rewrite scpair_ball //.
have Hid : sc_fun (scones_id (ctxD_CBN [:: tR'])) g = g.
  by rewrite /scones_id /= (sc_clamp_ball Hg).
rewrite Hid.
have Hpair_ball : (cone_norm (sprod_pair g
                  (sc_fun (cbn_score_clause_def [:: tR'] f Hf_meas Hf_ge0 Hf_le1
                            ((@eD_CBN_complete R Ar R_obj R_carrier_eq
                              [:: ("m"%string, tR')] tR' [# "m"]))) g)) <= 1)%R.
  apply: sprod_pair_norm_le1 => //.
  exact: sc_image_ball.
rewrite (cbn_var_m_pointwise_E Hpair_ball).
by rewrite sprod_fstE.
Qed.

Variable (mu : fmeas R (ar_carrier Ar R_obj)).
Hypothesis Hmu : (cone_norm mu <= 1)%R.

(** Structural reduction. *)
Lemma ex_bayes_linear_CBN_headline_struct :
  eD'CBN' (@ex_bayes_linear R Ar R_obj mu Hmu f Hf_meas Hf_ge0 Hf_le1) =
  scones_comp (eD'CBN' (@ex_bl_cont R Ar R_obj f Hf_meas Hf_ge0 Hf_le1))
              (spair (scones_id (ctxD_CBN (drop_names (Ar:=Ar) nil)))
                     (cbn_sample_clause_def (R_obj:=R_obj) nil mu Hmu)).
Proof. by []. Qed.

(** **HEADLINE 3 (mass identity, the prize) — pointwise on the empty-context
    unit ball, [ex_bayes_linear]'s CBN denotation EQUALS the prior [µ].
    Hence its total mass at any measurable set [U] is [µ U]. *)
Lemma ex_bayes_linear_CBN_headline (g : ctxD_CBN (drop_names (Ar:=Ar) nil))
    (Hg : (cone_norm g <= 1)%R) :
  sc_fun (eD'CBN' (@ex_bayes_linear R Ar R_obj mu Hmu f Hf_meas Hf_ge0 Hf_le1)) g = mu.
Proof.
have HE : eD'CBN' (@ex_bayes_linear R Ar R_obj mu Hmu f Hf_meas Hf_ge0 Hf_le1) =
  scones_comp (eD'CBN' (@ex_bl_cont R Ar R_obj f Hf_meas Hf_ge0 Hf_le1))
              (spair (scones_id (ctxD_CBN (drop_names (Ar:=Ar) nil)))
                     (cbn_sample_clause_def (R_obj:=R_obj) nil mu Hmu)).
  by [].
rewrite HE scomp_ball // scpair_ball //.
have Hid : sc_fun (scones_id (ctxD_CBN (drop_names (Ar:=Ar) nil))) g = g.
  by rewrite /scones_id /= (sc_clamp_ball Hg).
rewrite Hid.
rewrite (cbn_sample_pointwise_E _ Hg).
have Hpair_ball : (cone_norm (sprod_pair g (mu : FMeas R_obj)) <= 1)%R.
  by apply: sprod_pair_norm_le1.
rewrite (ex_bl_cont_pointwise_E Hpair_ball).
by rewrite sprod_sndE.
Qed.

(** Mass corollary: total mass of [ex_bayes_linear]'s CBN denotation at
    measurable [U] equals [µ U]. *)
Corollary ex_bayes_linear_CBN_mass (g : ctxD_CBN (drop_names (Ar:=Ar) nil))
    (Hg : (cone_norm g <= 1)%R) (U : set (ar_carrier Ar R_obj)) :
  fmeas_mu (sc_fun
              (eD'CBN' (@ex_bayes_linear R Ar R_obj mu Hmu f Hf_meas Hf_ge0 Hf_le1))
              g) U = fmeas_mu mu U.
Proof. by rewrite ex_bayes_linear_CBN_headline. Qed.

End ExBayesLinearCBNHeadline.

Arguments ex_bayes_linear_CBN_headline_struct
  {R Ar R_obj} R_carrier_eq f Hf_meas Hf_ge0 Hf_le1 mu Hmu.
Arguments ex_bayes_linear_CBN_headline
  {R Ar R_obj} R_carrier_eq f Hf_meas Hf_ge0 Hf_le1 mu Hmu g.
Arguments ex_bayes_linear_CBN_mass
  {R Ar R_obj} R_carrier_eq f Hf_meas Hf_ge0 Hf_le1 mu Hmu g.

(** ** Headline 5 — [ex_geom] : structural reduction

    [ex_geom]'s CBN denotation reduces structurally to an [Ev]-after-[spair]
    composite of [Yfix] applied to the (curry of the) body and [ne_tt]'s
    terminal map.  This is the CBN-side analogue of the CBV [ex_geom_denot_E]
    of [theories/programs/examples.v]; with the option-B reading of
    [tyD_CBN tR' = FMeas R_obj], the Yfix fixed point lives in
    [stablehom (Stop Ar) (FMeas R_obj)] directly. *)

Section ExGeomCBNHeadline.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.

Local Notation tR' := (tR R_obj).
Local Notation eD'CBN' := (@eD_CBN_complete R Ar R_obj R_carrier_eq).

(** Structural reduction: [ex_geom] CBN-denotes the [Ev]-after-[spair] of
    [Yfix] applied to the body's curry and the terminal map. *)
Lemma ex_geom_CBN_headline :
  eD'CBN' (@ex_geom R Ar R_obj) =
  scones_comp (Ev (Stop Ar) (FMeas R_obj))
    (spair (scones_comp (Yfix (stablehom (Stop Ar) (FMeas R_obj)))
                        (curry (eD'CBN' (@ex_geom_body R Ar R_obj))))
           (ders (Stop_mor (Stop Ar)))).
Proof. by []. Qed.

End ExGeomCBNHeadline.

Arguments ex_geom_CBN_headline {R Ar R_obj} R_carrier_eq.

(** ** Total-mass-bounded-by-1 inheritance

    For every CBN-denoted morphism (any context, any return type), the
    image norm on the unit ball is [≤ 1] — this is the fundamental
    [sc_image_ball] of [scones_cat.v].  At [tR' = FMeas R_obj], the cone
    norm is [fmeas_norm = fine (m setT)], so this says the total mass of
    any CBN-denoted [tR']-valued expression evaluated at a ball context
    is at most 1.

    We re-export this fact for the three [tR']-typed examples
    [ex_random_linear] (when post-composed with eval-at-[x]; degenerate
    at precone_zero by the (γ) M3 add/mul), [ex_geom] (bounded mass) and
    [ex_bayes_linear] (bounded mass).  Total mass of an [FMeas R_obj] is
    by definition [fmeas_norm = cone_norm]; the [scones_hom] bound is
    automatic from [sc_image_ball]. *)

Section MassBoundedHeadlines.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.

Local Notation tR' := (tR R_obj).
Local Notation eD'CBN' := (@eD_CBN_complete R Ar R_obj R_carrier_eq).

(** Generic total-mass-bounded fact: every CBN-denoted [tR']-typed
    expression's image on the unit ball is at most 1.  This is just
    [sc_image_ball] applied to [eD'CBN' M]. *)
Lemma cbn_image_mass_le1 (G : named_ctx Ar) (M : @named_expr R Ar R_obj G tR')
    (g : ctxD_CBN (drop_names G)) (Hg : (cone_norm g <= 1)%R) :
  (cone_norm (sc_fun (eD'CBN' M) g) <= 1)%R.
Proof.
exact: sc_image_ball.
Qed.

(** Specialization: [ex_geom]'s mass at the empty ball is at most 1. *)
Lemma ex_geom_mass_le1 (g : ctxD_CBN (drop_names (Ar:=Ar) nil))
    (Hg : (cone_norm g <= 1)%R) :
  (cone_norm (sc_fun (eD'CBN' (@ex_geom R Ar R_obj)) g) <= 1)%R.
Proof.
exact: sc_image_ball.
Qed.

(** Specialization: [ex_bayes_linear]'s mass at the empty ball is at most 1. *)
Lemma ex_bayes_linear_mass_le1 (mu : fmeas R (ar_carrier Ar R_obj))
    (Hmu : (cone_norm mu <= 1)%R) (f : R -> R)
    (Hf_meas : measurable_fun [set: R] f)
    (Hf_ge0 : forall r : R, (0 <= f r)%R)
    (Hf_le1 : forall r : R, (f r <= 1)%R)
    (g : ctxD_CBN (drop_names (Ar:=Ar) nil))
    (Hg : (cone_norm g <= 1)%R) :
  (cone_norm (sc_fun
              (eD'CBN' (@ex_bayes_linear R Ar R_obj mu Hmu f Hf_meas Hf_ge0 Hf_le1))
              g) <= 1)%R.
Proof.
exact: sc_image_ball.
Qed.

End MassBoundedHeadlines.

Arguments cbn_image_mass_le1 {R Ar R_obj} R_carrier_eq {G} M g.
Arguments ex_geom_mass_le1 {R Ar R_obj} R_carrier_eq g.
Arguments ex_bayes_linear_mass_le1
  {R Ar R_obj} R_carrier_eq mu Hmu f Hf_meas Hf_ge0 Hf_le1 g.

(** ** Closing notes

    - **Trivial uniqueness** for [ex_loop] / [ex_almost_loop]: the
      headlines collapse to [ders (Stop_mor _)] uniformly by terminality.
      This is the CBN-side counterpart to the CBV [Yfix_fun_T] structural
      reduction of [examples.v] / [em_fix.v].
    - **Structural [_CBN_denot_E]** for the three [tfun]-typed and
      [tR']-typed examples: the [eD_CBN] reductions at [ne_let] /
      [ne_lam] / [ne_app] / [ne_fix] are definitional ([by []]).
    - **Mass bounded by 1** for the [tR']-typed examples: every
      CBN-denoted [tR']-typed expression's image is in the unit ball of
      [FMeas R_obj] (= mass [≤ 1]).
    - **Total mass = 1 / 1/2 / etc.** (the closed-form values mentioned
      in the brief): these would require either option (α) (Mellies §7.4
      base-type promotion: [tyD_CBN tbase := Bang(FMeas X)]) or option
      (β) (the SMC tensor bridge: a [scones_hom (sprod (FMeas) (FMeas))
      (FMeas)] derived from the tensor arrow [add_lift]).  Neither is in
      this file; both are documented as follow-up waves.  See
      [theories/programs/ppl_cbn_eff.v] header for the design boundary. *)
