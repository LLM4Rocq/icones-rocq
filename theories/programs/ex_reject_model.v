(**md**************************************************************************)
(** * Rejection sampling over ANY model — the higher-order combinator

    BEYOND THE PAPER.  This file is NOT part of the Ehrhard-Geoffroy
    2025 formalization (paper §2-§9).  It generalises the
    rejection-sampling headline of [ex_reject_headline.v] from the one
    hard-coded program to a higher-order COMBINATOR over an arbitrary
    probabilistic MODEL: the surface program
    [theories/programs/examples.v::ex_reject_comb]
    [[
       fix rs = λ m. λ a.
         let x = m a in
         if Bernoulli (Meas{f} x) then x else rs m a
    ]]
    of type [(ta → tR) → (ta → tR)], for an ARBITRARY input type [ta].
    A model is any function value [m : ta → tR] — itself a
    lambda-written probabilistic program, free to contain samples,
    scores, recursion, … — and [ex_reject_comb m a] runs the model at
    the input [a], accepts the produced value [x] with probability
    [f x], and recurses (at the same model and input) on rejection.

    ** The semantic set-up

    The theorems quantify over the model VALUE and the input VALUE:
    - the model argument is the promoted point [g!] of an arbitrary
      unit-ball linear map [g : U⟦ta⟧ ⊸ FMeas] — EVERY lambda-written
      model denotes such a point ([eD_lam_E] + [adj_psi_at_setlike]:
      the λ-clause promotes the curried body at the closed
      environment), so no generality is lost;
    - the input argument is an arbitrary setlike unit-ball point
      [a₀ : U⟦ta⟧] (at [ta = tR] these are exactly the Diracs; at
      [ta = tunit] the unit point).

    Writing [ν_M := g(a₀) : FMeas] for the model's output
    SUB-distribution at the input (the model may itself diverge:
    sub-probability honest), [m₀ := ν_M(setT)] for its total mass,
    [If := ∫ f dν_M], [IUf U := ∫_U f dν_M], and [ν] for the
    denotation of [(reject_comb m) a], the results are:

    - [reject_model_master] : [(1 - m₀ + If) · ν(U) = IUf U]
      — unconditionally (graceful in the degenerate corner
      [m₀ = 1 ∧ If = 0] where the loop never terminates);
    - [reject_model_is_normalised] : [0 < 1 - m₀ + If] implies
      [ν(U) = IUf U / (1 - m₀ + If)] — the normalised distribution,
      with the sub-probability-honest normaliser: a run is REJECTED
      with probability [m₀ - If] (the model terminated AND the coin
      said no), so the success-per-trial mass is [1 - (m₀ - If)];
    - [reject_model_mass] : the total-mass identity
      [ν(setT) = If / (1 - m₀ + If)];
    - [reject_model_mass_one] : for a PROBABILITY model ([m₀ = 1])
      with positive acceptance ([0 < If]), [ν(setT) = 1] — the
      sampler terminates almost surely;
    - [reject_model_zero] : [f ≡ 0] implies [ν = 0] — certain
      rejection diverges, whatever the model does.

    ** The instance: the headline program is the simplest model

    At [ta := tunit] and the sampler model [λ_. sample µ]
    ([examples.v::ex_sampler]) with a unit-mass prior, the combinator
    REPRODUCES the [ex_reject] headline:
    - [ex_reject_comb_sampler_E] : the combinator applied to the
      sampler model and the unit input denotes THE SAME measure as
      [ex_reject µ f] — proved by equating the two Kleene chains'
      per-iterate masses (both satisfy the cascade
      [x_{n+1} = ∫_U f dµ + (1 - ∫f dµ)·x_n]) and passing to the
      suprema;
    - [ex_reject_comb_sampler_master] : the old master identity
      [∫f dµ · ν(U) = ∫_U f dµ], re-derived through the bridge.
    (The old [ex_reject] program abstracts over an acceptance
    continuation instead of a model — a different surface shape — so
    its own theorems in [ex_reject_headline.v] stand unchanged; the
    bridge identifies the DENOTATIONS.)

    ** Proof skeleton

    The reduction chain of [ex_reject_headline.v] §2, parameterised:
    1. [reject_comb_val_E] — the closed fixpoint program denotes the
       promoted fixpoint VALUE; the two [der ∘ prom] redexes of the
       applications to [g!] and [a₀] cancel BEFORE any continuity
       argument.
    2. [reject_model_sup_E] — [ν] is the [cone_sup_ball] of the
       per-iterate measures [ν_n]: evaluation at [g!], the counit
       [der], and evaluation at [a₀] all commute with the Kleene
       supremum ([linhom_fun_sup_ball] twice + [Lfun_sup_ball], the
       ω-continuity field of the [Cones] morphism class).
    3. [reject_model_iter_S] — the Kleene step is the inner let-if
       body at the extended setlike environment
       [((1 ⊗ rs_n!) ⊗ g!) ⊗ a₀].
    4. [reject_model_if_at_dirac] — at the Dirac extension the branch
       dispatch computes: THEN gives the accepted sample [δ_r], ELSE
       is the recursive call AT THE SAME MODEL AND INPUT — exactly the
       previous iterate [ν_n].
    5. [reject_model_iter_mass] — the mass recurrence
       [ν_{n+1}(U) = IUf U + (m₀ - If)·ν_n(U)] via the GENERAL let-law
       [eD_let_mu_E] of [let_sample_law.v] (the let now binds the
       model application [m @ a], whose denotation at the environment
       is [ν_M] — [reject_model_app_E]).
    6. The theorems, via the affine cascade [a := IUf U],
       [q := m₀ - If] ([affine_cascade.v]): [q + If = m₀ ≤ 1], and
       [q = 1] exactly in the degenerate never-terminating corner
       [m₀ = 1 ∧ If = 0] covered by [affine_iter_deg_eq0]-style
       induction.

    ** The [condition] combinator and the equivalence

    §4 adds the Pyro-style soft conditioning operator
    [examples.v::ex_condition_comb] — [condition M f] runs the model,
    scores the produced value by the density [f], and returns it —
    with its conditioning law [condition_model_E]: the conditioned
    model's output at the input is the REWEIGHTED measure
    [U ↦ ∫_U f dν_M] (the generalisation of
    [cbv_marginals.v::ex_score_posterior_cbv_E] from [sample µ] to an
    arbitrary model).  §5 then states the equivalence in readable
    form ([reject_normalises_condition]): rejection sampling computes
    the conditioned model's normalised distribution,
    [[
       Z · ⟦ reject M f ⟧ U = ⟦ condition M f ⟧ U,
       Z := 1 - ν_M(setT) + ∫ f dν_M
    ]]
    with the division form [reject_prog_computes_condition] and, for
    probability models, [reject_normalises_condition_prob]: the
    normaliser IS the conditioned model's total mass (the evidence).

    See also: [theories/programs/ex_reject_headline.v] (the original
    headline and the §1 setlike/sup kit reused here),
    [theories/programs/infra/let_sample_law.v] (the general let-law),
    [theories/programs/infra/cbv_marginals.v] (the score-discard kit
    [em_proj1_mor_unitE] / [Lfun_scaleE] reused by §4),
    [theories/programs/infra/em_fix_value.v] (the value-fixpoint
    combinator), [theories/programs/infra/affine_cascade.v].

    Author: Guillaume Baudart <guillaume.baudart@inria.fr>. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals constructive_ereal.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import ereal.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import measure dirac_measure numfun.
From mathcomp.analysis Require Import lebesgue_integral_definition.
From mathcomp.analysis Require Import lebesgue_integral_nonneg.
From mathcomp.analysis Require Import lebesgue_integral_monotone_convergence.
From mathcomp.analysis Require Import topology normedtype sequences.
Import numFieldTopology.Exports.

From Stdlib Require Import Strings.String.

Require Import Icones.cones.precone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.cone.
Require Import Icones.cones.cone_cat.
Require Import Icones.programs.infra.bool_cone.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.mcones.path.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_integral.
Require Import Icones.icones.examples_icone.
Require Import Icones.icones.icone_cat.
Require Import Icones.stable.scones_cat.
Require Import Icones.stable.scones_ccc.
Require Import Icones.homs.icones_iso.
Require Import Icones.homs.linhom.
Require Import Icones.homs.bilin.
Require Import Icones.homs.tensor.
Require Import Icones.homs.tensor_construct.
Require Import Icones.homs.smcc.
Require Import Icones.homs.exp_adjunction.
Require Import Icones.homs.bang.
Require Import Icones.homs.seely_defs.
Require Import Icones.homs.seely.
Require Import Icones.homs.tensor_hom_iso.
Require Import Icones.programs.infra.bool_case_hom.
Require Import Icones.homs.coalgebra.
Require Import Icones.programs.infra.bool_cone_coalg.
Require Import Icones.homs.fmeas_lax.
Require Import Icones.homs.em_cat.
Require Import Icones.homs.em_seely_comonoid.
Require Import Icones.homs.em_cartesian.
Require Import Icones.programs.infra.cbv_adjunction.
Require Import Icones.programs.ppl.
Require Import Icones.programs.infra.em_fix.
Require Import Icones.programs.infra.em_fix_value.
Require Import Icones.programs.ppl_cbv.
Require Import Icones.programs.infra.cbv_anchors.
Require Import Icones.programs.infra.cbv_fix_unfold.
Require Import Icones.programs.infra.let_sample_law.
Require Import Icones.programs.infra.affine_cascade.
Require Import Icones.programs.examples.
Require Import Icones.programs.ex_reject_headline.
Require Import Icones.programs.infra.cbv_marginals.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Opaque tensor_mor tensor_assoc tensor_lunit tensor_runit tensor_braid
       ptensor tau Seely2.
Local Opaque dig der prom bang_fmap d_bang e_bang unit_cofree_str Coalg
       tens_cofree_str m_bang.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** §1 — Kit: [Lfun] is monotone and ω-continuous

    Every [ICones] morphism is, through its underlying [Cones]
    morphism, linear (hence monotone) and ω-continuous BY DEFINITION
    ([cone_cat.v::cones_hom]); we expose the two pointwise readings
    the sup-commutation chain of step 2 consumes (the headline only
    ever evaluated linhom-cone sups at points; here the counit [der]
    must additionally be pushed under a sup of POINTS of [!B]). *)

Section LfunKit.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

(** [Lfun] of an [ICones] morphism is monotone (linearity). *)
Lemma Lfun_le (B C : ICone.type Ar) (h : icones_hom Ar B C) (x y : B) :
  precone_le x y -> precone_le (Lfun h x) (Lfun h y).
Proof.
exact: (linear_increasing
          (cones_hom_linear (mcones_hom_cones (icones_hom_mcones h)))).
Qed.

(** [Lfun] of an [ICones] morphism commutes with ball-sups of chains
    (the [cones_hom_continuous] field, with witness irrelevance). *)
Lemma Lfun_sup_ball (B C : ICone.type Ar) (h : icones_hom Ar B C)
    (u : nat -> B)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, cone_norm (u n) <= 1)
    (fuch : forall n, precone_le (Lfun h (u n)) (Lfun h (u n.+1)))
    (fub1 : forall n, cone_norm (Lfun h (u n)) <= 1) :
  Lfun h (cone_sup_ball u uch ub1) =
  cone_sup_ball (fun n => Lfun h (u n)) fuch fub1.
Proof.
rewrite (@cones_hom_continuous _ _ _
           (mcones_hom_cones (icones_hom_mcones h)) u uch ub1 fuch fub1).
exact: cone_sup_ball_irr.
Qed.

End LfunKit.

Arguments Lfun_le {R Ar B C} h {x y}.
Arguments Lfun_sup_ball {R Ar B C} h {u} uch ub1 fuch fub1.

(** ** §2 — The combinator reduction chain *)

Section RejectModel.
Variables (R : realType) (Ar : MeasSubcat R).
(* Reparameterized over the bundled [probObj]. *)
Variable (P : probObj Ar).
Local Notation R_obj := (po_robj P).
Local Notation R_carrier_eq := (po_robj_eq P).
Local Notation R_carrier_meas := (po_robj_meas P).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

(** The model's input type: an ARBITRARY PPL type. *)
Variable (ta : ppl_type Ar).

(** The soft acceptance predicate: a BUNDLED [[0,1]]-valued test function;
    its projections are exposed under their historical names. *)
Variable (f : testfn R).
Local Notation Hf_meas := (test_meas f).
Local Notation Hf_ge0 := (test_ge0 f).
Local Notation Hf_le1 := (test_le1 f).

(** The bundle factoring of [f] into the probability object, the clean
    [tProb]-coin map behind [Bernoulli (ToProb f #"x")]. *)
Local Notation rm_phi := (po_into P f Hf_meas Hf_ge0 Hf_le1).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '!'" := (prom x) (at level 2, format "x '!'").
Local Notation eD_cbv' :=
  (@eD_cbv R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation eD' :=
  (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation cR := (carrier_to_R R_carrier_eq).
Local Notation tR' := (tR R_obj).
Local Notation Lty t1 t2 :=
  (linhom_car Ar (coalg_obj (tyD_cbv t1)) (coalg_obj (tyD_cbv t2))).

(** Abbreviations: the model type, the recursion type, and their
    underlying linhom cones. *)
Local Notation tmod := (tfun ta tR').
Local Notation trec := (tfun tmod tmod).
Local Notation Bmod := (Lty ta tR').
Local Notation Lrec := (Lty tmod tmod).

(** *** The semantic arguments: the model value [g!] and the input [a₀]

    The model argument is the PROMOTED point of an arbitrary unit-ball
    linear map [g : U⟦ta⟧ ⊸ FMeas].  Every lambda-written model
    denotes such a point: the [ne_lam] clause is [adj_psi] of the
    curried body, which PROMOTES at setlike environments
    ([adj_psi_at_setlike]) — see [sampler_val_E] below for the worked
    instance.  The input is an arbitrary setlike unit-ball point. *)

Variable (g : Bmod).
Hypothesis Hg_ball : cone_norm g <= 1.

Variable (a0 : coalg_obj (tyD_cbv ta)).
Hypothesis Ha_ball : cone_norm a0 <= 1.
Hypothesis Ha_setlike : Lfun (coalg_str (tyD_cbv ta)) a0 = a0!.

(** *** Syntactic decomposition of [ex_reject_comb] — all definitional *)

Local Notation ctx_rs :=
  (("rs"%string, trec) :: nil).
Local Notation ctx_m :=
  (("m"%string, tmod) :: ("rs"%string, trec) :: nil).
Local Notation ctx_a :=
  (("a"%string, ta) :: ("m"%string, tmod) :: ("rs"%string, trec) :: nil).
Local Notation ctx_x :=
  (("x"%string, tR') :: ("a"%string, ta) :: ("m"%string, tmod) ::
   ("rs"%string, trec) :: nil).

(** The test-and-dispatch body under the sample binder. *)
Definition rm_if : @named_expr R Ar R_obj ctx_x tR' :=
  [ if Bernoulli (ToProb {rm_phi} # "x")
    then # "x"
    else # "rs" @ # "m" @ # "a" ].

(** The five variables, as standalone terms. *)
Definition rm_var_x : @named_expr R Ar R_obj ctx_x tR' := [ # "x" ].
Definition rm_var_a4 : @named_expr R Ar R_obj ctx_x ta := [ # "a" ].
Definition rm_var_m4 : @named_expr R Ar R_obj ctx_x tmod := [ # "m" ].
Definition rm_var_rs4 : @named_expr R Ar R_obj ctx_x trec := [ # "rs" ].
Definition rm_var_a3 : @named_expr R Ar R_obj ctx_a ta := [ # "a" ].
Definition rm_var_m3 : @named_expr R Ar R_obj ctx_a tmod := [ # "m" ].

Lemma ex_reject_comb_decomp :
  ex_reject_comb (P := P) ta f =
  ne_fix "rs" (ex_reject_comb_body ta f).
Proof. by []. Qed.

Lemma ex_reject_comb_body_decomp :
  ex_reject_comb_body (P := P) ta f =
  ne_lam "m" (ex_reject_comb_fun ta f).
Proof. by []. Qed.

Lemma ex_reject_comb_fun_decomp :
  ex_reject_comb_fun (P := P) ta f =
  ne_lam "a" (ex_reject_comb_inner ta f).
Proof. by []. Qed.

Lemma ex_reject_comb_inner_decomp :
  ex_reject_comb_inner (P := P) ta f =
  ne_let "x" (ne_app rm_var_m3 rm_var_a3) rm_if.
Proof. by []. Qed.

(** The clean coin's underlying [tProb] argument: the acceptance
    test function [f] pushed through the bundle factoring [po_into] at the
    produced value [#"x"]. *)
Local Notation rm_coin_arg := (ne_to_prob rm_phi rm_var_x).

Lemma rm_if_decomp :
  rm_if =
  ne_if tR' (ne_bernoulli_p (po_density P) (po_density_meas P)
               (po_ge0 P) (po_le1 P) rm_coin_arg)
        rm_var_x
        (ne_app (ne_app rm_var_rs4 rm_var_m4) rm_var_a4).
Proof. by []. Qed.

(** *** The semantic objects *)

Let Hone : cone_norm (one1 : cone_one_car Ar) <= 1.
Proof. by rewrite one1_norm. Qed.

(** The model's output distribution at the input. *)
Definition reject_model_dist : coalg_obj (tyD_cbv tR') := linhom_fun g a0.

(** [W₀ := curry ⟦body⟧ (one1) : !Lrec ⊸ !Lrec] — the recursion body's
    endo-function at the closed environment. *)
Definition rm_W0 : linhom_car Ar (Bang Ar Lrec) (Bang Ar Lrec) :=
  Lfun (tensor_curry
         (eD_cbv' (ex_reject_comb_body ta f)))
       one1.

Lemma rm_W0_ball : cone_norm rm_W0 <= 1.
Proof. exact: le_trans (cones_hom_norm_le1 _ _) Hone. Qed.

(** The model value [g!] is a setlike unit-ball point of the cofree
    function-type coalgebra. *)
Lemma rm_g_ball : cone_norm (g!) <= 1.
Proof. exact: prom_ball Hg_ball. Qed.

Lemma rm_g_setlike :
  Lfun (coalg_str (tyD_cbv tmod)) (g!) = (g!)!.
Proof.
rewrite -[tyD_cbv tmod]/(bang_cofree Bmod) bang_cofree_str.
exact: (dig_prom _ Hg_ball).
Qed.

(** *** Step 1 — the program value and the application collapse

    The closed fixpoint program denotes the PROMOTED fixpoint value;
    CBV application of a function value [v : !L] to an argument [x] is
    [der(v)(x)], so the two applications to [g!] and [a₀] strip the
    promotion by [der ∘ prom = id] BEFORE any continuity argument. *)

Definition reject_comb_val : coalg_obj (tyD_cbv trec) :=
  Lfun (eD_cbv' (ex_reject_comb ta f)) one1.

Lemma reject_comb_val_E :
  reject_comb_val = (sc_fun (fix_value Lrec) rm_W0)!.
Proof.
have HoneG : cone_norm
    (one1 : coalg_obj (ctxD_cbv (drop_names (nil : named_ctx Ar)))) <= 1.
  by rewrite one1_norm.
rewrite /reject_comb_val ex_reject_comb_decomp.
exact: (eD_fix_at_setlike "rs"
          (ex_reject_comb_body ta f)
          HoneG coalg_str_one1).
Qed.

(** [ν] — the denotation of [(reject_comb m) a] at the model value
    [m = g!] and the input [a = a₀] (CBV application of the program
    value, twice). *)
Definition reject_model_denot : coalg_obj (tyD_cbv tR') :=
  linhom_fun
    (Lfun (der Bmod)
       (linhom_fun (Lfun (der Lrec) reject_comb_val) (g!)))
    a0.

Lemma reject_model_app_E :
  reject_model_denot =
  linhom_fun
    (Lfun (der Bmod)
       (linhom_fun (sc_fun (fix_value Lrec) rm_W0) (g!)))
    a0.
Proof.
rewrite /reject_model_denot reject_comb_val_E.
by rewrite (der_prom _ (fix_value_ball rm_W0 rm_W0_ball)).
Qed.

(** *** Step 2 — the denotation is the sup of the per-iterate measures

    [ν_n := der(fix_chain W₀ n (g!))(a₀)] — the n-th Kleene iterate
    applied to the model and the input. *)

Definition rm_chain (n : nat) : coalg_obj (tyD_cbv tmod) :=
  linhom_fun (fix_chain rm_W0 n) (g!).

Lemma rm_chain_chain n : precone_le (rm_chain n) (rm_chain n.+1).
Proof.
exact: (linhom_le_pointwise (fix_chain_chain rm_W0_ball n) (g!)).
Qed.

Lemma rm_chain_ball n : cone_norm (rm_chain n) <= 1.
Proof.
apply: le_trans
  (linhom_norm_apply_le (fix_chain_ball rm_W0_ball n) (g!)) _.
by rewrite mul1r rm_g_ball.
Qed.

Definition rm_der (n : nat) : Bmod := Lfun (der Bmod) (rm_chain n).

Lemma rm_der_chain n : precone_le (rm_der n) (rm_der n.+1).
Proof. exact: (Lfun_le (der Bmod) (rm_chain_chain n)). Qed.

Lemma rm_der_ball n : cone_norm (rm_der n) <= 1.
Proof. exact: le_trans (cones_hom_norm_le1 _ _) (rm_chain_ball n). Qed.

Definition reject_model_iter (n : nat) : coalg_obj (tyD_cbv tR') :=
  linhom_fun (rm_der n) a0.

Lemma rm_iter_chain n :
  precone_le (reject_model_iter n) (reject_model_iter n.+1).
Proof. exact: (linhom_le_pointwise (rm_der_chain n) a0). Qed.

Lemma rm_iter_ball n : cone_norm (reject_model_iter n) <= 1.
Proof.
apply: le_trans (linhom_norm_apply_le (rm_der_ball n) a0) _.
by rewrite mul1r Ha_ball.
Qed.

(** Evaluation at [g!], the counit [der], and evaluation at [a₀] all
    commute with the Kleene supremum: [linhom_fun_sup_ball] twice,
    with the [Lfun_sup_ball] ω-continuity reading in between. *)
Lemma reject_model_sup_E :
  reject_model_denot =
  cone_sup_ball reject_model_iter rm_iter_chain rm_iter_ball.
Proof.
rewrite reject_model_app_E (fix_value_E rm_W0_ball).
rewrite (linhom_fun_sup_ball (fix_chain_chain rm_W0_ball)
  (fix_chain_ball rm_W0_ball) rm_g_ball rm_chain_chain rm_chain_ball).
rewrite (Lfun_sup_ball (der Bmod) rm_chain_chain rm_chain_ball
  rm_der_chain rm_der_ball).
rewrite (linhom_fun_sup_ball rm_der_chain rm_der_ball Ha_ball
  rm_iter_chain rm_iter_ball).
by [].
Qed.

(** *** Step 3 — the Kleene step at the extended setlike environment *)

Lemma rm_chain_prom_ball n : cone_norm ((fix_chain rm_W0 n)!) <= 1.
Proof. exact: prom_ball (fix_chain_ball rm_W0_ball n). Qed.

Lemma rm_chain_prom_setlike n :
  Lfun (coalg_str (tyD_cbv trec))
       ((fix_chain rm_W0 n)!) = ((fix_chain rm_W0 n)!)!.
Proof.
rewrite -[tyD_cbv trec]/(bang_cofree Lrec) bang_cofree_str.
exact: (dig_prom _ (fix_chain_ball rm_W0_ball n)).
Qed.

(** The environment tower: ["rs"], then ["m"], then ["a"], then the
    Dirac-bound ["x"]. *)
Definition rm_env1 (n : nat) :
    coalg_obj (ctxD_cbv (drop_names ctx_rs)) :=
  one1 ⊗p (fix_chain rm_W0 n)!.

Definition rm_env2 (n : nat) :
    coalg_obj (ctxD_cbv (drop_names ctx_m)) :=
  rm_env1 n ⊗p (g!).

Definition rm_env3 (n : nat) :
    coalg_obj (ctxD_cbv (drop_names ctx_a)) :=
  rm_env2 n ⊗p a0.

Definition rm_env4 (n : nat) (r : ar_carrier Ar R_obj) :
    coalg_obj (ctxD_cbv (drop_names ctx_x)) :=
  rm_env3 n ⊗p dirac_fmeas r.

Lemma rm_env1_ball n : cone_norm (rm_env1 n) <= 1.
Proof.
by rewrite /rm_env1 tensor_normME one1_norm mul1r rm_chain_prom_ball.
Qed.

Lemma rm_env1_setlike n :
  Lfun (coalg_str (ctxD_cbv (drop_names ctx_rs))) (rm_env1 n) =
  (rm_env1 n)!.
Proof.
exact: (coalg_str_tensor_setlike (P:=EM_term) (Q:=tyD_cbv trec)
          Hone (rm_chain_prom_ball n) coalg_str_one1
          (rm_chain_prom_setlike n)).
Qed.

Lemma rm_env2_ball n : cone_norm (rm_env2 n) <= 1.
Proof.
rewrite /rm_env2 tensor_normME.
by rewrite mulr_ile1 ?cone_norm_ge0 ?rm_env1_ball ?rm_g_ball.
Qed.

Lemma rm_env2_setlike n :
  Lfun (coalg_str (ctxD_cbv (drop_names ctx_m))) (rm_env2 n) =
  (rm_env2 n)!.
Proof.
exact: (coalg_str_tensor_setlike
          (P:=ctxD_cbv (drop_names ctx_rs)) (Q:=tyD_cbv tmod)
          (rm_env1_ball n) rm_g_ball (rm_env1_setlike n) rm_g_setlike).
Qed.

Lemma rm_env3_ball n : cone_norm (rm_env3 n) <= 1.
Proof.
rewrite /rm_env3 tensor_normME.
by rewrite mulr_ile1 ?cone_norm_ge0 ?rm_env2_ball ?Ha_ball.
Qed.

Lemma rm_env3_setlike n :
  Lfun (coalg_str (ctxD_cbv (drop_names ctx_a))) (rm_env3 n) =
  (rm_env3 n)!.
Proof.
exact: (coalg_str_tensor_setlike
          (P:=ctxD_cbv (drop_names ctx_m)) (Q:=tyD_cbv ta)
          (rm_env2_ball n) Ha_ball (rm_env2_setlike n) Ha_setlike).
Qed.

Lemma rm_env4_ball n r : cone_norm (rm_env4 n r) <= 1.
Proof.
rewrite /rm_env4 tensor_normME.
by rewrite mulr_ile1 ?cone_norm_ge0 ?rm_env3_ball ?dirac_fmeas_norm_le1.
Qed.

Lemma rm_env4_setlike n r :
  Lfun (coalg_str (ctxD_cbv (drop_names ctx_x))) (rm_env4 n r) =
  (rm_env4 n r)!.
Proof.
exact: (coalg_str_tensor_setlike
          (P:=ctxD_cbv (drop_names ctx_a)) (Q:=FMeas_coalgebra R_obj)
          (rm_env3_ball n) (dirac_fmeas_norm_le1 r)
          (rm_env3_setlike n) (Coalg_dirac R_obj r)).
Qed.

(** The recursion body at the promoted iterate: the [λm]-packaging
    PROMOTES the curried [λa]-stage at the extended environment. *)
Lemma rm_W0_at_prom n :
  linhom_fun rm_W0 ((fix_chain rm_W0 n)!) =
  (Lfun (tensor_curry
          (eD_cbv' (ex_reject_comb_fun ta f)))
     (rm_env1 n))!.
Proof.
rewrite {1}/rm_W0 tensor_curryE ex_reject_comb_body_decomp eD_lam_E.
exact: (adj_psi_at_setlike (P:=ctxD_cbv (drop_names ctx_rs))
          _ (rm_env1_ball n) (rm_env1_setlike n)).
Qed.

(** One Kleene step at the model: [rs_{n+1}(g!) = ⟦λa.…⟧(1 ⊗ rs_n! ⊗ g!)]
    — and the [λa]-packaging promotes the curried inner body in turn. *)
Lemma rm_chain_S n :
  rm_chain n.+1 =
  Lfun (eD_cbv' (ex_reject_comb_fun ta f))
       (rm_env2 n).
Proof.
rewrite /rm_chain fix_chain_S rm_W0_at_prom.
rewrite (der_prom _ (le_trans (cones_hom_norm_le1 _ _) (rm_env1_ball n))).
exact: tensor_curryE.
Qed.

Lemma rm_chain_S_prom n :
  rm_chain n.+1 =
  (Lfun (tensor_curry
          (eD_cbv' (ex_reject_comb_inner ta f)))
     (rm_env2 n))!.
Proof.
rewrite rm_chain_S ex_reject_comb_fun_decomp eD_lam_E.
exact: (adj_psi_at_setlike (P:=ctxD_cbv (drop_names ctx_m))
          _ (rm_env2_ball n) (rm_env2_setlike n)).
Qed.

Lemma reject_model_iter_S n :
  reject_model_iter n.+1 =
  Lfun (eD_cbv' (ex_reject_comb_inner ta f))
       (rm_env3 n).
Proof.
rewrite /reject_model_iter /rm_der rm_chain_S_prom.
rewrite (der_prom _ (le_trans (cones_hom_norm_le1 _ _) (rm_env2_ball n))).
exact: tensor_curryE.
Qed.

(** *** Step 4 — variable projections and the dispatch at the Dirac
    environment *)

(** The variable projections at [rm_env3] (for the let-bound model
    application). *)
Lemma rm_var_a3_E n :
  Lfun (eD_cbv' rm_var_a3) (rm_env3 n) = a0.
Proof.
apply: (eq_trans (y := Lfun (em_proj2_mor (R:=R)
  (ctxD_cbv (drop_names ctx_m)) (tyD_cbv ta)) (rm_env3 n))).
  by [].
exact: (em_proj2_morE (rm_env2_ball n) (rm_env2_setlike n)).
Qed.

Lemma rm_var_m3_E n :
  Lfun (eD_cbv' rm_var_m3) (rm_env3 n) = (g!).
Proof.
apply: (eq_trans (y := Lfun (icones_comp
  (em_proj2_mor (R:=R) (ctxD_cbv (drop_names ctx_rs)) (tyD_cbv tmod))
  (em_proj1_mor (R:=R) (ctxD_cbv (drop_names ctx_m)) (tyD_cbv ta)))
  (rm_env3 n))).
  by [].
rewrite Lfun_comp.
rewrite (em_proj1_morE (Q:=tyD_cbv ta) Ha_ball Ha_setlike).
exact: (em_proj2_morE (P:=ctxD_cbv (drop_names ctx_rs))
          (rm_env1_ball n) (rm_env1_setlike n)).
Qed.

(** The let-bound MODEL APPLICATION at the environment: [⟦m @ a⟧ = ν_M]
    — the model's output distribution, whatever [n]. *)
Lemma rm_model_app_E n :
  Lfun (eD_cbv' (ne_app rm_var_m3 rm_var_a3)) (rm_env3 n) =
  reject_model_dist.
Proof.
rewrite (eD_app_at_setlike R_carrier_eq R_carrier_meas R_to_carrier_meas
           (rm_env3_ball n) (rm_env3_setlike n)).
rewrite rm_var_m3_E rm_var_a3_E.
by rewrite (der_prom _ Hg_ball).
Qed.

(** The variable projections at the Dirac environment [rm_env4]. *)
Lemma rm_var_x_E n r :
  Lfun (eD_cbv' rm_var_x) (rm_env4 n r) = dirac_fmeas r.
Proof.
apply: (eq_trans (y := Lfun (em_proj2_mor (R:=R)
  (ctxD_cbv (drop_names ctx_a)) (FMeas_coalgebra R_obj)) (rm_env4 n r))).
  by [].
exact: (em_proj2_morE (rm_env3_ball n) (rm_env3_setlike n)).
Qed.

Lemma rm_var_a4_E n r :
  Lfun (eD_cbv' rm_var_a4) (rm_env4 n r) = a0.
Proof.
apply: (eq_trans (y := Lfun (icones_comp
  (em_proj2_mor (R:=R) (ctxD_cbv (drop_names ctx_m)) (tyD_cbv ta))
  (em_proj1_mor (R:=R) (ctxD_cbv (drop_names ctx_a))
     (FMeas_coalgebra R_obj))) (rm_env4 n r))).
  by [].
rewrite Lfun_comp.
rewrite (em_proj1_morE (Q:=FMeas_coalgebra R_obj)
           (dirac_fmeas_norm_le1 r) (Coalg_dirac R_obj r)).
exact: (em_proj2_morE (P:=ctxD_cbv (drop_names ctx_m))
          (rm_env2_ball n) (rm_env2_setlike n)).
Qed.

Lemma rm_var_m4_E n r :
  Lfun (eD_cbv' rm_var_m4) (rm_env4 n r) = (g!).
Proof.
apply: (eq_trans (y := Lfun (icones_comp
  (icones_comp
    (em_proj2_mor (R:=R) (ctxD_cbv (drop_names ctx_rs)) (tyD_cbv tmod))
    (em_proj1_mor (R:=R) (ctxD_cbv (drop_names ctx_m)) (tyD_cbv ta)))
  (em_proj1_mor (R:=R) (ctxD_cbv (drop_names ctx_a))
     (FMeas_coalgebra R_obj))) (rm_env4 n r))).
  by [].
rewrite Lfun_comp Lfun_comp.
rewrite (em_proj1_morE (Q:=FMeas_coalgebra R_obj)
           (dirac_fmeas_norm_le1 r) (Coalg_dirac R_obj r)).
rewrite (em_proj1_morE (Q:=tyD_cbv ta) Ha_ball Ha_setlike).
exact: (em_proj2_morE (P:=ctxD_cbv (drop_names ctx_rs))
          (rm_env1_ball n) (rm_env1_setlike n)).
Qed.

Lemma rm_var_rs4_E n r :
  Lfun (eD_cbv' rm_var_rs4) (rm_env4 n r) = (fix_chain rm_W0 n)!.
Proof.
apply: (eq_trans (y := Lfun (icones_comp
  (icones_comp
    (icones_comp
      (em_proj2_mor (R:=R) EM_term (tyD_cbv trec))
      (em_proj1_mor (R:=R) (ctxD_cbv (drop_names ctx_rs))
         (tyD_cbv tmod)))
    (em_proj1_mor (R:=R) (ctxD_cbv (drop_names ctx_m)) (tyD_cbv ta)))
  (em_proj1_mor (R:=R) (ctxD_cbv (drop_names ctx_a))
     (FMeas_coalgebra R_obj))) (rm_env4 n r))).
  by [].
rewrite Lfun_comp Lfun_comp Lfun_comp.
rewrite (em_proj1_morE (Q:=FMeas_coalgebra R_obj)
           (dirac_fmeas_norm_le1 r) (Coalg_dirac R_obj r)).
rewrite (em_proj1_morE (Q:=tyD_cbv ta) Ha_ball Ha_setlike).
rewrite (em_proj1_morE (Q:=tyD_cbv tmod) rm_g_ball rm_g_setlike).
exact: (em_proj2_morE (P:=EM_term) Hone coalg_str_one1).
Qed.

(** The scrutinee at [δ_r] is the [f r]-coin (the bundled
    [ne_bernoulli_f] node desugared directly — no clamp transport). *)
Lemma rm_scrut_E n r :
  Lfun (eD_cbv' (ne_bernoulli_p (po_density P) (po_density_meas P)
                   (po_ge0 P) (po_le1 P) rm_coin_arg))
       (rm_env4 n r) =
  bernoulli (f (cR r)) (Hf_ge0 (cR r)) (Hf_le1 (cR r)).
Proof.
(* Clean-surface coin leaf: push [#"x"] through the bundle factoring
   [po_into f] and read off the [f r]-coin with [bern_lift_P];
   [po_into_E] recovers [f r]. *)
rewrite eD_bernoulli_p_E Lfun_comp.
rewrite -[bern_lift_g _ _ _]/(bern_lift_P P).
rewrite eD_to_prob_E Lfun_comp.
rewrite rm_var_x_E FMeas_fmap_dirac bern_lift_P_dirac.
apply: bool_cone_eq; apply: val_inj => /=; by rewrite /po_density po_into_E.
Qed.

(** ELSE: the recursive call AT THE SAME MODEL AND INPUT is exactly the
    previous iterate. *)
Lemma rm_else_E n r :
  Lfun (eD_cbv' (ne_app (ne_app rm_var_rs4 rm_var_m4) rm_var_a4))
       (rm_env4 n r) =
  reject_model_iter n.
Proof.
rewrite (eD_app_at_setlike R_carrier_eq R_carrier_meas R_to_carrier_meas
           (rm_env4_ball n r) (rm_env4_setlike n r)).
rewrite (eD_app_at_setlike R_carrier_eq R_carrier_meas R_to_carrier_meas
           (rm_env4_ball n r) (rm_env4_setlike n r)).
rewrite rm_var_rs4_E rm_var_m4_E rm_var_a4_E.
by rewrite (der_prom _ (fix_chain_ball rm_W0_ball n)).
Qed.

Lemma reject_model_if_at_dirac n r :
  Lfun (eD_cbv' rm_if) (rm_env4 n r) =
  bool_case (bernoulli (Ar:=Ar) (f (cR r)) (Hf_ge0 (cR r)) (Hf_le1 (cR r)))
            (dirac_fmeas r) (reject_model_iter n).
Proof.
rewrite rm_if_decomp eD_if_E.
rewrite (if_icones_at
  (eD_cbv' rm_var_x)
  (eD_cbv' (ne_app (ne_app rm_var_rs4 rm_var_m4) rm_var_a4))
  (eD_cbv' (ne_bernoulli_p (po_density P) (po_density_meas P)
              (po_ge0 P) (po_le1 P) rm_coin_arg))
  (rm_env4_ball n r) (rm_env4_setlike n r)).
by rewrite rm_scrut_E rm_var_x_E rm_else_E.
Qed.

(** *** Step 5 — the mass recurrence

    [ν_{n+1}(U) = ∫_U f dν_M + (m₀ - ∫f dν_M)·ν_n(U)] via the GENERAL
    let-law: the rejected-AND-model-terminated mass is
    [∫(1-f) dν_M = m₀ - ∫f dν_M] — the model's own divergence mass
    [1 - m₀] never re-enters the loop. *)

Local Open Scope ereal_scope.

(** [If] / [IUf U] abbreviate the acceptance-mass integrals in the
    PROOFS only ([only parsing]); the headline STATEMENTS below spell the
    integrals out explicitly so the reader sees the real measure
    [fmeas_mu reject_model_dist] and integrand [(f (cR ·))%:E]. *)
Local Notation If :=
  (\int[fmeas_mu reject_model_dist]_(r in [set: ar_carrier Ar R_obj])
     (f (cR r))%:E) (only parsing).
Local Notation IUf U :=
  (\int[fmeas_mu reject_model_dist]_(r in U) (f (cR r))%:E) (only parsing).
Local Notation m0 :=
  (fine (fmeas_mu reject_model_dist [set: ar_carrier Ar R_obj])).

Let f_cR_meas : measurable_fun [set: ar_carrier Ar R_obj]
    (fun r => f (cR r)).
Proof. exact: (bern_f_cR_meas R_carrier_meas Hf_meas). Qed.

(** [ν_M] is a sub-probability: total mass [m₀ ≤ 1]. *)
Lemma rm_dist_ball : (cone_norm reject_model_dist <= 1)%R.
Proof.
apply: le_trans (linhom_norm_apply_le Hg_ball a0) _.
by rewrite mul1r Ha_ball.
Qed.

Lemma rm_m0_le1 : (m0 <= 1)%R.
Proof. exact: rm_dist_ball. Qed.

Lemma rm_If_ge0 : 0 <= If.
Proof. by apply: integral_ge0 => r _; rewrite lee_fin Hf_ge0. Qed.

(** [∫ f dν_M ≤ ν_M(setT) = m₀]: acceptance cannot outweigh the
    model's own termination mass. *)
Lemma rm_If_le_mass :
  If <= fmeas_mu reject_model_dist [set: ar_carrier Ar R_obj].
Proof.
apply: (le_trans (y := \int[fmeas_mu reject_model_dist]_
                        (r in [set: ar_carrier Ar R_obj]) (cst 1%:E) r)).
  apply: ge0_le_integral => //.
  - by move=> r _; rewrite lee_fin Hf_ge0.
  - by apply/measurable_EFinP; exact: f_cR_meas.
  - by move=> r _; rewrite lee_fin Hf_le1.
by rewrite integral_cst// mul1e.
Qed.

Lemma rm_If_fin : If \is a fin_num.
Proof.
rewrite ge0_fin_numE ?rm_If_ge0//.
apply: le_lt_trans rm_If_le_mass _.
by rewrite ltey_eq fmeas_setT_fin.
Qed.

Lemma rm_fine_If_le_m0 : (fine If <= m0)%R.
Proof.
apply: fine_le; [exact: rm_If_fin | | exact: rm_If_le_mass].
exact: fmeas_setT_fin.
Qed.

Lemma rm_IUf_ge0 U : measurable U -> 0 <= IUf U.
Proof. by move=> mU; apply: integral_ge0 => r _; rewrite lee_fin Hf_ge0. Qed.

Lemma rm_IUf_le_If U : measurable U -> IUf U <= If.
Proof.
move=> mU; apply: ge0_subset_integral => //.
- by apply/measurable_EFinP; exact: f_cR_meas.
- by move=> r _; rewrite lee_fin Hf_ge0.
Qed.

Lemma rm_IUf_fin U : measurable U -> IUf U \is a fin_num.
Proof.
move=> mU; rewrite ge0_fin_numE ?rm_IUf_ge0//.
apply: le_lt_trans (rm_IUf_le_If mU) _.
apply: le_lt_trans rm_If_le_mass _.
by rewrite ltey_eq fmeas_setT_fin.
Qed.

(** The rejected-AND-terminated weight:
    [∫ (1 - f) dν_M = m₀ - ∫ f dν_M]. *)
Lemma rm_int_onem :
  \int[fmeas_mu reject_model_dist]_(r in [set: ar_carrier Ar R_obj])
     ((1 - f (cR r))%R)%:E = ((m0 - fine If)%R)%:E.
Proof.
have Honem_meas : measurable_fun [set: ar_carrier Ar R_obj]
    (fun r => ((1 - f (cR r))%R)%:E).
  apply/measurable_EFinP.
  by apply: measurable_funB => //; exact: f_cR_meas.
have Hsum : If + \int[fmeas_mu reject_model_dist]_
                  (r in [set: ar_carrier Ar R_obj])
                   ((1 - f (cR r))%R)%:E =
            fmeas_mu reject_model_dist [set: ar_carrier Ar R_obj].
  rewrite -ge0_integralD//; first last.
  - by move=> r _; rewrite lee_fin subr_ge0 Hf_le1.
  - by apply/measurable_EFinP; exact: f_cR_meas.
  - by move=> r _; rewrite lee_fin Hf_ge0.
  under eq_integral => r _.
    rewrite -EFinD addrCA subrr addr0.
    over.
  by rewrite integral_cst// mul1e.
have := congr1 (fun z => z - If) Hsum.
rewrite addeC addeK ?rm_If_fin// => ->.
rewrite -{1}(fineK (fmeas_setT_fin
               (reject_model_dist : fmeas R (ar_carrier Ar R_obj)))).
by rewrite -{1}(fineK rm_If_fin) -EFinB.
Qed.

(** The mass of one branch dispatch. *)
Lemma rm_case_mass n r U (mU : measurable U) :
  fmeas_mu (bool_case
    (bernoulli (Ar:=Ar) (f (cR r)) (Hf_ge0 (cR r)) (Hf_le1 (cR r)))
    (dirac_fmeas r) (reject_model_iter n)) U =
  ((f (cR r) * \1_U r + (1 - f (cR r)) *
      fine (fmeas_mu (reject_model_iter n) U))%R)%:E.
Proof.
have -> : (bool_case
    (bernoulli (Ar:=Ar) (f (cR r)) (Hf_ge0 (cR r)) (Hf_le1 (cR r)))
    (dirac_fmeas r) (reject_model_iter n) : fmeas R (ar_carrier Ar R_obj)) =
  fmeas_add
    (fmeas_scale (NngNum (Hf_ge0 (cR r))) (dirac_fmeas r))
    (fmeas_scale (NngNum (subr_ge0_le1 (f (cR r)) (Hf_le1 (cR r))))
       (reject_model_iter n)).
  by [].
rewrite fmeas_addE 2!fmeas_scaleE (dirac_fmeas_E r mU) diracE/=.
rewrite -(fineK (fmeas_fin (reject_model_iter n) U mU)).
by rewrite -2!EFinM -EFinD indicE.
Qed.

Lemma reject_model_iter_mass n U (mU : measurable U) :
  fmeas_mu (reject_model_iter n.+1) U =
  IUf U + ((m0 - fine If)%R)%:E * fmeas_mu (reject_model_iter n) U.
Proof.
have Hiter : reject_model_iter n.+1 =
    linhom_fun (eD' (ne_let "x"%string (ne_app rm_var_m3 rm_var_a3) rm_if))
               (rm_env3 n).
  rewrite reject_model_iter_S ex_reject_comb_inner_decomp.
  by rewrite /eD icones_to_linhomE.
rewrite Hiter.
rewrite (eD_let_mu_E R_carrier_meas R_to_carrier_meas
           (ne_app rm_var_m3 rm_var_a3) rm_if
           (rm_env3_ball n) (rm_env3_setlike n) mU).
rewrite rm_model_app_E.
set c := fine (fmeas_mu (reject_model_iter n) U).
under eq_integral => r _.
  rewrite reject_model_if_at_dirac (rm_case_mass n r mU)/= EFinD.
  over.
have Hc0 : (0 <= c)%R by rewrite /c fine_ge0// measure_ge0.
have m1 : measurable_fun [set: ar_carrier Ar R_obj]
    (fun r => ((f (cR r) * \1_U r)%R)%:E).
  apply/measurable_EFinP; apply: measurable_funM => //.
have m2 : measurable_fun [set: ar_carrier Ar R_obj]
    (fun r => (((1 - f (cR r)) *
                fine (fmeas_mu (reject_model_iter n) U))%R)%:E).
  apply/measurable_EFinP; apply: measurable_funM => //.
  by apply: measurable_funB => //; exact: f_cR_meas.
rewrite ge0_integralD//; first last.
- by move=> r _; rewrite lee_fin mulr_ge0// ?subr_ge0 ?Hf_le1.
- by move=> r _; rewrite lee_fin mulr_ge0// Hf_ge0.
congr (_ + _).
- rewrite [RHS](integral_mkcond U) epatch_indic.
  apply: eq_integral => r _.
  by rewrite /= EFinM.
- under eq_integral => r _.
    rewrite EFinM.
    over.
  rewrite ge0_integralZr//; first last.
  - by move=> x _; rewrite lee_fin subr_ge0 Hf_le1.
  - by apply/measurable_EFinP; apply: measurable_funB => //;
       exact: f_cR_meas.
  rewrite rm_int_onem.
  by rewrite (fineK (fmeas_fin (reject_model_iter n) U mU)).
Qed.

(** *** Step 6 — the headline theorems *)

Lemma rm_iter_0 : reject_model_iter 0 = precone_zero.
Proof.
rewrite /reject_model_iter /rm_der /rm_chain fix_chain_0 linhom_fun_zero.
have [Z0 _ _] := cones_hom_linear
  (mcones_hom_cones (icones_hom_mcones (der Bmod))).
by rewrite Z0 linhom_fun_zero.
Qed.

Lemma rm_iter_0_mass U : fmeas_mu (reject_model_iter 0) U = 0.
Proof.
have -> : (reject_model_iter 0 : fmeas R (ar_carrier Ar R_obj)) =
          fmeas_zero.
  by rewrite rm_iter_0.
exact: fmeas_zeroE.
Qed.

(** The master identity — division-free, unconditional, and
    sub-probability honest: [(1 - m₀ + ∫f dν_M) · ν(U) = ∫_U f dν_M].
    The success-per-trial mass is [1 - q] for [q := m₀ - ∫f dν_M] (the
    run is rejected exactly when the model terminates AND the coin
    rejects); the degenerate corner [q = 1] (a probability model with
    [f ≡ 0] [ν_M]-a.e.) has both sides [0]. *)
Theorem reject_model_master U (mU : measurable U) :
  ((1 - m0
      + fine (\int[fmeas_mu reject_model_dist]_(x in [set: ar_carrier Ar R_obj])
                ((f (cR x))%:E)))%R)%:E
    * fmeas_mu reject_model_denot U
  = \int[fmeas_mu reject_model_dist]_(x in U) ((f (cR x))%:E).
Proof.
have HnormE : (1 - m0 + fine If)%R = (1 - (m0 - fine If))%R.
  by rewrite opprB addrA addrAC.
rewrite HnormE.
pose xs := fun k => fine (fmeas_mu (reject_model_iter k) U).
have Hx0 : xs 0%N = 0%R by rewrite /xs rm_iter_0_mass.
have HxS : forall k,
    xs k.+1 = (fine (IUf U) + (m0 - fine If) * xs k)%R.
  move=> k; rewrite /xs (reject_model_iter_mass k mU).
  rewrite fineD ?rm_IUf_fin//; last first.
    by rewrite fin_numM// (fmeas_fin (reject_model_iter k) U mU).
  by rewrite fineM// (fmeas_fin (reject_model_iter k) U mU).
have Hq0 : (0 <= m0 - fine If)%R by rewrite subr_ge0 rm_fine_If_le_m0.
have Hq1 : (m0 - fine If <= 1)%R.
  apply: le_trans rm_m0_le1.
  by rewrite lerBlDr lerDl fine_ge0// rm_If_ge0.
have := Hq1; rewrite le_eqVlt => /orP[/eqP Hq_eq1 | Hq_lt1].
- (* Degenerate corner: q = 1 forces m₀ = 1 and ∫f dν_M = 0 — the
     loop never terminates; both sides vanish. *)
  have HfIf_ge0 : (0 <= fine If)%R by rewrite fine_ge0// rm_If_ge0.
  have Hm0_eq : (1 + fine If)%R = m0 by rewrite -Hq_eq1 subrK.
  have HfIf0 : fine If = 0%R.
    apply/le_anti/andP; split=> //.
    by rewrite -(lerD2l 1%R) addr0 Hm0_eq rm_m0_le1.
  have HIf0 : If = 0 by rewrite -(fineK rm_If_fin) HfIf0.
  have -> : IUf U = 0.
    apply/eqP; rewrite eq_le rm_IUf_ge0// andbT.
    by rewrite (le_trans (rm_IUf_le_If mU))// -HIf0.
  by rewrite Hq_eq1 subrr mul0e.
- (* Main case: the cascade converges to a/(1-q). *)
  have Hcvg := affine_iter_cvg (fine (IUf U)) (m0 - fine If)
                 Hq0 Hx0 HxS Hq_lt1.
  have HsupE : fmeas_mu reject_model_denot U =
      ((fine (IUf U) / (1 - (m0 - fine If)))%R)%:E.
    rewrite reject_model_sup_E.
    apply: (fmeas_kleene_sup_U_E rm_iter_chain rm_iter_ball mU).
    have HE : (fun k => fmeas_mu (reject_model_iter k) U) =
              (fun k => (xs k)%:E).
      apply/funext => k.
      by rewrite /xs fineK// (fmeas_fin (reject_model_iter k) U mU).
    by rewrite HE.
  rewrite HsupE -EFinM.
  have Hne : (1 - (m0 - fine If))%R != 0%R.
    by rewrite gt_eqF// subr_gt0.
  by rewrite mulrC mulfVK// (fineK (rm_IUf_fin mU)).
Qed.

(** Normalisation: when the loop makes progress
    ([0 < 1 - m₀ + ∫f dν_M] — automatic as soon as [0 < ∫f dν_M], and
    also whenever the model is a strict sub-probability), the
    combinator denotes the NORMALISED distribution
    [ν(U) = (∫_U f dν_M) / (1 - m₀ + ∫f dν_M)].  At [m₀ = 1] the
    normaliser is the classical [∫ f dν_M]. *)
Theorem reject_model_is_normalised :
  (0 < 1 - m0
     + fine (\int[fmeas_mu reject_model_dist]_(x in [set: ar_carrier Ar R_obj])
               ((f (cR x))%:E)))%R ->
  forall U, measurable U ->
  fmeas_mu reject_model_denot U =
  ((fine (\int[fmeas_mu reject_model_dist]_(x in U) ((f (cR x))%:E))
    / (1 - m0
         + fine (\int[fmeas_mu reject_model_dist]_
                   (x in [set: ar_carrier Ar R_obj]) ((f (cR x))%:E))))%R)%:E.
Proof.
move=> Hpos U mU.
have HmF : ((1 - m0 + fine If) *
            fine (fmeas_mu reject_model_denot U))%R = fine (IUf U).
  have := congr1 fine (reject_model_master mU).
  by rewrite fineM// (fmeas_fin reject_model_denot U mU).
rewrite -(fineK (fmeas_fin reject_model_denot U mU)); congr (_%:E).
by rewrite -HmF mulrAC divff ?mul1r// gt_eqF.
Qed.

(** The total-mass identity: [ν(setT) = ∫f dν_M / (1 - m₀ + ∫f dν_M)]
    — the probability that SOME trial eventually accepts. *)
Theorem reject_model_mass :
  (0 < 1 - m0
     + fine (\int[fmeas_mu reject_model_dist]_(x in [set: ar_carrier Ar R_obj])
               ((f (cR x))%:E)))%R ->
  fmeas_mu reject_model_denot [set: ar_carrier Ar R_obj] =
  ((fine (\int[fmeas_mu reject_model_dist]_(x in [set: ar_carrier Ar R_obj])
            ((f (cR x))%:E))
    / (1 - m0
         + fine (\int[fmeas_mu reject_model_dist]_
                   (x in [set: ar_carrier Ar R_obj]) ((f (cR x))%:E))))%R)%:E.
Proof.
move=> Hpos; exact: (reject_model_is_normalised Hpos measurableT).
Qed.

(** Almost-sure termination for PROBABILITY models: at [m₀ = 1] with
    positive acceptance mass the combinator denotes a probability
    distribution. *)
Theorem reject_model_mass_one :
  m0 = 1%R ->
  0 < \int[fmeas_mu reject_model_dist]_(x in [set: ar_carrier Ar R_obj])
        ((f (cR x))%:E) ->
  fmeas_mu reject_model_denot [set: ar_carrier Ar R_obj] = 1.
Proof.
move=> Hm01 HIf.
have HfIf : (0 < fine If)%R.
  rewrite fine_gt0// HIf/= (le_lt_trans rm_If_le_mass)//.
  by rewrite ltey_eq fmeas_setT_fin.
have Hpos : (0 < 1 - m0 + fine If)%R by rewrite Hm01 subrr add0r.
rewrite (reject_model_mass Hpos) Hm01 subrr add0r divff// gt_eqF//.
Qed.

(** Certain rejection diverges — whatever the model does: at [f ≡ 0]
    the combinator denotes the zero measure (each iterate's mass is
    [0 + q·0 = 0], for ANY rejected-mass [q]). *)
Theorem reject_model_zero :
  (forall r : R, f r = 0%R) -> reject_model_denot = precone_zero.
Proof.
move=> Hf0.
have HIUf0 : forall U : set (ar_carrier Ar R_obj), IUf U = 0.
  move=> U.
  under eq_integral => r _ do rewrite Hf0.
  exact: integral0.
have Hmass : forall n (U : set (ar_carrier Ar R_obj)),
    measurable U -> fmeas_mu (reject_model_iter n) U = 0.
  elim=> [ | n IH] U mU; first exact: rm_iter_0_mass.
  by rewrite (reject_model_iter_mass n mU) IH// mule0 adde0 HIUf0.
apply: fmeas_eq => U mU.
rewrite reject_model_sup_E.
rewrite (fmeas_kleene_sup_U_E rm_iter_chain rm_iter_ball mU (l := 0)).
  by rewrite -[precone_zero]/(fmeas_zero : fmeas R (ar_carrier Ar R_obj))
       fmeas_zeroE.
have HE : (fun n => fmeas_mu (reject_model_iter n) U) =
          (fun n => (0 : \bar R)).
  by apply/funext => n; rewrite Hmass.
rewrite HE.
exact: cvg_cst.
Qed.

End RejectModel.

(** ** §3 — Instance: the sampler model reproduces the [ex_reject]
    headline

    At [ta := tunit] and the lambda-written model [λ_. sample µ]
    ([examples.v::ex_sampler]) with a unit-mass prior, [ν_M = µ] and
    [m₀ = 1]: the combinator's master identity specialises to the
    classical [∫f dµ · ν(U) = ∫_U f dµ] — and in fact the combinator
    applied to the sampler model denotes THE SAME measure as the
    original [ex_reject] program (whose recursive function abstracts
    over an acceptance continuation instead of a model: a different
    surface shape, same Kleene-iterate masses). *)

Section SamplerInstance.
Variables (R : realType) (Ar : MeasSubcat R).
(* Reparameterized over the bundled [probObj]. *)
Variable (P : probObj Ar).
Local Notation R_obj := (po_robj P).
Local Notation R_carrier_eq := (po_robj_eq P).
Local Notation R_carrier_meas := (po_robj_meas P).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

(** The prior: a bundled sub-probability of unit mass (the
    [ex_reject] hypotheses). *)
Variable (m : pmeas Ar R_obj).
Local Notation mu := (pm_meas m).
Hypothesis Hmu1 : (fmeas_mu mu [set: ar_carrier Ar R_obj] = 1)%E.

Variable (f : testfn R).
Local Notation Hf_meas := (test_meas f).
Local Notation Hf_ge0 := (test_ge0 f).
Local Notation Hf_le1 := (test_le1 f).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '!'" := (prom x) (at level 2, format "x '!'").
Local Notation eD_cbv' :=
  (@eD_cbv R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation cR := (carrier_to_R R_carrier_eq).
Local Notation tR' := (tR R_obj).
Local Notation Lty t1 t2 :=
  (linhom_car Ar (coalg_obj (tyD_cbv t1)) (coalg_obj (tyD_cbv t2))).

Let Hone : cone_norm (one1 : cone_one_car Ar) <= 1.
Proof. by rewrite one1_norm. Qed.

(** *** The sampler model's underlying linear map [g_µ]

    The lambda-clause of [eD] packages the model as the PROMOTION of
    the curried body at the closed environment — the exact shape the
    combinator theorems quantify over. *)

Definition sampler_lin : Lty tunit tR' :=
  Lfun (tensor_curry (eD_cbv' (ex_sampler_body m))) one1.

Lemma sampler_lin_ball : cone_norm sampler_lin <= 1.
Proof. exact: le_trans (cones_hom_norm_le1 _ _) Hone. Qed.

Lemma ex_sampler_decomp :
  ex_sampler m = ne_lam "_" (ex_sampler_body m).
Proof. by []. Qed.

(** [⟦λ_. sample µ⟧(1) = g_µ!] — the lambda-written model denotes the
    promoted point of [g_µ]. *)
Lemma sampler_val_E :
  Lfun (eD_cbv' (ex_sampler m)) one1 = sampler_lin!.
Proof.
rewrite ex_sampler_decomp eD_lam_E.
by rewrite (adj_psi_at_setlike
              (tensor_curry (eD_cbv' (ex_sampler_body m)))
              Hone coalg_str_one1).
Qed.

(** The model's output distribution at the unit input is the prior:
    [ν_M = g_µ(1) = µ]. *)
Lemma sampler_out_E : linhom_fun sampler_lin one1 = mu.
Proof.
rewrite /sampler_lin tensor_curryE.
have Henv_ball : cone_norm
    ((one1 : cone_one_car Ar) ⊗p (one1 : cone_one_car Ar)) <= 1.
  by rewrite tensor_normME one1_norm mul1r.
have Henv_setlike :
    Lfun (coalg_str (ctxD_cbv (drop_names (("_"%string, tunit) :: nil))))
      ((one1 : cone_one_car Ar) ⊗p (one1 : cone_one_car Ar)) =
    ((one1 : cone_one_car Ar) ⊗p (one1 : cone_one_car Ar))!.
  exact: (coalg_str_tensor_setlike (P:=EM_term) (Q:=EM_term)
            Hone Hone coalg_str_one1 coalg_str_one1).
rewrite eD_sample_E.
exact: (const_iconesE (Z := ctxD_cbv (drop_names (("_"%string, tunit) :: nil)))
          Henv_ball Henv_setlike).
Qed.

(** *** The instance denotation and the bridge to [ex_reject] *)

(** The combinator applied to the sampler model at the unit input. *)
Local Notation inst_denot :=
  (reject_model_denot R_to_carrier_meas
     f sampler_lin one1).

Local Notation inst_iter :=
  (reject_model_iter R_to_carrier_meas
     f sampler_lin one1).

(** The instance's model-output distribution is the prior. *)
Lemma inst_dist_E :
  reject_model_dist (ta := tunit) (P := P) sampler_lin one1 = mu.
Proof. exact: sampler_out_E. Qed.

(** Per-iterate masses agree with the [ex_reject] headline's: both
    chains satisfy the SAME cascade
    [x_{n+1}(U) = ∫_U f dµ + (1 - ∫f dµ)·x_n(U)] from [x_0 = 0]. *)
Lemma inst_iter_massE n U (mU : measurable U) :
  fmeas_mu (inst_iter n) U =
  fmeas_mu
    (reject_iter R_to_carrier_meas m
       f n) U.
Proof.
elim: n U mU => [ | n IH] U mU.
  by rewrite rm_iter_0_mass reject_iter_0_mass.
rewrite (reject_model_iter_mass _ _ sampler_lin_ball Hone
           coalg_str_one1 n mU).
rewrite (ex_reject_iter_mass R_to_carrier_meas
           Hmu1 f n mU).
by rewrite inst_dist_E Hmu1 IH.
Qed.

(** The bridge: the combinator at the sampler model denotes the same
    measure as the original [ex_reject] program — equal per-iterate
    masses pass to the Kleene suprema by uniqueness of limits. *)
Theorem ex_reject_comb_sampler_E :
  inst_denot =
  linhom_fun (ex_reject_cbv P R_to_carrier_meas
                m f) one1.
Proof.
apply: fmeas_eq => U mU.
rewrite (reject_model_sup_E _ _ sampler_lin_ball Hone).
rewrite (ex_reject_sup_E R_to_carrier_meas
           m f).
apply: (fmeas_kleene_sup_U_E _ _ mU).
have HE : (fun n => fmeas_mu (inst_iter n) U) =
          (fun n => fmeas_mu
             (reject_iter R_to_carrier_meas m
                f n) U).
  by apply/funext => n; exact: inst_iter_massE.
rewrite HE.
exact: (fmeas_kleene_sup_U_cvg _ _ mU).
Qed.

(** The [ex_reject] master identity, re-derived from the combinator
    through the bridge: [∫f dµ · ν(U) = ∫_U f dµ]. *)
Theorem ex_reject_comb_sampler_master U (mU : measurable U) :
  ((\int[fmeas_mu mu]_(r in [set: ar_carrier Ar R_obj]) (f (cR r))%:E) *
   fmeas_mu inst_denot U =
   \int[fmeas_mu mu]_(r in U) (f (cR r))%:E)%E.
Proof.
rewrite ex_reject_comb_sampler_E.
exact: (ex_reject_master R_to_carrier_meas
          Hmu1 f mU).
Qed.

End SamplerInstance.

(** ** §4 — The [condition] combinator: soft conditioning of a model

    [examples.v::ex_condition_comb] is the Pyro-style [condition]
    operator
    [[
       condition = λ m. λ a.
         let x = m a in
         let _ = Score (Meas{f} x) in
         x
    ]]
    — run the model at the input, weigh the trace by the likelihood
    [f x] of the produced value, return the value.  THE CONDITIONING
    LAW ([condition_model_E]): at a unit-ball model value [g!] and a
    setlike unit-ball input [a₀] (the §2 set-up verbatim), the
    conditioned model's output is the prior-reweighted-by-likelihood
    measure
    [[
       ν_cond(U) = ∫_U f dν_M,    ν_M := g(a₀),
    ]]
    the generalisation of [ex_score_posterior_cbv_E]
    ([cbv_marginals.v] §2 — the special case [m = λ_. sample µ]) to an
    ARBITRARY model.  The reduction chain is the §2 chain MINUS the
    fixpoint: the combinator is a plain double lambda, so the two
    applications are [der ∘ prom] collapses, the let binds the model
    application ([eD_let_mu_E] at [ν_M]), and the score-and-return
    continuation computes at Dirac environments exactly as in the
    [ex_score_posterior] proof ([score_lift_dirac] +
    [em_proj1_mor_unitE]). *)

Section ConditionModel.
Variables (R : realType) (Ar : MeasSubcat R).
(* Reparameterized over the bundled [probObj]. *)
Variable (P : probObj Ar).
Local Notation R_obj := (po_robj P).
Local Notation R_carrier_eq := (po_robj_eq P).
Local Notation R_carrier_meas := (po_robj_meas P).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

(** The model's input type: an ARBITRARY PPL type. *)
Variable (ta : ppl_type Ar).

(** The soft observation test function (the likelihood) as a BUNDLED
    [[0,1]] record; its projections are exposed under their historical
    names. *)
Variable (f : testfn R).
Local Notation Hf_meas := (test_meas f).
Local Notation Hf_ge0 := (test_ge0 f).
Local Notation Hf_le1 := (test_le1 f).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '!'" := (prom x) (at level 2, format "x '!'").
Local Notation eD_cbv' :=
  (@eD_cbv R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation eD' :=
  (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation cR := (carrier_to_R R_carrier_eq).
Local Notation tR' := (tR R_obj).
Local Notation Lty t1 t2 :=
  (linhom_car Ar (coalg_obj (tyD_cbv t1)) (coalg_obj (tyD_cbv t2))).

(** Abbreviations: the model type and its underlying linhom cone. *)
Local Notation tmod := (tfun ta tR').
Local Notation Bmod := (Lty ta tR').

(** *** The semantic arguments: the model value [g!] and the input
    [a₀] — the §2 set-up verbatim. *)

Variable (g : Bmod).
Hypothesis Hg_ball : cone_norm g <= 1.

Variable (a0 : coalg_obj (tyD_cbv ta)).
Hypothesis Ha_ball : cone_norm a0 <= 1.
Hypothesis Ha_setlike : Lfun (coalg_str (tyD_cbv ta)) a0 = a0!.

(** *** Syntactic decomposition of [ex_condition_comb] — all
    definitional *)

Local Notation cctx_m :=
  (("m"%string, tmod) :: nil).
Local Notation cctx_a :=
  (("a"%string, ta) :: ("m"%string, tmod) :: nil).
Local Notation cctx_x :=
  (("x"%string, tR') :: ("a"%string, ta) :: ("m"%string, tmod) :: nil).
Local Notation cctx_u :=
  (("_"%string, tunit) :: ("x"%string, tR') :: ("a"%string, ta) ::
   ("m"%string, tmod) :: nil).

(** The variables, as standalone terms. *)
Definition cm_var_m : @named_expr R Ar R_obj cctx_a tmod := [ # "m" ].
Definition cm_var_a : @named_expr R Ar R_obj cctx_a ta := [ # "a" ].
Definition cm_var_x : @named_expr R Ar R_obj cctx_x tR' := [ # "x" ].
Definition cm_ret : @named_expr R Ar R_obj cctx_u tR' := [ # "x" ].

(** The bundle factoring of the likelihood [f] into the probability
    object, the clean [tProb]-score map behind [Score (ToProb f #"x")]. *)
Local Notation cm_phi := (po_into P f Hf_meas Hf_ge0 Hf_le1).

(** The clean [tProb]-score node. *)
Local Notation cm_score :=
  (ne_score_p (po_density P) (po_density_meas P) (po_ge0 P) (po_le1 P)
     (ne_to_prob cm_phi cm_var_x)).

(** The score-and-return continuation under the value binder. *)
Definition cm_K : @named_expr R Ar R_obj cctx_x tR' :=
  ne_let "_" cm_score cm_ret.

Lemma ex_condition_comb_decomp :
  ex_condition_comb (P := P) ta f =
  ne_lam "m" (ex_condition_fun ta f).
Proof. by []. Qed.

Lemma ex_condition_fun_decomp :
  ex_condition_fun (P := P) ta f =
  ne_lam "a" (ex_condition_inner ta f).
Proof. by []. Qed.

Lemma ex_condition_inner_decomp :
  ex_condition_inner (P := P) ta f =
  ne_let "x" (ne_app cm_var_m cm_var_a) cm_K.
Proof. by []. Qed.

(** *** The semantic objects *)

Let Hone : cone_norm (one1 : cone_one_car Ar) <= 1.
Proof. by rewrite one1_norm. Qed.

Lemma cm_g_ball : cone_norm (g!) <= 1.
Proof. exact: prom_ball Hg_ball. Qed.

Lemma cm_g_setlike :
  Lfun (coalg_str (tyD_cbv tmod)) (g!) = (g!)!.
Proof.
rewrite -[tyD_cbv tmod]/(bang_cofree Bmod) bang_cofree_str.
exact: (dig_prom _ Hg_ball).
Qed.

(** *** Step 1 — the combinator value and the application collapses

    No fixpoint here: the closed double-lambda denotes a promoted
    curried stage, and the applications to [g!] and [a₀] strip the
    promotions by [der ∘ prom = id]. *)

(** The combinator's underlying linear map (the [λa]-stage curried at
    the closed environment). *)
Definition cond_fun_lin : Lty tmod tmod :=
  Lfun (tensor_curry (eD_cbv' (ex_condition_fun ta f)))
       one1.

Lemma cond_fun_lin_ball : cone_norm cond_fun_lin <= 1.
Proof. exact: le_trans (cones_hom_norm_le1 _ _) Hone. Qed.

(** The combinator program's value. *)
Definition cond_comb_val : coalg_obj (tyD_cbv (tfun tmod tmod)) :=
  Lfun (eD_cbv' (ex_condition_comb ta f)) one1.

Lemma cond_comb_val_E : cond_comb_val = cond_fun_lin!.
Proof.
rewrite /cond_comb_val ex_condition_comb_decomp eD_lam_E.
by rewrite (adj_psi_at_setlike
              (tensor_curry
                 (eD_cbv' (ex_condition_fun ta f)))
              Hone coalg_str_one1).
Qed.

(** [ν_cond] — the denotation of [(condition_comb m) a] at the model
    value [m = g!] and the input [a = a₀]. *)
Definition cond_model_denot : coalg_obj (tyD_cbv tR') :=
  linhom_fun
    (Lfun (der Bmod)
       (linhom_fun (Lfun (der (Lty tmod tmod)) cond_comb_val) (g!)))
    a0.

(** *** Step 2 — collapse to the inner body at the extended setlike
    environment [(1 ⊗ g!) ⊗ a₀] *)

(** The environment tower: ["m"], then ["a"], then the Dirac-bound
    ["x"]. *)
Definition cond_env1 : coalg_obj (ctxD_cbv (drop_names cctx_m)) :=
  one1 ⊗p (g!).

Definition cond_env2 : coalg_obj (ctxD_cbv (drop_names cctx_a)) :=
  cond_env1 ⊗p a0.

Definition cond_env3 (r : ar_carrier Ar R_obj) :
    coalg_obj (ctxD_cbv (drop_names cctx_x)) :=
  cond_env2 ⊗p dirac_fmeas r.

Lemma cond_env1_ball : cone_norm cond_env1 <= 1.
Proof. by rewrite /cond_env1 tensor_normME one1_norm mul1r cm_g_ball. Qed.

Lemma cond_env1_setlike :
  Lfun (coalg_str (ctxD_cbv (drop_names cctx_m))) cond_env1 =
  cond_env1!.
Proof.
exact: (coalg_str_tensor_setlike (P:=EM_term) (Q:=tyD_cbv tmod)
          Hone cm_g_ball coalg_str_one1 cm_g_setlike).
Qed.

Lemma cond_env2_ball : cone_norm cond_env2 <= 1.
Proof.
rewrite /cond_env2 tensor_normME.
by rewrite mulr_ile1 ?cone_norm_ge0 ?cond_env1_ball ?Ha_ball.
Qed.

Lemma cond_env2_setlike :
  Lfun (coalg_str (ctxD_cbv (drop_names cctx_a))) cond_env2 =
  cond_env2!.
Proof.
exact: (coalg_str_tensor_setlike
          (P:=ctxD_cbv (drop_names cctx_m)) (Q:=tyD_cbv ta)
          cond_env1_ball Ha_ball cond_env1_setlike Ha_setlike).
Qed.

Lemma cond_env3_ball r : cone_norm (cond_env3 r) <= 1.
Proof.
rewrite /cond_env3 tensor_normME.
by rewrite mulr_ile1 ?cone_norm_ge0 ?cond_env2_ball ?dirac_fmeas_norm_le1.
Qed.

Lemma cond_env3_setlike r :
  Lfun (coalg_str (ctxD_cbv (drop_names cctx_x))) (cond_env3 r) =
  (cond_env3 r)!.
Proof.
exact: (coalg_str_tensor_setlike
          (P:=ctxD_cbv (drop_names cctx_a)) (Q:=FMeas_coalgebra R_obj)
          cond_env2_ball (dirac_fmeas_norm_le1 r)
          cond_env2_setlike (Coalg_dirac R_obj r)).
Qed.

(** The [λa]-stage at the model value promotes the curried inner
    body. *)
Lemma cond_fun_at_g :
  linhom_fun cond_fun_lin (g!) =
  (Lfun (tensor_curry
           (eD_cbv' (ex_condition_inner ta f)))
     cond_env1)!.
Proof.
rewrite /cond_fun_lin tensor_curryE ex_condition_fun_decomp eD_lam_E.
exact: (adj_psi_at_setlike (P:=ctxD_cbv (drop_names cctx_m))
          _ cond_env1_ball cond_env1_setlike).
Qed.

(** The full collapse: [ν_cond = ⟦inner⟧((1 ⊗ g!) ⊗ a₀)]. *)
Lemma cond_model_denot_E :
  cond_model_denot =
  Lfun (eD_cbv' (ex_condition_inner ta f))
       cond_env2.
Proof.
rewrite /cond_model_denot cond_comb_val_E.
rewrite (der_prom _ cond_fun_lin_ball) cond_fun_at_g.
rewrite (der_prom _ (le_trans (cones_hom_norm_le1 _ _) cond_env1_ball)).
exact: tensor_curryE.
Qed.

(** *** Step 3 — variable projections and the model application *)

Lemma cm_var_a_E :
  Lfun (eD_cbv' cm_var_a) cond_env2 = a0.
Proof.
apply: (eq_trans (y := Lfun (em_proj2_mor (R:=R)
  (ctxD_cbv (drop_names cctx_m)) (tyD_cbv ta)) cond_env2)).
  by [].
exact: (em_proj2_morE cond_env1_ball cond_env1_setlike).
Qed.

Lemma cm_var_m_E :
  Lfun (eD_cbv' cm_var_m) cond_env2 = (g!).
Proof.
apply: (eq_trans (y := Lfun (icones_comp
  (em_proj2_mor (R:=R) EM_term (tyD_cbv tmod))
  (em_proj1_mor (R:=R) (ctxD_cbv (drop_names cctx_m)) (tyD_cbv ta)))
  cond_env2)).
  by [].
rewrite Lfun_comp.
rewrite (em_proj1_morE (Q:=tyD_cbv ta) Ha_ball Ha_setlike).
exact: (em_proj2_morE (P:=EM_term) Hone coalg_str_one1).
Qed.

(** The let-bound MODEL APPLICATION at the environment:
    [⟦m @ a⟧ = ν_M]. *)
Lemma cond_app_E :
  Lfun (eD_cbv' (ne_app cm_var_m cm_var_a)) cond_env2 =
  reject_model_dist g a0.
Proof.
rewrite (eD_app_at_setlike R_carrier_eq R_carrier_meas R_to_carrier_meas
           cond_env2_ball cond_env2_setlike).
rewrite cm_var_m_E cm_var_a_E.
by rewrite (der_prom _ Hg_ball).
Qed.

(** *** Step 4 — the score-and-return continuation at the Dirac
    environment (the [ex_score_posterior] computation at [ν_M]) *)

(** The scored variable projects the bound value. *)
Lemma cm_var_x_E r :
  Lfun (eD_cbv' cm_var_x) (cond_env3 r) = dirac_fmeas r.
Proof.
apply: (eq_trans (y := Lfun (em_proj2_mor (R:=R)
  (ctxD_cbv (drop_names cctx_a)) (FMeas_coalgebra R_obj)) (cond_env3 r))).
  by [].
exact: (em_proj2_morE cond_env2_ball cond_env2_setlike).
Qed.

(** The score value at [δ_r] is the scalar [f r] (the bundled
    [ne_score] node desugared directly — no clamp transport — then
    [score_lift_dirac]). *)
Lemma cm_score_E r :
  Lfun (eD_cbv' cm_score)
       (cond_env3 r) =
  MkConeOne Ar (NngNum (Hf_ge0 (cR r))).
Proof.
(* Clean-surface score leaf: push [#"x"] through the bundle factoring
   [po_into f] and read off the score scalar with [score_lift_P];
   [po_into_E] recovers [f r]. *)
rewrite eD_score_p_E.
rewrite -[score_lift_g _ _ _]/(score_lift_P P).
rewrite (Lfun_comp (score_lift_P P) (eD_cbv' (ne_to_prob cm_phi cm_var_x))
  (cond_env3 r)).
rewrite eD_to_prob_E.
rewrite (Lfun_comp (FMeas_fmap cm_phi) (eD_cbv' cm_var_x) (cond_env3 r)).
rewrite cm_var_x_E FMeas_fmap_dirac score_lift_P_dirac.
apply: cone_one_eq; apply: val_inj => /=.
by rewrite /po_density po_into_E.
Qed.

(** The returned variable under the score binder: the [tunit]-typed
    score result is NOT setlike — [em_proj1_mor_unitE] turns the score
    scalar into a [precone_scale] weight. *)
Lemma cm_ret_at r (s : cone_one_car Ar) :
  Lfun (eD_cbv' cm_ret) ((cond_env3 r) ⊗p s) =
  precone_scale (c1_val s) (dirac_fmeas r).
Proof.
apply: (eq_trans (y := Lfun (icones_comp
  (em_proj2_mor (R:=R) (ctxD_cbv (drop_names cctx_a))
     (FMeas_coalgebra R_obj))
  (em_proj1_mor (R:=R) (ctxD_cbv (drop_names cctx_x)) EM_term))
  ((cond_env3 r) ⊗p s))).
  by [].
rewrite Lfun_comp.
rewrite (em_proj1_mor_unitE
  (P:=ctxD_cbv (drop_names cctx_x)) (cond_env3 r) s).
rewrite (Lfun_scaleE
  (em_proj2_mor (R:=R) (ctxD_cbv (drop_names cctx_a))
     (FMeas_coalgebra R_obj))
  (c1_val s) (cond_env3 r)).
by rewrite (em_proj2_morE (P:=ctxD_cbv (drop_names cctx_a))
              cond_env2_ball cond_env2_setlike).
Qed.

(** The continuation at [δ_r] weighs the returned point mass by the
    density: [⟦let _ = score f x in x⟧(γ ⊗ δ_r) = (f r)·δ_r]. *)
Lemma cm_K_at_dirac r :
  Lfun (eD_cbv' cm_K) (cond_env3 r) =
  precone_scale (NngNum (Hf_ge0 (cR r))) (dirac_fmeas r).
Proof.
rewrite /cm_K eD_let_E.
rewrite (Lfun_comp (eD_cbv' cm_ret)
  (em_pair_mor
     (icones_id Ar (coalg_obj (ctxD_cbv (drop_names cctx_x))))
     (eD_cbv' cm_score))
  (cond_env3 r)).
rewrite /em_pair_mor.
rewrite (Lfun_comp
  (tensor_mor
     (icones_id Ar (coalg_obj (ctxD_cbv (drop_names cctx_x))))
     (eD_cbv' cm_score))
  (coalg_d (ctxD_cbv (drop_names cctx_x)))
  (cond_env3 r)).
rewrite (coalg_d_setlike (P:=ctxD_cbv (drop_names cctx_x))
  (cond_env3_ball r) (cond_env3_setlike r)).
rewrite (tensor_morE
  (icones_id Ar (coalg_obj (ctxD_cbv (drop_names cctx_x))))
  (eD_cbv' cm_score)
  (cond_env3 r) (cond_env3 r)).
by rewrite icones_idE cm_score_E cm_ret_at.
Qed.

(** *** Step 5 — the conditioning law *)

Local Open Scope ereal_scope.

(** [ν_cond(U) = ∫_U f dν_M] — the conditioned model's output is the
    model's output reweighted by the likelihood (unnormalised). *)
Theorem condition_model_E (U : set (ar_carrier Ar R_obj))
    (mU : measurable U) :
  fmeas_mu cond_model_denot U =
  \int[fmeas_mu (reject_model_dist g a0)]_(r in U) (f (cR r))%:E.
Proof.
have Hinner : cond_model_denot =
    linhom_fun (eD' (ne_let "x"%string (ne_app cm_var_m cm_var_a) cm_K))
               cond_env2.
  rewrite cond_model_denot_E ex_condition_inner_decomp.
  by rewrite /eD icones_to_linhomE.
rewrite Hinner.
rewrite (eD_let_mu_E R_carrier_meas R_to_carrier_meas
           (ne_app cm_var_m cm_var_a) cm_K
           cond_env2_ball cond_env2_setlike mU).
rewrite cond_app_E.
under eq_integral => r _.
  rewrite cm_K_at_dirac fmeas_scaleE (dirac_fmeas_E r mU) diracE -EFinM /=.
  over.
rewrite [RHS](integral_mkcond U) epatch_indic.
apply: eq_integral => r _.
by rewrite /= EFinM.
Qed.

(** Mass corollary — the model evidence: the conditioned model's total
    mass is [∫ f dν_M]. *)
Theorem condition_model_mass :
  fmeas_mu cond_model_denot [set: ar_carrier Ar R_obj] =
  \int[fmeas_mu (reject_model_dist g a0)]_
     (r in [set: ar_carrier Ar R_obj]) (f (cR r))%:E.
Proof. exact: (condition_model_E measurableT). Qed.

End ConditionModel.

(** ** §5 — Readable restatements: the [⟦·⟧] denotation brackets

    RESTATED ALIASES ONLY — every theorem in this section is a
    corollary of the §2 results above; nothing is re-proved.  The
    point is the SHAPE of the statements: closed surface PROGRAMS
    under semantic brackets, masses and integrals against the
    program-denoted measures.

    [⟦ M ⟧] denotes the MEASURE of the closed [tR]-typed program [M]:
    [⟦ M ⟧ := fmeas_mu (linhom_fun (eD M) one1)] — so [⟦ M ⟧ U] is the
    sub-probability mass on [U] and [\int[⟦ M ⟧]_(x in U) …]
    integrates against it.  (The notation is section-local: the
    interpreter [eD] carries the three standing carrier-cast
    hypotheses, which a global notation cannot infer.)

    The programs:
    - [model_prog := λ_. Mbody] — an ARBITRARY thunked model: [Mbody]
      is any program of type [tR] (samples, scores, recursion, …);
    - [model_run  := model_prog ()] — the model, run;
    - [reject_prog := reject_comb model_prog ()] — rejection sampling
      over the model, run at the unit input.

    The master identity then reads (with [ν_M := ⟦ model_run ⟧]):
    [[
       (1 - ν_M(setT) + ∫ f dν_M) · ⟦ reject_prog ⟧ U = ∫_U f dν_M
    ]] *)

Section ReadableHeadlines.
Variables (R : realType) (Ar : MeasSubcat R).
(* Reparameterized over the bundled [probObj]. *)
Variable (P : probObj Ar).
Local Notation R_obj := (po_robj P).
Local Notation R_carrier_eq := (po_robj_eq P).
Local Notation R_carrier_meas := (po_robj_meas P).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

(** The soft acceptance test function as a BUNDLED [[0,1]] record; its
    projections are exposed under their historical names. *)
Variable (f : testfn R).
Local Notation Hf_meas := (test_meas f).
Local Notation Hf_ge0 := (test_ge0 f).
Local Notation Hf_le1 := (test_le1 f).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation "x '!'" := (prom x) (at level 2, format "x '!'").
Local Notation eD_cbv' :=
  (@eD_cbv R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation eD' :=
  (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation cR := (carrier_to_R R_carrier_eq).
Local Notation tR' := (tR R_obj).
Local Notation Lty t1 t2 :=
  (linhom_car Ar (coalg_obj (tyD_cbv t1)) (coalg_obj (tyD_cbv t2))).

(** The semantic brackets: the measure denoted by a closed [tR]-typed
    program. *)
Local Notation "⟦ M ⟧" :=
  (fmeas_mu (linhom_fun (eD' M) one1)) (at level 0, format "⟦ M ⟧").

(** The model body: an ARBITRARY [tR]-typed program over the thunk
    context. *)
Variable (Mbody : @named_expr R Ar R_obj (("_"%string, tunit) :: nil) tR').

(** The three closed programs. *)
Definition model_prog : @named_expr R Ar R_obj nil (tfun tunit tR') :=
  [ \ "_" ::: tunit => {Mbody} ].

Definition model_run : @named_expr R Ar R_obj nil tR' :=
  [ {model_prog} @ () ].

Definition reject_prog : @named_expr R Ar R_obj nil tR' :=
  [ {ex_reject_comb tunit f} @ {model_prog} @ () ].

(** *** The semantic bridges — the program denotations are the §2
    semantic objects at [g := model_lin], [a₀ := one1] *)

Let Hone : cone_norm (one1 : cone_one_car Ar) <= 1.
Proof. by rewrite one1_norm. Qed.

(** [Hone] retyped at the empty-context coalgebra (the form
    [eD_app_at_setlike] keys on). *)
Let HoneG : cone_norm
    (one1 : coalg_obj (ctxD_cbv (drop_names (nil : named_ctx Ar)))) <= 1.
Proof. by rewrite one1_norm. Qed.

(** The model's underlying linear map (the [sampler_lin] pattern). *)
Definition model_lin : Lty tunit tR' :=
  Lfun (tensor_curry (eD_cbv' Mbody)) one1.

Lemma model_lin_ball : cone_norm model_lin <= 1.
Proof. exact: le_trans (cones_hom_norm_le1 _ _) Hone. Qed.

(** [⟦λ_. Mbody⟧(1) = model_lin!]. *)
Lemma model_prog_val_E :
  Lfun (eD_cbv' model_prog) one1 = model_lin!.
Proof.
rewrite -[model_prog]/(ne_lam "_"%string Mbody) eD_lam_E.
by rewrite (adj_psi_at_setlike (tensor_curry (eD_cbv' Mbody))
              Hone coalg_str_one1).
Qed.

(** [⟦()⟧(1) = one1] — the unit value at the closed environment. *)
Lemma tt_val_E :
  Lfun (eD_cbv' (@ne_tt R Ar R_obj nil)) one1 = one1.
Proof.
rewrite eD_tt_E.
rewrite -[ch_mor (em_term_mor (ctxD_cbv (drop_names (nil : named_ctx Ar))))]
        /(coalg_e (EM_term : Coalgebra Ar)).
by rewrite coalg_e_term.
Qed.

(** [⟦model_prog ()⟧(1) = ν_M] — running the model is the §2 output
    distribution. *)
Lemma model_run_val_E :
  Lfun (eD_cbv' model_run) one1 =
  reject_model_dist (ta := tunit) (P := P) model_lin one1.
Proof.
rewrite -[model_run]/(ne_app model_prog (@ne_tt R Ar R_obj nil)).
rewrite (eD_app_at_setlike R_carrier_eq R_carrier_meas R_to_carrier_meas
           HoneG coalg_str_one1).
rewrite model_prog_val_E tt_val_E.
by rewrite (der_prom _ model_lin_ball).
Qed.

(** [⟦reject_comb model_prog ()⟧(1) = ν] — the program denotes the §2
    combinator denotation. *)
Lemma reject_prog_val_E :
  Lfun (eD_cbv' reject_prog) one1 =
  reject_model_denot R_to_carrier_meas
    f model_lin one1.
Proof.
rewrite -[reject_prog]/(ne_app
  (ne_app (ex_reject_comb tunit f) model_prog)
  (@ne_tt R Ar R_obj nil)).
rewrite (eD_app_at_setlike R_carrier_eq R_carrier_meas R_to_carrier_meas
           HoneG coalg_str_one1).
rewrite (eD_app_at_setlike R_carrier_eq R_carrier_meas R_to_carrier_meas
           HoneG coalg_str_one1).
by rewrite model_prog_val_E tt_val_E.
Qed.

(** The linhom-level readings of the bridges (for rewriting under
    [⟦·⟧], which is phrased on the public [eD]). *)
Let model_run_lin_E :
  linhom_fun (eD' model_run) one1 =
  reject_model_dist (ta := tunit) (P := P) model_lin one1.
Proof. by rewrite /eD icones_to_linhomE model_run_val_E. Qed.

Let reject_prog_lin_E :
  linhom_fun (eD' reject_prog) one1 =
  reject_model_denot R_to_carrier_meas
    f model_lin one1.
Proof. by rewrite /eD icones_to_linhomE reject_prog_val_E. Qed.

Local Open Scope ereal_scope.

(** *** The restated headlines *)

(** The master identity, in math form: writing [ν_M := ⟦ model_run ⟧] for the
    model's output distribution,
    [[
       (1 - ν_M(setT) + ∫ f dν_M) · ⟦ reject_prog ⟧ U = ∫_U f dν_M.
    ]] *)
Theorem reject_prog_master U (mU : measurable U) :
  ((1 - fine (⟦ model_run ⟧ [set: ar_carrier Ar R_obj])
      + fine (\int[⟦ model_run ⟧]_(x in [set: ar_carrier Ar R_obj])
                (f (cR x))%:E))%R)%:E
    * ⟦ reject_prog ⟧ U
  = \int[⟦ model_run ⟧]_(x in U) (f (cR x))%:E.
Proof.
rewrite model_run_lin_E reject_prog_lin_E.
exact: (reject_model_master _ _ model_lin_ball Hone
          coalg_str_one1 mU).
Qed.

(** The normalised form: when the loop makes progress, the program
    denotes the normalised distribution
    [[
       ⟦ reject_prog ⟧ U = (∫_U f dν_M) / (1 - ν_M(setT) + ∫ f dν_M).
    ]] *)
Theorem reject_prog_is_normalised :
  (0 < 1 - fine (⟦ model_run ⟧ [set: ar_carrier Ar R_obj])
     + fine (\int[⟦ model_run ⟧]_(x in [set: ar_carrier Ar R_obj])
               (f (cR x))%:E))%R ->
  forall U, measurable U ->
  ⟦ reject_prog ⟧ U =
  ((fine (\int[⟦ model_run ⟧]_(x in U) (f (cR x))%:E)
    / (1 - fine (⟦ model_run ⟧ [set: ar_carrier Ar R_obj])
         + fine (\int[⟦ model_run ⟧]_(x in [set: ar_carrier Ar R_obj])
                   (f (cR x))%:E)))%R)%:E.
Proof.
rewrite model_run_lin_E reject_prog_lin_E => Hpos U mU.
exact: (reject_model_is_normalised _ model_lin_ball Hone
          coalg_str_one1 Hpos mU).
Qed.

(** Almost-sure termination for probability models: if the model is a
    probability ([⟦ model_run ⟧(setT) = 1]) with positive acceptance
    mass, the sampler accepts almost surely:
    [[
       ⟦ reject_prog ⟧ (setT) = 1.
    ]] *)
Theorem reject_prog_mass_one :
  ⟦ model_run ⟧ [set: ar_carrier Ar R_obj] = 1 ->
  0 < \int[⟦ model_run ⟧]_(x in [set: ar_carrier Ar R_obj])
        (f (cR x))%:E ->
  ⟦ reject_prog ⟧ [set: ar_carrier Ar R_obj] = 1.
Proof.
rewrite model_run_lin_E reject_prog_lin_E => Hm1 HIf.
apply: (reject_model_mass_one _ model_lin_ball Hone
          coalg_str_one1 _ HIf).
by rewrite -[1%R]/(fine (1 : \bar R)) Hm1.
Qed.

(** Certain rejection diverges: [f ≡ 0] forces the zero measure,
    whatever the model does:
    [[
       ⟦ reject_prog ⟧ U = 0.
    ]] *)
Theorem reject_prog_zero U :
  (forall r : R, f r = 0%R) -> ⟦ reject_prog ⟧ U = 0.
Proof.
rewrite reject_prog_lin_E => Hf0.
rewrite (reject_model_zero _ model_lin_ball Hone
           coalg_str_one1 Hf0).
by rewrite -[precone_zero]/(fmeas_zero : fmeas R (ar_carrier Ar R_obj))
           fmeas_zeroE.
Qed.

(** *** The conditioned model and the equivalence

    [condition_prog] is the CONDITIONED MODEL, run: the Pyro-style
    [condition M f] operator ([examples.v::ex_condition], surface form
    [Condition { f , … } M]) applied to the same [model_prog] and run
    at the same unit input as [reject_prog].  The §4 conditioning law
    and the §2 master identity then meet in the equivalence: rejection
    sampling computes the conditioned model's normalised
    distribution. *)

Definition condition_prog : @named_expr R Ar R_obj nil tR' :=
  [ {ex_condition f model_prog} @ () ].

(** [⟦condition_comb model_prog ()⟧(1) = ν_cond] — the program denotes
    the §4 conditioned-model denotation. *)
Lemma condition_prog_val_E :
  Lfun (eD_cbv' condition_prog) one1 =
  cond_model_denot R_to_carrier_meas
    f model_lin one1.
Proof.
rewrite -[condition_prog]/(ne_app
  (ne_app (ex_condition_comb tunit f) model_prog)
  (@ne_tt R Ar R_obj nil)).
rewrite (eD_app_at_setlike R_carrier_eq R_carrier_meas R_to_carrier_meas
           HoneG coalg_str_one1).
rewrite (eD_app_at_setlike R_carrier_eq R_carrier_meas R_to_carrier_meas
           HoneG coalg_str_one1).
by rewrite model_prog_val_E tt_val_E.
Qed.

Let condition_prog_lin_E :
  linhom_fun (eD' condition_prog) one1 =
  cond_model_denot R_to_carrier_meas
    f model_lin one1.
Proof. by rewrite /eD icones_to_linhomE condition_prog_val_E. Qed.

(** The conditioning law, in math form: the conditioned model denotes
    the model's output reweighted by the likelihood,
    [[
       ⟦ condition_prog ⟧ U = ∫_U f dν_M,    ν_M := ⟦ model_run ⟧.
    ]] *)
Theorem condition_E U (mU : measurable U) :
  ⟦ condition_prog ⟧ U = \int[⟦ model_run ⟧]_(x in U) (f (cR x))%:E.
Proof.
rewrite condition_prog_lin_E model_run_lin_E.
exact: (condition_model_E _ _ model_lin_ball Hone
          coalg_str_one1 mU).
Qed.

(** The model evidence: the conditioned model's total mass is
    [∫ f dν_M]. *)
Theorem condition_prog_evidence :
  ⟦ condition_prog ⟧ [set: ar_carrier Ar R_obj] =
  \int[⟦ model_run ⟧]_(x in [set: ar_carrier Ar R_obj]) (f (cR x))%:E.
Proof. exact: (condition_E measurableT). Qed.

(** The equivalence — rejection sampling computes the conditioned
    model's normalised distribution:
    [[
       Z · ⟦ reject_prog ⟧ U = ⟦ condition_prog ⟧ U,
       Z := 1 - ⟦ model_run ⟧(setT) + ∫ f d⟦ model_run ⟧
    ]]
    unconditionally (division-free, graceful in the degenerate
    never-accepting corner where both sides vanish). *)
Theorem reject_normalises_condition U (mU : measurable U) :
  ((1 - fine (⟦ model_run ⟧ [set: ar_carrier Ar R_obj])
      + fine (\int[⟦ model_run ⟧]_(x in [set: ar_carrier Ar R_obj])
                (f (cR x))%:E))%R)%:E
    * ⟦ reject_prog ⟧ U
  = ⟦ condition_prog ⟧ U.
Proof. by rewrite (condition_E mU); exact: (reject_prog_master mU). Qed.

(** The DIVISION form: when the loop makes progress ([0 < Z]),
    [[
       ⟦ reject_prog ⟧ U = ⟦ condition_prog ⟧ U / Z.
    ]] *)
Theorem reject_prog_computes_condition :
  (0 < 1 - fine (⟦ model_run ⟧ [set: ar_carrier Ar R_obj])
     + fine (\int[⟦ model_run ⟧]_(x in [set: ar_carrier Ar R_obj])
               (f (cR x))%:E))%R ->
  forall U, measurable U ->
  ⟦ reject_prog ⟧ U =
  ((fine (⟦ condition_prog ⟧ U)
    / (1 - fine (⟦ model_run ⟧ [set: ar_carrier Ar R_obj])
         + fine (\int[⟦ model_run ⟧]_(x in [set: ar_carrier Ar R_obj])
                   (f (cR x))%:E)))%R)%:E.
Proof.
move=> Hpos U mU.
rewrite (condition_E mU).
exact: (reject_prog_is_normalised Hpos mU).
Qed.

(** The PROBABILITY-MODEL form: for a unit-mass model the normaliser
    IS the conditioned model's total mass (the model evidence), so the
    equivalence reads
    [[
       ⟦ condition_prog ⟧(setT) · ⟦ reject_prog ⟧ U
         = ⟦ condition_prog ⟧ U.
    ]] *)
Theorem reject_normalises_condition_prob U (mU : measurable U) :
  ⟦ model_run ⟧ [set: ar_carrier Ar R_obj] = 1 ->
  ⟦ condition_prog ⟧ [set: ar_carrier Ar R_obj] * ⟦ reject_prog ⟧ U
  = ⟦ condition_prog ⟧ U.
Proof.
move=> Hm1.
rewrite -(reject_normalises_condition mU); congr (_ * _).
rewrite condition_prog_evidence Hm1.
have HIf_fin :
    (\int[⟦ model_run ⟧]_(x in [set: ar_carrier Ar R_obj])
       (f (cR x))%:E) \is a fin_num.
  rewrite model_run_lin_E.
  exact: (rm_If_fin f model_lin one1).
by rewrite -[in LHS](fineK HIf_fin)/= subrr add0r.
Qed.

End ReadableHeadlines.
