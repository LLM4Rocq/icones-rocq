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
         if Bernoulli_f { f } x then x else rs m a
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
      [ν(U) = IUf U / (1 - m₀ + If)] — THE normalised distribution,
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

    See also: [theories/programs/ex_reject_headline.v] (the original
    headline and the §1 setlike/sup kit reused here),
    [theories/programs/infra/let_sample_law.v] (the general let-law),
    [theories/programs/infra/em_fix_value.v] (the value-fixpoint
    combinator), [theories/programs/infra/affine_cascade.v].

    Author: Guillaume Baudart <guillaume.baudart@inria.fr>. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals signed constructive_ereal.
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
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

(** The model's input type: an ARBITRARY PPL type. *)
Variable (ta : ppl_type Ar).

(** The soft acceptance predicate: a [[0,1]]-valued density. *)
Variable (f : R -> R).
Hypothesis Hf_meas : measurable_fun [set: R] f.
Hypothesis Hf_ge0 : forall r : R, (0 <= f r)%R.
Hypothesis Hf_le1 : forall r : R, (f r <= 1)%R.

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
  [ if Bernoulli_f { f , Hf_meas , Hf_ge0 , Hf_le1 } # "x"
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
  ex_reject_comb (R_obj := R_obj) ta f Hf_meas Hf_ge0 Hf_le1 =
  ne_fix "rs" (ex_reject_comb_body ta f Hf_meas Hf_ge0 Hf_le1).
Proof. by []. Qed.

Lemma ex_reject_comb_body_decomp :
  ex_reject_comb_body (R_obj := R_obj) ta f Hf_meas Hf_ge0 Hf_le1 =
  ne_lam "m" (ex_reject_comb_fun ta f Hf_meas Hf_ge0 Hf_le1).
Proof. by []. Qed.

Lemma ex_reject_comb_fun_decomp :
  ex_reject_comb_fun (R_obj := R_obj) ta f Hf_meas Hf_ge0 Hf_le1 =
  ne_lam "a" (ex_reject_comb_inner ta f Hf_meas Hf_ge0 Hf_le1).
Proof. by []. Qed.

Lemma ex_reject_comb_inner_decomp :
  ex_reject_comb_inner (R_obj := R_obj) ta f Hf_meas Hf_ge0 Hf_le1 =
  ne_let "x" (ne_app rm_var_m3 rm_var_a3) rm_if.
Proof. by []. Qed.

Lemma rm_if_decomp :
  rm_if =
  ne_if tR' (ne_bernoulli_f f Hf_meas Hf_ge0 Hf_le1 rm_var_x)
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
         (eD_cbv' (ex_reject_comb_body ta f Hf_meas Hf_ge0 Hf_le1)))
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
  Lfun (eD_cbv' (ex_reject_comb ta f Hf_meas Hf_ge0 Hf_le1)) one1.

Lemma reject_comb_val_E :
  reject_comb_val = (sc_fun (fix_value Lrec) rm_W0)!.
Proof.
have HoneG : cone_norm
    (one1 : coalg_obj (ctxD_cbv (drop_names (nil : named_ctx Ar)))) <= 1.
  by rewrite one1_norm.
rewrite /reject_comb_val ex_reject_comb_decomp.
exact: (eD_fix_at_setlike "rs"
          (ex_reject_comb_body ta f Hf_meas Hf_ge0 Hf_le1)
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
          (eD_cbv' (ex_reject_comb_fun ta f Hf_meas Hf_ge0 Hf_le1)))
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
  Lfun (eD_cbv' (ex_reject_comb_fun ta f Hf_meas Hf_ge0 Hf_le1))
       (rm_env2 n).
Proof.
rewrite /rm_chain fix_chain_S rm_W0_at_prom.
rewrite (der_prom _ (le_trans (cones_hom_norm_le1 _ _) (rm_env1_ball n))).
exact: tensor_curryE.
Qed.

Lemma rm_chain_S_prom n :
  rm_chain n.+1 =
  (Lfun (tensor_curry
          (eD_cbv' (ex_reject_comb_inner ta f Hf_meas Hf_ge0 Hf_le1)))
     (rm_env2 n))!.
Proof.
rewrite rm_chain_S ex_reject_comb_fun_decomp eD_lam_E.
exact: (adj_psi_at_setlike (P:=ctxD_cbv (drop_names ctx_m))
          _ (rm_env2_ball n) (rm_env2_setlike n)).
Qed.

Lemma reject_model_iter_S n :
  reject_model_iter n.+1 =
  Lfun (eD_cbv' (ex_reject_comb_inner ta f Hf_meas Hf_ge0 Hf_le1))
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
rewrite (eD_app_at_setlike R_carrier_meas R_to_carrier_meas _ _
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

(** The scrutinee at [δ_r] is the [f r]-coin. *)
Lemma rm_scrut_E n r :
  Lfun (eD_cbv' (ne_bernoulli_f f Hf_meas Hf_ge0 Hf_le1 rm_var_x))
       (rm_env4 n r) =
  bernoulli (f (cR r)) (Hf_ge0 (cR r)) (Hf_le1 (cR r)).
Proof.
rewrite eD_bernoulli_f_E.
rewrite (Lfun_comp
  (bern_lift (R_carrier_meas:=R_carrier_meas) Hf_meas Hf_ge0 Hf_le1)
  (eD_cbv' rm_var_x) (rm_env4 n r)).
rewrite rm_var_x_E.
rewrite -{1}(carrier_to_RK R_carrier_eq r).
by rewrite (bern_lift_dirac Hf_meas Hf_ge0 Hf_le1 (cR r)).
Qed.

(** ELSE: the recursive call AT THE SAME MODEL AND INPUT is exactly the
    previous iterate. *)
Lemma rm_else_E n r :
  Lfun (eD_cbv' (ne_app (ne_app rm_var_rs4 rm_var_m4) rm_var_a4))
       (rm_env4 n r) =
  reject_model_iter n.
Proof.
rewrite (eD_app_at_setlike R_carrier_meas R_to_carrier_meas _ _
           (rm_env4_ball n r) (rm_env4_setlike n r)).
rewrite (eD_app_at_setlike R_carrier_meas R_to_carrier_meas _ _
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
  (eD_cbv' (ne_bernoulli_f f Hf_meas Hf_ge0 Hf_le1 rm_var_x))
  (rm_env4_ball n r) (rm_env4_setlike n r)).
by rewrite rm_scrut_E rm_var_x_E rm_else_E.
Qed.

(** *** Step 5 — the mass recurrence

    [ν_{n+1}(U) = ∫_U f dν_M + (m₀ - ∫f dν_M)·ν_n(U)] via the GENERAL
    let-law: the rejected-AND-model-terminated mass is
    [∫(1-f) dν_M = m₀ - ∫f dν_M] — the model's own divergence mass
    [1 - m₀] never re-enters the loop. *)

Local Open Scope ereal_scope.

Local Notation If :=
  (\int[fmeas_mu reject_model_dist]_(r in [set: ar_carrier Ar R_obj])
     (f (cR r))%:E).
Local Notation IUf U :=
  (\int[fmeas_mu reject_model_dist]_(r in U) (f (cR r))%:E).
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

Lemma rm_m0_ge0 : (0 <= m0)%R.
Proof. by rewrite fine_ge0// measure_ge0. Qed.

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
- by move=> r _; rewrite lee_fin mulr_ge0// indicE; case: (_ \in _).
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

(** THE MASTER IDENTITY — division-free, unconditional, and
    sub-probability honest: [(1 - m₀ + ∫f dν_M) · ν(U) = ∫_U f dν_M].
    The success-per-trial mass is [1 - q] for [q := m₀ - ∫f dν_M] (the
    run is rejected exactly when the model terminates AND the coin
    rejects); the degenerate corner [q = 1] (a probability model with
    [f ≡ 0] [ν_M]-a.e.) has both sides [0]. *)
Theorem reject_model_master U (mU : measurable U) :
  ((1 - m0 + fine If)%R)%:E * fmeas_mu reject_model_denot U = IUf U.
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

(** THE HEADLINE: when the loop makes progress
    ([0 < 1 - m₀ + ∫f dν_M] — automatic as soon as [0 < ∫f dν_M], and
    also whenever the model is a strict sub-probability), the
    combinator denotes the NORMALISED distribution
    [ν(U) = (∫_U f dν_M) / (1 - m₀ + ∫f dν_M)].  At [m₀ = 1] the
    normaliser is the classical [∫ f dν_M]. *)
Theorem reject_model_is_normalised :
  (0 < 1 - m0 + fine If)%R ->
  forall U, measurable U ->
  fmeas_mu reject_model_denot U =
  ((fine (IUf U) / (1 - m0 + fine If))%R)%:E.
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
  (0 < 1 - m0 + fine If)%R ->
  fmeas_mu reject_model_denot [set: ar_carrier Ar R_obj] =
  ((fine If / (1 - m0 + fine If))%R)%:E.
Proof.
move=> Hpos; exact: (reject_model_is_normalised Hpos measurableT).
Qed.

(** Almost-sure termination for PROBABILITY models: at [m₀ = 1] with
    positive acceptance mass the combinator denotes a probability
    distribution. *)
Theorem reject_model_mass_one :
  m0 = 1%R -> 0 < If ->
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
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

(** The prior: a unit-mass measure (the [ex_reject] hypotheses). *)
Variable (mu : fmeas R (ar_carrier Ar R_obj)).
Hypothesis Hmu_ball : (cone_norm mu <= 1)%R.
Hypothesis Hmu1 : (fmeas_mu mu [set: ar_carrier Ar R_obj] = 1)%E.

Variable (f : R -> R).
Hypothesis Hf_meas : measurable_fun [set: R] f.
Hypothesis Hf_ge0 : forall r : R, (0 <= f r)%R.
Hypothesis Hf_le1 : forall r : R, (f r <= 1)%R.

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
  Lfun (tensor_curry (eD_cbv' (ex_sampler_body mu Hmu_ball))) one1.

Lemma sampler_lin_ball : cone_norm sampler_lin <= 1.
Proof. exact: le_trans (cones_hom_norm_le1 _ _) Hone. Qed.

Lemma ex_sampler_decomp :
  ex_sampler mu Hmu_ball = ne_lam "_" (ex_sampler_body mu Hmu_ball).
Proof. by []. Qed.

(** [⟦λ_. sample µ⟧(1) = g_µ!] — the lambda-written model denotes the
    promoted point of [g_µ]. *)
Lemma sampler_val_E :
  Lfun (eD_cbv' (ex_sampler mu Hmu_ball)) one1 = sampler_lin!.
Proof.
rewrite ex_sampler_decomp eD_lam_E.
by rewrite (adj_psi_at_setlike
              (tensor_curry (eD_cbv' (ex_sampler_body mu Hmu_ball)))
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
  (reject_model_denot R_carrier_meas R_to_carrier_meas
     Hf_meas Hf_ge0 Hf_le1 sampler_lin one1).

Local Notation inst_iter :=
  (reject_model_iter R_carrier_meas R_to_carrier_meas
     Hf_meas Hf_ge0 Hf_le1 sampler_lin one1).

(** The instance's model-output distribution is the prior. *)
Lemma inst_dist_E :
  reject_model_dist (ta := tunit) (R_obj := R_obj) sampler_lin one1 = mu.
Proof. exact: sampler_out_E. Qed.

(** Per-iterate masses agree with the [ex_reject] headline's: both
    chains satisfy the SAME cascade
    [x_{n+1}(U) = ∫_U f dµ + (1 - ∫f dµ)·x_n(U)] from [x_0 = 0]. *)
Lemma inst_iter_massE n U (mU : measurable U) :
  fmeas_mu (inst_iter n) U =
  fmeas_mu
    (reject_iter R_carrier_meas R_to_carrier_meas Hmu_ball
       Hf_meas Hf_ge0 Hf_le1 n) U.
Proof.
elim: n U mU => [ | n IH] U mU.
  by rewrite rm_iter_0_mass reject_iter_0_mass.
rewrite (reject_model_iter_mass _ _ _ _ _ sampler_lin_ball Hone
           coalg_str_one1 n mU).
rewrite (ex_reject_iter_mass R_carrier_meas R_to_carrier_meas
           Hmu_ball Hmu1 Hf_meas Hf_ge0 Hf_le1 n mU).
by rewrite inst_dist_E Hmu1 IH.
Qed.

(** THE BRIDGE: the combinator at the sampler model denotes THE SAME
    measure as the original [ex_reject] program — equal per-iterate
    masses pass to the Kleene suprema by uniqueness of limits. *)
Theorem ex_reject_comb_sampler_E :
  inst_denot =
  linhom_fun (ex_reject_cbv R_carrier_meas R_to_carrier_meas
                Hmu_ball Hf_meas Hf_ge0 Hf_le1) one1.
Proof.
apply: fmeas_eq => U mU.
rewrite (reject_model_sup_E _ _ _ _ _ sampler_lin_ball Hone).
rewrite (ex_reject_sup_E R_carrier_meas R_to_carrier_meas
           Hmu_ball Hf_meas Hf_ge0 Hf_le1).
apply: (fmeas_kleene_sup_U_E _ _ mU).
have HE : (fun n => fmeas_mu (inst_iter n) U) =
          (fun n => fmeas_mu
             (reject_iter R_carrier_meas R_to_carrier_meas Hmu_ball
                Hf_meas Hf_ge0 Hf_le1 n) U).
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
exact: (ex_reject_master R_carrier_meas R_to_carrier_meas
          Hmu_ball Hmu1 Hf_meas Hf_ge0 Hf_le1 mU).
Qed.

End SamplerInstance.
