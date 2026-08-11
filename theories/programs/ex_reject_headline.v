(**md**************************************************************************)
(** * Rejection sampling denotes the normalised posterior — the headline

    BEYOND THE PAPER.  This file is NOT part of the Ehrhard-Geoffroy
    2025 formalization (paper §2-§9).  It assembles the full semantic
    analysis of the rejection-sampling program [ex_reject] of
    [theories/programs/examples.v]
    [[
       let rec rs accept :=
         let x = sample m in
         if Bernoulli (Meas{f} x) then accept x else rs accept
       in rs (λ y. y)
    ]]
    under the CBV interpreter [eD] of [theories/programs/ppl_cbv.v]: a
    HIGHER-ORDER (the recursive function abstracts over the acceptance
    continuation), PROBABILISTIC (continuous [sample] + value-dependent
    coin [ne_bernoulli_f]), NON-TERMINATING (rejection recurses, and
    may loop forever) program, whose denotation we identify in closed
    form.

    Writing [ν := ⟦ex_reject⟧(one1) : FMeas R_obj],
    [If := ∫ f dµ] and [IUf U := ∫_U f dµ], the results are:

    - [ex_reject_master] : [If * ν(U) = IUf U]  — unconditionally
      (graceful at [If = 0]);
    - [ex_reject_is_normalised_posterior] : [0 < If] implies
      [ν(U) = IUf U / If]  — the normalised posterior of the prior [µ]
      given the soft acceptance predicate [f];
    - [ex_reject_posterior_simple] : [If = 1] implies [ν(U) = IUf U];
    - [ex_reject_mass_one] : [0 < If] implies [ν(setT) = 1] — the
      sampler terminates almost surely whenever acceptance has
      positive mass;
    - [ex_reject_zero] : [f ≡ 0] implies [ν = 0] — certain rejection
      diverges.

    The proof is the 6-step reduction chain of the plan:
    1. [ex_reject_app_E] — the outer application of the promoted
       fixpoint to the identity continuation collapses ([der ∘ prom]
       cancels BEFORE any continuity argument).
    2. [ex_reject_sup_E] — [ν] is the [cone_sup_ball] of the
       per-iterate measures [ν_n] (evaluation at a point commutes with
       the Kleene supremum: linhom-cone sups are pointwise).
    3. [ex_reject_iter_S] — the Kleene step: [ν_{n+1}] is the inner
       let-if body evaluated at the extended setlike environment.
    4. [ex_reject_inner_at_dirac] — at the environment [γ ⊗ δ_r] the
       branch dispatch computes: THEN gives [(f r)·δ_r], ELSE gives
       [(1 - f r)·ν_n] (the recursive call at the same continuation).
    5. [ex_reject_iter_mass] — the mass recurrence
       [ν_{n+1}(U) = IUf U + (1 - If)·ν_n(U)] via the let-at-sample
       Pettis integral law.
    6. The theorems, via the affine-cascade closed form
       ([theories/prelude/geom_series.v]) and the sup-mass bridge
       ([theories/mcones/fmeas.v]).

    Supporting kit (generic, owned by
    [theories/programs/infra/cbv_anchors.v]): [adj_psi_at_setlike] (the
    [U ⊣ !̃] packaging promotes at setlike points), [if_icones_at] (the
    if-then-else dispatch at setlike points), [eD_app_at_setlike] (the
    application clause there), [linhom_fun_sup_ball] (pointwise reading
    of the linhom-cone supremum; the ball-sup proof-irrelevance it
    rests on is [cone_sup_ball_irr] of
    [theories/cones/omega_general.v]), and [bool_case_mass] (the
    per-branch mass bookkeeping).

    The three sibling headline programs run the SAME skeleton and each
    lives in its own file: [theories/programs/ex_almost_loop.v] (the
    Bernoulli-guarded loop), [theories/programs/ex_geom.v] (the
    geometric counter) and [theories/programs/ex_even_odd.v] (the
    mutual-recursion witness).  The skeleton is documented here, once.

    See also: [theories/programs/infra/em_fix_value.v] (the seeded
    value-fixpoint combinator), [theories/programs/infra/
    cbv_fix_unfold.v] (the recursion-unfolding laws),
    [theories/programs/infra/let_sample_law.v] (the let-at-sample
    integral law), [theories/prelude/geom_series.v] (the scalar
    cascade), [theories/mcones/fmeas.v] (the sup-mass bridge and the
    mass bookkeeping [fmeas_int_*]),
    [theories/programs/infra/cbv_anchors.v] (the setlike kit).

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

Require Import Icones.prelude.geom_series.
Require Import Icones.cones.precone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.cone.
Require Import Icones.cones.cone_cat.
Require Import Icones.cones.omega_general.
Require Import Icones.icones.bool_cone.
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
Require Import Icones.homs.linhom_functor.
Require Import Icones.homs.bilin.
Require Import Icones.homs.tensor.
Require Import Icones.homs.tensor_construct.
Require Import Icones.homs.smcc.
Require Import Icones.exp.exp_adjunction.
Require Import Icones.exp.bang.
Require Import Icones.exp.seely_defs.
Require Import Icones.exp.seely.
Require Import Icones.homs.tensor_hom_iso.
Require Import Icones.exp.bool_case_hom.
Require Import Icones.exp.coalgebra.
Require Import Icones.programs.infra.bool_cone_coalg.
Require Import Icones.cbv.fmeas_lax.
Require Import Icones.cbv.em_cat.
Require Import Icones.cbv.em_seely_comonoid.
Require Import Icones.cbv.em_cartesian.
Require Import Icones.cbv.cbv_adjunction.
Require Import Icones.programs.ppl.
Require Import Icones.programs.infra.em_fix.
Require Import Icones.programs.infra.em_fix_mr.
Require Import Icones.programs.infra.em_fix_value.
Require Import Icones.programs.ppl_cbv.
Require Import Icones.programs.infra.cbv_anchors.
Require Import Icones.programs.infra.cbv_fix_unfold.
Require Import Icones.programs.infra.let_sample_law.
Require Import Icones.programs.examples.

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

(** ** §1 — Generic kit: MOVED

    The setlike computation laws and the pointwise-sup reading that
    used to open this file ([adj_psi_at_setlike], [if_icones_at],
    [linhom_fun_sup_ball], [eD_app_at_setlike]) are generic and are now
    owned by [theories/programs/infra/cbv_anchors.v] — the infra file
    both this rider and [theories/programs/ex_reject_model.v] already
    import.  Names and [Arguments] are unchanged. *)


(** ** §2 — The rejection-sampling reduction chain *)

Section RejectHeadline.
Variables (R : realType) (Ar : MeasSubcat R).
(* Reparameterized over the bundled [probObj]. *)
Variable (P : probObj Ar).
Local Notation R_obj := (po_robj P).
Local Notation R_carrier_eq := (po_robj_eq P).
Local Notation R_carrier_meas := (po_robj_meas P).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

(** The prior: a bundled sub-probability, assumed of unit mass. *)
Variable (m : pmeas Ar R_obj).
Local Notation mu := (pm_meas m).
Local Notation Hmu_ball := (pm_ball m).
Hypothesis Hmu1 : fmeas_mu mu [set: ar_carrier Ar R_obj] = 1%E.

(** The soft acceptance predicate: a BUNDLED [[0,1]]-valued test
    function.  The function carrier is supplied by the [test_fun]
    coercion, and the three proof projections are exposed under their
    historical names so the proof bodies below read unchanged. *)
Variable (f : testfn R).
Local Notation Hf_meas := (test_meas f).
Local Notation Hf_ge0 := (test_ge0 f).
Local Notation Hf_le1 := (test_le1 f).

(** The bundle factoring of [f] into the probability object, the
    clean [tProb]-coin map behind [Bernoulli (ToProb f #"x")]. *)
Local Notation rj_phi := (po_into P f Hf_meas Hf_ge0 Hf_le1).

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

(** *** Syntactic decomposition of [ex_reject] — all definitional

    The [let rec] surface form elaborates to a [ne_let] binding the
    fixpoint under ["rs"], whose continuation applies the bound
    recursive sampler to the identity acceptance continuation. *)

(** The identity acceptance continuation [λ y. y], in the [let rec]
    continuation context. *)
Definition reject_lam_id :
    @named_expr R Ar R_obj
      (("rs"%string, tfun (tfun tR' tR') tR') :: nil) (tfun tR' tR') :=
  [ \ "y" ::: tR' => # "y" ].

(** The test-and-dispatch body under the sample binder. *)
Definition reject_if :
    @named_expr R Ar R_obj
      (("x"%string, tR') :: ("accept"%string, tfun tR' tR') ::
       ("rs"%string, tfun (tfun tR' tR') tR') :: nil) tR' :=
  [ if Bernoulli (ToProb {rj_phi} # "x")
    then # "accept" @ # "x"
    else # "rs" @ # "accept" ].

Lemma ex_reject_decomp :
  ex_reject m f =
  ne_let "rs" (ne_fix "rs" (ex_reject_body m f))
    (ne_app (ne_var (nv_head "rs" (tfun (tfun tR' tR') tR') nil))
            reject_lam_id).
Proof. by []. Qed.

Lemma ex_reject_body_decomp :
  ex_reject_body m f =
  ne_lam "accept" (ex_reject_inner m f).
Proof. by []. Qed.

Lemma ex_reject_inner_decomp :
  ex_reject_inner m f =
  ne_let "x" (ne_sample mu Hmu_ball) reject_if.
Proof. by []. Qed.

(** The variable body of the identity continuation. *)
Definition reject_id_var :
    @named_expr R Ar R_obj
      (("y"%string, tR') ::
       ("rs"%string, tfun (tfun tR' tR') tR') :: nil) tR' :=
  [ # "y" ].

Lemma reject_lam_id_decomp : reject_lam_id = ne_lam "y" reject_id_var.
Proof. by []. Qed.

Let Hone : cone_norm (one1 : cone_one_car Ar) <= 1.
Proof. by rewrite one1_norm. Qed.

(** *** The semantic objects: the body's endo-function [W₀], the
    [let rec] environment, and the continuation value [a₀ = ℓ!] *)

(** [W₀ := curry ⟦body⟧ (one1) : !L₁ ⊸ !L₁] — the recursion body's
    endo-function at the closed environment ([L₁ := U⟦(R→R)→R⟧]). *)
Definition reject_W0 :
    linhom_car Ar (Bang Ar (Lty (tfun tR' tR') tR'))
                  (Bang Ar (Lty (tfun tR' tR') tR')) :=
  Lfun (tensor_curry
         (eD_cbv' (ex_reject_body m f)))
       one1.

Lemma reject_W0_ball : cone_norm reject_W0 <= 1.
Proof. exact: le_trans (cones_hom_norm_le1 _ _) Hone. Qed.

(** The promoted fixpoint value is a setlike unit-ball point. *)
Lemma reject_fix_prom_ball :
  cone_norm ((sc_fun (fix_value (Lty (tfun tR' tR') tR')) reject_W0)!) <= 1.
Proof. exact: (fix_value_prom_ball reject_W0_ball). Qed.

Lemma reject_fix_prom_setlike :
  Lfun (coalg_str (tyD_cbv (tfun (tfun tR' tR') tR')))
       ((sc_fun (fix_value (Lty (tfun tR' tR') tR')) reject_W0)!) =
  ((sc_fun (fix_value (Lty (tfun tR' tR') tR')) reject_W0)!)!.
Proof. exact: (fix_value_prom_setlike reject_W0_ball). Qed.

(** The [let rec] continuation environment: ["rs"] bound to the
    promoted fixpoint value. *)
Definition reject_env0 :
    coalg_obj (ctxD_cbv (drop_names
      (("rs"%string, tfun (tfun tR' tR') tR') :: nil))) :=
  one1 ⊗p (sc_fun (fix_value (Lty (tfun tR' tR') tR')) reject_W0)!.

Lemma reject_env0_ball : cone_norm reject_env0 <= 1.
Proof.
by rewrite /reject_env0 tensor_normME one1_norm mul1r reject_fix_prom_ball.
Qed.

Lemma reject_env0_setlike :
  Lfun (coalg_str (ctxD_cbv (drop_names
         (("rs"%string, tfun (tfun tR' tR') tR') :: nil))))
       reject_env0 = reject_env0!.
Proof.
exact: (coalg_str_tensor_setlike (P:=EM_term)
          (Q:=tyD_cbv (tfun (tfun tR' tR') tR'))
          Hone reject_fix_prom_ball coalg_str_one1
          reject_fix_prom_setlike).
Qed.

(** [ℓ] — the function value of the identity continuation: the linear
    map [⟦λy.y⟧] is closed over the [let rec] environment. *)
Definition reject_acc : Lty tR' tR' :=
  Lfun (tensor_curry (eD_cbv' reject_id_var)) reject_env0.

(** [a₀ := ℓ!] — the PROMOTED identity continuation, the function
    value the fixpoint is applied to. *)
Definition reject_arg : coalg_obj (tyD_cbv (tfun tR' tR')) := reject_acc!.

Lemma reject_acc_ball : cone_norm reject_acc <= 1.
Proof. exact: le_trans (cones_hom_norm_le1 _ _) reject_env0_ball. Qed.

(** [ℓ] IS the identity function on measures. *)
Lemma reject_acc_E (x : coalg_obj (tyD_cbv tR')) :
  linhom_fun reject_acc x = x.
Proof.
rewrite /reject_acc tensor_curryE.
apply: (eq_trans (y := Lfun (em_proj2_mor (R:=R)
  (ctxD_cbv (drop_names (("rs"%string, tfun (tfun tR' tR') tR') :: nil)))
  (FMeas_coalgebra R_obj)) (reject_env0 ⊗p x))).
  by [].
exact: (em_proj2_morE reject_env0_ball reject_env0_setlike).
Qed.

Lemma reject_arg_ball : cone_norm reject_arg <= 1.
Proof. exact: prom_ball reject_acc_ball. Qed.

(** [a₀] is a setlike point of the cofree function-type coalgebra. *)
Lemma reject_arg_setlike :
  Lfun (coalg_str (tyD_cbv (tfun tR' tR'))) reject_arg = reject_arg!.
Proof.
rewrite -[tyD_cbv (tfun tR' tR')]/(bang_cofree (Lty tR' tR'))
        bang_cofree_str /reject_arg.
exact: (dig_prom _ reject_acc_ball).
Qed.

Lemma reject_arg_E :
  Lfun (eD_cbv' reject_lam_id) reject_env0 = reject_arg.
Proof.
rewrite reject_lam_id_decomp eD_lam_E.
by rewrite (adj_psi_at_setlike (tensor_curry (eD_cbv' reject_id_var))
              reject_env0_ball reject_env0_setlike).
Qed.

(** *** Step 1 — the [let rec] binding collapses: the let pairs the
    promoted fixpoint value onto the environment, the head-variable
    lookup recovers it, and [der ∘ prom] cancels BEFORE any continuity
    argument, leaving the fixpoint VALUE applied to the (promoted)
    identity continuation. *)

Local Notation reject_denot :=
  (linhom_fun (ex_reject_cbv P R_to_carrier_meas m f) one1).

Lemma ex_reject_app_E :
  reject_denot =
  linhom_fun (sc_fun (fix_value (Lty (tfun tR' tR') tR')) reject_W0)
             reject_arg.
Proof.
rewrite /ex_reject_cbv /eD icones_to_linhomE ex_reject_decomp.
have HoneG : cone_norm
    (one1 : coalg_obj (ctxD_cbv (drop_names (nil : named_ctx Ar)))) <= 1.
  by rewrite one1_norm.
rewrite (eD_let_at_setlike "rs"
          (ne_fix "rs" (ex_reject_body m f))
          (ne_app (ne_var (nv_head "rs" (tfun (tfun tR' tR') tR') nil))
                  reject_lam_id)
          HoneG coalg_str_one1).
rewrite (eD_fix_at_setlike "rs"
          (ex_reject_body m f)
          HoneG coalg_str_one1).
rewrite (eD_app_at_setlike R_carrier_eq R_carrier_meas R_to_carrier_meas reject_env0_ball reject_env0_setlike).
rewrite (eD_var_head_at_setlike "rs"
          (t := tfun (tfun tR' tR') tR')
          ((sc_fun (fix_value (Lty (tfun tR' tR') tR')) reject_W0)!)
          HoneG coalg_str_one1).
rewrite reject_arg_E.
by rewrite (der_prom _ (fix_value_ball reject_W0 reject_W0_ball)).
Qed.

(** *** Step 2 — the denotation is the sup of the per-iterate measures

    [ν_n := (fix_chain W₀ n)(a₀)] — the n-th Kleene iterate of the
    recursion body, applied to the identity continuation. *)

Definition reject_iter (n : nat) : coalg_obj (tyD_cbv tR') :=
  linhom_fun (fix_chain reject_W0 n) reject_arg.

Lemma reject_iter_chain n : precone_le (reject_iter n) (reject_iter n.+1).
Proof.
exact: (linhom_le_pointwise (fix_chain_chain reject_W0_ball n) reject_arg).
Qed.

Lemma reject_iter_ball n : cone_norm (reject_iter n) <= 1.
Proof.
apply: le_trans
  (linhom_norm_apply_le (fix_chain_ball reject_W0_ball n) reject_arg) _.
by rewrite mul1r reject_arg_ball.
Qed.

(** Evaluation at [a₀] commutes with the Kleene supremum because
    linhom-cone sups are pointwise ([linhom_fun_sup_ball]). *)
Lemma ex_reject_sup_E :
  reject_denot =
  cone_sup_ball reject_iter reject_iter_chain reject_iter_ball.
Proof.
rewrite ex_reject_app_E (fix_value_E reject_W0_ball).
rewrite (linhom_fun_sup_ball (fix_chain_chain reject_W0_ball)
  (fix_chain_ball reject_W0_ball) reject_arg_ball
  reject_iter_chain reject_iter_ball).
by [].
Qed.

(** *** Step 3 — the Kleene step is the inner body at the extended
    setlike environment *)

Lemma fix_chain_prom_ball n :
  cone_norm ((fix_chain reject_W0 n)!) <= 1.
Proof. exact: (kleene_prom_ball reject_W0_ball n). Qed.

Lemma fix_chain_prom_setlike n :
  Lfun (coalg_str (tyD_cbv (tfun (tfun tR' tR') tR')))
       ((fix_chain reject_W0 n)!) = ((fix_chain reject_W0 n)!)!.
Proof. exact: (kleene_prom_setlike reject_W0_ball n). Qed.

(** The one-variable environment binding ["rs"] to the n-th promoted
    iterate is a setlike unit-ball point. *)
Lemma reject_env_ball n :
  cone_norm (one1 ⊗p (fix_chain reject_W0 n)!) <= 1.
Proof.
by rewrite tensor_normME one1_norm mul1r fix_chain_prom_ball.
Qed.

Lemma reject_env_setlike n :
  Lfun (coalg_str (ctxD_cbv (drop_names
         (("rs"%string, tfun (tfun tR' tR') tR') :: nil))))
       (one1 ⊗p (fix_chain reject_W0 n)!) =
  (one1 ⊗p (fix_chain reject_W0 n)!)!.
Proof.
exact: (coalg_str_tensor_setlike (P:=EM_term)
          (Q:=tyD_cbv (tfun (tfun tR' tR') tR'))
          Hone (fix_chain_prom_ball n) coalg_str_one1
          (fix_chain_prom_setlike n)).
Qed.

(** The recursion body at the promoted iterate: the [λaccept]-packaging
    PROMOTES the curried inner body at the extended environment. *)
Lemma reject_W0_at_prom n :
  linhom_fun reject_W0 ((fix_chain reject_W0 n)!) =
  (Lfun (tensor_curry
          (eD_cbv' (ex_reject_inner m f)))
     (one1 ⊗p (fix_chain reject_W0 n)!))!.
Proof.
rewrite {1}/reject_W0 tensor_curryE ex_reject_body_decomp eD_lam_E.
exact: (adj_psi_at_setlike
  (P:=ctxD_cbv (drop_names (("rs"%string, tfun (tfun tR' tR') tR') :: nil)))
  _ (reject_env_ball n) (reject_env_setlike n)).
Qed.

Lemma ex_reject_iter_S n :
  reject_iter n.+1 =
  Lfun (eD_cbv' (ex_reject_inner m f))
       ((one1 ⊗p (fix_chain reject_W0 n)!) ⊗p reject_arg).
Proof.
rewrite /reject_iter fix_chain_S reject_W0_at_prom.
rewrite (der_prom _ (le_trans (cones_hom_norm_le1 _ _)
                              (reject_env_ball n))).
exact: tensor_curryE.
Qed.

(** *** Step 4 — the inner if-body at the Dirac environment

    At the environment [γ_n ⊗ a₀ ⊗ δ_r] the branch dispatch computes:
    the scrutinee is [Bernoulli (f r)], the THEN branch returns the
    accepted sample [δ_r] (the identity continuation applied to the
    bound variable), the ELSE branch is the RECURSIVE CALL at the same
    continuation — which is exactly the previous iterate [ν_n]. *)

(** The three variables of [reject_if], as standalone terms. *)
Definition reject_var_x :
    @named_expr R Ar R_obj
      (("x"%string, tR') :: ("accept"%string, tfun tR' tR') ::
       ("rs"%string, tfun (tfun tR' tR') tR') :: nil) tR' :=
  [ # "x" ].

Definition reject_var_acc :
    @named_expr R Ar R_obj
      (("x"%string, tR') :: ("accept"%string, tfun tR' tR') ::
       ("rs"%string, tfun (tfun tR' tR') tR') :: nil) (tfun tR' tR') :=
  [ # "accept" ].

Definition reject_var_rs :
    @named_expr R Ar R_obj
      (("x"%string, tR') :: ("accept"%string, tfun tR' tR') ::
       ("rs"%string, tfun (tfun tR' tR') tR') :: nil)
      (tfun (tfun tR' tR') tR') :=
  [ # "rs" ].

(** The clean coin's underlying [tProb] argument: the acceptance
    test function [f] pushed through the bundle factoring [po_into] at
    the sampled variable. *)
Local Notation reject_coin_arg := (ne_to_prob rj_phi reject_var_x).

Lemma reject_if_decomp :
  reject_if =
  ne_if tR' (ne_bernoulli_p (po_density P) (po_density_meas P)
               (po_ge0 P) (po_le1 P) reject_coin_arg)
        (ne_app reject_var_acc reject_var_x)
        (ne_app reject_var_rs reject_var_acc).
Proof. by []. Qed.

(** The inner-let context point [γ_n ⊗ a₀] and its Dirac extension. *)
Definition reject_env2 (n : nat) :
    coalg_obj (ctxD_cbv (drop_names
      (("accept"%string, tfun tR' tR') ::
       ("rs"%string, tfun (tfun tR' tR') tR') :: nil))) :=
  (one1 ⊗p (fix_chain reject_W0 n)!) ⊗p reject_arg.

Definition reject_env3 (n : nat) (r : ar_carrier Ar R_obj) :
    coalg_obj (ctxD_cbv (drop_names
      (("x"%string, tR') :: ("accept"%string, tfun tR' tR') ::
       ("rs"%string, tfun (tfun tR' tR') tR') :: nil))) :=
  reject_env2 n ⊗p dirac_fmeas r.

Lemma reject_env2_ball n : cone_norm (reject_env2 n) <= 1.
Proof.
rewrite /reject_env2 tensor_normME.
by rewrite mulr_ile1 ?cone_norm_ge0 ?reject_env_ball ?reject_arg_ball.
Qed.

Lemma reject_env2_setlike n :
  Lfun (coalg_str (ctxD_cbv (drop_names
         (("accept"%string, tfun tR' tR') ::
          ("rs"%string, tfun (tfun tR' tR') tR') :: nil))))
       (reject_env2 n) = (reject_env2 n)!.
Proof.
exact: (coalg_str_tensor_setlike
          (P:=ctxD_cbv (drop_names
                (("rs"%string, tfun (tfun tR' tR') tR') :: nil)))
          (Q:=tyD_cbv (tfun tR' tR'))
          (reject_env_ball n) reject_arg_ball
          (reject_env_setlike n) reject_arg_setlike).
Qed.

Lemma reject_env3_ball n r : cone_norm (reject_env3 n r) <= 1.
Proof.
rewrite /reject_env3 tensor_normME.
by rewrite mulr_ile1 ?cone_norm_ge0 ?reject_env2_ball ?dirac_fmeas_norm_le1.
Qed.

Lemma reject_env3_setlike n r :
  Lfun (coalg_str (ctxD_cbv (drop_names
         (("x"%string, tR') :: ("accept"%string, tfun tR' tR') ::
          ("rs"%string, tfun (tfun tR' tR') tR') :: nil))))
       (reject_env3 n r) = (reject_env3 n r)!.
Proof.
exact: (coalg_str_tensor_setlike
          (P:=ctxD_cbv (drop_names
                (("accept"%string, tfun tR' tR') ::
                 ("rs"%string, tfun (tfun tR' tR') tR') :: nil)))
          (Q:=FMeas_coalgebra R_obj)
          (reject_env2_ball n) (dirac_fmeas_norm_le1 r)
          (reject_env2_setlike n) (Coalg_dirac R_obj r)).
Qed.

(** The variable projections at the Dirac environment. *)
Lemma reject_var_x_E n r :
  Lfun (eD_cbv' reject_var_x) (reject_env3 n r) = dirac_fmeas r.
Proof.
apply: (eq_trans (y := Lfun (em_proj2_mor (R:=R)
  (ctxD_cbv (drop_names
     (("accept"%string, tfun tR' tR') ::
      ("rs"%string, tfun (tfun tR' tR') tR') :: nil)))
  (FMeas_coalgebra R_obj)) (reject_env3 n r))).
  by [].
exact: (em_proj2_morE (reject_env2_ball n) (reject_env2_setlike n)).
Qed.

Lemma reject_var_acc_E n r :
  Lfun (eD_cbv' reject_var_acc) (reject_env3 n r) = reject_arg.
Proof.
apply: (eq_trans (y := Lfun (icones_comp
  (em_proj2_mor (R:=R)
     (ctxD_cbv (drop_names
        (("rs"%string, tfun (tfun tR' tR') tR') :: nil)))
     (tyD_cbv (tfun tR' tR')))
  (em_proj1_mor (R:=R)
     (ctxD_cbv (drop_names
        (("accept"%string, tfun tR' tR') ::
         ("rs"%string, tfun (tfun tR' tR') tR') :: nil)))
     (FMeas_coalgebra R_obj))) (reject_env3 n r))).
  by [].
rewrite Lfun_comp.
rewrite (em_proj1_morE (Q:=FMeas_coalgebra R_obj)
           (dirac_fmeas_norm_le1 r) (Coalg_dirac R_obj r)).
exact: (em_proj2_morE (P:=ctxD_cbv (drop_names
          (("rs"%string, tfun (tfun tR' tR') tR') :: nil)))
          (reject_env_ball n) (reject_env_setlike n)).
Qed.

Lemma reject_var_rs_E n r :
  Lfun (eD_cbv' reject_var_rs) (reject_env3 n r) =
  (fix_chain reject_W0 n)!.
Proof.
apply: (eq_trans (y := Lfun (icones_comp
  (icones_comp
    (em_proj2_mor (R:=R) EM_term (tyD_cbv (tfun (tfun tR' tR') tR')))
    (em_proj1_mor (R:=R)
       (ctxD_cbv (drop_names
          (("rs"%string, tfun (tfun tR' tR') tR') :: nil)))
       (tyD_cbv (tfun tR' tR'))))
  (em_proj1_mor (R:=R)
     (ctxD_cbv (drop_names
        (("accept"%string, tfun tR' tR') ::
         ("rs"%string, tfun (tfun tR' tR') tR') :: nil)))
     (FMeas_coalgebra R_obj))) (reject_env3 n r))).
  by [].
rewrite Lfun_comp Lfun_comp.
rewrite (em_proj1_morE (Q:=FMeas_coalgebra R_obj)
           (dirac_fmeas_norm_le1 r) (Coalg_dirac R_obj r)).
rewrite (em_proj1_morE (Q:=tyD_cbv (tfun tR' tR'))
           reject_arg_ball reject_arg_setlike).
exact: (em_proj2_morE (P:=EM_term) Hone coalg_str_one1).
Qed.

(** The scrutinee at [δ_r] is the [f r]-coin (the bundled
    [ne_bernoulli_f] node desugared directly — no clamp transport —
    then [bern_lift_dirac]). *)
Lemma reject_scrut_E n r :
  Lfun (eD_cbv' (ne_bernoulli_p (po_density P) (po_density_meas P)
                   (po_ge0 P) (po_le1 P) reject_coin_arg))
       (reject_env3 n r) =
  bernoulli (f (cR r)) (Hf_ge0 (cR r)) (Hf_le1 (cR r)).
Proof.
(* Clean-surface coin leaf: push the sampled real through the bundle
   factoring [po_into f] and read off the [f r]-coin with
   [bern_lift_P]; [po_into_E] recovers [f r]. *)
rewrite eD_bernoulli_p_E Lfun_comp.
rewrite -[bern_lift_g _ _ _]/(bern_lift_P P).
rewrite eD_to_prob_E Lfun_comp.
rewrite reject_var_x_E FMeas_fmap_dirac bern_lift_P_dirac.
apply: bool_cone_eq; apply: val_inj => /=; by rewrite /po_density po_into_E.
Qed.

(** THEN: the identity continuation applied to the bound sample. *)
Lemma reject_then_E n r :
  Lfun (eD_cbv' (ne_app reject_var_acc reject_var_x)) (reject_env3 n r) =
  dirac_fmeas r.
Proof.
rewrite (eD_app_at_setlike R_carrier_eq R_carrier_meas R_to_carrier_meas (reject_env3_ball n r)
           (reject_env3_setlike n r)).
rewrite reject_var_acc_E reject_var_x_E.
rewrite (der_prom _ reject_acc_ball).
exact: reject_acc_E.
Qed.

(** ELSE: the recursive call at the same continuation IS the previous
    iterate. *)
Lemma reject_else_E n r :
  Lfun (eD_cbv' (ne_app reject_var_rs reject_var_acc)) (reject_env3 n r) =
  reject_iter n.
Proof.
rewrite (eD_app_at_setlike R_carrier_eq R_carrier_meas R_to_carrier_meas (reject_env3_ball n r)
           (reject_env3_setlike n r)).
rewrite reject_var_rs_E reject_var_acc_E.
by rewrite (der_prom _ (fix_chain_ball reject_W0_ball n)).
Qed.

Lemma ex_reject_inner_at_dirac n r :
  Lfun (eD_cbv' reject_if) (reject_env3 n r) =
  bool_case (bernoulli (Ar:=Ar) (f (cR r)) (Hf_ge0 (cR r)) (Hf_le1 (cR r)))
            (dirac_fmeas r) (reject_iter n).
Proof.
rewrite reject_if_decomp eD_if_E.
rewrite (if_icones_at
  (eD_cbv' (ne_app reject_var_acc reject_var_x))
  (eD_cbv' (ne_app reject_var_rs reject_var_acc))
  (eD_cbv' (ne_bernoulli_p (po_density P) (po_density_meas P)
              (po_ge0 P) (po_le1 P) reject_coin_arg))
  (reject_env3_ball n r) (reject_env3_setlike n r)).
by rewrite reject_scrut_E reject_then_E reject_else_E.
Qed.

(** *** Step 5 — the mass recurrence

    [ν_{n+1}(U) = ∫_U f dµ + (1 - ∫ f dµ) · ν_n(U)] via the
    let-at-sample Pettis integral law, with the acceptance and
    rejection weights accounted by [∫(1-f) dµ = 1 - ∫f dµ] (the prior
    has unit mass). *)

Local Open Scope ereal_scope.

(** [If] / [IUf U] abbreviate the acceptance-mass integrals in the
    PROOFS only ([only parsing]); the headline STATEMENTS below spell the
    integrals out explicitly so the reader sees the real measure
    [fmeas_mu mu] and integrand [(f (cR ·))%:E]. *)
Local Notation If :=
  (\int[fmeas_mu mu]_(r in [set: ar_carrier Ar R_obj]) (f (cR r))%:E)
  (only parsing).
Local Notation IUf U :=
  (\int[fmeas_mu mu]_(r in U) (f (cR r))%:E) (only parsing).

Let f_cR_meas : measurable_fun [set: ar_carrier Ar R_obj]
    (fun r => f (cR r)).
Proof. exact: (bern_f_cR_meas R_carrier_meas Hf_meas). Qed.

(** The acceptance-mass bookkeeping is the generic one of
    [theories/mcones/fmeas.v] (Section
    [MassBookkeeping]) at [ν := µ] and [g := f ∘ cR]; the prior's unit
    mass [Hmu1] is the only place the headline is more special than the
    model rider, and it enters exactly by turning the generic [ν(setT)]
    into [1]. *)

Let f_cR_ge0 r : (0 <= f (cR r))%R.
Proof. exact: Hf_ge0. Qed.

Let f_cR_le1 r : (f (cR r) <= 1)%R.
Proof. exact: Hf_le1. Qed.

Lemma reject_If_ge0 : 0 <= If.
Proof. exact: (fmeas_int_ge0 mu f_cR_ge0). Qed.

Lemma reject_If_le1 : If <= 1.
Proof.
by have := fmeas_int_le_mass mu f_cR_ge0 f_cR_le1 f_cR_meas; rewrite Hmu1.
Qed.

Lemma reject_If_fin : If \is a fin_num.
Proof. exact: (fmeas_int_fin mu f_cR_ge0 f_cR_le1 f_cR_meas). Qed.

Lemma reject_IUf_ge0 U : measurable U -> 0 <= IUf U.
Proof. exact: (fmeas_intU_ge0 mu f_cR_ge0). Qed.

Lemma reject_IUf_le_If U : measurable U -> IUf U <= If.
Proof. exact: (fmeas_intU_le mu f_cR_ge0 f_cR_meas). Qed.

Lemma reject_IUf_fin U : measurable U -> IUf U \is a fin_num.
Proof. exact: (fmeas_intU_fin mu f_cR_ge0 f_cR_le1 f_cR_meas). Qed.

(** The rejection weight: [∫ (1 - f) dµ = 1 - ∫ f dµ] at [µ(setT)=1]. *)
Lemma reject_int_onem :
  \int[fmeas_mu mu]_(r in [set: ar_carrier Ar R_obj])
     ((1 - f (cR r))%R)%:E = ((1 - fine If)%R)%:E.
Proof.
have Honem_ge0 r : (0 <= 1 - f (cR r))%R by rewrite subr_ge0 Hf_le1.
have Honem_meas : measurable_fun [set: ar_carrier Ar R_obj]
    (fun r => (1 - f (cR r))%R).
  by apply: measurable_funB => //; exact: f_cR_meas.
have Hsum r : (f (cR r) + (1 - f (cR r)))%R = 1%R.
  by rewrite addrCA subrr addr0.
rewrite (fmeas_int_compl mu f_cR_ge0 f_cR_le1 f_cR_meas
           (fun r => (1 - f (cR r))%R) Honem_ge0 Honem_meas Hsum).
by rewrite Hmu1.
Qed.

(** The mass of one branch dispatch — the generic [bool_case_mass] of
    [theories/programs/infra/cbv_anchors.v] at a [bernoulli] scrutinee,
    whose [bc_t]/[bc_f] read as [f (cR r)] / [1 - f (cR r)]. *)
Lemma reject_case_mass n r U (mU : measurable U) :
  fmeas_mu (bool_case
    (bernoulli (Ar:=Ar) (f (cR r)) (Hf_ge0 (cR r)) (Hf_le1 (cR r)))
    (dirac_fmeas r) (reject_iter n)) U =
  ((f (cR r) * \1_U r + (1 - f (cR r)) *
      fine (fmeas_mu (reject_iter n) U))%R)%:E.
Proof.
exact: (bool_case_mass
  (bernoulli (Ar:=Ar) (f (cR r)) (Hf_ge0 (cR r)) (Hf_le1 (cR r)))
  r (reject_iter n) mU).
Qed.

Lemma ex_reject_iter_mass n U (mU : measurable U) :
  fmeas_mu (reject_iter n.+1) U =
  IUf U + ((1 - fine If)%R)%:E * fmeas_mu (reject_iter n) U.
Proof.
have Hiter : reject_iter n.+1 =
    linhom_fun (eD' (ne_let "x"%string (ne_sample mu Hmu_ball) reject_if))
               (reject_env2 n).
  rewrite ex_reject_iter_S ex_reject_inner_decomp.
  by rewrite /eD icones_to_linhomE.
rewrite Hiter.
rewrite (eD_let_sample_mu_E R_carrier_meas R_to_carrier_meas Hmu_ball
           reject_if (reject_env2 n) mU).
set c := fine (fmeas_mu (reject_iter n) U).
under eq_integral => r _.
  rewrite ex_reject_inner_at_dirac (reject_case_mass n r mU)/= EFinD.
  over.
have Hc0 : (0 <= c)%R by rewrite /c fine_ge0// measure_ge0.
have m1 : measurable_fun [set: ar_carrier Ar R_obj]
    (fun r => ((f (cR r) * \1_U r)%R)%:E).
  apply/measurable_EFinP; apply: measurable_funM => //.
have m2 : measurable_fun [set: ar_carrier Ar R_obj]
    (fun r => (((1 - f (cR r)) * fine (fmeas_mu (reject_iter n) U))%R)%:E).
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
  rewrite reject_int_onem.
  by rewrite (fineK (fmeas_fin (reject_iter n) U mU)).
Qed.

(** *** Step 6 — the headline theorems *)

Lemma reject_iter_0 : reject_iter 0 = precone_zero.
Proof. by rewrite /reject_iter fix_chain_0 linhom_fun_zero. Qed.

Lemma reject_iter_0_mass U : fmeas_mu (reject_iter 0) U = 0.
Proof.
have -> : (reject_iter 0 : fmeas R (ar_carrier Ar R_obj)) = fmeas_zero.
  by rewrite reject_iter_0.
exact: fmeas_zeroE.
Qed.

(** Main result: when acceptance has positive mass, rejection
    sampling denotes the NORMALISED POSTERIOR
    [ν(U) = (∫_U f dµ) / (∫ f dµ)]. *)
Theorem ex_reject_is_normalised_posterior :
  0 < \int[fmeas_mu mu]_(x in [set: ar_carrier Ar R_obj]) ((f (cR x))%:E) ->
  forall U, measurable U ->
  fmeas_mu reject_denot U =
  ((fine (\int[fmeas_mu mu]_(x in U) ((f (cR x))%:E))
    / fine (\int[fmeas_mu mu]_(x in [set: ar_carrier Ar R_obj])
              ((f (cR x))%:E)))%R)%:E.
Proof.
move=> HIf U mU.
rewrite ex_reject_sup_E.
pose x := fun n => fine (fmeas_mu (reject_iter n) U).
have Hx0 : x 0%N = 0%R by rewrite /x reject_iter_0_mass.
have HxS : forall n,
    x n.+1 = (fine (IUf U) + (1 - fine If) * x n)%R.
  move=> n; rewrite /x (ex_reject_iter_mass n mU).
  rewrite fineD ?reject_IUf_fin//; last first.
    by rewrite fin_numM// (fmeas_fin (reject_iter n) U mU).
  by rewrite fineM// (fmeas_fin (reject_iter n) U mU).
have Hq0 : (0 <= 1 - fine If)%R.
  by rewrite subr_ge0 -lee_fin (fineK reject_If_fin) reject_If_le1.
have Hq1 : (1 - fine If < 1)%R.
  rewrite ltrBlDr ltrDl.
  by rewrite fine_gt0// HIf/= (le_lt_trans reject_If_le1)// ltey.
have Hcvg := affine_iter_cvg (fine (IUf U)) (1 - fine If) Hq0 Hx0 HxS Hq1.
apply: (fmeas_kleene_sup_U_E reject_iter_chain reject_iter_ball mU).
have HE : (fun n => fmeas_mu (reject_iter n) U) = (fun n => (x n)%:E).
  by apply/funext => n; rewrite /x fineK// (fmeas_fin (reject_iter n) U mU).
rewrite HE.
by rewrite -[in X in _ --> X](subKr 1 (fine If)).
Qed.

(** The division-free master form — unconditional, graceful at
    [∫ f dµ = 0]. *)
Theorem ex_reject_master U : measurable U ->
  \int[fmeas_mu mu]_(x in [set: ar_carrier Ar R_obj]) ((f (cR x))%:E)
    * fmeas_mu reject_denot U
  = \int[fmeas_mu mu]_(x in U) ((f (cR x))%:E).
Proof.
move=> mU.
have := reject_If_ge0; rewrite le_eqVlt => /orP[/eqP HIf0 | HIfpos].
- rewrite -HIf0 mul0e.
  apply/esym/eqP; rewrite eq_le reject_IUf_ge0// andbT.
  by rewrite (le_trans (reject_IUf_le_If mU))// -HIf0.
- rewrite (ex_reject_is_normalised_posterior HIfpos mU).
  have HfI_neq0 : fine If != 0%R.
    by rewrite gt_eqF// fine_gt0// HIfpos/=
       (le_lt_trans reject_If_le1)// ltey.
  rewrite -{1}(fineK reject_If_fin) -EFinM.
  by rewrite mulrC mulfVK// (fineK (reject_IUf_fin mU)).
Qed.

(** When the acceptance density already integrates to [1], the
    denotation is the un-normalised reweighted prior itself. *)
Theorem ex_reject_posterior_simple :
  \int[fmeas_mu mu]_(x in [set: ar_carrier Ar R_obj]) ((f (cR x))%:E) = 1 ->
  forall U, measurable U ->
  fmeas_mu reject_denot U = \int[fmeas_mu mu]_(x in U) ((f (cR x))%:E).
Proof.
move=> HIf1 U mU.
by rewrite -(ex_reject_master mU) HIf1 mul1e.
Qed.

(** Almost-sure termination: positive acceptance mass gives a
    PROBABILITY distribution. *)
Theorem ex_reject_mass_one :
  0 < \int[fmeas_mu mu]_(x in [set: ar_carrier Ar R_obj]) ((f (cR x))%:E) ->
  fmeas_mu reject_denot [set: ar_carrier Ar R_obj] = 1.
Proof.
move=> HIf.
rewrite (ex_reject_is_normalised_posterior HIf measurableT).
rewrite divff// ?gt_eqF// fine_gt0// HIf/=.
by rewrite (le_lt_trans reject_If_le1)// ltey.
Qed.

(** Certain rejection diverges: at [f ≡ 0] the denotation is the zero
    measure. *)
Theorem ex_reject_zero :
  (forall r : R, f r = 0%R) -> reject_denot = precone_zero.
Proof.
move=> Hf0.
have HIUf0 : forall U : set (ar_carrier Ar R_obj), IUf U = 0.
  move=> U.
  under eq_integral => r _ do rewrite Hf0.
  exact: integral0.
have Hmass : forall n (U : set (ar_carrier Ar R_obj)),
    measurable U -> fmeas_mu (reject_iter n) U = 0.
  elim=> [ | n IH] U mU; first exact: reject_iter_0_mass.
  by rewrite (ex_reject_iter_mass n mU) IH// mule0 adde0 HIUf0.
apply: fmeas_eq => U mU.
rewrite ex_reject_sup_E.
rewrite (fmeas_kleene_sup_U_E reject_iter_chain reject_iter_ball mU
          (l := 0)).
  by rewrite -[precone_zero]/(fmeas_zero : fmeas R (ar_carrier Ar R_obj))
       fmeas_zeroE.
have HE : (fun n => fmeas_mu (reject_iter n) U) = (fun n => (0 : \bar R)).
  by apply/funext => n; rewrite Hmass.
rewrite HE.
exact: cvg_cst.
Qed.

End RejectHeadline.
