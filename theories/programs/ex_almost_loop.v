(**md*** [ex_almost_loop] — escape with probability one

    BEYOND THE PAPER.  This file is NOT part of the Ehrhard-Geoffroy
    2025 formalization (paper §2-§9).  It is one headline CBV program
    of the chapter; the six-step reduction-chain skeleton it runs on is
    documented once, for the rejection sampler, in
    [theories/programs/ex_reject_headline.v].

    The program is the Bernoulli-guarded loop of
    [theories/programs/examples.v]
    [[
       (let rec l = λ_. if Bernoulli(p) then () else l ()) ()
    ]]
    (no [sample] inside the iterate): the denotation at [tunit] is a
    scalar (a point of the unit cone), whose mass is the termination
    probability.  Dichotomy: [0 < p] gives mass [1] (almost-sure
    termination), [p = 0] gives the zero point (certain divergence).

    Results:
    - [ex_almost_loop_cbv_mass_one] : [0 < p] implies the denotation
      has mass [1];
    - [ex_almost_loop_cbv_dirac] : [0 < p] implies it *is* [one1] (the
      unit cone is one-dimensional, so mass one pins the point);
    - [ex_almost_loop_cbv_zero] : [p = 0] gives [precone_zero].

    Supporting kit: [theories/programs/infra/cbv_anchors.v] (the
    setlike-point kit), [theories/programs/infra/em_fix_value.v] (the
    seeded value-fixpoint combinator),
    [theories/programs/infra/cbv_fix_unfold.v] (the
    recursion-unfolding laws), [theories/prelude/geom_series.v] (the
    scalar affine cascade).

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

Section AlmostLoopRider.
Variables (R : realType) (Ar : MeasSubcat R).
(* Reparameterized over the bundled [probObj]: the real object and its
   carrier casts come from [P], the clean [tProb] surface's bundle. *)
Variable (P : probObj Ar).
Local Notation R_obj := (po_robj P).
Local Notation R_carrier_eq := (po_robj_eq P).
Local Notation R_carrier_meas := (po_robj_meas P).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

(** The divergence parameter as a BUNDLED probability; its scalar and
    bounds are exposed under their historical names. *)
Variable (pr : prob R).
Local Notation p := (pr_val pr).
Local Notation Hp0 := (pr_ge0 pr).
Local Notation Hp1 := (pr_le1 pr).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '!'" := (prom x) (at level 2, format "x '!'").
Local Notation eD_cbv' :=
  (@eD_cbv R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation eD' :=
  (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation Lty t1 t2 :=
  (linhom_car Ar (coalg_obj (tyD_cbv t1)) (coalg_obj (tyD_cbv t2))).

(** *** Syntactic decomposition *)

Definition al_var_l :
    @named_expr R Ar R_obj
      (("_"%string, tunit) :: ("l"%string, tfun tunit tunit) :: nil)
      (tfun tunit tunit) :=
  [ # "l" ].

Definition al_if :
    @named_expr R Ar R_obj
      (("_"%string, tunit) :: ("l"%string, tfun tunit tunit) :: nil)
      tunit :=
  [ if Bernoulli (Const pr [| 0%R |]) then () else # "l" @ () ].

Lemma ex_almost_loop_decomp :
  ex_almost_loop (P := P) pr =
  ne_let "l" (ne_fix "l" (ex_almost_loop_body (P := P) pr))
    (ne_app (ne_var (nv_head "l" (tfun tunit tunit) nil)) ne_tt).
Proof. by []. Qed.

Lemma ex_almost_loop_body_decomp :
  ex_almost_loop_body (P := P) pr = ne_lam "_" al_if.
Proof. by []. Qed.

(** The clean coin's underlying [tProb] argument: the constant
    [pr_val pr] pushed through the bundle's factoring [po_into] at the
    real literal [0]. *)
Local Notation al_coin_arg :=
  (ne_to_prob (po_into P (cst (pr_val pr)) (measurable_cst (pr_val pr))
                 (fun=> pr_ge0 pr) (fun=> pr_le1 pr)) (ne_real 0%R)).

Lemma al_if_decomp :
  al_if = ne_if tunit
            (ne_bernoulli_p (po_density P) (po_density_meas P)
               (po_ge0 P) (po_le1 P) al_coin_arg)
            ne_tt
            (ne_app al_var_l ne_tt).
Proof. by []. Qed.

Let Hone : cone_norm (one1 : cone_one_car Ar) <= 1.
Proof. by rewrite one1_norm. Qed.

(** *** The reduction chain (steps 1-4, mirrored) *)

Definition al_W0 :
    linhom_car Ar (Bang Ar (Lty tunit tunit))
                  (Bang Ar (Lty tunit tunit)) :=
  Lfun (tensor_curry (eD_cbv' (ex_almost_loop_body (P := P) pr)))
       one1.

Lemma al_W0_ball : cone_norm al_W0 <= 1.
Proof. exact: le_trans (cones_hom_norm_le1 _ _) Hone. Qed.

(** The promoted fixpoint value is a setlike unit-ball point, so the
    [let rec] continuation environment is one too. *)
Lemma al_fix_prom_ball :
  cone_norm ((sc_fun (fix_value (Lty tunit tunit)) al_W0)!) <= 1.
Proof. exact: (fix_value_prom_ball al_W0_ball). Qed.

Lemma al_fix_prom_setlike :
  Lfun (coalg_str (tyD_cbv (tfun tunit tunit)))
       ((sc_fun (fix_value (Lty tunit tunit)) al_W0)!) =
  ((sc_fun (fix_value (Lty tunit tunit)) al_W0)!)!.
Proof. exact: (fix_value_prom_setlike al_W0_ball). Qed.

Definition al_env0 :
    coalg_obj (ctxD_cbv (drop_names
      (("l"%string, tfun tunit tunit) :: nil))) :=
  one1 ⊗p (sc_fun (fix_value (Lty tunit tunit)) al_W0)!.

Lemma al_env0_ball : cone_norm al_env0 <= 1.
Proof.
by rewrite /al_env0 tensor_normME one1_norm mul1r al_fix_prom_ball.
Qed.

Lemma al_env0_setlike :
  Lfun (coalg_str (ctxD_cbv (drop_names
         (("l"%string, tfun tunit tunit) :: nil)))) al_env0 = al_env0!.
Proof.
exact: (coalg_str_tensor_setlike (P:=EM_term)
          (Q:=tyD_cbv (tfun tunit tunit))
          Hone al_fix_prom_ball coalg_str_one1 al_fix_prom_setlike).
Qed.

Definition al_iter (n : nat) : cone_one_car Ar :=
  linhom_fun (fix_chain al_W0 n) one1.

Lemma al_iter_chain n : precone_le (al_iter n) (al_iter n.+1).
Proof.
exact: (linhom_le_pointwise (fix_chain_chain al_W0_ball n) one1).
Qed.

Lemma al_iter_ball n : cone_norm (al_iter n) <= 1.
Proof.
apply: le_trans
  (linhom_norm_apply_le (fix_chain_ball al_W0_ball n) one1) _.
by rewrite mul1r Hone.
Qed.

Local Notation al_denot :=
  (linhom_fun (ex_almost_loop_cbv P R_to_carrier_meas pr)
     one1).

Lemma ex_almost_loop_app_E :
  al_denot =
  linhom_fun (sc_fun (fix_value (Lty tunit tunit)) al_W0) one1.
Proof.
rewrite /ex_almost_loop_cbv /eD icones_to_linhomE ex_almost_loop_decomp.
have HoneG : cone_norm
    (one1 : coalg_obj (ctxD_cbv (drop_names (nil : named_ctx Ar)))) <= 1.
  by rewrite one1_norm.
rewrite (eD_let_at_setlike "l"
          (ne_fix "l" (ex_almost_loop_body (P := P) pr))
          (ne_app (ne_var (nv_head "l" (tfun tunit tunit) nil)) ne_tt)
          HoneG coalg_str_one1).
rewrite (eD_fix_at_setlike "l" (ex_almost_loop_body (P := P) pr)
          HoneG coalg_str_one1).
rewrite (eD_app_at_setlike R_carrier_eq R_carrier_meas R_to_carrier_meas al_env0_ball al_env0_setlike).
rewrite (eD_var_head_at_setlike "l"
          (t := tfun tunit tunit)
          ((sc_fun (fix_value (Lty tunit tunit)) al_W0)!)
          HoneG coalg_str_one1).
rewrite (eD_tt_at_setlike al_env0_ball al_env0_setlike).
by rewrite (der_prom _ (fix_value_ball al_W0 al_W0_ball)).
Qed.

Lemma ex_almost_loop_sup_E :
  al_denot = cone_sup_ball al_iter al_iter_chain al_iter_ball.
Proof.
rewrite ex_almost_loop_app_E (fix_value_E al_W0_ball).
rewrite (linhom_fun_sup_ball (fix_chain_chain al_W0_ball)
  (fix_chain_ball al_W0_ball) Hone al_iter_chain al_iter_ball).
by [].
Qed.

Lemma al_chain_prom_ball n : cone_norm ((fix_chain al_W0 n)!) <= 1.
Proof. exact: (kleene_prom_ball al_W0_ball n). Qed.

Lemma al_chain_prom_setlike n :
  Lfun (coalg_str (tyD_cbv (tfun tunit tunit)))
       ((fix_chain al_W0 n)!) = ((fix_chain al_W0 n)!)!.
Proof. exact: (kleene_prom_setlike al_W0_ball n). Qed.

Lemma al_env_ball n :
  cone_norm (one1 ⊗p (fix_chain al_W0 n)!) <= 1.
Proof.
by rewrite tensor_normME one1_norm mul1r al_chain_prom_ball.
Qed.

Lemma al_env_setlike n :
  Lfun (coalg_str (ctxD_cbv (drop_names
         (("l"%string, tfun tunit tunit) :: nil))))
       (one1 ⊗p (fix_chain al_W0 n)!) =
  (one1 ⊗p (fix_chain al_W0 n)!)!.
Proof.
exact: (coalg_str_tensor_setlike (P:=EM_term)
          (Q:=tyD_cbv (tfun tunit tunit))
          Hone (al_chain_prom_ball n) coalg_str_one1
          (al_chain_prom_setlike n)).
Qed.

Lemma al_W0_at_prom n :
  linhom_fun al_W0 ((fix_chain al_W0 n)!) =
  (Lfun (tensor_curry (eD_cbv' al_if))
     (one1 ⊗p (fix_chain al_W0 n)!))!.
Proof.
rewrite {1}/al_W0 tensor_curryE ex_almost_loop_body_decomp eD_lam_E.
exact: (adj_psi_at_setlike
  (P:=ctxD_cbv (drop_names (("l"%string, tfun tunit tunit) :: nil)))
  _ (al_env_ball n) (al_env_setlike n)).
Qed.

Lemma ex_almost_loop_iter_S n :
  al_iter n.+1 =
  Lfun (eD_cbv' al_if)
       ((one1 ⊗p (fix_chain al_W0 n)!) ⊗p one1).
Proof.
rewrite /al_iter fix_chain_S al_W0_at_prom.
rewrite (der_prom _ (le_trans (cones_hom_norm_le1 _ _) (al_env_ball n))).
exact: tensor_curryE.
Qed.

Definition al_env3 (n : nat) :
    coalg_obj (ctxD_cbv (drop_names
      (("_"%string, tunit) :: ("l"%string, tfun tunit tunit) :: nil))) :=
  (one1 ⊗p (fix_chain al_W0 n)!) ⊗p one1.

Lemma al_env3_ball n : cone_norm (al_env3 n) <= 1.
Proof.
rewrite /al_env3 tensor_normME.
by rewrite mulr_ile1 ?cone_norm_ge0 ?al_env_ball ?Hone.
Qed.

Lemma al_env3_setlike n :
  Lfun (coalg_str (ctxD_cbv (drop_names
         (("_"%string, tunit) :: ("l"%string, tfun tunit tunit) :: nil))))
       (al_env3 n) = (al_env3 n)!.
Proof.
exact: (coalg_str_tensor_setlike
          (P:=ctxD_cbv (drop_names
                (("l"%string, tfun tunit tunit) :: nil)))
          (Q:=EM_term)
          (al_env_ball n) Hone (al_env_setlike n) coalg_str_one1).
Qed.

Lemma al_var_l_E n :
  Lfun (eD_cbv' al_var_l) (al_env3 n) = (fix_chain al_W0 n)!.
Proof.
apply: (eq_trans (y := Lfun (icones_comp
  (em_proj2_mor (R:=R) EM_term (tyD_cbv (tfun tunit tunit)))
  (em_proj1_mor (R:=R)
     (ctxD_cbv (drop_names (("l"%string, tfun tunit tunit) :: nil)))
     EM_term)) (al_env3 n))).
  by [].
rewrite Lfun_comp.
rewrite (em_proj1_morE (Q:=EM_term) Hone coalg_str_one1).
exact: (em_proj2_morE (P:=EM_term) Hone coalg_str_one1).
Qed.

Lemma al_tt_E n :
  Lfun (eD_cbv' (@ne_tt R Ar R_obj
         (("_"%string, tunit) :: ("l"%string, tfun tunit tunit) :: nil)))
       (al_env3 n) = one1.
Proof.
rewrite eD_tt_E.
apply: (eq_trans (y := Lfun (coalg_e (ctxD_cbv (drop_names
  (("_"%string, tunit) :: ("l"%string, tfun tunit tunit) :: nil))))
  (al_env3 n))).
  by [].
exact: (coalg_e_setlike (al_env3_ball n) (al_env3_setlike n)).
Qed.

(** The recursive call at the unit argument IS the previous iterate. *)
Lemma al_else_E n :
  Lfun (eD_cbv' (ne_app al_var_l ne_tt)) (al_env3 n) = al_iter n.
Proof.
rewrite (eD_app_at_setlike R_carrier_eq R_carrier_meas R_to_carrier_meas (al_env3_ball n) (al_env3_setlike n)).
rewrite al_var_l_E al_tt_E.
by rewrite (der_prom _ (fix_chain_ball al_W0_ball n)).
Qed.

(** *** Clean-surface coin leaf

    The clean [tProb] constant coin [Bernoulli (Const pr [|0|])] denotes, at
    any setlike unit-ball environment, the SAME [bernoulli p] cone as
    the legacy constant coin [Bernoulli pr]: the real literal [0] is the
    Dirac [δ_0], pushed by the bundle factoring [po_into (cst p)] to
    [δ_(po_into 0)], on which the carrier-density Bernoulli lift
    [bern_lift_P] reads off [bernoulli (po_density P (po_into 0))], and
    [po_into_E] computes that density back to [pr_val pr = p]. *)
Lemma al_coin_E n :
  Lfun (eD_cbv' (ne_bernoulli_p (po_density P) (po_density_meas P)
                   (po_ge0 P) (po_le1 P) al_coin_arg))
       (al_env3 n) = bernoulli (Ar:=Ar) p Hp0 Hp1.
Proof.
rewrite eD_bernoulli_p_E Lfun_comp.
rewrite -[bern_lift_g _ _ _]/(bern_lift_P P).
rewrite eD_to_prob_E Lfun_comp.
rewrite eD_real_E /real_icones (const_iconesE (al_env3_ball n) (al_env3_setlike n)).
rewrite FMeas_fmap_dirac bern_lift_P_dirac.
apply: bool_cone_eq; apply: val_inj => /=; by rewrite /po_density po_into_E.
Qed.

(** The Kleene step is the affine combination
    [ν_{n+1} = p·1 + (1-p)·ν_n]. *)
Lemma al_step n :
  al_iter n.+1 =
  bool_case (bernoulli (Ar:=Ar) p Hp0 Hp1) one1 (al_iter n).
Proof.
rewrite ex_almost_loop_iter_S al_if_decomp eD_if_E.
rewrite (if_icones_at
  (eD_cbv' (@ne_tt R Ar R_obj
     (("_"%string, tunit) :: ("l"%string, tfun tunit tunit) :: nil)))
  (eD_cbv' (ne_app al_var_l ne_tt))
  (eD_cbv' (ne_bernoulli_p (po_density P) (po_density_meas P)
              (po_ge0 P) (po_le1 P) al_coin_arg))
  (al_env3_ball n) (al_env3_setlike n)).
by rewrite al_tt_E al_else_E al_coin_E.
Qed.

(** *** The scalar cascade and the dichotomy theorems *)

Lemma al_iter_0 : al_iter 0 = precone_zero.
Proof. by rewrite /al_iter fix_chain_0 linhom_fun_zero. Qed.

Definition al_val (n : nat) : R := ((c1_val (al_iter n))%:num)%R.

Lemma al_val_0 : al_val 0%N = 0%R.
Proof. by rewrite /al_val al_iter_0. Qed.

Lemma al_norm n : cone_norm (al_iter n) = al_val n.
Proof. by []. Qed.

Lemma al_val_S n : al_val n.+1 = (p + (1 - p) * al_val n)%R.
Proof. by rewrite /al_val al_step /= mulr1. Qed.

(** Almost-sure termination at positive flip probability: the
    denotation has full mass. *)
Theorem ex_almost_loop_cbv_mass_one : (0 < p)%R ->
  cone_norm al_denot = 1%R.
Proof.
move=> Hp.
apply/le_anti/andP; split.
- by rewrite ex_almost_loop_sup_E cone_sup_ball_norm.
- have Hq0 : (0 <= 1 - p)%R by rewrite subr_ge0 Hp1.
  have Hq1 : (1 - p < 1)%R by rewrite ltrBlDr ltrDl.
  have Hcvg := affine_iter_cvg_real p (1 - p) Hq0 al_val_0 al_val_S Hq1.
  rewrite subKr divff ?gt_eqF// in Hcvg.
  have HK : forall n, (al_val n <= cone_norm al_denot)%R.
    move=> n; rewrite -al_norm ex_almost_loop_sup_E.
    apply: cone_normp; exact: cone_sup_ball_ub.
  rewrite -(cvg_lim (@Rhausdorff R) Hcvg).
  apply: limr_le.
  + by apply/cvg_ex; exists 1%R.
  + by apply: nearW => n; exact: HK.
Qed.

(** Certain divergence at [p = 0]: the chain is constantly zero. *)
Theorem ex_almost_loop_cbv_zero : p = 0%R -> al_denot = precone_zero.
Proof.
move=> Hp.
have Hbern : bernoulli (Ar:=Ar) p Hp0 Hp1 = bool_dirac_false.
  by apply: bool_cone_eq; apply: val_inj => /=; rewrite Hp ?subr0.
have Hiter0 : forall n, al_iter n = precone_zero.
  elim=> [ | n IH]; first exact: al_iter_0.
  by rewrite al_step Hbern bool_case_false IH.
rewrite ex_almost_loop_sup_E.
apply: precone_le_anti.
- apply: cone_sup_ball_lub => n.
  rewrite Hiter0; exact: precone_le_refl.
- exact: precone_le0.
Qed.

(** A norm-one element of the one-dimensional unit cone is the unit
    point: [cone_one_car Ar] is a thin wrapper around a nonnegative
    scalar, so [cone_norm x = (c1_val x)%:num] and [one1] is the
    scalar [1]. *)
Lemma cone_one_norm_eq1 (x : cone_one_car Ar) :
  cone_norm x = 1%R -> x = one1.
Proof.
rewrite /cone_norm/= /c1_norm => Hx.
by apply: cone_one_eq; apply: val_inj; rewrite /= Hx.
Qed.

(** Almost-sure termination at positive flip probability pins the CBV
    denotation as the unit point [one1] (the Dirac on the one-point
    space), strengthening [ex_almost_loop_cbv_mass_one] from the total
    mass to the cone element itself. *)
Theorem ex_almost_loop_cbv_dirac : (0 < p)%R -> al_denot = one1.
Proof. by move=> Hp; apply: cone_one_norm_eq1; exact: ex_almost_loop_cbv_mass_one. Qed.

End AlmostLoopRider.
