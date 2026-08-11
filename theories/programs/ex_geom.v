(**md*** [ex_geom] — the geometric counter has total mass [1]

    BEYOND THE PAPER.  This file is NOT part of the Ehrhard-Geoffroy
    2025 formalization (paper §2-§9).  It is one headline CBV program
    of the chapter; the six-step reduction-chain skeleton it runs on is
    documented once, for the rejection sampler, in
    [theories/programs/ex_reject_headline.v].

    The program is the fair-coin counter of
    [theories/programs/examples.v]
    [[
       (let rec g = λ_. if Bernoulli(½) then 0 else 1 + g ()) ()
    ]]
    — the iterate is [ν_{n+1} = ½·δ_0 + ½·(δ_1 + ν_n)] where the ELSE
    branch shifts the recursive call by [1] through the arithmetic
    lift; the translation-mass invariance [add_lift_mass] reduces the
    mass cascade to [x_{n+1} = ½ + ½·x_n], whose limit is [1].

    Results:
    - [ex_geom_cbv_mass_one] : the counter terminates almost surely;
    - [ex_geom_cbv_distribution] : the denotation is the geometric law
      [∑_k (1/2)^(k+1) δ_k];
    - [ex_geom_cbv_pmf] : the atom at the embedded natural [k] carries
      mass [(1/2)^(k+1)].

    Supporting kit: [theories/programs/infra/cbv_anchors.v] (the
    setlike-point kit), [theories/programs/infra/em_fix_value.v] (the
    seeded value-fixpoint combinator),
    [theories/programs/infra/cbv_fix_unfold.v] (the
    recursion-unfolding laws), [theories/prelude/geom_series.v] (the
    scalar affine cascade), [theories/mcones/fmeas.v] (the sup-mass
    bridge).

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

Section GeomRider.
Variables (R : realType) (Ar : MeasSubcat R).
(* Reparameterized over the bundled [probObj]: the real object and its
   carrier casts come from [P]. *)
Variable (P : probObj Ar).
Local Notation R_obj := (po_robj P).
Local Notation R_carrier_eq := (po_robj_eq P).
Local Notation R_carrier_meas := (po_robj_meas P).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

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

(** *** Syntactic decomposition *)

Definition g_var :
    @named_expr R Ar R_obj
      (("_"%string, tunit) :: ("g"%string, tfun tunit tR') :: nil)
      (tfun tunit tR') :=
  [ # "g" ].

Definition g_if :
    @named_expr R Ar R_obj
      (("_"%string, tunit) :: ("g"%string, tfun tunit tR') :: nil) tR' :=
  [ if Bernoulli [| (1 / 2 : R) |]
    then [| 0%R |]
    else [| 1%R |] + # "g" @ () ].

Lemma ex_geom_decomp :
  (ex_geom : @named_expr R Ar R_obj nil tR') =
  ne_let "g" (ne_fix "g" (ex_geom_body : @named_expr R Ar R_obj _ _))
    (ne_app (ne_var (nv_head "g" (tfun tunit tR') nil)) ne_tt).
Proof. by []. Qed.

Lemma ex_geom_body_decomp :
  (ex_geom_body : @named_expr R Ar R_obj _ _) = ne_lam "_" g_if.
Proof. by []. Qed.

(** The fair coin's underlying constant-literal Bernoulli: success
    probability [1/2] with the [[0,1]] bounds discharged by [lra]
    (the [Bernoulli [| (1/2 : R) |]] surface form). *)
Local Notation g_coin :=
  (ne_bernoulli (Ar:=Ar) (R_obj:=R_obj)
     (G := ("_"%string, tunit) :: ("g"%string, tfun tunit tR') :: nil)
     (1 / 2 : R) (bernoulli_half_ge0 R) (bernoulli_half_le1 R)).

Lemma g_if_decomp :
  g_if = ne_if tR'
           g_coin
           (ne_real 0%R)
           (ne_add (ne_real 1%R) (ne_app g_var ne_tt)).
Proof.
rewrite /g_if /=; congr (ne_if _ (ne_bernoulli _ _ _) _ _);
  exact: bool_irrelevance.
Qed.

Let Hone : cone_norm (one1 : cone_one_car Ar) <= 1.
Proof. by rewrite one1_norm. Qed.

(** *** The reduction chain (steps 1-4, mirrored) *)

Definition g_W0 :
    linhom_car Ar (Bang Ar (Lty tunit tR')) (Bang Ar (Lty tunit tR')) :=
  Lfun (tensor_curry
         (eD_cbv' (ex_geom_body : @named_expr R Ar R_obj _ _))) one1.

Lemma g_W0_ball : cone_norm g_W0 <= 1.
Proof. exact: le_trans (cones_hom_norm_le1 _ _) Hone. Qed.

(** The promoted fixpoint value is a setlike unit-ball point, so the
    [let rec] continuation environment is one too. *)
Lemma g_fix_prom_ball :
  cone_norm ((sc_fun (fix_value (Lty tunit tR')) g_W0)!) <= 1.
Proof. exact: (fix_value_prom_ball g_W0_ball). Qed.

Lemma g_fix_prom_setlike :
  Lfun (coalg_str (tyD_cbv (tfun tunit tR')))
       ((sc_fun (fix_value (Lty tunit tR')) g_W0)!) =
  ((sc_fun (fix_value (Lty tunit tR')) g_W0)!)!.
Proof. exact: (fix_value_prom_setlike g_W0_ball). Qed.

Definition g_env0 :
    coalg_obj (ctxD_cbv (drop_names
      (("g"%string, tfun tunit tR') :: nil))) :=
  one1 ⊗p (sc_fun (fix_value (Lty tunit tR')) g_W0)!.

Lemma g_env0_ball : cone_norm g_env0 <= 1.
Proof.
by rewrite /g_env0 tensor_normME one1_norm mul1r g_fix_prom_ball.
Qed.

Lemma g_env0_setlike :
  Lfun (coalg_str (ctxD_cbv (drop_names
         (("g"%string, tfun tunit tR') :: nil)))) g_env0 = g_env0!.
Proof.
exact: (coalg_str_tensor_setlike (P:=EM_term)
          (Q:=tyD_cbv (tfun tunit tR'))
          Hone g_fix_prom_ball coalg_str_one1 g_fix_prom_setlike).
Qed.

Definition g_iter (n : nat) : coalg_obj (tyD_cbv tR') :=
  linhom_fun (fix_chain g_W0 n) one1.

Lemma g_iter_chain n : precone_le (g_iter n) (g_iter n.+1).
Proof.
exact: (linhom_le_pointwise (fix_chain_chain g_W0_ball n) one1).
Qed.

Lemma g_iter_ball n : cone_norm (g_iter n) <= 1.
Proof.
apply: le_trans
  (linhom_norm_apply_le (fix_chain_ball g_W0_ball n) one1) _.
by rewrite mul1r Hone.
Qed.

Local Notation g_denot :=
  (linhom_fun (ex_geom_cbv P R_to_carrier_meas) one1).

Lemma ex_geom_app_E :
  g_denot = linhom_fun (sc_fun (fix_value (Lty tunit tR')) g_W0) one1.
Proof.
rewrite /ex_geom_cbv /eD icones_to_linhomE ex_geom_decomp.
have HoneG : cone_norm
    (one1 : coalg_obj (ctxD_cbv (drop_names (nil : named_ctx Ar)))) <= 1.
  by rewrite one1_norm.
rewrite (eD_let_at_setlike "g"
          (ne_fix "g" (ex_geom_body : @named_expr R Ar R_obj _ _))
          (ne_app (ne_var (nv_head "g" (tfun tunit tR') nil)) ne_tt)
          HoneG coalg_str_one1).
rewrite (eD_fix_at_setlike "g" (ex_geom_body : @named_expr R Ar R_obj _ _)
          HoneG coalg_str_one1).
rewrite (eD_app_at_setlike R_carrier_eq R_carrier_meas R_to_carrier_meas g_env0_ball g_env0_setlike).
rewrite (eD_var_head_at_setlike "g"
          (t := tfun tunit tR')
          ((sc_fun (fix_value (Lty tunit tR')) g_W0)!)
          HoneG coalg_str_one1).
rewrite (eD_tt_at_setlike g_env0_ball g_env0_setlike).
by rewrite (der_prom _ (fix_value_ball g_W0 g_W0_ball)).
Qed.

Lemma ex_geom_sup_E :
  g_denot = cone_sup_ball g_iter g_iter_chain g_iter_ball.
Proof.
rewrite ex_geom_app_E (fix_value_E g_W0_ball).
rewrite (linhom_fun_sup_ball (fix_chain_chain g_W0_ball)
  (fix_chain_ball g_W0_ball) Hone g_iter_chain g_iter_ball).
by [].
Qed.

Lemma g_chain_prom_ball n : cone_norm ((fix_chain g_W0 n)!) <= 1.
Proof. exact: (kleene_prom_ball g_W0_ball n). Qed.

Lemma g_chain_prom_setlike n :
  Lfun (coalg_str (tyD_cbv (tfun tunit tR')))
       ((fix_chain g_W0 n)!) = ((fix_chain g_W0 n)!)!.
Proof. exact: (kleene_prom_setlike g_W0_ball n). Qed.

Lemma g_env_ball n :
  cone_norm (one1 ⊗p (fix_chain g_W0 n)!) <= 1.
Proof.
by rewrite tensor_normME one1_norm mul1r g_chain_prom_ball.
Qed.

Lemma g_env_setlike n :
  Lfun (coalg_str (ctxD_cbv (drop_names
         (("g"%string, tfun tunit tR') :: nil))))
       (one1 ⊗p (fix_chain g_W0 n)!) =
  (one1 ⊗p (fix_chain g_W0 n)!)!.
Proof.
exact: (coalg_str_tensor_setlike (P:=EM_term)
          (Q:=tyD_cbv (tfun tunit tR'))
          Hone (g_chain_prom_ball n) coalg_str_one1
          (g_chain_prom_setlike n)).
Qed.

Lemma g_W0_at_prom n :
  linhom_fun g_W0 ((fix_chain g_W0 n)!) =
  (Lfun (tensor_curry (eD_cbv' g_if))
     (one1 ⊗p (fix_chain g_W0 n)!))!.
Proof.
rewrite {1}/g_W0 tensor_curryE ex_geom_body_decomp eD_lam_E.
exact: (adj_psi_at_setlike
  (P:=ctxD_cbv (drop_names (("g"%string, tfun tunit tR') :: nil)))
  _ (g_env_ball n) (g_env_setlike n)).
Qed.

Lemma ex_geom_iter_S n :
  g_iter n.+1 =
  Lfun (eD_cbv' g_if) ((one1 ⊗p (fix_chain g_W0 n)!) ⊗p one1).
Proof.
rewrite /g_iter fix_chain_S g_W0_at_prom.
rewrite (der_prom _ (le_trans (cones_hom_norm_le1 _ _) (g_env_ball n))).
exact: tensor_curryE.
Qed.

Definition g_env3 (n : nat) :
    coalg_obj (ctxD_cbv (drop_names
      (("_"%string, tunit) :: ("g"%string, tfun tunit tR') :: nil))) :=
  (one1 ⊗p (fix_chain g_W0 n)!) ⊗p one1.

Lemma g_env3_ball n : cone_norm (g_env3 n) <= 1.
Proof.
rewrite /g_env3 tensor_normME.
by rewrite mulr_ile1 ?cone_norm_ge0 ?g_env_ball ?Hone.
Qed.

Lemma g_env3_setlike n :
  Lfun (coalg_str (ctxD_cbv (drop_names
         (("_"%string, tunit) :: ("g"%string, tfun tunit tR') :: nil))))
       (g_env3 n) = (g_env3 n)!.
Proof.
exact: (coalg_str_tensor_setlike
          (P:=ctxD_cbv (drop_names (("g"%string, tfun tunit tR') :: nil)))
          (Q:=EM_term)
          (g_env_ball n) Hone (g_env_setlike n) coalg_str_one1).
Qed.

Lemma g_var_E n :
  Lfun (eD_cbv' g_var) (g_env3 n) = (fix_chain g_W0 n)!.
Proof.
apply: (eq_trans (y := Lfun (icones_comp
  (em_proj2_mor (R:=R) EM_term (tyD_cbv (tfun tunit tR')))
  (em_proj1_mor (R:=R)
     (ctxD_cbv (drop_names (("g"%string, tfun tunit tR') :: nil)))
     EM_term)) (g_env3 n))).
  by [].
rewrite Lfun_comp.
rewrite (em_proj1_morE (Q:=EM_term) Hone coalg_str_one1).
exact: (em_proj2_morE (P:=EM_term) Hone coalg_str_one1).
Qed.

Lemma g_tt_E n :
  Lfun (eD_cbv' (@ne_tt R Ar R_obj
         (("_"%string, tunit) :: ("g"%string, tfun tunit tR') :: nil)))
       (g_env3 n) = one1.
Proof.
rewrite eD_tt_E.
apply: (eq_trans (y := Lfun (coalg_e (ctxD_cbv (drop_names
  (("_"%string, tunit) :: ("g"%string, tfun tunit tR') :: nil))))
  (g_env3 n))).
  by [].
exact: (coalg_e_setlike (g_env3_ball n) (g_env3_setlike n)).
Qed.

Lemma g_then_E n :
  Lfun (eD_cbv' (@ne_real R Ar R_obj
         (("_"%string, tunit) :: ("g"%string, tfun tunit tR') :: nil) 0%R))
       (g_env3 n) =
  dirac_fmeas (R_to_carrier R_carrier_eq 0%R).
Proof.
rewrite eD_real_E /real_icones.
by rewrite (const_iconesE (g_env3_ball n) (g_env3_setlike n)).
Qed.

Lemma g_one_E n :
  Lfun (eD_cbv' (@ne_real R Ar R_obj
         (("_"%string, tunit) :: ("g"%string, tfun tunit tR') :: nil) 1%R))
       (g_env3 n) =
  dirac_fmeas (R_to_carrier R_carrier_eq 1%R).
Proof.
rewrite eD_real_E /real_icones.
by rewrite (const_iconesE (g_env3_ball n) (g_env3_setlike n)).
Qed.

Lemma g_call_E n :
  Lfun (eD_cbv' (ne_app g_var ne_tt)) (g_env3 n) = g_iter n.
Proof.
rewrite (eD_app_at_setlike R_carrier_eq R_carrier_meas R_to_carrier_meas (g_env3_ball n) (g_env3_setlike n)).
rewrite g_var_E g_tt_E.
by rewrite (der_prom _ (fix_chain_ball g_W0_ball n)).
Qed.

(** ELSE: the shifted recursive call [1 + g ()]. *)
Lemma g_else_E n :
  Lfun (eD_cbv' (ne_add (ne_real 1%R) (ne_app g_var ne_tt))) (g_env3 n) =
  Lfun (@add_lift R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas)
       (dirac_fmeas (R_to_carrier R_carrier_eq 1%R) ⊗p g_iter n).
Proof.
rewrite eD_add_E.
rewrite (Lfun_comp
  (@add_lift R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas)
  (em_pair_mor (eD_cbv' (ne_real 1%R)) (eD_cbv' (ne_app g_var ne_tt)))
  (g_env3 n)).
rewrite /em_pair_mor (Lfun_comp
  (tensor_mor (eD_cbv' (ne_real 1%R)) (eD_cbv' (ne_app g_var ne_tt)))
  (coalg_d (ctxD_cbv (drop_names
     (("_"%string, tunit) :: ("g"%string, tfun tunit tR') :: nil))))
  (g_env3 n)).
rewrite (coalg_d_setlike (g_env3_ball n) (g_env3_setlike n)) tensor_morE.
by rewrite g_one_E g_call_E.
Qed.

(** *** Constant-literal coin leaf

    The fair coin [Bernoulli [| (1/2 : R) |]] denotes, at any setlike
    unit-ball environment, the [bernoulli (1/2)] cone directly: the
    constant-coin denotation pin [eD_bernoulli_E] rewrites the leaf to
    the constant [icones_hom] [bernoulli_icones … (1/2)], which
    [const_iconesE] evaluates to [bernoulli (1/2)] at the setlike
    environment.  No [tProb]/[po_into]/[bern_lift_P] detour. *)
Lemma g_coin_E n :
  Lfun (eD_cbv' g_coin) (g_env3 n) =
  bernoulli (Ar:=Ar) (1 / 2 : R) (bernoulli_half_ge0 R) (bernoulli_half_le1 R).
Proof.
rewrite eD_bernoulli_E.
exact: (const_iconesE (g_env3_ball n) (g_env3_setlike n)).
Qed.

Lemma g_step n :
  g_iter n.+1 =
  bool_case (bernoulli (Ar:=Ar) (1 / 2 : R) (bernoulli_half_ge0 R)
               (bernoulli_half_le1 R))
    (dirac_fmeas (R_to_carrier R_carrier_eq 0%R))
    (Lfun (@add_lift R Ar R_obj R_carrier_eq R_carrier_meas
             R_to_carrier_meas)
       (dirac_fmeas (R_to_carrier R_carrier_eq 1%R) ⊗p g_iter n)).
Proof.
rewrite ex_geom_iter_S g_if_decomp eD_if_E.
rewrite (if_icones_at
  (eD_cbv' (@ne_real R Ar R_obj
     (("_"%string, tunit) :: ("g"%string, tfun tunit tR') :: nil) 0%R))
  (eD_cbv' (ne_add (ne_real 1%R) (ne_app g_var ne_tt)))
  (eD_cbv' g_coin)
  (g_env3_ball n) (g_env3_setlike n)).
by rewrite g_then_E g_else_E g_coin_E.
Qed.

(** *** The half-half cascade and the mass-one theorem *)

Local Open Scope ereal_scope.

(** *** Per-[U] pushforward evaluation

    Generalises [ppl.v::FMeas_fmap_setT_E] from [setT] to an arbitrary
    measurable [U]: the pushforward [FMeas_fmap φ] of a measure [ν]
    evaluates at [U] by integrating the Dirac masses [δ_(φ r)(U)]
    against [ν], which is the indicator of [φ ⁻¹` U]. *)
Lemma FMeas_fmap_U_E (X Y : ar_obj Ar) (φ : ar_hom Ar X Y)
    (ν : fmeas R (ar_carrier Ar X))
    (U : set (ar_carrier Ar Y)) (mU : measurable U) :
  fmeas_mu (Lfun (FMeas_fmap φ) ν) U =
  fmeas_mu ν (φ @^-1` U).
Proof.
have HE : Lfun (FMeas_fmap φ) ν =
    icone_integral (path_fun (push_dirac_path φ))
                   (path_is_path (push_dirac_path φ)) ν.
  by rewrite /FMeas_fmap (linhom_iconesE _ (FMeas_fmap_norm_le1 φ) ν).
rewrite HE.
rewrite (distributions.icone_integral_fmeas_E
           (path_is_path (push_dirac_path φ)) ν mU).
have mpreU : measurable (φ @^-1` U).
  have H := measurable_funPT φ measurableT U mU.
  by rewrite setTI in H.
under eq_integral => r _.
  have -> : fmeas_mu (path_fun (push_dirac_path φ) r) U
          = fmeas_mu (dirac_fmeas (φ r) : FMeas Y) U by [].
  rewrite (dirac_fmeas_E (φ r) mU) diracE/=.
  have -> : ((φ r \in U)%:R)%:E = (\1_(φ @^-1` U) r)%:E :> \bar R.
    by rewrite indicE.
  over.
by rewrite integral_indic// setIT.
Qed.

(** The shift map [+a] on the real carrier, [s_shift a c = a + c]. *)
Local Notation s_shift a :=
  (fun c : ar_carrier Ar R_obj =>
     R_to_carrier R_carrier_eq (a + carrier_to_R R_carrier_eq c)).

(** Per-[U] evaluation of the arithmetic shift [add_lift (δ_a ⊗ ν)]:
    adding the constant [a] to each sample is the pushforward of [ν]
    along [+a].  This is the per-[U] refinement of [ppl.v::add_lift_mass]
    (the [U = setT] case). *)
Lemma add_lift_dirac_U (a : R) (ν : fmeas R (ar_carrier Ar R_obj))
    (U : set (ar_carrier Ar R_obj)) (mU : measurable U) :
  fmeas_mu (Lfun (@add_lift R Ar R_obj R_carrier_eq R_carrier_meas
                   R_to_carrier_meas)
              (dirac_fmeas (R_to_carrier R_carrier_eq a) ⊗p ν)) U =
  fmeas_mu ν ((s_shift a) @^-1` U).
Proof.
set am := @add_meas R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas.
set apc := (ar_prod_cast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj)).
rewrite /add_lift.
rewrite -[Lfun _ _]/(Lfun (FMeas_fmap am)
  (Lfun (fmeas_lax R_obj R_obj)
    (dirac_fmeas (R_to_carrier R_carrier_eq a) ⊗p ν))).
have maddU : measurable (am @^-1` U).
  have H := measurable_funPT am measurableT U mU.
  by rewrite setTI in H.
rewrite (FMeas_fmap_U_E am _ mU).
rewrite (fmeas_lax_E (dirac_fmeas (R_to_carrier R_carrier_eq a)) ν).
rewrite (fmeas_lax_preE (dirac_fmeas (R_to_carrier R_carrier_eq a)) ν
           (am @^-1` U) maddU).
have mprecast : measurable (apc @^-1` (am @^-1` U)).
  have Hc := ar_prod_cast_meas Ar R_obj R_obj.
  have H := Hc measurableT (am @^-1` U) maddU.
  by rewrite setTI in H.
rewrite (fubini.fmeas_prodE _ _ (apc @^-1` (am @^-1` U)) mprecast).
(* The product measure on a general set is the iterated integral of
   the [ν]-sections against the outer Dirac, which collapses to the
   section at [R_to_carrier a]. *)
rewrite -[lebesgue_integral_fubini.product_measure1 _ _ _]/(
  \int[fubini.fmeas_fin_view (dirac_fmeas (R_to_carrier R_carrier_eq a))]_x
   (fubini.fmeas_fin_view ν) (xsection (apc @^-1` (am @^-1` U)) x)).
have eq_xint :
    \int[fubini.fmeas_fin_view (dirac_fmeas (R_to_carrier R_carrier_eq a))]_x
       (fubini.fmeas_fin_view ν) (xsection (apc @^-1` (am @^-1` U)) x)
    = \int[\d_(R_to_carrier R_carrier_eq a)]_x
       (fubini.fmeas_fin_view ν) (xsection (apc @^-1` (am @^-1` U)) x).
  apply: eq_measure_integral => W mW _.
  transitivity (fmeas_mu (dirac_fmeas (R_to_carrier R_carrier_eq a)) W).
    exact: (fubini.fmeas_fin_viewE (dirac_fmeas (R_to_carrier R_carrier_eq a))
              W mW).
  exact: (dirac_fmeas_E _ mW).
have ms_sec : measurable_fun [set: ar_carrier Ar R_obj]
    (fun x => fubini.fmeas_fin_view ν (xsection (apc @^-1` (am @^-1` U)) x)).
  exact: (lebesgue_integral_fubini.measurable_fun_xsection
            (fubini.fmeas_fin_view ν) mprecast).
rewrite eq_xint (integral_dirac _ measurableT ms_sec).
rewrite diracT mul1e.
rewrite (fubini.fmeas_fin_viewE ν); last first.
  exact: (measurable_xsection _ mprecast).
congr (fmeas_mu ν _).
apply/seteqP; split=> y; rewrite /xsection/= inE /am /apc /preimage/=
  (add_meas_cast R_carrier_meas R_to_carrier_meas (R_to_carrier R_carrier_eq a) y)
  R_to_carrierK//.
Qed.

Lemma g_iter_0 : g_iter 0 = precone_zero.
Proof. by rewrite /g_iter fix_chain_0 linhom_fun_zero. Qed.

Definition g_val (n : nat) : R :=
  fine (fmeas_mu (g_iter n) [set: ar_carrier Ar R_obj]).

Lemma g_val_0 : g_val 0%N = 0%R.
Proof.
rewrite /g_val.
have -> : (g_iter 0 : fmeas R (ar_carrier Ar R_obj)) = fmeas_zero.
  by rewrite g_iter_0.
by rewrite fmeas_zeroE.
Qed.

(** The mass recurrence [x_{n+1} = ½ + ½·x_n]: the THEN Dirac has
    unit mass, and the shifted recursive call has the mass of the
    previous iterate by translation invariance ([add_lift_mass]). *)
Lemma g_val_S n : g_val n.+1 = (1 / 2 + (1 / 2) * g_val n)%R.
Proof.
rewrite /g_val g_step.
have -> : (bool_case (bernoulli (Ar:=Ar) (1 / 2 : R) (bernoulli_half_ge0 R)
               (bernoulli_half_le1 R))
    (dirac_fmeas (R_to_carrier R_carrier_eq 0%R))
    (Lfun (@add_lift R Ar R_obj R_carrier_eq R_carrier_meas
             R_to_carrier_meas)
       (dirac_fmeas (R_to_carrier R_carrier_eq 1%R) ⊗p g_iter n))
    : fmeas R (ar_carrier Ar R_obj)) =
  fmeas_add
    (fmeas_scale (NngNum (bernoulli_half_ge0 R))
       (dirac_fmeas (R_to_carrier R_carrier_eq 0%R)))
    (fmeas_scale (NngNum (subr_ge0_le1 (1 / 2 : R) (bernoulli_half_le1 R)))
       (Lfun (@add_lift R Ar R_obj R_carrier_eq R_carrier_meas
                R_to_carrier_meas)
          (dirac_fmeas (R_to_carrier R_carrier_eq 1%R) ⊗p g_iter n))).
  by [].
rewrite fmeas_addE 2!fmeas_scaleE dirac_fmeas_setT_E mule1.
rewrite add_lift_mass.
rewrite fineD//; first last.
  by rewrite fin_numM// fmeas_setT_fin.
rewrite fineM// ?fmeas_setT_fin//=.
congr (_ + _ * _)%R.
by rewrite {1}(splitr (1 : R)) addrK.
Qed.

(** Almost-sure termination of the geometric counter: the CBV
    denotation is a PROBABILITY distribution. *)
Theorem ex_geom_cbv_mass_one :
  fmeas_mu g_denot [set: ar_carrier Ar R_obj] = 1.
Proof.
rewrite ex_geom_sup_E.
apply: (fmeas_kleene_sup_U_E g_iter_chain g_iter_ball measurableT).
have HE : (fun n => fmeas_mu (g_iter n) [set: ar_carrier Ar R_obj]) =
          (fun n => (g_val n)%:E).
  by apply/funext => n; rewrite /g_val fineK// fmeas_setT_fin.
rewrite HE.
exact: (affine_iter_cvg_half g_val_0 g_val_S).
Qed.

(** *** The geometric distribution: [⟦ex_geom⟧ = Σ_k (1/2)^(k+1) δ_k]

    The per-iterate scaffolding above pins not just the total mass but
    the full per-set behaviour: the [n]-th Kleene iterate is the
    truncated geometric law [Σ_{k<n} (1/2)^(k+1) δ_k], and the
    denotation is its limit. *)

(** The embedded atom [k ∈ ℕ] as a point of the real carrier. *)
Local Notation gpt k := (R_to_carrier R_carrier_eq (k%:R : R)).

(** The geometric weight [(1/2)^(k+1)] as an ereal. *)
Local Notation geom_w k := (((1 / 2 : R) ^+ k.+1)%:E).

(** [add_lift] shifts the atom index by one: [s_shift 1] maps
    [gpt k] to [gpt k.+1]. *)
Lemma g_shift_atom (k : nat) (U : set (ar_carrier Ar R_obj))
    (mU : measurable U) :
  fmeas_mu (dirac_fmeas (gpt k)) ((s_shift (1 : R)) @^-1` U) =
  fmeas_mu (dirac_fmeas (gpt k.+1)) U.
Proof.
have ms : measurable_fun [set: ar_carrier Ar R_obj] (s_shift (1 : R)).
  apply: measurableT_comp; first exact: R_to_carrier_meas.
  apply: measurable_funD; first exact: measurable_cst.
  exact: (carrier_to_R_meas R_carrier_meas).
have mpre : measurable ((s_shift (1 : R)) @^-1` U).
  have H := ms measurableT _ mU.
  by rewrite setTI in H.
rewrite (dirac_fmeas_E (gpt k) mpre).
rewrite (dirac_fmeas_E (gpt k.+1) mU).
rewrite !diracE.
congr (_%:R)%:E; congr (nat_of_bool _).
by congr (_ \in U); rewrite /preimage/= R_to_carrierK -natr1 addrC.
Qed.

(** Per-[U] iterate recurrence: the measure refinement of [g_val_S].
    The THEN branch contributes [(1/2) δ_0]; the ELSE branch the
    previous iterate pushed forward by [+1]. *)
Lemma g_iter_U_S n (U : set (ar_carrier Ar R_obj)) (mU : measurable U) :
  fmeas_mu (g_iter n.+1) U =
  (1 / 2)%:E * fmeas_mu (dirac_fmeas (gpt 0%N)) U
  + (1 / 2)%:E * fmeas_mu (g_iter n) ((s_shift (1 : R)) @^-1` U).
Proof.
rewrite g_step.
have -> : (bool_case (bernoulli (Ar:=Ar) (1 / 2 : R) (bernoulli_half_ge0 R)
               (bernoulli_half_le1 R))
    (dirac_fmeas (R_to_carrier R_carrier_eq 0%R))
    (Lfun (@add_lift R Ar R_obj R_carrier_eq R_carrier_meas
             R_to_carrier_meas)
       (dirac_fmeas (R_to_carrier R_carrier_eq 1%R) ⊗p g_iter n))
    : fmeas R (ar_carrier Ar R_obj)) =
  fmeas_add
    (fmeas_scale (NngNum (bernoulli_half_ge0 R))
       (dirac_fmeas (R_to_carrier R_carrier_eq 0%R)))
    (fmeas_scale (NngNum (subr_ge0_le1 (1 / 2 : R) (bernoulli_half_le1 R)))
       (Lfun (@add_lift R Ar R_obj R_carrier_eq R_carrier_meas
                R_to_carrier_meas)
          (dirac_fmeas (R_to_carrier R_carrier_eq 1%R) ⊗p g_iter n))).
  by [].
rewrite fmeas_addE 2!fmeas_scaleE/=.
rewrite (add_lift_dirac_U 1%R (g_iter n) mU).
have -> : ((1 - 1 / 2)%R : R) = (1 / 2)%R
  by rewrite {1}(splitr (1 : R)) addrK.
have -> : (gpt 0%N) = R_to_carrier R_carrier_eq 0%R by rewrite mulr0n.
by [].
Qed.

(** Closed form: the [n]-th iterate is the truncated geometric law. *)
Lemma g_iter_closed n (U : set (ar_carrier Ar R_obj)) (mU : measurable U) :
  fmeas_mu (g_iter n) U =
  \sum_(k < n) geom_w k * fmeas_mu (dirac_fmeas (gpt k)) U.
Proof.
elim: n U mU => [ | n IH] U mU.
  rewrite big_ord0.
  have -> : (g_iter 0 : fmeas R (ar_carrier Ar R_obj)) = fmeas_zero
    by rewrite g_iter_0.
  by rewrite fmeas_zeroE.
have ms : measurable_fun [set: ar_carrier Ar R_obj] (s_shift (1 : R)).
  apply: measurableT_comp; first exact: R_to_carrier_meas.
  apply: measurable_funD; first exact: measurable_cst.
  exact: (carrier_to_R_meas R_carrier_meas).
have mpre : measurable ((s_shift (1 : R)) @^-1` U).
  have H := ms measurableT _ mU.
  by rewrite setTI in H.
rewrite (g_iter_U_S n mU) (IH _ mpre).
rewrite big_ord_recl/= expr1 mulr0n; congr (_ + _).
under [RHS]eq_bigr => i _ do rewrite /bump/= add1n.
rewrite ge0_sume_distrr; last first.
  move=> i _.
  by rewrite mule_ge0// ?lee_fin ?exprn_ge0// ?divr_ge0// measure_ge0.
apply: eq_bigr => i _.
by rewrite (g_shift_atom i mU) muleA -EFinM -exprS.
Qed.

(** The geometric series limit: the partial sums of the geometric
    weights converge to the full ereal series. *)
Lemma g_iter_series_cvg (U : set (ar_carrier Ar R_obj))
    (mU : measurable U) :
  fmeas_mu (g_iter n) U @[n --> \oo] -->
    \sum_(k <oo) geom_w k * fmeas_mu (dirac_fmeas (gpt k)) U.
Proof.
have HE : (fun n => fmeas_mu (g_iter n) U) =
          (fun n => \sum_(0 <= k < n)
             geom_w k * fmeas_mu (dirac_fmeas (gpt k)) U).
  by apply/funext => n; rewrite big_mkord; exact: g_iter_closed.
rewrite HE.
apply: (is_cvg_nneseries (N := 0%N)) => k _ _.
by rewrite mule_ge0// ?measure_ge0// lee_fin exprn_ge0// divr_ge0.
Qed.

(** The distribution identity: the CBV denotation of [ex_geom]
    evaluates on every measurable [U] as the geometric series
    [Σ_k (1/2)^(k+1) δ_k(U)]. *)
Theorem ex_geom_cbv_distribution (U : set (ar_carrier Ar R_obj))
    (mU : measurable U) :
  fmeas_mu g_denot U =
  \sum_(k <oo) geom_w k * fmeas_mu (dirac_fmeas (gpt k)) U.
Proof.
rewrite ex_geom_sup_E.
apply: (fmeas_kleene_sup_U_E g_iter_chain g_iter_ball mU).
exact: g_iter_series_cvg.
Qed.

(** The atoms are distinct: [gpt] is injective, since [R_to_carrier]
    has the left inverse [carrier_to_R] and [_%:R] is injective on
    [nat]. *)
Lemma gpt_inj : injective (fun k : nat => gpt k).
Proof.
move=> i j /(congr1 (carrier_to_R R_carrier_eq)).
rewrite !R_to_carrierK => Hij.
by apply/eqP; rewrite -(eqr_nat R) Hij eqxx.
Qed.

(** The embedded atom set is measurable: it is the [carrier_to_R]
    preimage of the (measurable) real singleton [{k%:R}]. *)
Lemma measurable_gpt (k : nat) : measurable [set gpt k].
Proof.
have -> : [set gpt k] = carrier_to_R R_carrier_eq @^-1` [set (k%:R : R)].
  apply/seteqP; split=> c.
    by move=> ->; rewrite /preimage/= R_to_carrierK.
  rewrite /preimage/= => Hc.
  by rewrite -(carrier_to_RK R_carrier_eq c) Hc.
have m1 : measurable [set (k%:R : R)] by rewrite -set_itv1.
rewrite -[X in measurable X]setTI.
exact: (carrier_to_R_meas R_carrier_meas measurableT m1).
Qed.

(** The probability mass function: the denotation assigns mass exactly
    [(1/2)^(k+1)] to each embedded natural [k]. *)
Theorem ex_geom_cbv_pmf (k : nat) :
  fmeas_mu g_denot [set gpt k] = ((1 / 2 : R) ^+ k.+1)%:E.
Proof.
have mpt : measurable [set gpt k] by exact: measurable_gpt.
have hge0 : forall j : nat,
    0 <= geom_w j * fmeas_mu (dirac_fmeas (gpt j)) [set gpt k].
  move=> j.
  by rewrite mule_ge0// ?measure_ge0// lee_fin exprn_ge0// divr_ge0.
rewrite (ex_geom_cbv_distribution mpt).
rewrite (nneseriesD1 (n := k) (P := xpredT) (fun j _ => hge0 j) isT).
have -> : geom_w k * fmeas_mu (dirac_fmeas (gpt k)) [set gpt k]
        = ((1 / 2 : R) ^+ k.+1)%:E.
  rewrite (dirac_fmeas_E _ mpt) diracE/= mem_set// mulr1n mule1//.
rewrite [X in _ + X](_ : _ = 0) ?adde0//.
apply: (eseries0 (N := 0%N)) => j _; rewrite andTb => Hjk.
rewrite (dirac_fmeas_E _ mpt) diracE/=.
have -> : (gpt j \in [set gpt k]) = false.
  apply: memNset => /= /gpt_inj Heq.
  by rewrite Heq eqxx in Hjk.
by rewrite mulr0n mule0.
Qed.

End GeomRider.
