(**md**************************************************************************)
(** * Denotation bridge — the clean [ne_reject] / [ne_condition] surface

    BEYOND THE PAPER.  This file is NOT part of the Ehrhard-Geoffroy 2025
    formalization.  It is INCREMENT 2 of the hard-rejection programme
    ([docs/hard_reject_condition.md]): the DENOTATION BRIDGE that carries
    the boolean rejection headlines of [ex_reject_bool.v] (proved for the
    SOFT [reject_prog]/[condition_prog] at a {0,1}-indicator test) over to
    the CLEAN [ne_reject] / [ne_condition] combinators built on the
    deterministic [ne_test] primitive ([hard_reject.v]).

    ** The route (Report 1's "scrutinee morphism-equality")

    At a {0,1} test, the clean [ne_test f] and the soft
    [Bernoulli (test (ind_testfn P_acc) x)] both denote the SAME
    deterministic Dirac-on-bool [δ_{f x}].  Concretely the SCRUTINEE LEAF
    morphisms coincide:
    [[
       test_lift f_bool  =  bern_lift_P ∘ FMeas(po_into (1_P_acc))
    ]]
    ([scrut_leaf_E], proved by [dirac_dense] + the exact Dirac
    computation of [ex_reject_model.v::rm_scrut_E]).  Since [ne_reject]
    and the soft [ex_reject_comb] (at the indicator bundle) differ ONLY
    in this scrutinee leaf and in the fixpoint binder NAME — and [eD_cbv]
    erases names ([drop_names], [named_var_to_has_var]) and [eD_fix_E]
    does not mention the binder — the two combinator denotations are equal
    by structural congruence of [eD_cbv] ([reject_comb_denot_E]).  The
    program denotations then coincide ([reject_prog'_denot_E]) and every
    boolean reject headline transfers VERBATIM.

    No existing proof is edited.

    Standalone compile (deps built):
      rocq c -Q theories Icones -w -notation-overridden
        -w -projection-no-head-constant -w -redundant-canonical-projection
        -w -hiding-delimiting-key -w -ambiguous-paths
        -w -deprecated-since-mathcomp-analysis-1.9.0
        -w -deprecated-since-mathcomp-2.5.0 theories/programs/hard_reject_denot.v *)
(***************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals constructive_ereal.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import ereal.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import measure dirac_measure.
From mathcomp.analysis Require Import lebesgue_integral_definition numfun.
From Stdlib Require Import Strings.String.

Require Import Icones.prelude.nonneg_extra.
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
Require Import Icones.icones.examples_icone.
Require Import Icones.homs.bilin.
Require Import Icones.homs.tensor.
Require Import Icones.homs.tensor_construct.
Require Import Icones.homs.smcc.
Require Import Icones.homs.exp_adjunction.
Require Import Icones.homs.seely_defs.
Require Import Icones.homs.linhom.
Require Import Icones.homs.bang.
Require Import Icones.homs.tensor_hom_iso.
Require Import Icones.homs.seely.
Require Import Icones.homs.coalgebra.
Require Import Icones.homs.em_cat.
Require Import Icones.homs.em_seely_comonoid.
Require Import Icones.homs.em_cartesian.
Require Import Icones.programs.infra.bool_cone.
Require Import Icones.programs.ppl.
Require Import Icones.programs.infra.cbv_anchors.
Require Import Icones.programs.infra.em_fix_value.
Require Import Icones.programs.infra.cbv_fix_unfold.
Require Import Icones.programs.infra.cbv_marginals.
Require Import Icones.programs.infra.let_sample_law.
Require Import Icones.programs.ppl_cbv.
Require Import Icones.programs.examples.
Require Import Icones.programs.hard_reject.
Require Import Icones.programs.ex_reject_headline.
Require Import Icones.programs.ex_reject_model.
Require Import Icones.programs.ex_reject_bool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** §1 — The reject denotation bridge *)

Section RejectDenotBridge.
Variables (R : realType) (Ar : MeasSubcat R) (P : probObj Ar).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier (po_robj_eq P)).
Variable (P_acc : set R).
Hypothesis mPacc : measurable P_acc.
Variable (Mbody :
  @named_expr R Ar (po_robj P) (("_"%string, tunit) :: nil) (tR (po_robj P))).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation cR := (carrier_to_R (po_robj_eq P)).
Local Notation f0 := (ind_testfn P_acc mPacc).
Local Notation tR' := (tR (po_robj P)).
Local Notation eD_cbv' :=
  (@eD_cbv R Ar (po_robj P) (po_robj_eq P) (po_robj_meas P)
           R_to_carrier_meas _ _).
Local Notation eD' :=
  (@eD R Ar (po_robj P) (po_robj_eq P) (po_robj_meas P)
       R_to_carrier_meas _ _).

(** The meta boolean test: membership of the carrier accept set
    [A := cR^{-1}(P_acc)]. *)
Definition f0_bool : ar_carrier Ar (po_robj P) -> bool :=
  fun r => cR r \in P_acc.

Lemma Hf0_bool : measurable_fun [set: ar_carrier Ar (po_robj P)] f0_bool.
Proof.
apply: (measurable_fun_bool true); rewrite setTI.
have -> : f0_bool @^-1` [set true] = cR @^-1` P_acc.
  rewrite predeqE => r; rewrite /f0_bool /preimage/=; split => H.
  - exact: set_mem H.
  - exact: mem_set H.
have H := (po_robj_meas P) measurableT P_acc mPacc; rewrite setTI in H.
exact: H.
Qed.

(** The clean coin's underlying [tProb] factoring of [f0] — EXACTLY the
    [po_into] desugaring of [Bernoulli (test f0 #"x")] (cf. [ptest]). *)
Let rm_phi :=
  po_into P (test_fun f0) (test_meas f0) (test_ge0 f0) (test_le1 f0).

(** ** §2 — The scrutinee leaf morphism equality (the only real content)

    The deterministic boolean-test lift at [f0_bool] equals the soft
    {0,1}-coin scrutinee composite.  Both denote [δ_{f x}] on every
    Dirac, so [dirac_dense] reduces the equality to the Dirac computation
    that is literally the body of [ex_reject_model.v::rm_scrut_E]. *)
Lemma scrut_leaf_E :
  @test_lift R Ar (po_robj P) f0_bool Hf0_bool
  = icones_comp (bern_lift_P P) (FMeas_fmap rm_phi).
Proof.
apply: dirac_dense => r.
rewrite test_lift_dirac Lfun_comp FMeas_fmap_dirac bern_lift_P_dirac /f0_bool.
apply: bool_cone_eq; apply: val_inj => /=;
  rewrite /po_density po_into_E f0E indicE;
  by case: (cR r \in P_acc) => /=; rewrite ?subr0 ?subrr.
Qed.

(** The composite reading the congruence step consumes directly. *)
Lemma scrut_comp_E (A0 : ICone.type Ar)
    (m : icones_hom Ar A0 (FMeas (po_robj P))) :
  icones_comp (@test_lift R Ar (po_robj P) f0_bool Hf0_bool) m
  = icones_comp (bern_lift_P P) (icones_comp (FMeas_fmap rm_phi) m).
Proof. by rewrite scrut_leaf_E icones_compA. Qed.

(** ** §3 — The combinator denotation equality

    [ne_reject] and the soft [ex_reject_comb] (at the indicator bundle)
    have identical [eD_cbv] structure: the fixpoint binder name (["rx"]
    vs ["rs"]) is erased by [eD_cbv] ([drop_names] / [named_var_to_has_var];
    [eD_fix_E] omits the name), and the scrutinee leaf is handled by
    [scrut_comp_E].  Everything else is definitional. *)
Lemma reject_comb_denot_E :
  eD_cbv' (ne_reject (R_obj := po_robj P) tunit f0_bool Hf0_bool)
  = eD_cbv' (ex_reject_comb (P:=P) tunit f0).
Proof.
rewrite /ne_reject /ex_reject_comb /pbern /ptest.
rewrite !eD_fix_E !eD_lam_E !eD_let_E !eD_if_E.
rewrite eD_test_E eD_bernoulli_p_E eD_to_prob_E.
by rewrite scrut_comp_E.
Qed.

(** ** §4 — The clean program and its denotation transfer *)

Definition reject_prog' : @named_expr R Ar (po_robj P) nil tR' :=
  [ {ne_reject (R_obj := po_robj P) tunit f0_bool Hf0_bool}
      @ {model_prog (P:=P) Mbody} @ () ].

Lemma reject_prog'_denot_E :
  eD' reject_prog' = eD' (reject_prog (P:=P) f0 Mbody).
Proof.
rewrite /reject_prog' /reject_prog /eD.
by rewrite !eD_app_E reject_comb_denot_E.
Qed.

(** ** §5 — The transferred boolean reject headlines

    Restated for the CLEAN combinator; each transfers VERBATIM because
    the denotations are equal objects.  [nu_M] / [A] are the SAME
    objects as in [ex_reject_bool.v::BoolHeadlines]. *)

Local Notation nu_M :=
  (fmeas_mu (linhom_fun (eD (R_carrier_meas := po_robj_meas P)
     (R_to_carrier_meas := R_to_carrier_meas) (model_run (P:=P) Mbody)) one1)).
Local Notation reject' :=
  (fmeas_mu (linhom_fun (eD (R_carrier_meas := po_robj_meas P)
     (R_to_carrier_meas := R_to_carrier_meas) reject_prog') one1)).
Local Notation Aacc := (@A R Ar P P_acc).

Local Open Scope ereal_scope.

(** The master identity, boolean form:
    [(1 - nu_M(setT) + nu_M(A)) · reject(U) = nu_M (A `&` U)]. *)
Theorem reject_bool_master' U (mU : measurable U) :
  ((1 - fine (nu_M setT) + fine (nu_M Aacc))%R)%:E * reject' U
  = nu_M (Aacc `&` U).
Proof.
rewrite reject_prog'_denot_E.
exact: (reject_bool_master R Ar P R_to_carrier_meas P_acc mPacc Mbody U mU).
Qed.

(** The normalised form. *)
Theorem reject_bool_is_normalised' :
  (0 < 1 - fine (nu_M setT) + fine (nu_M Aacc))%R ->
  forall U, measurable U ->
  reject' U =
  ((fine (nu_M (Aacc `&` U))
    / (1 - fine (nu_M setT) + fine (nu_M Aacc)))%R)%:E.
Proof.
move=> Hpos U mU; rewrite reject_prog'_denot_E.
exact: (reject_bool_is_normalised R Ar P R_to_carrier_meas P_acc mPacc
          Mbody Hpos U mU).
Qed.

(** Total mass, normalised form. *)
Theorem reject_bool_mass' :
  (0 < 1 - fine (nu_M setT) + fine (nu_M Aacc))%R ->
  reject' setT =
  ((fine (nu_M Aacc) / (1 - fine (nu_M setT) + fine (nu_M Aacc)))%R)%:E.
Proof.
move=> Hpos; rewrite reject_prog'_denot_E.
exact: (reject_bool_mass R Ar P R_to_carrier_meas P_acc mPacc Mbody Hpos).
Qed.

(** Almost-sure termination for probability models. *)
Theorem reject_bool_mass_one' :
  nu_M setT = 1 -> 0 < nu_M Aacc -> reject' setT = 1.
Proof.
move=> Hm1 HA; rewrite reject_prog'_denot_E.
exact: (reject_bool_mass_one R Ar P R_to_carrier_meas P_acc mPacc Mbody Hm1 HA).
Qed.

(** Certain rejection diverges (empty accept set). *)
Theorem reject_bool_zero' U : P_acc = set0 -> reject' U = 0.
Proof.
move=> HP0; rewrite reject_prog'_denot_E.
exact: (reject_bool_zero R Ar P R_to_carrier_meas P_acc mPacc Mbody U HP0).
Qed.

End RejectDenotBridge.

(** ** §6 — [ne_fail] denotes the zero sub-distribution

    The guarded diverging fixpoint [ne_fail] (the clean surface's
    [fail]) denotes [precone_zero] at every setlike unit-ball
    environment.  This is the genuinely-new ingredient the clean
    [ne_condition] / [ne_assert] need (the [else fail] branch).

    The proof is the live [fix_value] backbone (NOT the removed naive
    [Phi_fun]): [eD_fix_at_setlike] -> [fix_value_E] -> a [fix_chain]
    induction whose every iterate, applied to the unit input, collapses
    to the previous iterate (the body [\_. fail @ ()] just re-invokes
    [fail]) — base [fix_chain_0 = precone_zero] — so the Kleene sup of
    the constant-zero chain is [precone_zero]. *)

Section FailZero.
Variables (R : realType) (Ar : MeasSubcat R) (P : probObj Ar).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier (po_robj_eq P)).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation eD_cbv' :=
  (@eD_cbv R Ar (po_robj P) (po_robj_eq P) (po_robj_meas P)
           R_to_carrier_meas _ _).
Local Notation "x '!'" := (prom x) (at level 2, format "x '!'").
Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.

Variables (G : named_ctx Ar) (t : ppl_type Ar).
Variable (gam : coalg_obj (ctxD_cbv (drop_names G))).
Hypothesis Hgam_ball : cone_norm gam <= 1.
Hypothesis Hgam_setlike :
  Lfun (coalg_str (ctxD_cbv (drop_names G))) gam = gam!.

Local Notation L :=
  (linhom_car Ar (coalg_obj (tyD_cbv tunit)) (coalg_obj (tyD_cbv t))).

(** Syntactic decomposition of [ne_fail] — all definitional. *)
Definition fvar : @named_expr R Ar (po_robj P)
    (("_"%string, tunit) :: ("fail"%string, tfun tunit t) :: G)
    (tfun tunit t) := [ # "fail" ].

Definition finner : @named_expr R Ar (po_robj P)
    (("_"%string, tunit) :: ("fail"%string, tfun tunit t) :: G) t :=
  [ {fvar} @ () ].

Definition fbody : @named_expr R Ar (po_robj P)
    (("fail"%string, tfun tunit t) :: G) (tfun tunit t) :=
  [ \ "_" ::: tunit => {finner} ].

Lemma ne_fail_decomp :
  @ne_fail R Ar (po_robj P) G t =
  ne_app (ne_fix "fail" fbody) (@ne_tt R Ar (po_robj P) G).
Proof. by []. Qed.

Lemma finner_decomp :
  finner = ne_app fvar (@ne_tt R Ar (po_robj P) _).
Proof. by []. Qed.

(** The body endofunction at the closed environment [gam]. *)
Definition F : linhom_car Ar (Bang Ar L) (Bang Ar L) :=
  Lfun (tensor_curry (eD_cbv' fbody)) gam.

Lemma HF_ball : cone_norm F <= 1.
Proof. exact: le_trans (cones_hom_norm_le1 _ _) Hgam_ball. Qed.

Let Hone1_ball : cone_norm (one1 : cone_one_car Ar) <= 1.
Proof. by rewrite one1_norm. Qed.

(** The "fail"-iterate environment tower. *)
Definition fenv1 (n : nat) :
    coalg_obj (ctxD_cbv (drop_names (("fail"%string, tfun tunit t) :: G))) :=
  gam ⊗p (fix_chain F n)!.

Definition fenv2 (n : nat) :
    coalg_obj (ctxD_cbv (drop_names
      (("_"%string, tunit) :: ("fail"%string, tfun tunit t) :: G))) :=
  fenv1 n ⊗p one1.

Lemma fix_chain_prom_ball n : cone_norm ((fix_chain F n)!) <= 1.
Proof. exact: prom_ball (fix_chain_ball HF_ball n). Qed.

Lemma fix_chain_prom_setlike n :
  Lfun (coalg_str (tyD_cbv (tfun tunit t))) ((fix_chain F n)!) =
  ((fix_chain F n)!)!.
Proof.
rewrite -[tyD_cbv (tfun tunit t)]/(bang_cofree L) bang_cofree_str.
exact: (dig_prom _ (fix_chain_ball HF_ball n)).
Qed.

Lemma fenv1_ball n : cone_norm (fenv1 n) <= 1.
Proof.
by rewrite /fenv1 tensor_normME mulr_ile1 ?cone_norm_ge0
   ?Hgam_ball ?fix_chain_prom_ball.
Qed.

Lemma fenv1_setlike n :
  Lfun (coalg_str (ctxD_cbv (drop_names (("fail"%string, tfun tunit t) :: G))))
       (fenv1 n) = (fenv1 n)!.
Proof.
exact: (coalg_str_tensor_setlike (P:=ctxD_cbv (drop_names G))
          (Q:=tyD_cbv (tfun tunit t)) Hgam_ball (fix_chain_prom_ball n)
          Hgam_setlike (fix_chain_prom_setlike n)).
Qed.

Lemma fenv2_ball n : cone_norm (fenv2 n) <= 1.
Proof.
by rewrite /fenv2 tensor_normME mulr_ile1 ?cone_norm_ge0
   ?fenv1_ball ?one1_norm.
Qed.

Lemma fenv2_setlike n :
  Lfun (coalg_str (ctxD_cbv (drop_names
      (("_"%string, tunit) :: ("fail"%string, tfun tunit t) :: G))))
       (fenv2 n) = (fenv2 n)!.
Proof.
exact: (coalg_str_tensor_setlike
          (P:=ctxD_cbv (drop_names (("fail"%string, tfun tunit t) :: G)))
          (Q:=tyD_cbv tunit) (fenv1_ball n) Hone1_ball
          (fenv1_setlike n) coalg_str_one1).
Qed.

(** The "fail" variable projects the promoted previous iterate. *)
Lemma fail_var_E n :
  Lfun (eD_cbv' fvar) (fenv2 n) = (fix_chain F n)!.
Proof.
apply: (eq_trans (y := Lfun (icones_comp
  (em_proj2_mor (R:=R) (ctxD_cbv (drop_names G)) (tyD_cbv (tfun tunit t)))
  (em_proj1_mor (R:=R)
     (ctxD_cbv (drop_names (("fail"%string, tfun tunit t) :: G)))
     (tyD_cbv tunit)))
  (fenv2 n))).
  by [].
rewrite Lfun_comp.
rewrite (em_proj1_morE (Q:=tyD_cbv tunit) Hone1_ball coalg_str_one1).
exact: (em_proj2_morE (P:=ctxD_cbv (drop_names G)) Hgam_ball Hgam_setlike).
Qed.

(** One Kleene step of the fail body, exposed at the [fenv1] environment. *)
Lemma fix_chain_S_E n :
  fix_chain F n.+1 = Lfun (tensor_curry (eD_cbv' finner)) (fenv1 n).
Proof.
rewrite fix_chain_S /F tensor_curryE.
rewrite -[gam ⊗p (fix_chain F n)!]/(fenv1 n).
rewrite -[fbody]/(ne_lam "_"%string finner) eD_lam_E.
rewrite (adj_psi_at_setlike (tensor_curry (eD_cbv' finner))
           (fenv1_ball n) (fenv1_setlike n)).
exact: (der_prom _ (le_trans (cones_hom_norm_le1 _ _) (fenv1_ball n))).
Qed.

(** Each iterate, applied to the unit input, is the zero measure. *)
Lemma fail_iter_zero n :
  linhom_fun (fix_chain F n) one1 = precone_zero.
Proof.
elim: n => [ | n IH].
  by rewrite fix_chain_0 linhom_fun_zero.
rewrite fix_chain_S_E tensor_curryE -[fenv1 n ⊗p one1]/(fenv2 n).
rewrite finner_decomp.
rewrite (eD_app_at_setlike (po_robj_eq P) (po_robj_meas P) R_to_carrier_meas
           (fenv2_ball n) (fenv2_setlike n)).
rewrite (eD_tt_at_setlike (fenv2_ball n) (fenv2_setlike n)).
rewrite fail_var_E.
by rewrite (der_prom _ (fix_chain_ball HF_ball n)).
Qed.

(** [ne_fail] denotes [precone_zero] at every setlike unit-ball
    environment. *)
Theorem ne_fail_zero :
  Lfun (eD_cbv' (@ne_fail R Ar (po_robj P) G t)) gam = precone_zero.
Proof.
rewrite ne_fail_decomp.
rewrite (eD_app_at_setlike (po_robj_eq P) (po_robj_meas P) R_to_carrier_meas
           Hgam_ball Hgam_setlike).
rewrite (eD_fix_at_setlike "fail"%string fbody Hgam_ball Hgam_setlike).
rewrite -/F (der_prom _ (fix_value_ball F HF_ball)).
rewrite (eD_tt_at_setlike Hgam_ball Hgam_setlike).
rewrite (fix_value_E HF_ball).
have pwch n : precone_le (linhom_fun (fix_chain F n) one1)
                         (linhom_fun (fix_chain F n.+1) one1).
  by rewrite !fail_iter_zero; exact: precone_le0.
have pwub n : cone_norm (linhom_fun (fix_chain F n) one1) <= 1.
  by rewrite fail_iter_zero cone_norm0.
rewrite (linhom_fun_sup_ball (fix_chain_chain HF_ball)
           (fix_chain_ball HF_ball) Hone1_ball pwch pwub).
apply: precone_le_anti; last exact: precone_le0.
by apply: cone_sup_ball_lub => n; rewrite fail_iter_zero; exact: precone_le0.
Qed.

End FailZero.

Arguments ne_fail_zero {R Ar P} R_to_carrier_meas {G t gam}.

(** ** §7 — The condition/assert denotation bridge

    BEYOND THE PAPER.  The CLEAN [ne_condition] ([hard_reject.v]) denotes
    the conditioning measure.  Unlike the reject bridge, the clean
    [ne_condition] continuation [let _ = (if Test{f} x then () else fail)
    in x] is STRUCTURALLY DIFFERENT from the soft condition's
    [let _ = Score (test f x) in x], so the scrutinee-congruence shortcut
    does NOT apply.  We compute [⟦ne_condition⟧] DIRECTLY, mirroring the
    SOFT condition proof ([ex_reject_model.v::Section ConditionModel]):
    the combinator has NO recursion, so [eD] reduces via [eD_let_mu_E]
    to a Lebesgue integral over [ν_M]; at each Dirac [δ_r] the clean
    continuation computes — through [if_icones_at], [test_lift_dirac],
    [bool_case_true]/[bool_case_false] and [ne_fail_zero] — to the {0,1}
    point mass [if f0_bool r then δ_r else 0], i.e. the {0,1}
    specialisation of [cm_K_at_dirac].  Integrating gives
    [cond'(U) = ν_M (A `&` U)] and the boolean condition headlines
    transfer to the clean combinator. *)

Section ConditionDenotBridge.
Variables (R : realType) (Ar : MeasSubcat R) (P : probObj Ar).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier (po_robj_eq P)).
Variable (P_acc : set R).
Hypothesis mPacc : measurable P_acc.
Variable (Mbody :
  @named_expr R Ar (po_robj P) (("_"%string, tunit) :: nil) (tR (po_robj P))).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation "x '!'" := (prom x) (at level 2, format "x '!'").
Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.
Local Notation cR := (carrier_to_R (po_robj_eq P)).
Local Notation tR' := (tR (po_robj P)).
Local Notation eD_cbv' :=
  (@eD_cbv R Ar (po_robj P) (po_robj_eq P) (po_robj_meas P)
           R_to_carrier_meas _ _).
Local Notation eD' :=
  (@eD R Ar (po_robj P) (po_robj_eq P) (po_robj_meas P)
       R_to_carrier_meas _ _).

(** The meta boolean test (same object as the reject bridge). *)
Definition f0b : ar_carrier Ar (po_robj P) -> bool :=
  fun r => cR r \in P_acc.

Lemma Hf0b : measurable_fun [set: ar_carrier Ar (po_robj P)] f0b.
Proof.
apply: (measurable_fun_bool true); rewrite setTI.
have -> : f0b @^-1` [set true] = cR @^-1` P_acc.
  rewrite predeqE => r; rewrite /f0b /preimage/=; split => H.
  - exact: set_mem H.
  - exact: mem_set H.
have H := (po_robj_meas P) measurableT P_acc mPacc; rewrite setTI in H.
exact: H.
Qed.

(** Abbreviations matching the soft [ConditionModel] set-up at
    [ta := tunit], [g := model_lin], [a₀ := one1]. *)
Local Notation Lty t1 t2 :=
  (linhom_car Ar (coalg_obj (tyD_cbv t1)) (coalg_obj (tyD_cbv t2))).
Local Notation tmod := (tfun tunit tR').
Local Notation Bmod := (Lty tunit tR').
Local Notation mlin := (model_lin (P:=P) R_to_carrier_meas Mbody).
Local Notation nu0 :=
  (reject_model_dist (P:=P) (ta:=tunit) mlin one1).

(** The clean combinator and its context tower. *)
Local Notation COMB := (ne_condition (R_obj := po_robj P) tunit f0b Hf0b).
Local Notation cctx_m := (("m"%string, tmod) :: nil).
Local Notation cctx_a := (("a"%string, tunit) :: ("m"%string, tmod) :: nil).
Local Notation cctx_x :=
  (("x"%string, tR') :: ("a"%string, tunit) :: ("m"%string, tmod) :: nil).
Local Notation cctx_u :=
  (("_"%string, tunit) :: ("x"%string, tR') :: ("a"%string, tunit) ::
   ("m"%string, tmod) :: nil).

Definition cc_var_m : @named_expr R Ar (po_robj P) cctx_a tmod := [ # "m" ].
Definition cc_var_a : @named_expr R Ar (po_robj P) cctx_a tunit := [ # "a" ].
Definition cc_var_x : @named_expr R Ar (po_robj P) cctx_x tR' := [ # "x" ].
Definition cc_ret   : @named_expr R Ar (po_robj P) cctx_u tR' := [ # "x" ].

(** The clean scrutinee [if Test{f} x then () else fail] and the
    score-free continuation. *)
Definition cleanScrut : @named_expr R Ar (po_robj P) cctx_x tunit :=
  ne_if tunit (ne_test f0b Hf0b cc_var_x) ne_tt ne_fail.
Definition cc_K : @named_expr R Ar (po_robj P) cctx_x tR' :=
  ne_let "_" cleanScrut cc_ret.
Definition cc_inner : @named_expr R Ar (po_robj P) cctx_a tR' :=
  ne_let "x" (ne_app cc_var_m cc_var_a) cc_K.

Local Notation cc_fun := (ne_lam "a"%string cc_inner).

Definition condition_prog' : @named_expr R Ar (po_robj P) nil tR' :=
  [ {COMB} @ {model_prog (P:=P) Mbody} @ () ].

(** *** Semantic plumbing *)

Let Hone1 : cone_norm (one1 : cone_one_car Ar) <= 1.
Proof. by rewrite one1_norm. Qed.

Let HoneG : cone_norm
    (one1 : coalg_obj (ctxD_cbv (drop_names (nil : named_ctx Ar)))) <= 1.
Proof. by rewrite one1_norm. Qed.

Let Hmlin_ball : cone_norm mlin <= 1.
Proof. exact: (model_lin_ball (P:=P) R_to_carrier_meas Mbody). Qed.

Lemma cc_g_ball : cone_norm (mlin!) <= 1.
Proof. exact: prom_ball Hmlin_ball. Qed.

Lemma cc_g_setlike :
  Lfun (coalg_str (tyD_cbv tmod)) (mlin!) = (mlin!)!.
Proof.
rewrite -[tyD_cbv tmod]/(bang_cofree (Lty tunit tR')) bang_cofree_str.
exact: (dig_prom _ Hmlin_ball).
Qed.

Definition cc_env1 : coalg_obj (ctxD_cbv (drop_names cctx_m)) :=
  one1 ⊗p (mlin!).
Definition cc_env2 : coalg_obj (ctxD_cbv (drop_names cctx_a)) :=
  cc_env1 ⊗p one1.
Definition cc_env3 (r : ar_carrier Ar (po_robj P)) :
    coalg_obj (ctxD_cbv (drop_names cctx_x)) :=
  cc_env2 ⊗p dirac_fmeas r.

Lemma cc_env1_ball : cone_norm cc_env1 <= 1.
Proof. by rewrite /cc_env1 tensor_normME one1_norm mul1r cc_g_ball. Qed.

Lemma cc_env1_setlike :
  Lfun (coalg_str (ctxD_cbv (drop_names cctx_m))) cc_env1 = cc_env1!.
Proof.
exact: (coalg_str_tensor_setlike (P:=EM_term) (Q:=tyD_cbv tmod)
          Hone1 cc_g_ball coalg_str_one1 cc_g_setlike).
Qed.

Lemma cc_env2_ball : cone_norm cc_env2 <= 1.
Proof.
rewrite /cc_env2 tensor_normME.
by rewrite mulr_ile1 ?cone_norm_ge0 ?cc_env1_ball ?Hone1.
Qed.

Lemma cc_env2_setlike :
  Lfun (coalg_str (ctxD_cbv (drop_names cctx_a))) cc_env2 = cc_env2!.
Proof.
exact: (coalg_str_tensor_setlike (P:=ctxD_cbv (drop_names cctx_m))
          (Q:=tyD_cbv tunit) cc_env1_ball Hone1 cc_env1_setlike coalg_str_one1).
Qed.

Lemma cc_env3_ball r : cone_norm (cc_env3 r) <= 1.
Proof.
rewrite /cc_env3 tensor_normME.
by rewrite mulr_ile1 ?cone_norm_ge0 ?cc_env2_ball ?dirac_fmeas_norm_le1.
Qed.

Lemma cc_env3_setlike r :
  Lfun (coalg_str (ctxD_cbv (drop_names cctx_x))) (cc_env3 r) = (cc_env3 r)!.
Proof.
exact: (coalg_str_tensor_setlike (P:=ctxD_cbv (drop_names cctx_a))
          (Q:=FMeas_coalgebra (po_robj P)) cc_env2_ball (dirac_fmeas_norm_le1 r)
          cc_env2_setlike (Coalg_dirac (po_robj P) r)).
Qed.

(** *** The combinator value and the application collapses *)

Definition cc_comb_val : coalg_obj (tyD_cbv (tfun tmod tmod)) :=
  Lfun (eD_cbv' COMB) one1.

Definition cc_fun_lin : Lty tmod tmod :=
  Lfun (tensor_curry (eD_cbv' cc_fun)) one1.

Definition cc_model_denot : coalg_obj (tyD_cbv tR') :=
  linhom_fun
    (Lfun (der Bmod)
       (linhom_fun (Lfun (der (Lty tmod tmod)) cc_comb_val) (mlin!)))
    one1.

Lemma cc_comb_decomp : COMB = ne_lam "m"%string cc_fun.
Proof. by []. Qed.

Lemma cc_comb_val_E : cc_comb_val = cc_fun_lin!.
Proof.
rewrite /cc_comb_val cc_comb_decomp eD_lam_E.
by rewrite (adj_psi_at_setlike (tensor_curry (eD_cbv' cc_fun))
              Hone1 coalg_str_one1).
Qed.

Lemma cc_fun_lin_ball : cone_norm cc_fun_lin <= 1.
Proof. exact: le_trans (cones_hom_norm_le1 _ _) Hone1. Qed.

Lemma cc_fun_at_g :
  linhom_fun cc_fun_lin (mlin!) =
  (Lfun (tensor_curry (eD_cbv' cc_inner)) cc_env1)!.
Proof.
rewrite /cc_fun_lin tensor_curryE eD_lam_E.
exact: (adj_psi_at_setlike (P:=ctxD_cbv (drop_names cctx_m))
          _ cc_env1_ball cc_env1_setlike).
Qed.

Lemma cc_model_denot_E :
  cc_model_denot = Lfun (eD_cbv' cc_inner) cc_env2.
Proof.
rewrite /cc_model_denot cc_comb_val_E.
rewrite (der_prom _ cc_fun_lin_ball) cc_fun_at_g.
rewrite (der_prom _ (le_trans (cones_hom_norm_le1 _ _) cc_env1_ball)).
exact: tensor_curryE.
Qed.

Lemma cc_prog_val : Lfun (eD_cbv' condition_prog') one1 = cc_model_denot.
Proof.
rewrite -[condition_prog']/(ne_app (ne_app COMB (model_prog (P:=P) Mbody))
  (@ne_tt R Ar (po_robj P) nil)).
rewrite (eD_app_at_setlike (po_robj_eq P) (po_robj_meas P) R_to_carrier_meas
           HoneG coalg_str_one1).
rewrite (eD_app_at_setlike (po_robj_eq P) (po_robj_meas P) R_to_carrier_meas
           HoneG coalg_str_one1).
by rewrite (model_prog_val_E (P:=P) R_to_carrier_meas Mbody)
           (tt_val_E (P:=P) R_to_carrier_meas).
Qed.

(** *** Variable projections and the model application *)

Lemma cc_var_a_E : Lfun (eD_cbv' cc_var_a) cc_env2 = one1.
Proof.
apply: (eq_trans (y := Lfun (em_proj2_mor (R:=R)
  (ctxD_cbv (drop_names cctx_m)) (tyD_cbv tunit)) cc_env2)).
  by [].
exact: (em_proj2_morE cc_env1_ball cc_env1_setlike).
Qed.

Lemma cc_var_m_E : Lfun (eD_cbv' cc_var_m) cc_env2 = (mlin!).
Proof.
apply: (eq_trans (y := Lfun (icones_comp
  (em_proj2_mor (R:=R) EM_term (tyD_cbv tmod))
  (em_proj1_mor (R:=R) (ctxD_cbv (drop_names cctx_m)) (tyD_cbv tunit)))
  cc_env2)).
  by [].
rewrite Lfun_comp.
rewrite (em_proj1_morE (Q:=tyD_cbv tunit) Hone1 coalg_str_one1).
exact: (em_proj2_morE (P:=EM_term) Hone1 coalg_str_one1).
Qed.

Lemma cc_app_E :
  Lfun (eD_cbv' (ne_app cc_var_m cc_var_a)) cc_env2 = nu0.
Proof.
rewrite (eD_app_at_setlike (po_robj_eq P) (po_robj_meas P) R_to_carrier_meas
           cc_env2_ball cc_env2_setlike).
rewrite cc_var_m_E cc_var_a_E.
by rewrite (der_prom _ Hmlin_ball).
Qed.

(** *** The clean continuation at a Dirac — the {0,1} [cm_K_at_dirac] *)

Lemma cc_var_x_E r : Lfun (eD_cbv' cc_var_x) (cc_env3 r) = dirac_fmeas r.
Proof.
apply: (eq_trans (y := Lfun (em_proj2_mor (R:=R)
  (ctxD_cbv (drop_names cctx_a)) (FMeas_coalgebra (po_robj P))) (cc_env3 r))).
  by [].
exact: (em_proj2_morE cc_env2_ball cc_env2_setlike).
Qed.

(** The clean scrutinee at [δ_r]: the {0,1} weight — [1] (the unit value
    [()]) when [f0_bool r], else [0] (the diverging [fail], by
    [ne_fail_zero]). *)
Lemma cleanScrut_E r :
  Lfun (eD_cbv' cleanScrut) (cc_env3 r) =
  ((if f0b r then one1 else precone_zero) : cone_one_car Ar).
Proof.
rewrite /cleanScrut eD_if_E.
rewrite (if_icones_at _ _ _ (cc_env3_ball r) (cc_env3_setlike r)).
rewrite eD_test_E.
rewrite (Lfun_comp (test_lift Hf0b) (eD_cbv' cc_var_x) (cc_env3 r)).
rewrite cc_var_x_E (test_lift_dirac Hf0b r).
rewrite (eD_tt_at_setlike (cc_env3_ball r) (cc_env3_setlike r)).
rewrite (ne_fail_zero R_to_carrier_meas (cc_env3_ball r) (cc_env3_setlike r)).
by case: (f0b r); [exact: bool_case_true | exact: bool_case_false].
Qed.

Lemma cc_ret_at r (s : cone_one_car Ar) :
  Lfun (eD_cbv' cc_ret) ((cc_env3 r) ⊗p s) =
  precone_scale (c1_val s) (dirac_fmeas r).
Proof.
apply: (eq_trans (y := Lfun (icones_comp
  (em_proj2_mor (R:=R) (ctxD_cbv (drop_names cctx_a)) (FMeas_coalgebra (po_robj P)))
  (em_proj1_mor (R:=R) (ctxD_cbv (drop_names cctx_x)) EM_term))
  ((cc_env3 r) ⊗p s))).
  by [].
rewrite Lfun_comp.
rewrite (em_proj1_mor_unitE (P:=ctxD_cbv (drop_names cctx_x)) (cc_env3 r) s).
rewrite (Lfun_scaleE
  (em_proj2_mor (R:=R) (ctxD_cbv (drop_names cctx_a)) (FMeas_coalgebra (po_robj P)))
  (c1_val s) (cc_env3 r)).
by rewrite (em_proj2_morE (P:=ctxD_cbv (drop_names cctx_a))
              cc_env2_ball cc_env2_setlike).
Qed.

Lemma cm_K_clean_raw r :
  Lfun (eD_cbv' cc_K) (cc_env3 r) =
  precone_scale (c1_val ((if f0b r then one1 else precone_zero) : cone_one_car Ar))
                (dirac_fmeas r).
Proof.
rewrite /cc_K eD_let_E.
rewrite (Lfun_comp (eD_cbv' cc_ret)
  (em_pair_mor (icones_id Ar (coalg_obj (ctxD_cbv (drop_names cctx_x))))
     (eD_cbv' cleanScrut))
  (cc_env3 r)).
rewrite /em_pair_mor.
rewrite (Lfun_comp
  (tensor_mor (icones_id Ar (coalg_obj (ctxD_cbv (drop_names cctx_x))))
     (eD_cbv' cleanScrut))
  (coalg_d (ctxD_cbv (drop_names cctx_x)))
  (cc_env3 r)).
rewrite (coalg_d_setlike (P:=ctxD_cbv (drop_names cctx_x))
  (cc_env3_ball r) (cc_env3_setlike r)).
rewrite (tensor_morE
  (icones_id Ar (coalg_obj (ctxD_cbv (drop_names cctx_x))))
  (eD_cbv' cleanScrut)
  (cc_env3 r) (cc_env3 r)).
by rewrite icones_idE cleanScrut_E cc_ret_at.
Qed.

(** The {0,1} weight, as a real, is the indicator [f0 (cR r)] — exactly
    the soft likelihood specialised to the indicator bundle. *)
Lemma c1_sval_num r :
  (c1_val ((if f0b r then one1 else precone_zero) : cone_one_car Ar))%:num =
  test_fun (ind_testfn P_acc mPacc) (cR r).
Proof.
rewrite -[test_fun (ind_testfn P_acc mPacc) (cR r)]/(\1_P_acc (cR r)).
rewrite /f0b indicE.
by case: (cR r \in P_acc) => /=; rewrite ?mulr1n ?mulr0n.
Qed.

(** The {0,1} specialisation of [cm_K_at_dirac]: the clean continuation
    at [δ_r] weighs the returned point mass by the indicator. *)
Lemma cm_K_clean_at_dirac r :
  Lfun (eD_cbv' cc_K) (cc_env3 r) =
  precone_scale (NngNum (test_ge0 (ind_testfn P_acc mPacc) (cR r)))
                (dirac_fmeas r).
Proof.
rewrite cm_K_clean_raw; congr precone_scale.
apply: nngnum_inj; exact: c1_sval_num.
Qed.

(** *** The clean conditioning law (no recursion: [eD_let_mu_E]) *)

Local Open Scope ereal_scope.

Theorem condition_model_E' (U : set (ar_carrier Ar (po_robj P)))
    (mU : measurable U) :
  fmeas_mu (Lfun (eD_cbv' cc_inner) cc_env2) U =
  \int[fmeas_mu nu0]_(r in U) (test_fun (ind_testfn P_acc mPacc) (cR r))%:E.
Proof.
have Hinner : Lfun (eD_cbv' cc_inner) cc_env2 =
    linhom_fun (eD' (ne_let "x"%string (ne_app cc_var_m cc_var_a) cc_K)) cc_env2.
  by rewrite /eD icones_to_linhomE.
rewrite Hinner.
rewrite (eD_let_mu_E (po_robj_meas P) R_to_carrier_meas
           (ne_app cc_var_m cc_var_a) cc_K cc_env2_ball cc_env2_setlike mU).
rewrite cc_app_E.
under eq_integral => r _.
  rewrite cm_K_clean_at_dirac fmeas_scaleE (dirac_fmeas_E r mU) diracE -EFinM /=.
  over.
rewrite [RHS](integral_mkcond U) epatch_indic.
apply: eq_integral => r _.
by rewrite /= EFinM.
Qed.

(** *** The transferred boolean condition headlines *)

Local Notation Aacc := (@A R Ar P P_acc).
Local Notation nu_M :=
  (fmeas_mu (linhom_fun (eD (R_carrier_meas := po_robj_meas P)
     (R_to_carrier_meas := R_to_carrier_meas) (model_run (P:=P) Mbody)) one1)).
Local Notation cond' :=
  (fmeas_mu (linhom_fun (eD (R_carrier_meas := po_robj_meas P)
     (R_to_carrier_meas := R_to_carrier_meas) condition_prog') one1)).
Local Notation reject' :=
  (fmeas_mu (linhom_fun (eD (R_carrier_meas := po_robj_meas P)
     (R_to_carrier_meas := R_to_carrier_meas)
     (@reject_prog' R Ar P P_acc mPacc Mbody)) one1)).

(** [ν_M] is the model-run distribution — the §4/§6 object. *)
Lemma nu_M_E : nu_M = fmeas_mu nu0.
Proof.
congr fmeas_mu.
rewrite /eD icones_to_linhomE.
exact: (model_run_val_E (P:=P) R_to_carrier_meas Mbody).
Qed.

(** The conditioning law, boolean form: [cond'(U) = ν_M (A `&` U)]. *)
Theorem condition_bool_E' U (mU : measurable U) :
  cond' U = nu_M (Aacc `&` U).
Proof.
have Hred : linhom_fun (eD' condition_prog') one1 = Lfun (eD_cbv' cc_inner) cc_env2.
  by rewrite /eD icones_to_linhomE cc_prog_val cc_model_denot_E.
rewrite Hred (condition_model_E' mU).
rewrite (@If_bool R Ar P P_acc mPacc (fmeas_mu nu0) U mU).
by rewrite nu_M_E.
Qed.

(** The model EVIDENCE: the conditioned model's total mass is [ν_M(A)]. *)
Theorem condition_bool_evidence' : cond' setT = nu_M Aacc.
Proof.
have H := condition_bool_E' (U := setT) measurableT; rewrite setIT in H; exact: H.
Qed.

(** The equivalence — rejection sampling computes the conditioned model's
    normalised distribution (division-free):
    [(1 - ν_M(setT) + ν_M(A)) · reject'(U) = cond'(U)]. *)
Theorem reject_normalises_condition_bool' U (mU : measurable U) :
  ((1 - fine (nu_M setT) + fine (nu_M Aacc))%R)%:E * reject' U = cond' U.
Proof.
rewrite (condition_bool_E' mU).
exact: (@reject_bool_master' R Ar P R_to_carrier_meas P_acc mPacc Mbody U mU).
Qed.

(** The DIVISION form against the conditioned model. *)
Theorem reject_computes_condition_bool' :
  (0 < 1 - fine (nu_M setT) + fine (nu_M Aacc))%R ->
  forall U, measurable U ->
  reject' U =
  ((fine (cond' U) / (1 - fine (nu_M setT) + fine (nu_M Aacc)))%R)%:E.
Proof.
move=> Hpos U mU; rewrite (condition_bool_E' mU).
exact: (@reject_bool_is_normalised' R Ar P R_to_carrier_meas P_acc mPacc
          Mbody Hpos U mU).
Qed.

(** The PROBABILITY-MODEL form: for a unit-mass model the normaliser is
    the conditioned model's total mass, so [cond'(setT) · reject'(U) =
    cond'(U)]. *)
Theorem reject_normalises_condition_prob_bool' U (mU : measurable U) :
  nu_M setT = 1 -> cond' setT * reject' U = cond' U.
Proof.
move=> Hm1.
rewrite -(reject_normalises_condition_bool' mU); congr (_ * _).
rewrite condition_bool_evidence' Hm1.
have HAfin : nu_M Aacc \is a fin_num.
  by rewrite nu_M_E; apply: fmeas_fin; exact: (@mA R Ar P P_acc mPacc).
by rewrite -[in LHS](fineK HAfin)/= subrr add0r.
Qed.

End ConditionDenotBridge.
