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
