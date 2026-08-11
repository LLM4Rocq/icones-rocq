(**md**************************************************************************)
(** * CBV marginal headlines for the basic sampling/scoring examples

    BEYOND THE PAPER.  This file is NOT part of the Ehrhard-Geoffroy
    2025 formalization (paper §2-§9).  It proves, against the CBV
    interpreter [eD] of [theories/programs/ppl_cbv.v], the headline
    semantic identities of the three non-recursive basic
    sampling/scoring examples of [theories/programs/examples.v]:

    - [ex_score_posterior_cbv_E] : the denotation of
      [let m = sample µ in let _ = score f m in m] is the UNNORMALISED
      POSTERIOR: its measure on every measurable [U] is [∫_U f dµ].
      The companion [ex_reject_normalises_score] records that the
      rejection-sampling program of [ex_reject_headline.v] denotes
      exactly the normalisation of this measure.
    - [ex_random_constant_cbv_marginal] : the denotation of
      [let c = sample µ in λx. c] is a (promoted) function value;
      dereliction followed by evaluation at any probability test point
      recovers the prior [µ].  At a Dirac test point this is
      [ex_random_constant_cbv_marginal_dirac].
    - [ex_random_linear_cbv_marginal] : the denotation of
      [let m = sample µ in let b = sample µ in λx. m*x + b],
      derelicted and evaluated at a Dirac test point [δ_{r0}], has on
      every measurable [U] the iterated-integral measure
      [∫∫ δ_{m·r0+b}(U) µ(db) µ(dm)].
    - [ex_bayes_linear_cbv_evidence] (§5) : the higher-order Bayesian
      LINEAR-REGRESSION headline, for a GENERAL observation list [l] —
      the counit ("total mass") of the function-space denotation of
      [examples.v::ex_bayes_linear l] is the MODEL EVIDENCE
      [∫∫ ∏_{o ∈ l} (obs_d o)(m·(obs_x o)+b) dµ(m) dµ(b)]; the
      2-observation corollary [ex_bayes_linear_cbv_evidence2] writes
      the product literally.

    These restate, against [eD], the identities the retired CBN track
    proved; the score posterior is new content the CBN option-γ
    interpreter could not express (its score collapsed).

    Supporting kit (§1):
    - [coalg_e_FMeas_prob] — the comonoid counit of the §9.7 coalgebra
      [FMeas X] sends every probability measure to [one1] (computed
      through the Dirac-to-integral lift of [coalgebra.v] and the
      Pettis equation on [cone_one]);
    - [em_proj1_mor_unitE] / [em_proj1_mor_probE] — the first
      cartesian projection computed at NON-setlike discarded
      components: a [tunit]-typed point is discarded as its scalar
      weight, an [FMeas]-typed probability is discarded silently;
    - [Lfun_scaleE] — morphism application commutes with
      [precone_scale];
    - the one-Dirac environment [one1 ⊗ δ_r] is a setlike unit-ball
      point ([one_dirac_ball] / [one_dirac_setlike]).

    See also: [theories/programs/ex_reject_headline.v] — imported for
    the single theorem [ex_reject_master], which
    [ex_reject_normalises_score] below combines with the posterior
    identity; the setlike-point kit itself is NOT taken from there but
    from [theories/programs/infra/cbv_anchors.v].  Also
    [theories/programs/infra/let_sample_law.v] (the let-at-sample
    integral law).

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
Require Import Icones.homs.bilin.
Require Import Icones.homs.tensor.
Require Import Icones.homs.tensor_construct.
Require Import Icones.homs.tensor_iso.
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
Require Import Icones.programs.distributions.
Require Import Icones.programs.infra.em_fix.
Require Import Icones.programs.infra.em_fix_value.
Require Import Icones.programs.ppl_cbv.
Require Import Icones.programs.infra.cbv_anchors.
Require Import Icones.programs.infra.cbv_fix_unfold.
Require Import Icones.programs.infra.let_sample_law.
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

(** ** §1 — Kit: the [FMeas] counit on probabilities, projections at
    non-setlike points, one-Dirac environments *)

Section FMeasCounitKit.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

(** The comonoid counit of the §9.7 coalgebra [FMeas X] sends every
    PROBABILITY measure to [one1]: on Diracs the counit is [one1]
    (Diracs are setlike), so by the Dirac-to-integral lift the counit
    of [ν] is the integral of the constant path [one1] — the total
    mass of [ν], read off the Pettis equation on [cone_one]. *)
Lemma coalg_e_FMeas_prob (X : ar_obj Ar) (nu : FMeas X) :
  fmeas_mu nu [set: ar_carrier Ar X] = 1%E ->
  Lfun (coalg_e (FMeas_coalgebra X)) nu = one1.
Proof.
move=> Hnu1.
have Hphi : forall r : ar_carrier Ar X,
    Lfun (coalg_e (FMeas_coalgebra X)) (dirac_fmeas r) = one1.
  move=> r.
  apply: coalg_e_setlike; last exact: Coalg_dirac.
  by rewrite dirac_fmeas_norm.
have Hpath : is_measurable_path (Ar:=Ar) (C:=cone_one_car Ar) (X:=X)
    (fun _ : ar_carrier Ar X => (one1 : cone_one_car Ar)).
  exact: const_path_measurable.
rewrite (icones_hom_dirac_to_integral
           (coalg_e (FMeas_coalgebra X))
           (fun _ : ar_carrier Ar X => (one1 : cone_one_car Ar))
           Hpath Hphi nu).
apply/esym.
apply: icone_integral_eqP => m mM s.
have Em : m = ConeOneMConeAux.id_test (R:=R) (Ar:=Ar) (ar_zero Ar) := mM.
rewrite Em /ConeOneMConeAux.id_test /= /ConeOneMConeAux.id_test_fun /=.
by rewrite integral_cst// mul1e Hnu1.
Qed.

End FMeasCounitKit.

Arguments coalg_e_FMeas_prob {R Ar X nu}.

Section EMProjKit.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.

(** Discarding a [tunit]-typed component that is NOT setlike: the
    counit at [EM_term] is the identity, so the first projection
    weighs the kept component by the discarded scalar. *)
Lemma em_proj1_mor_unitE (P : Coalgebra Ar)
    (x : coalg_obj P) (s : cone_one_car Ar) :
  Lfun (em_proj1_mor (R:=R) P (EM_term : Coalgebra Ar)) (x ⊗p s) =
  precone_scale (c1_val s) x.
Proof.
rewrite /em_proj1_mor Lfun_comp tensor_morE coalg_e_term !icones_idE.
by rewrite tensor_runitEp.
Qed.

(** Discarding an [FMeas]-typed PROBABILITY component: the counit is
    [one1] ([coalg_e_FMeas_prob]), so the first projection keeps the
    other component unchanged.  No setlike hypothesis on [ν]. *)
Lemma em_proj1_mor_probE (P : Coalgebra Ar) (X : ar_obj Ar)
    (x : coalg_obj P) (nu : FMeas X) :
  fmeas_mu nu [set: ar_carrier Ar X] = 1%E ->
  Lfun (em_proj1_mor (R:=R) P (FMeas_coalgebra X)) (x ⊗p nu) = x.
Proof.
move=> Hnu1.
rewrite /em_proj1_mor Lfun_comp tensor_morE (coalg_e_FMeas_prob Hnu1).
rewrite icones_idE tensor_runitEp.
by rewrite -[c1_val one1]/(1%:nng) precone_scale_1.
Qed.

(** Morphism application commutes with [precone_scale] (the [linearZ]
    field of the underlying [cones_hom]). *)
Lemma Lfun_scaleE (B C : ICone.type Ar) (h : icones_hom Ar B C)
    (c : {nonneg R}) (x : B) :
  Lfun h (precone_scale c x) = precone_scale c (Lfun h x).
Proof.
by have [_ _ HZ] := cones_hom_linear
  (mcones_hom_cones (icones_hom_mcones h)); rewrite HZ.
Qed.

End EMProjKit.

Arguments em_proj1_mor_unitE {R Ar P} x s.
Arguments em_proj1_mor_probE {R Ar P X} x {nu}.
Arguments Lfun_scaleE {R Ar B C} h c x.

(** The one-Dirac environment [one1 ⊗ δ_r] — THE context point of a
    single [tR]-binding — is a setlike unit-ball point. *)

Section OneDiracEnv.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '!'" := (prom x) (at level 2, format "x '!'").

Let Hone : cone_norm (one1 : cone_one_car Ar) <= 1.
Proof. by rewrite one1_norm. Qed.

Lemma one_dirac_ball (r : ar_carrier Ar R_obj) :
  cone_norm ((one1 : cone_one_car Ar) ⊗p dirac_fmeas r) <= 1.
Proof.
by rewrite tensor_normME one1_norm mul1r dirac_fmeas_norm_le1.
Qed.

Lemma one_dirac_setlike (r : ar_carrier Ar R_obj) :
  Lfun (coalg_str (EM_prod (EM_term : Coalgebra Ar)
                     (FMeas_coalgebra R_obj)))
       ((one1 : cone_one_car Ar) ⊗p dirac_fmeas r) =
  ((one1 : cone_one_car Ar) ⊗p dirac_fmeas r)!.
Proof.
exact: (coalg_str_tensor_setlike (P:=EM_term) (Q:=FMeas_coalgebra R_obj)
          Hone (dirac_fmeas_norm_le1 r) coalg_str_one1
          (Coalg_dirac R_obj r)).
Qed.

End OneDiracEnv.

Arguments one_dirac_ball {R Ar R_obj} r.
Arguments one_dirac_setlike {R Ar R_obj} r.

(** ** §2 — [ex_score_posterior]: the unnormalised posterior *)

Section ScorePosterior.
Variables (R : realType) (Ar : MeasSubcat R).
(* Reparameterized over the bundled [probObj]. *)
Variable (P : probObj Ar).
Local Notation R_obj := (po_robj P).
Local Notation R_carrier_eq := (po_robj_eq P).
Local Notation R_carrier_meas := (po_robj_meas P).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

(** The prior: a unit-ball measure on the reals. *)
Variable (pm : pmeas Ar R_obj).
Local Notation mu := (pm_meas pm).
Local Notation Hmu := (pm_ball pm).

(** The soft evidence as a BUNDLED [[0,1]]-valued test function; its
    projections are exposed under their historical names. *)
Variable (f : testfn R).
Local Notation Hf_meas := (test_meas f).
Local Notation Hf_ge0 := (test_ge0 f).
Local Notation Hf_le1 := (test_le1 f).

(** The bundle factoring of [f] into the probability object, the
    clean-surface [tProb]-score map behind [Sc (ToProb f #"m")]. *)
Local Notation sp_phi := (po_into P f Hf_meas Hf_ge0 Hf_le1).

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

Let Hone : cone_norm (one1 : cone_one_car Ar) <= 1.
Proof. by rewrite one1_norm. Qed.

(** *** Syntactic decomposition — all definitional *)

(** The scored variable [#m], in the prior-extended context. *)
Definition sp_var_m : @named_expr R Ar R_obj (("m"%string, tR') :: nil) tR' :=
  [ # "m" ].

(** The returned variable [#m], under the score binder. *)
Definition sp_body :
    @named_expr R Ar R_obj
      (("_"%string, tunit) :: ("m"%string, tR') :: nil) tR' :=
  [ # "m" ].

(** The clean [tProb]-score node: weigh by [po_density P] of the
    factored value [ToProb sp_phi #"m"]. *)
Local Notation sp_score :=
  (ne_score_p (po_density P) (po_density_meas P) (po_ge0 P) (po_le1 P)
     (ne_to_prob sp_phi sp_var_m)).

Lemma ex_sp_cont_decomp :
  ex_sp_cont f =
  ne_let "_" sp_score sp_body.
Proof. by []. Qed.

Lemma ex_score_posterior_decomp :
  ex_score_posterior pm f =
  ne_let "m" (ne_sample mu Hmu) (ex_sp_cont f).
Proof. by []. Qed.

(** *** The continuation at the Dirac environment

    At [one1 ⊗ δ_r] the score clause weighs the returned point mass by
    the density: [⟦let _ = score f m in m⟧(1 ⊗ δ_r) = (f r)·δ_r]. *)

(** The scored variable projects the bound sample. *)
Lemma sp_var_m_E (r : ar_carrier Ar R_obj) :
  Lfun (eD_cbv' sp_var_m) (one1 ⊗p dirac_fmeas r) = dirac_fmeas r.
Proof.
apply: (eq_trans (y := Lfun (em_proj2_mor (R:=R) EM_term
                              (FMeas_coalgebra R_obj))
                            (one1 ⊗p dirac_fmeas r))).
  by [].
exact: (em_proj2_morE (P:=EM_term) Hone coalg_str_one1).
Qed.

(** The score value at [δ_r] is the scalar [f r] (the bundled
    [ne_score] node desugared directly — no clamp transport — then
    [score_lift_dirac]). *)
Lemma sp_score_E (r : ar_carrier Ar R_obj) :
  Lfun (eD_cbv' sp_score)
       (one1 ⊗p dirac_fmeas r) =
  MkConeOne Ar (NngNum (Hf_ge0 (cR r))).
Proof.
(* Clean-surface score leaf: push the sampled real through the bundle
   factoring [po_into f] and read off the score scalar with
   [score_lift_P]; [po_into_E] recovers [f r]. *)
rewrite eD_score_p_E.
rewrite -[score_lift_g _ _ _]/(score_lift_P P).
rewrite (Lfun_comp (score_lift_P P) (eD_cbv' (ne_to_prob sp_phi sp_var_m))
  (one1 ⊗p dirac_fmeas r)).
rewrite eD_to_prob_E.
rewrite (Lfun_comp (FMeas_fmap sp_phi) (eD_cbv' sp_var_m)
  (one1 ⊗p dirac_fmeas r)).
rewrite sp_var_m_E FMeas_fmap_dirac score_lift_P_dirac.
apply: cone_one_eq; apply: val_inj => /=.
by rewrite /po_density po_into_E.
Qed.

(** The returned variable under the score binder: the [tunit]-typed
    score result is NOT setlike, so the first projection is computed
    by [em_proj1_mor_unitE] — the score scalar becomes a
    [precone_scale] weight, pulled through the second projection by
    linearity. *)
Lemma sp_body_at (r : ar_carrier Ar R_obj) (s : cone_one_car Ar) :
  Lfun (eD_cbv' sp_body) ((one1 ⊗p dirac_fmeas r) ⊗p s) =
  precone_scale (c1_val s) (dirac_fmeas r).
Proof.
apply: (eq_trans (y := Lfun (icones_comp
  (em_proj2_mor (R:=R) EM_term (FMeas_coalgebra R_obj))
  (em_proj1_mor (R:=R)
     (ctxD_cbv (drop_names (("m"%string, tR') :: nil))) EM_term))
  ((one1 ⊗p dirac_fmeas r) ⊗p s))).
  by [].
rewrite Lfun_comp.
rewrite (em_proj1_mor_unitE
  (P:=ctxD_cbv (drop_names (("m"%string, tR') :: nil)))
  (one1 ⊗p dirac_fmeas r) s).
rewrite (Lfun_scaleE
  (em_proj2_mor (R:=R) EM_term (FMeas_coalgebra R_obj))
  (c1_val s) (one1 ⊗p dirac_fmeas r)).
by rewrite (em_proj2_morE (P:=EM_term) Hone coalg_str_one1).
Qed.

Lemma sp_cont_at_dirac (r : ar_carrier Ar R_obj) :
  Lfun (eD_cbv' (ex_sp_cont f))
       (one1 ⊗p dirac_fmeas r) =
  precone_scale (NngNum (Hf_ge0 (cR r))) (dirac_fmeas r).
Proof.
rewrite ex_sp_cont_decomp eD_let_E.
rewrite (Lfun_comp (eD_cbv' sp_body)
  (em_pair_mor
     (icones_id Ar
        (coalg_obj (ctxD_cbv (drop_names (("m"%string, tR') :: nil)))))
     (eD_cbv' sp_score))
  (one1 ⊗p dirac_fmeas r)).
rewrite /em_pair_mor.
rewrite (Lfun_comp
  (tensor_mor
     (icones_id Ar
        (coalg_obj (ctxD_cbv (drop_names (("m"%string, tR') :: nil)))))
     (eD_cbv' sp_score))
  (coalg_d (ctxD_cbv (drop_names (("m"%string, tR') :: nil))))
  (one1 ⊗p dirac_fmeas r)).
rewrite (coalg_d_setlike (P:=ctxD_cbv (drop_names (("m"%string, tR') :: nil)))
  (one_dirac_ball r) (one_dirac_setlike r)).
rewrite (tensor_morE
  (icones_id Ar (coalg_obj (ctxD_cbv (drop_names (("m"%string, tR') :: nil)))))
  (eD_cbv' sp_score)
  (one1 ⊗p dirac_fmeas r) (one1 ⊗p dirac_fmeas r)).
by rewrite icones_idE sp_score_E sp_body_at.
Qed.

(** *** Main result — the unnormalised posterior

    On every measurable [U], the denotation of [ex_score_posterior] is
    [∫_U f dµ] — the prior reweighted by the evidence density, NOT
    normalised.  This is the identity the retired CBN interpreter
    could not state (its score collapsed). *)

Local Open Scope ereal_scope.

Theorem ex_score_posterior_cbv_E (U : set (ar_carrier Ar R_obj))
    (mU : measurable U) :
  fmeas_mu
    (linhom_fun (ex_score_posterior_cbv P R_to_carrier_meas pm f) one1) U =
  \int[fmeas_mu mu]_(r in U) (f (cR r))%:E.
Proof.
rewrite /ex_score_posterior_cbv ex_score_posterior_decomp.
rewrite (eD_let_sample_mu_E R_carrier_meas R_to_carrier_meas Hmu
           (ex_sp_cont f) one1 mU).
under eq_integral => r _.
  rewrite sp_cont_at_dirac.
  rewrite fmeas_scaleE (dirac_fmeas_E r mU) diracE -EFinM /=.
  over.
rewrite [RHS](integral_mkcond U) epatch_indic.
apply: eq_integral => r _.
by rewrite /= EFinM.
Qed.

(** Mass corollary: the total evidence [∫ f dµ]. *)
Theorem ex_score_posterior_cbv_mass :
  fmeas_mu
    (linhom_fun (ex_score_posterior_cbv P R_to_carrier_meas pm f) one1)
    [set: ar_carrier Ar R_obj] =
  \int[fmeas_mu mu]_(r in [set: ar_carrier Ar R_obj]) (f (cR r))%:E.
Proof. by apply: ex_score_posterior_cbv_E. Qed.

(** Rejection sampling normalises exactly this measure: combining
    [ex_reject_master] with the posterior identity, the rejection
    denotation times the total evidence is the Bayes denotation. *)
Theorem ex_reject_normalises_score
    (Hmu1 : fmeas_mu mu [set: ar_carrier Ar R_obj] = 1)
    (U : set (ar_carrier Ar R_obj)) (mU : measurable U) :
  (\int[fmeas_mu mu]_(r in [set: ar_carrier Ar R_obj]) (f (cR r))%:E) *
  fmeas_mu
    (linhom_fun (ex_reject_cbv P R_to_carrier_meas pm f) one1) U =
  fmeas_mu
    (linhom_fun (ex_score_posterior_cbv P R_to_carrier_meas pm f) one1) U.
Proof.
rewrite (ex_score_posterior_cbv_E mU).
exact: (ex_reject_master R_to_carrier_meas Hmu1 f mU).
Qed.

End ScorePosterior.

(** ** §3 — [ex_random_constant]: the sampled constant's marginal *)

Section RandomConstantMarginal.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

(** The prior: a unit-ball measure on the reals. *)
Variable (pm : pmeas Ar R_obj).
Local Notation mu := (pm_meas pm).
Local Notation Hmu := (pm_ball pm).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '!'" := (prom x) (at level 2, format "x '!'").
Local Notation eD_cbv' :=
  (@eD_cbv R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation eD' :=
  (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation tR' := (tR R_obj).
Local Notation Lty t1 t2 :=
  (linhom_car Ar (coalg_obj (tyD_cbv t1)) (coalg_obj (tyD_cbv t2))).

Let Hone : cone_norm (one1 : cone_one_car Ar) <= 1.
Proof. by rewrite one1_norm. Qed.

(** *** Syntactic decomposition — definitional *)

(** The lambda body [#c], under the [x]-binder. *)
Definition rc_var_c :
    @named_expr R Ar R_obj
      (("x"%string, tR') :: ("c"%string, tR') :: nil) tR' :=
  [ # "c" ].

Lemma ex_random_constant_decomp :
  ex_random_constant pm = ne_let "c" (ne_sample mu Hmu)
                                (ne_lam "x" rc_var_c).
Proof. by []. Qed.

(** *** The closure value at a sampled constant [δ_c] *)

(** [ℓ_c] — the function value of [λx. c] over the environment
    [one1 ⊗ δ_c]. *)
Definition rc_clo (c : ar_carrier Ar R_obj) : Lty tR' tR' :=
  Lfun (tensor_curry (eD_cbv' rc_var_c)) (one1 ⊗p dirac_fmeas c).

Lemma rc_clo_ball (c : ar_carrier Ar R_obj) : cone_norm (rc_clo c) <= 1.
Proof.
exact: le_trans (cones_hom_norm_le1 _ _) (one_dirac_ball c).
Qed.

(** The lambda clause PROMOTES the closure at the setlike one-Dirac
    environment. *)
Lemma rc_lam_at (c : ar_carrier Ar R_obj) :
  Lfun (eD_cbv' (ne_lam "x" rc_var_c)) (one1 ⊗p dirac_fmeas c) =
  (rc_clo c)!.
Proof.
rewrite eD_lam_E.
exact: (adj_psi_at_setlike
  (P:=ctxD_cbv (drop_names (("c"%string, tR') :: nil)))
  (tensor_curry (eD_cbv' rc_var_c))
  (one_dirac_ball c) (one_dirac_setlike c)).
Qed.

(** The body at a probability argument [x]: the unused [x] is
    discarded silently ([em_proj1_mor_probE]) and the closure returns
    the captured constant [δ_c]. *)
Lemma rc_var_c_at (c : ar_carrier Ar R_obj) (x : FMeas R_obj) :
  fmeas_mu x [set: ar_carrier Ar R_obj] = 1%E ->
  Lfun (eD_cbv' rc_var_c) ((one1 ⊗p dirac_fmeas c) ⊗p x) =
  dirac_fmeas c.
Proof.
move=> Hx1.
apply: (eq_trans (y := Lfun (icones_comp
  (em_proj2_mor (R:=R) EM_term (FMeas_coalgebra R_obj))
  (em_proj1_mor (R:=R)
     (ctxD_cbv (drop_names (("c"%string, tR') :: nil)))
     (FMeas_coalgebra R_obj)))
  ((one1 ⊗p dirac_fmeas c) ⊗p x))).
  by [].
rewrite Lfun_comp.
rewrite (em_proj1_mor_probE
  (P:=ctxD_cbv (drop_names (("c"%string, tR') :: nil)))
  (one1 ⊗p dirac_fmeas c) Hx1).
exact: (em_proj2_morE (P:=EM_term) Hone coalg_str_one1).
Qed.

(** *** Main result — the marginal recovers the prior

    The denotation of [let c = sample µ in λx. c] lives in [!(L)];
    derelicting it and evaluating at any PROBABILITY test point [x]
    yields the prior [µ] itself: the let-at-sample law turns the
    denotation into the Pettis integral [∫ (ℓ_c)! µ(dc)], dereliction
    and evaluation push inside the integral ([icones_hom_pres_int] /
    [linhom_int_eval]), the integrand computes to [δ_c], and
    [∫ δ_c µ(dc) = µ]. *)
Theorem ex_random_constant_cbv_marginal (x : FMeas R_obj) :
  fmeas_mu x [set: ar_carrier Ar R_obj] = 1%E ->
  linhom_fun
    (Lfun (der (Lty tR' tR'))
       (linhom_fun (ex_random_constant_cbv R_carrier_meas
                      R_to_carrier_meas pm) one1)) x = mu.
Proof.
move=> Hx1.
rewrite /ex_random_constant_cbv ex_random_constant_decomp.
rewrite (eD_let_sample_int R_carrier_meas R_to_carrier_meas Hmu
           (ne_lam "x" rc_var_c) one1).
rewrite (icones_hom_pres_int (der (Lty tR' tR')) R_obj _
  (let_sample_path R_carrier_meas R_to_carrier_meas
     (ne_lam "x" rc_var_c) one1) mu).
rewrite (linhom_int_eval
  (mcones_hom_pres_path (der (Lty tR' tR')) R_obj
     (fun r : ar_carrier Ar R_obj =>
      Lfun (eD_cbv' (ne_lam "x" rc_var_c)) (one1 ⊗p dirac_fmeas r))
     (let_sample_path R_carrier_meas R_to_carrier_meas
        (ne_lam "x" rc_var_c) one1)) mu x).
have Hpt : forall c : ar_carrier Ar R_obj,
    linhom_fun
      (Lfun (der (Lty tR' tR'))
         (Lfun (eD_cbv' (ne_lam "x" rc_var_c)) (one1 ⊗p dirac_fmeas c)))
      x = dirac_fmeas c.
  move=> c.
  rewrite rc_lam_at (der_prom _ (rc_clo_ball c)).
  rewrite /rc_clo tensor_curryE.
  by apply: rc_var_c_at.
rewrite (icone_integral_ext _ (dirac_fmeas_is_path R_obj) mu Hpt).
exact: icone_integral_dirac_fmeas.
Qed.

(** At a Dirac test point: the marginal is the prior. *)
Theorem ex_random_constant_cbv_marginal_dirac (r0 : ar_carrier Ar R_obj) :
  linhom_fun
    (Lfun (der (Lty tR' tR'))
       (linhom_fun (ex_random_constant_cbv R_carrier_meas
                      R_to_carrier_meas pm) one1)) (dirac_fmeas r0) = mu.
Proof.
apply: ex_random_constant_cbv_marginal.
exact: dirac_fmeas_setT_E.
Qed.

(** Mass corollary: the marginal agrees with the prior on every
    measurable [U]. *)
Theorem ex_random_constant_cbv_marginal_mass (x : FMeas R_obj)
    (Hx1 : fmeas_mu x [set: ar_carrier Ar R_obj] = 1%E)
    (U : set (ar_carrier Ar R_obj)) :
  fmeas_mu
    (linhom_fun
       (Lfun (der (Lty tR' tR'))
          (linhom_fun (ex_random_constant_cbv R_carrier_meas
                         R_to_carrier_meas pm) one1)) x) U =
  fmeas_mu mu U.
Proof. by rewrite (ex_random_constant_cbv_marginal Hx1). Qed.

End RandomConstantMarginal.

(** ** §4 — [ex_random_linear]: the marginal at a Dirac test point *)

Section RandomLinearMarginal.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

(** The prior: a unit-ball measure on the reals. *)
Variable (pm : pmeas Ar R_obj).
Local Notation mu := (pm_meas pm).
Local Notation Hmu := (pm_ball pm).

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

Let Hone : cone_norm (one1 : cone_one_car Ar) <= 1.
Proof. by rewrite one1_norm. Qed.

(** *** Syntactic decomposition — all definitional *)

(** The lambda body and its three variables, in the full context. *)
Definition rl_body :
    @named_expr R Ar R_obj
      (("x"%string, tR') :: ("b"%string, tR') :: ("m"%string, tR') :: nil)
      tR' :=
  [ # "m" * # "x" + # "b" ].

Definition rl_var_m :
    @named_expr R Ar R_obj
      (("x"%string, tR') :: ("b"%string, tR') :: ("m"%string, tR') :: nil)
      tR' :=
  [ # "m" ].

Definition rl_var_x :
    @named_expr R Ar R_obj
      (("x"%string, tR') :: ("b"%string, tR') :: ("m"%string, tR') :: nil)
      tR' :=
  [ # "x" ].

Definition rl_var_b :
    @named_expr R Ar R_obj
      (("x"%string, tR') :: ("b"%string, tR') :: ("m"%string, tR') :: nil)
      tR' :=
  [ # "b" ].

Lemma rl_body_decomp :
  rl_body = ne_add (ne_mul rl_var_m rl_var_x) rl_var_b.
Proof. by []. Qed.

Lemma ex_random_linear_decomp :
  ex_random_linear pm =
  ne_let "m" (ne_sample mu Hmu) (ex_rl_inner pm).
Proof. by []. Qed.

Lemma ex_rl_inner_decomp :
  ex_rl_inner pm =
  ne_let "b" (ne_sample mu Hmu) (ne_lam "x" rl_body).
Proof. by []. Qed.

(** *** The two-Dirac environments are setlike unit-ball points *)

Definition rl_env2 (m b : ar_carrier Ar R_obj) :
    coalg_obj (ctxD_cbv (drop_names
      (("b"%string, tR') :: ("m"%string, tR') :: nil))) :=
  (one1 ⊗p dirac_fmeas m) ⊗p dirac_fmeas b.

Lemma rl_env2_ball (m b : ar_carrier Ar R_obj) :
  cone_norm (rl_env2 m b) <= 1.
Proof.
rewrite /rl_env2 tensor_normME.
by rewrite mulr_ile1 ?cone_norm_ge0 ?(one_dirac_ball m)
   ?dirac_fmeas_norm_le1.
Qed.

Lemma rl_env2_setlike (m b : ar_carrier Ar R_obj) :
  Lfun (coalg_str (ctxD_cbv (drop_names
         (("b"%string, tR') :: ("m"%string, tR') :: nil))))
       (rl_env2 m b) = (rl_env2 m b)!.
Proof.
exact: (coalg_str_tensor_setlike
          (P:=ctxD_cbv (drop_names (("m"%string, tR') :: nil)))
          (Q:=FMeas_coalgebra R_obj)
          (one_dirac_ball m) (dirac_fmeas_norm_le1 b)
          (one_dirac_setlike m) (Coalg_dirac R_obj b)).
Qed.

Definition rl_env3 (m b r0 : ar_carrier Ar R_obj) :
    coalg_obj (ctxD_cbv (drop_names
      (("x"%string, tR') :: ("b"%string, tR') :: ("m"%string, tR')
       :: nil))) :=
  rl_env2 m b ⊗p dirac_fmeas r0.

Lemma rl_env3_ball (m b r0 : ar_carrier Ar R_obj) :
  cone_norm (rl_env3 m b r0) <= 1.
Proof.
rewrite /rl_env3 tensor_normME.
by rewrite mulr_ile1 ?cone_norm_ge0 ?rl_env2_ball ?dirac_fmeas_norm_le1.
Qed.

Lemma rl_env3_setlike (m b r0 : ar_carrier Ar R_obj) :
  Lfun (coalg_str (ctxD_cbv (drop_names
         (("x"%string, tR') :: ("b"%string, tR') :: ("m"%string, tR')
          :: nil))))
       (rl_env3 m b r0) = (rl_env3 m b r0)!.
Proof.
exact: (coalg_str_tensor_setlike
          (P:=ctxD_cbv (drop_names
                (("b"%string, tR') :: ("m"%string, tR') :: nil)))
          (Q:=FMeas_coalgebra R_obj)
          (rl_env2_ball m b) (dirac_fmeas_norm_le1 r0)
          (rl_env2_setlike m b) (Coalg_dirac R_obj r0)).
Qed.

(** *** The variable projections at the three-Dirac environment *)

Lemma rl_var_x_E (m b r0 : ar_carrier Ar R_obj) :
  Lfun (eD_cbv' rl_var_x) (rl_env3 m b r0) = dirac_fmeas r0.
Proof.
apply: (eq_trans (y := Lfun (em_proj2_mor (R:=R)
  (ctxD_cbv (drop_names
     (("b"%string, tR') :: ("m"%string, tR') :: nil)))
  (FMeas_coalgebra R_obj)) (rl_env3 m b r0))).
  by [].
exact: (em_proj2_morE (rl_env2_ball m b) (rl_env2_setlike m b)).
Qed.

Lemma rl_var_b_E (m b r0 : ar_carrier Ar R_obj) :
  Lfun (eD_cbv' rl_var_b) (rl_env3 m b r0) = dirac_fmeas b.
Proof.
apply: (eq_trans (y := Lfun (icones_comp
  (em_proj2_mor (R:=R)
     (ctxD_cbv (drop_names (("m"%string, tR') :: nil)))
     (FMeas_coalgebra R_obj))
  (em_proj1_mor (R:=R)
     (ctxD_cbv (drop_names
        (("b"%string, tR') :: ("m"%string, tR') :: nil)))
     (FMeas_coalgebra R_obj))) (rl_env3 m b r0))).
  by [].
rewrite Lfun_comp.
rewrite (em_proj1_morE (Q:=FMeas_coalgebra R_obj)
           (dirac_fmeas_norm_le1 r0) (Coalg_dirac R_obj r0)).
rewrite /rl_env2.
exact: (em_proj2_morE
          (P:=ctxD_cbv (drop_names (("m"%string, tR') :: nil)))
          (Q:=FMeas_coalgebra R_obj)
          (one_dirac_ball m) (one_dirac_setlike m)).
Qed.

Lemma rl_var_m_E (m b r0 : ar_carrier Ar R_obj) :
  Lfun (eD_cbv' rl_var_m) (rl_env3 m b r0) = dirac_fmeas m.
Proof.
apply: (eq_trans (y := Lfun (icones_comp
  (icones_comp
    (em_proj2_mor (R:=R) EM_term (FMeas_coalgebra R_obj))
    (em_proj1_mor (R:=R)
       (ctxD_cbv (drop_names (("m"%string, tR') :: nil)))
       (FMeas_coalgebra R_obj)))
  (em_proj1_mor (R:=R)
     (ctxD_cbv (drop_names
        (("b"%string, tR') :: ("m"%string, tR') :: nil)))
     (FMeas_coalgebra R_obj))) (rl_env3 m b r0))).
  by [].
rewrite Lfun_comp Lfun_comp.
rewrite (em_proj1_morE (Q:=FMeas_coalgebra R_obj)
           (dirac_fmeas_norm_le1 r0) (Coalg_dirac R_obj r0)).
rewrite /rl_env2.
rewrite (em_proj1_morE (Q:=FMeas_coalgebra R_obj)
           (dirac_fmeas_norm_le1 b) (Coalg_dirac R_obj b)).
exact: (em_proj2_morE (P:=EM_term) Hone coalg_str_one1).
Qed.

(** *** The body computes on Diracs through the arithmetic lifts *)

Lemma rl_mul_E (m b r0 : ar_carrier Ar R_obj) :
  Lfun (eD_cbv' (ne_mul rl_var_m rl_var_x)) (rl_env3 m b r0) =
  dirac_fmeas (R_to_carrier R_carrier_eq (cR m * cR r0)).
Proof.
rewrite eD_mul_E.
rewrite (Lfun_comp
  (@mul_lift R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas)
  (em_pair_mor (eD_cbv' rl_var_m) (eD_cbv' rl_var_x)) (rl_env3 m b r0)).
rewrite /em_pair_mor.
rewrite (Lfun_comp
  (tensor_mor (eD_cbv' rl_var_m) (eD_cbv' rl_var_x))
  (coalg_d (ctxD_cbv (drop_names
     (("x"%string, tR') :: ("b"%string, tR') :: ("m"%string, tR') :: nil))))
  (rl_env3 m b r0)).
rewrite (coalg_d_setlike (P:=ctxD_cbv (drop_names
    (("x"%string, tR') :: ("b"%string, tR') :: ("m"%string, tR') :: nil)))
  (rl_env3_ball m b r0) (rl_env3_setlike m b r0)).
rewrite (tensor_morE (eD_cbv' rl_var_m) (eD_cbv' rl_var_x)
  (rl_env3 m b r0) (rl_env3 m b r0)).
rewrite rl_var_m_E rl_var_x_E.
rewrite -{1}(carrier_to_RK R_carrier_eq m) -{1}(carrier_to_RK R_carrier_eq r0).
by rewrite (mul_lift_dirac (R_carrier_meas:=R_carrier_meas)
  (R_to_carrier_meas:=R_to_carrier_meas) (cR m) (cR r0)).
Qed.

Lemma rl_body_at (m b r0 : ar_carrier Ar R_obj) :
  Lfun (eD_cbv' rl_body) (rl_env3 m b r0) =
  dirac_fmeas (R_to_carrier R_carrier_eq (cR m * cR r0 + cR b)).
Proof.
rewrite rl_body_decomp eD_add_E.
rewrite (Lfun_comp
  (@add_lift R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas)
  (em_pair_mor (eD_cbv' (ne_mul rl_var_m rl_var_x)) (eD_cbv' rl_var_b))
  (rl_env3 m b r0)).
rewrite /em_pair_mor.
rewrite (Lfun_comp
  (tensor_mor (eD_cbv' (ne_mul rl_var_m rl_var_x)) (eD_cbv' rl_var_b))
  (coalg_d (ctxD_cbv (drop_names
     (("x"%string, tR') :: ("b"%string, tR') :: ("m"%string, tR') :: nil))))
  (rl_env3 m b r0)).
rewrite (coalg_d_setlike (P:=ctxD_cbv (drop_names
    (("x"%string, tR') :: ("b"%string, tR') :: ("m"%string, tR') :: nil)))
  (rl_env3_ball m b r0) (rl_env3_setlike m b r0)).
rewrite (tensor_morE (eD_cbv' (ne_mul rl_var_m rl_var_x)) (eD_cbv' rl_var_b)
  (rl_env3 m b r0) (rl_env3 m b r0)).
rewrite rl_mul_E rl_var_b_E.
rewrite -{1}(carrier_to_RK R_carrier_eq b).
by rewrite (add_lift_dirac (R_carrier_meas:=R_carrier_meas)
  (R_to_carrier_meas:=R_to_carrier_meas) (cR m * cR r0) (cR b)).
Qed.

(** *** The closure value and the pointwise marginal *)

(** [ℓ_{m,b}] — the function value of [λx. m*x + b] over [1 ⊗ δ_m ⊗ δ_b]. *)
Definition rl_clo (m b : ar_carrier Ar R_obj) : Lty tR' tR' :=
  Lfun (tensor_curry (eD_cbv' rl_body)) (rl_env2 m b).

Lemma rl_clo_ball (m b : ar_carrier Ar R_obj) :
  cone_norm (rl_clo m b) <= 1.
Proof.
exact: le_trans (cones_hom_norm_le1 _ _) (rl_env2_ball m b).
Qed.

Lemma rl_lam_at (m b : ar_carrier Ar R_obj) :
  Lfun (eD_cbv' (ne_lam "x" rl_body)) (rl_env2 m b) = (rl_clo m b)!.
Proof.
rewrite eD_lam_E.
exact: (adj_psi_at_setlike
  (P:=ctxD_cbv (drop_names (("b"%string, tR') :: ("m"%string, tR') :: nil)))
  (tensor_curry (eD_cbv' rl_body))
  (rl_env2_ball m b) (rl_env2_setlike m b)).
Qed.

(** The derelicted closure at the Dirac test point [δ_{r0}] is the
    point mass at [m·r0 + b]. *)
Lemma rl_marginal_pt (m b r0 : ar_carrier Ar R_obj) :
  linhom_fun
    (Lfun (der (Lty tR' tR'))
       (Lfun (eD_cbv' (ne_lam "x" rl_body)) (rl_env2 m b)))
    (dirac_fmeas r0) =
  dirac_fmeas (R_to_carrier R_carrier_eq (cR m * cR r0 + cR b)).
Proof.
rewrite rl_lam_at (der_prom _ (rl_clo_ball m b)).
rewrite /rl_clo tensor_curryE.
exact: rl_body_at.
Qed.

(** *** The marginals — the iterated-integral identities *)

Local Open Scope ereal_scope.

(** The inner continuation (one sample left) marginalises to a single
    integral over the slope offset. *)
Lemma rl_inner_marginal (m r0 : ar_carrier Ar R_obj)
    (U : set (ar_carrier Ar R_obj)) (mU : measurable U) :
  fmeas_mu
    (linhom_fun
       (Lfun (der (Lty tR' tR'))
          (Lfun (eD_cbv' (ex_rl_inner pm)) (one1 ⊗p dirac_fmeas m)))
       (dirac_fmeas r0)) U =
  \int[fmeas_mu mu]_(b in [set: ar_carrier Ar R_obj])
     (fine (fmeas_mu
        (dirac_fmeas (R_to_carrier R_carrier_eq (cR m * cR r0 + cR b)))
        U))%:E.
Proof.
have -> : Lfun (eD_cbv' (ex_rl_inner pm)) (one1 ⊗p dirac_fmeas m)
        = icone_integral
            (fun b => Lfun (eD_cbv' (ne_lam "x" rl_body))
                        ((one1 ⊗p dirac_fmeas m) ⊗p dirac_fmeas b))
            (let_sample_path R_carrier_meas R_to_carrier_meas
               (ne_lam "x" rl_body) (one1 ⊗p dirac_fmeas m)) mu.
  rewrite ex_rl_inner_decomp.
  exact: (eD_let_sample_int R_carrier_meas R_to_carrier_meas Hmu
            (ne_lam "x" rl_body) (one1 ⊗p dirac_fmeas m)).
rewrite (icones_hom_pres_int (der (Lty tR' tR')) R_obj _
  (let_sample_path R_carrier_meas R_to_carrier_meas
     (ne_lam "x" rl_body) (one1 ⊗p dirac_fmeas m)) mu).
rewrite (linhom_int_eval
  (mcones_hom_pres_path (der (Lty tR' tR')) R_obj
     (fun b : ar_carrier Ar R_obj =>
      Lfun (eD_cbv' (ne_lam "x" rl_body))
        ((one1 ⊗p dirac_fmeas m) ⊗p dirac_fmeas b))
     (let_sample_path R_carrier_meas R_to_carrier_meas
        (ne_lam "x" rl_body) (one1 ⊗p dirac_fmeas m))) mu
  (dirac_fmeas r0)).
rewrite (icone_integral_fmeas_E _ mu mU).
apply: eq_integral => b _.
by rewrite rl_marginal_pt.
Qed.

(** Main result — at a Dirac test point [δ_{r0}], the marginal of the
    sampled affine function is the iterated-integral measure
    [∫∫ δ_{m·r0+b}(U) µ(db) µ(dm)]. *)
Theorem ex_random_linear_cbv_marginal (r0 : ar_carrier Ar R_obj)
    (U : set (ar_carrier Ar R_obj)) (mU : measurable U) :
  fmeas_mu
    (linhom_fun
       (Lfun (der (Lty tR' tR'))
          (linhom_fun (ex_random_linear_cbv R_carrier_meas
                         R_to_carrier_meas pm) one1))
       (dirac_fmeas r0)) U =
  \int[fmeas_mu mu]_(m in [set: ar_carrier Ar R_obj])
    (fine (\int[fmeas_mu mu]_(b in [set: ar_carrier Ar R_obj])
       (fine (fmeas_mu
          (dirac_fmeas (R_to_carrier R_carrier_eq (cR m * cR r0 + cR b)))
          U))%:E))%:E.
Proof.
rewrite /ex_random_linear_cbv ex_random_linear_decomp.
rewrite (eD_let_sample_int R_carrier_meas R_to_carrier_meas Hmu
           (ex_rl_inner pm) one1).
rewrite (icones_hom_pres_int (der (Lty tR' tR')) R_obj _
  (let_sample_path R_carrier_meas R_to_carrier_meas
     (ex_rl_inner pm) one1) mu).
rewrite (linhom_int_eval
  (mcones_hom_pres_path (der (Lty tR' tR')) R_obj
     (fun m : ar_carrier Ar R_obj =>
      Lfun (eD_cbv' (ex_rl_inner pm)) (one1 ⊗p dirac_fmeas m))
     (let_sample_path R_carrier_meas R_to_carrier_meas
        (ex_rl_inner pm) one1)) mu (dirac_fmeas r0)).
rewrite (icone_integral_fmeas_E _ mu mU).
apply: eq_integral => m _.
by rewrite (rl_inner_marginal m r0 mU).
Qed.

End RandomLinearMarginal.

(** ** §5 — [ex_bayes_linear]: the model evidence

    THE Bayesian-linear-regression headline, for a GENERAL observation
    list [l] (seq induction).  The program samples the random affine
    model [f = λx. m·x + b] (EXACTLY Example 2's [ex_random_linear] —
    §4's kit is reused wholesale), scores each observation [o ∈ l] of
    the model's value [f(obs_x o)] by the density [obs_d o], and
    returns [f].  The denotation lives in the FUNCTION-space cone
    [!(U⟦tR⟧ ⊸ U⟦tR⟧)]; the honest "total mass" reading is the
    comonoid counit [coalg_e] (the [e_bang]-style discard — NOT
    [cone_norm], which at [!]-level is provably not the operational
    mass in this model), and the headline computes it as the MODEL
    EVIDENCE
    [[
       ∫∫ ∏_{o ∈ l} (obs_d o)(m·(obs_x o) + b) dµ(m) dµ(b).
    ]]

    Route: the outer [let "f"] diagonal at the setlike [one1] feeds
    the model value [Φ = ⟦ex_random_linear⟧(1)] into the observation
    fold's environment; [Φ] is the double Pettis integral of the
    promoted closures [(ℓ_{m,b})!] (the let-at-sample law twice); the
    [one1 ⊗ −] packaging, the fold and the counit all push inside the
    integrals ([ptensor_icone_integral] / [icones_hom_pres_int]).
    Pointwise at [(m,b)] the fold peels one observation per step
    ([obs_fold_at], seq induction over a tower [obs_env] of growing
    setlike environments): the scored value computes through
    [eD_app_at_setlike] / [rl_body_at] / [score_lift_dirac] to the
    SCALAR [obs_d o (m·x_o + b)], which factors out of the
    environment by bilinearity ([ptensorZr]) and linearity
    ([Lfun_scaleE]) — the shared ["f"] is duplicated by the comonoid
    [coalg_d] at a SETLIKE point of the function-type coalgebra, so
    each duplicate is again the promoted closure ([obs_var_E]).  The
    counit sends the weighted prom-point to the weighted [one1]
    ([coalg_e_setlike]), and the iterated [cone_one]-valued Pettis
    integral reads off as the iterated Lebesgue integral
    ([icone_integral_c1E] via [cone_one_int]). *)

Section BayesLinearEvidence.
Variables (R : realType) (Ar : MeasSubcat R).
(* Reparameterized over the bundled [probObj]. *)
Variable (P : probObj Ar).
Local Notation R_obj := (po_robj P).
Local Notation R_carrier_eq := (po_robj_eq P).
Local Notation R_carrier_meas := (po_robj_meas P).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

(** The prior: a unit-ball measure on the reals. *)
Variable (pm : pmeas Ar R_obj).
Local Notation mu := (pm_meas pm).
Local Notation Hmu := (pm_ball pm).

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
Local Notation tF := (tfun tR' tR').
Local Notation Lty t1 t2 :=
  (linhom_car Ar (coalg_obj (tyD_cbv t1)) (coalg_obj (tyD_cbv t2))).
Local Notation rl_clo' :=
  (rl_clo (R_carrier_eq:=R_carrier_eq) R_carrier_meas R_to_carrier_meas).

Let Hone : cone_norm (one1 : cone_one_car Ar) <= 1.
Proof. by rewrite one1_norm. Qed.

(** *** The promoted closure is a setlike unit-ball point of [⟦tF⟧] *)

Lemma rl_clo_prom_ball (m b : ar_carrier Ar R_obj) :
  cone_norm ((rl_clo' m b)!) <= 1.
Proof. exact: prom_ball (rl_clo_ball R_carrier_meas R_to_carrier_meas m b). Qed.

Lemma rl_clo_prom_setlike (m b : ar_carrier Ar R_obj) :
  Lfun (coalg_str (tyD_cbv tF)) ((rl_clo' m b)!) = ((rl_clo' m b)!)!.
Proof.
rewrite -[tyD_cbv tF]/(bang_cofree (Lty tR' tR')) bang_cofree_str.
exact: (dig_prom _ (rl_clo_ball R_carrier_meas R_to_carrier_meas m b)).
Qed.

(** *** The observation tower: contexts, witnesses, environments

    [obs_ctx n] is the context after [n] observations
    ([("_", tunit)ⁿ ++ [("f", tF)]]); [obs_var n] the [nv_tail]-chain
    locating ["f"]; [obs_env m b n] the environment after the scalar
    score weights have been factored out: [n] copies of [one1] over
    the base environment [one1 ⊗ (ℓ_{m,b})!]. *)

Fixpoint obs_ctx (n : nat) : named_ctx Ar :=
  if n is n'.+1 then ("_"%string, tunit) :: obs_ctx n'
  else [:: ("f"%string, tF)].

Fixpoint obs_var (n : nat) : named_var (obs_ctx n) tF :=
  match n with
  | 0 => nv_head "f"%string tF nil
  | n'.+1 => nv_tail "_"%string tunit (obs_ctx n') (obs_var n')
  end.

Fixpoint obs_env (m b : ar_carrier Ar R_obj) (n : nat) :
    coalg_obj (ctxD_cbv (drop_names (obs_ctx n))) :=
  match n with
  | 0 => (one1 : cone_one_car Ar) ⊗p (rl_clo' m b)!
  | n'.+1 => obs_env m b n' ⊗p (one1 : cone_one_car Ar)
  end.

Lemma obs_env_ball (m b : ar_carrier Ar R_obj) n :
  cone_norm (obs_env m b n) <= 1.
Proof.
elim: n => [ | n IH] /=.
- exact: (ptensor_prom_ball Hone (rl_clo_prom_ball m b)).
- exact: (ptensor_prom_ball IH Hone).
Qed.

Lemma obs_env_setlike (m b : ar_carrier Ar R_obj) n :
  Lfun (coalg_str (ctxD_cbv (drop_names (obs_ctx n)))) (obs_env m b n) =
  (obs_env m b n)!.
Proof.
elim: n => [ | n IH].
- exact: (coalg_str_tensor_setlike (P:=EM_term) (Q:=tyD_cbv tF)
            Hone (rl_clo_prom_ball m b) coalg_str_one1
            (rl_clo_prom_setlike m b)).
- exact: (coalg_str_tensor_setlike
            (P:=ctxD_cbv (drop_names (obs_ctx n))) (Q:=EM_term)
            (obs_env_ball m b n) Hone IH coalg_str_one1).
Qed.

(** The ["f"] lookup returns the promoted closure at EVERY depth: each
    [("_", tunit)] slot holds [one1] (weight already factored out), so
    [em_proj1_mor_unitE] peels it as a [precone_scale 1]. *)
Lemma obs_var_E (m b : ar_carrier Ar R_obj) n :
  Lfun (eD_cbv' (ne_var (obs_var n))) (obs_env m b n) = (rl_clo' m b)!.
Proof.
elim: n => [ | n IH].
- apply: (eq_trans (y := Lfun (em_proj2_mor (R:=R) EM_term (tyD_cbv tF))
      ((one1 : cone_one_car Ar) ⊗p (rl_clo' m b)!))).
    by [].
  exact: (em_proj2_morE (P:=EM_term) Hone coalg_str_one1).
- apply: (eq_trans (y := Lfun (icones_comp
      (ch_mor (var_lookup_cbv (named_var_to_has_var (obs_var n))))
      (em_proj1_mor (R:=R) (ctxD_cbv (drop_names (obs_ctx n)))
                    (EM_term : Coalgebra Ar)))
      (obs_env m b n.+1))).
    by [].
  rewrite (Lfun_comp
    (ch_mor (var_lookup_cbv (named_var_to_has_var (obs_var n))))
    (em_proj1_mor (R:=R) (ctxD_cbv (drop_names (obs_ctx n)))
                  (EM_term : Coalgebra Ar))
    (obs_env m b n.+1)).
  rewrite [obs_env m b n.+1]/=.
  rewrite (em_proj1_mor_unitE
    (P:=ctxD_cbv (drop_names (obs_ctx n))) (obs_env m b n) one1).
  rewrite -[c1_val one1]/(1%:nng) precone_scale_1.
  exact: IH.
Qed.

(** *** The per-observation scalar weights *)

Definition obs_w (m b : ar_carrier Ar R_obj) (o : obs R) : R :=
  obs_d o (cR m * obs_x o + cR b).

Lemma obs_prod_ge0 (m b : ar_carrier Ar R_obj) (l : seq (obs R)) :
  (0 <= \prod_(o <- l) obs_w m b o)%R.
Proof. by apply: prodr_ge0 => o _; exact: obs_ge0. Qed.

(** A [cone_one] element is its [c1]-scalar times [one1]. *)
Lemma cone_one_scaleE (w : {nonneg R}) :
  MkConeOne Ar w = precone_scale w (one1 : cone_one_car Ar).
Proof. by apply: cone_one_eq; apply: val_inj; rewrite /= mulr1. Qed.

(** One scored observation at depth [n] computes to the scalar
    [obs_d o (m·x_o + b)]: the application clause at the setlike
    environment, the model closure at the Dirac argument
    ([rl_body_at]), and the score lift on the resulting Dirac. *)
(** The clean [tProb]-score node for one observation [o]: weigh by
    [po_density P] of the model's prediction pushed through the bundle
    factoring [po_into (obs_d o)] of the Gaussian likelihood. *)
Local Notation obs_score n o :=
  (ne_score_p (po_density P) (po_density_meas P) (po_ge0 P) (po_le1 P)
     (ne_to_prob (po_into P (obs_d o) (obs_meas o) (obs_ge0 o) (obs_le1 o))
        (ne_app (ne_var (obs_var n)) (ne_real (obs_x o))))).

Lemma obs_score_E (m b : ar_carrier Ar R_obj) n (o : obs R) :
  Lfun (eD_cbv' (obs_score n o))
       (obs_env m b n) =
  MkConeOne Ar (NngNum (obs_ge0 o (cR m * obs_x o + cR b))).
Proof.
(* Clean-surface score leaf: the model's prediction at the input, a
   Dirac at [m·x_o + b], pushed through [po_into (obs_d o)], on which
   [score_lift_P] reads off the score scalar; [po_into_E] recovers
   [obs_d o]. *)
rewrite eD_score_p_E.
rewrite -[score_lift_g _ _ _]/(score_lift_P P).
rewrite (Lfun_comp (score_lift_P P)
  (eD_cbv' (ne_to_prob (po_into P (obs_d o) (obs_meas o) (obs_ge0 o)
              (obs_le1 o)) (ne_app (ne_var (obs_var n)) (ne_real (obs_x o)))))
  (obs_env m b n)).
rewrite eD_to_prob_E.
rewrite (Lfun_comp
  (FMeas_fmap (po_into P (obs_d o) (obs_meas o) (obs_ge0 o) (obs_le1 o)))
  (eD_cbv' (ne_app (ne_var (obs_var n)) (ne_real (obs_x o))))
  (obs_env m b n)).
rewrite (eD_app_at_setlike R_carrier_eq R_carrier_meas R_to_carrier_meas
  (F := ne_var (obs_var n)) (X := ne_real (obs_x o))
  (obs_env_ball m b n) (obs_env_setlike m b n)).
rewrite obs_var_E
  (der_prom _ (rl_clo_ball R_carrier_meas R_to_carrier_meas m b)).
rewrite eD_real_E /real_icones
  (const_iconesE (obs_env_ball m b n) (obs_env_setlike m b n)).
rewrite /rl_clo tensor_curryE.
rewrite (rl_body_at R_carrier_meas R_to_carrier_meas m b
           (R_to_carrier R_carrier_eq (obs_x o))).
rewrite R_to_carrierK FMeas_fmap_dirac score_lift_P_dirac.
apply: cone_one_eq; apply: val_inj => /=.
by rewrite po_into_E R_to_carrierK.
Qed.

(** *** The fold accumulates the product of densities

    [⟦obs_fold v l⟧] at the depth-[n] environment is the promoted
    closure weighted by [∏_{o ∈ l} obs_d o (m·x_o + b)].  Seq
    induction; each step factors the score scalar out by [ptensorZr]
    and the linearity of the remaining fold. *)
Lemma obs_fold_at (m b : ar_carrier Ar R_obj) (l : seq (obs R)) :
  forall n,
  Lfun (eD_cbv' (obs_fold (obs_var n) l)) (obs_env m b n) =
  precone_scale (NngNum (obs_prod_ge0 m b l)) ((rl_clo' m b)!).
Proof.
elim: l => [ | o l' IH] n.
- rewrite [LHS]obs_var_E.
  rewrite [NngNum _](_ : _ = 1%:nng) ?precone_scale_1//.
  by apply: val_inj; rewrite /= big_nil.
- have -> : obs_fold (obs_var n) (o :: l') =
      ne_let "_"%string
        (obs_score n o)
        (obs_fold (obs_var n.+1) l').
    by [].
  rewrite eD_let_E.
  rewrite (Lfun_comp (eD_cbv' (obs_fold (obs_var n.+1) l'))
    (em_pair_mor
       (icones_id Ar (coalg_obj (ctxD_cbv (drop_names (obs_ctx n)))))
       (eD_cbv' (obs_score n o)))
    (obs_env m b n)).
  rewrite /em_pair_mor.
  rewrite (Lfun_comp
    (tensor_mor
       (icones_id Ar (coalg_obj (ctxD_cbv (drop_names (obs_ctx n)))))
       (eD_cbv' (obs_score n o)))
    (coalg_d (ctxD_cbv (drop_names (obs_ctx n))))
    (obs_env m b n)).
  rewrite (coalg_d_setlike (P:=ctxD_cbv (drop_names (obs_ctx n)))
    (obs_env_ball m b n) (obs_env_setlike m b n)).
  rewrite (tensor_morE
    (icones_id Ar (coalg_obj (ctxD_cbv (drop_names (obs_ctx n)))))
    (eD_cbv' (obs_score n o))
    (obs_env m b n) (obs_env m b n)).
  rewrite icones_idE (obs_score_E m b n o).
  rewrite (cone_one_scaleE (NngNum (obs_ge0 o (cR m * obs_x o + cR b)))).
  rewrite ptensorZr.
  rewrite (Lfun_scaleE (eD_cbv' (obs_fold (obs_var n.+1) l'))
    (NngNum (obs_ge0 o (cR m * obs_x o + cR b)))
    (obs_env m b n ⊗p (one1 : cone_one_car Ar))).
  rewrite -[obs_env m b n ⊗p (one1 : cone_one_car Ar)]/(obs_env m b n.+1).
  rewrite IH.
  rewrite -precone_scale_A.
  congr (precone_scale _ _).
  by apply: val_inj; rewrite /= big_cons.
Qed.

(** *** Reading off [cone_one]-valued Pettis integrals *)

Local Open Scope ereal_scope.

Lemma icone_integral_c1E (X : ar_obj Ar)
    (beta : ar_carrier Ar X -> cone_one_car Ar)
    (Hbeta : is_measurable_path beta) (nu : fmeas R (ar_carrier Ar X)) :
  ((c1_val (icone_integral beta Hbeta nu))%:num)%R =
  fine (\int[fmeas_mu nu]_(r in [set: ar_carrier Ar X])
          (((c1_val (beta r))%:num)%R)%:E).
Proof.
have <- : cone_one_int Hbeta nu = icone_integral beta Hbeta nu.
  by apply: icone_integral_eqP; exact: cone_one_int_pettis.
by [].
Qed.

(** *** The inner (b)-integral at a fixed slope Dirac *)

Lemma obs_evidence_inner (l : seq (obs R)) (m : ar_carrier Ar R_obj) :
  ((c1_val (Lfun (coalg_e (tyD_cbv tF))
      (Lfun (eD_cbv' (obs_fold (obs_var 0) l))
         ((one1 : cone_one_car Ar) ⊗p
          Lfun (eD_cbv' (ex_rl_inner pm))
            (one1 ⊗p dirac_fmeas m)))))%:num)%R =
  fine (\int[fmeas_mu mu]_(b in [set: ar_carrier Ar R_obj])
     ((\prod_(o <- l) obs_d o (cR m * obs_x o + cR b))%R)%:E).
Proof.
have -> : Lfun (eD_cbv' (ex_rl_inner pm)) (one1 ⊗p dirac_fmeas m)
        = icone_integral
            (fun b => Lfun (eD_cbv' (ne_lam "x" (rl_body R_obj)))
                        ((one1 ⊗p dirac_fmeas m) ⊗p dirac_fmeas b))
            (let_sample_path R_carrier_meas R_to_carrier_meas
               (ne_lam "x" (rl_body R_obj)) (one1 ⊗p dirac_fmeas m)) mu.
  exact: (eD_let_sample_int R_carrier_meas R_to_carrier_meas Hmu
            (ne_lam "x" (rl_body R_obj)) (one1 ⊗p dirac_fmeas m)).
rewrite (ptensor_icone_integral (one1 : cone_one_car Ar)
  (let_sample_path R_carrier_meas R_to_carrier_meas
     (ne_lam "x" (rl_body R_obj)) (one1 ⊗p dirac_fmeas m)) mu).
rewrite (icones_hom_pres_int (eD_cbv' (obs_fold (obs_var 0) l)) R_obj _
  (ptensor_path (one1 : cone_one_car Ar)
     (let_sample_path R_carrier_meas R_to_carrier_meas
        (ne_lam "x" (rl_body R_obj)) (one1 ⊗p dirac_fmeas m))) mu).
rewrite (icones_hom_pres_int (coalg_e (tyD_cbv tF)) R_obj _
  (mcones_hom_pres_path
     (icones_hom_mcones (eD_cbv' (obs_fold (obs_var 0) l))) R_obj _
     (ptensor_path (one1 : cone_one_car Ar)
        (let_sample_path R_carrier_meas R_to_carrier_meas
           (ne_lam "x" (rl_body R_obj)) (one1 ⊗p dirac_fmeas m)))) mu).
rewrite icone_integral_c1E.
congr fine; apply: eq_integral => b _; congr ((_)%:E).
rewrite (rl_lam_at R_carrier_meas R_to_carrier_meas m b).
rewrite -[(one1 : cone_one_car Ar) ⊗p (rl_clo' m b)!]/(obs_env m b 0).
rewrite (obs_fold_at m b l 0).
rewrite (Lfun_scaleE (coalg_e (tyD_cbv tF))
  (NngNum (obs_prod_ge0 m b l)) ((rl_clo' m b)!)).
rewrite (coalg_e_setlike (P:=tyD_cbv tF) (rl_clo_prom_ball m b)
  (rl_clo_prom_setlike m b)).
by rewrite -(cone_one_scaleE (NngNum (obs_prod_ge0 m b l))).
Qed.

(** *** Main result — the model evidence

    The counit ("total mass") of the denotation of [ex_bayes_linear l]
    is the model evidence: the iterated integral of the product of the
    observation densities at the model's values, over the priors on
    slope and intercept.  GENERAL [l]. *)
Theorem ex_bayes_linear_cbv_evidence (l : seq (obs R)) :
  ((c1_val (Lfun (coalg_e (tyD_cbv tF))
      (linhom_fun
         (ex_bayes_linear_cbv P R_to_carrier_meas pm l)
         one1)))%:num)%R =
  fine (\int[fmeas_mu mu]_(m in [set: ar_carrier Ar R_obj])
     (fine (\int[fmeas_mu mu]_(b in [set: ar_carrier Ar R_obj])
        ((\prod_(o <- l) obs_d o (cR m * obs_x o + cR b))%R)%:E))%:E).
Proof.
rewrite /ex_bayes_linear_cbv.
rewrite -[linhom_fun (eD' (ex_bayes_linear pm l)) one1]
        /(Lfun (eD_cbv' (ex_bayes_linear pm l)) one1).
have -> : ex_bayes_linear pm l =
    ne_let "f"%string (ex_random_linear pm) (obs_fold (obs_var 0) l).
  by rewrite ex_bayes_linear_obs_fold.
rewrite eD_let_E.
rewrite (Lfun_comp (eD_cbv' (obs_fold (obs_var 0) l))
  (em_pair_mor
     (icones_id Ar (coalg_obj (ctxD_cbv (drop_names (nil : named_ctx Ar)))))
     (eD_cbv' (ex_random_linear pm)))
  one1).
rewrite /em_pair_mor.
rewrite (Lfun_comp
  (tensor_mor
     (icones_id Ar (coalg_obj (ctxD_cbv (drop_names (nil : named_ctx Ar)))))
     (eD_cbv' (ex_random_linear pm)))
  (coalg_d (ctxD_cbv (drop_names (nil : named_ctx Ar))))
  one1).
rewrite (coalg_d_setlike (P:=ctxD_cbv (drop_names (nil : named_ctx Ar)))
  Hone coalg_str_one1).
rewrite (tensor_morE
  (icones_id Ar (coalg_obj (ctxD_cbv (drop_names (nil : named_ctx Ar)))))
  (eD_cbv' (ex_random_linear pm)) one1 one1).
rewrite icones_idE.
have -> : Lfun (eD_cbv' (ex_random_linear pm)) one1
        = icone_integral
            (fun m0 => Lfun (eD_cbv' (ex_rl_inner pm))
                         (one1 ⊗p dirac_fmeas m0))
            (let_sample_path R_carrier_meas R_to_carrier_meas
               (ex_rl_inner pm) one1) mu.
  exact: (eD_let_sample_int R_carrier_meas R_to_carrier_meas Hmu
            (ex_rl_inner pm) one1).
rewrite (ptensor_icone_integral (one1 : cone_one_car Ar)
  (let_sample_path R_carrier_meas R_to_carrier_meas
     (ex_rl_inner pm) one1) mu).
rewrite (icones_hom_pres_int (eD_cbv' (obs_fold (obs_var 0) l)) R_obj _
  (ptensor_path (one1 : cone_one_car Ar)
     (let_sample_path R_carrier_meas R_to_carrier_meas
        (ex_rl_inner pm) one1)) mu).
rewrite (icones_hom_pres_int (coalg_e (tyD_cbv tF)) R_obj _
  (mcones_hom_pres_path
     (icones_hom_mcones (eD_cbv' (obs_fold (obs_var 0) l))) R_obj _
     (ptensor_path (one1 : cone_one_car Ar)
        (let_sample_path R_carrier_meas R_to_carrier_meas
           (ex_rl_inner pm) one1))) mu).
rewrite icone_integral_c1E.
congr fine; apply: eq_integral => m0 _; congr ((_)%:E).
exact: (obs_evidence_inner l m0).
Qed.

(** Two-observation corollary, product written literally. *)
Theorem ex_bayes_linear_cbv_evidence2 (o1 o2 : obs R) :
  ((c1_val (Lfun (coalg_e (tyD_cbv tF))
      (linhom_fun
         (ex_bayes_linear_cbv P R_to_carrier_meas pm
            [:: o1; o2])
         one1)))%:num)%R =
  fine (\int[fmeas_mu mu]_(m in [set: ar_carrier Ar R_obj])
     (fine (\int[fmeas_mu mu]_(b in [set: ar_carrier Ar R_obj])
        ((obs_d o1 (cR m * obs_x o1 + cR b) *
          obs_d o2 (cR m * obs_x o2 + cR b))%R)%:E))%:E).
Proof.
rewrite (ex_bayes_linear_cbv_evidence [:: o1; o2]).
congr fine; apply: eq_integral => m _; congr ((fine _)%:E).
apply: eq_integral => b _; congr ((_)%:E).
by rewrite !big_cons big_nil mulr1.
Qed.

End BayesLinearEvidence.
