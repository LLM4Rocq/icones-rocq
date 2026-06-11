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

    See also: [theories/programs/ex_reject_headline.v] (the template
    reduction-chain file whose §1 kit is reused), [theories/programs/
    infra/let_sample_law.v] (the let-at-sample integral law),
    [theories/programs/infra/cbv_anchors.v] (the setlike kit).

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
Require Import Icones.homs.tensor_iso.
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
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

(** The prior: a unit-ball measure on the reals. *)
Variable (mu : fmeas R (ar_carrier Ar R_obj)).
Hypothesis Hmu : (cone_norm mu <= 1)%R.

(** The soft evidence: a [[0,1]]-valued density. *)
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

Lemma ex_sp_cont_decomp :
  ex_sp_cont f Hf_meas Hf_ge0 Hf_le1 =
  ne_let "_" (ne_score f Hf_meas Hf_ge0 Hf_le1 sp_var_m) sp_body.
Proof. by []. Qed.

Lemma ex_score_posterior_decomp :
  ex_score_posterior mu Hmu f Hf_meas Hf_ge0 Hf_le1 =
  ne_let "m" (ne_sample mu Hmu) (ex_sp_cont f Hf_meas Hf_ge0 Hf_le1).
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

(** The score value at [δ_r] is the scalar [f r] ([score_lift_dirac]). *)
Lemma sp_score_E (r : ar_carrier Ar R_obj) :
  Lfun (eD_cbv' (ne_score f Hf_meas Hf_ge0 Hf_le1 sp_var_m))
       (one1 ⊗p dirac_fmeas r) =
  MkConeOne Ar (NngNum (Hf_ge0 (cR r))).
Proof.
rewrite eD_score_E.
rewrite (Lfun_comp
  (score_lift (R_carrier_meas:=R_carrier_meas) Hf_meas Hf_ge0 Hf_le1)
  (eD_cbv' sp_var_m) (one1 ⊗p dirac_fmeas r)).
rewrite sp_var_m_E.
rewrite -{1}(carrier_to_RK R_carrier_eq r).
by rewrite (score_lift_dirac Hf_meas Hf_ge0 Hf_le1 (cR r)).
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
  Lfun (eD_cbv' (ex_sp_cont f Hf_meas Hf_ge0 Hf_le1))
       (one1 ⊗p dirac_fmeas r) =
  precone_scale (NngNum (Hf_ge0 (cR r))) (dirac_fmeas r).
Proof.
rewrite ex_sp_cont_decomp eD_let_E.
rewrite (Lfun_comp (eD_cbv' sp_body)
  (em_pair_mor
     (icones_id Ar
        (coalg_obj (ctxD_cbv (drop_names (("m"%string, tR') :: nil)))))
     (eD_cbv' (ne_score f Hf_meas Hf_ge0 Hf_le1 sp_var_m)))
  (one1 ⊗p dirac_fmeas r)).
rewrite /em_pair_mor.
rewrite (Lfun_comp
  (tensor_mor
     (icones_id Ar
        (coalg_obj (ctxD_cbv (drop_names (("m"%string, tR') :: nil)))))
     (eD_cbv' (ne_score f Hf_meas Hf_ge0 Hf_le1 sp_var_m)))
  (coalg_d (ctxD_cbv (drop_names (("m"%string, tR') :: nil))))
  (one1 ⊗p dirac_fmeas r)).
rewrite (coalg_d_setlike (P:=ctxD_cbv (drop_names (("m"%string, tR') :: nil)))
  (one_dirac_ball r) (one_dirac_setlike r)).
rewrite (tensor_morE
  (icones_id Ar (coalg_obj (ctxD_cbv (drop_names (("m"%string, tR') :: nil)))))
  (eD_cbv' (ne_score f Hf_meas Hf_ge0 Hf_le1 sp_var_m))
  (one1 ⊗p dirac_fmeas r) (one1 ⊗p dirac_fmeas r)).
rewrite icones_idE sp_score_E sp_body_at.
by [].
Qed.

(** *** THE HEADLINE — the unnormalised posterior

    On every measurable [U], the denotation of [ex_score_posterior] is
    [∫_U f dµ] — the prior reweighted by the evidence density, NOT
    normalised.  This is the identity the retired CBN interpreter
    could not state (its score collapsed). *)

Local Open Scope ereal_scope.

Theorem ex_score_posterior_cbv_E (U : set (ar_carrier Ar R_obj))
    (mU : measurable U) :
  fmeas_mu
    (linhom_fun (ex_score_posterior_cbv R_carrier_meas R_to_carrier_meas
                   Hmu Hf_meas Hf_ge0 Hf_le1) one1) U =
  \int[fmeas_mu mu]_(r in U) (f (cR r))%:E.
Proof.
rewrite /ex_score_posterior_cbv ex_score_posterior_decomp.
rewrite (eD_let_sample_mu_E R_carrier_meas R_to_carrier_meas Hmu
           (ex_sp_cont f Hf_meas Hf_ge0 Hf_le1) one1 mU).
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
    (linhom_fun (ex_score_posterior_cbv R_carrier_meas R_to_carrier_meas
                   Hmu Hf_meas Hf_ge0 Hf_le1) one1)
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
    (linhom_fun (ex_reject_cbv R_carrier_meas R_to_carrier_meas
                   Hmu Hf_meas Hf_ge0 Hf_le1) one1) U =
  fmeas_mu
    (linhom_fun (ex_score_posterior_cbv R_carrier_meas R_to_carrier_meas
                   Hmu Hf_meas Hf_ge0 Hf_le1) one1) U.
Proof.
rewrite (ex_score_posterior_cbv_E mU).
exact: (ex_reject_master R_carrier_meas R_to_carrier_meas Hmu Hmu1
          Hf_meas Hf_ge0 Hf_le1 mU).
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
Variable (mu : fmeas R (ar_carrier Ar R_obj)).
Hypothesis Hmu : (cone_norm mu <= 1)%R.

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
  ex_random_constant mu Hmu = ne_let "c" (ne_sample mu Hmu)
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

(** *** THE HEADLINE — the marginal recovers the prior

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
                      R_to_carrier_meas Hmu) one1)) x = mu.
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
                      R_to_carrier_meas Hmu) one1)) (dirac_fmeas r0) = mu.
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
                         R_to_carrier_meas Hmu) one1)) x) U =
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
Variable (mu : fmeas R (ar_carrier Ar R_obj)).
Hypothesis Hmu : (cone_norm mu <= 1)%R.

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
  ex_random_linear mu Hmu =
  ne_let "m" (ne_sample mu Hmu) (ex_rl_inner mu Hmu).
Proof. by []. Qed.

Lemma ex_rl_inner_decomp :
  ex_rl_inner mu Hmu =
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
          (Lfun (eD_cbv' (ex_rl_inner mu Hmu)) (one1 ⊗p dirac_fmeas m)))
       (dirac_fmeas r0)) U =
  \int[fmeas_mu mu]_(b in [set: ar_carrier Ar R_obj])
     (fine (fmeas_mu
        (dirac_fmeas (R_to_carrier R_carrier_eq (cR m * cR r0 + cR b)))
        U))%:E.
Proof.
have -> : Lfun (eD_cbv' (ex_rl_inner mu Hmu)) (one1 ⊗p dirac_fmeas m)
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

(** THE HEADLINE — at a Dirac test point [δ_{r0}], the marginal of the
    sampled affine function is the iterated-integral measure
    [∫∫ δ_{m·r0+b}(U) µ(db) µ(dm)]. *)
Theorem ex_random_linear_cbv_marginal (r0 : ar_carrier Ar R_obj)
    (U : set (ar_carrier Ar R_obj)) (mU : measurable U) :
  fmeas_mu
    (linhom_fun
       (Lfun (der (Lty tR' tR'))
          (linhom_fun (ex_random_linear_cbv R_carrier_meas
                         R_to_carrier_meas Hmu) one1))
       (dirac_fmeas r0)) U =
  \int[fmeas_mu mu]_(m in [set: ar_carrier Ar R_obj])
    (fine (\int[fmeas_mu mu]_(b in [set: ar_carrier Ar R_obj])
       (fine (fmeas_mu
          (dirac_fmeas (R_to_carrier R_carrier_eq (cR m * cR r0 + cR b)))
          U))%:E))%:E.
Proof.
rewrite /ex_random_linear_cbv ex_random_linear_decomp.
rewrite (eD_let_sample_int R_carrier_meas R_to_carrier_meas Hmu
           (ex_rl_inner mu Hmu) one1).
rewrite (icones_hom_pres_int (der (Lty tR' tR')) R_obj _
  (let_sample_path R_carrier_meas R_to_carrier_meas
     (ex_rl_inner mu Hmu) one1) mu).
rewrite (linhom_int_eval
  (mcones_hom_pres_path (der (Lty tR' tR')) R_obj
     (fun m : ar_carrier Ar R_obj =>
      Lfun (eD_cbv' (ex_rl_inner mu Hmu)) (one1 ⊗p dirac_fmeas m))
     (let_sample_path R_carrier_meas R_to_carrier_meas
        (ex_rl_inner mu Hmu) one1)) mu (dirac_fmeas r0)).
rewrite (icone_integral_fmeas_E _ mu mU).
apply: eq_integral => m _.
by rewrite (rl_inner_marginal m r0 mU).
Qed.

End RandomLinearMarginal.
