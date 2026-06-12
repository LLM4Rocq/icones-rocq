(**md**************************************************************************)
(** * The let-at-sample Pettis integral law — CBV `let x = sample µ in K`

    The critical semantic lemma tying the CBV interpretation of
    [ne_let x (ne_sample µ Hµ) K] ([theories/programs/ppl_cbv.v]) to
    the Pettis integral of [K]'s denotation over the Diracs of [µ]:
    [[
       ⟦let x = sample µ in K⟧(γ) = ∫ ⟦K⟧(γ ⊗ δ_r) µ(dr)
    ]]
    POINTWISE AT ARBITRARY [γ] — no unit-ball (and a fortiori no
    setlike) restriction is needed anywhere: every step is driven by
    a genuine [linhom_car]/[icones_hom] field, all of which hold on
    the whole cone.

    Deliverables (one lemma per plan step; the proof of the law is
    literally their composition):
    - [eD_let_sample_collapse] — step 1, the sample-let collapse
      [⟦let x = sample µ in K⟧(γ) = ⟦K⟧(γ ⊗ µ)], via the comonoid
      counit law [emc_counitR] (Melliès Prop 27 / [em_cartesian.v])
      through the general constant-pairing law [em_pair_mor_const_E].
    - step 2, [µ = ∫ δ_r µ(dr)] with the bare [dirac_fmeas]
      integrand: [distributions.v::icone_integral_dirac_fmeas]
      (imported; re-spelling of [bilin.v]'s Thm 6.1 Dirac
      approximation [icone_integral_dirac_path]).
    - [ptensor_icone_integral] — step 3, tensoring with a fixed
      point preserves Pettis integrals,
      [γ ⊗ (∫ β dµ) = ∫ (γ ⊗ β r) µ(dr)], from the
      [linhom_pres_int] field of [τ(γ)] ([tensor.v::tau]).
    - [eD_let_sample_int] — the law (step 4): step 3 + the
      [icones_hom_pres_int] field of [⟦K⟧] pushed under the integral.
    - step 5, the per-U evaluation of an [FMeas]-valued Pettis
      integral [(∫ β dµ)(U) = ∫ (β r)(U) µ(dr)] for ARBITRARY
      measurable [U]: [distributions.v::icone_integral_fmeas_E]
      (imported), generalising [ppl.v::FMeas_fmap_setT_E] from [setT]
      to [U] via the test [fmeas_eU U] ([fmeas.v]).
    - [eD_let_sample_mu_E] — the fused 4+5 corollary at result type
      [tR]: the measure-on-[U] reading of the law, the exact shape
      the rejection-sampling mass recurrence (M4) consumes.
    - [eD_let_collapse_setlike] / [eD_let_int] / [eD_let_mu_E] — the
      GENERAL let-law for an ARBITRARY bound computation [M : tR]:
      [⟦let x = M in K⟧(γ) = ∫ ⟦K⟧(γ ⊗ δ_r) (⟦M⟧γ)(dr)] at setlike
      unit-ball [γ] (the bound SUB-DISTRIBUTION [⟦M⟧γ] replaces the
      constant prior; the collapse step now consumes the comonoid copy
      of [γ], hence the setlike hypothesis).  This is the law the
      rejection-sampling COMBINATOR ([ex_reject_model.v]) consumes,
      with [M = m @ a] the model applied to the input.
    - [let_sample_var_E] — sanity DoD:
      [⟦let x = sample µ in x⟧(1) = µ].

    Supporting infrastructure (private copies; dedup with
    [cbv_anchors] at integration):
    - [icones_compE]/[icones_idE] — pointwise reading of the
      [ICones] category operations.
    - [icone_integral_ext] — integrand extensionality for
      [icone_integral] (the witness is repackaged, so the two
      measurability proofs need not match).
    - [linhom_fun_pres_int] — [linhom_pres_int] re-spelled through
      [linhom_fun] (rewrite-friendly form).
    - [tensor_runit_bwdEp] — [ρ⁻¹(γ) = γ ⊗ 1] for the [smcc.v]
      unitor, with [tensor.v]'s [ptensor] spelling. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals signed constructive_ereal.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import measure dirac_measure.
From mathcomp.analysis Require Import lebesgue_integral_definition.
From mathcomp.analysis Require Import lebesgue_integral_nonneg.
From mathcomp.analysis Require Import lebesgue_integral_monotone_convergence.

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
Require Import Icones.homs.coalgebra.
Require Import Icones.homs.fmeas_lax.
Require Import Icones.homs.em_cat.
Require Import Icones.homs.em_seely_comonoid.
Require Import Icones.homs.em_cartesian.
Require Import Icones.programs.infra.cbv_adjunction.
Require Import Icones.programs.ppl.
Require Import Icones.programs.distributions.
Require Import Icones.programs.infra.em_fix_value.
Require Import Icones.programs.ppl_cbv.
Require Import Icones.programs.infra.cbv_anchors.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Opaque tensor_mor tensor_assoc tensor_lunit tensor_runit tensor_braid
       ptensor tau Seely2.
Opaque dig der prom bang_fmap d_bang e_bang unit_cofree_str Coalg
       tens_cofree_str m_bang.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** Pointwise category operations and Pettis plumbing

    Named pointwise readings of [icones_comp]/[icones_id] (definitional,
    but bare reduction is not always picked up by [rewrite]), the
    integrand-extensionality principle for [icone_integral], the Dirac
    approximation with the bare [dirac_fmeas] integrand, and the
    rewrite-friendly form of [linhom_pres_int].
    (dedup with cbv_anchors at integration) *)

Section IConesPointwise.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.

(** Pointwise composition in [ICones]. *)
Lemma icones_compE (B C D : ICone.type Ar)
    (g : icones_hom Ar C D) (f : icones_hom Ar B C) (x : B) :
  Lfun (icones_comp g f) x = Lfun g (Lfun f x).
Proof. by []. Qed.

(** Pointwise identity in [ICones]: [icones_idE] — the single public
    copy lives in [em_fix_value.v] (imported above). *)

(** Integrand extensionality: two pointwise-equal measurable paths have
    the same Pettis integral (the measurability witnesses need not
    match).  Via the uniqueness clause [icone_integral_eqP] of paper
    Def 4.1 and [eq_integral] on the test side. *)
Lemma icone_integral_ext (B : ICone.type Ar) (X : ar_obj Ar)
    (β1 β2 : ar_carrier Ar X -> B)
    (Hβ1 : is_measurable_path β1) (Hβ2 : is_measurable_path β2)
    (µ : fmeas R (ar_carrier Ar X)) :
  (forall r, β1 r = β2 r) ->
  icone_integral β1 Hβ1 µ = icone_integral β2 Hβ2 µ.
Proof.
move=> eqβ; apply: icone_integral_eqP => m mM s.
rewrite (icone_integralP β1 Hβ1 µ m mM s).
by congr fine; apply: eq_integral => r _; rewrite eqβ.
Qed.

(** Step 2 — Dirac approximation, [µ = ∫ δ_r µ(dr)], with the bare
    [dirac_fmeas] integrand (the form the law's proof composes with):
    [distributions.v::icone_integral_dirac_fmeas] (imported above). *)

(** [linhom_pres_int] re-spelled through [linhom_fun], so that it can
    be used as a plain [rewrite]/[have] after a [ptensorE] step. *)
Lemma linhom_fun_pres_int (C D : ICone.type Ar)
    (h : linhom_car Ar C D) (X : ar_obj Ar)
    (β : ar_carrier Ar X -> C) (Hβ : is_measurable_path β)
    (µ : fmeas R (ar_carrier Ar X)) :
  linhom_fun h (icone_integral β Hβ µ) =
  icone_integral (fun r => linhom_fun h (β r))
    (linhom_pre_pres_path (linhom_pre_of h) X β Hβ) µ.
Proof. exact: linhom_pres_int. Qed.

(** The inverse right unitor on points: [ρ⁻¹(a) = a ⊗ 1], with
    [tensor.v]'s [ptensor] spelling (bridges [tensor_iso.v]'s
    [tensor_runit_bwdE], which lives on that module's own pure
    tensor). *)
Lemma tensor_runit_bwdEp (A : ICone.type Ar) (a : A) :
  Lfun (iso_bwd (tensor_runit A)) a = a ⊗p one1.
Proof. exact: tensor_runit_bwdE. Qed.

(** ** Step 3 — tensoring with a fixed point preserves integrals

    [γ ⊗ −] is the linhom [τ(γ)] ([tensor.v::tau], paper §5.4); its
    [linhom_pres_int] field is exactly integral preservation.  First
    the manufactured measurability witness, then the law. *)

(** [r ↦ γ ⊗ β(r)] is a measurable path. *)
Lemma ptensor_path (B C : ICone.type Ar) (γ : B) (X : ar_obj Ar)
    (β : ar_carrier Ar X -> C) (Hβ : is_measurable_path β) :
  is_measurable_path (fun r => γ ⊗p (β r)).
Proof.
exact: (linhom_pre_pres_path (linhom_pre_of (tau B C γ)) X β Hβ).
Qed.

(** [γ ⊗ (∫ β dµ) = ∫ (γ ⊗ β r) µ(dr)]. *)
Lemma ptensor_icone_integral (B C : ICone.type Ar) (γ : B)
    (X : ar_obj Ar) (β : ar_carrier Ar X -> C)
    (Hβ : is_measurable_path β) (µ : fmeas R (ar_carrier Ar X)) :
  γ ⊗p (icone_integral β Hβ µ) =
  icone_integral (fun r => γ ⊗p (β r)) (ptensor_path γ Hβ) µ.
Proof.
rewrite ptensorE (linhom_fun_pres_int (tau B C γ) Hβ µ).
by apply: icone_integral_ext => r; rewrite ptensorE.
Qed.

End IConesPointwise.

Arguments icones_compE {R Ar B C D} g f x.
Arguments icone_integral_ext {R Ar B X β1 β2} Hβ1 Hβ2 µ.
Arguments ptensor_path {R Ar B C} γ {X β} Hβ.
Arguments ptensor_icone_integral {R Ar B C} γ {X β} Hβ µ.

(** ** Step 5 — per-U evaluation of an [FMeas]-valued Pettis integral

    [(∫ β dµ)(U) = ∫ (β r)(U) µ(dr)] for ARBITRARY measurable [U] —
    the generalisation of [ppl.v::FMeas_fmap_setT_E] from [setT] to
    [U], read off the Pettis equation against the test [fmeas_eU U]
    ([fmeas.v], paper §3.2.1): [distributions.v::icone_integral_fmeas_E]
    (imported above).  This is the lemma the headline mass recurrence
    consumes. *)

(** ** Step 1 — the sample-let collapse, then the law

    The [ne_let]-at-[ne_sample] clause of [eD_cbv] collapses pointwise
    to a pure tensor: the inner [em_pair_mor id (const µ)] erases the
    context copy through the comonoid counit law [emc_counitR]
    (Melliès Prop 27, [em_cartesian.v]) and re-materialises [µ]
    through [lin_pt] at the unit.  Stated for an arbitrary constant
    first ([em_pair_mor_const_E]); no restriction on [γ]. *)

Section LetSampleLaw.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Local Notation eD_cbv' :=
  (@eD_cbv R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation eD' :=
  (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.

(** *** Pairing the identity with a constant is the pure tensor

    [⟨id, const c⟩(γ) = γ ⊗ c] on any coalgebra context [Z]: factor
    the bifunctor through [tensor_mor_comp], erase the counit leg by
    [emc_counitR], land on [γ ⊗ 1] via [ρ⁻¹], and scale [c] in by
    [lin_pt_unit]. *)
Lemma em_pair_mor_const_E (Z Q : Coalgebra Ar)
    (c : coalg_obj Q) (Hc : (cone_norm c <= 1)%R) (γ : coalg_obj Z) :
  Lfun (em_pair_mor (icones_id Ar (coalg_obj Z)) (const_icones Z c Hc)) γ
  = γ ⊗p c.
Proof.
rewrite /em_pair_mor /const_icones icones_compE.
rewrite -[X in tensor_mor X _](icones_compIl (icones_id Ar (coalg_obj Z))).
rewrite tensor_mor_comp icones_compE.
have Hcr := emc_counitR (EMComon_all Z).
have Hpt : Lfun (iso_fwd (tensor_runit (coalg_obj Z)))
             (Lfun (tensor_mor (icones_id Ar (coalg_obj Z)) (coalg_e Z))
                (Lfun (coalg_d Z) γ)) = γ
  := congr1
       (fun h : icones_hom Ar (coalg_obj Z) (coalg_obj Z) => Lfun h γ)
       Hcr.
have HX : Lfun (tensor_mor (icones_id Ar (coalg_obj Z)) (coalg_e Z))
            (Lfun (coalg_d Z) γ) = γ ⊗p one1.
  rewrite -[LHS](iso_can (tensor_runit (coalg_obj Z))) Hpt.
  exact: tensor_runit_bwdEp.
rewrite HX tensor_morE icones_idE.
by rewrite linhom_iconesE lin_pt_unit.
Qed.

Variables (G : named_ctx Ar) (x : string) (t2 : ppl_type Ar).
Variable (mu : fmeas R (ar_carrier Ar R_obj)).
Hypothesis Hmu : (cone_norm mu <= 1)%R.
Variable K : @named_expr R Ar R_obj ((x, tR R_obj) :: G) t2.

Local Notation Gam := (ctxD_cbv (drop_names G)).
Local Notation Gamo := (coalg_obj (ctxD_cbv (drop_names G))).

(** [⟨id, ⟦sample µ⟧⟩(γ) = γ ⊗ µ] — [em_pair_mor_const_E] at the
    [sample_icones] constant. *)
Lemma em_pair_mor_sample_E (γ : Gamo) :
  Lfun (em_pair_mor (icones_id Ar Gamo)
          (sample_icones (R:=R) (ctxD_cbv (drop_names G)) mu Hmu)) γ =
  γ ⊗p mu.
Proof. exact: em_pair_mor_const_E. Qed.

(** *** Step 1, the collapse:
    [⟦let x = sample µ in K⟧(γ) = ⟦K⟧(γ ⊗ µ)].

    Arbitrary [γ] — no unit-ball hypothesis. *)
Lemma eD_let_sample_collapse (γ : Gamo) :
  Lfun (eD_cbv' (ne_let x (ne_sample mu Hmu) K)) γ =
  Lfun (eD_cbv' K) (γ ⊗p mu).
Proof.
rewrite eD_let_E eD_sample_E icones_compE.
by rewrite em_pair_mor_sample_E.
Qed.

(** *** The law's integrand is a measurable path

    [r ↦ ⟦K⟧(γ ⊗ δ_r)]: the Dirac path, tensored with the fixed [γ]
    (a [linhom_pre_pres_path] instance of [τ(γ)]), pushed through the
    path-preservation field of the [icones_hom] [⟦K⟧]. *)
Lemma let_sample_path (γ : Gamo) :
  is_measurable_path (fun r : ar_carrier Ar R_obj =>
     Lfun (eD_cbv' K) (γ ⊗p dirac_fmeas r)).
Proof.
apply: (mcones_hom_pres_path (icones_hom_mcones (eD_cbv' K)) R_obj
  (fun r => γ ⊗p dirac_fmeas r)).
exact: (ptensor_path (C := FMeas R_obj) γ (dirac_fmeas_is_path R_obj)).
Qed.

(** *** The law — step 4

    [[
       ⟦let x = sample µ in K⟧(γ) = ∫ ⟦K⟧(γ ⊗ δ_r) µ(dr)
    ]]
    pointwise at ARBITRARY [γ] (the let may sit under binders: in the
    headline [γ = (1 ⊗ b_n) ⊗ a₀]).  Composition of steps 1–3 with
    the [icones_hom_pres_int] field of [⟦K⟧] (paper Def 4.10). *)
Lemma eD_let_sample_int (γ : Gamo) :
  linhom_fun (eD' (ne_let x (ne_sample mu Hmu) K)) γ =
  icone_integral (fun r => Lfun (eD_cbv' K) (γ ⊗p dirac_fmeas r))
    (let_sample_path γ) mu.
Proof.
rewrite -[linhom_fun (eD' _) γ]
        /(Lfun (eD_cbv' (ne_let x (ne_sample mu Hmu) K)) γ).
rewrite eD_let_sample_collapse.
rewrite -[X in Lfun _ (γ ⊗p X)](icone_integral_dirac_fmeas mu).
rewrite ptensor_icone_integral.
rewrite (icones_hom_pres_int (eD_cbv' K) R_obj _ _ mu).
by apply: icone_integral_ext.
Qed.

End LetSampleLaw.

(** ** The fused 4+5 corollary at result type [tR]

    When the let body has type [tR R_obj] the denotation is a measure;
    evaluating the law on a measurable [U] through
    [icone_integral_fmeas_E] gives the mass form
    [[
       ⟦let x = sample µ in K⟧(γ)(U) = ∫ ⟦K⟧(γ ⊗ δ_r)(U) µ(dr)
    ]]
    — the exact shape of the headline mass recurrence (plan M4). *)

Section LetSampleLawFMeas.
Local Open Scope ereal_scope.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Local Notation eD_cbv' :=
  (@eD_cbv R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation eD' :=
  (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.

Variables (G : named_ctx Ar) (x : string).
Variable (mu : fmeas R (ar_carrier Ar R_obj)).
Hypothesis Hmu : (cone_norm mu <= 1)%R.
Variable K : @named_expr R Ar R_obj ((x, tR R_obj) :: G) (tR R_obj).

Local Notation Gamo := (coalg_obj (ctxD_cbv (drop_names G))).

Lemma eD_let_sample_mu_E (γ : Gamo) (U : set (ar_carrier Ar R_obj))
    (mU : measurable U) :
  fmeas_mu (linhom_fun (eD' (ne_let x (ne_sample mu Hmu) K)) γ) U =
  \int[fmeas_mu mu]_(r in [set: ar_carrier Ar R_obj])
     (fine (fmeas_mu (Lfun (eD_cbv' K) (γ ⊗p dirac_fmeas r)) U))%:E.
Proof.
rewrite (eD_let_sample_int R_carrier_meas R_to_carrier_meas Hmu K γ).
exact: (icone_integral_fmeas_E
          (let_sample_path R_carrier_meas R_to_carrier_meas K γ) mu mU).
Qed.

End LetSampleLawFMeas.

(** ** The GENERAL let-law — arbitrary bound computation

    The let-at-sample law above is the special case [M = sample µ] of
    the general CBV sequencing law
    [[
       ⟦let x = M in K⟧(γ) = ∫ ⟦K⟧(γ ⊗ δ_r) (⟦M⟧γ)(dr)
    ]]
    for an ARBITRARY bound computation [M : tR] — the bound
    SUB-DISTRIBUTION [⟦M⟧γ] replaces the constant prior [µ].  Unlike
    the sample case, the step-1 collapse here genuinely consumes the
    comonoid copy of the context ([em_pair_mor id ⟦M⟧] feeds [γ] to
    BOTH legs), so the context point must be a SETLIKE unit-ball point
    — which is harmless: in every consumer the let sits under binders
    whose environments are setlike by construction.  Steps 2-4 are
    reused verbatim ([icone_integral_dirac_fmeas],
    [ptensor_icone_integral], [icones_hom_pres_int], and the
    [let_sample_path] measurability witness, none of which mention the
    bound measure). *)

Section LetLawGeneral.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Local Notation eD_cbv' :=
  (@eD_cbv R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation eD' :=
  (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.

Variables (G : named_ctx Ar) (x : string) (t2 : ppl_type Ar).
Variable M : @named_expr R Ar R_obj G (tR R_obj).
Variable K : @named_expr R Ar R_obj ((x, tR R_obj) :: G) t2.

Local Notation Gamo := (coalg_obj (ctxD_cbv (drop_names G))).

(** *** Step 1, generalised: the setlike collapse
    [⟦let x = M in K⟧(γ) = ⟦K⟧(γ ⊗ ⟦M⟧γ)]. *)
Lemma eD_let_collapse_setlike (γ : Gamo) :
  cone_norm γ <= 1 ->
  Lfun (coalg_str (ctxD_cbv (drop_names G))) γ = prom γ ->
  Lfun (eD_cbv' (ne_let x M K)) γ =
  Lfun (eD_cbv' K) (γ ⊗p Lfun (eD_cbv' M) γ).
Proof.
move=> Hg Hs.
rewrite eD_let_E icones_compE.
rewrite /em_pair_mor (icones_compE
  (tensor_mor (icones_id Ar Gamo) (eD_cbv' M))
  (coalg_d (ctxD_cbv (drop_names G))) γ).
by rewrite (coalg_d_setlike Hg Hs) tensor_morE icones_idE.
Qed.

(** *** THE GENERAL LAW

    [[
       ⟦let x = M in K⟧(γ) = ∫ ⟦K⟧(γ ⊗ δ_r) (⟦M⟧γ)(dr)
    ]]
    at setlike unit-ball [γ]: the collapse followed by steps 2-3 and
    the [icones_hom_pres_int] field of [⟦K⟧], with the Pettis integral
    now taken against the bound sub-distribution [⟦M⟧γ]. *)
Lemma eD_let_int (γ : Gamo) :
  cone_norm γ <= 1 ->
  Lfun (coalg_str (ctxD_cbv (drop_names G))) γ = prom γ ->
  linhom_fun (eD' (ne_let x M K)) γ =
  icone_integral (fun r => Lfun (eD_cbv' K) (γ ⊗p dirac_fmeas r))
    (let_sample_path R_carrier_meas R_to_carrier_meas K γ)
    (Lfun (eD_cbv' M) γ).
Proof.
move=> Hg Hs.
rewrite -[linhom_fun (eD' _) γ]
        /(Lfun (eD_cbv' (ne_let x M K)) γ).
rewrite (eD_let_collapse_setlike Hg Hs).
rewrite -[X in Lfun _ (γ ⊗p X)]
        (icone_integral_dirac_fmeas (Lfun (eD_cbv' M) γ)).
rewrite ptensor_icone_integral.
rewrite (icones_hom_pres_int (eD_cbv' K) R_obj _ _ (Lfun (eD_cbv' M) γ)).
by apply: icone_integral_ext.
Qed.

End LetLawGeneral.

(** ** The fused per-[U] form of the general law at result type [tR]

    [[
       ⟦let x = M in K⟧(γ)(U) = ∫ ⟦K⟧(γ ⊗ δ_r)(U) (⟦M⟧γ)(dr)
    ]]
    — the exact shape the rejection-sampling COMBINATOR mass
    recurrence ([ex_reject_model.v]) consumes, with [M = m @ a]. *)

Section LetLawGeneralFMeas.
Local Open Scope ereal_scope.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Local Notation eD_cbv' :=
  (@eD_cbv R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation eD' :=
  (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.

Variables (G : named_ctx Ar) (x : string).
Variable M : @named_expr R Ar R_obj G (tR R_obj).
Variable K : @named_expr R Ar R_obj ((x, tR R_obj) :: G) (tR R_obj).

Local Notation Gamo := (coalg_obj (ctxD_cbv (drop_names G))).

Lemma eD_let_mu_E (γ : Gamo)
    (Hg : (cone_norm γ <= 1)%R)
    (Hs : Lfun (coalg_str (ctxD_cbv (drop_names G))) γ = prom γ)
    (U : set (ar_carrier Ar R_obj)) (mU : measurable U) :
  fmeas_mu (linhom_fun (eD' (ne_let x M K)) γ) U =
  \int[fmeas_mu (Lfun (eD_cbv' M) γ)]_(r in [set: ar_carrier Ar R_obj])
     (fine (fmeas_mu (Lfun (eD_cbv' K) (γ ⊗p dirac_fmeas r)) U))%:E.
Proof.
rewrite (eD_let_int R_carrier_meas R_to_carrier_meas M K Hg Hs).
exact: (icone_integral_fmeas_E
          (let_sample_path R_carrier_meas R_to_carrier_meas K γ)
          (Lfun (eD_cbv' M) γ) mU).
Qed.

End LetLawGeneralFMeas.

(** ** Sanity DoD — [⟦let x = sample µ in x⟧(1) = µ]

    The collapse followed by the second projection at the terminal
    context: [⟦x⟧ = π₂], [ε_1 = id] ([coalg_e_term]), and the left
    unitor at [1 ⊗ µ] scales by [c1_val 1 = 1]. *)

Section LetSampleVar.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Local Notation eD_cbv' :=
  (@eD_cbv R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation eD' :=
  (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

Variable (mu : fmeas R (ar_carrier Ar R_obj)).
Hypothesis Hmu : (cone_norm mu <= 1)%R.

(** The surface program [let "x" := sample µ in x] (closed, type
    [tR]). *)
Definition ex_let_sample_var : @named_expr R Ar R_obj nil (tR R_obj) :=
  [ let "x" := Sample (mu , Hmu) in # "x" ].

Lemma let_sample_var_E : linhom_fun (eD' ex_let_sample_var) one1 = mu.
Proof.
rewrite -[linhom_fun (eD' ex_let_sample_var) one1]
        /(Lfun (eD_cbv' ex_let_sample_var) one1).
rewrite /ex_let_sample_var eD_let_sample_collapse.
(* [⟦#"x"⟧ = π₂ = λ ∘ (ε_1 ⊗ id)] — definitional on the
   witness. *)
apply: (eq_trans (y := Lfun (em_proj2_mor (R:=R) EM_term
                              (FMeas_coalgebra R_obj))
                            (ptensor one1 mu))).
  by [].
rewrite icones_compE tensor_morE coalg_e_term !icones_idE.
by rewrite tensor_lunitEp precone_scale_1.
Qed.

End LetSampleVar.
