(**md**************************************************************************)
(** * Runtime-parameter distribution anchors — Gaussian/Uniform reductions

    Semantic anchors for the runtime-parameter surface forms
    [Gaussian(e1,e2)] / [Uniform(e1,e2)] ([ppl.v::ne_gaussian] /
    [ne_uniform], interpreted by [ppl_cbv.v] through the two-argument
    kernel lift [distributions.v::kernel_lift2]).

    Deliverables:
    - [em_pair_mor_setlikeE] — the generic pairing law at setlike
      unit-ball context points: [⟨f, g⟩(γ) = f(γ) ⊗ g(γ)] (the inline
      step of [cbv_marginals.v::rl_mul_E], factored once).
    - [eD_real_at] — the literal clause at setlike points:
      [⟦[|r|]⟧(γ) = δ_{toC r}].
    - [eD_gaussian_at] / [eD_uniform_at] — the setlike/Dirac reduction:
      when the two arguments denote point masses at [a], [b], the
      runtime-parameter draw IS the kernel at the cast pair
      ([gaussian_ker_fun (a, b)] / [uniform_ker_fun (a, b)]).
    - [eD_gaussian_dirac_E] / [eD_uniform_dirac_E] — the per-[U]
      measure reading: the transported [normal_prob (cR c) s] (with the
      [s = 0] fibre the Dirac at the mean) / the total uniform integral
      [uniform_int a b] (with the [b ≤ a] fibre the Dirac at [a]).
    - [eD_gaussian_mass] / [eD_uniform_mass] — mass multiplicativity at
      setlike points: the kernels are pointwise probabilities, so the
      result's total mass is the PRODUCT of the argument masses
      ([kernel_lift2_mass] + the [*_kernel_norm1] facts).
    - [pmeas_of_prob_fmeas] — the transport bridge: [examples.v]'s
      [pmeas_of_prob] (the [sample]-surface transport) and
      [distributions.v]'s [fmeas_of_prob] (the kernel-layer transport)
      produce THE SAME [fmeas] (they differ only in re-proved measure
      witnesses; [fmeas_eq] closes the gap).
    - [eD_gaussian_sample_agree] / [eD_uniform_sample_agree] — the
      constant-parameter agreement: at real literals the kernel surface
      IS the old bundled-sample surface,
      [⟦Gaussian([|m|],[|s|])⟧γ = ⟦sample (gaussian m s)⟧γ] for
      [s ≠ 0] (and dually for [Uniform] at [a < b]).
    - The [examples.v::ex_gaussian_walk] hierarchy demo, reduced:
      [ex_gaussian_walk_E] — for measurable [U],
      [[
         ⟦let s = Gaussian(0,1) in Gaussian(s,1)⟧(U)
            = ∫ N(r, 1)(U) dN(0,1)(r)
      ]]
      (the two-level Gaussian hierarchy integral), and
      [ex_gaussian_walk_mass] — the program is a PROBABILITY (total
      mass exactly [1]), by the let-law mass accounting
      ([infra/let_sample_law.v::eD_let_mu_E] + pointwise norm-1 of the
      gaussian kernel). *)

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
From mathcomp.analysis Require Import probability.

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
Require Import Icones.programs.ppl_cbv.
Require Import Icones.programs.examples.
Require Import Icones.programs.infra.cbv_anchors.
Require Import Icones.programs.infra.let_sample_law.

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

(** ** The generic pairing law at setlike points

    [⟨f, g⟩(γ) = f(γ) ⊗ g(γ)] when the context point [γ] is a setlike
    unit-ball point — the comonoid diagonal duplicates [γ]
    ([cbv_anchors.v::coalg_d_setlike]) and the bifunctor computes on
    the pure tensor.  This is the inline step of every two-argument
    clause reduction ([cbv_marginals.v::rl_mul_E] et al.), factored
    once for the kernel anchors below. *)

Section PairSetlikeKit.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.

Lemma em_pair_mor_setlikeE (Z P Q : Coalgebra Ar)
    (f : icones_hom Ar (coalg_obj Z) (coalg_obj P))
    (g : icones_hom Ar (coalg_obj Z) (coalg_obj Q))
    (γ : coalg_obj Z) :
  cone_norm γ <= 1 ->
  Lfun (coalg_str Z) γ = prom γ ->
  Lfun (em_pair_mor f g) γ = (Lfun f γ) ⊗p (Lfun g γ).
Proof.
move=> Hγ Hs.
rewrite /em_pair_mor (Lfun_comp (tensor_mor f g) (coalg_d Z) γ).
by rewrite (coalg_d_setlike Hγ Hs) (tensor_morE f g γ γ).
Qed.

End PairSetlikeKit.

Arguments em_pair_mor_setlikeE {R Ar Z P Q} f g {γ}.

(** ** Kernel-clause reductions at setlike points *)

Section KernelAnchors.
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
Local Notation cR := (carrier_to_R R_carrier_eq).
Local Notation toC := (R_to_carrier R_carrier_eq).
Local Notation tR' := (tR R_obj).
Local Notation Gamo G := (coalg_obj (ctxD_cbv (drop_names G))).

(** *** The literal clause at setlike points: [⟦[|r|]⟧(γ) = δ_{toC r}] *)
Lemma eD_real_at (G : named_ctx Ar) (γ : Gamo G) (r : R) :
  cone_norm γ <= 1 ->
  Lfun (coalg_str (ctxD_cbv (drop_names G))) γ = prom γ ->
  Lfun (eD_cbv' (@ne_real R Ar R_obj G r)) γ =
  dirac_fmeas (toC r).
Proof.
move=> Hγ Hs.
rewrite eD_real_E /real_icones.
exact: (const_iconesE Hγ Hs).
Qed.

(** *** Gaussian: setlike/Dirac reduction

    When the two arguments denote point masses at [a] (the mean) and
    [b] (the deviation), the runtime-parameter draw IS the gaussian
    kernel at the cast pair. *)
Lemma eD_gaussian_at (G : named_ctx Ar)
    (e1 e2 : @named_expr R Ar R_obj G tR')
    (γ : Gamo G) (a b : ar_carrier Ar R_obj) :
  cone_norm γ <= 1 ->
  Lfun (coalg_str (ctxD_cbv (drop_names G))) γ = prom γ ->
  Lfun (eD_cbv' e1) γ = dirac_fmeas a ->
  Lfun (eD_cbv' e2) γ = dirac_fmeas b ->
  Lfun (eD_cbv' (ne_gaussian e1 e2)) γ =
  gaussian_ker_fun R_to_carrier_meas
    (ar_prod_cast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj) (a, b)).
Proof.
move=> Hγ Hs H1 H2.
rewrite eD_gaussian_E
  (Lfun_comp (kernel_lift2 (gaussian_kernel R_carrier_meas R_to_carrier_meas))
     (em_pair_mor (eD_cbv' e1) (eD_cbv' e2)) γ).
rewrite (em_pair_mor_setlikeE (eD_cbv' e1) (eD_cbv' e2) Hγ Hs) H1 H2.
exact: (kernel_lift2_dirac
          (gaussian_kernel R_carrier_meas R_to_carrier_meas) a b).
Qed.

(** The per-[U] measure reading: the transported normal family at the
    parameters — [normal_prob (cR c) s] pushed along [toC], with the
    [s = 0] fibre TOTALISED as the Dirac at the mean (the degenerate
    weak limit; mathcomp-analysis' own [s = 0] convention is a junk
    uniform-[0,1] placeholder, see [distributions.v]). *)
Lemma eD_gaussian_dirac_E (G : named_ctx Ar)
    (e1 e2 : @named_expr R Ar R_obj G tR')
    (γ : Gamo G) (c : ar_carrier Ar R_obj) (s : R)
    (U : set (ar_carrier Ar R_obj)) :
  measurable U ->
  cone_norm γ <= 1 ->
  Lfun (coalg_str (ctxD_cbv (drop_names G))) γ = prom γ ->
  Lfun (eD_cbv' e1) γ = dirac_fmeas c ->
  Lfun (eD_cbv' e2) γ = dirac_fmeas (toC s) ->
  fmeas_mu (Lfun (eD_cbv' (ne_gaussian e1 e2)) γ) U =
  (if s == 0%R then \d_(toC (cR c)) U
   else normal_prob (cR c) s (toC @^-1` U))%E.
Proof.
move=> mU Hγ Hs H1 H2.
rewrite (eD_gaussian_at Hγ Hs H1 H2).
exact: gaussian_ker_cast_E.
Qed.

(** Mass multiplicativity at setlike points: the gaussian kernel is a
    pointwise probability, so the draw's total mass is the PRODUCT of
    the argument masses. *)
Lemma eD_gaussian_mass (G : named_ctx Ar)
    (e1 e2 : @named_expr R Ar R_obj G tR') (γ : Gamo G) :
  cone_norm γ <= 1 ->
  Lfun (coalg_str (ctxD_cbv (drop_names G))) γ = prom γ ->
  fmeas_mu (Lfun (eD_cbv' (ne_gaussian e1 e2)) γ)
    [set: ar_carrier Ar R_obj] =
  (fmeas_mu (Lfun (eD_cbv' e1) γ) [set: ar_carrier Ar R_obj] *
   fmeas_mu (Lfun (eD_cbv' e2) γ) [set: ar_carrier Ar R_obj])%E.
Proof.
move=> Hγ Hs.
rewrite eD_gaussian_E
  (Lfun_comp (kernel_lift2 (gaussian_kernel R_carrier_meas R_to_carrier_meas))
     (em_pair_mor (eD_cbv' e1) (eD_cbv' e2)) γ).
rewrite (em_pair_mor_setlikeE (eD_cbv' e1) (eD_cbv' e2) Hγ Hs).
apply: kernel_lift2_mass => c.
exact: gaussian_kernel_norm1.
Qed.

(** *** Uniform: the same three anchors *)

Lemma eD_uniform_at (G : named_ctx Ar)
    (e1 e2 : @named_expr R Ar R_obj G tR')
    (γ : Gamo G) (a b : ar_carrier Ar R_obj) :
  cone_norm γ <= 1 ->
  Lfun (coalg_str (ctxD_cbv (drop_names G))) γ = prom γ ->
  Lfun (eD_cbv' e1) γ = dirac_fmeas a ->
  Lfun (eD_cbv' e2) γ = dirac_fmeas b ->
  Lfun (eD_cbv' (ne_uniform e1 e2)) γ =
  uniform_ker_fun R_to_carrier_meas
    (ar_prod_cast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj) (a, b)).
Proof.
move=> Hγ Hs H1 H2.
rewrite eD_uniform_E
  (Lfun_comp (kernel_lift2 (uniform_kernel R_carrier_meas R_to_carrier_meas))
     (em_pair_mor (eD_cbv' e1) (eD_cbv' e2)) γ).
rewrite (em_pair_mor_setlikeE (eD_cbv' e1) (eD_cbv' e2) Hγ Hs) H1 H2.
exact: (kernel_lift2_dirac
          (uniform_kernel R_carrier_meas R_to_carrier_meas) a b).
Qed.

(** The per-[U] reading at transported literal endpoints: the total
    uniform integral [uniform_int a b] for [a < b], the Dirac at [a]
    otherwise. *)
Lemma eD_uniform_dirac_E (G : named_ctx Ar)
    (e1 e2 : @named_expr R Ar R_obj G tR')
    (γ : Gamo G) (a b : R)
    (U : set (ar_carrier Ar R_obj)) :
  measurable U ->
  cone_norm γ <= 1 ->
  Lfun (coalg_str (ctxD_cbv (drop_names G))) γ = prom γ ->
  Lfun (eD_cbv' e1) γ = dirac_fmeas (toC a) ->
  Lfun (eD_cbv' e2) γ = dirac_fmeas (toC b) ->
  fmeas_mu (Lfun (eD_cbv' (ne_uniform e1 e2)) γ) U =
  (if (a < b)%R then uniform_int a b (toC @^-1` U)
   else \d_(toC a) U)%E.
Proof.
move=> mU Hγ Hs H1 H2.
rewrite (eD_uniform_at Hγ Hs H1 H2).
exact: uniform_ker_cast_E.
Qed.

Lemma eD_uniform_mass (G : named_ctx Ar)
    (e1 e2 : @named_expr R Ar R_obj G tR') (γ : Gamo G) :
  cone_norm γ <= 1 ->
  Lfun (coalg_str (ctxD_cbv (drop_names G))) γ = prom γ ->
  fmeas_mu (Lfun (eD_cbv' (ne_uniform e1 e2)) γ)
    [set: ar_carrier Ar R_obj] =
  (fmeas_mu (Lfun (eD_cbv' e1) γ) [set: ar_carrier Ar R_obj] *
   fmeas_mu (Lfun (eD_cbv' e2) γ) [set: ar_carrier Ar R_obj])%E.
Proof.
move=> Hγ Hs.
rewrite eD_uniform_E
  (Lfun_comp (kernel_lift2 (uniform_kernel R_carrier_meas R_to_carrier_meas))
     (em_pair_mor (eD_cbv' e1) (eD_cbv' e2)) γ).
rewrite (em_pair_mor_setlikeE (eD_cbv' e1) (eD_cbv' e2) Hγ Hs).
apply: kernel_lift2_mass => c.
exact: uniform_kernel_norm1.
Qed.

(** *** The transport bridge

    [examples.v::pmeas_of_prob] (the [sample]-surface transport) and
    [distributions.v::fmeas_of_prob] (the kernel-layer transport) are
    THE SAME [fmeas]: both are [prob_fmeas] at the same measure
    function, differing only in re-proved [Prop] witnesses —
    [fmeas_eq] closes the gap on every measurable set. *)
Lemma pmeas_of_prob_fmeas
    (P : probability
      (g_sigma_algebraType ((R.-ocitv).-measurable
         : set (set (ocitv_type R)))) R) :
  pm_meas (pmeas_of_prob R_carrier_eq R_to_carrier_meas P) =
  fmeas_of_prob (R_carrier_eq:=R_carrier_eq) R_to_carrier_meas P.
Proof.
apply: fmeas_eq => U mU.
rewrite fmeas_of_probE//.
exact: prob_fmeasE.
Qed.

(** *** Agreement with the constant-parameter surface

    At real literals the kernel surface IS the old bundled-sample
    surface: for [s ≠ 0],
    [⟦Gaussian([|m|],[|s|])⟧γ = ⟦sample (gaussian m s)⟧γ] at every
    setlike unit-ball context point. *)
Lemma eD_gaussian_sample_agree (G : named_ctx Ar)
    (γ : Gamo G) (m s : R) :
  s != 0%R ->
  cone_norm γ <= 1 ->
  Lfun (coalg_str (ctxD_cbv (drop_names G))) γ = prom γ ->
  Lfun (eD_cbv' (ne_gaussian (@ne_real R Ar R_obj G m) (ne_real s))) γ =
  Lfun (eD_cbv' (@ne_sample R Ar R_obj G
          (pm_meas (gaussian R_carrier_eq R_to_carrier_meas m s))
          (pm_ball _))) γ.
Proof.
move=> Hs0 Hγ Hs.
rewrite (eD_gaussian_at Hγ Hs (eD_real_at m Hγ Hs) (eD_real_at s Hγ Hs)).
rewrite eD_sample_E /sample_icones (const_iconesE Hγ Hs).
rewrite gaussian_ker_fun_cast (negbTE Hs0).
by rewrite -[pm_meas _]/(pm_meas (pmeas_of_prob R_carrier_eq
     R_to_carrier_meas [the probability _ _ of normal_prob m s]))
   pmeas_of_prob_fmeas.
Qed.

(** Dually for [Uniform] at [a < b]:
    [⟦Uniform([|a|],[|b|])⟧γ = ⟦sample (uniform ab)⟧γ].  (The two
    sides carry DIFFERENT [a < b] witnesses — the kernel's [pselect]
    vs the user's [ab] — so the comparison goes per-[U] through
    [fmeas_eq]; the values agree because [uniform_prob]'s value only
    depends on the endpoints.) *)
Lemma eD_uniform_sample_agree (G : named_ctx Ar)
    (γ : Gamo G) (a b : R) (ab : (a < b)%R) :
  cone_norm γ <= 1 ->
  Lfun (coalg_str (ctxD_cbv (drop_names G))) γ = prom γ ->
  Lfun (eD_cbv' (ne_uniform (@ne_real R Ar R_obj G a) (ne_real b))) γ =
  Lfun (eD_cbv' (@ne_sample R Ar R_obj G
          (pm_meas (uniform R_carrier_eq R_to_carrier_meas ab))
          (pm_ball _))) γ.
Proof.
move=> Hγ Hs.
rewrite (eD_uniform_at Hγ Hs (eD_real_at a Hγ Hs) (eD_real_at b Hγ Hs)).
rewrite eD_sample_E /sample_icones (const_iconesE Hγ Hs).
rewrite -[pm_meas _]/(pm_meas (pmeas_of_prob R_carrier_eq
     R_to_carrier_meas [the probability _ _ of uniform_prob ab]))
   pmeas_of_prob_fmeas.
apply: fmeas_eq => U mU.
(* [uniform_int_probE]: the kernel's totalised integral IS
   [uniform_prob ab] (definitionally, for any [a < b] witness). *)
by rewrite uniform_ker_cast_E// ab fmeas_of_probE.
Qed.

End KernelAnchors.

Arguments eD_real_at
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G γ} r.
Arguments eD_gaussian_at
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G e1 e2 γ a b}.
Arguments eD_gaussian_dirac_E
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G e1 e2 γ c s U}.
Arguments eD_gaussian_mass
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G} e1 e2 {γ}.
Arguments eD_uniform_at
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G e1 e2 γ a b}.
Arguments eD_uniform_dirac_E
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G e1 e2 γ a b U}.
Arguments eD_uniform_mass
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G} e1 e2 {γ}.
Arguments pmeas_of_prob_fmeas
  {R Ar R_obj R_carrier_eq R_to_carrier_meas} P.
Arguments eD_gaussian_sample_agree
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G γ} m s.
Arguments eD_uniform_sample_agree
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G γ} a b ab.

(** ** The Gaussian hierarchy demo, reduced

    [examples.v::ex_gaussian_walk] = [let s = Gaussian(0,1) in
    Gaussian(s,1)]: the headline per-[U] reduction (the hierarchy
    integral [∫ N(r,1)(U) dN(0,1)(r)]) and the mass-1 corollary. *)

Section GaussianWalkAnchors.
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
Local Notation cR := (carrier_to_R R_carrier_eq).
Local Notation toC := (R_to_carrier R_carrier_eq).
Local Notation tR' := (tR R_obj).

Let Hone : (cone_norm (one1 : cone_one_car Ar) <= 1)%R.
Proof. by rewrite one1_norm. Qed.

(** The prior of the hierarchy: the transported [N(0, 1)]. *)
Definition gw_prior : fmeas R (ar_carrier Ar R_obj) :=
  fmeas_of_prob (R_carrier_eq:=R_carrier_eq) R_to_carrier_meas
    [the probability _ _ of normal_prob 0 1].

Lemma gw_prior_setT : fmeas_mu gw_prior [set: ar_carrier Ar R_obj] = 1.
Proof. exact: fmeas_of_prob_setT. Qed.

(** The first stage at the empty context: [⟦Gaussian([|0|],[|1|])⟧(1)]
    IS the prior. *)
Lemma gw_first_E :
  Lfun (eD_cbv' (ne_gaussian (@ne_real R Ar R_obj nil 0) (ne_real 1)))
    one1 = gw_prior.
Proof.
rewrite (eD_gaussian_at (R_carrier_meas:=R_carrier_meas) (G:=[::])
  Hone coalg_str_one1
  (eD_real_at (R_carrier_meas:=R_carrier_meas) (G:=[::]) 0
     Hone coalg_str_one1)
  (eD_real_at (R_carrier_meas:=R_carrier_meas) (G:=[::]) 1
     Hone coalg_str_one1)).
by rewrite gaussian_ker_fun_cast oner_eq0.
Qed.

(** The one-Dirac environment [1 ⊗ δ_r] of the body's context is a
    setlike unit-ball point. *)
Lemma gw_env_ball (r : ar_carrier Ar R_obj) :
  (cone_norm ((one1 : cone_one_car Ar) ⊗p dirac_fmeas r) <= 1)%R.
Proof.
by rewrite tensor_normME one1_norm mul1r dirac_fmeas_norm_le1.
Qed.

Lemma gw_env_setlike (r : ar_carrier Ar R_obj) :
  Lfun (coalg_str (EM_prod (EM_term : Coalgebra Ar)
                     (FMeas_coalgebra R_obj)))
       ((one1 : cone_one_car Ar) ⊗p dirac_fmeas r) =
  prom ((one1 : cone_one_car Ar) ⊗p dirac_fmeas r).
Proof.
exact: (coalg_str_tensor_setlike (P:=EM_term) (Q:=FMeas_coalgebra R_obj)
          Hone (dirac_fmeas_norm_le1 r) coalg_str_one1
          (Coalg_dirac R_obj r)).
Qed.

(** The bound variable at the one-Dirac environment. *)
Lemma gw_var_E (r : ar_carrier Ar R_obj) :
  Lfun (eD_cbv' (ne_var (nv_head "s"%string tR' nil)))
       ((one1 : cone_one_car Ar) ⊗p dirac_fmeas r) = dirac_fmeas r.
Proof.
rewrite eD_var_E.
exact: (em_proj2_morE (P:=EM_term) (Q:=tyD_cbv tR') Hone coalg_str_one1).
Qed.

(** The second stage under the binder: at [1 ⊗ δ_r], the body is the
    gaussian kernel at [(r, toC 1)]. *)
Lemma gw_body_at (r : ar_carrier Ar R_obj) :
  Lfun (eD_cbv' (ex_gaussian_walk_body : @named_expr R Ar R_obj _ _))
       ((one1 : cone_one_car Ar) ⊗p dirac_fmeas r) =
  gaussian_ker_fun R_to_carrier_meas
    (ar_prod_cast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj) (r, toC 1)).
Proof.
rewrite (eD_gaussian_at (R_carrier_meas:=R_carrier_meas)
  (G:=("s"%string, tR') :: nil)
  (gw_env_ball r) (gw_env_setlike r) (gw_var_E r)
  (eD_real_at (R_carrier_meas:=R_carrier_meas)
     (G:=("s"%string, tR') :: nil) 1
     (gw_env_ball r) (gw_env_setlike r))).
by [].
Qed.

(** **** THE headline: the hierarchy integral.

    For every measurable [U],
    [[
       ⟦let s = Gaussian(0,1) in Gaussian(s,1)⟧(U)
          = ∫ N(r, 1)(toC⁻¹ U) dN(0,1)(r)
    ]]
    — the let-law [eD_let_mu_E] at the prior, with the body reduced by
    the setlike/Dirac anchor. *)
Lemma ex_gaussian_walk_E (U : set (ar_carrier Ar R_obj)) :
  measurable U ->
  fmeas_mu (linhom_fun
              (eD' (ex_gaussian_walk : @named_expr R Ar R_obj nil tR'))
              one1) U =
  \int[fmeas_mu gw_prior]_(r in [set: ar_carrier Ar R_obj])
     (fine (normal_prob (cR r) 1 (toC @^-1` U)))%:E.
Proof.
move=> mU.
rewrite ex_gaussian_walk_decomp.
rewrite (eD_let_mu_E R_carrier_meas R_to_carrier_meas
           (ne_gaussian (@ne_real R Ar R_obj nil 0) (ne_real 1))
           (ex_gaussian_walk_body : @named_expr R Ar R_obj _ _)
           Hone coalg_str_one1 mU).
rewrite gw_first_E.
under eq_integral => r _.
  rewrite gw_body_at (gaussian_ker_cast_E (R_carrier_eq:=R_carrier_eq)
    R_to_carrier_meas r 1 mU) oner_eq0.
  over.
by [].
Qed.

(** **** Mass-1 corollary: the hierarchy is a PROBABILITY.

    Each stage is a pointwise probability kernel, so the total mass is
    [∫ 1 dN(0,1) = 1]. *)
Lemma ex_gaussian_walk_mass :
  fmeas_mu (linhom_fun
              (eD' (ex_gaussian_walk : @named_expr R Ar R_obj nil tR'))
              one1) [set: ar_carrier Ar R_obj] = 1.
Proof.
rewrite (ex_gaussian_walk_E (@measurableT _ (ar_carrier Ar R_obj))).
under eq_integral => r _.
  have -> : fine (normal_prob (cR r) 1
                    (toC @^-1` [set: ar_carrier Ar R_obj])) = 1%R
    by rewrite preimage_setT probability_setT.
  over.
by rewrite integral_cst//= mul1e gw_prior_setT.
Qed.

End GaussianWalkAnchors.

Arguments gw_prior {R Ar R_obj R_carrier_eq} R_to_carrier_meas.
Arguments ex_gaussian_walk_E
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas U}.
Arguments ex_gaussian_walk_mass
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}.
