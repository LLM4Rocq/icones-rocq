(**md**************************************************************************)
(** * Distributions in general — measurable probability-kernel families

    The general distribution/kernel layer for the PPL: a [pkernel X Y]
    bundles a family of sub-probability measures [pk_ker : X → FMeas Y]
    with the two facts that make it usable as a semantic primitive —
    measurability of the family ([pk_meas], the mathcomp-analysis
    kernel condition [x ↦ k(x)(U)] measurable for every measurable
    [U], phrased in [fine] form, which is exactly the [e_U]-test form
    the [FMeas] cone consumes) and the unit-ball bound ([pk_ball],
    mirroring [ppl.v::pmeas]).

    Deliverables:
    - [pkernel X Y] — the record; [pkernel_is_path] shows the family
      IS a measurable path of [FMeas Y] (paper Def 3.7), so the whole
      [int_to_linhom] machinery of Thm 6.1 applies verbatim.
    - The bridge to the paper-side [Skern] category (§6.1):
      [pkernel_to_Skern_hom] / [Skern_hom_to_pkernel], mutually
      inverse by [pkernel_to_Skern_homK] / [Skern_hom_to_pkernelK] —
      a [pkernel] and a [Skern_hom] are the same data in two
      packagings.  This is the only [Require] edge from
      [theories/programs/] into [Icones.kernels].
    - [kernel_lift k : icones_hom (FMeas X) (FMeas Y)] — the semantic
      lift [ν ↦ ∫ k(x) ν(dx)] (Pettis integral), DEFINED as the paper's
      Thm 6.5 embedding functor [Klin]
      ([kernels/kernel_embedding.v::Skern_to_ICones_mor]) at the
      bridged kernel, so the [Skern] category laws
      ([Skern_compIl]/[Skern_compIr]/[Skern_compA]) and [Klin]'s
      functoriality carry over to the PPL for free.
      Laws: [kernel_lift_E] (per-[U] evaluation
      [(kernel_lift k ν)(U) = ∫ k(x)(U) ν(dx)]), [kernel_lift_mass]
      (mass preservation for pointwise-mass-1 kernels) and
      [kernel_lift_dirac] ([kernel_lift k δ_x = k(x)], a corollary of
      [Skern_compIr]).
    - Instances: [dirac_kernel] ([x ↦ δ_x], with
      [dirac_kernel_lift_id : kernel_lift dirac_kernel ν = ν]),
      [gaussian_kernel]
      ([(m,s) ↦ N(m,s)], totalised at [s = 0] as [δ_m]; for [s ≠ 0]
      mathcomp-analysis' [normal_prob m s] is already total with
      deviation [|s|]) and [uniform_kernel] ([(a,b) ↦ U(a,b)],
      totalised at [b ≤ a] as [δ_a]).
    - The mathcomp-analysis side of the gaussian/uniform family
      measurability: [measurable_funV] (inversion is measurable),
      [measurable_normal_peak] / [measurable_normal_pdf_pair] /
      [measurable_normal_prob_pair] and
      [measurable_uniform_pdf_pair] / [measurable_uniform_int_pair] —
      joint measurability in the PARAMETERS via Fubini–Tonelli
      ([measurable_fun_fubini_tonelli_F] against Lebesgue measure).

    Two-argument kernels through the lax map: [kernel_lift2 k] packages
    [kernel_lift k ∘ fmeas_lax X Y] — the tensored argument pair becomes
    a joint measure on [ar_prod X Y], fed to the kernel.  Laws:
    [kernel_lift2_dirac] (point masses reduce to the kernel at the
    cast pair) and [kernel_lift2_mass] (a pointwise-mass-1 kernel sends
    [µ ⊗ ν] to a measure of total mass [µ(setT)·ν(setT)]).  This is the
    semantic engine of the surface forms [Gaussian(e1,e2)] /
    [Uniform(e1,e2)] ([ppl.v::ne_gaussian]/[ne_uniform], interpreted in
    [ppl_cbv.v] by the exact [add_lift]/[mul_lift] clause shape).

    Supporting infrastructure: THE canonical copies of
    [icone_integral_dirac_fmeas] and [icone_integral_fmeas_E]
    (re-exported to [theories/programs/infra/let_sample_law.v], which
    imports this file). *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.classical Require Import set_interval.
From mathcomp.reals Require Import reals constructive_ereal.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun realfun exp.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import measure dirac_measure numfun.
From mathcomp.analysis Require Import lebesgue_measure.
From mathcomp.analysis Require Import lebesgue_integral_definition.
From mathcomp.analysis Require Import lebesgue_integral_nonneg.
From mathcomp.analysis Require Import lebesgue_integral_monotone_convergence.
From mathcomp.analysis Require Import lebesgue_integrable.
From mathcomp.analysis Require Import lebesgue_integral_fubini.
From mathcomp.analysis Require Import probability.

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
Require Import Icones.homs.seely.
Require Import Icones.homs.coalgebra.
Require Import Icones.homs.fmeas_lax.
Require Import Icones.kernels.skern.
Require Import Icones.kernels.kernel_embedding.
Require Import Icones.programs.ppl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Opaque tensor_mor tensor_assoc tensor_lunit tensor_runit tensor_braid
       ptensor tau Seely2.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** [pkernel] — measurable families of sub-probability measures

    A probability kernel from [X] to [Y] (both in [Ar]): a function
    [pk_ker : ar_carrier X → fmeas (ar_carrier Y)] together with
    - [pk_meas]: for every measurable [U ⊆ Y], the evaluation
      [x ↦ k(x)(U)] is measurable (the mathcomp-analysis kernel
      condition, [fine]-valued since [fmeas] values are finite — this
      is verbatim the [e_U]-test section the [FMeas] cone tests
      compute);
    - [pk_ball]: each [k(x)] is a sub-probability ([‖k(x)‖ ≤ 1],
      mirroring [pmeas]). *)

Section PKernelDef.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (X Y : ar_obj Ar).

Record pkernel : Type := MkPkernel {
  pk_ker : ar_carrier Ar X -> fmeas R (ar_carrier Ar Y);
  pk_meas : forall U : set (ar_carrier Ar Y),
    measurable U ->
    measurable_fun [set: ar_carrier Ar X]
      (fun x => fine (fmeas_mu (pk_ker x) U));
  pk_ball : forall x, (cone_norm (pk_ker x) <= 1)%R
}.

(** The mathcomp-analysis kernel condition in its native [ereal] form
    ([kernel.v]'s [measurable_fun (k ^~ U)]), recovered from the
    [fine] field through [fineK] on finite values. *)
Lemma pk_meas_ereal (k : pkernel) (U : set (ar_carrier Ar Y)) :
  measurable U ->
  measurable_fun [set: ar_carrier Ar X]
    (fun x => fmeas_mu (pk_ker k x) U).
Proof.
move=> mU.
apply: (eq_measurable_fun
  (fun x => (fine (fmeas_mu (pk_ker k x) U))%:E)).
  by move=> x _; rewrite fineK//; exact: fmeas_fin.
apply/measurable_EFinP.
exact: pk_meas mU.
Qed.

(** A [pkernel] is a measurable path of [FMeas Y] (paper Def 3.7):
    boundedness is [pk_ball]; the tests of [FMeas Y] are the [e_U]
    family, whose path sections are exactly [pk_meas]. *)
Lemma pkernel_is_path (k : pkernel) :
  is_measurable_path (Ar := Ar) (C := fmeas R (ar_carrier Ar Y))
    (X := X) (pk_ker k).
Proof.
split.
  by exists 1%R => x; exact: pk_ball.
move=> Z m [U [mU ->]].
apply: (measurableT_comp
  (f := fun x => fine (fmeas_mu (pk_ker k x) U))).
- exact: pk_meas mU.
- exact: measurable_snd.
Qed.

Definition kernel_path (k : pkernel) :
    path_car Ar X (fmeas R (ar_carrier Ar Y)) :=
  MkPath (pkernel_is_path k).

(** Path-norm bound: the values are sub-probabilities, so the sup is
    [≤ 1]. *)
Lemma kernel_path_norm_le1 (k : pkernel) :
  (path_norm (kernel_path k) <= 1)%R.
Proof.
apply: ge_sup; first exact: path_normset_nonempty.
by move=> _ [x ->] /=; exact: pk_ball.
Qed.

(** Norm bound for [int_to_linhom (kernel_path k)]. *)
Lemma kernel_int_norm_le1 (k : pkernel) :
  (cone_norm (int_to_linhom (kernel_path k)) <= 1)%R.
Proof.
apply: le_trans (int_to_linhom_norm_le (kernel_path k)) _.
exact: kernel_path_norm_le1.
Qed.

(** ** Bridge to the paper-side [Skern] category (paper §6.1)

    [pkernel X Y] and [Skern_hom Ar X Y] ([theories/kernels/skern.v])
    are the SAME data in two packagings: a [pkernel] is a function
    [X → FMeas Y] with the [e_U]-test measurability field [pk_meas]
    and the pointwise unit-ball field [pk_ball]; a [Skern_hom] is a
    [path_car X (FMeas Y)] with [path_norm ≤ 1].  [pkernel_is_path]
    above is one direction; the converse reads the two [pkernel]
    fields back off a path — [pk_meas] is
    [measurable_test_path_section] at the test [fmeas_eU], [pk_ball]
    is [path_norm_ub] composed with [skern_norm_le1].

    The bridge is what lets the PPL inherit the [Skern] category laws
    ([Skern_compIl] / [Skern_compIr] / [Skern_compA]) and the Thm 6.5
    embedding functor [Klin] ([kernel_embedding.v]) instead of
    re-deriving them. *)

(** A [pkernel] IS a substochastic kernel: package [kernel_path] with
    its norm bound. *)
Definition pkernel_to_Skern_hom (k : pkernel) : Skern_hom Ar X Y :=
  MkSkernHom (kernel_path k) (kernel_path_norm_le1 k).

(** Converse, [pk_meas] field: the [e_U] sections of a measurable path
    are measurable — this is [measurable_test_path_section] at the
    test [fmeas_eU], whose value is by [fmeas_eUE] exactly
    [fine (µ U)]. *)
Lemma Skern_hom_pk_meas (κ : Skern_hom Ar X Y)
    (U : set (ar_carrier Ar Y)) (mU : measurable U) :
  measurable_fun [set: ar_carrier Ar X]
    (fun x => fine (fmeas_mu (skern_path κ x) U)).
Proof.
have HM : mcone_M (ar_zero Ar) (fmeas_eU (ar_zero Ar) mU)
  by exists U, mU.
exact: (measurable_test_path_section HM (path_is_path (skern_path κ))
          (ar_zero_pt Ar)).
Qed.

(** Converse, [pk_ball] field: each value of a unit-ball path is a
    sub-probability. *)
Lemma Skern_hom_pk_ball (κ : Skern_hom Ar X Y) (x : ar_carrier Ar X) :
  (cone_norm (skern_path κ x) <= 1)%R.
Proof.
apply: le_trans (path_norm_ub (skern_path κ) x) _.
exact: skern_norm_le1.
Qed.

(** Converse direction of the bridge. *)
Definition Skern_hom_to_pkernel (κ : Skern_hom Ar X Y) : pkernel :=
  @MkPkernel (path_fun (skern_path κ))
    (fun U mU => Skern_hom_pk_meas κ mU) (Skern_hom_pk_ball κ).

(** Extensionality for [pkernel] (both fields are [Prop]s). *)
Lemma pkernel_eq (k1 k2 : pkernel) : pk_ker k1 = pk_ker k2 -> k1 = k2.
Proof.
case: k1 => f1 m1 b1; case: k2 => f2 m2 b2 /= Hf.
move: m1 b1; rewrite Hf => m1 b1.
by congr MkPkernel; exact: Prop_irrelevance.
Qed.

(** The two packagings are inverse: [pkernel ≃ Skern_hom]. *)
Lemma Skern_hom_to_pkernelK (κ : Skern_hom Ar X Y) :
  pkernel_to_Skern_hom (Skern_hom_to_pkernel κ) = κ.
Proof. by apply: Skern_hom_eq; exact: path_eq. Qed.

Lemma pkernel_to_Skern_homK (k : pkernel) :
  Skern_hom_to_pkernel (pkernel_to_Skern_hom k) = k.
Proof. exact: pkernel_eq. Qed.

(** ** [kernel_lift] — the lift [ν ↦ ∫ k(x) ν(dx)] as an [icones_hom]

    The Pettis integral of the kernel path against the input measure.
    This is nothing but the paper's Thm 6.5 embedding functor [Klin]
    ([kernel_embedding.v::Skern_to_ICones_mor]) evaluated at the
    bridged kernel, so the PPL gets [Klin]'s functoriality
    ([Skern_to_ICones_mor_id] / [Skern_to_ICones_mor_comp]) and full
    faithfulness for free. *)
Definition kernel_lift (k : pkernel) :
    icones_hom Ar (FMeas X) (FMeas Y) :=
  Skern_to_ICones_mor (pkernel_to_Skern_hom k).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

(** The lift IS the Pettis integral of the kernel (definitional
    reading of the [Klin]/[int_to_linhom] packaging —
    [Skern_to_ICones_mor_E] at the bridged kernel). *)
Lemma kernel_liftE (k : pkernel) (nu : fmeas R (ar_carrier Ar X)) :
  Lfun (kernel_lift k) nu =
  icone_integral (pk_ker k) (pkernel_is_path k) nu.
Proof. exact: (Skern_to_ICones_mor_E (pkernel_to_Skern_hom k) nu). Qed.

(** **** Load-bearing Dirac identity: [kernel_lift k δ_x = k(x)].
    Corollary of the [Skern] right-unit law [Skern_compIr], read off
    at the point [x]. *)
Lemma kernel_lift_dirac (k : pkernel) (x : ar_carrier Ar X) :
  Lfun (kernel_lift k) (dirac_fmeas x) = pk_ker k x.
Proof.
have := Skern_compIr (pkernel_to_Skern_hom k).
by move/(congr1 (fun κ => skern_path κ x)).
Qed.

End PKernelDef.

Arguments pkernel {R Ar} X Y.
Arguments MkPkernel {R Ar X Y} pk_ker pk_meas pk_ball.
Arguments pk_ker {R Ar X Y} p x.
Arguments pk_meas {R Ar X Y} p {U} mU.
Arguments pk_ball {R Ar X Y} p x.
Arguments pk_meas_ereal {R Ar X Y} k {U} mU.
Arguments pkernel_is_path {R Ar X Y} k.
Arguments kernel_path {R Ar X Y} k.
Arguments kernel_path_norm_le1 {R Ar X Y} k.
Arguments kernel_int_norm_le1 {R Ar X Y} k.
Arguments pkernel_to_Skern_hom {R Ar X Y} k.
Arguments Skern_hom_pk_meas {R Ar X Y} κ {U} mU.
Arguments Skern_hom_pk_ball {R Ar X Y} κ x.
Arguments Skern_hom_to_pkernel {R Ar X Y} κ.
Arguments pkernel_eq {R Ar X Y} k1 k2.
Arguments Skern_hom_to_pkernelK {R Ar X Y} κ.
Arguments pkernel_to_Skern_homK {R Ar X Y} k.
Arguments kernel_lift {R Ar X Y} k.
Arguments kernel_liftE {R Ar X Y} k nu.
Arguments kernel_lift_dirac {R Ar X Y} k x.

(** ** Per-[U] evaluation and the mass identity

    [(kernel_lift k ν)(U) = ∫ k(x)(U) ν(dx)] for any measurable [U],
    via the per-[U] evaluation of [FMeas]-valued Pettis integrals
    ([icone_integral_fmeas_E] — the canonical copy; consumed by
    [theories/programs/infra/let_sample_law.v]). *)

Section KernelLiftEval.
Local Open Scope ereal_scope.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

(** Per-[U] evaluation of an [FMeas]-valued Pettis integral —
    [(∫ β dµ)(U) = ∫ (β r)(U) µ(dr)].  The CANONICAL copy (the
    [let_sample_law.v] law layer imports it from here). *)
Lemma icone_integral_fmeas_E (X Y : ar_obj Ar)
    (β : ar_carrier Ar X -> FMeas Y)
    (Hβ : is_measurable_path β) (µ : fmeas R (ar_carrier Ar X))
    (U : set (ar_carrier Ar Y)) (mU : measurable U) :
  fmeas_mu (icone_integral β Hβ µ) U =
  \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X])
     (fine (fmeas_mu (β r) U))%:E.
Proof.
have HP := icone_integralP β Hβ µ (fmeas_eU (ar_zero Ar) mU)
             (ex_intro _ U (ex_intro _ mU erefl)) (ar_zero_pt Ar).
have HLfin : fmeas_mu (icone_integral β Hβ µ) U \is a fin_num
  by exact: fmeas_fin.
have mInt : measurable_fun [set: ar_carrier Ar X]
              (fun r => (fine (fmeas_mu (β r) U))%:E).
  apply/measurable_EFinP.
  exact: (measurable_test_path_section
            (m := fmeas_eU (ar_zero Ar) mU)
            (ex_intro _ U (ex_intro _ mU erefl)) Hβ (ar_zero_pt Ar)).
have [[M HM] _] := Hβ.
have HRfin : \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X])
                (fine (fmeas_mu (β r) U))%:E \is a fin_num.
  rewrite ge0_fin_numE; last first.
    by apply: integral_ge0 => r _; rewrite lee_fin fine_ge0// measure_ge0.
  apply: (le_lt_trans
    (y := \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X]) M%:E)).
    apply: ge0_le_integral => //.
    move=> r _; rewrite lee_fin.
    apply: le_trans (HM r).
    exact: (test_norm_le (fmeas_eU (ar_zero Ar) mU) (ar_zero_pt Ar) (β r)).
  rewrite (_ : (fun _ => M%:E) = cst M%:E)// integral_cst//.
  have HfT : fmeas_mu µ [set: ar_carrier Ar X] \is a fin_num
    by exact: fmeas_setT_fin.
  by rewrite ltey_eq fin_numM.
by rewrite -(fineK HLfin) -(fineK HRfin); congr (_%:E); exact: HP.
Qed.

(** **** THE evaluation law:
    [(kernel_lift k ν)(U) = ∫ k(x)(U) ν(dx)]. *)
Lemma kernel_lift_E (X Y : ar_obj Ar) (k : pkernel X Y)
    (nu : fmeas R (ar_carrier Ar X))
    (U : set (ar_carrier Ar Y)) (mU : measurable U) :
  fmeas_mu (Lfun (kernel_lift k) nu) U =
  \int[fmeas_mu nu]_(x in [set: ar_carrier Ar X])
     (fine (fmeas_mu (pk_ker k x) U))%:E.
Proof.
rewrite kernel_liftE.
exact: (icone_integral_fmeas_E (pkernel_is_path k) nu mU).
Qed.

(** **** Mass identity: a pointwise-mass-1 (probability) kernel
    preserves total mass. *)
Lemma kernel_lift_mass (X Y : ar_obj Ar) (k : pkernel X Y)
    (nu : fmeas R (ar_carrier Ar X)) :
  (forall x, cone_norm (pk_ker k x) = 1%R) ->
  fmeas_mu (Lfun (kernel_lift k) nu) [set: ar_carrier Ar Y] =
  fmeas_mu nu [set: ar_carrier Ar X].
Proof.
move=> Hk1.
rewrite (kernel_lift_E k nu (@measurableT _ (ar_carrier Ar Y))).
under eq_integral => x _.
  have -> : fine (fmeas_mu (pk_ker k x) [set: ar_carrier Ar Y]) = 1%R
    by exact: Hk1 x.
  over.
rewrite integral_cst//= mul1e//.
Qed.

End KernelLiftEval.

Arguments icone_integral_fmeas_E {R Ar X Y β} Hβ µ {U} mU.
Arguments kernel_lift_E {R Ar X Y} k nu {U} mU.
Arguments kernel_lift_mass {R Ar X Y} k nu Hk1.

(** ** [kernel_lift2] — two-argument kernels through the lax map

    A kernel on a PRODUCT object consumed from a TENSORED pair of
    measures: [kernel_lift2 k = kernel_lift k ∘ fmeas_lax X Y], the
    same "tensored pair → joint measure" route as [ppl.v::add_lift] /
    [mul_lift] (with the kernel lift in place of the [FMeas_fmap] of a
    measurable function).  This is the semantic engine of the
    runtime-parameter surface forms [Gaussian(e1,e2)] /
    [Uniform(e1,e2)]. *)

Section KernelLift2.
Local Open Scope ereal_scope.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (X Y Z : ar_obj Ar).
Variable (k : pkernel (ar_prod Ar X Y) Z).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

Definition kernel_lift2 :
    icones_hom Ar (tensor Ar (FMeas X) (FMeas Y)) (FMeas Z) :=
  icones_comp (kernel_lift k) (fmeas_lax X Y).

(** **** Load-bearing Dirac identity: on point masses the two-argument
    lift is the kernel at the cast pair. *)
Lemma kernel_lift2_dirac (x : ar_carrier Ar X) (y : ar_carrier Ar Y) :
  Lfun kernel_lift2
    (ptensor (B := FMeas X) (C := FMeas Y)
       (dirac_fmeas x) (dirac_fmeas y)) =
  pk_ker k (ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y) (x, y)).
Proof.
rewrite /kernel_lift2.
rewrite -[LHS]/(Lfun (kernel_lift k)
  (Lfun (fmeas_lax X Y)
     (ptensor (B := FMeas X) (C := FMeas Y)
        (dirac_fmeas x) (dirac_fmeas y)))).
rewrite (fmeas_lax_dirac x y).
exact: kernel_lift_dirac.
Qed.

(** **** Mass identity: for a pointwise-mass-1 kernel, the mass of the
    two-argument lift on a pure tensor is the PRODUCT of the argument
    masses ([kernel_lift_mass] + [fmeas_lax_pre_setT]). *)
Lemma kernel_lift2_mass
    (µ : fmeas R (ar_carrier Ar X)) (ν : fmeas R (ar_carrier Ar Y)) :
  (forall c, cone_norm (pk_ker k c) = 1%R) ->
  fmeas_mu (Lfun kernel_lift2 (ptensor (B := FMeas X) (C := FMeas Y) µ ν))
    [set: ar_carrier Ar Z] =
  fmeas_mu µ [set: ar_carrier Ar X] * fmeas_mu ν [set: ar_carrier Ar Y].
Proof.
move=> Hk1.
rewrite /kernel_lift2.
rewrite -[Lfun _ _]/(Lfun (kernel_lift k)
  (Lfun (fmeas_lax X Y) (ptensor (B := FMeas X) (C := FMeas Y) µ ν))).
rewrite (fmeas_lax_E µ ν) (kernel_lift_mass k _ Hk1).
exact: fmeas_lax_pre_setT.
Qed.

End KernelLift2.

Arguments kernel_lift2 {R Ar X Y Z} k.
Arguments kernel_lift2_dirac {R Ar X Y Z} k x y.
Arguments kernel_lift2_mass {R Ar X Y Z} k µ ν Hk1.

(** ** [dirac_kernel] — the identity kernel [x ↦ δ_x] *)

Section DiracKernel.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (X : ar_obj Ar).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

Lemma dirac_kernel_meas (U : set (ar_carrier Ar X)) :
  measurable U ->
  measurable_fun [set: ar_carrier Ar X]
    (fun x => fine (fmeas_mu (dirac_fmeas x) U)).
Proof.
move=> mU.
apply: (eq_measurable_fun (fun x => fine (\d_x U : \bar R))).
  by move=> x _; rewrite dirac_fmeas_E.
apply: (measurableT_comp (f := fine)).
- exact: (fine_measurable measurableT).
- exact: measurable_fun_dirac.
Qed.

Lemma dirac_kernel_ball (x : ar_carrier Ar X) :
  (cone_norm (dirac_fmeas x : fmeas R (ar_carrier Ar X)) <= 1)%R.
Proof. by rewrite dirac_fmeas_norm. Qed.

Definition dirac_kernel : pkernel X X :=
  MkPkernel (@dirac_fmeas R Ar X) dirac_kernel_meas dirac_kernel_ball.

(** Pointwise the Dirac kernel is a probability (norm exactly 1). *)
Lemma dirac_kernel_norm1 (x : ar_carrier Ar X) :
  cone_norm (pk_ker dirac_kernel x) = 1%R.
Proof. exact: dirac_fmeas_norm. Qed.

(** [µ = ∫ δ_r µ(dr)] with the bare [dirac_fmeas] integrand —
    the CANONICAL copy (consumed by
    [theories/programs/infra/let_sample_law.v]). *)
Lemma icone_integral_dirac_fmeas (µ : fmeas R (ar_carrier Ar X)) :
  icone_integral (@dirac_fmeas R Ar X) (dirac_fmeas_is_path X) µ = µ.
Proof.
have HP := icone_integralP (path_fun (dirac_path Ar X))
             (path_is_path (dirac_path Ar X)) µ.
rewrite icone_integral_dirac_path in HP.
by apply/esym/icone_integral_eqP.
Qed.

(** The Dirac kernel bridges to the [Skern] identity — paper §6.1,
    line 3042 ([Skern_id] is the Dirac path). *)
Lemma pkernel_to_Skern_hom_dirac :
  pkernel_to_Skern_hom dirac_kernel = Skern_id Ar X.
Proof. by apply: Skern_hom_eq; exact: path_eq. Qed.

(** [kernel_lift dirac_kernel] is the identity — now a corollary of
    [Klin(δ_X) = id_{FMeas X}] (Thm 6.5 functoriality,
    [kernel_embedding.v::Skern_to_ICones_mor_id]) transported along
    the bridge, rather than a local re-derivation. *)
Lemma dirac_kernel_lift_id (nu : fmeas R (ar_carrier Ar X)) :
  Lfun (kernel_lift dirac_kernel) nu = nu.
Proof.
by rewrite /kernel_lift pkernel_to_Skern_hom_dirac Skern_to_ICones_mor_id.
Qed.

End DiracKernel.

Arguments dirac_kernel {R Ar} X.
Arguments dirac_kernel_norm1 {R Ar X} x.
Arguments pkernel_to_Skern_hom_dirac {R Ar} X.
Arguments dirac_kernel_lift_id {R Ar X} nu.

(** ** Family measurability for the named distributions

    The pure mathcomp-analysis layer: joint measurability of the
    normal/uniform families IN THEIR PARAMETERS.  The route is
    Fubini–Tonelli ([measurable_fun_fubini_tonelli_F] against Lebesgue
    measure): for a fixed measurable [V],
    [(m,s) ↦ ∫_V normal_pdf m s x dx] is the partial integral of the
    jointly measurable density [((m,s),x) ↦ 1_V(x) · pdf(m,s,x)].
    Joint measurability of the densities needs measurability of
    inversion ([measurable_funV], proved by splitting at the sign and
    reading [x^-1] off [powR]). *)

Section RealFamilyMeasurability.
Variable R : realType.
Local Notation mu := (@lebesgue_measure R).

(** Inversion is measurable: on [{x > 0}] it is [x ↦ x `^ (-1)], on
    [{x < 0}] it is [x ↦ -((-x) `^ (-1))], and [0^-1 = 0]. *)
Lemma measurable_funV : measurable_fun [set: R] (@GRing.inv R).
Proof.
have mpos : measurable [set y : R | 0 < y]%R.
  have := @measurable_itv R
    (interval.Interval (interval.BRight (0 : R)) (interval.BInfty R false)).
  set S := [set` _] => mS.
  have -> : [set y : R | 0 < y]%R = S.
    by apply/seteqP; split => y; rewrite /S/= interval.in_itv/= andbT.
  exact: mS.
have mneg : measurable [set y : R | y < 0]%R.
  have := @measurable_itv R
    (interval.Interval (interval.BInfty R true) (interval.BLeft (0 : R))).
  by set S := [set` _] => mS; exact: mS.
apply: (eq_measurable_fun (fun x : R =>
  (\1_([set y : R | 0 < y]%R) x * (x `^ (-1)) -
   \1_([set y : R | y < 0]%R) x * ((- x) `^ (-1)))%R)).
  move=> x _ /=; rewrite !indicE.
  have [x0|x0|e] := ltgtP 0%R x.
  - rewrite mem_set//= memNset/=; last by apply/negP; rewrite -leNgt ltW.
    by rewrite mul1r mul0r subr0 powR_inv1// ltW.
  - rewrite memNset/=; last by apply/negP; rewrite -leNgt ltW.
    rewrite mem_set//= mul0r mul1r sub0r powR_inv1;
      last by rewrite oppr_ge0 ltW.
    by rewrite invrN opprK.
  - rewrite -e memNset/=; last by rewrite ltxx.
    rewrite memNset/=; last by rewrite ltxx.
    by rewrite !mul0r subr0 invr0.
apply: measurable_funB.
- apply: measurable_funM; first exact: measurable_indic.
  exact: measurable_powR.
- apply: measurable_funM; first exact: measurable_indic.
  apply: (measurableT_comp (f := fun y : R => y `^ (-1))).
  + exact: measurable_powR.
  + exact: oppr_measurable.
Qed.

(** The normal-density peak [s ↦ (√(s²·2π))^-1] is measurable. *)
Lemma measurable_normal_peak : measurable_fun [set: R] (@normal_peak R).
Proof.
rewrite /normal_peak.
apply: (measurableT_comp (f := @GRing.inv R)); first exact: measurable_funV.
apply: (measurableT_comp (f := @Num.sqrt R)).
  exact: (continuous_measurable_fun (@sqrt_continuous R)).
apply: (measurableT_comp (f := fun y : R => y *+ 2)).
  exact: natmul_measurable.
by apply: measurable_funM => //; exact: exprn_measurable.
Qed.

(** Joint measurability of the normal pdf in (parameters, point). *)
Lemma measurable_normal_pdf_pair :
  measurable_fun [set: ((R * R)%type * R)%type]
    (fun q => normal_pdf q.1.1 q.1.2 q.2).
Proof.
rewrite /normal_pdf.
apply: measurable_fun_if => //.
- apply: measurable_fun_eqr => //.
  exact: (measurableT_comp measurable_snd measurable_fst).
- apply: (measurable_funS measurableT (subsetT _)).
  by apply: measurableT_comp;
    [exact: measurable_indic | exact: measurable_snd].
- apply: (measurable_funS measurableT (subsetT _)).
  apply: measurable_funM.
    apply: (measurableT_comp (f := @normal_peak R)).
    + exact: measurable_normal_peak.
    + exact: (measurableT_comp measurable_snd measurable_fst).
  rewrite /normal_fun.
  apply: measurableT_comp; first exact: measurable_expR.
  apply: measurable_funM.
    apply: measurable_funN.
    apply: measurable_funX.
    apply: measurable_funB; first exact: measurable_snd.
    exact: (measurableT_comp measurable_fst measurable_fst).
  apply: (measurableT_comp (f := @GRing.inv R)).
    exact: measurable_funV.
  apply: (measurableT_comp (f := fun y : R => y *+ 2)).
    exact: natmul_measurable.
  apply: (measurableT_comp (f := fun y : R => y ^+ 2)).
    exact: exprn_measurable.
  exact: (measurableT_comp measurable_snd measurable_fst).
Qed.

(** Family measurability: for fixed measurable [V],
    [(m,s) ↦ normal_prob m s V] is measurable. *)
Lemma measurable_normal_prob_pair (V : set R) (mV : measurable V) :
  measurable_fun [set: (R * R)%type] (fun p => normal_prob p.1 p.2 V).
Proof.
pose f : ((R * R)%type * R)%type -> \bar R :=
  fun q => (\1_V q.2 * normal_pdf q.1.1 q.1.2 q.2)%:E.
have mf : measurable_fun [set: ((R * R)%type * R)%type] f.
  apply/measurable_EFinP; apply: measurable_funM.
    exact: (measurableT_comp (measurable_indic mV) measurable_snd).
  exact: measurable_normal_pdf_pair.
have f0 q : (0 <= f q)%E.
  by rewrite lee_fin mulr_ge0 ?normal_pdf_ge0.
have H := measurable_fun_fubini_tonelli_F
  (m2 := [the {sigma_finite_measure set _ -> \bar R} of mu]) f mf f0.
apply: eq_measurable_fun H => p _.
rewrite /fubini_F/= /f /normal_prob [RHS]integral_mkcond.
apply: eq_integral => y _.
rewrite patchE indicE; case: ifPn => yV; first by rewrite mul1r.
by rewrite mul0r.
Qed.

(** The TOTAL uniform pdf [if a ≤ x ≤ b then (b−a)^-1 else 0] is
    nonnegative for ALL [a b] (when the test holds, [a ≤ b]). *)
Lemma uniform_pdf_ge0_total (a b x : R) : (0 <= uniform_pdf a b x)%R.
Proof.
rewrite /uniform_pdf; case: ifPn => // /andP[ax xb].
by rewrite invr_ge0 subr_ge0 (le_trans ax xb).
Qed.

(** Joint measurability of the uniform pdf in (parameters, point). *)
Lemma measurable_uniform_pdf_pair :
  measurable_fun [set: ((R * R)%type * R)%type]
    (fun q => uniform_pdf q.1.1 q.1.2 q.2).
Proof.
rewrite /uniform_pdf.
apply: measurable_fun_if => //.
- apply: measurable_and; apply: measurable_fun_ler.
  + exact: (measurableT_comp measurable_fst measurable_fst).
  + exact: measurable_snd.
  + exact: measurable_snd.
  + exact: (measurableT_comp measurable_snd measurable_fst).
- apply: (measurable_funS measurableT (subsetT _)).
  apply: (measurableT_comp (f := @GRing.inv R)).
    exact: measurable_funV.
  apply: measurable_funB.
  + exact: (measurableT_comp measurable_snd measurable_fst).
  + exact: (measurableT_comp measurable_fst measurable_fst).
Qed.

(** The total uniform measure formula — agrees with [uniform_prob]
    whenever [a < b] ([uniform_int_probE]). *)
Definition uniform_int (a b : R) (V : set R) : \bar R :=
  (\int[mu]_(x in V) (uniform_pdf a b x)%:E)%E.

Lemma uniform_int_probE (a b : R) (ab : (a < b)%R) (V : set R) :
  uniform_int a b V = uniform_prob ab V.
Proof. by []. Qed.

(** Family measurability: for fixed measurable [V],
    [(a,b) ↦ ∫_V uniform_pdf a b dx] is measurable. *)
Lemma measurable_uniform_int_pair (V : set R) (mV : measurable V) :
  measurable_fun [set: (R * R)%type] (fun p => uniform_int p.1 p.2 V).
Proof.
pose f : ((R * R)%type * R)%type -> \bar R :=
  fun q => (\1_V q.2 * uniform_pdf q.1.1 q.1.2 q.2)%:E.
have mf : measurable_fun [set: ((R * R)%type * R)%type] f.
  apply/measurable_EFinP; apply: measurable_funM.
    exact: (measurableT_comp (measurable_indic mV) measurable_snd).
  exact: measurable_uniform_pdf_pair.
have f0 q : (0 <= f q)%E.
  by rewrite lee_fin mulr_ge0 ?uniform_pdf_ge0_total.
have H := measurable_fun_fubini_tonelli_F
  (m2 := [the {sigma_finite_measure set _ -> \bar R} of mu]) f mf f0.
apply: eq_measurable_fun H => p _.
rewrite /fubini_F/= /f /uniform_int [RHS]integral_mkcond.
apply: eq_integral => y _.
rewrite patchE indicE; case: ifPn => yV; first by rewrite mul1r.
by rewrite mul0r.
Qed.

End RealFamilyMeasurability.

(** ** [gaussian_kernel] / [uniform_kernel] — named-distribution kernels

    Kernels on the product object [R_obj × R_obj]: the parameters are
    a pair of reals read off the carrier through [ar_prod_uncast] and
    the carrier cast.
    - [gaussian_kernel]: [(m,s) ↦ normal_prob m s] transported along
      [toC] (the [ppl.v::ProbTransport] pushforward), TOTALISED at
      [s = 0] as [δ_m] (the degenerate weak limit; mathcomp-analysis'
      own [s = 0] convention is a placeholder uniform-[0,1] pdf, while
      [s ≠ 0] — including [s < 0] — is the genuine normal with
      deviation [|s|], which we keep).
    - [uniform_kernel]: [(a,b) ↦ uniform_prob ab] for [a < b],
      totalised as [δ_a] otherwise.
    Family measurability is [measurable_normal_prob_pair] /
    [measurable_uniform_int_pair] composed with the parameter
    projections. *)

Section NamedKernels.
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

Local Notation cR := (carrier_to_R R_carrier_eq).
Local Notation toC := (R_to_carrier R_carrier_eq).
Local Notation P2 := (ar_prod Ar R_obj R_obj).
Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

(** *** Transporting a mathcomp-analysis probability on [R] into an
    [fmeas], through [ppl.v::prob_fmeas].

    This is the SINGLE transport: the kernel layer uses the raw
    [fmeas_of_prob], and [pmeas_of_prob] below is its [pmeas]
    packaging, from which [examples.v]'s [sample]-surface transport
    is a one-line derivation. *)
Section ProbFmeas.
Variable P : probability
  (g_sigma_algebraType ((R.-ocitv).-measurable : set (set (ocitv_type R))))
  R.

Let nuP : set R -> \bar R := fun U => P U.

Local Lemma nuP0 : nuP set0 = 0.
Proof. exact: measure0. Qed.

Local Lemma nuP_ge0 (U : set R) : 0 <= nuP U.
Proof. exact: measure_ge0. Qed.

Local Lemma nuP_sigma : semi_sigma_additive nuP.
Proof.
move=> F mF tF mUF.
have HH := @measure_semi_sigma_additive _ _ R P F.
by apply: HH.
Qed.

Local Lemma nuP_le1 (U : set (ar_carrier Ar R_obj)) :
  measurable U -> nuP (toC @^-1` U) <= 1.
Proof.
move=> mU.
apply: probability_le1.
exact: (prob_push_pre_meas R_to_carrier_meas mU).
Qed.

Definition fmeas_of_prob : fmeas R (ar_carrier Ar R_obj) :=
  prob_fmeas R_carrier_eq R_to_carrier_meas nuP nuP0 nuP_ge0 nuP_sigma nuP_le1.

Lemma fmeas_of_probE (U : set (ar_carrier Ar R_obj)) :
  measurable U -> fmeas_mu fmeas_of_prob U = P (toC @^-1` U).
Proof. exact: prob_fmeasE. Qed.

Lemma fmeas_of_prob_ball : (cone_norm fmeas_of_prob <= 1)%R.
Proof. exact: prob_fmeas_ball. Qed.

(** Probabilities transport to norm-EXACTLY-1 measures. *)
Lemma fmeas_of_prob_norm1 : cone_norm fmeas_of_prob = 1%R.
Proof.
rewrite -[cone_norm _]/(fmeas_norm fmeas_of_prob) /fmeas_norm.
by rewrite fmeas_of_probE ?measurableT// preimage_setT probability_setT.
Qed.

(** The ereal form of the norm-1 fact: total mass exactly [1]. *)
Lemma fmeas_of_prob_setT :
  fmeas_mu fmeas_of_prob [set: ar_carrier Ar R_obj] = 1.
Proof.
by rewrite fmeas_of_probE ?measurableT// preimage_setT probability_setT.
Qed.

(** The [pmeas] packaging of the same transport, through
    [ppl.v::prob_pmeas]: [pm_meas] of it IS [fmeas_of_prob], by
    conversion.  This is the bundled sub-probability consumed by the
    [sample] surface; [examples.v::pmeas_of_prob] is a one-line
    derivation of it. *)
Definition pmeas_of_prob : pmeas Ar R_obj :=
  prob_pmeas R_carrier_eq R_to_carrier_meas nuP nuP0 nuP_ge0 nuP_sigma nuP_le1.

End ProbFmeas.

(** *** Parameter projections from the product-object carrier *)

Definition par1 (c : ar_carrier Ar P2) : R :=
  cR (ar_prod_uncast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj) c).1.
Definition par2 (c : ar_carrier Ar P2) : R :=
  cR (ar_prod_uncast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj) c).2.

Lemma par1_meas : measurable_fun [set: ar_carrier Ar P2] par1.
Proof.
apply: (measurableT_comp (f := cR)); first exact: R_carrier_meas.
exact: (measurableT_comp measurable_fst (ar_prod_uncast_meas Ar R_obj R_obj)).
Qed.

Lemma par2_meas : measurable_fun [set: ar_carrier Ar P2] par2.
Proof.
apply: (measurableT_comp (f := cR)); first exact: R_carrier_meas.
exact: (measurableT_comp measurable_snd (ar_prod_uncast_meas Ar R_obj R_obj)).
Qed.

Lemma par_pair_meas :
  measurable_fun [set: ar_carrier Ar P2] (fun c => (par1 c, par2 c)).
Proof. exact: (measurable_fun_pair par1_meas par2_meas). Qed.

(** Computation at a cast pair: the projections read off the
    components ([ar_prod_castK]). *)
Lemma par1_cast (a b : ar_carrier Ar R_obj) :
  par1 (ar_prod_cast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj) (a, b)) = cR a.
Proof. by rewrite /par1 ar_prod_castK. Qed.

Lemma par2_cast (a b : ar_carrier Ar R_obj) :
  par2 (ar_prod_cast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj) (a, b)) = cR b.
Proof. by rewrite /par2 ar_prod_castK. Qed.

(** *** The gaussian kernel *)

Definition gaussian_ker_fun (c : ar_carrier Ar P2) :
    fmeas R (ar_carrier Ar R_obj) :=
  if par2 c == 0%R then dirac_fmeas (toC (par1 c))
  else fmeas_of_prob
         [the probability _ _ of normal_prob (par1 c) (par2 c)].

Lemma gaussian_ker_funE (c : ar_carrier Ar P2)
    (U : set (ar_carrier Ar R_obj)) :
  measurable U ->
  fmeas_mu (gaussian_ker_fun c) U =
  if par2 c == 0%R then \d_(toC (par1 c)) U
  else normal_prob (par1 c) (par2 c) (toC @^-1` U).
Proof.
move=> mU; rewrite /gaussian_ker_fun; case: (par2 c == 0%R).
- exact: dirac_fmeas_E.
- exact: fmeas_of_probE.
Qed.

(** Computation at a cast pair of transported reals: the kernel IS
    the (totalised) transported normal family at the parameters. *)
Lemma gaussian_ker_fun_cast (m s : R) :
  gaussian_ker_fun
    (ar_prod_cast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj) (toC m, toC s)) =
  if s == 0%R then dirac_fmeas (toC m)
  else fmeas_of_prob [the probability _ _ of normal_prob m s].
Proof.
by rewrite /gaussian_ker_fun par1_cast par2_cast !R_to_carrierK.
Qed.

(** The per-[U] reading at a cast pair with a RAW carrier first
    component (the runtime-parameter shape: the mean is a sampled
    carrier point [c], the deviation a transported literal [s]). *)
Lemma gaussian_ker_cast_E (c : ar_carrier Ar R_obj) (s : R)
    (U : set (ar_carrier Ar R_obj)) :
  measurable U ->
  fmeas_mu (gaussian_ker_fun
    (ar_prod_cast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj) (c, toC s))) U =
  if s == 0%R then \d_(toC (cR c)) U
  else normal_prob (cR c) s (toC @^-1` U).
Proof.
by move=> mU; rewrite gaussian_ker_funE// par1_cast par2_cast R_to_carrierK.
Qed.

Lemma gaussian_ker_meas (U : set (ar_carrier Ar R_obj)) :
  measurable U ->
  measurable_fun [set: ar_carrier Ar P2]
    (fun c => fine (fmeas_mu (gaussian_ker_fun c) U)).
Proof.
move=> mU.
have mV : measurable (toC @^-1` U)
  := prob_push_pre_meas R_to_carrier_meas mU.
apply: (eq_measurable_fun (fun c =>
  if par2 c == 0%R then (\1_U (toC (par1 c)) : R)
  else fine (normal_prob (par1 c) (par2 c) (toC @^-1` U)))).
  move=> c _; rewrite gaussian_ker_funE//.
  by case: (par2 c == 0%R) => //; rewrite diracE indicE.
apply: measurable_fun_if => //.
- apply: measurable_fun_eqr => //; exact: par2_meas.
- apply: (measurable_funS measurableT (subsetT _)).
  apply: (measurableT_comp (measurable_indic mU)).
  apply: (measurableT_comp (f := toC)); first exact: R_to_carrier_meas.
  exact: par1_meas.
- apply: (measurable_funS measurableT (subsetT _)).
  apply: (measurableT_comp (f := fine)).
    exact: (fine_measurable measurableT).
  exact: (measurableT_comp (measurable_normal_prob_pair mV) par_pair_meas).
Qed.

Lemma gaussian_ker_ball (c : ar_carrier Ar P2) :
  (cone_norm (gaussian_ker_fun c) <= 1)%R.
Proof.
rewrite /gaussian_ker_fun; case: (par2 c == 0%R).
- by rewrite dirac_fmeas_norm.
- exact: fmeas_of_prob_ball.
Qed.

Definition gaussian_kernel : pkernel P2 R_obj :=
  MkPkernel gaussian_ker_fun gaussian_ker_meas gaussian_ker_ball.

(** Pointwise the gaussian kernel is a probability. *)
Lemma gaussian_kernel_norm1 (c : ar_carrier Ar P2) :
  cone_norm (pk_ker gaussian_kernel c) = 1%R.
Proof.
rewrite -[pk_ker _ _]/(gaussian_ker_fun c) /gaussian_ker_fun.
case: (par2 c == 0%R).
- by rewrite dirac_fmeas_norm.
- exact: fmeas_of_prob_norm1.
Qed.

(** *** The uniform kernel *)

Definition uniform_ker_fun (c : ar_carrier Ar P2) :
    fmeas R (ar_carrier Ar R_obj) :=
  match pselect ((par1 c < par2 c)%R) with
  | left ab => fmeas_of_prob [the probability _ _ of uniform_prob ab]
  | right _ => dirac_fmeas (toC (par1 c))
  end.

Lemma uniform_ker_funE (c : ar_carrier Ar P2)
    (U : set (ar_carrier Ar R_obj)) :
  measurable U ->
  fmeas_mu (uniform_ker_fun c) U =
  if (par1 c < par2 c)%R
  then uniform_int (par1 c) (par2 c) (toC @^-1` U)
  else \d_(toC (par1 c)) U.
Proof.
move=> mU; rewrite /uniform_ker_fun; case: pselect => [ab|nab].
- by rewrite ab fmeas_of_probE.
- have -> : (par1 c < par2 c)%R = false by apply/negbTE/negP.
  exact: dirac_fmeas_E.
Qed.

(** The per-[U] reading at a cast pair of transported reals. *)
Lemma uniform_ker_cast_E (a b : R) (U : set (ar_carrier Ar R_obj)) :
  measurable U ->
  fmeas_mu (uniform_ker_fun
    (ar_prod_cast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj) (toC a, toC b))) U =
  if (a < b)%R then uniform_int a b (toC @^-1` U)
  else \d_(toC a) U.
Proof.
by move=> mU; rewrite uniform_ker_funE// par1_cast par2_cast !R_to_carrierK.
Qed.

Lemma uniform_ker_meas (U : set (ar_carrier Ar R_obj)) :
  measurable U ->
  measurable_fun [set: ar_carrier Ar P2]
    (fun c => fine (fmeas_mu (uniform_ker_fun c) U)).
Proof.
move=> mU.
have mV : measurable (toC @^-1` U)
  := prob_push_pre_meas R_to_carrier_meas mU.
apply: (eq_measurable_fun (fun c =>
  if (par1 c < par2 c)%R
  then fine (uniform_int (par1 c) (par2 c) (toC @^-1` U))
  else (\1_U (toC (par1 c)) : R))).
  move=> c _; rewrite uniform_ker_funE//.
  by case: (par1 c < par2 c)%R => //; rewrite diracE indicE.
apply: measurable_fun_if => //.
- apply: measurable_fun_ltr; [exact: par1_meas | exact: par2_meas].
- apply: (measurable_funS measurableT (subsetT _)).
  apply: (measurableT_comp (f := fine)).
    exact: (fine_measurable measurableT).
  exact: (measurableT_comp (measurable_uniform_int_pair mV) par_pair_meas).
- apply: (measurable_funS measurableT (subsetT _)).
  apply: (measurableT_comp (measurable_indic mU)).
  apply: (measurableT_comp (f := toC)); first exact: R_to_carrier_meas.
  exact: par1_meas.
Qed.

Lemma uniform_ker_ball (c : ar_carrier Ar P2) :
  (cone_norm (uniform_ker_fun c) <= 1)%R.
Proof.
rewrite /uniform_ker_fun; case: pselect => [ab|_].
- exact: fmeas_of_prob_ball.
- by rewrite dirac_fmeas_norm.
Qed.

Definition uniform_kernel : pkernel P2 R_obj :=
  MkPkernel uniform_ker_fun uniform_ker_meas uniform_ker_ball.

(** Pointwise the uniform kernel is a probability. *)
Lemma uniform_kernel_norm1 (c : ar_carrier Ar P2) :
  cone_norm (pk_ker uniform_kernel c) = 1%R.
Proof.
rewrite -[pk_ker _ _]/(uniform_ker_fun c) /uniform_ker_fun.
case: pselect => [ab|_].
- exact: fmeas_of_prob_norm1.
- by rewrite dirac_fmeas_norm.
Qed.

End NamedKernels.

Arguments pmeas_of_prob {R Ar R_obj} R_carrier_eq R_to_carrier_meas P.
