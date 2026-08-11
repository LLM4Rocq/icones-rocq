(** * A lax monoidal map for [FMeas] — function level and [icones_hom] level

    Paper reference: §9, the symmetric monoidal structure of [FMeas].

    Mathematical content.  For [X, Y : ar_obj Ar], the product measure
    [µ × ν] defines a lax monoidal map

      [fmeas_lax_pre : FMeas X → FMeas Y → FMeas (ar_prod X Y),]
      [fmeas_lax_pre µ ν = pushforward of (µ ×_meas ν) along ar_prod_cast.]

    The carrier of [fmeas_prod µ ν] is the *cartesian* product
    [(ar_carrier X * ar_carrier Y)%type]; [ar_prod_cast] is the
    propositional carrier cast to [ar_carrier (ar_prod X Y)].

    Coverage (function level).

    - [fmeas_lax_pre µ ν : fmeas R (ar_carrier Ar (ar_prod Ar X Y))]
      — the pushforward of the cartesian-product fmeas along
      [ar_prod_cast], canonicalised to vanish off the σ-algebra.
    - [fmeas_lax_preE] — agreement on measurable [U] with the raw
      pushforward equation
      [(fmeas_lax_pre µ ν) U = (µ ×_meas ν) (ar_prod_cast @^-1` U)].
    - [fmeas_lax_pre_setT] / [fmeas_lax_pre_normE] — the total-mass
      product formula [(fmeas_lax_pre µ ν)(setT) = µ(setT)·ν(setT)] and
      the norm identity [‖fmeas_lax_pre µ ν‖ = ‖µ‖·‖ν‖].
    - [fmeas_lax_pre_dirac] — the Dirac identity at the function level
      [fmeas_lax_pre (dirac_fmeas x) (dirac_fmeas y) =
         dirac_fmeas (ar_prod_cast (x, y))].

    Coverage ([icones_hom] level — paper §9 packaging).

    - [dirac_lax x : path_car Ar Y (FMeas (X × Y))] — the path
      [y ↦ δ_{ar_prod_cast (x, y)}].
    - [dirac_lax_is_path_of_paths] — [x ↦ dirac_lax x] is itself a
      measurable path of [path_car Ar Y (FMeas (X × Y))].
    - [fmeas_lax_pre_at_dirac x := int_to_linhom (dirac_lax x)]
      — the inner [linhom_car Ar (FMeas Y) (FMeas (X × Y))] for fixed
      [x], via paper Thm 6.1.
    - [fmeas_lax_outer := int_to_linhom (x ↦ fmeas_lax_pre_at_dirac x)]
      — the outer [linhom_car Ar (FMeas X) (FMeas Y ⊸ FMeas (X × Y))],
      via paper Thm 6.1 applied at the [linhom_car] iCone using Phase A's
      [int_to_linhom_pres_path_in_cone] for path-preservation in the
      cone variable.
    - [fmeas_lax X Y : icones_hom Ar (tensor (FMeas X) (FMeas Y))
                                     (FMeas (X × Y))]
      — the genuine lax-monoidal map at the ICones level, obtained by
      [tensor_uncurry] from [fmeas_lax_outer] packaged as an
      [icones_hom] via [linhom_icones].
    - [fmeas_lax_pre_iterated] — the load-bearing Pettis/Tonelli
      identity expressing [fmeas_lax_pre µ ν] on measurable [U] as
      the iterated icone-integral of [dirac_lax].
    - [fmeas_lax_E] — pointwise computation on the pure tensor:
      [fmeas_lax X Y (µ ⊗p ν) = fmeas_lax_pre µ ν].
    - [fmeas_lax_dirac] — the Dirac identity at the [icones_hom]
      level:
      [fmeas_lax X Y (δ_x ⊗p δ_y) = δ_{ar_prod_cast (x, y)}].
      The load-bearing computational content used by
      [theories/programs/ppl.v]. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals constructive_ereal.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import ereal.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import measure.
From mathcomp.analysis Require Import dirac_measure.
From mathcomp.analysis Require Import lebesgue_integral_definition.
From mathcomp.analysis Require Import lebesgue_integral_nonneg.
From mathcomp.analysis Require Import lebesgue_integral_monotone_convergence.
From mathcomp.analysis Require Import lebesgue_integral_fubini.

Require Import Icones.prelude.nonneg_extra.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.cone_cat.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.icones.pettis.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_integral.
Require Import Icones.icones.examples_icone.
Require Import Icones.icones.fubini.
Require Import Icones.mcones.path.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.test_pullback.
Require Import Icones.icones.icone_cat.
Require Import Icones.homs.representable.
Require Import Icones.homs.linhom.
Require Import Icones.homs.bilin.
Require Import Icones.homs.linhom_functor.
Require Import Icones.homs.icones_iso.
Require Import Icones.homs.limpl_continuous.
Require Import Icones.homs.tensor_construct.
Require Import Icones.homs.tensor_hom_iso.
Require Import Icones.homs.tensor_iso.
Require Import Icones.homs.tensor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** The lax pre-map [fmeas_lax_pre]

    For [µ : FMeas X], [ν : FMeas Y], the canonical measure
    [(µ ×_meas ν)] lives on the cartesian product carrier
    [(ar_carrier X * ar_carrier Y)%type]. We push it forward along
    the propositional carrier cast
    [ar_prod_cast : ar_carrier X * ar_carrier Y → ar_carrier (ar_prod X Y)]
    (a measurable function, by the [MeasSubcat] record field
    [ar_prod_cast_meas]). *)

Section FmeasLaxPre.
Local Open Scope ereal_scope.
Variables (R : realType) (Ar : MeasSubcat R).
Variables X Y : ar_obj Ar.
Variables (µ : fmeas R (ar_carrier Ar X)) (ν : fmeas R (ar_carrier Ar Y)).

(** Canonicalised pushforward of [fmeas_prod µ ν] along
    [ar_prod_cast], cut off on non-measurable sets. *)
Local Definition lax_fun :
    set (ar_carrier Ar (ar_prod Ar X Y)) -> \bar R :=
  fun A => if `[< measurable A >] then
             pushforward (fmeas_mu (fmeas_prod µ ν))
                         (ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y)) A
           else 0.

Local Lemma lax_funE A :
  measurable A ->
  lax_fun A =
  pushforward (fmeas_mu (fmeas_prod µ ν))
              (ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y)) A.
Proof. by move=> mA; rewrite /lax_fun asboolT. Qed.

Local Lemma lax_fun_off A :
  ~ measurable A -> lax_fun A = 0.
Proof. by move=> nmA; rewrite /lax_fun asboolF. Qed.

Local Lemma lax_fun_set0 : lax_fun set0 = 0.
Proof.
rewrite lax_funE ?measurable0//.
by rewrite /pushforward preimage_set0 measure0.
Qed.

Local Lemma lax_fun_ge0 A : 0 <= lax_fun A.
Proof.
rewrite /lax_fun; case: asboolP => _; last exact: lexx.
apply: measure_ge0.
exact: (ar_prod_cast_meas Ar X Y).
Qed.

Local Lemma lax_fun_sigma_additive :
  semi_sigma_additive lax_fun.
Proof.
move=> F mF tF mUF.
have measc : measurable_fun setT
    (ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y))
  by exact: (ar_prod_cast_meas Ar X Y).
have base := @measure_semi_sigma_additive _ _ R
  (pushforward (fmeas_mu (fmeas_prod µ ν))
               (ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y)))
  F mF tF mUF.
have eqU : lax_fun (\bigcup_n F n) =
           pushforward (fmeas_mu (fmeas_prod µ ν))
                       (ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y))
                       (\bigcup_n F n).
  by rewrite lax_funE.
have eqi i : lax_fun (F i) =
             pushforward (fmeas_mu (fmeas_prod µ ν))
                         (ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y))
                         (F i).
  by rewrite lax_funE.
rewrite eqU.
have -> :
  (fun n => \sum_(0 <= i < n) lax_fun (F i)) =
  (fun n => \sum_(0 <= i < n)
              pushforward (fmeas_mu (fmeas_prod µ ν))
                          (ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y))
                          (F i)).
  by apply: funext => n; apply: eq_bigr => i _; exact: eqi.
exact: base.
Qed.

HB.instance Definition _ :=
  isMeasure.Build (ar_disp Ar (ar_prod Ar X Y))
                  (ar_carrier Ar (ar_prod Ar X Y)) R
    lax_fun
    lax_fun_set0 lax_fun_ge0
    lax_fun_sigma_additive.

(** Finiteness on every measurable set. *)
Local Lemma lax_fun_finP : fmeas_finP lax_fun.
Proof.
move=> U mU; rewrite lax_funE//.
rewrite /pushforward.
apply: fmeas_fin.
have measc : measurable_fun setT
    (ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y))
  by exact: (ar_prod_cast_meas Ar X Y).
rewrite -[X in measurable X]setTI.
exact: measc.
Qed.

Local Lemma lax_fun_canon : fmeas_canon lax_fun.
Proof. exact: lax_fun_off. Qed.

(** The lax pre-map as an [fmeas]. *)
Definition fmeas_lax_pre :
    fmeas R (ar_carrier Ar (ar_prod Ar X Y)) :=
  MkFmeas
    [the {measure set _ -> \bar R} of lax_fun]
    lax_fun_finP lax_fun_canon.

(** Agreement on measurable [U]: [fmeas_lax_pre] is the
    pushforward of [µ ×_meas ν] along [ar_prod_cast]. *)
Lemma fmeas_lax_preE (U : set (ar_carrier Ar (ar_prod Ar X Y))) :
  measurable U ->
  fmeas_mu fmeas_lax_pre U =
  fmeas_mu (fmeas_prod µ ν)
           ((ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y)) @^-1` U).
Proof. exact: lax_funE. Qed.

(** Total mass: [(fmeas_lax_pre)(setT) = µ(setT) · ν(setT)]. *)
Lemma fmeas_lax_pre_setT :
  fmeas_mu fmeas_lax_pre [set: ar_carrier Ar (ar_prod Ar X Y)] =
  fmeas_mu µ [set: ar_carrier Ar X] * fmeas_mu ν [set: ar_carrier Ar Y].
Proof.
rewrite fmeas_lax_preE//.
have preE : (ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y))
                @^-1` [set: ar_carrier Ar (ar_prod Ar X Y)] =
             [set: (ar_carrier Ar X * ar_carrier Ar Y)%type].
  by apply/seteqP; split.
rewrite preE.
have setT_eq : ([set: (ar_carrier Ar X * ar_carrier Ar Y)%type] =
                [set: ar_carrier Ar X] `*` [set: ar_carrier Ar Y])%classic.
  by apply/seteqP; split=> // -[a b].
by rewrite setT_eq fmeas_prod_rectE.
Qed.

(** Norm bound: [‖fmeas_lax_pre‖ = ‖µ‖ · ‖ν‖]. *)
Lemma fmeas_lax_pre_normE :
  (fmeas_norm fmeas_lax_pre = fmeas_norm µ * fmeas_norm ν)%R.
Proof.
rewrite /fmeas_norm fmeas_lax_pre_setT fineM//.
- exact: fmeas_setT_fin.
- exact: fmeas_setT_fin.
Qed.

End FmeasLaxPre.

Arguments fmeas_lax_pre {R Ar X Y} µ ν.
Arguments fmeas_lax_preE {R Ar X Y} µ ν.
Arguments fmeas_lax_pre_setT {R Ar X Y} µ ν.
Arguments fmeas_lax_pre_normE {R Ar X Y} µ ν.

(** ** Dirac identity

    [fmeas_lax_pre (δ_x) (δ_y) = δ_(ar_prod_cast (x, y))].

    Proof.  By [fmeas_eq], it suffices to check both sides on every
    measurable set [U].  Both sides are by definition the value
    [(δ_x ×_meas δ_y) (ar_prod_cast @^-1` U)] and
    [δ_(ar_prod_cast (x, y)) U] respectively; the standard product-
    Dirac fact

      [(δ_x ×_meas δ_y) A = δ_{(x, y)} A    for all measurable A]

    is verified via [indic_fubini_tonelli1] (mathcomp-analysis):
    [(δ_x ×_meas δ_y)(A) = ∫[δ_x]_x' δ_y (xsection A x')
                          = δ_y (xsection A x)
                          = ((x, y) ∈ A)
                          = δ_{(x, y)} (A)]. *)

Section FmeasLaxPreDirac.
Local Open Scope ereal_scope.
Variables (R : realType) (Ar : MeasSubcat R).
Variables X Y : ar_obj Ar.

(** Key step — the product of two canonical Dirac measures, viewed
    on the cartesian product, is the Dirac at the pair, on every
    measurable [A]. *)
Lemma dirac_prod_E (x : ar_carrier Ar X) (y : ar_carrier Ar Y)
    (A : set (ar_carrier Ar X * ar_carrier Ar Y)) :
  measurable A ->
  (fmeas_fin_view (dirac_fmeas x) \x fmeas_fin_view (dirac_fmeas y)) A =
  \d_(x, y) A.
Proof.
move=> mA.
(* Strategy: (m1 \x m2) A = ∫[m1]_x m2 (xsection A x') = m2 (xsection A x)
            = δ_y (xsection A x) = ((x,y) ∈ A) = δ_(x,y) A. *)
(* Step 1: rewrite LHS via the rectangle/xsection formula. *)
have lhs_step :
    (fmeas_fin_view (dirac_fmeas x) \x fmeas_fin_view (dirac_fmeas y)) A =
    \int[fmeas_fin_view (dirac_fmeas x)]_x'
       (fmeas_fin_view (dirac_fmeas y)) (xsection A x').
  rewrite -[in LHS](setIT A) -integral_indic//.
  rewrite (@indic_fubini_tonelli1 _ _ _ _ _
            (fmeas_fin_view (dirac_fmeas x))
            (fmeas_fin_view (dirac_fmeas y)) _ mA).
  have HF : fubini_F (fmeas_fin_view (dirac_fmeas y))
                     (EFin \o numfun.indic A) =
            (fmeas_fin_view (dirac_fmeas y)) \o xsection A.
    exact: indic_fubini_tonelli_FE.
  apply: eq_integral => x' _.
  by rewrite HF.
rewrite lhs_step.
(* Step 2: switch outer integration measure to \d_x. *)
have eq_xint :
    \int[fmeas_fin_view (dirac_fmeas x)]_x'
       (fmeas_fin_view (dirac_fmeas y)) (xsection A x') =
    \int[\d_x]_x'
       (fmeas_fin_view (dirac_fmeas y)) (xsection A x').
  apply: eq_measure_integral => U mU _.
  transitivity (fmeas_fin_view (dirac_fmeas x) U); first by [].
  transitivity (fmeas_mu (dirac_fmeas x) U); first exact: fmeas_fin_viewE.
  exact: dirac_fmeas_E.
rewrite eq_xint.
(* Step 3: measurability of the integrand. *)
have meas_g : measurable_fun setT
    (fun x' : ar_carrier Ar X =>
       (fmeas_fin_view (dirac_fmeas y)) (xsection A x')).
  have step := @indic_measurable_fun_fubini_tonelli_F _ _ _ _ R
                 (fmeas_fin_view (dirac_fmeas y)) A mA.
  rewrite (indic_fubini_tonelli_FE (fmeas_fin_view (dirac_fmeas y)) mA) in step.
  exact: step.
(* Step 4: integral against \d_x. *)
have rhs_step :
    \int[\d_x]_x' (fmeas_fin_view (dirac_fmeas y)) (xsection A x') =
    (fmeas_fin_view (dirac_fmeas y)) (xsection A x).
  by rewrite integral_dirac// diracT mul1e.
rewrite rhs_step.
(* Step 5: fmeas_fin_view (dirac_fmeas y) (xsection A x) = \d_y (xsection A x). *)
rewrite /fmeas_fin_view /mfrestr /mrestr/= setIT.
rewrite dirac_fmeas_E; last exact: measurable_xsection.
(* Step 6: \d_y (xsection A x) = ((x,y) ∈ A) = \d_{(x,y)} A. *)
rewrite !diracE.
congr (_%:E).
congr (_%:R).
by rewrite mem_xsection.
Qed.

(** The Dirac identity at the fmeas-level. *)
Lemma fmeas_lax_pre_dirac (x : ar_carrier Ar X) (y : ar_carrier Ar Y) :
  fmeas_lax_pre (dirac_fmeas x) (dirac_fmeas y) =
  dirac_fmeas (X := ar_prod Ar X Y)
              (ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y) (x, y)).
Proof.
apply: fmeas_eq => U mU.
rewrite fmeas_lax_preE//.
rewrite dirac_fmeas_E//.
(* LHS: pushforward of (δ_x × δ_y) along ar_prod_cast at U. *)
(* = (δ_x × δ_y) (ar_prod_cast ⁻¹ U) = \d_(x,y) (ar_prod_cast ⁻¹ U). *)
have mpreU : measurable
    ((ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y)) @^-1` U).
  have measc : measurable_fun setT
      (ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y))
    by exact: (ar_prod_cast_meas Ar X Y).
  rewrite -[X in measurable X]setTI.
  exact: measc.
rewrite fmeas_prodE//.
rewrite (dirac_prod_E _ _ mpreU).
(* \d_(x,y) (ar_prod_cast ⁻¹ U) = ((x,y) ∈ ar_prod_cast ⁻¹ U)
                                = (ar_prod_cast (x,y) ∈ U). *)
rewrite !diracE.
by congr (_%:E).
Qed.

End FmeasLaxPreDirac.

Arguments dirac_prod_E {R Ar X Y} x y A.
Arguments fmeas_lax_pre_dirac {R Ar X Y} x y.

(** ** Phase B — packaging [fmeas_lax_pre] as an [icones_hom]

    Paper §9: the symmetric monoidal structure of [FMeas].  Building
    on Phase A ([int_to_linhom_pres_path_in_cone] in [bilin.v]) and
    on the function-level [fmeas_lax_pre] / [fmeas_lax_pre_dirac]
    delivered above, we package the lax monoidal map of [FMeas] as
    a genuine [icones_hom]

      [fmeas_lax X Y :
         icones_hom Ar (FMeas X ⊗ FMeas Y) (FMeas (ar_prod X Y))]

    with the load-bearing computation

      [fmeas_lax X Y (δ_x ⊗p δ_y) = δ_{ar_prod_cast (x, y)}].

    Strategy.  Use two nested applications of paper Thm 6.1
    ([int_to_linhom] from [bilin.v]) and Phase A's
    [int_to_linhom_pres_path_in_cone] (cone-variable path-preservation):

    - Innermost path: [dirac_lax x : path_car Ar Y (FMeas (X × Y))],
      the path [y ↦ δ_{ar_prod_cast (x, y)}].  Direct from
      [dirac_fmeas_is_path] reindexed along [ar_prod_cast (x, _)].

    - Inner linhom: [fmeas_lax_pre_at_dirac x :=
         int_to_linhom (dirac_lax x) : FMeas Y ⊸ FMeas (X × Y)].

    - Cone-variable path of inner linhoms: by Phase A,
      [x ↦ fmeas_lax_pre_at_dirac x] is a measurable path of
      [linhom_car Ar (FMeas Y) (FMeas (X × Y))], provided
      [x ↦ dirac_lax x] is itself a measurable path of
      [path_car Ar Y (FMeas (X × Y))].

    - Outer linhom: [fmeas_lax_outer_pre := int_to_linhom (fun x =>
        fmeas_lax_pre_at_dirac x)] is a [linhom_car Ar (FMeas X)
        (linhom_car Ar (FMeas Y) (FMeas (X × Y)))].

    - Packaging: a norm-[≤1] bound on [fmeas_lax_outer_pre] (proved
      via the [‖fmeas_lax_pre µ ν‖ = ‖µ‖·‖ν‖] norm identity)
      yields an [icones_hom Ar (FMeas X) (FMeas Y ⊸ FMeas (X × Y))]
      through [linhom_icones]; then [tensor_uncurry] produces the
      target [icones_hom (FMeas X ⊗ FMeas Y) (FMeas (X × Y))].

    The pointwise identity [fmeas_lax (µ ⊗p ν) = fmeas_lax_pre µ ν]
    ([fmeas_lax_E]) follows from [tensor_curryEp] composed with
    [linhom_int_eval] (paper Lemma 5.4) and a single Tonelli step on
    the indicator of [ar_prod_cast @^-1` U]. *)

(** *** The Dirac path of products [dirac_lax x : Y → FMeas (X × Y)] *)

Section DiracLaxPath.
Variables (R : realType) (Ar : MeasSubcat R).
Variables X Y : ar_obj Ar.

(** [dirac_lax_fun x y := δ_{ar_prod_cast (x, y)}] *)
Definition dirac_lax_fun (x : ar_carrier Ar X) (y : ar_carrier Ar Y) :
    fmeas R (ar_carrier Ar (ar_prod Ar X Y)) :=
  dirac_fmeas (ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y) (x, y)).

(** For each fixed [x], [y ↦ dirac_lax_fun x y] is a measurable path
    of [FMeas (X × Y)]. *)
Lemma dirac_lax_is_path (x : ar_carrier Ar X) :
  is_measurable_path
    (Ar:=Ar) (C:=fmeas R (ar_carrier Ar (ar_prod Ar X Y)))
    (X:=Y) (dirac_lax_fun x).
Proof.
split.
  by exists 1 => y; rewrite /dirac_lax_fun dirac_fmeas_norm.
move=> Z m mM.
case: mM => [U [mU ->]].
(* test_fun (fmeas_eU U) s (dirac_lax_fun x y)
   = fine (\d_{ar_prod_cast (x, y)} U). *)
apply: (eq_measurable_fun
  (fun p : ar_carrier Ar Z * ar_carrier Ar Y =>
     fine (\d_(ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y) (x, p.2)) U
           : \bar R))).
  by move=> p _; rewrite /= /eU_fun /= /dirac_lax_fun dirac_fmeas_E.
pose g (y : ar_carrier Ar Y) : \bar R :=
  \d_(ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y) (x, y)) U.
have g_meas : measurable_fun setT g.
  apply: (measurableT_comp (f := fun p => \d_p U)).
  - exact: measurable_fun_dirac.
  - apply: (measurableT_comp (f := ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y))).
    + exact: (ar_prod_cast_meas Ar X Y).
    + by apply: measurable_fun_pair; [exact: measurable_cst|exact: @measurable_id].
have finecomp : measurable_fun setT
                  (fun y : ar_carrier Ar Y => fine (g y)).
  by apply: (measurableT_comp (f := fine)) => //; exact: fine_measurable.
exact: (measurableT_comp finecomp measurable_snd).
Qed.

(** Packaged as a [path_car]. *)
Definition dirac_lax (x : ar_carrier Ar X) :
    path_car Ar Y (fmeas R (ar_carrier Ar (ar_prod Ar X Y))) :=
  MkPath (dirac_lax_is_path x).

(** The path-of-paths [x ↦ dirac_lax x] is a measurable path of
    [path_car Ar Y (FMeas (X × Y))]. *)
Lemma dirac_lax_is_path_of_paths :
  is_measurable_path
    (Ar:=Ar)
    (C:=path_car Ar Y (fmeas R (ar_carrier Ar (ar_prod Ar X Y))))
    (X:=X)
    dirac_lax.
Proof.
split.
  exists 1 => x.
  rewrite /cone_norm /= /path_norm.
  apply: ge_sup; first exact: path_normset_nonempty.
  move=> _ [y ->] /=.
  by rewrite /dirac_lax_fun dirac_fmeas_norm.
move=> Z m mM.
case: mM => [φ [m' [m'M ->]]].
(* test_fun (path_test φ m' m'M) s (dirac_lax x)
   = test_fun m' s (dirac_lax_fun x (φ s)). *)
have [U [mU m'_eq]] : exists U (mU : measurable U),
    m' = fmeas_eU (R := R) (X := ar_carrier Ar (ar_prod Ar X Y))
                  (Ar := Ar) Z mU.
  by case: m'M => U [mU ->]; exists U, mU.
apply: (eq_measurable_fun
  (fun p : ar_carrier Ar Z * ar_carrier Ar X =>
     fine (\d_(ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y) (p.2, φ p.1)) U
           : \bar R))).
  move=> p _ /=.
  rewrite /path_test /= /path_test_fun /= /dirac_lax_fun.
  by rewrite m'_eq /= /eU_fun /= dirac_fmeas_E.
pose g (q : ar_carrier Ar X * ar_carrier Ar Y) : \bar R :=
  \d_(ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y) q) U.
have g_meas : measurable_fun setT g.
  apply: (measurableT_comp (f := fun p => \d_p U)).
  - exact: measurable_fun_dirac.
  - exact: (ar_prod_cast_meas Ar X Y).
pose ψ (p : ar_carrier Ar Z * ar_carrier Ar X) :
    ar_carrier Ar X * ar_carrier Ar Y :=
  (p.2, φ p.1).
have ψ_meas : measurable_fun
  [set: ar_carrier Ar Z * ar_carrier Ar X] ψ.
  apply: measurable_fun_pair; first exact: measurable_snd.
  by apply: (measurableT_comp (f := φ));
    [exact: measurable_funPT|exact: measurable_fst].
have g_comp_ψ_meas : measurable_fun
  [set: ar_carrier Ar Z * ar_carrier Ar X] (g \o ψ).
  exact: (measurableT_comp g_meas ψ_meas).
have finecomp : measurable_fun
  [set: ar_carrier Ar Z * ar_carrier Ar X]
  (fun p => fine ((g \o ψ) p)).
  by apply: (measurableT_comp (f := fine)) => //; exact: fine_measurable.
by [].
Qed.

End DiracLaxPath.

Arguments dirac_lax_fun {R Ar X Y}.
Arguments dirac_lax {R Ar X Y}.
Arguments dirac_lax_is_path {R Ar X Y} x.
Arguments dirac_lax_is_path_of_paths {R Ar} X Y.

(** *** Inner linhom [fmeas_lax_pre_at_dirac x : FMeas Y ⊸ FMeas (X × Y)] *)

Section FmeasLaxInner.
Variables (R : realType) (Ar : MeasSubcat R).
Variables X Y : ar_obj Ar.

(** The inner linhom at [x : X] is [int_to_linhom (dirac_lax x)].
    By paper Thm 6.1, this is a [linhom_car Ar (FMeas Y) (FMeas (X × Y))].
    Its underlying function is
      [ν ↦ icone_integral (dirac_lax x) _ ν]. *)
Definition fmeas_lax_pre_at_dirac (x : ar_carrier Ar X) :
    linhom_car Ar (fmeas R (ar_carrier Ar Y))
                  (fmeas R (ar_carrier Ar (ar_prod Ar X Y))) :=
  int_to_linhom (dirac_lax x).

(** By Phase A's [int_to_linhom_pres_path_in_cone] applied to the
    measurable path-of-paths [dirac_lax_is_path_of_paths]. *)
Lemma fmeas_lax_pre_at_dirac_is_path :
  is_measurable_path
    (Ar:=Ar)
    (C:=linhom_car Ar (fmeas R (ar_carrier Ar Y))
                      (fmeas R (ar_carrier Ar (ar_prod Ar X Y))))
    (X:=X)
    fmeas_lax_pre_at_dirac.
Proof.
exact:
  (int_to_linhom_pres_path_in_cone dirac_lax (dirac_lax_is_path_of_paths X Y)).
Qed.

End FmeasLaxInner.

Arguments fmeas_lax_pre_at_dirac {R Ar X Y}.
Arguments fmeas_lax_pre_at_dirac_is_path {R Ar} X Y.

(** *** Outer linhom [fmeas_lax_outer : FMeas X ⊸ (FMeas Y ⊸ FMeas (X × Y))] *)

Section FmeasLaxOuter.
Variables (R : realType) (Ar : MeasSubcat R).
Variables X Y : ar_obj Ar.

Local Notation L := (linhom_car Ar (fmeas R (ar_carrier Ar Y))
                                   (fmeas R (ar_carrier Ar (ar_prod Ar X Y)))).

(** The path-of-linhoms is itself a measurable path in [L]. *)
Definition fmeas_lax_outer_path : path_car Ar X L :=
  MkPath (fmeas_lax_pre_at_dirac_is_path X Y).

(** The outer linhom [µ ↦ int_to_linhom (fmeas_lax_outer_path)] gives
    the [linhom_car Ar (FMeas X) L] we want. *)
Definition fmeas_lax_outer :
    linhom_car Ar (fmeas R (ar_carrier Ar X)) L :=
  int_to_linhom fmeas_lax_outer_path.

(** Its operator-norm is bounded by [path_norm] of [fmeas_lax_outer_path],
    which is bounded by [1] (each inner linhom has norm [≤ 1] since
    [‖fmeas_lax_pre (δ_x) ν‖ = ‖δ_x‖ · ‖ν‖ = ‖ν‖]). *)
Lemma fmeas_lax_outer_path_norm_le1 :
  cone_norm fmeas_lax_outer_path <= 1.
Proof.
rewrite /cone_norm /=.
apply: ge_sup; first exact: path_normset_nonempty.
move=> _ [x ->] /=.
rewrite /fmeas_lax_pre_at_dirac.
(* [linhom_norm (int_to_linhom (dirac_lax x)) <= path_norm (dirac_lax x)] *)
apply: le_trans (int_to_linhom_norm_le (dirac_lax x)) _.
(* path_norm (dirac_lax x) <= 1 because each dirac_lax_fun x y is unit-norm. *)
rewrite /cone_norm /= /path_norm.
apply: ge_sup; first exact: path_normset_nonempty.
move=> _ [y ->] /=.
by rewrite /dirac_lax_fun dirac_fmeas_norm.
Qed.

Lemma fmeas_lax_outer_norm_le1 : cone_norm fmeas_lax_outer <= 1.
Proof.
rewrite /fmeas_lax_outer.
apply: le_trans (int_to_linhom_norm_le fmeas_lax_outer_path) _.
exact: fmeas_lax_outer_path_norm_le1.
Qed.

(** The outer linhom as an [icones_hom] via [linhom_icones]. *)
Definition fmeas_lax_outer_icones :
    icones_hom Ar (fmeas R (ar_carrier Ar X)) L :=
  linhom_icones fmeas_lax_outer fmeas_lax_outer_norm_le1.

End FmeasLaxOuter.

Arguments fmeas_lax_outer_path {R Ar} X Y.
Arguments fmeas_lax_outer {R Ar} X Y.
Arguments fmeas_lax_outer_icones {R Ar} X Y.

(** *** [fmeas_lax X Y : icones_hom (FMeas X ⊗ FMeas Y) (FMeas (X × Y))]

    The genuine lax-monoidal map at the [ICones] level, obtained by
    [tensor_uncurry] from the outer [icones_hom]. *)

Section FmeasLaxDef.
Variables (R : realType) (Ar : MeasSubcat R).
Variables X Y : ar_obj Ar.

Definition fmeas_lax :
    icones_hom Ar
      (tensor Ar (fmeas R (ar_carrier Ar X))
                 (fmeas R (ar_carrier Ar Y)))
      (fmeas R (ar_carrier Ar (ar_prod Ar X Y))) :=
  tensor_uncurry (fmeas_lax_outer_icones X Y).

End FmeasLaxDef.

Arguments fmeas_lax {R Ar} X Y.


(** *** Pettis-style Tonelli identity for [fmeas_lax_pre]

    For measurable [U ⊆ ar_carrier (X × Y)], the pushed-forward measure
    [fmeas_lax_pre µ ν] decomposes as the *iterated* icone-integral of
    the path-of-paths
    [dirac_lax x : Y → FMeas (X × Y)],
    via the standard Tonelli identity on the indicator of
    [ar_prod_cast @^-1` U].  This is the load-bearing step underlying
    [fmeas_lax_E]. *)

Section FmeasLaxIterated.
Local Open Scope ereal_scope.
Variables (R : realType) (Ar : MeasSubcat R).
Variables X Y : ar_obj Ar.

(** Helper: [(δ_{ar_prod_cast(x, y)})(U) = \d_{ar_prod_cast(x, y)} U] as
    an ereal on measurable [U]. *)
Lemma dirac_lax_funE (x : ar_carrier Ar X) (y : ar_carrier Ar Y)
    (U : set (ar_carrier Ar (ar_prod Ar X Y))) :
  measurable U ->
  fmeas_mu (dirac_lax_fun x y) U =
  \d_(ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y) (x, y)) U.
Proof. by move=> mU; rewrite /dirac_lax_fun dirac_fmeas_E. Qed.

(** Per-test Pettis equation for [icone_integral (dirac_lax x) _ ν]:
    on measurable [U], the integral measures the [ν]-fraction of
    [y]-fibres at [ar_prod_cast(x, ·)] hitting [U]. *)
Lemma icone_integral_dirac_lax_E (x : ar_carrier Ar X)
    (ν : fmeas R (ar_carrier Ar Y))
    (U : set (ar_carrier Ar (ar_prod Ar X Y))) :
  measurable U ->
  fmeas_mu (icone_integral (dirac_lax_fun x) (dirac_lax_is_path x) ν) U =
  \int[fmeas_mu ν]_(y in [set: ar_carrier Ar Y])
    \d_(ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y) (x, y)) U.
Proof.
move=> mU.
have mMU : mcone_M (Ar:=Ar) (ar_zero Ar)
              (fmeas_eU (R:=R) (X:=ar_carrier Ar (ar_prod Ar X Y))
                        (Ar:=Ar) (ar_zero Ar) mU).
  by exists U, mU.
have HP := icone_integralP (dirac_lax_fun x) (dirac_lax_is_path x) ν _ mMU
                           (ar_zero_pt Ar).
have rwInteg : forall y : ar_carrier Ar Y,
    \d_(ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y) (x, y)) U =
    fmeas_mu (dirac_lax_fun x y) U.
  by move=> y; rewrite (dirac_lax_funE _ _ mU).
under [in RHS]eq_integral => y _ do rewrite rwInteg.
have Hfin :
    fmeas_mu (icone_integral (dirac_lax_fun x) (dirac_lax_is_path x) ν) U
    \is a fin_num.
  exact: fmeas_fin.
have Hintfin :
    \int[fmeas_mu ν]_(y in [set: ar_carrier Ar Y])
      fmeas_mu (dirac_lax_fun x y) U \is a fin_num.
  have intle :
    \int[fmeas_mu ν]_(y in [set: ar_carrier Ar Y])
       fmeas_mu (dirac_lax_fun x y) U <=
    fmeas_mu ν [set: ar_carrier Ar Y].
    apply: (@le_trans _ _
      (\int[fmeas_mu ν]_(y in [set: ar_carrier Ar Y]) (1 : \bar R))); last first.
      by rewrite integral_cst// mul1e.
    apply: ge0_le_integral.
    - exact: measurableT.
    - by move=> y _; exact: measure_ge0.
    - apply: (eq_measurable_fun
        (fun y => \d_(ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y) (x, y)) U)).
        by move=> y _; rewrite rwInteg.
      have meas_d : measurable_fun setT
        (fun p : ar_carrier Ar (ar_prod Ar X Y) => \d_p U : \bar R).
        exact: measurable_fun_dirac.
      have measc : measurable_fun setT
        (ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y))
        by exact: (ar_prod_cast_meas Ar X Y).
      have meas_pair : measurable_fun setT
        (fun y : ar_carrier Ar Y =>
           ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y) (x, y)).
        apply: (measurableT_comp measc).
        by apply: measurable_fun_pair;
          [exact: measurable_cst|exact: @measurable_id].
      exact: (measurableT_comp meas_d meas_pair).
    - exact: measurable_cst.
    - move=> y _.
      rewrite -rwInteg.
      apply: (@le_trans _ _
        (\d_(ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y) (x, y)) setT)).
      + by apply: le_measure => //; rewrite inE.
      + by rewrite diracT.
  rewrite ge0_fin_numE//; last by apply: integral_ge0 => y _; exact: measure_ge0.
  apply: le_lt_trans intle _.
  have HfinT : fmeas_mu ν [set: ar_carrier Ar Y] \is a fin_num
    by exact: fmeas_setT_fin.
  by rewrite ltey_eq HfinT.
have HPE := HP.
rewrite /fmeas_eU /eU_fun /= in HPE.
rewrite -(fineK Hfin) -(fineK Hintfin); congr (_%:E).
rewrite HPE.
congr fine.
apply: eq_integral => y _.
have Hfiny : fmeas_mu (dirac_lax_fun x y) U \is a fin_num.
  exact: fmeas_fin.
by rewrite -[in RHS](fineK Hfiny).
Qed.

(** The fully iterated Pettis identity for [fmeas_lax_pre].  On
    measurable [U], the pushed-forward product is the [µ ↦ ν ↦] iterated
    icone-integral of [dirac_lax].  Proved via [fubini_tonelli1] on the
    indicator of [ar_prod_cast @^-1` U]. *)
Lemma fmeas_lax_pre_iterated
    (µ : fmeas R (ar_carrier Ar X)) (ν : fmeas R (ar_carrier Ar Y))
    (U : set (ar_carrier Ar (ar_prod Ar X Y))) :
  measurable U ->
  fmeas_mu (fmeas_lax_pre µ ν) U =
  \int[fmeas_mu µ]_(x in [set: ar_carrier Ar X])
    fmeas_mu (icone_integral (dirac_lax_fun x) (dirac_lax_is_path x) ν) U.
Proof.
move=> mU.
have rwInner : forall x : ar_carrier Ar X,
  fmeas_mu (icone_integral (dirac_lax_fun x) (dirac_lax_is_path x) ν) U =
  \int[fmeas_mu ν]_(y in [set: ar_carrier Ar Y])
    \d_(ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y) (x, y)) U.
  by move=> x; exact: icone_integral_dirac_lax_E.
under eq_integral => x _ do rewrite rwInner.
rewrite fmeas_lax_preE//.
have measc : measurable_fun setT
  (ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y))
  by exact: (ar_prod_cast_meas Ar X Y).
have mPreU : measurable
    ((ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y)) @^-1` U).
  rewrite -[X in measurable X]setTI; exact: measc.
rewrite fmeas_prodE//.
rewrite -[in LHS](setIT
  ((ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y)) @^-1` U)) -integral_indic//.
rewrite (@indic_fubini_tonelli1 _ _ _ _ _
          (fmeas_fin_view µ) (fmeas_fin_view ν) _ mPreU).
have eq_outer :
    \int[fmeas_fin_view µ]_(x in [set: ar_carrier Ar X])
      fubini_F (fmeas_fin_view ν) (EFin \o numfun.indic
        ((ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y)) @^-1` U)) x =
    \int[fmeas_mu µ]_(x in [set: ar_carrier Ar X])
      fubini_F (fmeas_fin_view ν) (EFin \o numfun.indic
        ((ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y)) @^-1` U)) x.
  by apply: eq_measure_integral => V mV _; exact: fmeas_fin_viewE.
rewrite eq_outer.
apply: eq_integral => x _.
rewrite (indic_fubini_tonelli_FE (fmeas_fin_view ν) mPreU).
have meas_xsec : measurable
    (xsection ((ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y)) @^-1` U) x).
  exact: measurable_xsection.
rewrite /=.
rewrite -[LHS]/(fmeas_fin_view ν
  (xsection ((ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y)) @^-1` U) x)).
rewrite (fmeas_fin_viewE _ _ meas_xsec).
rewrite -(setIT
  (xsection ((ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y)) @^-1` U) x))
  -integral_indic//.
apply: eq_integral => y _.
rewrite /numfun.indic /=.
rewrite (mem_xsection x y
  ((ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y)) @^-1` U)).
rewrite diracE.
by congr (((_)%:R)%:E).
Qed.

End FmeasLaxIterated.

Arguments dirac_lax_funE {R Ar X Y} x y U _.
Arguments icone_integral_dirac_lax_E {R Ar X Y} x ν U _.
Arguments fmeas_lax_pre_iterated {R Ar X Y} µ ν U _.

(** ** Symmetric (Y-then-X) Fubini for [fmeas_lax_pre] — Lemma B

    The Y-then-X dual of [fmeas_lax_pre_iterated], plus the headline
    commutativity statement [fmeas_lax_pre_fubini] that the two
    iteration orders agree.  These together express the *commutativity
    of the FMeas-Kleisli monad on the tensor* (Fubini at the
    Kleisli-monad level), the load-bearing identity that supports the
    downstream PPL marginal lemma for [ex_random_linear].

    Coverage.

    - [dirac_lax_fun_swap_is_path] : for each fixed [y : Y], the map
      [x ↦ δ_{ar_prod_cast(x, y)}] is itself a measurable path in
      [FMeas (X × Y)].  The symmetric dual of [dirac_lax_is_path].

    - [icone_integral_dirac_lax_swap_E] : the Pettis equation in the
      [µ]-on-[X] direction.

    - [fmeas_lax_pre_iterated_Y] : the load-bearing Y-then-X iteration
      identity, [(µ ⊗p ν)(U) = ∫[ν]_y ∫[µ]_x δ_{(x,y)}(U)].  Proved by
      chaining [fmeas_lax_pre_iterated] (X-then-Y) with mathcomp-analysis's
      symmetric [fubini_tonelli] on the dirac integrand — the genuine
      Fubini swap at the scalar level.

    - [fmeas_lax_pre_fubini] : the two iteration orders agree.
      Pure corollary of [fmeas_lax_pre_iterated] and
      [fmeas_lax_pre_iterated_Y]. *)

Section FmeasLaxIteratedSwap.
Local Open Scope ereal_scope.
Variables (R : realType) (Ar : MeasSubcat R).
Variables X Y : ar_obj Ar.

(** For each fixed [y : Y], the map [x ↦ δ_{ar_prod_cast(x, y)}] is
    a measurable path of [FMeas (X × Y)].  Symmetric to [dirac_lax_is_path]. *)
Lemma dirac_lax_fun_swap_is_path (y : ar_carrier Ar Y) :
  is_measurable_path
    (Ar:=Ar) (C:=fmeas R (ar_carrier Ar (ar_prod Ar X Y)))
    (X:=X) (fun x => dirac_lax_fun (Y:=Y) x y).
Proof.
split.
  by exists 1%R => x; rewrite /dirac_lax_fun dirac_fmeas_norm.
move=> Z m mM.
case: mM => [U [mU ->]].
apply: (eq_measurable_fun
  (fun p : ar_carrier Ar Z * ar_carrier Ar X =>
     fine (\d_(ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y) (p.2, y)) U
           : \bar R))).
  by move=> p _; rewrite /= /eU_fun /= /dirac_lax_fun dirac_fmeas_E.
pose g (x : ar_carrier Ar X) : \bar R :=
  \d_(ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y) (x, y)) U.
have g_meas : measurable_fun setT g.
  apply: (measurableT_comp (f := fun p => \d_p U)).
  - exact: measurable_fun_dirac.
  - apply: (measurableT_comp (f := ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y))).
    + exact: (ar_prod_cast_meas Ar X Y).
    + by apply: measurable_fun_pair;
        [exact: @measurable_id|exact: measurable_cst].
have finecomp : measurable_fun setT
                  (fun x : ar_carrier Ar X => fine (g x)).
  by apply: (measurableT_comp (f := fine)) => //; exact: fine_measurable.
exact: (measurableT_comp finecomp measurable_snd).
Qed.

(** Per-test Pettis equation for [icone_integral _ _ µ] with the swapped
    [dirac_lax].  On measurable [U], the integral measures the
    [µ]-fraction of [x]-fibres at [ar_prod_cast(·, y)] hitting [U]. *)
Lemma icone_integral_dirac_lax_swap_E (y : ar_carrier Ar Y)
    (µ : fmeas R (ar_carrier Ar X))
    (U : set (ar_carrier Ar (ar_prod Ar X Y))) :
  measurable U ->
  fmeas_mu (icone_integral (fun x => dirac_lax_fun x y)
                           (dirac_lax_fun_swap_is_path y) µ) U =
  \int[fmeas_mu µ]_(x in [set: ar_carrier Ar X])
    \d_(ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y) (x, y)) U.
Proof.
move=> mU.
have mMU : mcone_M (Ar:=Ar) (ar_zero Ar)
              (fmeas_eU (R:=R) (X:=ar_carrier Ar (ar_prod Ar X Y))
                        (Ar:=Ar) (ar_zero Ar) mU).
  by exists U, mU.
have HP := icone_integralP (fun x => dirac_lax_fun x y)
                           (dirac_lax_fun_swap_is_path y) µ _ mMU
                           (ar_zero_pt Ar).
have rwInteg : forall x : ar_carrier Ar X,
    \d_(ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y) (x, y)) U =
    fmeas_mu (dirac_lax_fun x y) U.
  by move=> x; rewrite /dirac_lax_fun dirac_fmeas_E.
under [in RHS]eq_integral => x _ do rewrite rwInteg.
have Hfin :
    fmeas_mu (icone_integral (fun x => dirac_lax_fun x y)
                             (dirac_lax_fun_swap_is_path y) µ) U
    \is a fin_num.
  exact: fmeas_fin.
have Hintfin :
    \int[fmeas_mu µ]_(x in [set: ar_carrier Ar X])
      fmeas_mu (dirac_lax_fun x y) U \is a fin_num.
  have intle :
    \int[fmeas_mu µ]_(x in [set: ar_carrier Ar X])
       fmeas_mu (dirac_lax_fun x y) U <=
    fmeas_mu µ [set: ar_carrier Ar X].
    apply: (@le_trans _ _
      (\int[fmeas_mu µ]_(x in [set: ar_carrier Ar X]) (1 : \bar R)));
      last first.
      by rewrite integral_cst// mul1e.
    apply: ge0_le_integral.
    - exact: measurableT.
    - by move=> x _; exact: measure_ge0.
    - apply: (eq_measurable_fun
        (fun x => \d_(ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y) (x, y)) U)).
        by move=> x _; rewrite rwInteg.
      have meas_d : measurable_fun setT
        (fun p : ar_carrier Ar (ar_prod Ar X Y) => \d_p U : \bar R).
        exact: measurable_fun_dirac.
      have measc : measurable_fun setT
        (ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y))
        by exact: (ar_prod_cast_meas Ar X Y).
      have meas_pair : measurable_fun setT
        (fun x : ar_carrier Ar X =>
           ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y) (x, y)).
        apply: (measurableT_comp measc).
        by apply: measurable_fun_pair;
          [exact: @measurable_id|exact: measurable_cst].
      exact: (measurableT_comp meas_d meas_pair).
    - exact: measurable_cst.
    - move=> x _.
      rewrite -rwInteg.
      apply: (@le_trans _ _
        (\d_(ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y) (x, y)) setT)).
      + by apply: le_measure => //; rewrite inE.
      + by rewrite diracT.
  rewrite ge0_fin_numE//; last
    by apply: integral_ge0 => x _; exact: measure_ge0.
  apply: le_lt_trans intle _.
  have HfinT : fmeas_mu µ [set: ar_carrier Ar X] \is a fin_num
    by exact: fmeas_setT_fin.
  by rewrite ltey_eq HfinT.
have HPE := HP.
rewrite /fmeas_eU /eU_fun /= in HPE.
rewrite -(fineK Hfin) -(fineK Hintfin); congr (_%:E).
rewrite HPE.
congr fine.
apply: eq_integral => x _.
have Hfinx : fmeas_mu (dirac_lax_fun x y) U \is a fin_num.
  exact: fmeas_fin.
by rewrite -[in RHS](fineK Hfinx).
Qed.

(** *** The Y-then-X iteration identity — the load-bearing Fubini step.

    Proved by chaining [fmeas_lax_pre_iterated] (the X-then-Y direction)
    with mathcomp-analysis's symmetric [fubini_tonelli] applied to the
    measurable nonneg dirac integrand [\d_{ar_prod_cast (x, y)} U]. *)
Lemma fmeas_lax_pre_iterated_Y
    (µ : fmeas R (ar_carrier Ar X)) (ν : fmeas R (ar_carrier Ar Y))
    (U : set (ar_carrier Ar (ar_prod Ar X Y))) :
  measurable U ->
  fmeas_mu (fmeas_lax_pre µ ν) U =
  \int[fmeas_mu ν]_(y in [set: ar_carrier Ar Y])
    fmeas_mu (icone_integral (fun x => dirac_lax_fun x y)
                             (dirac_lax_fun_swap_is_path y) µ) U.
Proof.
move=> mU.
(* Step 1: Replace inner integrand on the RHS by its Pettis expansion. *)
have rwInnerY : forall y : ar_carrier Ar Y,
  fmeas_mu (icone_integral (fun x => dirac_lax_fun x y)
                           (dirac_lax_fun_swap_is_path y) µ) U =
  \int[fmeas_mu µ]_(x in [set: ar_carrier Ar X])
    \d_(ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y) (x, y)) U.
  by move=> y; exact: icone_integral_dirac_lax_swap_E.
under eq_integral => y _ do rewrite rwInnerY.
(* Step 2: Rewrite LHS to the X-then-Y iterated form. *)
rewrite (fmeas_lax_pre_iterated µ ν U mU).
have rwInnerX : forall x : ar_carrier Ar X,
  fmeas_mu (icone_integral (dirac_lax_fun x) (dirac_lax_is_path x) ν) U =
  \int[fmeas_mu ν]_(y in [set: ar_carrier Ar Y])
    \d_(ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y) (x, y)) U.
  by move=> x; exact: icone_integral_dirac_lax_E.
under eq_integral => x _ do rewrite rwInnerX.
(* Step 3: Both sides are scalar integrals; swap via fubini_tonelli on
   the joint dirac F(x, y) = \d_{ar_prod_cast (x, y)} U. *)
pose F (p : ar_carrier Ar X * ar_carrier Ar Y) : \bar R :=
  \d_(ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y) p) U.
have F_meas : measurable_fun setT F.
  apply: (measurableT_comp (f := fun p => \d_p U)).
  - exact: measurable_fun_dirac.
  - exact: (ar_prod_cast_meas Ar X Y).
have F_ge0 p : 0 <= F p by rewrite /F; exact: measure_ge0.
(* Bridge to fmeas_fin_view to use fubini_tonelli (which wants
   sigma_finite measures). *)
have outerEqµ (g : ar_carrier Ar X -> \bar R) :
  \int[fmeas_fin_view µ]_(x in [set: ar_carrier Ar X]) g x =
  \int[fmeas_mu µ]_(x in [set: ar_carrier Ar X]) g x.
  by apply: eq_measure_integral => V mV _; exact: fmeas_fin_viewE.
have outerEqν (g : ar_carrier Ar Y -> \bar R) :
  \int[fmeas_fin_view ν]_(y in [set: ar_carrier Ar Y]) g y =
  \int[fmeas_mu ν]_(y in [set: ar_carrier Ar Y]) g y.
  by apply: eq_measure_integral => V mV _; exact: fmeas_fin_viewE.
rewrite -outerEqµ -outerEqν.
under eq_integral => x _ do rewrite -outerEqν.
under [in RHS]eq_integral => y _ do rewrite -outerEqµ.
exact: (fubini_tonelli F F_meas F_ge0).
Qed.

(** *** The headline commutativity — Lemma B "FMeas-Kleisli Fubini".

    The two iteration orders of the integration agree.  This is the
    commutativity of the FMeas-tensor-Kleisli monad on the lax-monoidal
    pushforward [fmeas_lax_pre µ ν].  Pure corollary of
    [fmeas_lax_pre_iterated] (X-then-Y) and [fmeas_lax_pre_iterated_Y]
    (Y-then-X). *)
Lemma fmeas_lax_pre_fubini
    (µ : fmeas R (ar_carrier Ar X)) (ν : fmeas R (ar_carrier Ar Y))
    (U : set (ar_carrier Ar (ar_prod Ar X Y))) :
  measurable U ->
  \int[fmeas_mu µ]_(x in [set: ar_carrier Ar X])
    fmeas_mu (icone_integral (dirac_lax_fun x)
                             (dirac_lax_is_path x) ν) U =
  \int[fmeas_mu ν]_(y in [set: ar_carrier Ar Y])
    fmeas_mu (icone_integral (fun x => dirac_lax_fun x y)
                             (dirac_lax_fun_swap_is_path y) µ) U.
Proof.
move=> mU.
rewrite -(fmeas_lax_pre_iterated µ ν U mU).
exact: fmeas_lax_pre_iterated_Y.
Qed.

End FmeasLaxIteratedSwap.

Arguments dirac_lax_fun_swap_is_path {R Ar X Y} y.
Arguments icone_integral_dirac_lax_swap_E {R Ar X Y} y µ U _.
Arguments fmeas_lax_pre_iterated_Y {R Ar X Y} µ ν U _.
Arguments fmeas_lax_pre_fubini {R Ar X Y} µ ν U _.

(** ** [kbind_ext] / [fmeas_lax] commutativity (pre-image form)

    The headline "FMeas-Kleisli Fubini through a pushforward [φ]" identity.

    For [µ : FMeas X], [ν : FMeas Y] and a measurable
    [φ : ar_carrier (X × Y) -> ar_carrier Z], the value of
    [fmeas_lax_pre µ ν] on the pre-image [φ ⁻¹ U] of a measurable [U]
    is the iterated integral

      [∫µ ∫ν δ_(φ (ar_prod_cast (x, y))) U.]

    Mathematical content.  This is the COMMUTATIVITY of the
    [FMeas]-Kleisli monad on the tensor: the doubled-bind composition

      [let m := sample µ in let b := sample ν in η (φ (m, b))]

    coincides with the single-bind against the joint measure
    [fmeas_lax_pre µ ν] then [η ∘ φ].  Symbolically,

      [bind (sample µ) (λ m. bind (sample ν) (λ b. return (φ (m, b))))
       = bind (sample (fmeas_lax µ ν)) (λ p. return (φ p))].

    Stated set-theoretically — without the categorical [kbind_ext]
    packaging that would require traversing the [EM(!)]-coalgebra
    cartesian-η machinery — this is the present lemma applied at
    every measurable [U ⊆ Z].  The downstream [examples.v] caller
    converts the set-level identity into the headline pushforward
    form for [ex_random_linear] via [add_lift_dirac] /
    [mul_lift_dirac] (the Dirac evaluation laws for [add_lift] /
    [mul_lift]) applied to the iterated form.

    Scope / honesty caveats.
    - The two factors [µ] and [ν] are NOT assumed to be equal; the
      lemma holds for arbitrary independent finite measures.
    - [φ] is an arbitrary measurable function on the propositional
      product carrier [ar_carrier (ar_prod X Y)], NOT an [ar_hom]
      (which would add a structure-preserving wrapper but no extra
      content). The cartesian-vs-propositional product cast is
      mediated by [ar_prod_cast] inside the iterated integrand.
    - The statement is at the [fmeas_mu] level rather than the
      Kleisli-arrow level: it is the load-bearing computational
      content used by [add_lift] / [mul_lift] downstream, but does
      NOT require navigating the [EM(!)]-coalgebra cartesian-η gap
      ([em_pair_mor (em_proj1, em_proj2) = id]) that blocks the
      generic [kbind_ext] reformulation. *)

Section FmeasLaxPreimage.
Local Open Scope ereal_scope.
Variables (R : realType) (Ar : MeasSubcat R).
Variables X Y : ar_obj Ar.

Lemma fmeas_lax_pre_preimage
    (Z : ar_obj Ar)
    (φ : ar_carrier Ar (ar_prod Ar X Y) -> ar_carrier Ar Z)
    (Hφ_meas : measurable_fun
       [set: ar_carrier Ar (ar_prod Ar X Y)] φ)
    (µ : fmeas R (ar_carrier Ar X)) (ν : fmeas R (ar_carrier Ar Y))
    (U : set (ar_carrier Ar Z)) :
  measurable U ->
  fmeas_mu (fmeas_lax_pre µ ν) (φ @^-1` U) =
    \int[fmeas_mu µ]_(x in [set: ar_carrier Ar X])
      \int[fmeas_mu ν]_(y in [set: ar_carrier Ar Y])
        \d_(φ (ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y) (x, y))) U.
Proof.
move=> mU.
have mPreU : measurable (φ @^-1` U).
  by rewrite -[X in measurable X]setTI; exact: Hφ_meas.
(* Step 1: apply [fmeas_lax_pre_iterated] on the pre-image [φ ⁻¹ U]. *)
rewrite (fmeas_lax_pre_iterated µ ν _ mPreU).
(* Step 2: reduce each inner integrand via [icone_integral_dirac_lax_E],
   then push the [ar_prod_cast]-then-[φ] composition through the
   Dirac. *)
apply: eq_integral => x _.
rewrite (icone_integral_dirac_lax_E x ν _ mPreU).
apply: eq_integral => y _.
(* [\d_(ar_prod_cast (x, y)) (φ ⁻¹ U) = \d_(φ (ar_prod_cast (x, y))) U]:
   both sides reduce by [diracE] to [(... ∈ U)%:R%:E] applied to the
   same membership, since [a ∈ φ ⁻¹ U] iff [φ a ∈ U] by definition
   of [@^-1`]. *)
rewrite !diracE.
by congr ((_)%:R)%:E; rewrite [LHS]propeqE; split=> /[!inE].
Qed.

End FmeasLaxPreimage.

Arguments fmeas_lax_pre_preimage {R Ar X Y Z} φ Hφ_meas µ ν U _.

(** *** [fmeas_lax_E] — pointwise computation on the pure tensor

    [fmeas_lax X Y (µ ⊗p ν) = fmeas_lax_pre µ ν].

    Proved by chaining
    - [tensor_curryEp]+[tensor_uncurryK]: the SAFT defining
      equation, reducing the LHS to
      [linhom_fun (linhom_fun fmeas_lax_outer µ) ν];
    - the [int_to_linhom] unfolding (the outer Pettis integral);
    - paper Lemma 5.4 [linhom_int_eval] (evaluation commutes with
      [linhom_car] integrals);
    - the [int_to_linhom] unfolding for the inner integral;
    - the Tonelli identity [fmeas_lax_pre_iterated].
    The two icone-integrals are compared on every measurable [U]
    via [fmeas_eq], using the Pettis equation and a finiteness
    argument bounded by [‖ν‖]. *)

Section FmeasLaxE.
Local Open Scope ereal_scope.
Variables (R : realType) (Ar : MeasSubcat R).
Variables X Y : ar_obj Ar.

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

Lemma fmeas_lax_E
    (µ : fmeas R (ar_carrier Ar X))
    (ν : fmeas R (ar_carrier Ar Y)) :
  Lfun (fmeas_lax X Y)
    (ptensor (B := fmeas R (ar_carrier Ar X))
             (C := fmeas R (ar_carrier Ar Y)) µ ν) =
  fmeas_lax_pre µ ν.
Proof.
(* Step 1: reduce LHS to [linhom_fun (linhom_fun fmeas_lax_outer µ) ν]. *)
rewrite /fmeas_lax.
have HtucK := tensor_uncurryK (fmeas_lax_outer_icones X Y).
have HtcEp := tensor_curryEp (tensor_uncurry (fmeas_lax_outer_icones X Y))
                             µ ν.
rewrite -HtcEp HtucK.
rewrite /fmeas_lax_outer_icones.
rewrite (linhom_iconesE (fmeas_lax_outer X Y) _ µ).
rewrite /fmeas_lax_outer.
have rwOuter : linhom_fun (int_to_linhom (fmeas_lax_outer_path X Y)) µ =
  icone_integral
    (path_fun (fmeas_lax_outer_path X Y))
    (path_is_path (fmeas_lax_outer_path X Y)) µ.
  by [].
rewrite rwOuter.
(* Step 2: pull evaluation at ν inside via [linhom_int_eval]. *)
rewrite (linhom_int_eval (path_is_path (fmeas_lax_outer_path X Y)) µ ν).
(* Step 3: compare both fmeas on every measurable U. *)
apply: fmeas_eq => U mU.
(* RHS: fmeas_lax_pre µ ν U = \int[µ]_x fmeas_mu (icone_integral (dirac_lax x) _ ν) U
   by fmeas_lax_pre_iterated. *)
rewrite (fmeas_lax_pre_iterated µ ν U mU).
(* The two integrands at x agree pointwise:
   [linhom_fun (path_fun outer_path x) ν = icone_integral (dirac_lax_fun x) _ ν]
   because [path_fun outer_path x = fmeas_lax_pre_at_dirac x =
   int_to_linhom (dirac_lax x)] and [linhom_fun (int_to_linhom β) µ =
   icone_integral β _ µ]. *)
have Hmeas_outer :
    is_measurable_path (fun r : ar_carrier Ar X =>
      linhom_fun (path_fun (fmeas_lax_outer_path X Y) r) ν).
  exact: (linhom_int_section_meas
    (path_is_path (fmeas_lax_outer_path X Y)) ν).
have mMU : mcone_M (Ar:=Ar) (ar_zero Ar)
              (fmeas_eU (R:=R) (X:=ar_carrier Ar (ar_prod Ar X Y))
                        (Ar:=Ar) (ar_zero Ar) mU).
  by exists U, mU.
have HP_outer := icone_integralP _ Hmeas_outer µ _ mMU (ar_zero_pt Ar).
have Hfin :
    fmeas_mu (icone_integral
      (fun r : ar_carrier Ar X => linhom_fun (fmeas_lax_outer_path X Y r) ν)
      Hmeas_outer µ) U \is a fin_num.
  exact: fmeas_fin.
have Hintfin :
    \int[fmeas_mu µ]_(x in [set: ar_carrier Ar X])
      fmeas_mu (icone_integral (dirac_lax_fun x) (dirac_lax_is_path x) ν) U
    \is a fin_num.
  have inner_meas_setT : measurable_fun setT
      (fun x : ar_carrier Ar X =>
        fmeas_mu (icone_integral (dirac_lax_fun x) (dirac_lax_is_path x) ν) U).
    apply: (eq_measurable_fun
      (fun x : ar_carrier Ar X =>
        \int[fmeas_mu ν]_(y in [set: ar_carrier Ar Y])
          \d_(ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y) (x, y)) U)).
      by move=> x _; rewrite (icone_integral_dirac_lax_E x ν U mU).
    pose F (q : ar_carrier Ar X * ar_carrier Ar Y) : \bar R :=
      \d_(ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y) q) U.
    have meas_d : measurable_fun setT
      (fun p : ar_carrier Ar (ar_prod Ar X Y) => \d_p U : \bar R).
      exact: measurable_fun_dirac.
    have measc : measurable_fun setT
      (ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y))
      by exact: (ar_prod_cast_meas Ar X Y).
    have F_meas : measurable_fun setT F.
      exact: (measurableT_comp meas_d measc).
    have F_ge0 q : 0 <= F q by exact: measure_ge0.
    have -> :
      (fun x : ar_carrier Ar X =>
       \int[fmeas_mu ν]_(y in [set: ar_carrier Ar Y]) F (x, y)) =
      fubini_F (fmeas_fin_view ν) F.
      apply: funext => x.
      rewrite /fubini_F.
      by apply: eq_measure_integral => V mV _; exact/esym/fmeas_fin_viewE.
    apply: (@measurable_fun_fubini_tonelli_F _ _ _ _ _
              (fmeas_fin_view ν) F).
    - exact: F_meas.
    - exact: F_ge0.
  have intle :
    \int[fmeas_mu µ]_(x in [set: ar_carrier Ar X])
       fmeas_mu (icone_integral (dirac_lax_fun x) (dirac_lax_is_path x) ν) U <=
    \int[fmeas_mu µ]_(x in [set: ar_carrier Ar X])
       fmeas_mu ν [set: ar_carrier Ar Y].
    apply: ge0_le_integral.
    - exact: measurableT.
    - by move=> x _; exact: measure_ge0.
    - exact: inner_meas_setT.
    - exact: measurable_cst.
    - move=> x _.
      (* (icone_integral (dirac_lax_fun x) _ ν)(setT) <=
         (icone_integral (dirac_lax_fun x) _ ν) [setT] = ν(setT). *)
      rewrite (icone_integral_dirac_lax_E x ν U mU).
      apply: (@le_trans _ _
        (\int[fmeas_mu ν]_(y in [set: ar_carrier Ar Y]) (1 : \bar R))); last first.
        by rewrite integral_cst// mul1e.
      apply: ge0_le_integral.
      + exact: measurableT.
      + by move=> y _; exact: measure_ge0.
      + apply: (eq_measurable_fun
          (fun y : ar_carrier Ar Y =>
            \d_(ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y) (x, y)) U)).
          by move=> y _.
        have meas_d : measurable_fun setT
          (fun p : ar_carrier Ar (ar_prod Ar X Y) => \d_p U : \bar R).
          exact: measurable_fun_dirac.
        have measc : measurable_fun setT
          (ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y))
          by exact: (ar_prod_cast_meas Ar X Y).
        have meas_pair : measurable_fun setT
          (fun y : ar_carrier Ar Y =>
             ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y) (x, y)).
          apply: (measurableT_comp measc).
          by apply: measurable_fun_pair;
            [exact: measurable_cst|exact: @measurable_id].
        exact: (measurableT_comp meas_d meas_pair).
      + exact: measurable_cst.
      + move=> y _.
        apply: (@le_trans _ _ (\d_(ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y)
                                              (x, y)) setT)).
          by apply: le_measure => //; rewrite inE.
        by rewrite diracT.
  rewrite ge0_fin_numE//; last
    by apply: integral_ge0 => x _; exact: measure_ge0.
  apply: le_lt_trans intle _.
  rewrite integral_cst//.
  have HfinNu : fmeas_mu ν [set: ar_carrier Ar Y] \is a fin_num
    by exact: fmeas_setT_fin.
  have HfinMu : fmeas_mu µ [set: ar_carrier Ar X] \is a fin_num
    by exact: fmeas_setT_fin.
  rewrite ltey_eq fin_numM//.
have HPE := HP_outer.
rewrite /fmeas_eU /eU_fun /= in HPE.
have HrwIrr : Hmeas_outer =
  linhom_int_section_meas (path_is_path (fmeas_lax_outer_path X Y)) ν.
  exact: Prop_irrelevance.
rewrite -HrwIrr.
rewrite -(fineK Hfin) -(fineK Hintfin); congr (_%:E).
rewrite HPE.
congr fine.
apply: eq_integral => x _.
have Hfinx :
  fmeas_mu (icone_integral (dirac_lax_fun x) (dirac_lax_is_path x) ν) U
    \is a fin_num.
  exact: fmeas_fin.
rewrite -[in RHS](fineK Hfinx).
have rwInner :
  linhom_fun (fmeas_lax_pre_at_dirac x) ν =
  icone_integral (dirac_lax_fun x) (dirac_lax_is_path x) ν.
  by [].
by rewrite rwInner.
Qed.

(** *** [fmeas_lax_dirac] — the load-bearing Dirac identity at ICones

    [fmeas_lax (δ_x ⊗p δ_y) = δ_{ar_prod_cast (x, y)}].
    Combines [fmeas_lax_E] with [fmeas_lax_pre_dirac]. *)
Lemma fmeas_lax_dirac (x : ar_carrier Ar X) (y : ar_carrier Ar Y) :
  Lfun (fmeas_lax X Y)
    (ptensor (B := fmeas R (ar_carrier Ar X))
             (C := fmeas R (ar_carrier Ar Y)) (dirac_fmeas x) (dirac_fmeas y)) =
  dirac_fmeas (X := ar_prod Ar X Y)
              (ar_prod_cast (R:=R) (Ar:=Ar) (X:=X) (Y:=Y) (x, y)).
Proof.
rewrite (fmeas_lax_E (dirac_fmeas x) (dirac_fmeas y)).
exact: fmeas_lax_pre_dirac.
Qed.

End FmeasLaxE.

Arguments fmeas_lax_E {R Ar X Y} µ ν.
Arguments fmeas_lax_dirac {R Ar X Y} x y.
