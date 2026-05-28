(** * Phase 1 — A lax monoidal map for [FMeas]: the product-measure layer

    Paper reference: §9, the symmetric monoidal structure of [FMeas].

    Mathematical content.  For [X, Y : ar_obj Ar], the product measure
    [µ × ν] defines a candidate lax monoidal map

      [fmeas_lax_pre : FMeas X → FMeas Y → FMeas (ar_prod X Y),]
      [fmeas_lax_pre µ ν = pushforward of (µ ×_meas ν) along ar_prod_cast.]

    The carrier of [fmeas_prod µ ν] is the *cartesian* product
    [(ar_carrier X * ar_carrier Y)%type]; [ar_prod_cast] is the
    propositional carrier cast to [ar_carrier (ar_prod X Y)].

    Coverage in this file.

    - [fmeas_lax_pre µ ν : fmeas R (ar_carrier Ar (ar_prod Ar X Y))]
      — the pushforward of the cartesian-product fmeas along
      [ar_prod_cast], canonicalised to vanish off the σ-algebra.
    - [fmeas_lax_preE] — agreement on measurable [U] with the raw
      pushforward equation
      [(fmeas_lax_pre µ ν) U = (µ ×_meas ν) (ar_prod_cast @^-1` U)].
    - [fmeas_lax_pre_setT] / [fmeas_lax_pre_normE] — the total-mass
      product formula [(fmeas_lax_pre µ ν)(setT) = µ(setT)·ν(setT)] and
      the norm identity [‖fmeas_lax_pre µ ν‖ = ‖µ‖·‖ν‖].
    - [fmeas_lax_pre_dirac] — the Dirac identity
      [fmeas_lax_pre (dirac_fmeas x) (dirac_fmeas y) =
         dirac_fmeas (ar_prod_cast (x, y))].
      This is the load-bearing computational content used in
      [theories/programs/ppl.v] to reduce arithmetic expressions on
      Diracs.

    Scope of Phase 1.  Wrapping [fmeas_lax_pre] into a full
    [icones_hom Ar (tensor Ar (FMeas X) (FMeas Y)) (FMeas (ar_prod X Y))]
    requires the bilinear analogue of paper Thm 6.1, which is the
    same path-preservation-of-[int_to_linhom]-in-the-cone-variable
    step deferred in [theories/homs/bilin.v] (file header, item
    "Still deferred / follow-up"). The function-level
    infrastructure delivered here is the prerequisite; lifting it
    to the tensor [⊗] is a second piece of genuine missing
    infrastructure (the "lax monoidal map as an [icones_hom]"
    obligation), to be addressed in a follow-up that revisits the
    deferred bilin.v item. *)

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
From mathcomp.analysis Require Import lebesgue_integral_fubini.

Require Import Icones.prelude.classical_extra.
Require Import Icones.prelude.nonneg_extra.
Require Import Icones.prelude.ereal_extra.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.icones.pettis.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_integral.
Require Import Icones.icones.examples_icone.
Require Import Icones.icones.fubini.
Require Import Icones.homs.linhom.
Require Import Icones.homs.bilin.

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

(** ** Dirac identity — load-bearing for Phase 2

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

