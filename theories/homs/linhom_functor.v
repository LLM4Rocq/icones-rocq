(**md**************************************************************************)
(* # The linear hom functor on morphisms — Paper §5.3, Prop 5.8              *)
(*                                                                            *)
(*   This file packages the object map [linhom_map_fun h g : (C1 ⊸ D1) →     *)
(*   (C2 ⊸ D2)], [f ↦ g ∘ f ∘ h], as a morphism                              *)
(*   [icones_hom Ar (C1 ⊸ D1) (C2 ⊸ D2)] (Paper Prop 5.8), closing the        *)
(*   deferral noted at [linhom.v:5185].  The crux — measurable-path           *)
(*   preservation *in [f]* — is discharged using the reusable test-pullback   *)
(*   infrastructure of [Icones.mcones.test_pullback]: pulling a [D2]-test     *)
(*   back along [g] (resp. a [C2]-path forward along [h]) lands inside the    *)
(*   measurability structure of [D1] (resp. [C1]), exactly as in §5.3.        *)
(*                                                                            *)
(*   Deliverables:                                                            *)
(*   - [linhom_map_cones h g] : [cones_hom (C1 ⊸ D1) (C2 ⊸ D2)] — linear,    *)
(*     ω-continuous, norm-decreasing in [f].  ω-continuity uses the           *)
(*     test-separation (Mssep) of [D2] together with the test-of-sup          *)
(*     identity [linhom_sup_fun_test_sup] and [test_pullback_cont].           *)
(*   - [linhom_map_mcones h g] : [mcones_hom Ar (C1 ⊸ D1) (C2 ⊸ D2)] —        *)
(*     measurable-path preservation, via [test_pullback_meas_bivar].          *)
(*   - [linhom_map_icones h g] : [icones_hom Ar (C1 ⊸ D1) (C2 ⊸ D2)] —        *)
(*     integral preservation, via [icones_hom_pres_int]/[linhom_pres_int]     *)
(*     and uniqueness of the path integral (the §5.3 integral computation).   *)
(*   - One-sided actions [linhom_post_icones g] ([C ⊸ g]) and                 *)
(*     [linhom_pre_icones h] ([h ⊸ D]) as the [icones_id]-specialisations.    *)
(*   - Morphism-level functoriality [linhom_map_icones_id] /                  *)
(*     [linhom_map_icones_comp] (Prop 5.8 as equalities in [ICones]).         *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.

Require Import Icones.prelude.classical_extra.
Require Import Icones.prelude.nonneg_extra.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.cone_cat.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.mcones.path.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.mcones.test_pullback.
Require Import Icones.icones.pettis.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_integral.
Require Import Icones.icones.examples_icone.
Require Import Icones.icones.fubini.
Require Import Icones.icones.icone_cat.
Require Import Icones.homs.linhom.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** Auxiliary: a nonnegative scalar commutes with [sup] *)

Section SupScale.
Variable R : realType.

Lemma sup_scaleM (c : R) (A : set R) :
  0 <= c -> A !=set0 -> has_ubound A ->
  c * sup A = sup [set c * a | a in A].
Proof.
move=> cge0 [a0 Ha0] [M HM].
have hsA : has_sup A by split; [exists a0|exists M].
have [c0|cpos] := eqVneq c 0.
  rewrite c0 mul0r.
  have -> : [set 0 * a | a in A] = [set 0].
    apply/seteqP; split.
      by move=> z [a _ <-]; rewrite mul0r.
    by move=> z ->; exists a0 => //; rewrite mul0r.
  by rewrite sup1.
have cposR : 0 < c by rewrite lt_def cpos cge0.
have hsB : has_sup [set c * a | a in A].
  split; first by exists (c * a0), a0.
  by exists (c * M) => _ [a Ha <-]; rewrite ler_pM2l //; exact: HM.
apply: le_anti; apply/andP; split.
- rewrite -ler_pdivlMl //.
  apply: ge_sup; first by exists a0.
  move=> a Ha; rewrite ler_pdivlMl //.
  by move/ubP : (sup_upper_bound hsB); apply; exists a.
- apply: ge_sup; first by exists (c * a0), a0.
  move=> _ [a Ha <-]; rewrite ler_pM2l //.
  by move/ubP : (sup_upper_bound hsA); apply.
Qed.

End SupScale.

Arguments sup_scaleM {R} c A.

(** ** The action of [⊸] on morphisms — Paper §5.3, Prop 5.8 *)

Section LinhomMapHom.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (C1 C2 D1 D2 : ICone.type Ar).
Variable h : icones_hom Ar C2 C1.
Variable g : icones_hom Ar D1 D2.

Local Notation Λ := (linhom_map_fun h g).
Local Notation gf := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones g))).
Local Notation hf := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

(** Pointwise: [(Λ f) x = g (f (h x))]. *)
Lemma linhom_mapE (f : linhom_car Ar C1 D1) (x : C2) :
  linhom_fun (Λ f) x = gf (linhom_fun f (hf x)).
Proof. exact: linhom_map_funE. Qed.

(** Linearity of [Λ] as a map between the linhom cones. *)
Lemma linhom_map_linear : is_linear Λ.
Proof.
have [Hg0 HgD HgZ] := cones_hom_linear (mcones_hom_cones (icones_hom_mcones g)).
split.
- apply: linhom_eq => x; rewrite linhom_mapE /=.
  by rewrite (_ : linhom_fun (linhom_zero C1 D1) (hf x) = precone_zero)// Hg0.
- move=> f1 f2; apply: linhom_eq => x.
  by rewrite linhom_mapE /= HgD.
- move=> r f; apply: linhom_eq => x.
  by rewrite linhom_mapE /= HgZ.
Qed.

(** [Λ] is norm-decreasing: [‖Λ f‖ ≤ ‖f‖].  Pointwise
    [‖g(f(h x))‖ ≤ ‖f(h x)‖ ≤ ‖f‖ ‖h x‖ ≤ ‖f‖ ‖x‖], then the
    operator-norm sup is the least upper bound. *)
Lemma linhom_map_norm_le1 (f : linhom_car Ar C1 D1) :
  cone_norm (Λ f) <= cone_norm f.
Proof.
rewrite [cone_norm (Λ f)]/= [cone_norm f]/=.
apply: linhom_norm_sup_lub => x Hx.
rewrite linhom_mapE.
apply: le_trans
  (cones_hom_norm_le1 (mcones_hom_cones (icones_hom_mcones g)) _) _.
apply: le_trans (linhom_norm_apply_le (lexx _) (hf x)) _.
rewrite -[X in _ <= X]mulr1.
apply: ler_wpM2l; first exact: linhom_norm_ge0.
apply: le_trans
  (cones_hom_norm_le1 (mcones_hom_cones (icones_hom_mcones h)) _) _.
exact: Hx.
Qed.

(** ω-continuity of [Λ] as a map between the linhom cones.

    By extensionality ([linhom_eq]) and test-separation (Mssep) of
    [D2], it suffices to check, for every arity-0 test [m₂ ∈ M^{D2}_0]
    and every [x : C2], that
      [m₂(0, (Λ (sup U)) x) = m₂(0, (sup (Λ ∘ U)) x)].
    The LHS expands to [m₂(0, g((sup U)(h x)))]; pushing the cone-sup
    through [g] (test-pullback continuity) turns it into a real
    supremum [sup_n m₂(0, g((U n)(h x)))].  The RHS expands via
    [linhom_sup_fun_test_sup] to the same real supremum. *)
Lemma linhom_map_continuous : is_omega_continuous Λ.
Proof.
move=> U Uch Uub1 ΛUch ΛUub1.
apply: linhom_eq => x.
apply: mcone_M_sep => m2 m2M.
rewrite linhom_mapE.
rewrite (linhom_sup_fun_test_sup ΛUch ΛUub1 m2 (ar_zero_pt Ar) x).
(* Scale [h x] into the unit ball: [S := ‖h x‖ + 1], [y' := S⁻¹ • h x]. *)
have S_ge0 : 0 <= cnorm (hf x) + 1 by exact: ltW (cnorm_succ_pos _).
pose S : {nonneg R} := NngNum S_ge0.
have Spos : 0 < S%:num by exact: cnorm_succ_pos.
have Hxs : cnorm (precone_scale (nng_inv S) (hf x)) <= 1.
  rewrite cone_normh /=.
  by rewrite mulrC ler_pdivrMr // mul1r
             -[X in X <= _]addr0 lerD2l ler01.
have Hlin_sup : linhom_fun (cone_sup_ball U Uch Uub1) (hf x) =
    linhom_sup_fun Uch Uub1 (hf x) by [].
rewrite Hlin_sup (linhom_sup_fun_at_scale Uch Uub1 Spos Hxs).
rewrite /linhom_sup_unit.
have [_ _ HgZ] :=
  cones_hom_linear (mcones_hom_cones (icones_hom_mcones g)).
rewrite HgZ test_linZ.
rewrite (test_pullback_cont (mcones_hom_cones (icones_hom_mcones g))
           m2 (ar_zero_pt Ar)).
(* Identify the right-hand chain with the [g ∘ U ∘ h] chain. *)
have RHSeq :
    [set m2 (ar_zero_pt Ar) (linhom_fun (Λ (U n)) x) | n in [set: nat]] =
    [set m2 (ar_zero_pt Ar) (gf (linhom_fun (U n) (hf x))) | n in [set: nat]].
  apply: eq_set => z; split=> -[n _ <-]; exists n => //;
    by rewrite linhom_mapE.
rewrite RHSeq.
(* Each left-hand element is [S⁻¹ •] the right-hand element. *)
have innerE n :
    m2 (ar_zero_pt Ar) (gf (linhom_fun (U n) (nng_inv S *: hf x)%PC)) =
    (nng_inv S)%:num * m2 (ar_zero_pt Ar) (gf (linhom_fun (U n) (hf x))).
  have [_ _ HUZn] := linhom_pre_linear (linhom_pre_of (U n)).
  by rewrite /linhom_fun HUZn HgZ test_linZ.
(* Pull [S •] through the [sup] via [sup_scaleM]. *)
pose B : set R :=
  [set m2 (ar_zero_pt Ar) (gf (linhom_fun (U n) (hf x))) | n in [set: nat]].
have HB0 : B !=set0.
  by exists (m2 (ar_zero_pt Ar) (gf (linhom_fun (U 0%N) (hf x)))), 0%N.
have HBub : has_ubound B.
  exists (cnorm (hf x)) => _ [n _ <-].
  apply: le_trans (test_norm_le _ _ _) _.
  apply: le_trans
    (cones_hom_norm_le1 (mcones_hom_cones (icones_hom_mcones g)) _) _.
  apply: le_trans (linhom_norm_apply_le (Uub1 n) (hf x)) _.
  by rewrite mul1r.
have setE :
    [set m2 (ar_zero_pt Ar) (gf (linhom_fun (U i) (nng_inv S *: hf x)%PC))
       | i in [set: nat]] =
    [set (nng_inv S)%:num * b | b in B].
  apply/seteqP; split=> z.
    by move=> [n _ <-]; exists (m2 (ar_zero_pt Ar)
      (gf (linhom_fun (U n) (hf x)))); [exists n|rewrite -innerE].
  by move=> [_ [n _ <-] <-]; exists n; rewrite // innerE.
rewrite setE.
rewrite -(sup_scaleM (nng_inv S)%:num B) //.
rewrite mulrA.
have -> : S%:num * (nng_inv S)%:num = 1.
  by rewrite /= mulfV// gt_eqF.
by rewrite mul1r.
Qed.

(** Paper Prop 5.8: [Λ] packaged as a [cones_hom] between the linhom
    cones. *)
Definition linhom_map_cones : cones_hom (linhom_car Ar C1 D1)
                                        (linhom_car Ar C2 D2) :=
  ConesHom Λ linhom_map_linear linhom_map_continuous linhom_map_norm_le1.

(** Paper Prop 5.8 (measurability) — the test-pullback core.

    Given a measurable path [Φ] of [C1 ⊸ D1], the composite path
    [r ↦ Λ (Φ r)] is a measurable path of [C2 ⊸ D2].  By the linhom
    test family it suffices, for [γ₂ ∈ Path(Z, C2)] (‖γ₂‖ ≤ 1) and
    [m₂ ∈ M^{D2}_Z], to show
      [(s, r) ↦ m₂(s, g((Φ r)(h(γ₂ s))))]
    is measurable on [Z × W].  This is §5.3's [φ]: the bivariate path
    [δ(s, r) := (Φ r)(h(γ₂ s))] is measurable in [D1] (it is the
    flattening of [Φ ∘ - ∘ (h ∘ γ₂)], obtained by testing [Φ] against
    [linhom_test (h ∘ γ₂)]), and pulling [m₂] back along [g] keeps it
    measurable ([test_pullback_meas_bivar]). *)
Lemma linhom_map_pres_path
    (W : ar_obj Ar) (Φ : ar_carrier Ar W -> linhom_car Ar C1 D1) :
  is_measurable_path Φ ->
  is_measurable_path (fun r => Λ (Φ r)).
Proof.
move=> HΦ.
have [[MΦ HMΦ] HΦm] := HΦ.
have MΦ_ge0 : 0 <= MΦ.
  by apply: le_trans (HMΦ (ar_point Ar W)); exact: cone_norm_ge0.
split.
  exists MΦ => r.
  by exact: (le_trans (linhom_map_norm_le1 (Φ r)) (HMΦ r)).
move=> Z p [γ2 [γ2ub [m2 [m2M ->]]]].
(* The pulled-forward unit-ball path of [C1]: [hγ2 := h ∘ γ2]. *)
pose hγ2 : ar_carrier Ar Z -> C1 := fun s => hf (path_fun γ2 s).
have Hhγ2 : is_measurable_path hγ2.
  exact: (mcones_hom_pres_path (icones_hom_mcones h) Z _ (path_is_path γ2)).
pose hγ2_path : path_car Ar Z C1 := MkPath Hhγ2.
have hγ2_ub : cnorm hγ2_path <= 1.
  rewrite /cone_norm /=.
  apply: ge_sup; first exact: path_normset_nonempty.
  move=> _ [s ->] /=.
  rewrite /hγ2 /=.
  apply: le_trans
    (cones_hom_norm_le1 (mcones_hom_cones (icones_hom_mcones h)) _) _.
  by apply: le_trans (path_norm_ub γ2 s) _; exact: γ2ub.
(* The bivariate [D1]-path [δ(s, r) := (Φ r)(hγ2 s)] at arity
   [ar_prod Z W]; §5.3's [fl(δ1)]. *)
pose δar : ar_carrier Ar (ar_prod Ar Z W) -> D1 :=
  fun q => linhom_fun (Φ (ar_prod_snd Z W q)) (hγ2 (ar_prod_fst Z W q)).
have Hδ : is_measurable_path δar.
  split.
    exists MΦ => q; rewrite /δar.
    apply: le_trans (linhom_norm_apply_le (HMΦ _) (hγ2 _)) _.
    rewrite -[X in _ <= X]mulr1 ler_wpM2l //.
    by apply: le_trans hγ2_ub; exact: (path_norm_ub hγ2_path _).
  (* Joint test-measurability of [δ] against a [C1]-test [m'] of [D1]
     by testing [Φ] against [linhom_test (hγ2 ∘ ar_prod_snd) (m' ∘
     ar_prod_fst)] at the product arity [ar_prod Y' Z]. *)
  move=> Y' m' m'M.
  pose ar_sndYZ : ar_hom Ar (ar_prod Ar Y' Z) Z := ar_prod_snd Y' Z.
  pose ar_fstYZ : ar_hom Ar (ar_prod Ar Y' Z) Y' := ar_prod_fst Y' Z.
  have HhγYZ : is_measurable_path (fun q => hγ2 (ar_sndYZ q)).
    exact: (reindex_path_measurable ar_sndYZ Hhγ2).
  pose hγYZ_path : path_car Ar (ar_prod Ar Y' Z) C1 := MkPath HhγYZ.
  have hγYZ_ub : cnorm hγYZ_path <= 1.
    rewrite /cone_norm /=.
    apply: ge_sup; first exact: path_normset_nonempty.
    move=> _ [q ->] /=.
    by apply: le_trans hγ2_ub; exact: (path_norm_ub hγ2_path (ar_sndYZ q)).
  pose m'r : test_of Ar (ar_prod Ar Y' Z) D1 := test_reindex ar_fstYZ m'.
  have m'rM : mcone_M (ar_prod Ar Y' Z) m'r by exact: mcone_M_comp.
  have HΦtest := HΦm (ar_prod Ar Y' Z)
    (linhom_test hγYZ_path hγYZ_ub m'r m'rM)
    (ex_intro _ hγYZ_path (ex_intro _ hγYZ_ub
       (ex_intro _ m'r (ex_intro _ m'rM (erefl _))))).
  (* Fold [(z, (s, w))] to [((z, s), w)] via [ar_prod_cast]. *)
  pose ψ (p0 : (ar_carrier Ar Y' * ar_carrier Ar (ar_prod Ar Z W))%type) :
      (ar_carrier Ar (ar_prod Ar Y' Z) * ar_carrier Ar W)%type :=
    (ar_prod_cast (p0.1, ar_prod_fst Z W p0.2), ar_prod_snd Z W p0.2).
  have ψ_meas : measurable_fun
      [set: (ar_carrier Ar Y' * ar_carrier Ar (ar_prod Ar Z W))%type] ψ.
    apply: measurable_fun_pair.
    - have meas_pair : measurable_fun setT
          (fun p0 : ar_carrier Ar Y' * ar_carrier Ar (ar_prod Ar Z W) =>
            (p0.1, ar_prod_fst Z W p0.2)).
        apply: measurable_fun_pair; first exact: measurable_fst.
        by apply: (measurableT_comp (f := ar_prod_fst Z W));
          [exact: measurable_funP|exact: measurable_snd].
      exact: (measurableT_comp (ar_prod_cast_meas Ar Y' Z) meas_pair).
    - by apply: (measurableT_comp (f := ar_prod_snd Z W));
        [exact: measurable_funP|exact: measurable_snd].
  apply: (eq_measurable_fun
    (fun p0 => (fun q : ar_carrier Ar (ar_prod Ar Y' Z) * ar_carrier Ar W =>
        linhom_test hγYZ_path hγYZ_ub m'r m'rM q.1 (Φ q.2)) (ψ p0))).
    move=> p0 _ /=.
    rewrite /linhom_test /linhom_test_fun /= /δar /ψ /=.
    rewrite /m'r /test_reindex /test_reindex_fun /=.
    rewrite /ar_fstYZ /ar_prod_fst /ar_prod_fst_fun ar_prod_castK /=.
    rewrite /hγYZ_path /= /ar_sndYZ /ar_prod_snd /ar_prod_snd_fun
            ar_prod_castK /=.
    by [].
  exact: (measurableT_comp HΦtest ψ_meas).
(* Pull [m₂] back along [g] over the bivariate path [δ]. *)
have Hbase :=
  test_pullback_meas_bivar (mcones_hom_cones (icones_hom_mcones g)) m2M Hδ.
have castfst (pq : (ar_carrier Ar Z * ar_carrier Ar W)%type) :
    ar_prod_fst Z W (ar_prod_cast pq) = pq.1.
  by change ((ar_prod_uncast (ar_prod_cast pq)).1 = pq.1);
     rewrite ar_prod_castK.
have castsnd (pq : (ar_carrier Ar Z * ar_carrier Ar W)%type) :
    ar_prod_snd Z W (ar_prod_cast pq) = pq.2.
  by change ((ar_prod_uncast (ar_prod_cast pq)).2 = pq.2);
     rewrite ar_prod_castK.
apply: (eq_measurable_fun
  (fun pq => test_fun m2 pq.1 (gf (δar (ar_prod_cast pq))))).
  move=> pq _ /=.
  rewrite /linhom_test /linhom_test_fun /= linhom_mapE /δar.
  by rewrite castfst castsnd.
exact: Hbase.
Qed.

(** Paper Prop 5.8: [Λ] packaged as an [mcones_hom]. *)
Definition linhom_map_mcones : mcones_hom Ar (linhom_car Ar C1 D1)
                                           (linhom_car Ar C2 D2) :=
  MkMConesHom linhom_map_cones linhom_map_pres_path.

(** Paper Prop 5.8 (integral preservation in [f]) — §5.3's integral
    computation.  [Λ (∫ Φ dµ) = ∫ (Λ ∘ Φ) dµ] in [C2 ⊸ D2].  By
    uniqueness of the linhom path integral it suffices to show the LHS
    satisfies the linhom Pettis equation for [Λ ∘ Φ]; pointwise this
    reduces, via [g]'s integral preservation and [D2]'s Pettis spec, to
    the same iterated integral on both sides. *)
Lemma linhom_map_pres_int
    (W : ar_obj Ar) (Φ : ar_carrier Ar W -> linhom_car Ar C1 D1)
    (HΦ : is_measurable_path Φ)
    (µ : fmeas R (ar_carrier Ar W)) :
  cones_hom_fun (mcones_hom_cones linhom_map_mcones)
    (icone_integral Φ HΦ µ) =
  icone_integral
    (fun r => cones_hom_fun (mcones_hom_cones linhom_map_mcones) (Φ r))
    (mcones_hom_pres_path linhom_map_mcones W Φ HΦ) µ.
Proof.
apply: icone_integral_eqP.
move=> p pM s.
case: pM => γ2 [γ2ub [m2 [m2M ->]]].
rewrite /linhom_test /= /linhom_test_fun /=.
rewrite linhom_mapE.
have Hinteq : icone_integral Φ HΦ µ = linhom_int_car HΦ µ.
  by apply/esym; apply: icone_integral_eqP; exact: linhom_int_car_pettis.
rewrite Hinteq.
have HevE : linhom_fun (linhom_int_car HΦ µ) (hf (path_fun γ2 s)) =
  icone_integral (fun r => linhom_fun (Φ r) (hf (path_fun γ2 s)))
    (linhom_int_pt_meas HΦ (hf (path_fun γ2 s))) µ by [].
rewrite HevE.
have HgInt := icones_hom_pres_int g W
  (fun r => linhom_fun (Φ r) (hf (path_fun γ2 s)))
  (linhom_int_pt_meas HΦ (hf (path_fun γ2 s))) µ.
rewrite /= in HgInt.
rewrite HgInt.
rewrite (icone_integralP _ _ µ m2 m2M s).
by [].
Qed.

(** Paper Prop 5.8: the action of [⊸] on morphisms as an [icones_hom]. *)
Definition linhom_map_icones : icones_hom Ar (linhom_car Ar C1 D1)
                                            (linhom_car Ar C2 D2) :=
  MkIConesHom linhom_map_mcones linhom_map_pres_int.

(** The underlying map of [linhom_map_icones] is [linhom_map_fun h g]. *)
Lemma linhom_map_iconesE (f : linhom_car Ar C1 D1) :
  cones_hom_fun (mcones_hom_cones (icones_hom_mcones linhom_map_icones)) f =
  linhom_map_fun h g f.
Proof. by []. Qed.

End LinhomMapHom.

Arguments linhom_map_cones {R Ar C1 C2 D1 D2}.
Arguments linhom_map_mcones {R Ar C1 C2 D1 D2}.
Arguments linhom_map_icones {R Ar C1 C2 D1 D2}.

(** ** One-sided actions — Paper §5.3

    [C ⊸ g := linhom_map_icones (id C) g] (post-composition by [g],
    covariant in the codomain) and [h ⊸ D := linhom_map_icones h
    (id D)] (pre-composition by [h], contravariant in the domain). *)

Section LinhomOneSided.
Variables (R : realType) (Ar : MeasSubcat R).

(** [C ⊸ g : (C ⊸ D1) → (C ⊸ D2)] as an [icones_hom]. *)
Definition linhom_post_icones (C D1 D2 : ICone.type Ar)
    (g : icones_hom Ar D1 D2) :
    icones_hom Ar (linhom_car Ar C D1) (linhom_car Ar C D2) :=
  linhom_map_icones (icones_id Ar C) g.

(** [h ⊸ D : (C1 ⊸ D) → (C2 ⊸ D)] as an [icones_hom]. *)
Definition linhom_pre_icones (C1 C2 D : ICone.type Ar)
    (h : icones_hom Ar C2 C1) :
    icones_hom Ar (linhom_car Ar C1 D) (linhom_car Ar C2 D) :=
  linhom_map_icones h (icones_id Ar D).

(** Pointwise: [(C ⊸ g) f = linhom_post g f = g ∘ f]. *)
Lemma linhom_post_iconesE (C D1 D2 : ICone.type Ar)
    (g : icones_hom Ar D1 D2) (f : linhom_car Ar C D1) :
  cones_hom_fun
    (mcones_hom_cones (icones_hom_mcones (@linhom_post_icones C D1 D2 g)))
    f = linhom_post g f.
Proof. by []. Qed.

(** Pointwise: [(h ⊸ D) f = linhom_pre_act h f = f ∘ h]. *)
Lemma linhom_pre_iconesE (C1 C2 D : ICone.type Ar)
    (h : icones_hom Ar C2 C1) (f : linhom_car Ar C1 D) :
  cones_hom_fun
    (mcones_hom_cones (icones_hom_mcones (@linhom_pre_icones C1 C2 D h)))
    f = linhom_pre_act h f.
Proof. by []. Qed.

End LinhomOneSided.

Arguments linhom_post_icones {R Ar C D1 D2}.
Arguments linhom_pre_icones {R Ar C1 C2 D}.

(** ** Morphism-level functoriality — Paper Prop 5.8

    The identity and composition laws of the hom-functor, now stated as
    equalities of morphisms in [ICones] (via [icones_hom_eq]), reducing
    to the object-level laws [linhom_map_id] / [linhom_map_comp]. *)

Section LinhomMapFunctor.
Variables (R : realType) (Ar : MeasSubcat R).

(** Prop 5.8 (identity): [(id C) ⊸ (id D) = id (C ⊸ D)] in [ICones]. *)
Lemma linhom_map_icones_id (C D : ICone.type Ar) :
  linhom_map_icones (icones_id Ar C) (icones_id Ar D) =
  icones_id Ar (linhom_car Ar C D).
Proof.
apply: icones_hom_eq => f.
rewrite linhom_map_iconesE.
exact: linhom_map_id.
Qed.

(** Prop 5.8 (composition, contravariant in the first slot):
    [(h' ∘ h) ⊸ (g ∘ g') = (h' ⊸ g') ∘ (h ⊸ g)] in [ICones]. *)
Lemma linhom_map_icones_comp
    (C1 C2 C3 D1 D2 D3 : ICone.type Ar)
    (h : icones_hom Ar C2 C1) (h' : icones_hom Ar C3 C2)
    (g : icones_hom Ar D1 D2) (g' : icones_hom Ar D2 D3) :
  linhom_map_icones (icones_comp h h') (icones_comp g' g) =
  icones_comp (linhom_map_icones h' g') (linhom_map_icones h g).
Proof.
apply: icones_hom_eq => f.
rewrite linhom_map_iconesE.
exact: linhom_map_comp.
Qed.

End LinhomMapFunctor.
