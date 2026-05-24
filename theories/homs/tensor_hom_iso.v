(**md**************************************************************************)
(* # Tensor discharge T2A — Thm 5.12 [tensor_hom_iso] + Thm 5.13 [tensor_normM]*)
(*                                                                            *)
(* This file DISCHARGES, as genuine AXIOM-FREE theorems about the concrete    *)
(* [tensor_construct] construction, two of the remaining staged [Parameter]s  *)
(* of [theories/axioms/saft_interface.v]:                                     *)
(*                                                                            *)
(*   tensor_hom_iso  (Paper Thm 5.12 — [(B ⊗ C) ⊸ D ≅ B ⊸ (C ⊸ D)])           *)
(*   tensor_normM    (Paper Thm 5.13 — [‖x ⊗ y‖ = ‖x‖ · ‖y‖])                  *)
(*                                                                            *)
(* It is AXIOM-FREE relative to the classical [boolp] base ([pselect]/[cid]/  *)
(* extensionality) — NO [Axiom]/[Parameter]/[Admitted], and it does NOT       *)
(* import [saft_interface]: the proved versions are built from scratch, in    *)
(* their own module [Icones_tensor_hom_iso], from the proved [tensor_curry] / *)
(* [tensor_uncurry] of [tensor_construct].                                    *)
(*                                                                            *)
(* The signatures match the [saft_interface] arguments exactly:               *)
(*   tensor_hom_iso {R Ar} B C D                                              *)
(*   tensor_normM   {R Ar B C}                                                 *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals constructive_ereal.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import ereal.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import measure.
From mathcomp.analysis Require Import lebesgue_integral_definition.
From mathcomp.analysis Require Import lebesgue_integral_monotone_convergence.
From mathcomp.analysis Require Import topology normedtype sequences.
Import numFieldTopology.Exports.

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
Require Import Icones.icones.icone_cat.
Require Import Icones.icones.representable.
Require Import Icones.homs.linhom.
Require Import Icones.homs.linhom_functor.
Require Import Icones.homs.icones_iso.
Require Import Icones.homs.limpl_continuous.
Require Import Icones.homs.bilin.
Require Import Icones.homs.tensor_construct.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Import Icones_tensor_construct.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Module Icones_tensor_hom_iso.

(** ** Bridge: an [icones_hom] as a [linhom_car] element

    The reverse of [seely.v]'s [linhom_icones].  An [icones_hom Ar B X]
    is an integrable linear map of operator norm [≤ 1]; its underlying
    function is exactly the data of a [linhom_car Ar B X] element.  All
    five [linhom_car] fields come verbatim from the [icones_hom] fields;
    the boundedness witness is [M := 1] (norm [≤ 1]). *)

Section IConesToLinhom.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B X : ICone.type Ar.
Variable h : icones_hom Ar B X.

Local Notation ch := (mcones_hom_cones (icones_hom_mcones h)).
Local Notation hf := (cones_hom_fun ch).

Lemma i2l_bounded :
  exists M : R, forall x : B, cnorm x <= 1 -> cnorm (hf x) <= M.
Proof.
exists 1 => x Hx.
by apply: le_trans (cones_hom_norm_le1 ch x) _.
Qed.

Definition i2l_pre : linhom_pre Ar B X :=
  MkLinhomPre hf
    (@cones_hom_linear _ _ _ ch)
    (@cones_hom_continuous _ _ _ ch)
    i2l_bounded
    (fun Y g Hg => mcones_hom_pres_path (icones_hom_mcones h) Y g Hg).

Lemma i2l_pres_int
    (Y : ar_obj Ar) (β : ar_carrier Ar Y -> B)
    (Hβ : is_measurable_path β) (µ : fmeas R (ar_carrier Ar Y)) :
  linhom_pre_fun i2l_pre (icone_integral β Hβ µ) =
  icone_integral
    (fun r => linhom_pre_fun i2l_pre (β r))
    (linhom_pre_pres_path i2l_pre Y β Hβ) µ.
Proof.
rewrite /i2l_pre /= (icones_hom_pres_int h Y β Hβ µ).
by congr icone_integral; exact: Prop_irrelevance.
Qed.

Definition icones_to_linhom : linhom_car Ar B X :=
  MkLinhom i2l_pre i2l_pres_int.

Lemma icones_to_linhomE (x : B) :
  linhom_fun icones_to_linhom x = hf x.
Proof. by []. Qed.

(** Its operator norm is [≤ 1]. *)
Lemma icones_to_linhom_norm_le1 : cone_norm icones_to_linhom <= 1.
Proof.
rewrite -[cone_norm _]/(linhom_norm icones_to_linhom).
apply: linhom_norm_sup_lub => x Hx.
by apply: le_trans (cones_hom_norm_le1 ch x) _.
Qed.

End IConesToLinhom.

Arguments icones_to_linhom {R Ar B X} h.
Arguments icones_to_linhomE {R Ar B X} h.
Arguments icones_to_linhom_norm_le1 {R Ar B X} h.

(** ** Bridge: a norm-[≤1] [linhom_car] as an [icones_hom]

    The forward of [icones_to_linhom] (= [seely.v]'s [linhom_icones],
    re-derived here to avoid importing the staged-interface chain).  A
    [linhom_car Ar C D] element [φ] of operator norm [≤ 1] is exactly the
    data of an [icones_hom Ar C D]; the per-point bound is
    [linhom_norm_apply_le] at [K = 1]. *)

Section LinhomIcones.
Variables (R : realType) (Ar : MeasSubcat R).
Variables C D : ICone.type Ar.
Variable phi : linhom_car Ar C D.
Hypothesis Hphi : cone_norm phi <= 1.

Lemma linhom_icones_normP (x : C) :
  cone_norm (linhom_fun phi x) <= cone_norm x.
Proof. by have := linhom_norm_apply_le Hphi x; rewrite mul1r. Qed.

Definition linhom_icones_cones : cones_hom C D :=
  ConesHom (linhom_fun phi)
    (linhom_pre_linear (linhom_pre_of phi))
    (linhom_pre_continuous (linhom_pre_of phi))
    linhom_icones_normP.

Definition linhom_icones_mcones : mcones_hom Ar C D :=
  MkMConesHom linhom_icones_cones
    (fun X g Hg => linhom_pre_pres_path (linhom_pre_of phi) X g Hg).

Lemma linhom_icones_pres_int
    (X : ar_obj Ar) (β : ar_carrier Ar X -> C)
    (Hβ : is_measurable_path β) (µ : fmeas R (ar_carrier Ar X)) :
  cones_hom_fun (mcones_hom_cones linhom_icones_mcones)
    (icone_integral β Hβ µ) =
  icone_integral
    (fun r => cones_hom_fun (mcones_hom_cones linhom_icones_mcones) (β r))
    (mcones_hom_pres_path linhom_icones_mcones X β Hβ) µ.
Proof.
rewrite /= /linhom_fun (linhom_pres_int phi X β Hβ µ).
by congr icone_integral; exact: Prop_irrelevance.
Qed.

Definition linhom_icones : icones_hom Ar C D :=
  MkIConesHom linhom_icones_mcones linhom_icones_pres_int.

Lemma linhom_iconesE (x : C) :
  cones_hom_fun (mcones_hom_cones (icones_hom_mcones linhom_icones)) x =
  linhom_fun phi x.
Proof. by []. Qed.

End LinhomIcones.

Arguments linhom_icones {R Ar C D} phi Hphi.
Arguments linhom_iconesE {R Ar C D} phi Hphi.

(** ** General composition of two [linhom_car] elements

    [linhom_comp g f := g ∘ f] for general [g : D1 ⊸ D2] and
    [f : C ⊸ D1], neither necessarily of norm [≤ 1].  We reduce to the
    norm-[≤1] post-composition [linhom_postc] of [linhom.v] (which
    already handles an arbitrary-norm pre-map [f]) by rescaling [g] into
    the unit ball: [g = (‖g‖+1) · gs] with [gs := (‖g‖+1)⁻¹ · g] of norm
    [≤ 1], and post-scaling the result.  All five [linhom_car] fields
    therefore come for free; the per-point computation
    [linhom_compE] cancels the two scalings. *)

Section LinhomComp.
Variables (R : realType) (Ar : MeasSubcat R).
Variables C D1 D2 : ICone.type Ar.
Variable g : linhom_car Ar D1 D2.
Variable f : linhom_car Ar C D1.

Let t : R := cone_norm g + 1.
Let t_pos : 0 < t.
Proof.
rewrite /t.
by apply: lt_le_trans ltr01 _; rewrite lerDr cone_norm_ge0.
Qed.
Let tinv_ge0 : 0 <= t^-1.
Proof. by rewrite invr_ge0 ltW. Qed.
Let tge0 : 0 <= t.
Proof. exact: ltW. Qed.

Definition lc_t : {nonneg R} := NngNum tge0.
Definition lc_tinv : {nonneg R} := NngNum tinv_ge0.

(** The rescaled [gs := t⁻¹ · g] has operator norm [≤ 1]. *)
Let gs : linhom_car Ar D1 D2 := linhom_scale lc_tinv g.

Lemma lc_gs_norm : cone_norm gs <= 1.
Proof.
rewrite -[cone_norm gs]/(linhom_norm gs) /gs linhom_normh /=.
rewrite mulrC -ler_pdivlMr ?invr_gt0 // mul1r invrK.
by rewrite /t lerDl ler01.
Qed.

Definition linhom_comp : linhom_car Ar C D2 :=
  linhom_scale lc_t (linhom_postc (linhom_icones gs lc_gs_norm) f).

(** Per-point computation: [linhom_comp g f x = g (f x)]. *)
Lemma linhom_compE (x : C) :
  linhom_fun linhom_comp x = linhom_fun g (linhom_fun f x).
Proof.
rewrite /linhom_comp /linhom_fun /= /linhom_scale_fun /=.
rewrite (linhom_postc_E (linhom_icones gs lc_gs_norm) f x).
rewrite (linhom_iconesE gs lc_gs_norm (linhom_fun f x)).
rewrite /gs /linhom_fun /= /linhom_scale_fun /=.
rewrite -precone_scale_A.
have -> : (lc_t%:num * lc_tinv%:num)%:nng = 1%:nng :> {nonneg R}.
  by apply: val_inj => /=; rewrite mulfV// gt_eqF.
by rewrite precone_scale_1.
Qed.

End LinhomComp.

Arguments linhom_comp {R Ar C D1 D2} g f.
Arguments linhom_compE {R Ar C D1 D2} g f.

(** ** Local pure tensor [⊗p] and its computation law

    We re-introduce, from the proved [tensor_construct] primitives (NOT
    from the staged [tensor.v]/[smcc.v]), the universal map
    [tauL := tensor_curry id] and the pure tensor [x ⊗p y := tauL(x)(y)],
    together with [tensor_curryEp] (Paper Eq 5.1):
    [Φ(h)(x)(y) = h(x ⊗p y)]. *)

Section PureTensor.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : ICone.type Ar.

Definition tauL : icones_hom Ar B (linhom_car Ar C (tensor B C)) :=
  tensor_curry (icones_id Ar (tensor B C)).

Definition ptensor (x : B) (y : C) : tensor B C :=
  linhom_fun ((tauL : icones_hom _ _ _) x) y.

Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity).

(** Paper Eq 5.1: [Φ(h)(x)(y) = h(x ⊗p y)]. *)
Lemma tensor_curryEp (D : ICone.type Ar)
    (h : icones_hom Ar (tensor B C) D) (x : B) (y : C) :
  linhom_fun ((tensor_curry h : icones_hom _ _ _) x) y =
  (h : icones_hom _ _ _) (x ⊗p y).
Proof.
rewrite /ptensor /tauL.
rewrite -[in LHS](icones_compIr h).
rewrite (tensor_curry_natural_post h (icones_id Ar (tensor B C))).
by rewrite /= linhom_map_funE /=.
Qed.

End PureTensor.

Arguments tauL {R Ar} B C.
Arguments ptensor {R Ar B C}.
Arguments tensor_curryEp {R Ar B C D}.

(** ** The "line" morphism [1 ⊸ (C ⊸ D)] — Paper §5.4 (dual-test tool)

    For a fixed norm-[≤1] element [ψ : C ⊸ D], the map
    [r ↦ (c1_val r) ·: ψ : 1 → (C ⊸ D)] is an [icones_hom].  This is the
    elementary "scalar line through ψ" map; composed with a functional
    [φ : B → 1] it gives the external-product functional needed for the
    [≥] half of [tensor_normM] (Paper Thm 5.13). *)

Section LineHom.
Variables (R : realType) (Ar : MeasSubcat R).
Variables C D : ICone.type Ar.
Variable psi : linhom_car Ar C D.
Hypothesis Hpsi : cone_norm psi <= 1.
Local Notation One := (cone_one_car Ar).

Definition line_fun (r : One) : linhom_car Ar C D :=
  linhom_scale (c1_val r) psi.

Lemma line_funE (r : One) (z : C) :
  linhom_fun (line_fun r) z = precone_scale (c1_val r) (linhom_fun psi z).
Proof. by []. Qed.

Lemma line_linear : is_linear line_fun.
Proof.
split.
- rewrite /line_fun (_ : c1_val (0%PC : One) = 0%:nng) ?linhom_scale_0l //.
- move=> x y; apply: linhom_eq => z; rewrite line_funE.
  rewrite /linhom_fun /= /linhom_add_fun /= !line_funE.
  rewrite (_: nng_add (c1_val x) (c1_val y) =
              ((c1_val x)%:num + (c1_val y)%:num)%:nng) ?precone_scale_DAl //.
- move=> s x; apply: linhom_eq => z; rewrite line_funE.
  rewrite /linhom_fun /= /linhom_scale_fun /= !line_funE.
  rewrite (_: nng_mul s (c1_val x) =
              (s%:num * (c1_val x)%:num)%:nng) ?precone_scale_A //.
Qed.

Lemma line_norm_le1 (r : One) : cone_norm (line_fun r) <= cone_norm r.
Proof.
rewrite -[cone_norm (line_fun r)]/(linhom_norm (line_fun r)) /line_fun.
rewrite linhom_normh /=.
rewrite -[cone_norm r]/((c1_val r)%:num).
rewrite -[X in _ <= X]mulr1.
by apply: ler_wpM2l => //.
Qed.

Lemma line_bounded :
  exists M : R, forall r : One, cnorm r <= 1 -> cnorm (line_fun r) <= M.
Proof. by exists 1 => r Hr; apply: le_trans (line_norm_le1 r) _. Qed.

(** ω-continuity: the sup commutes.  The [≥] half is monotonicity; the
    [≤] half writes [line_fun(sup u) = sup(line_fun ∘ u) + t] and shows
    [‖t‖ = 0] via the [sup]-adherence of [c1_val(u_n) ↗ L] (mirroring
    [findiff.scale_chain_sup]). *)
Lemma line_continuous : is_omega_continuous line_fun.
Proof.
move=> u uch ub1 fuch fub1.
set L := c1_val (cone_sup_ball u uch ub1).
set s := cone_sup_ball (line_fun \o u) fuch fub1.
have HuL : forall n, ((c1_val (u n))%:num <= L%:num)%R.
  move=> n.
  have := cone_sup_ball_ub u uch ub1 n.
  by move=> /(cone_normp _ _); rewrite /cone_norm /= /c1_norm /=.
have s_le : (s <=p line_fun (cone_sup_ball u uch ub1))%PC.
  apply: cone_sup_ball_lub => n; apply: (linear_increasing line_linear).
  exact: cone_sup_ball_ub.
apply/esym/precone_le_anti => //.
have [t Ht] := s_le.
have t_bound : forall n,
    (cone_norm t <= (L%:num - (c1_val (u n))%:num) * cone_norm psi)%R.
  move=> n.
  have [w Hw] : (line_fun (u n) <=p s)%PC by exact: cone_sup_ball_ub.
  have dn_ge0 : (0 <= L%:num - (c1_val (u n))%:num)%R by rewrite subr_ge0 HuL.
  pose dn : {nonneg R} := NngNum dn_ge0.
  have E1 : line_fun (cone_sup_ball u uch ub1) =
            (line_fun (u n) + linhom_scale dn psi)%PC.
    rewrite -[line_fun (u n)]/(linhom_scale (c1_val (u n)) psi).
    rewrite -[line_fun (cone_sup_ball u uch ub1)]/(linhom_scale L psi).
    rewrite -[(_ + _)%PC]/(linhom_add (linhom_scale (c1_val (u n)) psi)
                                       (linhom_scale dn psi)).
    rewrite -linhom_scale_DAl; congr (linhom_scale _ psi); apply: val_inj => /=.
    by rewrite addrC subrK.
  have E2 : line_fun (cone_sup_ball u uch ub1) =
            (line_fun (u n) + (w + t))%PC.
    by rewrite Ht Hw -precone_addA.
  have Heq : linhom_scale dn psi = (w + t)%PC.
    by apply: (@precone_cancel _ _ (line_fun (u n))); rewrite -E1 -E2.
  have t_le : (t <=p linhom_scale dn psi)%PC.
    by rewrite Heq precone_addC; exists w.
  have := cone_normp _ _ t_le.
  rewrite -[cone_norm (linhom_scale dn psi)]/(linhom_norm (linhom_scale dn psi)).
  by rewrite linhom_normh.
have LsupE : L%:num = sup [set (c1_val (u n))%:num | n in [set: nat]].
  exact: c1_sup_ball_E.
have t_norm0 : (cone_norm t <= 0)%R.
  apply/unstable.ler_gtP => e e_pos.
  have hs : has_sup [set (c1_val (u n))%:num | n in [set: nat]].
    split; first by exists (c1_val (u 0%N))%:num, 0%N.
    by exists 1 => _ [n _ <-]; have := ub1 n; rewrite /cone_norm /= /c1_norm /=.
  have [a [n _ Hae] Ha] := sup_adherent e_pos hs.
  move: Ha; rewrite -Hae -LsupE => Ha.
  apply: le_trans (t_bound n) _.
  apply: le_trans (_ : (L%:num - (c1_val (u n))%:num) * 1 <= e)%R.
    by rewrite ler_wpM2l // subr_ge0 HuL.
  by rewrite mulr1 ltW // ltrBlDr addrC -ltrBlDr.
have t0 : t = precone_zero.
  by apply: cone_normz; apply/le_anti; rewrite t_norm0 cone_norm_ge0.
by rewrite Ht t0 precone_addr0; exact: precone_le_refl.
Qed.

(** Path-preservation: tests of [C ⊸ D] are [δ ▷ m]; the pulled-back
    test of [line_fun ∘ γ] factors as [c1_val(γ r) · m(s, ψ(δ s))] —
    a product of a measurable [r]-function and a measurable [s]-function,
    hence jointly measurable. *)
Lemma line_pres_path (X : ar_obj Ar) (γ : ar_carrier Ar X -> One) :
  is_measurable_path γ ->
  is_measurable_path (fun r => line_fun (γ r)).
Proof.
move=> Hγ.
have [[M HM] Hmeas] := Hγ.
split.
  exists M => r; apply: le_trans (line_norm_le1 (γ r)) _; exact: HM.
move=> Y p pM.
case: pM => δ [δub [m [mM ->]]].
rewrite /linhom_test /=.
have -> : (fun q : (ar_carrier Ar Y * ar_carrier Ar X)%type =>
            linhom_test_fun δ m q.1 (line_fun (γ q.2))) =
          (fun q => (c1_val (γ q.2))%:num *
                    test_fun m q.1 (linhom_fun psi (path_fun δ q.1))).
  apply: funext => q.
  by rewrite /linhom_test_fun line_funE /linhom_fun /= test_linZ.
rewrite [X in measurable_fun _ X](_ : _ =
  ((fun s => m s (linhom_fun psi (path_fun δ s))) \o fst) \*
  ((fun r => (c1_val (γ r))%:num) \o snd)); last first.
  by apply: funext => q; rewrite /GRing.mul /= mulrC.
apply: measurable_funM.
- apply: (measurable_comp (F := setT) measurableT (subsetT _) _ measurable_fst).
  have Hpsiδ : is_measurable_path (fun r => linhom_fun psi (path_fun δ r)).
    exact: (linhom_pre_pres_path (linhom_pre_of psi) Y (path_fun δ)
              (path_is_path δ)).
  have [_ Hj] := Hpsiδ.
  have Hbase := Hj Y m mM.
  pose F (pp : ar_carrier Ar Y * ar_carrier Ar Y) : R :=
    test_fun m pp.1 (linhom_fun psi (path_fun δ pp.2)).
  have -> : (fun s => test_fun m s (linhom_fun psi (path_fun δ s))) =
            F \o (fun s => (s, s)).
    by apply: funext.
  apply: (measurable_comp (F := setT) measurableT (subsetT _) Hbase).
  by apply: measurable_fun_pair; exact: measurable_id.
- apply: (measurable_comp (F := setT) measurableT (subsetT _) _ measurable_snd).
  exact: (measurable_test_path_section (B := cone_one_car Ar)
            (m := ConeOneMConeAux.id_test (R:=R) (Ar:=Ar) (ar_zero Ar))
            (erefl) Hγ (ar_zero_pt Ar)).
Qed.

Definition line_pre : linhom_pre Ar One (linhom_car Ar C D) :=
  MkLinhomPre line_fun line_linear line_continuous line_bounded
              (fun X g Hg => line_pres_path (X:=X) (γ:=g) Hg).

(** Integral-preservation: by [icone_integral_eqP] on [C ⊸ D]; tests are
    [δ ▷ m], for which the obligation reduces (via [test_linZ] + the
    [1]-cone integral [icone_integralP] against [id_test]) to the scalar
    Lebesgue identity [c1_val(∫β) · K = ∫ (c1_val(β r) · K)]. *)
Lemma line_pres_int
  (X : ar_obj Ar) (β : ar_carrier Ar X -> One)
  (Hβ : is_measurable_path β) (µ : fmeas R (ar_carrier Ar X)) :
  linhom_pre_fun line_pre (icone_integral β Hβ µ) =
  icone_integral
    (fun r => linhom_pre_fun line_pre (β r))
    (linhom_pre_pres_path line_pre X β Hβ) µ.
Proof.
apply: icone_integral_eqP => p pM s.
case: pM => δ [δub [m [mM ->]]].
rewrite /linhom_test /linhom_test_fun /=.
rewrite line_funE /linhom_fun /= test_linZ.
set K : R := test_fun m s (linhom_fun psi (path_fun δ s)).
(* c1_val (∫_1 β µ) = ∫ c1_val (β r) dµ, by icone_integralP at id_test. *)
have HcInt : (c1_val (icone_integral β Hβ µ))%:num =
  fine (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X])
          ((c1_val (β r))%:num)%:E).
  have := icone_integralP β Hβ µ
            (ConeOneMConeAux.id_test (R:=R) (Ar:=Ar) (ar_zero Ar)) erefl
            (ar_zero_pt Ar).
  by [].
rewrite HcInt.
(* RHS integrand: test_fun (δ▷m) s (line_fun (β r)) = c1_val(β r) · K. *)
rewrite [in RHS](eq_integral (fun r => (((c1_val (β r))%:num)%:E * K%:E)%E));
  last by move=> r _; rewrite /linhom_scale_fun test_linZ -/K -EFinM.
have Hmeas_c : measurable_fun [set: ar_carrier Ar X]
    (fun x : ar_carrier Ar X => ((c1_val (β x))%:num)%:E).
  apply/measurable_EFinP.
  exact: (measurable_test_path_section (B := cone_one_car Ar)
            (m := ConeOneMConeAux.id_test (R:=R) (Ar:=Ar) (ar_zero Ar))
            (erefl) Hβ (ar_zero_pt Ar)).
have [Mb HMb] : exists M : R, forall r, ((c1_val (β r))%:num <= M)%R.
  by have := Hβ; case=> -[Mb HMb] _; exists Mb => r;
     have := HMb r; rewrite /cone_norm /= /c1_norm /=.
have Kge0 : (0 <= K)%R by rewrite /K; exact: test_ge0.
have Hfin : (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X])
              ((c1_val (β r))%:num)%:E < +oo)%E.
  apply: (@le_lt_trans _ _
    (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X]) Mb%:E)%E).
    apply: (ge0_le_integral _ measurableT _ Hmeas_c (measurable_cst _)).
    - by move=> r _; rewrite lee_fin.
    - by move=> r _; rewrite lee_fin HMb.
  rewrite -[(fun=> Mb%:E)]/(cst Mb%:E) lebesgue_integral_nonneg.integral_cst//.
  by rewrite ltey_eq fin_numM// fmeas_setT_fin.
rewrite lebesgue_integral_nonneg.ge0_integralZr//;
  try by move=> r _; rewrite lee_fin.
rewrite fineM//.
by rewrite ge0_fin_numE//; apply: integral_ge0 => r _; rewrite lee_fin.
Qed.

Definition line_hom : icones_hom Ar One (linhom_car Ar C D) :=
  MkIConesHom (MkMConesHom (ConesHom line_fun line_linear line_continuous
                             line_norm_le1)
                 (fun X g Hg => line_pres_path (X:=X) (γ:=g) Hg))
    line_pres_int.

Lemma line_homE (r : One) (z : C) :
  cones_hom_fun (mcones_hom_cones (icones_hom_mcones line_hom)) r =
  linhom_scale (c1_val r) psi.
Proof. by []. Qed.

End LineHom.

Arguments line_hom {R Ar C D} psi Hpsi.

(** ** Theorem 5.13 — [‖x ⊗ y‖ = ‖x‖ · ‖y‖]

    The [≤] half is [ptensor_norm_le] (norm-decrease of [τ]).  For the
    [≥] half (Paper Thm 5.13, the dual-test argument), given near-optimal
    arity-0 tests [m1] on [B] and [m2] on [C] (Prop 3.11 adherence,
    [mcone_test_pairing_adherent]), the external-product functional
    [g(b)(c) = ⟨b,m1⟩·⟨c,m2⟩] is realised as
    [ghom := (line through m2-as-functional) ∘ (m1-as-functional)], and
    its uncurry [zz := Φ⁻¹(g) : (B⊗C) → 1] is a norm-[≤1] map satisfying
    [zz(x⊗y) = ⟨x,m1⟩·⟨y,m2⟩] (by [tensor_uncurryK] + Eq 5.1).  Norm
    decrease of [zz] gives [⟨x,m1⟩·⟨y,m2⟩ ≤ ‖x⊗y‖] ([zz_pairing]); the
    sup over near-optimal tests is [‖x‖·‖y‖]. *)

Section NormM.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : ICone.type Ar.
Local Notation One := (cone_one_car Ar).

(** The external-product functional [b ↦ (c ↦ ⟨b,m1⟩·⟨c,m2⟩)], as an
    [icones_hom B (C ⊸ 1)], built from two selected arity-0 tests. *)
Section ExtProd.
Variables (m1 : test_of Ar (ar_zero Ar) B) (m2 : test_of Ar (ar_zero Ar) C).
Hypothesis m1M : mcone_M (ar_zero Ar) m1.
Hypothesis m2M : mcone_M (ar_zero Ar) m2.

Definition np_xx : icones_hom Ar B One := hom_of_test m1 m1M.
Definition np_yy : icones_hom Ar C One := hom_of_test m2 m2M.

Lemma np_psi_norm : cone_norm (icones_to_linhom np_yy) <= 1.
Proof. exact: icones_to_linhom_norm_le1. Qed.

Definition np_ghom : icones_hom Ar B (linhom_car Ar C One) :=
  icones_comp (line_hom (icones_to_linhom np_yy) np_psi_norm) np_xx.

Definition np_zz : icones_hom Ar (tensor B C) One := tensor_uncurry np_ghom.

(** [np_ghom b c = ⟨b,m1⟩·⟨c,m2⟩] (as a real, via [c1_val]). *)
Lemma np_ghomE (x : B) (y : C) :
  (c1_val (linhom_fun ((np_ghom : icones_hom _ _ _) x) y))%:num =
  test_fun m1 (ar_zero_pt Ar) x * test_fun m2 (ar_zero_pt Ar) y.
Proof. by rewrite /np_ghom /=. Qed.

(** Paper Thm 5.13 (key dual pairing): [⟨x,m1⟩·⟨y,m2⟩ ≤ ‖x ⊗ y‖]. *)
Lemma np_pairing (x : B) (y : C) :
  (test_fun m1 (ar_zero_pt Ar) x * test_fun m2 (ar_zero_pt Ar) y <=
   cone_norm (ptensor x y))%R.
Proof.
have Hz : (c1_val ((np_zz : icones_hom _ _ _) (ptensor x y)))%:num =
          test_fun m1 (ar_zero_pt Ar) x * test_fun m2 (ar_zero_pt Ar) y.
  rewrite /np_zz.
  have HH := tensor_curryEp (tensor_uncurry np_ghom) x y.
  rewrite tensor_uncurryK in HH.
  by rewrite -HH np_ghomE.
rewrite -Hz.
have := cones_hom_norm_le1 (mcones_hom_cones (icones_hom_mcones np_zz))
          (ptensor x y).
by rewrite -[cone_norm ((np_zz : icones_hom _ _ _) (ptensor x y))]
            /((c1_val _)%:num).
Qed.

End ExtProd.

(** Paper Thm 5.13 ([≤]): [‖x ⊗ y‖ ≤ ‖x‖ · ‖y‖], norm-decrease of [τ]. *)
Lemma ptensor_norm_le (x : B) (y : C) :
  (cone_norm (ptensor x y) <= cone_norm x * cone_norm y)%R.
Proof.
rewrite /ptensor.
apply: (@le_trans _ _
  (cone_norm ((tauL B C : icones_hom _ _ _) x) * cone_norm y)).
  by have := linhom_norm_apply_le
       (K := cone_norm ((tauL B C : icones_hom _ _ _) x)) (lexx _) y.
rewrite ler_wpM2r ?cone_norm_ge0 //.
by have := cones_hom_norm_le1 (mcones_hom_cones (icones_hom_mcones (tauL B C))) x.
Qed.

(** Paper Thm 5.13 ([≥], non-zero case): [‖x‖·‖y‖ ≤ ‖x ⊗ y‖]. *)
Lemma ptensor_norm_ge (x : B) (y : C) :
  x <> precone_zero -> y <> precone_zero ->
  (cone_norm x * cone_norm y <= cone_norm (ptensor x y))%R.
Proof.
move=> xnz ynz.
apply/ler_addgt0Pr => e e_pos.
set nx := cone_norm x. set ny := cone_norm y.
have nxge0 : (0 <= nx)%R by exact: cone_norm_ge0.
have nyge0 : (0 <= ny)%R by exact: cone_norm_ge0.
have den_pos : (0 < nx + ny + 1)%R by rewrite ltr_pwDr // addr_ge0.
pose d : R := Order.min 1 (e / (nx + ny + 1)).
have d_pos : (0 < d)%R by rewrite lt_min ltr01 divr_gt0.
have d_le1 : (d <= 1)%R by rewrite ge_min lexx.
have d_le : (d <= e / (nx + ny + 1))%R by rewrite ge_min lexx orbT.
have [vx [m1 m1M ->] Hvx] := mcone_test_pairing_adherent (B:=B) xnz d_pos.
have [vy [m2 m2M ->] Hvy] := mcone_test_pairing_adherent (B:=C) ynz d_pos.
have HmxU : (test_fun m1 (ar_zero_pt Ar) x <= nx)%R by exact: test_norm_le.
have HmyU : (test_fun m2 (ar_zero_pt Ar) y <= ny)%R by exact: test_norm_le.
have HmxG0 : (0 <= test_fun m1 (ar_zero_pt Ar) x)%R by exact: test_ge0.
have HmyG0 : (0 <= test_fun m2 (ar_zero_pt Ar) y)%R by exact: test_ge0.
have HmxL : (nx - d <= test_fun m1 (ar_zero_pt Ar) x)%R by rewrite lerBlDr.
have HmyL : (ny - d <= test_fun m2 (ar_zero_pt Ar) y)%R by rewrite lerBlDr.
have Hpair : (test_fun m1 (ar_zero_pt Ar) x * test_fun m2 (ar_zero_pt Ar) y
              <= cone_norm (ptensor x y))%R by exact: np_pairing.
have step : (nx * ny <=
    (test_fun m1 (ar_zero_pt Ar) x + d) * (test_fun m2 (ar_zero_pt Ar) y + d))%R.
  by apply: ler_pM => //; rewrite -lerBlDr.
apply: le_trans step _.
have expand : ((test_fun m1 (ar_zero_pt Ar) x + d) *
               (test_fun m2 (ar_zero_pt Ar) y + d) <=
               cone_norm (ptensor x y) + (d * (nx + ny) + d * d))%R.
  rewrite mulrDl !mulrDr -addrA.
  apply: lerD => //.
  rewrite addrA; apply: lerD; last exact: lexx.
  apply: lerD.
  - by rewrite mulrC ler_wpM2l // ltW.
  - by rewrite ler_wpM2l // ltW.
apply: le_trans expand _.
rewrite lerD2l.
apply: (@le_trans _ _ (d * (nx + ny + 1))%R).
  rewrite [in X in (_ <= X)%R]mulrDr mulr1 lerD2l.
  by rewrite -[X in (_ <= X)%R]mulr1 ler_wpM2l // ltW.
by rewrite -ler_pdivlMr // mulrC mulrA mulVf ?gt_eqF // mul1r.
Qed.

(** [ptensor] vanishes on a zero argument (linearity of [τ]). *)
Lemma ptensor_0l (y : C) : ptensor (precone_zero : B) y = precone_zero.
Proof.
rewrite /ptensor.
have HtauL0 : (tauL B C : icones_hom _ _ _) (precone_zero : B) = precone_zero.
  by have [K0 _ _] :=
    cones_hom_linear (mcones_hom_cones (icones_hom_mcones (tauL B C))).
rewrite HtauL0.
have [Z0 _ _] :=
  linhom_pre_linear (linhom_pre_of (precone_zero : linhom_car Ar C (tensor B C))).
exact: Z0.
Qed.

Lemma ptensor_0r (x : B) : ptensor x (precone_zero : C) = precone_zero.
Proof.
rewrite /ptensor.
by have [Z0 _ _] :=
  linhom_pre_linear (linhom_pre_of ((tauL B C : icones_hom _ _ _) x)).
Qed.

(** Paper Thm 5.13 (full): [‖x ⊗ y‖ = ‖x‖ · ‖y‖], matching the
    [saft_interface] statement [tensor_normM]. *)
Lemma tensor_normM (x : B) (y : C) :
  cone_norm (linhom_fun (tensor_curry (icones_id Ar (tensor B C)) x) y)
  = cone_norm x * cone_norm y.
Proof.
rewrite -[linhom_fun (tensor_curry (icones_id Ar (tensor B C)) x) y]
         /(ptensor x y).
apply/le_anti/andP; split; first exact: ptensor_norm_le.
have [x0|xnz] := pselect (x = precone_zero).
  by rewrite x0 cone_norm0 mul0r; exact: cone_norm_ge0.
have [y0|ynz] := pselect (y = precone_zero).
  by rewrite y0 cone_norm0 mulr0; exact: cone_norm_ge0.
exact: ptensor_norm_ge.
Qed.

End NormM.

Arguments ptensor_norm_le {R Ar B C}.
Arguments tensor_normM {R Ar B C}.

End Icones_tensor_hom_iso.
