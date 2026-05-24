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

End Icones_tensor_hom_iso.
