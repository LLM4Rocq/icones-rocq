(**md**************************************************************************)
(* # Tensor discharge T2A — Thm 5.13 [tensor_normM] (DONE) + Thm 5.12 skeleton *)
(*                                                                            *)
(* This file DISCHARGES, as a genuine AXIOM-FREE theorem about the concrete   *)
(* [tensor_construct] construction, one of the remaining staged [Parameter]s  *)
(* of [theories/axioms/saft_interface.v]:                                     *)
(*                                                                            *)
(*   tensor_normM    (Paper Thm 5.13 — [‖x ⊗ y‖ = ‖x‖ · ‖y‖])  — PROVED       *)
(*                                                                            *)
(* and, towards Thm 5.12, the AXIOM-FREE "measurability of τ" lemma            *)
(*                                                                            *)
(*   tensor_path  ([s ↦ (β s) ⊗ (γ s)] is a measurable path in [B ⊗ C])       *)
(*                                                                            *)
(* (Paper [lemma:path-tens-to-one], via the reusable Fubini swap              *)
(* [swap_lin_path]) — the stated "last blocker" of                            *)
(*                                                                            *)
(*   tensor_hom_iso  (Paper Thm 5.12 — [(B ⊗ C) ⊸ D ≅ B ⊸ (C ⊸ D)]) — PARTIAL *)
(*                                                                            *)
(* whose element maps [Phi_inner]/[Psi_inner] (with the pointwise laws        *)
(* [Phi_innerE]: [Φ(g)(b)(c) = g(b⊗c)] and [Psi_innerE]: [Ψ(h)(b⊗c) = h(b)(c)]*)
(* and the pure-tensor extensionality [linhom_tensor_ext], constructive Prop  *)
(* 5.14) are PROVED.  The full [icones_iso] packaging is DEFERRED: its only    *)
(* remaining obstruction is the *inverse's norm-decrease* [‖Ψ h‖ ≤ ‖h‖] =      *)
(* the [≥] half of the tensor-norm isometry (pure-tensor norm density), which *)
(* [tensor_path] does NOT unlock — see the footer for the precise statement.  *)
(*                                                                            *)
(* It is AXIOM-FREE relative to the classical [boolp] base ([pselect]/[cid]/  *)
(* extensionality) — NO [Axiom]/[Parameter]/[Admitted], and it does NOT       *)
(* import [saft_interface]: the proved versions are built from scratch, in    *)
(* their own module [Icones_tensor_hom_iso], from the proved [tensor_curry] / *)
(* [tensor_uncurry] of [tensor_construct].                                    *)
(*                                                                            *)
(* The [tensor_normM] signature matches the [saft_interface] arguments        *)
(* exactly: [tensor_normM {R Ar B C}].                                        *)
(*                                                                            *)
(* ## Reusable infrastructure built here                                      *)
(*  - [icones_to_linhom] / [linhom_icones] : the element↔morphism bridges.    *)
(*  - [linhom_comp] : general composition of two [linhom_car] elements.       *)
(*  - [tauL] / [ptensor] / [tensor_curryEp] : local pure tensor + Eq 5.1.     *)
(*  - [line_hom] : the scalar-line [icones_hom 1 (C⊸D)] (dual-test tool).     *)
(*  - [swap_lin_path] / [tensor_path] : the Fubini swap + measurability of τ. *)
(*  - [Phi_inner]/[Psi_inner]/[linhom_tensor_ext] : the Thm 5.12 element maps *)
(*    and constructive pure-tensor extensionality (Prop 5.14).                *)
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

(** ** Thm 5.12 [tensor_hom_iso] — algebraic skeleton of the forward [Φ]

    The element-level forward map [Φ : (B⊗C)⊸D → B⊸(C⊸D)] of Paper
    Thm 5.12 sends [g] to [b ↦ (c ↦ g(b⊗c))].  Its inner value at [b]
    is the general composite [g ∘ τ(b) = linhom_comp g (tauL B C b)],
    with the defining pointwise law [Phi_valE]: [Φ(g)(b)(c) = g(b⊗c)].

    ⚠ DEFERRED — the OUTER measurability/integral-preservation (the
    [icones_hom] fields of [Φ] as a map BETWEEN the hom-cones [(B⊗C)⊸D]
    and [B⊸(C⊸D)]) is the substantial Fubini step of the paper
    ([lemma:path-tens-to-one] + [lemma:swap-lin-path]).  It bottoms out
    in: [s ↦ (β s) ⊗ (γ s)] is a measurable path in [B ⊗ C] (the
    measurability of [τ]).  Establishing THAT requires unfolding the
    *selected* test family of the abstractly-constructed [B ⊗ C =
    wi_obj] (an equaliser of products of the coseparator power [1^J] in
    [tensor_construct] / [representable]) and threading each coordinate
    [j ∈ J = ICones(B, C⊸1)] through a diagonal joint-measurability of
    [j]'s path-preservation.  This deep dive into the [wi_obj] internals
    is the remaining T2A obstruction; [Phi_val]/[Phi_valE] are the proved
    algebraic skeleton on which it would be built.  See the file footer. *)

Section PhiSkeleton.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C D : ICone.type Ar.

(** The inner value of the forward [Φ] at [b]: the integrable linear map
    [c ↦ g(b ⊗ c) = (g ∘ τ(b))], a [linhom_car C D] element. *)
Definition Phi_val (g : linhom_car Ar (tensor B C) D) (b : B) :
    linhom_car Ar C D :=
  linhom_comp g ((tauL B C : icones_hom _ _ _) b).

(** Paper Eq 5.1 at the element level: [Φ(g)(b)(c) = g(b ⊗ c)]. *)
Lemma Phi_valE (g : linhom_car Ar (tensor B C) D) (b : B) (c : C) :
  linhom_fun (Phi_val g b) c = linhom_fun g (ptensor b c).
Proof. by rewrite /Phi_val linhom_compE /ptensor. Qed.

End PhiSkeleton.

Arguments Phi_val {R Ar B C D}.
Arguments Phi_valE {R Ar B C D}.

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

(** ** The Fubini swap [swap_lin_path] — Paper [lemma:swap-lin-path]

    Given a measurable path [Φ : X → (C ⊸ E)] and a UNIT-BALL measurable
    path [γ : X → C] (over the same arity [X]), the *diagonal evaluation*
    [r ↦ (Φ r)(γ r)] is a measurable path in [E].

    The argument mirrors [linhom_functor.v]'s [linhom_map_pres_path]:
    for a selected test [m] of [E] at arity [Y], the bivariate path
    [δ(s, r) := (Φ r)(γ s)] (at the product arity [ar_prod Y X]) is a
    measurable path in [E] — its test-measurability against any [E]-test
    [m'] is obtained by testing [Φ] against the internal-hom test
    [(γ ∘ snd) ▷ m'] at the doubled product arity.  Pulling [m] back over
    [δ] then specialising the index pair to the diagonal
    [(s, r) ↦ (s, ar_prod_cast(s, r))] gives the required joint
    measurability of [(s, r) ↦ m(s, (Φ r)(γ r))]. *)

Section SwapLinPath.
Variables (R : realType) (Ar : MeasSubcat R).
Variables C E : ICone.type Ar.
Variable X : ar_obj Ar.
Variable Φ : ar_carrier Ar X -> linhom_car Ar C E.
Variable γ : path_car Ar X C.
Hypothesis HΦ : is_measurable_path Φ.
Hypothesis γub : cone_norm γ <= 1.

Local Notation pf := (path_fun γ).

(** Paper [lemma:swap-lin-path]: the diagonal evaluation [r ↦ (Φ r)(γ r)]
    is a measurable path in [E].

    Boundedness: [‖(Φ r)(γ r)‖ ≤ ‖Φ r‖ · ‖γ r‖ ≤ MΦ · Mγ].

    Test-measurability: given an [E]-test [m] at arity [Y], we test the
    [C ⊸ E]-path [Φ] (at the path arity [X]) against the internal-hom
    test at the PRODUCT arity [ar_prod Y X], built from the [C]-path
    [γ ∘ snd] (picks the [X]-coordinate) and the [E]-test [m ∘ fst]
    (picks the [Y]-coordinate).  That gives, for [(s'', r) : (ar_prod Y X)
    × X], measurability of
      [(γsnd ▷ mfst)(s'', Φ r) = m(fst s'', (Φ r)(γ (snd s'')))].
    Setting [s'' := ar_prod_cast(s, r)] (the diagonal in the second slot)
    yields [m(s, (Φ r)(γ r))]. *)
Lemma swap_lin_path :
  is_measurable_path (fun r => linhom_fun (Φ r) (pf r)).
Proof.
have [[MΦ HMΦ] HΦm] := HΦ.
have MΦ_ge0 : 0 <= MΦ.
  by apply: le_trans (HMΦ (ar_point Ar X)); exact: cone_norm_ge0.
split.
  exists (MΦ * path_norm γ) => r.
  apply: le_trans (linhom_norm_apply_le (K := MΦ) (HMΦ r) (pf r)) _.
  apply: ler_pM => //; first exact: cone_norm_ge0.
  exact: path_norm_ub.
move=> Y m mM.
(* Reindex [γ] (over [X]) to a path [γsnd] at arity [ar_prod Y X]
   picking the [X]-coordinate. *)
pose γsnd : ar_carrier Ar (ar_prod Ar Y X) -> C := fun q => pf (ar_prod_snd Y X q).
have Hγsnd : is_measurable_path γsnd.
  exact: (reindex_path_measurable (ar_prod_snd Y X) (path_is_path γ)).
pose γA : path_car Ar (ar_prod Ar Y X) C := MkPath Hγsnd.
have γA_ub : cone_norm γA <= 1.
  rewrite /cone_norm /=.
  apply: ge_sup; first exact: path_normset_nonempty.
  move=> _ [q ->] /=.
  rewrite /γsnd /=.
  by apply: le_trans (path_norm_ub γ _) _; exact: γub.
(* Reindex [m] (over [Y]) to a test [mfst] at arity [ar_prod Y X]
   picking the [Y]-coordinate. *)
pose mfst : test_of Ar (ar_prod Ar Y X) E := test_reindex (ar_prod_fst Y X) m.
have mfstM : mcone_M (ar_prod Ar Y X) mfst by exact: mcone_M_comp.
(* Test [Φ] against the internal-hom test [γsnd ▷ mfst] at arity
   [ar_prod Y X]; this is in [Φ]'s measurability structure. *)
have HΦtest := HΦm (ar_prod Ar Y X)
  (linhom_test γA γA_ub mfst mfstM)
  (ex_intro _ γA (ex_intro _ γA_ub
     (ex_intro _ mfst (ex_intro _ mfstM (erefl _))))).
(* Specialise the index pair [(s'', r)] to the diagonal-in-[X]
   [(ar_prod_cast(s, r), r)]. *)
pose ψ (p : (ar_carrier Ar Y * ar_carrier Ar X)%type) :
    (ar_carrier Ar (ar_prod Ar Y X) * ar_carrier Ar X)%type :=
  (ar_prod_cast (p.1, p.2), p.2).
have ψ_meas : measurable_fun
    [set: (ar_carrier Ar Y * ar_carrier Ar X)%type] ψ.
  apply: measurable_fun_pair; last exact: measurable_snd.
  apply: (measurableT_comp (ar_prod_cast_meas Ar Y X)).
  by apply: measurable_fun_pair; [exact: measurable_fst|exact: measurable_snd].
rewrite (_ : (fun p : (ar_carrier Ar Y * ar_carrier Ar X)%type =>
                test_fun m p.1 (linhom_fun (Φ p.2) (pf p.2))) =
             (fun q : (ar_carrier Ar (ar_prod Ar Y X) *
                       ar_carrier Ar X)%type =>
                linhom_test γA γA_ub mfst mfstM q.1 (Φ q.2)) \o ψ).
  apply: (measurable_comp (F := setT) measurableT (subsetT _) HΦtest ψ_meas).
apply: funext => p /=.
rewrite /linhom_test /linhom_test_fun /= /ψ /=.
rewrite /mfst /test_reindex /test_reindex_fun /=.
rewrite /ar_prod_fst /ar_prod_fst_fun ar_prod_castK /=.
rewrite /γA /= /γsnd /= /ar_prod_snd /ar_prod_snd_fun ar_prod_castK /=.
by [].
Qed.

End SwapLinPath.

Arguments swap_lin_path {R Ar C E X} Φ γ HΦ γub.

(** ** The pure-tensor path [tensor_path] — measurability of [τ]

    Paper [lemma:path-tens-to-one].  For UNIT-BALL measurable paths
    [β : X → B] and [γ : X → C], the pointwise pure tensor
    [s ↦ (β s) ⊗ (γ s) = (τ(β s))(γ s)] is a measurable path in [B ⊗ C].

    Since [τ = tauL B C : B → (C ⊸ B⊗C)] is an [icones_hom], it preserves
    the measurable path [β], so [s ↦ τ(β s)] is a measurable path of
    [C ⊸ (B ⊗ C)].  Diagonally evaluating that at the [C]-path [γ] via
    [swap_lin_path] gives the result. *)

Section TensorPath.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : ICone.type Ar.
Variable X : ar_obj Ar.
Variables (β : ar_carrier Ar X -> B) (γ : path_car Ar X C).
Hypothesis Hβ : is_measurable_path β.
Hypothesis γub : cone_norm γ <= 1.

Lemma tensor_path :
  is_measurable_path (fun s => ptensor (β s) (γ s)).
Proof.
(* The path of internal homs [s ↦ τ(β s)] in [C ⊸ (B ⊗ C)]. *)
have HΦ : is_measurable_path
    (fun s => (tauL B C : icones_hom _ _ _) (β s)).
  exact: (mcones_hom_pres_path (icones_hom_mcones (tauL B C)) X β Hβ).
(* The diagonal evaluation [s ↦ (τ(β s))(γ s) = (β s) ⊗ (γ s)]. *)
exact: (swap_lin_path (fun s => (tauL B C : icones_hom _ _ _) (β s)) γ HΦ γub).
Qed.

End TensorPath.

Arguments tensor_path {R Ar B C X} β γ Hβ γub.

(** ** Thm 5.12 [tensor_hom_iso] — the forward/inverse element maps

    The element-level forward [Φ : (B⊗C)⊸D → B⊸(C⊸D)] sends [g] to
    [b ↦ (c ↦ g(b⊗c))]; the inverse [Ψ] sends [h] to the map with
    [Ψ(h)(b⊗c) = h(b)(c)].  Both are built from the proved morphism-level
    [tensor_curry] / [tensor_uncurry] by rescaling into the unit ball
    ([t := ‖·‖+1], [·ₛ := t⁻¹··]) — so the codomain is automatically a
    [linhom_car], and the five [linhom_car]/[icones_hom] structure fields
    of the *inner element* come for free from [tensor_curry]'s codomain
    being an [icones_hom].  The two scalings cancel, giving the clean
    pointwise laws [Phi_innerE] / [Psi_innerE]. *)

(** *** Scaling helpers — the unit-ball rescaling [·ₛ := (‖·‖+1)⁻¹··] *)

Section ScaleHelpers.
Variables (R : realType) (Ar : MeasSubcat R).
Variables C E : ICone.type Ar.
Variable f : linhom_car Ar C E.

Definition lh_t : R := cone_norm f + 1.

Lemma lh_t_pos : 0 < lh_t.
Proof.
by rewrite /lh_t; apply: lt_le_trans ltr01 _; rewrite lerDr cone_norm_ge0.
Qed.

Lemma lh_t_ge0 : 0 <= lh_t. Proof. exact: ltW lh_t_pos. Qed.

Lemma lh_tinv_ge0 : 0 <= lh_t^-1.
Proof. by rewrite invr_ge0 ltW// lh_t_pos. Qed.

Definition lh_tnng : {nonneg R} := NngNum lh_t_ge0.
Definition lh_tinvnng : {nonneg R} := NngNum lh_tinv_ge0.

Definition lh_scaled : linhom_car Ar C E := linhom_scale lh_tinvnng f.

Lemma lh_scaled_norm : cone_norm lh_scaled <= 1.
Proof.
rewrite -[cone_norm lh_scaled]/(linhom_norm lh_scaled) /lh_scaled linhom_normh /=.
rewrite mulrC -ler_pdivlMr ?invr_gt0 ?lh_t_pos // mul1r invrK.
by rewrite /lh_t lerDl ler01.
Qed.

(** [t · t⁻¹ = 1] as a nonneg-scalar identity (for cancelling the two
    rescalings). *)
Lemma lh_t_tinv : (lh_tnng%:num * lh_tinvnng%:num)%:nng = 1%:nng :> {nonneg R}.
Proof. by apply: val_inj => /=; rewrite mulfV// gt_eqF// lh_t_pos. Qed.

End ScaleHelpers.

Arguments lh_t {R Ar C E} f.
Arguments lh_scaled {R Ar C E} f.
Arguments lh_tnng {R Ar C E} f.
Arguments lh_tinvnng {R Ar C E} f.

(** *** The inner forward element [Phi_inner g : B ⊸ (C ⊸ D)] *)

Section PhiInner.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C D : ICone.type Ar.

(** [Phi_inner g := t · (tensor_curry (gₛ as icones_hom))] as a
    [linhom_car B (linhom_car C D)] element, where [gₛ = t⁻¹·g] has
    norm [≤ 1] ([lh_scaled_norm]). *)
Definition Phi_inner (g : linhom_car Ar (tensor B C) D) :
    linhom_car Ar B (linhom_car Ar C D) :=
  linhom_scale (lh_tnng g)
    (icones_to_linhom
       (tensor_curry (linhom_icones (lh_scaled g) (lh_scaled_norm g)))).

(** Paper Eq 5.1: [Φ(g)(b)(c) = g(b ⊗ c)].  The two scalings cancel. *)
Lemma Phi_innerE (g : linhom_car Ar (tensor B C) D) (b : B) (c : C) :
  linhom_fun (linhom_fun (Phi_inner g) b) c = linhom_fun g (ptensor b c).
Proof.
rewrite /Phi_inner /linhom_fun /= /linhom_scale_fun /=.
rewrite (tensor_curryEp (linhom_icones (lh_scaled g) (lh_scaled_norm g)) b c).
rewrite (linhom_iconesE (lh_scaled g) (lh_scaled_norm g) (ptensor b c)).
rewrite /lh_scaled /linhom_fun /= /linhom_scale_fun /=.
rewrite -precone_scale_A.
by rewrite lh_t_tinv precone_scale_1.
Qed.

End PhiInner.

Arguments Phi_inner {R Ar B C D}.
Arguments Phi_innerE {R Ar B C D}.

(** *** The inner inverse element [Psi_inner h : (B⊗C) ⊸ D] *)

Section PsiInner.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C D : ICone.type Ar.

(** [Psi_inner h := t · (tensor_uncurry (hₛ as icones_hom))], with
    [hₛ = t⁻¹·h] of norm [≤ 1]. *)
Definition Psi_inner (h : linhom_car Ar B (linhom_car Ar C D)) :
    linhom_car Ar (tensor B C) D :=
  linhom_scale (lh_tnng h)
    (icones_to_linhom
       (tensor_uncurry (linhom_icones (lh_scaled h) (lh_scaled_norm h)))).

(** Paper Eq 5.1 (inverse): [Ψ(h)(b ⊗ c) = h(b)(c)].

    [tensor_uncurry h'] computes on pure tensors by [tensor_uncurryK] +
    [tensor_curryEp]: [tensor_curry (tensor_uncurry h') = h'], so
    [(tensor_uncurry h')(b⊗c) = (tensor_curry (tensor_uncurry h') b)(c)
    = h'(b)(c)].  The two scalings cancel. *)
Lemma Psi_innerE (h : linhom_car Ar B (linhom_car Ar C D)) (b : B) (c : C) :
  linhom_fun (Psi_inner h) (ptensor b c) =
  linhom_fun (linhom_fun h b) c.
Proof.
rewrite /Psi_inner /linhom_fun /= /linhom_scale_fun /=.
set h' := linhom_icones (lh_scaled h) (lh_scaled_norm h).
have HH := tensor_curryEp (tensor_uncurry h') b c.
rewrite tensor_uncurryK in HH.
rewrite -/(ptensor b c) in HH.
rewrite icones_to_linhomE -HH.
rewrite (linhom_iconesE (lh_scaled h) (lh_scaled_norm h) b).
rewrite /lh_scaled /linhom_fun /= /linhom_scale_fun /=.
rewrite -precone_scale_A.
by rewrite lh_t_tinv precone_scale_1.
Qed.

End PsiInner.

Arguments Psi_inner {R Ar B C D}.
Arguments Psi_innerE {R Ar B C D}.

(** *** Pure-tensor extensionality — constructive Paper Prop 5.14

    A [linhom_car (B⊗C) D] element is determined by its values on pure
    tensors.  Reduce to the morphism-level uniqueness [tensor_curry_inj]
    by rescaling both maps by a COMMON factor [t] into the unit ball,
    converting to [icones_hom] via [linhom_icones]: equal pure-tensor
    values give equal [tensor_curry], hence the two scaled [icones_hom]s
    are equal, hence [t·f1 = t·f2], hence [f1 = f2]. *)

Section LinhomTensorExt.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C D : ICone.type Ar.

Lemma linhom_tensor_ext (f1 f2 : linhom_car Ar (tensor B C) D) :
  (forall (b : B) (c : C),
     linhom_fun f1 (ptensor b c) = linhom_fun f2 (ptensor b c)) ->
  f1 = f2.
Proof.
move=> Hpt.
pose t : R := cone_norm f1 + cone_norm f2 + 1.
have t_pos : 0 < t.
  by rewrite /t; apply: lt_le_trans ltr01 _;
     rewrite lerDr addr_ge0 ?cone_norm_ge0.
have tinv_ge0 : 0 <= t^-1 by rewrite invr_ge0 ltW.
pose tinv : {nonneg R} := NngNum tinv_ge0.
have Hnorm fi : cone_norm fi <= cone_norm f1 + cone_norm f2 ->
    cone_norm (linhom_scale tinv fi) <= 1.
  move=> Hfi.
  rewrite -[cone_norm _]/(linhom_norm (linhom_scale tinv fi)) linhom_normh /=.
  rewrite mulrC -ler_pdivlMr ?invr_gt0 // mul1r invrK.
  by apply: le_trans Hfi _; rewrite /t lerDl ler01.
have H1 : cone_norm (linhom_scale tinv f1) <= 1.
  by apply: Hnorm; rewrite lerDl cone_norm_ge0.
have H2 : cone_norm (linhom_scale tinv f2) <= 1.
  by apply: Hnorm; rewrite lerDr cone_norm_ge0.
(* The two rescaled maps agree on pure tensors, so equal [tensor_curry]. *)
have Hcurry :
    tensor_curry (linhom_icones (linhom_scale tinv f1) H1) =
    tensor_curry (linhom_icones (linhom_scale tinv f2) H2).
  apply: icones_hom_eq => b /=.
  apply: linhom_eq => c.
  rewrite !(tensor_curryEp _ b c).
  rewrite !(linhom_iconesE _ _ (ptensor b c)).
  rewrite /linhom_fun /= /linhom_scale_fun /=.
  by rewrite Hpt.
have Heq := tensor_curry_inj _ _ Hcurry.
(* Equal [icones_hom]s ⇒ equal underlying functions ⇒ [t·f1 = t·f2]. *)
have Hfun : linhom_scale tinv f1 = linhom_scale tinv f2.
  apply: linhom_eq => x.
  by have := f_equal
    (fun (w : icones_hom Ar (tensor B C) D) =>
       cones_hom_fun (mcones_hom_cones (icones_hom_mcones w)) x) Heq.
(* Cancel the common scaling [tinv > 0] by rescaling by [t]. *)
apply: linhom_eq => x.
have := f_equal (fun w : linhom_car Ar (tensor B C) D => linhom_fun w x) Hfun.
rewrite /linhom_fun /= /linhom_scale_fun /= => Hx.
have Ht := f_equal (precone_scale (NngNum (ltW t_pos))) Hx.
move: Ht; rewrite -!precone_scale_A.
have -> : (widen_itv ((NngNum (ltW t_pos))%:num * tinv%:num)%:itv : {nonneg R})
          = 1%:nng.
  by apply: val_inj => /=; rewrite mulfV// gt_eqF.
by rewrite !precone_scale_1.
Qed.

End LinhomTensorExt.

Arguments linhom_tensor_ext {R Ar B C D}.

(** ** Thm 5.12 [tensor_hom_iso] — the forward map [Φ] as an [icones_hom]

    The forward [Φ : (B⊗C)⊸D → B⊸(C⊸D)] sends [g] to [Phi_inner g] (the
    element [b ↦ (c ↦ g(b⊗c))]).  We package the map [g ↦ Phi_inner g] as
    a genuine [icones_hom] between the hom-cones.  EVERY structure field
    reduces, via the pointwise law [Phi_innerE], the pointwise codomain
    structure of [B⊸(C⊸D)] ([linhom_eq], [linhom_test], pointwise sup),
    and the proved [tensor_normM]/[tensor_path], to a fact about [g]
    itself (its own linearity / continuity / norm / path / integral) —
    NO from-scratch sup-ball analysis. *)

Section PhiIConesHom.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C D : ICone.type Ar.

Local Notation BC := (tensor B C).
Local Notation Dom := (linhom_car Ar BC D).
Local Notation Cod := (linhom_car Ar B (linhom_car Ar C D)).

(** The underlying map [Φ : Dom → Cod]. *)
Definition Phi_map (g : Dom) : Cod := Phi_inner g.

(** Extensional principle for [Cod]: two elements are equal iff they
    agree on all [b] then all [c]. *)
Lemma cod_eq (f1 f2 : Cod) :
  (forall (b : B) (c : C),
     linhom_fun (linhom_fun f1 b) c = linhom_fun (linhom_fun f2 b) c) ->
  f1 = f2.
Proof.
by move=> H; apply: linhom_eq => b; apply: linhom_eq => c; exact: H.
Qed.

(** *** Linearity of [Φ] — pure [Phi_innerE] + linearity of [g]. *)
Lemma Phi_linear : is_linear Phi_map.
Proof.
split.
- apply: cod_eq => b c; rewrite /Phi_map Phi_innerE.
  rewrite [linhom_fun (linhom_zero BC D) (ptensor b c)]/linhom_fun /=
          /linhom_zero_fun.
  have ZcodE : linhom_fun (0%PC : Cod) b = (0%PC : linhom_car Ar C D).
    by have [Z0c _ _] := linhom_pre_linear (linhom_pre_of (0%PC : Cod));
       exact: Z0c.
  rewrite ZcodE.
  by rewrite [linhom_fun (0%PC : linhom_car Ar C D) c]/linhom_fun /=
             /linhom_zero_fun.
- move=> g1 g2; apply: cod_eq => b c.
  rewrite /Phi_map Phi_innerE.
  rewrite [linhom_fun (g1 + g2)%PC (ptensor b c)]/linhom_fun /= /linhom_add_fun.
  rewrite -!/(linhom_fun _ (ptensor b c)) -!Phi_innerE.
  rewrite [linhom_fun (Phi_inner g1 + Phi_inner g2)%PC b]/linhom_fun /=
          /linhom_add_fun.
  by rewrite [linhom_fun (_ + _)%PC c]/linhom_fun /= /linhom_add_fun.
- move=> r g; apply: cod_eq => b c.
  rewrite /Phi_map Phi_innerE.
  rewrite [linhom_fun (r *: g)%PC (ptensor b c)]/linhom_fun /= /linhom_scale_fun.
  rewrite -!/(linhom_fun _ (ptensor b c)) -!Phi_innerE.
  rewrite [linhom_fun (r *: Phi_inner g)%PC b]/linhom_fun /= /linhom_scale_fun.
  by rewrite [linhom_fun (_ *: _)%PC c]/linhom_fun /= /linhom_scale_fun.
Qed.

(** *** Norm decrease [‖Φ g‖ ≤ ‖g‖] — via [tensor_normM]. *)
Lemma Phi_norm_le1 (g : Dom) : cone_norm (Phi_map g) <= cone_norm g.
Proof.
rewrite [cone_norm (Phi_map g)]/= [cone_norm g]/=.
apply: linhom_norm_sup_lub => b Hb.
(* ‖Phi g b‖ ≤ ‖g‖ · ‖b‖ ≤ ‖g‖, since (Phi g b)(c) = g(b⊗c). *)
rewrite -[cone_norm (linhom_fun (Phi_map g) b)]/(linhom_norm (linhom_fun (Phi_map g) b)).
apply: linhom_norm_sup_lub => c Hc.
rewrite /Phi_map Phi_innerE.
apply: le_trans (linhom_norm_apply_le (lexx _) (ptensor b c)) _.
rewrite -[cone_norm (ptensor b c)]/(cone_norm (ptensor b c)).
have Hbc : cone_norm (ptensor b c) <= 1.
  apply: le_trans (ptensor_norm_le b c) _.
  by rewrite -[X in _ <= X]mulr1; apply: ler_pM => //; exact: cone_norm_ge0.
rewrite -[X in _ <= X]mulr1.
by apply: ler_wpM2l => //; exact: linhom_norm_ge0.
Qed.

(** *** ω-continuity of [Φ].

    By [linhom_mcone_M_sep] for the codomain [B⊸(C⊸D)] it suffices, for
    an arity-0 test [β ▷ (γ ▷ m)] (with [β] a [B]-path, [γ] a [C]-path,
    [m] a [D]-test), to show both sides have the same value, which is
    [sup_n m(s, u_n((β s)⊗(γ s)))]: the LHS via [linhom_sup_fun_test_sup]
    on the domain [(B⊗C)⊸D] at [(β s)⊗(γ s)], the RHS via
    [linhom_sup_fun_test_sup] on [B⊸(C⊸D)] at [β s] with test [γ ▷ m].
    [Phi_innerE] bridges [Φ(u_n)(β s)(γ s) = u_n((β s)⊗(γ s))]. *)
Lemma Phi_continuous : is_omega_continuous Phi_map.
Proof.
move=> u uch ub1 fuch fub1.
apply: (@linhom_mcone_M_sep _ _ B (linhom_car Ar C D)) => p.
move=> [β [βub [m1 [m1M Hp]]]].
(* [m1] is a test of [C⊸D] in [mcone_M]; since the [C⊸D] test family is
   exactly [linhom_mcone_M], destructure it as [γ ▷ m]. *)
have [γ [γub [m [mM Hm1]]]] : linhom_mcone_M (Y := ar_zero Ar) m1 by exact: m1M.
rewrite Hp /linhom_test /linhom_test_fun /=.
rewrite Hm1 /linhom_test /linhom_test_fun /=.
set s := ar_zero_pt Ar.
(* LHS value: m s (Φ(sup u)(β s)(γ s)) = m s ((sup u)((β s)⊗(γ s))). *)
have LHSe : test_fun m s
    (linhom_fun (linhom_fun (Phi_map (cone_sup_ball u uch ub1)) (path_fun β s))
                (path_fun γ s)) =
    test_fun m s
      (linhom_fun (cone_sup_ball u uch ub1)
         (ptensor (path_fun β s) (path_fun γ s))).
  by rewrite /Phi_map Phi_innerE.
rewrite LHSe.
(* RHS value: (γ ▷ m) s ((sup(Φ∘u))(β s)), via [linhom_sup_fun_test_sup]
   at the [B⊸(C⊸D)] level. *)
have RHSe : test_fun m s
    (linhom_fun
       (linhom_fun (cone_sup_ball (Phi_map \o u) fuch fub1) (path_fun β s))
       (path_fun γ s)) =
    test_fun (linhom_test γ γub m mM) s
      (linhom_fun (cone_sup_ball (Phi_map \o u) fuch fub1) (path_fun β s)).
  by rewrite /linhom_test /linhom_test_fun.
rewrite RHSe.
have RHS_b : linhom_fun (cone_sup_ball (Phi_map \o u) fuch fub1) (path_fun β s) =
    linhom_sup_fun fuch fub1 (path_fun β s) by [].
rewrite RHS_b.
rewrite (linhom_sup_fun_test_sup fuch fub1 (linhom_test γ γub m mM) s
           (path_fun β s)).
(* LHS via [linhom_sup_fun_test_sup] on the domain. *)
have LHS_z : linhom_fun (cone_sup_ball u uch ub1)
    (ptensor (path_fun β s) (path_fun γ s)) =
    linhom_sup_fun uch ub1 (ptensor (path_fun β s) (path_fun γ s)) by [].
rewrite LHS_z.
rewrite (linhom_sup_fun_test_sup uch ub1 m s
           (ptensor (path_fun β s) (path_fun γ s))).
(* Both real-sup sets coincide, via [Phi_innerE] on each [u_n]. *)
congr (sup _).
apply: eq_imagel => n _ /=.
by rewrite /linhom_test /linhom_test_fun /Phi_map Phi_innerE.
Qed.

(** *** Boundedness of [Φ] (operator norm [≤ 1]). *)
Lemma Phi_bounded :
  exists M : R, forall g : Dom, cnorm g <= 1 -> cnorm (Phi_map g) <= M.
Proof. by exists 1 => g Hg; apply: le_trans (Phi_norm_le1 g) _. Qed.

(** *** Measurable-path preservation of [Φ].

    For a measurable path [G] of [(B⊗C)⊸D] we must show [r ↦ Φ(G r)] is
    a measurable path of [B⊸(C⊸D)].  By the codomain test family it
    suffices, for a unit-ball [B]-path [β], a unit-ball [C]-path [γ] (both
    at arity [Y]) and a [D]-test [m], to prove
      [(s, r) ↦ m(s, (G r)((β s)⊗(γ s)))]
    measurable on [Y × W].  We test the [(B⊗C)⊸D]-path [G] against the
    [(B⊗C)]-test [θ ▷ m], where [θ s := (β s)⊗(γ s)] is the [tensor_path]
    (measurable by [tensor_path]); pulling back along the diagonal in [s]
    gives exactly the required measurability. *)
Lemma Phi_pres_path
    (W : ar_obj Ar) (G : ar_carrier Ar W -> Dom) :
  is_measurable_path G ->
  is_measurable_path (fun r => Phi_map (G r)).
Proof.
move=> HG.
have [[MG HMG] HGm] := HG.
have MG_ge0 : 0 <= MG.
  by apply: le_trans (HMG (ar_point Ar W)); exact: cone_norm_ge0.
split.
  exists MG => r.
  by apply: le_trans (Phi_norm_le1 (G r)) _; exact: HMG.
move=> Y p [β [βub [m1 [m1M ->]]]].
have [γ [γub [m [mM Hm1]]]] : linhom_mcone_M (Y := Y) m1 by exact: m1M.
(* The [(B⊗C)]-path [θ s = (β s)⊗(γ s)] at arity [Y], of norm ≤ 1. *)
have Hθ : is_measurable_path (fun s => ptensor (path_fun β s) (path_fun γ s)).
  exact: (tensor_path (path_fun β) γ (path_is_path β) γub).
pose θ : path_car Ar Y BC := MkPath Hθ.
have θub : cone_norm θ <= 1.
  rewrite /cone_norm /=.
  apply: ge_sup; first exact: path_normset_nonempty.
  move=> _ [s ->] /=.
  apply: le_trans (ptensor_norm_le (path_fun β s) (path_fun γ s)) _.
  rewrite -[X in _ <= X]mulr1.
  apply: ler_pM; [exact: cone_norm_ge0|exact: cone_norm_ge0| |].
  - by apply: le_trans (path_norm_ub β s) _; exact: βub.
  - by apply: le_trans (path_norm_ub γ s) _; exact: γub.
(* Test [G] (a path of [(B⊗C)⊸D]) against the [(B⊗C)⊸D]-test [θ ▷ m]:
   this is in [G]'s measurability structure and yields measurability of
   [(s, r) ↦ m(s, (G r)((β s)⊗(γ s)))] directly. *)
have HGtest := HGm Y (linhom_test θ θub m mM)
  (ex_intro _ θ (ex_intro _ θub (ex_intro _ m (ex_intro _ mM (erefl _))))).
rewrite (_ : (fun p0 : (ar_carrier Ar Y * ar_carrier Ar W)%type =>
     linhom_test β βub m1 m1M p0.1 (Phi_map (G p0.2))) =
     (fun p0 => linhom_test θ θub m mM p0.1 (G p0.2))).
  exact: HGtest.
apply: funext => q.
rewrite /linhom_test /linhom_test_fun /=.
rewrite Hm1 /linhom_test /linhom_test_fun /=.
by rewrite /Phi_map Phi_innerE.
Qed.

(** [Φ] packaged as a [cones_hom] and an [mcones_hom]. *)
Definition Phi_cones : cones_hom Dom Cod :=
  ConesHom Phi_map Phi_linear Phi_continuous Phi_norm_le1.

Definition Phi_mcones : mcones_hom Ar Dom Cod :=
  MkMConesHom Phi_cones (fun W G HG => Phi_pres_path (W:=W) (G:=G) HG).

(** *** Integral-preservation of [Φ].

    By [icone_integral_eqP] on [B⊸(C⊸D)] it suffices to verify the
    Pettis specification: for an arity-0 test [β ▷ (γ ▷ m)] of the
    codomain, [(β▷(γ▷m))(s, Φ(∫G)) = fine ∫ (β▷(γ▷m))(s, Φ(G r)) dµ].  By
    [Phi_innerE] both sides rewrite to the [(B⊗C)]-test [θ ▷ m] (with
    [θ] the [tensor_path]) applied to [∫G] resp. [G r], so the identity
    is exactly the Pettis specification of [∫G] in [(B⊗C)⊸D] against the
    test [θ ▷ m] — i.e. [icone_integralP] for [G]. *)
Lemma Phi_pres_int
    (W : ar_obj Ar) (G : ar_carrier Ar W -> Dom)
    (HG : is_measurable_path G) (µ : fmeas R (ar_carrier Ar W)) :
  cones_hom_fun (mcones_hom_cones Phi_mcones) (icone_integral G HG µ) =
  icone_integral
    (fun r => cones_hom_fun (mcones_hom_cones Phi_mcones) (G r))
    (mcones_hom_pres_path Phi_mcones W G HG) µ.
Proof.
apply: icone_integral_eqP => p pM s.
move: pM => [β [βub [m1 [m1M Hp]]]].
have [γ [γub [m [mM Hm1]]]] : linhom_mcone_M (Y := ar_zero Ar) m1 by exact: m1M.
(* The [(B⊗C)]-path [θ s' = (β s')⊗(γ s')], norm ≤ 1. *)
have Hθ : is_measurable_path (fun s' => ptensor (path_fun β s') (path_fun γ s')).
  exact: (tensor_path (path_fun β) γ (path_is_path β) γub).
pose θ : path_car Ar (ar_zero Ar) BC := MkPath Hθ.
have θub : cone_norm θ <= 1.
  rewrite /cone_norm /=.
  apply: ge_sup; first exact: path_normset_nonempty.
  move=> _ [s' ->] /=.
  apply: le_trans (ptensor_norm_le (path_fun β s') (path_fun γ s')) _.
  rewrite -[X in _ <= X]mulr1.
  apply: ler_pM; [exact: cone_norm_ge0|exact: cone_norm_ge0| |].
  - by apply: le_trans (path_norm_ub β s') _; exact: βub.
  - by apply: le_trans (path_norm_ub γ s') _; exact: γub.
(* The Pettis spec of [∫G] in [(B⊗C)⊸D] against the [(B⊗C)⊸D]-test [θ ▷ m]. *)
have HGint := icone_integralP G HG µ (linhom_test θ θub m mM)
  (ex_intro _ θ (ex_intro _ θub (ex_intro _ m (ex_intro _ mM (erefl _)))))
  s.
(* LHS: (β▷(γ▷m))(s, Φ(∫G)) = m(s, (∫G)(θ s)) = (θ▷m)(s, ∫G). *)
have ->: test_fun p s
    (cones_hom_fun (mcones_hom_cones Phi_mcones) (icone_integral G HG µ)) =
    test_fun (linhom_test θ θub m mM) s (icone_integral G HG µ).
  rewrite Hp /linhom_test /linhom_test_fun /=.
  rewrite Hm1 /linhom_test /linhom_test_fun /=.
  by rewrite /Phi_map Phi_innerE.
rewrite HGint.
(* RHS: the integrand [(β▷(γ▷m))(s, Φ(G r)) = (θ▷m)(s, G r)] pointwise. *)
congr (fine _); apply: eq_integral => r _; congr (_%:E).
rewrite Hp /linhom_test /linhom_test_fun /=.
rewrite Hm1 /linhom_test /linhom_test_fun /=.
by rewrite /Phi_map Phi_innerE.
Qed.

(** [Φ] packaged as a genuine [icones_hom] (Thm 5.12 forward). *)
Definition Phi_icones : icones_hom Ar Dom Cod :=
  MkIConesHom Phi_mcones Phi_pres_int.

Lemma Phi_iconesE (g : Dom) (b : B) (c : C) :
  linhom_fun
    (linhom_fun
       (cones_hom_fun (mcones_hom_cones (icones_hom_mcones Phi_icones)) g) b) c
  = linhom_fun g (ptensor b c).
Proof. by rewrite -[cones_hom_fun _ _]/(Phi_map g) /Phi_map Phi_innerE. Qed.

End PhiIConesHom.

Arguments Phi_map {R Ar B C D}.
Arguments Phi_icones {R Ar B C D}.
Arguments Phi_iconesE {R Ar B C D}.


(**md**************************************************************************)
(* # STATUS — T2 (Thm 5.12 [tensor_hom_iso])                                   *)
(*                                                                            *)
(* DONE (axiom-free; verified Print Assumptions = the 3 classical [boolp]     *)
(* axioms only, no [saft_interface] symbols):                                 *)
(*  - Thm 5.13 [tensor_normM] : [‖x ⊗ y‖ = ‖x‖ · ‖y‖], via [line_hom] +       *)
(*    [np_pairing] (dual pairing) + Prop 3.11 adherence.                      *)
(*  - [swap_lin_path] (Paper [lemma:swap-lin-path], the "Fubini swap") and    *)
(*    [tensor_path] (Paper [lemma:path-tens-to-one], "measurability of τ"):   *)
(*    for unit-ball measurable [β : X → B], [γ : X → C], the pure tensor      *)
(*    [s ↦ (β s) ⊗ (γ s)] is a measurable path in [B ⊗ C].                    *)
(*  - Thm 5.12 element maps + laws: [Phi_inner]/[Phi_innerE]                   *)
(*    ([Φ(g)(b)(c) = g(b⊗c)]), [Psi_inner]/[Psi_innerE]                        *)
(*    ([Ψ(h)(b⊗c) = h(b)(c)]); and [linhom_tensor_ext] (constructive Paper    *)
(*    Prop 5.14: a [linhom_car (B⊗C) D] is determined by its pure-tensor       *)
(*    values, via [tensor_curry_inj]).                                        *)
(*  - ★ Thm 5.12 FORWARD as a genuine [icones_hom]: [Phi_icones] /            *)
(*    [Phi_iconesE], the map [Φ : (B⊗C)⊸D → B⊸(C⊸D)] with all five            *)
(*    structure fields proved (linear / ω-cont / norm-≤1 / path / integral).  *)
(*    Each field reduces — via [Phi_innerE] + the pointwise codomain          *)
(*    structure of [B⊸(C⊸D)] + the proved [tensor_normM]/[tensor_path] — to   *)
(*    a fact about [g] itself; in particular ω-continuity goes through        *)
(*    [linhom_mcone_M_sep] + two [linhom_sup_fun_test_sup] applications, and   *)
(*    path/integral preservation test [g] against the [(B⊗C)]-test [θ ▷ m]    *)
(*    with [θ] the [tensor_path].  NO from-scratch sup-ball analysis.         *)
(*  - Reusable: [icones_to_linhom], [linhom_icones], [linhom_comp],           *)
(*    [tauL]/[ptensor]/[tensor_curryEp], [line_hom], [Phi_val]/[Phi_valE].    *)
(*                                                                            *)
(* RESOLVED (was previously thought to be the blocker): the inverse's          *)
(* *norm-decrease* [‖Ψ h‖ ≤ ‖h‖] IS provable, by identifying [Psi_inner h]    *)
(* with the EXACT [‖h‖]-rescaling [‖h‖ · icones_to_linhom(tensor_uncurry      *)
(* (‖h‖⁻¹·h))] (via [linhom_tensor_ext], the two agree on pure tensors) whose *)
(* operator norm is [‖h‖ · ‖icones_to_linhom(…)‖ ≤ ‖h‖ · 1] by                *)
(* [icones_to_linhom_norm_le1] — the [‖h‖]-scaling (NOT [‖h‖+1]) keeps the    *)
(* built-in norm-≤1 of [tensor_uncurry].  [Ψ]'s linearity and ω-continuity    *)
(* likewise reduce to pure tensors via [linhom_tensor_ext] (equalities).      *)
(*                                                                            *)
(* RESIDUAL OBSTRUCTION (blocks the full [icones_iso]) — the *inverse [Ψ]'s    *)
(* PATH- and INTEGRAL-preservation* fields.  [Ψ : B⊸(C⊸D) → (B⊗C)⊸D].  Its    *)
(* codomain [(B⊗C)⊸D] is tested against the family [{θ ▷ m}] for an           *)
(* ARBITRARY measurable [(B⊗C)]-path [θ]; path-preservation needs, for a      *)
(* measurable path [H] of [B⊸(C⊸D)], joint measurability of                   *)
(*   [(s, r) ↦ m(s, (Ψ (H r))(θ s))]                                          *)
(* where [θ s] is a GENERAL element of [B ⊗ C] (not a pure tensor) and        *)
(* [Ψ (H r) = ‖H r‖ · tensor_uncurry((H r)')] is the SAFT mediator of         *)
(* [tensor_construct], whose value at non-pure [θ s] is opaque ([cid]-built,  *)
(* not natural/measurable in the input [H r]).  Unlike [Φ] — whose DOMAIN     *)
(* tests reduce to pure tensors via [tensor_path], so its path/integral       *)
(* fields close — [Ψ]'s CODOMAIN tests do NOT reduce to pure tensors:         *)
(* [Psi_innerE]/[linhom_tensor_ext] control [Ψ(h)] only on pure tensors,      *)
(* whereas these two fields quantify over non-pure [z ∈ B ⊗ C].  Closing      *)
(* them needs EITHER a pure-tensor *path/measure density* on [B ⊗ C] (read    *)
(* each [j ∈ J = ICones(B, C⊸1)] coordinate of [tensor_incl z]; a separate    *)
(* [wi_obj]-internals theorem) OR a joint-in-[r] measurable family of the     *)
(* [tensor_uncurry] mediators.  Without [Ψ]'s path/integral fields the         *)
(* [icones_iso] assembly [icones_iso_of_cancel Φ Ψ] is blocked; the round-     *)
(* trips [Ψ∘Φ = id]/[Φ∘Ψ = id] themselves follow from                         *)
(* [Phi_innerE]/[Psi_innerE] + [linhom_tensor_ext].                           *)
(******************************************************************************)

End Icones_tensor_hom_iso.
