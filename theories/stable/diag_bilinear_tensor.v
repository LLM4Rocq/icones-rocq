(**md**************************************************************************)
(** * Diagonal bilinear stability bridge — SCones ↔ ICones-tensor

    This file delivers the "diagonal bilinear" stability bridge needed by
    the generic CBV stage of [Yfix_arr_g] (Bang-fix at [eD ne_fix]); it
    was originally also consumed by the CBN headline
    [ex_geom_CBN_mass_one] (and friends), now preserved on the
    [cbn-track] branch:

    if [K : G → !A] is meas-stable and [Φ : G ⊗ !A → !B] is bilinear
    (i.e., an [icones_hom]), then [g ↦ Φ(g ⊗ K g)] is meas-stable.

    The recipe (research #181) is pure structural composition using the
    tensor↔internal-hom adjunction (Thm 5.12): we move to a curried form
    where elementwise reasoning works, via [tensor_curryE]:

      g ↦ Φ(g ⊗p K g)
        = linhom_fun ((tensor_curry Φ) g) (K g)              -- Thm 5.12
        = ev_fun ⟨ (linhom_to_stablehom ∘ ders) (tensor_curry Φ) g, K g ⟩
        = ev_fun ∘ spair (Ψ', K)

    where [Ψ' := λ g. linhom_to_stablehom ((tensor_curry Φ) g)].

    Contents:

    - **M1**  [linhom_to_stablehom] — the lift [linhom_car Ar B C →
      stablehom B C] (pointwise [sc_clamp]) and its key property
      [linhom_to_stablehom_meas_stable]: as a function between the
      [ICone.type Ar] carriers, the lift is itself stable-and-measurable.
      Paper Lemma 7.31 lifted to the internal-hom level.

    - **M2**  [meas_stable_comp_lin]: composing a meas-stable map with
      an [icones_hom] (post or pre) is meas-stable.

    - **M3**  [spair_meas_stable]: the pairing [g ↦ ⟨f g, K g⟩] of two
      meas-stable maps is meas-stable (CCC pairing via [scones_tuple]),
      with the diagonal [id_spair_meas_stable] ([g ↦ ⟨g, K g⟩]) derived
      from it at [f = id] ([meas_stable_id]).

    - **M4**  [meas_stable_diag_bilinear_tensor] — THE deliverable.
      Assembles M1 + M2 + M3 + [tensor_curryE] + [ev_meas_stable]. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import measurable_structure measurable_function.

Require Import Icones.prelude.classical_extra.
Require Import Icones.prelude.nonneg_extra.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.omega_general.
Require Import Icones.cones.cone_cat.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.path.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_cat.
Require Import Icones.homs.linhom.
Require Import Icones.homs.tensor.
Require Import Icones.stable.totmono.
Require Import Icones.stable.stablehom.
Require Import Icones.stable.compose.
Require Import Icones.stable.scones_cat.
Require Import Icones.stable.scones_ccc.
Require Import Icones.stable.stab_lin_swap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** M1 — the lift [linhom_car Ar B C → stablehom B C]

    A linear continuous map [h : B → C] is in particular meas-stable
    ([linhom_meas_stable], paper Lemma 7.31 at the pointwise level).
    We package it as a [stablehom B C] by clamping off the unit ball.

    The key M1 deliverable is [linhom_to_stablehom_meas_stable]: the
    lift, viewed as a function between the [ICone.type Ar] carriers
    [linhom_car Ar B C → stablehom B C], is itself stable-and-measurable.
    This is the "internal-hom" version of paper Lemma 7.31. *)

Section LinhomToStablehom.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : ICone.type Ar.
Local Open Scope precone_scope.

(** The lift, point-level 0-extended off the unit ball. *)
Definition linhom_to_stablehom (h : linhom_car Ar B C) : stablehom B C :=
  MkStablehom (sc_clamp (linhom_fun h))
              (sc_clamp_meas_stable (linhom_meas_stable h))
              (sc_clamp_offball_field _).

(** Pointwise computation rule: on the unit ball, the lift is the
    underlying [linhom_fun]; off the ball it vanishes. *)
Lemma linhom_to_stablehom_E (h : linhom_car Ar B C) (x : B) :
  cone_norm x <= 1 ->
  sh_fun (linhom_to_stablehom h) x = linhom_fun h x.
Proof. by move=> Hx; rewrite /linhom_to_stablehom /= (sc_clamp_ball Hx). Qed.

Lemma linhom_to_stablehom_off (h : linhom_car Ar B C) (x : B) :
  ~~ (cone_norm x <= 1) ->
  sh_fun (linhom_to_stablehom h) x = precone_zero.
Proof. by move=> Hx; rewrite /linhom_to_stablehom /= (sc_clamp_offball Hx). Qed.

End LinhomToStablehom.

Arguments linhom_to_stablehom {R Ar B C}.
Arguments linhom_to_stablehom_E {R Ar B C} h x.
Arguments linhom_to_stablehom_off {R Ar B C} h x.

(** ** Linearity of the lift

    The cone operations on [linhom_car Ar B C] and on [stablehom B C] are
    both pointwise on the unit ball.  Since both also vanish off the unit
    ball ([sc_clamp]/[sh_offball]), the lift commutes with [0], [+] and
    nonneg scaling [r *: -]. *)

Section LinhomToStablehomLinear.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : ICone.type Ar.
Local Open Scope precone_scope.

Lemma linhom_to_stablehom_0 :
  linhom_to_stablehom (0%PC : linhom_car Ar B C) = (0%PC : stablehom B C).
Proof.
apply: stablehom_eq => x.
rewrite -[(0%PC : stablehom B C)]/(sh_zero B C) sh_zeroE.
have [Hx | Hx] := boolP (cone_norm x <= 1).
  rewrite (linhom_to_stablehom_E _ _ Hx).
  by rewrite -[(0%PC : linhom_car Ar B C)]/(linhom_zero B C).
by rewrite (linhom_to_stablehom_off _ _ Hx).
Qed.

Lemma linhom_to_stablehom_D (h1 h2 : linhom_car Ar B C) :
  linhom_to_stablehom (h1 + h2)%PC =
  (linhom_to_stablehom h1 + linhom_to_stablehom h2)%PC.
Proof.
apply: stablehom_eq => x.
rewrite -[(linhom_to_stablehom h1 + linhom_to_stablehom h2)%PC]
  /(sh_add (linhom_to_stablehom h1) (linhom_to_stablehom h2)) sh_addE.
have [Hx | Hx] := boolP (cone_norm x <= 1); last first.
  rewrite (linhom_to_stablehom_off _ _ Hx).
  rewrite (linhom_to_stablehom_off h1 _ Hx).
  by rewrite (linhom_to_stablehom_off h2 _ Hx) precone_add0.
rewrite (linhom_to_stablehom_E _ _ Hx).
rewrite (linhom_to_stablehom_E h1 _ Hx).
rewrite (linhom_to_stablehom_E h2 _ Hx).
rewrite -[(h1 + h2)%PC]/(linhom_add h1 h2).
by rewrite /linhom_fun /= /linhom_add_fun.
Qed.

Lemma linhom_to_stablehom_Z (r : {nonneg R}) (h : linhom_car Ar B C) :
  linhom_to_stablehom (r *: h)%PC = (r *: linhom_to_stablehom h)%PC.
Proof.
apply: stablehom_eq => x.
rewrite -[(r *: linhom_to_stablehom h)%PC]
  /(sh_scale r (linhom_to_stablehom h)) sh_scaleE.
have [Hx | Hx] := boolP (cone_norm x <= 1); last first.
  rewrite (linhom_to_stablehom_off _ _ Hx).
  by rewrite (linhom_to_stablehom_off h _ Hx) precone_scale_0r.
rewrite (linhom_to_stablehom_E _ _ Hx).
rewrite (linhom_to_stablehom_E h _ Hx).
rewrite -[(r *: h)%PC]/(linhom_scale r h).
by rewrite /linhom_fun /= /linhom_scale_fun.
Qed.

Lemma linhom_to_stablehom_linear :
  is_linear (linhom_to_stablehom : linhom_car Ar B C -> stablehom B C).
Proof.
split; [exact: linhom_to_stablehom_0
       | exact: linhom_to_stablehom_D
       | exact: linhom_to_stablehom_Z].
Qed.

End LinhomToStablehomLinear.

Arguments linhom_to_stablehom_linear {R Ar B C}.

(** ** Norm bound

    The lift is norm-decreasing: [cone_norm (linhom_to_stablehom h) ≤
    cone_norm h].  Indeed, both sides are the sup of [cnorm (linhom_fun h
    x)] over the unit ball of [B] (the [stablehom] [sh_norm] computed via
    [sc_clamp] coincides on the ball with the [linhom_car] [linhom_norm]). *)

Section LinhomToStablehomNorm.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : ICone.type Ar.
Local Open Scope precone_scope.

Lemma linhom_to_stablehom_norm_le (h : linhom_car Ar B C) :
  cone_norm (linhom_to_stablehom h) <= cone_norm h.
Proof.
rewrite -[cone_norm (linhom_to_stablehom h)]
  /(sh_norm (linhom_to_stablehom h)).
apply: sh_norm_lub => x Hx.
rewrite (linhom_to_stablehom_E h _ Hx).
rewrite -[cone_norm h]/(linhom_norm h).
exact: linhom_norm_ub.
Qed.

Lemma linhom_to_stablehom_bounded :
  exists M : R, forall h : linhom_car Ar B C,
    cone_norm h <= 1 -> cone_norm (linhom_to_stablehom h) <= M.
Proof.
exists 1 => h Hh.
exact: le_trans (linhom_to_stablehom_norm_le h) Hh.
Qed.

End LinhomToStablehomNorm.

Arguments linhom_to_stablehom_norm_le {R Ar B C} h.

(** ** ω-continuity of the lift

    The unit-ball sup in [linhom_car] is the pointwise sup ([linhom_sup_ball]
    is built from [linhom_sup_fun], which on the ball computes pointwise).
    The unit-ball sup in [stablehom] is also the pointwise sup ([sh_sup_fun]
    is the [cone_sup_ball] of the per-point chain).  Hence the lift commutes
    with the unit-ball sup. *)

Section LinhomToStablehomContinuous.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : ICone.type Ar.
Local Open Scope precone_scope.

(** ω-continuity on the unit ball of [linhom_car]. *)
Lemma linhom_to_stablehom_continuous :
  is_omega_continuous
    (linhom_to_stablehom : linhom_car Ar B C -> stablehom B C).
Proof.
move=> u uch ub1 fuch fub1.
apply: stablehom_eq => x.
have [Hx | Hx] := boolP (cone_norm x <= 1); last first.
  (* Off-ball [x]: both sides are 0 (every stablehom in sight has the
     [sh_offball] field). *)
  rewrite (linhom_to_stablehom_off _ _ Hx).
  apply/esym.
  exact: sh_offball (cone_sup_ball (linhom_to_stablehom \o u) fuch fub1) _ Hx.
(* On-ball [x]: the LHS is [linhom_fun S x] where [S := cone_sup_ball u uch
   ub1] is the [linhom_car]-sup; the RHS is the [stablehom]-sup applied at
   [x].  Both reduce to the pointwise sup of [n ↦ linhom_fun (uₙ) x]. *)
rewrite (linhom_to_stablehom_E _ _ Hx).
(* Image chain in [D]. *)
set v := fun n => linhom_fun (u n) x.
have vch : forall n, precone_le (v n) (v n.+1).
  by move=> n; exact: linhom_le_pointwise (uch n) x.
have vb1 : forall n, cone_norm (v n) <= 1.
  move=> n; apply: (le_trans (linhom_norm_ub (u n) x Hx)).
  by rewrite -[linhom_norm (u n)]/(cone_norm (u n)); exact: ub1.
(* LHS = [cone_sup_ball v vch vb1]. *)
have LHSE : linhom_fun (cone_sup_ball u uch ub1) x = cone_sup_ball v vch vb1.
  rewrite -[cone_sup_ball u uch ub1 : linhom_car Ar B C]
    /(linhom_sup_ball _ uch ub1).
  rewrite -[linhom_fun (linhom_sup_ball _ uch ub1) x]
    /(linhom_sup_fun uch ub1 x).
  rewrite (@linhom_sup_fun_unitE R Ar B C u uch ub1 x Hx).
  rewrite (@linhom_sup_unitE R Ar B C u uch ub1 x Hx).
  apply: precone_le_anti; apply: cone_sup_ball_lub => n;
    exact: cone_sup_ball_ub.
rewrite LHSE.
(* RHS = [cone_sup_ball v ...] via the stablehom sup. *)
have ch : forall n, sh_fun ((linhom_to_stablehom \o u) n) x <=p
                    sh_fun ((linhom_to_stablehom \o u) n.+1) x.
  by move=> n; exact: sh_le_pointwise (fuch n) x.
have b1 : forall n, cnorm (sh_fun ((linhom_to_stablehom \o u) n) x) <= 1.
  move=> n; rewrite /comp /=.
  apply: (le_trans (sh_norm_ub (linhom_to_stablehom (u n)) x Hx)).
  by rewrite -[sh_norm _]/(cone_norm (linhom_to_stablehom (u n))); exact: fub1.
rewrite -[cone_sup_ball (linhom_to_stablehom \o u) fuch fub1
        : stablehom B C] /(@sh_sup R Ar B C _ fuch fub1).
rewrite -[sh_fun (@sh_sup R Ar B C _ fuch fub1) x]
  /(@sh_sup_fun R Ar B C _ fuch fub1 x).
rewrite (@sh_sup_fun_unitE R Ar B C _ fuch fub1 x Hx ch b1).
(* Both [cone_sup_ball] over the same diagonal chain, modulo
   the [linhom_to_stablehom_E] equality (defeq on ball). *)
apply: precone_le_anti.
- apply: cone_sup_ball_lub => n.
  have : sh_fun ((linhom_to_stablehom \o u) n) x = v n.
    by rewrite /comp /v (linhom_to_stablehom_E _ _ Hx).
  move=> <-.
  exact: cone_sup_ball_ub.
- apply: cone_sup_ball_lub => n.
  have : v n = sh_fun ((linhom_to_stablehom \o u) n) x.
    by rewrite /comp /v (linhom_to_stablehom_E _ _ Hx).
  move=> <-.
  exact: cone_sup_ball_ub.
Qed.

End LinhomToStablehomContinuous.

Arguments linhom_to_stablehom_continuous {R Ar B C}.

(** ** Path preservation of the lift

    A measurable unit-ball [linhom_car]-path [η : X → linhom_car Ar B C]
    yields a measurable [stablehom B C]-path [r ↦ linhom_to_stablehom (η r)].

    The stablehom test family ([sh_mcone_M]) and the linhom test family
    ([linhom_mcone_M]) have the same shape: both parametrised by a
    unit-ball [B]-path [γ] and a [C]-test [m].  On the ball, the stablehom
    test body coincides with the linhom one (via [linhom_to_stablehom_E]),
    so the joint measurability transports. *)

Section LinhomToStablehomPath.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : ICone.type Ar.
Local Open Scope precone_scope.

Lemma linhom_to_stablehom_pres_path
    (X : ar_obj Ar) (η : ar_carrier Ar X -> linhom_car Ar B C) :
  (forall r, cone_norm (η r) <= 1) ->
  is_measurable_path (Ar:=Ar) (C:=linhom_car Ar B C) η ->
  is_measurable_path (Ar:=Ar) (C:=stablehom B C)
    (fun r => linhom_to_stablehom (η r)).
Proof.
move=> Hηb Hη; split.
  (* Norm bound: the lift is norm-decreasing. *)
  exists 1 => r.
  exact: le_trans (linhom_to_stablehom_norm_le (η r)) (Hηb r).
move=> Y P PM.
(* Stablehom tests on Y are [sh_test γ γub m mM] (shape from [sh_mcone_M]). *)
case: PM => γ [γub [m [mM HP]]].
rewrite HP.
(* The test body. *)
have HE :
  (fun p : (ar_carrier Ar Y * ar_carrier Ar X)%type =>
     sh_test γ γub m mM p.1 (linhom_to_stablehom (η p.2))) =
  (fun p => test_fun m p.1 (linhom_fun (η p.2) (path_fun γ p.1))).
  apply: funext => p.
  have Hγs : cone_norm (path_fun γ p.1) <= 1.
    by apply: le_trans (path_norm_ub _ _) γub.
  rewrite -[sh_test γ γub m mM p.1 (linhom_to_stablehom (η p.2))]
    /(test_fun m p.1
        (sh_fun (linhom_to_stablehom (η p.2)) (path_fun γ p.1))).
  by rewrite (linhom_to_stablehom_E (η p.2) (path_fun γ p.1) Hγs).
rewrite HE.
(* The same body via a linhom test against [η]. *)
have [_ Hηm] := Hη.
have HinM : mcone_M Y (linhom_test γ γub m mM : test_of Ar Y _).
  by exists γ, γub, m, mM.
exact: (Hηm Y (linhom_test γ γub m mM) HinM).
Qed.

End LinhomToStablehomPath.

Arguments linhom_to_stablehom_pres_path {R Ar B C X η}.

(** ** The headline: the lift is meas-stable

    Combining [linhom_to_stablehom_linear] (totmono via linear),
    [linhom_to_stablehom_bounded], [linhom_to_stablehom_continuous] (Scott
    on the unit ball via [linear_scott_unit]), and
    [linhom_to_stablehom_pres_path]. *)

Section LinhomToStablehomMeasStable.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : ICone.type Ar.

Lemma linhom_to_stablehom_meas_stable :
  is_meas_stable (linhom_to_stablehom : linhom_car Ar B C -> stablehom B C).
Proof.
split.
  split.
  - exact: (linear_totmono _ linhom_to_stablehom_linear).
  - exact: linhom_to_stablehom_bounded.
  - apply: linear_scott_unit.
    + exact: linhom_to_stablehom_linear.
    + exact: linhom_to_stablehom_continuous.
move=> X η Hηb Hη.
exact: (linhom_to_stablehom_pres_path Hηb Hη).
Qed.

End LinhomToStablehomMeasStable.

Arguments linhom_to_stablehom_meas_stable {R Ar B C}.

(** ** M2 — composition of an [icones_hom] with a meas-stable map

    An [icones_hom] is meas-stable ([icones_meas_stable], paper Lemma
    7.31 at the morphism level) and norm-decreasing ([cones_hom_norm_le1]).
    Both pre- and post- composition with meas-stable maps land within
    the closure for [meas_stable_comp] of [stable/compose.v]. *)

Section MeasStableCompLin.
Variables (R : realType) (Ar : MeasSubcat R).

(** Post-composition: [g ∘ f] for [f : icones_hom B C] and
    [g : C → D] meas-stable. *)
Lemma meas_stable_comp_post (B C D : ICone.type Ar)
    (f : icones_hom Ar B C) (g : C -> D) :
  is_meas_stable g ->
  is_meas_stable (fun x => g (f x)).
Proof.
move=> Hg.
apply: (meas_stable_comp (cones_hom_fun
  (mcones_hom_cones (icones_hom_mcones f))) g).
- exact: icones_meas_stable.
- exact: Hg.
- move=> x Hx; apply: le_trans Hx; exact: cones_hom_norm_le1.
Qed.

(** Pre-composition: [g ∘ f] for [f : G → B] meas-stable and
    [g : icones_hom B C]. *)
Lemma meas_stable_comp_pre (G B C : ICone.type Ar)
    (f : G -> B) (g : icones_hom Ar B C) :
  is_meas_stable f ->
  (forall x, cone_norm x <= 1 -> cone_norm (f x) <= 1) ->
  is_meas_stable (fun x => g (f x)).
Proof.
move=> Hf Hfb.
apply: (meas_stable_comp f
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones g)))).
- exact: Hf.
- exact: icones_meas_stable.
- exact: Hfb.
Qed.

End MeasStableCompLin.

Arguments meas_stable_comp_post {R Ar B C D}.
Arguments meas_stable_comp_pre {R Ar G B C}.

(** ** M3 — the diagonal pairing into [sprod]

    For meas-stable [f₁ : G → A] and [f₂ : G → B], the diagonal pairing
    [g ↦ ⟨f₁ g, f₂ g⟩ : G → sprod A B] is meas-stable, proved directly
    (componentwise on [sprod = icones_prod (sprod_fam C A)]).

    Total monotonicity by the product (7.1) [cones_prod_le_compI]
    reduced to the components' totmono; boundedness by the [cones_prod]
    sup; Scott on the unit ball by [cones_prod_eq] componentwise;
    path-preservation by the product test family (an [iniTest] of a
    component test).  The diagonal [g ↦ ⟨g, K g⟩] is the [f = id]
    instance, derived as [id_spair_meas_stable] right after.

    Alternative direct proof would mirror [scones_tuple_meas_stable_bare]
    on a fixed [sprod] (without going through [scones_hom]). *)
Section SpairMeasStable.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (G C A : ICone.type Ar).
Local Open Scope precone_scope.

Lemma spair_meas_stable (f : G -> C) (K : G -> A) :
  is_meas_stable f -> is_meas_stable K ->
  is_meas_stable (fun g : G => sprod_pair (f g) (K g) : sprod C A).
Proof.
move=> Hf HK.
have [Hfs Hfp] := Hf.
have [Hftm [Mf' HMf'] Hfsc] := Hfs.
have [Hs Hp] := HK.
have [Htm [Mk HMk] Hsc] := Hs.
have Hk_ub g : cone_norm g <= 1 -> cone_norm (K g) <= Mk by exact: HMk.
have Hf_ub g : cone_norm g <= 1 -> cone_norm (f g) <= Mf' by exact: HMf'.
have Mk_ge0 : (0 <= Mk)%R.
  have H0le1 : cone_norm (precone_zero : G) <= 1 by rewrite cone_norm0 ler01.
  by apply: le_trans (cone_norm_ge0 (K precone_zero)) (HMk precone_zero H0le1).
have Mf_ge0 : (0 <= Mf')%R.
  have H0le1 : cone_norm (precone_zero : G) <= 1 by rewrite cone_norm0 ler01.
  by apply: le_trans (cone_norm_ge0 (f precone_zero)) (HMf' precone_zero H0le1).
split; first split.
- (* Totally monotonic, componentwise. *)
  move=> n x u Hz.
  apply: cones_prod_le_compI => i.
  rewrite !cones_prod_val_big.
  case: i.
    rewrite (eq_bigr (fun I => f (tm_arg x u I))) //.
    rewrite [X in _ <=p X](eq_bigr (fun I => f (tm_arg x u I))) //.
    exact: Hftm.
  rewrite (eq_bigr (fun I => K (tm_arg x u I))) //.
  rewrite [X in _ <=p X](eq_bigr (fun I => K (tm_arg x u I))) //.
  exact: Htm.
- (* Bounded on the unit ball. *)
  exists (Mf' + Mk)%R => g Hg.
  rewrite /cone_norm/=.
  apply: ge_sup; first by exists (cone_norm (f g)), true.
  move=> _ [b ->]; case: b => /=.
  + apply: le_trans (Hf_ub g Hg) _.
    by apply: ler_wpDr => //; exact: Mk_ge0.
  + apply: le_trans (Hk_ub g Hg) _.
    by apply: ler_wpDl => //; exact: Mf_ge0.
- (* Scott on the unit ball: componentwise. *)
  move=> Mfx u uch ub1 fuch fubMf Mfpos.
  pose Pc : bool -> coneType R := sprod_fam C A.
  pose pair_u : nat -> sprod C A := fun n => sprod_pair (f (u n)) (K (u n)).
  have proj_sct (i : bool) := linear_scott_of_omega (cones_proj_fun (P:=Pc) i)
    (cones_proj_linear Pc i) (cones_proj_continuous (P:=Pc) (i:=i)).
  have HL i := proj_sct i Mfx Mfx pair_u fuch fubMf Mfpos.
  apply: cones_prod_eq => i.
  case: i.
    (* true: f component. *)
    have eT n : cones_proj_fun (P:=Pc) true (pair_u n) = f (u n) by [].
    have eTch n : cones_proj_fun (P:=Pc) true (pair_u n) <=p
                  cones_proj_fun (P:=Pc) true (pair_u n.+1).
      rewrite !eT.
      have := fuch n.
      by move=> H; have := cones_prod_le_comp H true; rewrite /cones_prod_val/=.
    have eTub n : cone_norm (cones_proj_fun (P:=Pc) true (pair_u n)) <=
                  Mfx%:num.
      rewrite eT.
      apply: le_trans (fubMf n).
      exact: (cones_prod_norm_ge_comp (pair_u n) true).
    have f_fuch n : f (u n) <=p f (u n.+1) by rewrite -!eT; exact: eTch.
    have f_fubMf n : cone_norm (f (u n)) <= Mfx%:num by rewrite -eT.
    rewrite -[cones_prod_val (sprod_pair (f _) (K _)) true]
      /(f (cone_sup_ball u uch ub1)).
    rewrite (Hfsc Mfx u uch ub1 f_fuch f_fubMf Mfpos).
    rewrite -[cones_prod_val (cone_sup_at fuch fubMf Mfpos) true]
      /(cones_proj_fun (P:=Pc) true (cone_sup_at fuch fubMf Mfpos)).
    have := HL true eTch eTub Mfpos.
    move=> ->.
    apply: precone_le_anti.
    + apply: (cone_sup_at_lub f_fuch f_fubMf Mfpos) => n.
      by have := cone_sup_at_ub eTch eTub Mfpos n; rewrite eT.
    + apply: (cone_sup_at_lub eTch eTub Mfpos) => n.
      by rewrite eT; have := cone_sup_at_ub f_fuch f_fubMf Mfpos n.
  (* false: K component. *)
  have eF n : cones_proj_fun (P:=Pc) false (pair_u n) = K (u n) by [].
  have eFch n : cones_proj_fun (P:=Pc) false (pair_u n) <=p
                cones_proj_fun (P:=Pc) false (pair_u n.+1).
    rewrite !eF.
    have := fuch n.
    by move=> H; have := cones_prod_le_comp H false; rewrite /cones_prod_val/=.
  have eFub n : cone_norm (cones_proj_fun (P:=Pc) false (pair_u n)) <=
                Mfx%:num.
    rewrite eF.
    apply: le_trans (fubMf n).
    exact: (cones_prod_norm_ge_comp (pair_u n) false).
  have K_fuch n : K (u n) <=p K (u n.+1) by rewrite -!eF; exact: eFch.
  have K_fubMf n : cone_norm (K (u n)) <= Mfx%:num by rewrite -eF.
  rewrite -[cones_prod_val (sprod_pair (f _) (K _)) false]
    /(K (cone_sup_ball u uch ub1)).
  rewrite (Hsc Mfx u uch ub1 K_fuch K_fubMf Mfpos).
  rewrite -[cones_prod_val (cone_sup_at fuch fubMf Mfpos) false]
    /(cones_proj_fun (P:=Pc) false (cone_sup_at fuch fubMf Mfpos)).
  have := HL false eFch eFub Mfpos.
  move=> ->.
  apply: precone_le_anti.
  + apply: (cone_sup_at_lub K_fuch K_fubMf Mfpos) => n.
    by have := cone_sup_at_ub eFch eFub Mfpos n; rewrite eF.
  + apply: (cone_sup_at_lub eFch eFub Mfpos) => n.
    by rewrite eF; have := cone_sup_at_ub K_fuch K_fubMf Mfpos n.
(* Path-preservation. *)
move=> X γ Hγb Hγ.
split.
  exists (Mf' + Mk)%R => r.
  rewrite /cone_norm /= /cones_prod_norm.
  apply: ge_sup.
    by exists (cone_norm (cones_prod_val
       (sprod_pair (f (γ r)) (K (γ r))) true)), true.
  move=> _ [b ->]; case: b => /=.
  + apply: le_trans (Hf_ub _ (Hγb r)) _.
    by apply: ler_wpDr => //; exact: Mk_ge0.
  + apply: le_trans (Hk_ub _ (Hγb r)) _.
    by apply: ler_wpDl => //; exact: Mf_ge0.
move=> Y m mM.
have [j [n0 [n0M ->]]] := mM.
have Kγ_path : is_measurable_path (fun r => K (γ r)).
  exact: Hp X γ Hγb Hγ.
have [_ Kγ_meas] := Kγ_path.
have fγ_path : is_measurable_path (fun r => f (γ r)).
  exact: Hfp X γ Hγb Hγ.
have [_ fγ_meas] := fγ_path.
destruct j.
- have := fγ_meas Y n0 n0M.
  apply: eq_measurable_fun => p _.
  by rewrite /iniTest /= /iniTest_fun /= /cones_prod_val/=.
- have := Kγ_meas Y n0 n0M.
  apply: eq_measurable_fun => p _.
  by rewrite /iniTest /= /iniTest_fun /= /cones_prod_val/=.
Qed.

End SpairMeasStable.

Arguments spair_meas_stable {R Ar G C A}.

(** ** The diagonal pairing [g ↦ ⟨g, K g⟩] — the [f = id] instance

    The special case originally used by [meas_stable_diag_bilinear_tensor]'s
    ancestors and by [ppl.v]: pair a point with its image.  It is
    [spair_meas_stable] at [f = id], the identity being stable-and-measurable
    (linear + ω-continuous, hence totally monotone by [linear_totmono] and
    Scott-continuous on the unit ball by [linear_scott_unit]; it maps the
    unit ball to itself and preserves measurable paths on the nose). *)
Section IdSpairMeasStable.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (G A : ICone.type Ar).
Local Open Scope precone_scope.

Lemma meas_stable_id : is_meas_stable (fun g : G => g).
Proof.
have id_lin : is_linear (fun g : G => g) by split; rewrite ?precone_add0//.
have id_cont : is_omega_continuous (fun g : G => g).
  by move=> u' uch' ub1' fuch' fub1'; congr (cone_sup_ball _ _ _);
     exact: Prop_irrelevance.
split; last by move=> X γ _ Hγ.
split.
- exact: (linear_totmono _ id_lin).
- by exists 1 => g Hg.
- exact: linear_scott_unit id_lin id_cont.
Qed.

Lemma id_spair_meas_stable (K : G -> A) :
  is_meas_stable K ->
  is_meas_stable (fun g : G => sprod_pair g (K g) : sprod G A).
Proof. exact: (spair_meas_stable (fun g : G => g) K meas_stable_id). Qed.

End IdSpairMeasStable.

Arguments meas_stable_id {R Ar} G.
Arguments id_spair_meas_stable {R Ar G A}.

(** ** M4 — the deliverable: the diagonal bilinear stability bridge

    The headline of the file (task #171, recipe of research #181):
    if [K : G → !A] is meas-stable and [Φ : G ⊗ !A → !B] is bilinear
    into the [ICones] tensor (an [icones_hom]), then [g ↦ Φ(g ⊗p K g)]
    is meas-stable.

    Proof recipe (pure structural composition via the tensor↔hom
    adjunction Thm 5.12):
      g ↦ Φ(g ⊗p K g)
        = linhom_fun ((tensor_curry Φ) g) (K g)         [tensor_curryE]
        = (Ev_fun on stablehom) ⟨ψ' g, K g⟩
      where ψ' g := linhom_to_stablehom ((tensor_curry Φ) g).
    Then:
      - ψ' meas-stable, by [meas_stable_comp_post] applied to
        [tensor_curry Φ : icones_hom] (M2) and [linhom_to_stablehom]
        meas-stable (M1).
      - The diagonal pairing [g ↦ ⟨ψ' g, K g⟩] is meas-stable by
        [spair_meas_stable] (M3 generalized).
      - The evaluation [ev_fun : sprod (stablehom (Bang A) (Bang B))
        (Bang A) → Bang B] is meas-stable ([ev_meas_stable], paper
        Lemma 7.27).
      - Composing with [meas_stable_comp] (with the image-ball
        hypothesis for the diagonal pair) gives the result. *)
Section MeasStableDiagBilinearTensor.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (G EA EB : ICone.type Ar).
Local Open Scope precone_scope.

(** The deliverable, stated generically: [EA] and [EB] are arbitrary
    integrable cones (in the intended application, [EA = Bang Ar A] and
    [EB = Bang Ar B]; we keep them generic to avoid pulling
    [exp_adjunction.v] into [stable/]). *)
Lemma meas_stable_diag_bilinear_tensor
    (K : G -> EA)
    (Phi : icones_hom Ar (tensor Ar G EA) EB) :
  is_meas_stable K ->
  is_meas_stable (fun g : G => Phi (ptensor g (K g))).
Proof.
move=> HK.
have [Hs Hp] := HK.
have [_ [Mk HMk] _] := Hs.
have Hk_ub g : cone_norm g <= 1 -> cone_norm (K g) <= Mk by exact: HMk.
have Mk_ge0 : (0 <= Mk)%R.
  have H0le1 : cone_norm (precone_zero : G) <= 1 by rewrite cone_norm0 ler01.
  by apply: le_trans (cone_norm_ge0 (K precone_zero)) (HMk precone_zero H0le1).
(* Rescaling [K] into the unit ball: the [(M+1)]-rescale packaged in
   [stab_lin_swap.v] ([bnd_succ] / [bnd_succ_inv] / [bnd_succ_mulV]). *)
pose alpha : {nonneg R} := bnd_succ_inv Mk_ge0.
pose beta : {nonneg R} := bnd_succ Mk_ge0.
have alpha_beta : (beta%:num * alpha%:num)%:nng = (1%:nng : {nonneg R}).
  exact: (bnd_succ_mulV Mk_ge0).
pose K' := fun g : G => alpha *: K g.
have HK'_ms : is_meas_stable K'.
  rewrite /K' -[fun g : G => alpha *: K g]/(stm_scale alpha K).
  split; first exact: (stable_scale alpha Hs).
  exact: (meas_stable_scale alpha Hp).
have HK'_ball g : cone_norm g <= 1 -> cone_norm (K' g) <= 1.
  by move=> Hg; rewrite /K' cone_normh /alpha;
     exact: (bnd_succ_inv_ball Mk_ge0 (HMk g Hg)).
set Phi_curry := tensor_curry Phi.
(* Ψ' g := lift to stablehom. Meas-stable as composition of an icones_hom
   and the M1 lift. *)
have Hpsi : is_meas_stable
  (fun g : G => linhom_to_stablehom (Phi_curry g) : stablehom _ _).
  exact: (meas_stable_comp_post (Phi_curry : icones_hom Ar G _)
    linhom_to_stablehom linhom_to_stablehom_meas_stable).
(* Pair (Ψ', K'). Meas-stable by spair_meas_stable. *)
have Hpair : is_meas_stable (fun g : G =>
    sprod_pair (linhom_to_stablehom (Phi_curry g) : stablehom _ _) (K' g)
    : sprod _ _).
  exact: (spair_meas_stable _ _ Hpsi HK'_ms).
(* Image-ball hypothesis for the pair: norm of the pair ≤ 1 on unit ball
   of G. *)
have Hpair_ball g : cone_norm g <= 1 ->
  cone_norm (sprod_pair (linhom_to_stablehom (Phi_curry g) : stablehom _ _)
                        (K' g) : sprod _ _) <= 1.
  move=> Hg.
  rewrite /cone_norm/=.
  apply: ge_sup.
    by exists (cone_norm (cones_prod_val (sprod_pair
       (linhom_to_stablehom (Phi_curry g) : stablehom _ _) (K' g)) true));
       exists true.
  move=> _ [b ->]; case: b => /=.
  + apply: (sh_norm_lub (linhom_to_stablehom (Phi_curry g)) 1).
    move=> x Hx.
    rewrite linhom_to_stablehom_E //.
    apply:
      (le_trans (linhom_norm_apply_le (lexx (linhom_norm (Phi_curry g))) x)).
    rewrite -[linhom_norm (Phi_curry g)]/(cone_norm (Phi_curry g)).
    apply: le_trans (_ : cone_norm (Phi_curry g) * 1 <= 1).
      by apply: ler_wpM2l; [exact: cone_norm_ge0|exact: Hx].
    rewrite mulr1.
    exact: le_trans (cones_hom_norm_le1 Phi_curry g) Hg.
  + exact: HK'_ball.
pose aux := fun g : G =>
  beta *: ev_fun (sprod_pair
    (linhom_to_stablehom (Phi_curry g) : stablehom _ _) (K' g)).
have aux_ms : is_meas_stable aux.
  rewrite /aux.
  pose comp_fun := fun g : G => ev_fun (sprod_pair
    (linhom_to_stablehom (Phi_curry g) : stablehom _ _) (K' g)).
  have Hcomp : is_meas_stable comp_fun.
    apply: (meas_stable_comp
      (fun g : G => sprod_pair (linhom_to_stablehom (Phi_curry g)) (K' g))
      (@ev_fun _ Ar EA EB) Hpair (ev_meas_stable EA EB)).
    exact: Hpair_ball.
  have [Hcs Hcp] := Hcomp.
  rewrite -[fun g : G => beta *: _]/(stm_scale beta comp_fun).
  split; first exact: (stable_scale beta Hcs).
  exact: (meas_stable_scale beta Hcp).
(* The original function and [aux] agree on the unit ball of G. *)
apply: (meas_stable_eq_on_ball
  (fun g : G => Phi (ptensor g (K g))) aux aux_ms).
move=> g Hg.
rewrite /aux.
(* Evaluate ev_fun on a sprod_pair. *)
rewrite /ev_fun sprod_fstE sprod_sndE.
rewrite (linhom_to_stablehom_E (Phi_curry g) (K' g) (HK'_ball g Hg)).
(* Pull α out via linearity of [Phi_curry g]. *)
have [_ _ HZ] := linhom_pre_linear (linhom_pre_of (Phi_curry g)).
rewrite -[linhom_fun (Phi_curry g) (K' g)]/(Phi_curry g (K' g)).
rewrite /K' (HZ alpha (K g)).
(* β * α = 1. *)
rewrite -precone_scale_A alpha_beta precone_scale_1.
rewrite -[Phi_curry g (K g)]/(linhom_fun (Phi_curry g) (K g)).
by rewrite /Phi_curry tensor_curryE.
Qed.

End MeasStableDiagBilinearTensor.

Arguments meas_stable_diag_bilinear_tensor {R Ar G EA EB}.
