(**md**************************************************************************)
(** * Diagonal bilinear stability bridge — SCones ↔ ICones-tensor

    This file delivers the "diagonal bilinear" stability bridge needed by
    the CBN consumer for [ex_geom_CBN_mass_one] (and friends), and the
    generic CBV stage of [Yfix_arr_g] (Bang-fix at [eD ne_fix]):

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

    - **M3**  [id_spair_meas_stable]: the diagonal pairing
      [g ↦ ⟨g, K g⟩] for a meas-stable [K] is meas-stable (CCC pairing
      of two meas-stable maps via [scones_tuple]).

    - **M4**  [meas_stable_diag_bilinear_tensor] — THE deliverable.
      Assembles M1 + M2 + M3 + [tensor_curryE] + [ev_meas_stable]. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
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

(** A linear continuous map is in particular meas-stable. *)
Lemma linhom_is_meas_stable (h : linhom_car Ar B C) :
  is_meas_stable (linhom_fun h).
Proof. exact: linhom_meas_stable. Qed.

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
    [g ↦ ⟨f₁ g, f₂ g⟩ : G → sprod A B] is meas-stable.

    The construction reuses [scones_tuple_meas_stable_bare] (paper Thm
    7.32 at the bare-function level): the bool-indexed family of
    meas-stable maps gives a meas-stable tuple. We need to rescale each
    component to operator norm [≤ 1] to package them as [scones_hom]s,
    apply the tuple's meas-stability, and rescale back by linearity of
    [sprod_pair] in each factor.

    Alternative direct proof would mirror [scones_tuple_meas_stable_bare]
    on a fixed [sprod] (without going through [scones_hom]). *)

Section IdSpairMeasStable.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (G A : ICone.type Ar).
Local Open Scope precone_scope.

(** The diagonal pairing [g ↦ ⟨g, K g⟩] for a meas-stable [K], proved
    directly (componentwise on [sprod = icones_prod (sprod_fam G A)]).

    Total monotonicity by the product (7.1) [cones_prod_le_compI]
    reduced to identity/totmono of [K]; boundedness by [cones_prod] sup;
    Scott on the unit ball by [cones_prod_eq] componentwise; path-pres
    by the product test family (an [iniTest] of a component test). *)
Lemma id_spair_meas_stable (K : G -> A) :
  is_meas_stable K ->
  is_meas_stable (fun g : G => sprod_pair g (K g) : sprod G A).
Proof.
move=> HK.
have [Hs Hp] := HK.
have [Htm [Mk HMk] Hsc] := Hs.
have Hk_ub g : cone_norm g <= 1 -> cone_norm (K g) <= Mk by exact: HMk.
have Mk_ge0 : (0 <= Mk)%R.
  have H0le1 : cone_norm (precone_zero : G) <= 1 by rewrite cone_norm0 ler01.
  by apply: le_trans (cone_norm_ge0 (K precone_zero)) (HMk precone_zero H0le1).
have id_lin : is_linear (fun g : G => g).
  by split; rewrite ?precone_add0//.
have id_cont : is_omega_continuous (fun g : G => g).
  by move=> u' uch' ub1' fuch' fub1'; congr (cone_sup_ball _ _ _);
     exact: Prop_irrelevance.
split; first split.
- (* Totally monotonic. *)
  move=> n x u Hz.
  apply: cones_prod_le_compI => i.
  rewrite !cones_prod_val_big.
  case: i.
    (* true: identity sprod_fam = G; both sides of (7.1) sum [tm_arg]s
       directly. *)
    have := linear_totmono _ id_lin n x u Hz.
    by rewrite [X in X <=p _](eq_bigr (fun I => tm_arg x u I)); first done;
       move=> I _.
  (* false: sprod_fam false = A; (7.1) for K. *)
  rewrite (eq_bigr (fun I => K (tm_arg x u I))) //.
  rewrite [X in _ <=p X](eq_bigr (fun I => K (tm_arg x u I))) //.
  exact: Htm.
- (* Bounded on the unit ball. *)
  exists (Mk + 1)%R => g Hg.
  rewrite /cone_norm/=.
  apply: ge_sup; first by exists (cone_norm g), true.
  move=> _ [b ->]; case: b => /=.
  + apply: le_trans Hg _.
    by apply: ler_wpDl => //; exact: Mk_ge0.
  + apply: le_trans (Hk_ub g Hg) _.
    by apply: ler_wpDr => //; rewrite ler01.
- (* Scott on the unit ball: componentwise, via Scott of projections
     [cones_proj_fun] (linear + ω-cont). *)
  move=> Mf u uch ub1 fuch fubMf Mfpos.
  pose Pc : bool -> coneType R := sprod_fam G A.
  pose pair_u : nat -> sprod G A := fun n => sprod_pair (u n) (K (u n)).
  have proj_sct (i : bool) := linear_scott_of_omega (cones_proj_fun (P:=Pc) i)
    (cones_proj_linear Pc i) (cones_proj_continuous (P:=Pc) (i:=i)).
  have HL i := proj_sct i Mf Mf pair_u fuch fubMf Mfpos.
  apply: cones_prod_eq => i.
  case: i.
    (* true: identity component. *)
    have eT n : cones_proj_fun (P:=Pc) true (pair_u n) = u n by [].
    have eTch n : cones_proj_fun (P:=Pc) true (pair_u n) <=p
                  cones_proj_fun (P:=Pc) true (pair_u n.+1)
      by rewrite !eT; exact: uch.
    have eTub n : cone_norm (cones_proj_fun (P:=Pc) true (pair_u n)) <=
                  Mf%:num
      by rewrite eT;
        apply: le_trans (fubMf n);
        exact: (cones_prod_norm_ge_comp (pair_u n) true).
    rewrite -/(cones_proj_fun (P:=Pc) true
                 (sprod_pair (cone_sup_ball u uch ub1)
                             (K (cone_sup_ball u uch ub1)))).
    have id_fuch n : u n <=p u n.+1 by exact: uch.
    have id_fubMf n : cone_norm (u n) <= Mf%:num by rewrite -eT.
    have id_E := linear_scott_unit id_lin id_cont uch ub1 id_fuch id_fubMf
      Mfpos.
    rewrite -[cones_proj_fun (P:=Pc) true _]
      /(cone_sup_ball u uch ub1) id_E.
    have := HL true eTch eTub Mfpos.
    rewrite -[cones_prod_val (cone_sup_at fuch fubMf Mfpos) true]
      /(cones_proj_fun (P:=Pc) true (cone_sup_at fuch fubMf Mfpos)) => ->.
    apply: precone_le_anti.
    + apply: (cone_sup_at_lub id_fuch id_fubMf Mfpos) => n.
      by have := cone_sup_at_ub eTch eTub Mfpos n; rewrite eT.
    + apply: (cone_sup_at_lub eTch eTub Mfpos) => n.
      by rewrite eT; have := cone_sup_at_ub id_fuch id_fubMf Mfpos n.
  (* false: K component. *)
  have eF n : cones_proj_fun (P:=Pc) false (pair_u n) = K (u n) by [].
  have eFch n : cones_proj_fun (P:=Pc) false (pair_u n) <=p
                cones_proj_fun (P:=Pc) false (pair_u n.+1).
    rewrite !eF.
    have := fuch n.
    by move=> H; have := cones_prod_le_comp H false; rewrite /cones_prod_val/=.
  have eFub n : cone_norm (cones_proj_fun (P:=Pc) false (pair_u n)) <=
                Mf%:num.
    rewrite eF.
    apply: le_trans (fubMf n).
    exact: (cones_prod_norm_ge_comp (pair_u n) false).
  have K_fuch n : K (u n) <=p K (u n.+1) by rewrite -!eF; exact: eFch.
  have K_fubMf n : cone_norm (K (u n)) <= Mf%:num by rewrite -eF.
  rewrite -[cones_prod_val (sprod_pair _ (K _)) false]
    /(K (cone_sup_ball u uch ub1)).
  rewrite (Hsc Mf u uch ub1 K_fuch K_fubMf Mfpos).
  rewrite -[cones_prod_val (cone_sup_at fuch fubMf Mfpos) false]
    /(cones_proj_fun (P:=Pc) false (cone_sup_at fuch fubMf Mfpos)).
  have := HL false eFch eFub Mfpos.
  move=> ->.
  apply: precone_le_anti.
  + apply: (cone_sup_at_lub K_fuch K_fubMf Mfpos) => n.
    by have := cone_sup_at_ub eFch eFub Mfpos n; rewrite eF.
  + apply: (cone_sup_at_lub eFch eFub Mfpos) => n.
    by rewrite eF; have := cone_sup_at_ub K_fuch K_fubMf Mfpos n.
(* Path-preservation: product paths are test-tuples of components. *)
move=> X γ Hγb Hγ.
split.
  exists (Mk + 1)%R => r.
  rewrite /cone_norm /= /cones_prod_norm.
  apply: ge_sup.
    by exists (cone_norm (cones_prod_val (sprod_pair (γ r) (K (γ r))) true)),
      true.
  move=> _ [b ->]; case: b => /=.
  + apply: le_trans (Hγb r) _.
    by apply: ler_wpDl => //; exact: Mk_ge0.
  + apply: le_trans (Hk_ub _ (Hγb r)) _.
    by apply: ler_wpDr => //; rewrite ler01.
(* Per-test joint measurability via product tests. *)
move=> Y m mM.
have [j [n0 [n0M ->]]] := mM.
have Kγ_path : is_measurable_path (fun r => K (γ r)).
  exact: Hp X γ Hγb Hγ.
have [_ Kγ_meas] := Kγ_path.
have [_ γ_meas] := Hγ.
destruct j.
- (* true: test is on the [G] component. *)
  have := γ_meas Y n0 n0M.
  apply: eq_measurable_fun => p _.
  by rewrite /iniTest /= /iniTest_fun /= /cones_prod_val/=.
- (* false: test is on the [A] component. *)
  have := Kγ_meas Y n0 n0M.
  apply: eq_measurable_fun => p _.
  by rewrite /iniTest /= /iniTest_fun /= /cones_prod_val/=.
Qed.

End IdSpairMeasStable.

Arguments id_spair_meas_stable {R Ar G A}.
