(**md**************************************************************)
(** * The category [SCones] — Paper §7.4

    The cartesian (closed) category of integrable cones and stable and
    measurable functions.  We build the part of §7.4 that does not need
    the internal hom (Lemma 7.27): the category itself (Theorem 7.30),
    the dereliction inclusion [Ders : ICones → SCones] (Lemma 7.31),
    and the products (Theorem 7.32, products part).

    **The carrier — 0-extension off the unit ball.**  The paper's stable
    maps are functions [f : B_B → C] on the unit ball, equal iff they
    agree on [B_B].  We model them by a *total* function [B → C] that is
    *canonically extended by [0] off the unit ball*, exactly as
    [stablehom.v] does: the morphism record [scones_hom] carries a third
    field [sc_offball] forcing [f x = precone_zero] for [‖x‖ > 1].
    Since [is_meas_stable] only constrains [f] on [B_B], this makes the
    on-ball behaviour fully determine [f], so Leibniz equality coincides
    with agreement-on-[B_B] ([scones_hom_eq]).

    To keep this invariant under the category operations, every operation
    *composes, then re-extends by [0]* via the clamp [sc_clamp]: even
    though a nonlinear [g] has [g 0 ≠ 0] (so a bare composite need not
    vanish off the ball), the clamped composite does.  The workhorse is
    [meas_stable_eq_on_ball]: a function agreeing on [B_B] with a stable
    map is itself stable (every [is_meas_stable] clause is guarded by a
    [cone_norm … ≤ 1] hypothesis, so it only sees on-ball values).

    Contents:
    - [scones_hom B C] — the morphism record: a stable-and-measurable
      function [B → C] of operator norm [≤ 1], 0-extended off the unit
      ball ([sc_offball]).  Proof-irrelevant extensionality
      [scones_hom_eq].
    - The operator norm [sc_norm] (mirroring [sh_norm] of [stablehom.v])
      with [sc_norm_ub] / [sc_norm_lub] / [sc_norm_ge0].
    - The clamp [sc_clamp] (0-extension off the ball) and its congruence
      [meas_stable_eq_on_ball] / [sc_clamp_meas_stable] / [sc_norm_clamp].
    - [scones_id], [scones_comp] and the category laws [scones_compIl]
      / [scones_compIr] / [scones_compA] — Theorem 7.30 packaged as a
      category, reusing [meas_stable_comp] of [stable/compose.v].
    - [linear_totmono] (linear ⇒ totally monotonic) and the resulting
      [ders] inclusion (Lemma 7.31); functoriality [ders_id] /
      [ders_comp] and faithfulness [ders_faithful].
    - The product [icones_prod B] is the categorical product in
      [SCones] too: [scones_proj] (= [ders] of the ICones projection)
      and the tupling [scones_tuple] with the universal property
      [scones_tuple_proj] / [scones_tuple_unique] — Theorem 7.32
      (products part), delivered as Leibniz equalities thanks to the
      0-extension.

    The cartesian-*closed* structure [Ev] + currying — which needs
    Lemma 7.27 (the [B ⇒ₛ C] internal hom of [stablehom.v]) — is built
    on top of this file in [stable/scones_ccc.v].

    Paper reference: §7.4 (page 1:65), Theorems 7.30, 7.32 (products),
    Lemma 7.31. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import measurable_structure measurable_function.

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
Require Import Icones.stable.totmono.
Require Import Icones.stable.findiff.
Require Import Icones.stable.compose.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(** ** Linear maps are totally monotonic — Paper Lemma 7.31

    "Indeed linearity clearly implies total monotonicity."  We prove it
    by induction on the arity [n] of Condition (7.1), via the
    *unconditional* cons recurrences [Spos_recur] / [Sneg_recur]
    ([findiff.v], valid for any [f]).  The step needs only that, for a
    linear [f], increasing the centre by [u₀] adds the *same* cone
    element to [Spos] and to [Sneg] — which holds because [Pos] and
    [Neg] index sets have equal cardinality ([card_Ppos_Pneg]) and a
    constant cone-sum ([big_const]) depends only on the cardinality. *)

Section LinearTotmono.
Variable R : realType.
Variables B C : coneType R.
Local Open Scope precone_scope.

(** The two sign-split index families have the same cardinality
    (for arity [n.+1]): each splits into an [injI0]-image and an
    [injI]-image of the lower-arity families, and the two contributions
    are swapped between [Pos] and [Neg]. *)
Lemma card_Ppos_Pneg (n : nat) : #|Ppos n.+1| = #|Pneg n.+1|.
Proof.
have splitU (A : {set {set 'I_n.+1}}) :
    #|A| = (#|[set I in A | ord0 \in I]| + #|[set I in A | ord0 \notin I]|)%N.
  rewrite -(cardsID [set I : {set 'I_n.+1} | ord0 \in I] A).
  congr (_ + _)%N; apply: eq_card => I; rewrite !inE.
  - by rewrite andbC.
  - by rewrite andbC.
have injIinj : injective (@injI n) by apply: (can_inj (@projI_injI n)).
have injI0inj : injective (@injI0 n) by apply: (can_inj (@projI_injI0 n)).
rewrite (splitU (Ppos n.+1)) (splitU (Pneg n.+1)).
rewrite Ppos_split_in Ppos_split_out Pneg_split_in Pneg_split_out.
by rewrite !card_imset// addnC.
Qed.

(** A constant cone-sum over [Pneg n] is [≤p] the one over [Ppos n]:
    for [n.+1] they are equal ([big_const] + [card_Ppos_Pneg]); for
    [n = 0] the negative sum is [0]. *)
Lemma big_Pneg_le_Ppos (n : nat) (c : C) :
  \big[precone_add/precone_zero]_(I in Pneg n) c <=p
  \big[precone_add/precone_zero]_(I in Ppos n) c.
Proof.
case: n => [|n]; first by rewrite Pneg0 big_set0; exact: precone_le0.
by rewrite !big_const card_Ppos_Pneg; exact: precone_le_refl.
Qed.

End LinearTotmono.

Arguments big_Pneg_le_Ppos {R C} n c.

(** The centre-shift identity for the sign-split sums of a *linear* map:
    increasing the centre by [e] adds the constant sum [\sum f e] to
    both [Spos] and [Sneg].  By [linearD] the [f]-image of the shifted
    argument splits as [f(xb + Σ) + f e], and [sumP_add] distributes
    the split through the [Pε]-bigop. *)

Section LinearShift.
Variable R : realType.
Variables B C : coneType R.
Variable f : B -> C.
Hypothesis Hf : is_linear f.
Local Open Scope precone_scope.

Lemma Spos_lin_shift (n : nat) (w : 'I_n -> B) (xb e : B) :
  Spos f n w (xb + e) =
  Spos f n w xb + \big[precone_add/precone_zero]_(I in Ppos n) f e.
Proof.
rewrite /Spos -sumP_add; apply: eq_bigr => I _.
rewrite -precone_addA [e + _]precone_addC precone_addA.
by rewrite (basic_lemmas.linearD Hf).
Qed.

Lemma Sneg_lin_shift (n : nat) (w : 'I_n -> B) (xb e : B) :
  Sneg f n w (xb + e) =
  Sneg f n w xb + \big[precone_add/precone_zero]_(I in Pneg n) f e.
Proof.
rewrite /Sneg -sumP_add; apply: eq_bigr => I _.
rewrite -precone_addA [e + _]precone_addC precone_addA.
by rewrite (basic_lemmas.linearD Hf).
Qed.

End LinearShift.

Arguments Spos_lin_shift {R B C} f Hf n w xb e.
Arguments Sneg_lin_shift {R B C} f Hf n w xb e.

(** **Linear ⇒ totally monotonic** (Paper Lemma 7.31).  Induction on the
    arity [n] of (7.1): the unconditional cons recurrences
    [Spos_recur] / [Sneg_recur] reduce the [n.+1] difference to the [n]
    one shifted by the head [u ord0]; the linear centre-shift identities
    ([Spos_lin_shift] / [Sneg_lin_shift]) make the two increments equal
    constant sums ([big_Pneg_le_Ppos]), and the inductive order follows
    after cancelling [Spos f n w xb + Sneg f n w xb]. *)

Section LinearTotmonoMain.
Variable R : realType.
Variables B C : coneType R.
Variable f : B -> C.
Hypothesis Hf : is_linear f.
Local Open Scope precone_scope.

Lemma linear_Sneg_le_Spos (n : nat) (u : 'I_n -> B) (xb : B) :
  Sneg f n u xb <=p Spos f n u xb.
Proof.
elim: n u xb => [|n IHn] u xb.
  by rewrite /Sneg /Spos Pneg0 big_set0; exact: precone_le0.
rewrite (vcons_eta u) Spos_recur Sneg_recur.
set u0 := u ord0; set w := fun i : 'I_n => u (lift ord0 i).
rewrite (Spos_lin_shift f Hf) (Sneg_lin_shift f Hf).
set Sp := Spos f n w xb; set Sn := Sneg f n w xb.
set Dp := \big[precone_add/precone_zero]_(I in Ppos n) f u0.
set Dn := \big[precone_add/precone_zero]_(I in Pneg n) f u0.
have HD : Dn <=p Dp by exact: big_Pneg_le_Ppos.
(* Goal: (Sn + Dn) + Sp <=p (Sp + Dp) + Sn.  Bring both to
   [(Sn + Sp) + D{n,p}] and reduce to [Dn <=p Dp]. *)
rewrite -precone_addA [Dn + Sp]precone_addC precone_addA.
rewrite -[Sp + Dp + Sn]precone_addA [Dp + Sn]precone_addC precone_addA.
rewrite [Sp + Sn]precone_addC.
by apply: precone_add_le_l.
Qed.

Lemma linear_totmono : is_totmono f.
Proof. by move=> n x u _; exact: linear_Sneg_le_Spos. Qed.

End LinearTotmonoMain.

Arguments linear_totmono {R B C} f Hf.

(** ** The operator / sup norm of a stable-and-measurable map

    [‖f‖ = sup_{‖x‖ ≤ 1} ‖f x‖], well defined because stable maps are
    bounded ([is_stable] supplies the witness).  We mirror [sh_norm] of
    [stable/stablehom.v] but on a *bare* [is_meas_stable] function, not
    requiring the off-ball [0]-extension of [stablehom]. *)

Section SconesNorm.
Variable R : realType.
Variable Ar : MeasSubcat R.
Variables B C : ICone.type Ar.
Local Open Scope classical_set_scope.
Local Open Scope precone_scope.

(** The image norm-set [{‖f x‖ | ‖x‖ ≤ 1}]. *)
Definition sc_normset (f : B -> C) : set R :=
  [set y | exists x : B, cone_norm x <= 1 /\ y = cone_norm (f x)].

Lemma sc_normset_nonempty (f : B -> C) : sc_normset f !=set0.
Proof.
exists (cone_norm (f precone_zero)), precone_zero.
by split; first by rewrite cone_norm0.
Qed.

Lemma sc_normset_has_ubound (f : B -> C) :
  is_meas_stable f -> has_ubound (sc_normset f).
Proof.
move=> [[_ [M HM] _] _].
by exists M => _ [x [Hx ->]]; exact: HM.
Qed.

Lemma sc_normset_has_sup (f : B -> C) :
  is_meas_stable f -> has_sup (sc_normset f).
Proof.
by move=> Hf;
   split; [exact: sc_normset_nonempty | exact: sc_normset_has_ubound].
Qed.

(** [‖f‖ = sup_{‖x‖ ≤ 1} ‖f x‖]. *)
Definition sc_norm (f : B -> C) : R := sup (sc_normset f).

(** Pointwise bound: [‖f x‖ ≤ ‖f‖] for [‖x‖ ≤ 1]. *)
Lemma sc_norm_ub (f : B -> C) (Hf : is_meas_stable f) (x : B) :
  cone_norm x <= 1 -> cone_norm (f x) <= sc_norm f.
Proof.
move=> Hx; move/ubP: (sup_upper_bound (sc_normset_has_sup Hf)); apply.
by exists x.
Qed.

(** Least upper bound: any uniform pointwise bound dominates [‖f‖]. *)
Lemma sc_norm_lub (f : B -> C) (M : R) :
  (forall x : B, cone_norm x <= 1 -> cone_norm (f x) <= M) ->
  sc_norm f <= M.
Proof.
move=> HM; apply: ge_sup; first exact: sc_normset_nonempty.
by move=> _ [x [Hx ->]]; exact: HM.
Qed.

Lemma sc_norm_ge0 (f : B -> C) (Hf : is_meas_stable f) :
  (0 <= sc_norm f)%R.
Proof.
apply: le_trans (cone_norm_ge0 (f precone_zero)) _.
by apply: sc_norm_ub => //; rewrite cone_norm0.
Qed.

End SconesNorm.

Arguments sc_normset {R Ar B C}.
Arguments sc_norm {R Ar B C}.
Arguments sc_norm_ub {R Ar B C f}.
Arguments sc_norm_lub {R Ar B C f}.
Arguments sc_norm_ge0 {R Ar B C f}.

(** ** Morphisms of [SCones] — Paper §7.4

    [SCones(B, C)] is the set of stable-and-measurable functions [B → C]
    of operator norm [≤ 1]. *)

Section SconesHom.
Variable R : realType.
Variable Ar : MeasSubcat R.
Variables B C : ICone.type Ar.

Record scones_hom : Type := MkSconesHom {
  sc_fun :> B -> C;
  sc_meas_stable : is_meas_stable sc_fun;
  sc_norm_le1 : sc_norm sc_fun <= 1;
  sc_offball : forall x : B, ~~ (cone_norm x <= 1) -> sc_fun x = precone_zero;
}.

(** Proof-irrelevant extensionality: same underlying function ⇒ equal
    (all three proof fields are [Prop]). *)
Lemma scones_hom_eq (f g : scones_hom) :
  (forall x, sc_fun f x = sc_fun g x) -> f = g.
Proof.
case: f => ff fs fn fz; case: g => gf gs gn gz /= Hfg.
have Hf : ff = gf by apply: funext.
move: fs fn fz; rewrite Hf => fs fn fz.
by congr MkSconesHom; exact: Prop_irrelevance.
Qed.

End SconesHom.

Arguments scones_hom {R Ar} B C.
Arguments MkSconesHom {R Ar B C}.
Arguments sc_fun {R Ar B C}.
Arguments sc_meas_stable {R Ar B C}.
Arguments sc_norm_le1 {R Ar B C}.
Arguments sc_offball {R Ar B C}.
Arguments scones_hom_eq {R Ar B C}.

(** ** The clamp [sc_clamp] — 0-extension off the unit ball

    [sc_clamp f] agrees with [f] on the closed unit ball [B_B] and is the
    cone zero off it.  This is the canonical 0-extension of the carrier
    record applied to a *bare* function; every category operation below
    is "compose, then clamp", which both restores the [sc_offball]
    invariant and (since the clamp only touches off-ball values) leaves
    the on-ball behaviour — hence stability and norm — unchanged.

    The workhorse is the congruence [meas_stable_eq_on_ball]: every
    clause of [is_meas_stable] is guarded by a [cone_norm … ≤ 1]
    hypothesis, so a function agreeing with a stable map on [B_B] is
    itself stable. *)

Section SconesClamp.
Variable R : realType.
Variable Ar : MeasSubcat R.
Variables B C : ICone.type Ar.
Local Open Scope precone_scope.
Implicit Types f g : B -> C.

(** The 0-extension off the unit ball. *)
Definition sc_clamp f : B -> C :=
  fun x => if (cone_norm x <= 1)%R then f x else precone_zero.

Lemma sc_clamp_ball f (x : B) : cone_norm x <= 1 -> sc_clamp f x = f x.
Proof. by rewrite /sc_clamp => ->. Qed.

Lemma sc_clamp_offball f (x : B) :
  ~~ (cone_norm x <= 1) -> sc_clamp f x = precone_zero.
Proof. by rewrite /sc_clamp => /negbTE ->. Qed.

(** The [sc_offball] field witness for a clamped function. *)
Lemma sc_clamp_offball_field f :
  forall x : B, ~~ (cone_norm x <= 1) -> sc_clamp f x = precone_zero.
Proof. by move=> x; exact: sc_clamp_offball. Qed.

(** **The workhorse congruence.**  A function [f] agreeing on [B_B] with
    a measurable-stable [g] is itself measurable-stable.  Each clause of
    [is_meas_stable] is guarded by a [cone_norm … ≤ 1] hypothesis, under
    which the relevant arguments lie in [B_B] and [f = g] applies.  For
    [is_totmono]: under the guard [‖x + Σ_all u‖ ≤ 1], every (7.1)
    argument [tm_arg x u I] satisfies [tm_arg x u I ≤p tm_arg x u [set:_]]
    (the missing terms are nonneg, [sumP_sub_le]), hence
    [‖tm_arg x u I‖ ≤ 1] by [cone_normp]; then [eq_bigr] rewrites every
    [f (tm_arg …)] to [g (tm_arg …)]. *)
Lemma meas_stable_eq_on_ball f g :
  is_meas_stable g ->
  (forall x : B, cone_norm x <= 1 -> f x = g x) ->
  is_meas_stable f.
Proof.
move=> [[Htm [M HM] Hsc] Hpath] Hfg; split; last first.
  (* path preservation: γ is in B_B pointwise, so f∘γ = g∘γ. *)
  move=> X γ Hγb Hγ.
  have -> : (fun r => f (γ r)) = (fun r => g (γ r)).
    by apply: funext => r; exact: Hfg (γ r) (Hγb r).
  exact: Hpath.
split.
- (* total monotonicity *)
  move=> n x u Hz.
  have HzI (I : {set 'I_n}) : cone_norm (tm_arg x u I) <= 1.
    apply: le_trans Hz; apply: cone_normp; rewrite /tm_arg.
    by apply: precone_add_le_l; exact: sumP_sub_le.
  rewrite (eq_bigr (fun I => g (tm_arg x u I))); last first.
    by move=> I _; exact: Hfg _ (HzI I).
  rewrite [X in _ <=p X](eq_bigr (fun I => g (tm_arg x u I))); last first.
    by move=> I _; exact: Hfg _ (HzI I).
  exact: Htm.
- (* boundedness *)
  exists M => x Hx; rewrite (Hfg x Hx); exact: HM.
- (* ω-continuity on the unit ball *)
  move=> Mf u uch ub1 fuch fubMf Mfpos.
  (* convert the [f]-hypotheses to [g]-hypotheses on the ball *)
  have Hsupb : cone_norm (cone_sup_ball u uch ub1) <= 1.
    exact: cone_sup_ball_norm.
  have guch : forall n, precone_le (g (u n)) (g (u n.+1)).
    by move=> n; rewrite -(Hfg _ (ub1 n)) -(Hfg _ (ub1 n.+1)); exact: fuch.
  have gubMf : forall n, cone_norm (g (u n)) <= Mf%:num.
    by move=> n; rewrite -(Hfg _ (ub1 n)); exact: fubMf.
  rewrite (Hfg _ Hsupb) (Hsc Mf u uch ub1 guch gubMf Mfpos).
  (* both sides are [cone_sup_at] of the same chain up to proof terms *)
  apply: precone_le_anti.
  + apply: cone_sup_at_lub => n /=.
    rewrite -(Hfg _ (ub1 n)); exact: (cone_sup_at_ub fuch fubMf Mfpos n).
  + apply: cone_sup_at_lub => n /=.
    rewrite (Hfg _ (ub1 n)); exact: (cone_sup_at_ub guch gubMf Mfpos n).
Qed.

(** A clamped stable map is stable: it agrees with [f] on [B_B]. *)
Lemma sc_clamp_meas_stable f :
  is_meas_stable f -> is_meas_stable (sc_clamp f).
Proof.
move=> Hf; apply: (meas_stable_eq_on_ball (g := f) Hf).
by move=> x Hx; exact: sc_clamp_ball.
Qed.

(** The clamp does not raise the norm: the normsets range only over ball
    points, where [sc_clamp f = f]. *)
Lemma sc_norm_clamp f :
  is_meas_stable f -> sc_norm (sc_clamp f) <= sc_norm f.
Proof.
move=> Hf; apply: sc_norm_lub => x Hx.
rewrite (sc_clamp_ball f Hx); exact: (sc_norm_ub Hf x Hx).
Qed.

End SconesClamp.

Arguments sc_clamp {R Ar B C}.
Arguments sc_clamp_ball {R Ar B C f x}.
Arguments sc_clamp_offball {R Ar B C f x}.
Arguments sc_clamp_offball_field {R Ar B C} f.
Arguments meas_stable_eq_on_ball {R Ar B C} f g.
Arguments sc_clamp_meas_stable {R Ar B C f}.
Arguments sc_norm_clamp {R Ar B C f}.

(** ** Stability of linear morphisms — the [Ders] ingredient (Lemma 7.31)

    A linear, ω-continuous, norm-[≤ ‖·‖] map (the data of a [cones_hom])
    is stable: total monotonicity is [linear_totmono], boundedness comes
    from [cone_norm (f x) ≤ cone_norm x ≤ 1], and ω-continuity on the
    unit ball ([is_scott_continuous_unit]) is the [linear_scott_of_omega]
    bridge specialised to input radius [1] via [cone_sup_at_ball]. *)

Section LinearStable.
Variable R : realType.
Variables B C : coneType R.
Variable f : B -> C.
Hypothesis Hlin : is_linear f.
Hypothesis Hcont : is_omega_continuous f.
Hypothesis Hnorm : forall x : B, cone_norm (f x) <= cone_norm x.
Local Open Scope precone_scope.

Lemma linear_scott_unit : is_scott_continuous_unit f.
Proof.
have Hsc := linear_scott_of_omega f Hlin Hcont.
move=> Mf u uch ub1 fuch fubMf Mfpos.
have ubM n : cone_norm (u n) <= (widen_itv 1%:itv : {nonneg R})%:num.
  by apply: le_trans (ub1 n); rewrite /=.
have Mpos : (0 < (widen_itv 1%:itv : {nonneg R})%:num)%R by rewrite /= ltr01.
rewrite -(cone_sup_at_ball uch ub1 ubM Mpos).
exact: (Hsc _ Mf u uch ubM Mpos fuch fubMf Mfpos).
Qed.

Lemma linear_stable : is_stable f.
Proof.
split.
- exact: (linear_totmono f Hlin).
- by exists 1 => x Hx; apply: le_trans (Hnorm x) Hx.
- exact: linear_scott_unit.
Qed.

End LinearStable.

Arguments linear_stable {R B C} f Hlin Hcont Hnorm.

(** The underlying function of an [icones_hom] is stable-and-measurable
    (Lemma 7.31): stability from [linear_stable] (its [cones_hom] data),
    path-preservation from the [mcones_hom_pres_path] field. *)
Section IconesMeasStable.
Variable R : realType.
Variable Ar : MeasSubcat R.
Variables B C : ICone.type Ar.

Lemma icones_meas_stable (h : icones_hom Ar B C) :
  is_meas_stable (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Proof.
split.
  apply: linear_stable.
  - exact: cones_hom_linear.
  - exact: cones_hom_continuous.
  - exact: cones_hom_norm_le1.
move=> X γ Hγb Hγ.
exact: (mcones_hom_pres_path (icones_hom_mcones h) X γ Hγ).
Qed.

End IconesMeasStable.

Arguments icones_meas_stable {R Ar B C} h.

(** ** The category [SCones] — Paper Theorem 7.30

    Identity, composition, and the category laws.  Following the
    0-extension carrier, identity and composition are *clamped*: we
    compose the bare functions, then re-extend by [0] off the unit ball
    ([sc_clamp]).  The bare composite is stable by [meas_stable_comp] of
    [stable/compose.v] (its image-ball hypothesis is [sc_image_ball]) and
    has norm [≤ ‖g‖·‖f‖ ≤ 1]; the clamp preserves both ([sc_clamp_meas_stable]
    / [sc_norm_clamp]) and supplies the [sc_offball] field.  The category
    laws are then genuine Leibniz equalities, proved by [scones_hom_eq]
    with a case split on [‖x‖ ≤ 1]: on the ball the clamps unfold and the
    bare maps agree (using [sc_image_ball] so nested clamps reduce too);
    off the ball every clamp is [0] and the target's [sc_offball] gives
    [0] as well. *)

Section SconesCat.
Variable R : realType.
Variable Ar : MeasSubcat R.

(** *** Identity *)

Section SconesId.
Variable B : ICone.type Ar.

Lemma scones_id_meas_stable : is_meas_stable (fun x : B => x).
Proof.
have := icones_meas_stable (icones_id Ar B).
by congr is_meas_stable.
Qed.

Lemma scones_id_clamp_meas_stable : is_meas_stable (sc_clamp (fun x : B => x)).
Proof. exact: sc_clamp_meas_stable scones_id_meas_stable. Qed.

Lemma scones_id_norm_le1 : sc_norm (sc_clamp (fun x : B => x)) <= 1.
Proof. by apply: sc_norm_lub => x Hx; rewrite (sc_clamp_ball Hx); exact: Hx. Qed.

Definition scones_id : scones_hom B B :=
  MkSconesHom (sc_clamp (fun x => x)) scones_id_clamp_meas_stable
    scones_id_norm_le1 (sc_clamp_offball_field _).

End SconesId.

(** *** Composition *)

Section SconesComp.
Variables B C D : ICone.type Ar.

(** The image of the unit ball under a norm-[≤ 1] stable map stays in
    the unit ball — the [Hfb] hypothesis of [meas_stable_comp]. *)
Lemma sc_image_ball (f : scones_hom B C) (x : B) :
  cone_norm x <= 1 -> cone_norm (sc_fun f x) <= 1.
Proof.
move=> Hx; apply: le_trans (sc_norm_le1 f).
exact: (sc_norm_ub (sc_meas_stable f)).
Qed.

Lemma scones_comp_meas_stable_bare (g : scones_hom C D) (f : scones_hom B C) :
  is_meas_stable (fun x => sc_fun g (sc_fun f x)).
Proof.
apply: (meas_stable_comp (sc_fun f) (sc_fun g)
          (sc_meas_stable f) (sc_meas_stable g)).
exact: sc_image_ball.
Qed.

Lemma scones_comp_meas_stable (g : scones_hom C D) (f : scones_hom B C) :
  is_meas_stable (sc_clamp (fun x => sc_fun g (sc_fun f x))).
Proof. exact: sc_clamp_meas_stable (scones_comp_meas_stable_bare g f). Qed.

Lemma scones_comp_norm_le1 (g : scones_hom C D) (f : scones_hom B C) :
  sc_norm (sc_clamp (fun x => sc_fun g (sc_fun f x))) <= 1.
Proof.
apply: sc_norm_lub => x Hx; rewrite (sc_clamp_ball Hx).
apply: le_trans (sc_norm_le1 g).
apply: (sc_norm_ub (sc_meas_stable g)).
exact: sc_image_ball.
Qed.

Definition scones_comp (g : scones_hom C D) (f : scones_hom B C) :
    scones_hom B D :=
  MkSconesHom (sc_clamp (fun x => sc_fun g (sc_fun f x)))
    (scones_comp_meas_stable g f) (scones_comp_norm_le1 g f)
    (sc_clamp_offball_field _).

End SconesComp.

(** *** Category laws *)

Lemma scones_compIl (B C : ICone.type Ar) (f : scones_hom B C) :
  scones_comp (scones_id C) f = f.
Proof.
apply: scones_hom_eq => x; rewrite /=.
have [Hx | Hx] := boolP (cone_norm x <= 1); last first.
  by rewrite (sc_clamp_offball Hx) (sc_offball f x Hx).
by rewrite (sc_clamp_ball Hx) (sc_clamp_ball (sc_image_ball f Hx)).
Qed.

Lemma scones_compIr (B C : ICone.type Ar) (f : scones_hom B C) :
  scones_comp f (scones_id B) = f.
Proof.
apply: scones_hom_eq => x; rewrite /=.
have [Hx | Hx] := boolP (cone_norm x <= 1); last first.
  by rewrite (sc_clamp_offball Hx) (sc_offball f x Hx).
by rewrite (sc_clamp_ball Hx) (sc_clamp_ball Hx).
Qed.

Lemma scones_compA (B1 B2 B3 B4 : ICone.type Ar)
    (h : scones_hom B3 B4) (g : scones_hom B2 B3) (f : scones_hom B1 B2) :
  scones_comp h (scones_comp g f) = scones_comp (scones_comp h g) f.
Proof.
apply: scones_hom_eq => x; rewrite /=.
have [Hx | Hx] := boolP (cone_norm x <= 1); last first.
  by rewrite !(sc_clamp_offball Hx).
rewrite !(sc_clamp_ball Hx).
by rewrite (sc_clamp_ball (sc_image_ball f Hx)).
Qed.

End SconesCat.

Arguments scones_id {R Ar} B.
Arguments scones_comp {R Ar B C D}.

(** ** The dereliction functor [Ders : ICones → SCones] — Lemma 7.31

    [ICones(B, C) ⊆ SCones(B, C)]: a linear morphism is stable and
    measurable ([icones_meas_stable], built on [linear_totmono]) and has
    norm [≤ 1] ([cones_hom_norm_le1]).  [Ders] is the identity on objects
    and on (the underlying functions of) morphisms; it is a faithful
    functor, but not full (Examples 2.4 / 7.9). *)

Section Ders.
Variable R : realType.
Variable Ar : MeasSubcat R.

(** The underlying linear function of an [icones_hom]. *)
Local Notation Lfun h := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

Lemma ders_meas_stable (B C : ICone.type Ar) (h : icones_hom Ar B C) :
  is_meas_stable (sc_clamp (Lfun h)).
Proof. exact: sc_clamp_meas_stable (icones_meas_stable h). Qed.

Lemma ders_norm_le1 (B C : ICone.type Ar) (h : icones_hom Ar B C) :
  sc_norm (sc_clamp (Lfun h)) <= 1.
Proof.
apply: sc_norm_lub => x Hx; rewrite (sc_clamp_ball Hx).
by apply: le_trans Hx; exact: cones_hom_norm_le1.
Qed.

(** Paper Lemma 7.31: the inclusion [ICones(B,C) → SCones(B,C)].  The
    underlying linear function is 0-extended off the unit ball. *)
Definition ders (B C : ICone.type Ar) (h : icones_hom Ar B C) :
    scones_hom B C :=
  MkSconesHom (sc_clamp (Lfun h)) (ders_meas_stable h) (ders_norm_le1 h)
    (sc_clamp_offball_field _).

(** The linear function of an [icones_hom] does not increase the norm. *)
Lemma ders_lin_ball (B C : ICone.type Ar) (h : icones_hom Ar B C) (x : B) :
  cone_norm x <= 1 -> cone_norm (Lfun h x) <= 1.
Proof. by move=> Hx; apply: le_trans Hx; exact: cones_hom_norm_le1. Qed.

(** [Ders] preserves identities. *)
Lemma ders_id (B : ICone.type Ar) :
  ders (icones_id Ar B) = scones_id B.
Proof.
apply: scones_hom_eq => x; rewrite /=.
have [Hx | Hx] := boolP (cone_norm x <= 1); last first.
  by rewrite !(sc_clamp_offball Hx).
by rewrite !(sc_clamp_ball Hx).
Qed.

(** [Ders] preserves composition. *)
Lemma ders_comp (B C D : ICone.type Ar)
    (g : icones_hom Ar C D) (f : icones_hom Ar B C) :
  ders (icones_comp g f) = scones_comp (ders g) (ders f).
Proof.
apply: scones_hom_eq => x; rewrite /=.
have [Hx | Hx] := boolP (cone_norm x <= 1); last first.
  by rewrite !(sc_clamp_offball Hx).
by rewrite !(sc_clamp_ball Hx) (sc_clamp_ball (ders_lin_ball f Hx)).
Qed.

(** A linear function with [‖x‖ ≤ 1 → f x = g x] agrees everywhere, by
    homogeneity: for [r := ‖x‖ + 1 > 0], [‖r⁻¹ ·x‖ = ‖x‖/r ≤ 1], so
    [f (r⁻¹·x) = g (r⁻¹·x)]; scaling back by [r] (linearity) gives
    [f x = g x]. *)
Lemma ders_lin_eq_of_ball (B C : ICone.type Ar)
    (f g : icones_hom Ar B C) :
  (forall x : B, cone_norm x <= 1 -> Lfun f x = Lfun g x) ->
  forall x : B, Lfun f x = Lfun g x.
Proof.
move=> Hball x.
have rge0 : (0 <= cone_norm x + 1)%R.
  by rewrite addr_ge0 ?ler01//; exact: cone_norm_ge0.
pose r : {nonneg R} := NngNum rge0.
have rpos : (0 < r%:num)%R.
  by rewrite /r/= -[X in (X < _)%R]addr0 ler_ltD// ?cone_norm_ge0// ltr01.
have rinv_ge0 : (0 <= r%:num^-1)%R by rewrite invr_ge0 ltW.
pose ri : {nonneg R} := NngNum rinv_ge0.
(* [x = r *: (ri *: x)]. *)
have xE : x = (r *: (ri *: x))%PC.
  rewrite -precone_scale_A.
  have -> : (r%:num * ri%:num)%:nng = (1%R : R)%:nng.
    by apply/val_inj; rewrite /= mulrV// unitfE gt_eqF.
  by rewrite precone_scale_1.
have Hball_x : cone_norm (ri *: x)%PC <= 1.
  rewrite cone_normh /ri/= ler_pdivrMl// mulr1.
  by rewrite lerDl ler01.
rewrite {1}xE (basic_lemmas.linearZ (cones_hom_linear _)) (Hball _ Hball_x).
by rewrite -(basic_lemmas.linearZ (cones_hom_linear _)) -xE.
Qed.

(** [Ders] is faithful: equal (clamped) images ⇒ equal [icones_hom]s. *)
Lemma ders_faithful (B C : ICone.type Ar) (f g : icones_hom Ar B C) :
  ders f = ders g -> f = g.
Proof.
move=> Hfg; apply: icones_hom_eq.
apply: ders_lin_eq_of_ball => x Hx.
have := congr1 (fun h : scones_hom B C => sc_fun h x) Hfg.
by rewrite /= !(sc_clamp_ball Hx).
Qed.

End Ders.

Arguments ders {R Ar B C} h.

(** ** Products in [SCones] — Paper Theorem 7.32 (products part)

    The categorical product [&_{i} B i = icones_prod B] of [ICones] is
    also the product in [SCones].  We deliver the *projections*
    [scones_proj i = ders (icones_proj i)] and the componentwise
    infrastructure used to relate stability on the product [P] to
    stability on each factor [B i]:

    - [cones_prod_le_compI] — the backward direction of the
      componentwise cone order: [(∀i, x i ≤p y i) → x ≤p y] on [P]
      (the witness family is uniformly bounded by [‖y‖]).  Together with
      the forward [cones_prod_le_comp] (of [cone_cat.v]) it reduces the
      product (7.1) inequality to its factors;
    - [cones_prod_val_big] — projection commutes with the product
      cone-sum, so [(Sε g u⃗ xb) i = Sε (proj_i ∘ g) u⃗ xb], reducing the
      tupling's total monotonicity to that of each [f i].

    The *tupling* [⟨f i⟩ : y ↦ (f i y)_i] and its universal property
    ([scones_tuple_proj] / [scones_tuple_unique]) are now **delivered**,
    unblocked by the 0-extension carrier.  A point of [P] carries a
    uniform bound [∃M, ∀i, ‖x i‖ ≤ M]; for an arbitrary index [I : Type]
    this holds for the tuple only on the unit ball [B_Q] (there
    [‖f i y‖ ≤ ‖f i‖ ≤ 1], so [M := 1] works).  We therefore build the
    bare tuple with a *point-level* clamp — [⟨(f i y)_i⟩] for [‖y‖ ≤ 1],
    the product zero off the ball — which is exactly the 0-extension; the
    record-level [sc_clamp] then supplies the [sc_offball] field.  The
    tuple's stability reduces componentwise to that of each [f i] through
    [cones_prod_le_comp] / [cones_prod_le_compI] (the product (7.1)
    inequality) and [cones_prod_val_big] (projection of the product
    cone-sum). *)

Section SconesProducts.
Variable R : realType.
Variable Ar : MeasSubcat R.
Variable I : Type.
Variable B : I -> ICone.type Ar.

Local Notation P := (icones_prod B).
Local Open Scope precone_scope.

(** Backward direction of the componentwise order on the product: a
    componentwise [≤p] lifts to [≤p] on [P] (the family of witnesses is
    uniformly bounded by [‖y‖] since each [z_i ≤p y_i]). *)
Lemma cones_prod_le_compI (x y : P) :
  (forall i, cones_prod_val x i <=p cones_prod_val y i) -> x <=p y.
Proof.
move=> Hle.
have wsex i : exists z, cones_prod_val y i = cones_prod_val x i + z.
  exact: Hle i.
pose Z (i : I) : B i := projT1 (cid (wsex i)).
have ZP i : cones_prod_val y i = cones_prod_val x i + Z i.
  exact: projT2 (cid (wsex i)).
have Zbd : exists M : R, forall i, cone_norm (Z i) <= M.
  have [My HMy] := cones_prod_bd y.
  exists My => i; apply: le_trans (HMy i); apply: cone_normp.
  by exists (cones_prod_val x i); rewrite ZP precone_addC.
exists {| cones_prod_val := Z; cones_prod_bd := Zbd |}.
by apply: cones_prod_eq => i /=; exact: ZP.
Qed.

(** Projection of a product cone-sum is the componentwise cone-sum: the
    component map [x ↦ x i] is a [precone] morphism. *)
Lemma cones_prod_val_big (T : finType) (A : {set T}) (h : T -> P) (i : I) :
  cones_prod_val (\big[precone_add/precone_zero]_(j in A) h j) i =
  \big[precone_add/precone_zero]_(j in A) cones_prod_val (h j) i.
Proof. by elim/big_rec2: _ => [|j s s' _ <-]. Qed.

(** The [i]-th projection of [SCones] = [ders] of the [ICones]
    projection. *)
Definition scones_proj (i : I) : scones_hom P (B i) :=
  ders (icones_proj i).

(** *** Tupling — Paper Theorem 7.32 (universal property) *)

Variable Q : ICone.type Ar.
Variable f : forall i : I, scones_hom Q (B i).

(** Each component, point-level 0-extended ([sc_clamp]), is uniformly
    bounded by [1]: on [B_Q] it is [f i y] (norm [≤ ‖f i‖ ≤ 1] by
    [sc_image_ball]); off the ball it is the cone zero (norm [0]). *)
Lemma scones_tuple_bd (y : Q) :
  exists M : R, forall i, cone_norm (sc_clamp (sc_fun (f i)) y) <= M.
Proof.
exists 1 => i.
have [Hy | Hy] := boolP (cone_norm y <= 1).
  rewrite (sc_clamp_ball Hy); exact: (sc_image_ball (f i) Hy).
by rewrite (sc_clamp_offball Hy) cone_norm0 ler01.
Qed.

(** The bare tuple, *point-level* 0-extended off the unit ball: the
    [i]-th component is the 0-extension [sc_clamp (f i)], so on [B_Q] it
    is the genuine product point [⟨(f i y)_i⟩] and off the ball it is the
    product zero — exactly the 0-extension, total without a dependent
    match.  The record-level [sc_clamp] then only re-affirms it. *)
Definition scones_tuple_fun (y : Q) : P :=
  {| cones_prod_val := fun i => sc_clamp (sc_fun (f i)) y;
     cones_prod_bd := scones_tuple_bd y |}.

(** On the ball, the [i]-th component of the bare tuple is [f i y]. *)
Lemma scones_tuple_val (y : Q) (Hy : cone_norm y <= 1) (i : I) :
  cones_prod_val (scones_tuple_fun y) i = sc_fun (f i) y.
Proof. by rewrite /scones_tuple_fun /= (sc_clamp_ball Hy). Qed.

(** On the ball, the tuple's norm is [≤ 1]: every component is [≤ 1]
    ([sc_image_ball]), so the product norm — the [sup] of the component
    norms — is [≤ 1] by the least-upper-bound property. *)
Lemma scones_tuple_norm_ball (y : Q) :
  cone_norm y <= 1 -> cone_norm (scones_tuple_fun y) <= 1.
Proof.
move=> Hy; rewrite /cone_norm/= /cones_prod_norm.
have [[i0 _]|HE] := pselect (exists i : I, True); last first.
  rewrite (_ : cones_prod_normset _ = set0) ?sup0 ?ler01//.
  apply/predeqP => r; split=> // -[i _]; exfalso; exact: HE.
apply: ge_sup; first by exists (cone_norm (cones_prod_val (scones_tuple_fun y) i0)), i0.
move=> r [i ->]; rewrite (scones_tuple_val Hy); exact: (sc_image_ball (f i) Hy).
Qed.

(** Total monotonicity of the tuple, reduced componentwise.  Under the
    guard [‖x + Σ u‖ ≤ 1] every [tm_arg x u I] is in [B_Q]
    ([sumP_sub_le] + [cone_normp]), so its components are the genuine
    [f i (tm_arg …)]; the product (7.1) inequality then lifts the
    per-component [is_totmono (f i)] through [cones_prod_le_compI] and
    [cones_prod_val_big]. *)
Lemma scones_tuple_totmono : is_totmono scones_tuple_fun.
Proof.
move=> n x u Hz.
have HzI (J : {set 'I_n}) : cone_norm (tm_arg x u J) <= 1.
  apply: le_trans Hz; apply: cone_normp; rewrite /tm_arg.
  by apply: precone_add_le_l; exact: sumP_sub_le.
apply: cones_prod_le_compI => i.
rewrite !cones_prod_val_big.
rewrite (eq_bigr (fun J => sc_fun (f i) (tm_arg x u J))); last first.
  by move=> J _; rewrite scones_tuple_val//; exact: HzI.
rewrite [X in _ <=p X](eq_bigr (fun J => sc_fun (f i) (tm_arg x u J)));
  last first.
  by move=> J _; rewrite scones_tuple_val//; exact: HzI.
by have [[Hi _ _] _] := sc_meas_stable (f i); exact: Hi.
Qed.

(** Boundedness of the tuple on the unit ball: each component is [≤ 1],
    so the product norm is [≤ 1]. *)
Lemma scones_tuple_bounded :
  exists M : R, forall y : Q, cone_norm y <= 1 -> cone_norm (scones_tuple_fun y) <= M.
Proof. by exists 1 => y Hy; exact: scones_tuple_norm_ball. Qed.

(** ω-continuity of the tuple on the unit ball, reduced componentwise.
    The [i]-th projection [cones_prod_val · i] is linear and commutes
    with the unit-ball supremum ([cones_proj_continuous]); under the
    guard the tuple's argument is in [B_Q], so its component is
    [f i (·)], and the [i]-th component of both sides is the [f i]-image
    supremum at radius [Mf] ([f i]'s own ω-continuity). *)
Lemma scones_tuple_scott : is_scott_continuous_unit scones_tuple_fun.
Proof.
move=> Mf u uch ub1 fuch fubMf Mfpos.
have Hsupb : cone_norm (cone_sup_ball u uch ub1) <= 1.
  exact: cone_sup_ball_norm.
apply: cones_prod_eq => i.
rewrite (scones_tuple_val Hsupb).
(* per-component image-chain hypotheses, transported across [scones_tuple_val] *)
have ficuch : forall n, sc_fun (f i) (u n) <=p sc_fun (f i) (u n.+1).
  move=> n; have := cones_prod_le_comp (fuch n) i.
  by rewrite !(scones_tuple_val (ub1 _)).
have ficubMf : forall n, cone_norm (sc_fun (f i) (u n)) <= Mf%:num.
  move=> n; apply: le_trans (fubMf n).
  rewrite -(scones_tuple_val (ub1 n)); exact: cones_prod_norm_ge_comp.
have [[_ _ Hsc] _] := sc_meas_stable (f i).
rewrite (Hsc Mf u uch ub1 ficuch ficubMf Mfpos).
(* [proj_i] is linear + ω-continuous, hence Scott-continuous
   ([linear_scott_of_omega]); push it through the product [cone_sup_at]
   and identify the resulting [f i]-image [cone_sup_at] with the
   target's (same chain up to proof terms, [scones_tuple_val]). *)
pose Pc : I -> coneType R := fun i => B i : coneType R.
have Hproj := linear_scott_of_omega (cones_proj_fun (P:=Pc) i)
  (cones_proj_linear Pc i) (cones_proj_continuous (P:=Pc) (i:=i)).
have HL := Hproj Mf Mf (scones_tuple_fun \o u) fuch fubMf Mfpos.
have e n : cones_proj_fun i ((scones_tuple_fun \o u) n) = sc_fun (f i) (u n).
  by rewrite /cones_proj_fun (scones_tuple_val (ub1 n)).
have fuch0 : forall n, cones_proj_fun i ((scones_tuple_fun \o u) n) <=p
    cones_proj_fun i ((scones_tuple_fun \o u) n.+1).
  by move=> n; rewrite !e; exact: ficuch.
have fubMf0 : forall n,
    cone_norm (cones_proj_fun i ((scones_tuple_fun \o u) n)) <= Mf%:num.
  by move=> n; rewrite e; exact: ficubMf.
rewrite -/(cones_proj_fun i (cone_sup_at fuch fubMf Mfpos)) (HL fuch0 fubMf0 Mfpos).
apply: precone_le_anti.
- apply: cone_sup_at_lub => n.
  apply: precone_le_trans (cone_sup_at_ub fuch0 fubMf0 Mfpos n).
  by rewrite /comp/= (sc_clamp_ball (ub1 n)); exact: precone_le_refl.
- apply: cone_sup_at_lub => n.
  apply: precone_le_trans (cone_sup_at_ub ficuch ficubMf Mfpos n).
  by rewrite /comp/= (sc_clamp_ball (ub1 n)); exact: precone_le_refl.
Qed.

(** Path preservation of the tuple, reduced componentwise.  A product
    test is an [iniTest] of a component test ([icones_prod_M]); evaluated
    at a ball point the tuple's [i]-th component is [f i], so the
    per-test measurability is that of [f i ∘ γ] (each [f i]'s own path
    preservation). *)
Lemma scones_tuple_pres_path
    (X : ar_obj Ar) (γ : ar_carrier Ar X -> Q) :
  (forall r, cone_norm (γ r) <= 1) ->
  is_measurable_path (Ar:=Ar) (C:=Q) γ ->
  is_measurable_path (Ar:=Ar) (C:=P) (fun r => scones_tuple_fun (γ r)).
Proof.
move=> Hγb Hγ; split.
  by exists 1 => r; exact: scones_tuple_norm_ball.
move=> Y m mM.
have [i [n [nM ->]]] := mM.
have [_ Hp] := sc_meas_stable (f i).
have Hpi := Hp X γ Hγb Hγ.
have := proj2 Hpi Y n nM.
apply: eq_measurable_fun => p _.
by rewrite /iniTest /= /iniTest_fun (scones_tuple_val (Hγb p.2)).
Qed.

(** The bare tuple is measurable-stable. *)
Lemma scones_tuple_meas_stable_bare : is_meas_stable scones_tuple_fun.
Proof.
split; first split.
- exact: scones_tuple_totmono.
- exact: scones_tuple_bounded.
- exact: scones_tuple_scott.
- exact: scones_tuple_pres_path.
Qed.

(** The record-level clamp re-affirms the (already point-level)
    0-extension and supplies the [sc_offball] field. *)
Lemma scones_tuple_meas_stable : is_meas_stable (sc_clamp scones_tuple_fun).
Proof. exact: sc_clamp_meas_stable scones_tuple_meas_stable_bare. Qed.

Lemma scones_tuple_norm_le1 : sc_norm (sc_clamp scones_tuple_fun) <= 1.
Proof.
apply: sc_norm_lub => y Hy.
rewrite (sc_clamp_ball Hy); exact: scones_tuple_norm_ball.
Qed.

(** Paper Theorem 7.32 (tupling): the mediating [SCones] morphism
    [⟨f i⟩ : Q → &_i B_i]. *)
Definition scones_tuple : scones_hom Q P :=
  MkSconesHom (sc_clamp scones_tuple_fun) scones_tuple_meas_stable
    scones_tuple_norm_le1 (sc_clamp_offball_field _).

(** Paper Theorem 7.32 (universal property): the tupling factors each
    [f i] through the [i]-th projection. *)
Lemma scones_tuple_proj (i : I) :
  scones_comp (scones_proj i) scones_tuple = f i.
Proof.
apply: scones_hom_eq => y; rewrite /=.
have [Hy | Hy] := boolP (cone_norm y <= 1); last first.
  by rewrite (sc_clamp_offball Hy) (sc_offball (f i) y Hy).
rewrite !(sc_clamp_ball Hy).
(* now: [sc_fun (scones_proj i) (scones_tuple_fun y) = f i y] *)
rewrite /scones_proj /ders /= (sc_clamp_ball (scones_tuple_norm_ball Hy)).
(* the [ders]-clamp unfolds since the tuple is in the ball; left with
   the projection of the tuple, which is [f i y]. *)
rewrite /icones_proj /icones_proj_mcones /cones_proj /= /cones_proj_fun.
exact: scones_tuple_val.
Qed.

(** Paper Theorem 7.32 (universal property): the tupling is the unique
    such mediating morphism. *)
Lemma scones_tuple_unique (g : scones_hom Q P) :
  (forall i, scones_comp (scones_proj i) g = f i) -> g = scones_tuple.
Proof.
move=> Hg; apply: scones_hom_eq => y; rewrite /=.
have [Hy | Hy] := boolP (cone_norm y <= 1); last first.
  by rewrite (sc_clamp_offball Hy) (sc_offball g y Hy).
rewrite (sc_clamp_ball Hy).
(* both [g y] and the tuple agree componentwise. *)
apply: cones_prod_eq => i.
rewrite (scones_tuple_val Hy).
(* extract the [i]-th component of [g y] from [Hg i] at [y]. *)
have := congr1 (fun h : scones_hom Q (B i) => sc_fun h y) (Hg i).
rewrite /= !(sc_clamp_ball Hy).
rewrite /scones_proj /ders /= (sc_clamp_ball (sc_image_ball g Hy)).
by rewrite /icones_proj /icones_proj_mcones /cones_proj /= /cones_proj_fun => ->.
Qed.

End SconesProducts.

Arguments cones_prod_le_compI {R Ar I B} x y.
Arguments cones_prod_val_big {R Ar I B} T A h i.
Arguments scones_proj {R Ar I} B i.
Arguments scones_tuple_fun {R Ar I B Q} f y.
Arguments scones_tuple {R Ar I B Q} f.
Arguments scones_tuple_proj {R Ar I B Q} f i.
Arguments scones_tuple_unique {R Ar I B Q} f g.

(** ** Status of §7.4 in this file

    *Delivered* (no holes, no axioms beyond the project's classical
    base):

    - **Lemma 7.31 core** ([linear_totmono]): a linear map is totally
      monotonic.  Proved by induction on the (7.1) arity via the
      unconditional [Spos_recur] / [Sneg_recur] cons recurrences, the
      [card_Ppos_Pneg] cardinality balance ([injI0] / [injI] reindexing,
      contributions swapped between [Pos]/[Neg]) and [big_const]; the
      centre-shift identities [Spos_lin_shift] / [Sneg_lin_shift] make
      the two increments the equal constant sums of [big_Pneg_le_Ppos].
    - **The operator norm** [sc_norm] on a bare [is_meas_stable] map,
      with [sc_norm_ub] / [sc_norm_lub] / [sc_norm_ge0] (mirroring
      [sh_norm]).
    - **The morphism record** [scones_hom B C] (stable-measurable maps
      of norm [≤ 1], canonically 0-extended off the unit ball via the
      [sc_offball] field) with proof-irrelevant extensionality
      [scones_hom_eq] — Leibniz equality coincides with agreement on
      [B_B].
    - **The clamp** [sc_clamp] (the 0-extension of a bare function) with
      the congruence [meas_stable_eq_on_ball] (agreement on [B_B] with a
      stable map ⇒ stable, since every [is_meas_stable] clause is guarded
      by [cone_norm … ≤ 1]), [sc_clamp_meas_stable], and [sc_norm_clamp].
    - **Theorem 7.30 as a category**: [scones_id], [scones_comp]
      (compose-then-re-0-extend: the bare composite is stable by
      [meas_stable_comp], the clamp preserves stability/norm and restores
      [sc_offball]) and the laws [scones_compIl] / [scones_compIr] /
      [scones_compA], proved as Leibniz equalities by a ball case split.
    - **Lemma 7.31** ([ders]): the inclusion [ICones(B,C) ⊆
      SCones(B,C)] (the linear function 0-extended off the ball), with
      functoriality [ders_id] / [ders_comp] and faithfulness
      [ders_faithful] (clamped images equal ⇒ linear maps agree on
      [B_B] ⇒ agree everywhere by homogeneity, [ders_lin_eq_of_ball]).
      Built on [linear_stable] / [icones_meas_stable] (the linear →
      stable bridge: [linear_totmono], the [linear_scott_of_omega]
      specialisation [linear_scott_unit], and [cones_hom_norm_le1]).
    - **Theorem 7.32 (products), in full**: the projections
      [scones_proj i = ders (icones_proj i)] and the *tupling*
      [scones_tuple] (the per-component 0-extension [sc_clamp (f i)],
      re-affirmed by the record-level clamp) with the universal property
      [scones_tuple_proj] / [scones_tuple_unique] as genuine Leibniz
      equalities.  The tuple's stability reduces componentwise via
      [cones_prod_le_compI] / [cones_prod_le_comp] (the product (7.1)
      inequality), [cones_prod_val_big] (projection of the product
      cone-sum), and [linear_scott_of_omega] for the projection
      (ω-continuity passes through the product supremum).

    The cartesian-*closed* structure [Ev] / currying (which needs
    Lemma 7.27, the [B ⇒ₛ C] internal hom of [stablehom.v]) is built
    on top of this file in [stable/scones_ccc.v]. *)
