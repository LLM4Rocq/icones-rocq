(**md**************************************************************)
(** * The category [SCones] — Paper §7.4

    The cartesian (closed) category of integrable cones and stable and
    measurable functions.  We build the part of §7.4 that does not need
    the internal hom (Lemma 7.27): the category itself (Theorem 7.30),
    the dereliction inclusion [Ders : ICones → SCones] (Lemma 7.31),
    and the products (Theorem 7.32, products part).

    Contents:
    - [scones_hom B C] — the morphism record: a stable-and-measurable
      function [B → C] of operator norm [≤ 1].  Proof-irrelevant
      extensionality [scones_hom_eq].
    - The operator norm [sc_norm] (mirroring [sh_norm] of [stablehom.v])
      with [sc_norm_ub] / [sc_norm_lub] / [sc_norm_ge0].
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
      (products part).

    Deferred (the NEXT step): [Ev] + currying / the closed structure —
    they need Lemma 7.27 (the [B ⇒ₛ C] internal hom of [stablehom.v]).

    Paper reference: §7.4 (page 1:65), Theorems 7.30, 7.32 (products),
    Lemma 7.31. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp Require Import perm.
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
move=> Hf; split; [exact: sc_normset_nonempty | exact: sc_normset_has_ubound].
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
}.

(** Proof-irrelevant extensionality: same underlying function ⇒ equal. *)
Lemma scones_hom_eq (f g : scones_hom) :
  (forall x, sc_fun f x = sc_fun g x) -> f = g.
Proof.
case: f => ff fs fn; case: g => gf gs gn /= Hfg.
have Hf : ff = gf by apply: funext.
move: fs fn; rewrite Hf => fs fn.
by congr MkSconesHom; exact: Prop_irrelevance.
Qed.

End SconesHom.

Arguments scones_hom {R Ar} B C.
Arguments MkSconesHom {R Ar B C}.
Arguments sc_fun {R Ar B C}.
Arguments sc_meas_stable {R Ar B C}.
Arguments sc_norm_le1 {R Ar B C}.
Arguments scones_hom_eq {R Ar B C}.

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

    Identity, composition, and the category laws.  Composition reuses
    [meas_stable_comp] of [stable/compose.v]; the norm bound
    [‖g ∘ f‖ ≤ ‖g‖ · ‖f‖ ≤ 1] is obtained pointwise. *)

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

Lemma scones_id_norm_le1 : sc_norm (fun x : B => x) <= 1.
Proof. by apply: sc_norm_lub => x Hx. Qed.

Definition scones_id : scones_hom B B :=
  MkSconesHom (fun x => x) scones_id_meas_stable scones_id_norm_le1.

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

Lemma scones_comp_meas_stable (g : scones_hom C D) (f : scones_hom B C) :
  is_meas_stable (fun x => sc_fun g (sc_fun f x)).
Proof.
apply: (meas_stable_comp (sc_fun f) (sc_fun g)
          (sc_meas_stable f) (sc_meas_stable g)).
exact: sc_image_ball.
Qed.

Lemma scones_comp_norm_le1 (g : scones_hom C D) (f : scones_hom B C) :
  sc_norm (fun x => sc_fun g (sc_fun f x)) <= 1.
Proof.
apply: sc_norm_lub => x Hx.
apply: le_trans (sc_norm_le1 g).
apply: (sc_norm_ub (sc_meas_stable g)).
exact: sc_image_ball.
Qed.

Definition scones_comp (g : scones_hom C D) (f : scones_hom B C) :
    scones_hom B D :=
  MkSconesHom (fun x => sc_fun g (sc_fun f x))
    (scones_comp_meas_stable g f) (scones_comp_norm_le1 g f).

End SconesComp.

(** *** Category laws *)

Lemma scones_compIl (B C : ICone.type Ar) (f : scones_hom B C) :
  scones_comp (scones_id C) f = f.
Proof. by apply: scones_hom_eq. Qed.

Lemma scones_compIr (B C : ICone.type Ar) (f : scones_hom B C) :
  scones_comp f (scones_id B) = f.
Proof. by apply: scones_hom_eq. Qed.

Lemma scones_compA (B1 B2 B3 B4 : ICone.type Ar)
    (h : scones_hom B3 B4) (g : scones_hom B2 B3) (f : scones_hom B1 B2) :
  scones_comp h (scones_comp g f) = scones_comp (scones_comp h g) f.
Proof. by apply: scones_hom_eq. Qed.

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

Lemma ders_norm_le1 (B C : ICone.type Ar) (h : icones_hom Ar B C) :
  sc_norm (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))) <= 1.
Proof.
apply: sc_norm_lub => x Hx.
by apply: le_trans Hx; exact: cones_hom_norm_le1.
Qed.

(** Paper Lemma 7.31: the inclusion [ICones(B,C) → SCones(B,C)]. *)
Definition ders (B C : ICone.type Ar) (h : icones_hom Ar B C) :
    scones_hom B C :=
  MkSconesHom (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h)))
    (icones_meas_stable h) (ders_norm_le1 h).

(** [Ders] preserves identities. *)
Lemma ders_id (B : ICone.type Ar) :
  ders (icones_id Ar B) = scones_id B.
Proof. by apply: scones_hom_eq. Qed.

(** [Ders] preserves composition. *)
Lemma ders_comp (B C D : ICone.type Ar)
    (g : icones_hom Ar C D) (f : icones_hom Ar B C) :
  ders (icones_comp g f) = scones_comp (ders g) (ders f).
Proof. by apply: scones_hom_eq. Qed.

(** [Ders] is faithful: equal images ⇒ equal [icones_hom]s. *)
Lemma ders_faithful (B C : ICone.type Ar) (f g : icones_hom Ar B C) :
  ders f = ders g -> f = g.
Proof.
move=> Hfg; apply: icones_hom_eq => x.
by have := congr1 (fun h : scones_hom B C => sc_fun h x) Hfg.
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

    The *tupling* [⟨f i⟩ : x ↦ (f i x)_i] and its universal property are
    deferred.  The obstruction is well-definedness as a *total* map into
    [P]: a point of [P] carries a bound [∃M, ∀i, ‖x i‖ ≤ M] uniform in
    [i], which for an arbitrary index [I : Type] holds for the tuple only
    on the unit ball [B_Q] (there [‖f i y‖ ≤ ‖f i‖ ≤ 1]); off the ball
    the values [f i y] are unconstrained per [i] and admit no uniform
    bound.  The canonical [stablehom]-style fix — a [0]-extension field
    forcing [f y = 0] for [‖y‖ > 1] — is *incompatible with the [SCones]
    composition* (for nonlinear [g], [g 0 ≠ 0] in general, so [g ∘ f]
    need not vanish off the ball), which is why the morphism record here
    carries no off-ball field.  Reconciling the two (e.g. carrying the
    unit-ball-restricted maps [B_Q → B_P] of the paper directly) is the
    clean next step, alongside [Ev] / currying (Lemma 7.27). *)

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

End SconesProducts.

Arguments cones_prod_le_compI {R Ar I B} x y.
Arguments cones_prod_val_big {R Ar I B} T A h i.
Arguments scones_proj {R Ar I} B i.

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
      of norm [≤ 1]) with proof-irrelevant extensionality
      [scones_hom_eq].
    - **Theorem 7.30 as a category**: [scones_id], [scones_comp] (via
      [meas_stable_comp]; norm [≤ 1] pointwise) and the laws
      [scones_compIl] / [scones_compIr] / [scones_compA].
    - **Lemma 7.31** ([ders]): the inclusion [ICones(B,C) ⊆
      SCones(B,C)], with functoriality [ders_id] / [ders_comp] and
      faithfulness [ders_faithful].  Built on [linear_stable] /
      [icones_meas_stable] (the linear → stable bridge:
      [linear_totmono], the [linear_scott_of_omega] specialisation
      [linear_scott_unit], and [cones_hom_norm_le1]).
    - **Theorem 7.32 (products), projections + infrastructure**:
      [scones_proj i = ders (icones_proj i)]; the componentwise lemmas
      [cones_prod_le_compI] and [cones_prod_val_big].

    *Deferred*, with the precise wall documented at the products
    section: the product *tupling* (a total map into the [Type]-indexed
    product carrier needs an off-ball uniform bound that the bare
    morphism record cannot supply, the [0]-extension fix being
    incompatible with [SCones] composition), and the cartesian-*closed*
    structure [Ev] / currying (needs Lemma 7.27, the [B ⇒ₛ C] internal
    hom of [stablehom.v]). *)
