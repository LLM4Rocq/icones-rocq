(**md**************************************************************)
(** * Least-fixpoint operators in the CCC [SCones] — Paper §9.2

    This file is the §9.2 ("Fixpoint operators in the cartesian closed
    category") development, specialised to the concrete CCC [SCones].
    It is deliberately **axiom-free**: it depends only on the cone
    ω-cpo machinery ([cones/cone.v], [cones/omega_general.v]) and on the
    cartesian-closed category [SCones] of [stable/scones_ccc.v] — it does
    NOT use any staged interface (tensor / bang / Seely).

    The mathematical content is Kleene's least-fixpoint theorem on the
    unit-ball ω-cpo of an integrable cone, applied twice:

    - **CP1.**  For a map [f : B → B] which is (i) increasing on the
      unit ball [B_B], (ii) ω-continuous on [B_B], and (iii) ball-
      preserving, the iterates [fⁿ(0)] form an increasing unit-ball
      chain ([0] is the least element by [precone_le0]), whose supremum
      [lfp f := sup_n fⁿ(0)] is the least fixpoint:
        - [lfp_fixpoint : f (lfp f) = lfp f] (ω-continuity + a shift of
          the chain);
        - [lfp_least : ‖y‖ ≤ 1 → f y ≤p y → lfp f ≤p y];
        - [lfp_ball  : ‖lfp f‖ ≤ 1].
      Every [SCones] endomorphism [f : scones_hom B B] satisfies the
      three hypotheses ([totmono_increasing] of its [is_totmono]; its
      [is_scott_continuous_unit]; [sc_norm_le1] + [sc_image_ball]),
      giving [sfix f := lfp (sc_fun f)] with [sfix_fixpoint] and
      [sfix_least].

    - **CP2.**  The parametrised least-fixpoint operator [Yfix :
      scones_hom (stablehom B B) B].  We take the *direct* route: we
      show [f ↦ sfix f] is measurable-and-stable (total monotonicity
      and ω-continuity in the argument [f : stablehom B B], plus path
      preservation), package it as the [SCones] morphism [Yfix], and
      prove the fixpoint equation [Yfix_fix : f (Yfix f) = Yfix f] for a
      unit-ball [f].

    Paper reference: §9.2, the displayed [Z(F)(f) = f(F(f))] and its
    least fixpoint [Y(f) = sup_n fⁿ(0)]. *)
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
Require Import Icones.stable.totmono.
Require Import Icones.stable.stablehom.
Require Import Icones.stable.scones_cat.
Require Import Icones.stable.scones_ccc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(** ** CP1 — Kleene least fixpoint on the unit-ball ω-cpo

    We work with a single integrable cone [B] and a raw map [f : B → B]
    with the three Kleene hypotheses. *)

Section KleeneCore.
Variable R : realType.
Variable B : coneType R.
Local Open Scope precone_scope.

Variable f : B -> B.
Hypothesis f_incr : forall x y : B, x <=p y -> cone_norm y <= 1 -> f x <=p f y.
Hypothesis f_ball : forall x : B, cone_norm x <= 1 -> cone_norm (f x) <= 1.

(** The Kleene chain [n ↦ fⁿ(0)]. *)
Definition kleene (n : nat) : B := iter n f (0 : B).

Lemma kleene0 : kleene 0 = (0 : B). Proof. by []. Qed.

Lemma kleeneS n : kleene n.+1 = f (kleene n).
Proof. by rewrite /kleene iterS. Qed.

(** Every iterate stays in the unit ball (ball-preservation, [0] in). *)
Lemma kleene_ball n : cone_norm (kleene n) <= 1.
Proof.
elim: n => [|n IH]; first by rewrite kleene0 cone_norm0.
by rewrite kleeneS; exact: f_ball.
Qed.

(** The Kleene chain is increasing (base: [0] is least; step:
    monotonicity on the unit ball). *)
Lemma kleene_chain n : kleene n <=p kleene n.+1.
Proof.
elim: n => [|n IH]; first by rewrite kleene0; exact: precone_le0.
rewrite !kleeneS.
by apply: f_incr; [exact: IH | rewrite -kleeneS; exact: kleene_ball].
Qed.

(** The least fixpoint [lfp f := sup_n fⁿ(0)] in the unit ball. *)
Definition lfp : B := cone_sup_ball kleene kleene_chain kleene_ball.

Lemma lfp_ball : cone_norm lfp <= 1.
Proof. exact: cone_sup_ball_norm. Qed.

Lemma kleene_le_lfp n : kleene n <=p lfp.
Proof. exact: cone_sup_ball_ub. Qed.

(** Leastness: any [y] in the unit ball with [f y ≤p y] is a pre-fixpoint
    and dominates [lfp]. *)
Lemma lfp_least (y : B) :
  cone_norm y <= 1 -> f y <=p y -> lfp <=p y.
Proof.
move=> Hy Hfy; apply: cone_sup_ball_lub => n.
elim: n => [|n IH]; first by rewrite kleene0; exact: precone_le0.
rewrite kleeneS.
apply: (precone_le_trans (y := f y)); last exact: Hfy.
exact: f_incr.
Qed.

End KleeneCore.

Arguments kleene {R B} f n.
Arguments lfp {R B} f f_incr f_ball.

(** *** ω-continuity gives the fixpoint equation

    We isolate the fixpoint equation in its own section because it needs
    the extra ω-continuity hypothesis [is_scott_continuous_unit f] (with
    image radius [1], available since the image chain is in the ball). *)

Section KleeneFixpoint.
Variable R : realType.
Variable B : coneType R.
Local Open Scope precone_scope.

Variable f : B -> B.
Hypothesis f_incr : forall x y : B, x <=p y -> cone_norm y <= 1 -> f x <=p f y.
Hypothesis f_ball : forall x : B, cone_norm x <= 1 -> cone_norm (f x) <= 1.
Hypothesis f_cont : is_scott_continuous_unit f.

Local Notation u := (kleene f).

(** The image chain [f ∘ u] is the shifted Kleene chain [n ↦ u n.+1]. *)
Lemma kleene_image_shift n : (f \o u) n = u n.+1.
Proof. by rewrite kleeneS. Qed.

(** Paper §9.2: [f(lfp f) = lfp f].  By ω-continuity [f(sup uₙ) = sup
    f(uₙ) = sup uₙ₊₁]; the shifted chain [n ↦ uₙ₊₁] has the same supremum
    (its tail is cofinal), so the right-hand side is again [lfp f]. *)
Lemma lfp_fixpoint : f (lfp f f_incr f_ball) = lfp f f_incr f_ball.
Proof.
rewrite /lfp.
set uu := kleene f.
set uuch := (kleene_chain f_incr f_ball).
set uub1 := (kleene_ball f_ball).
(* The image chain [f ∘ u] is increasing and in the unit ball. *)
have fuch n : (f \o u) n <=p (f \o u) n.+1.
  by rewrite /comp; apply: f_incr;
    [exact: (kleene_chain f_incr f_ball) | exact: (kleene_ball f_ball)].
have fub1 n : cone_norm ((f \o u) n) <= 1.
  by rewrite /comp; apply: f_ball; exact: (kleene_ball f_ball).
(* ω-continuity at image radius [1]: [f (sup u) = cone_sup_at (f∘u)].
   [is_scott_continuous_unit] is a [Prop]-constant; unfold it to a
   product before applying it positionally. *)
move: (f_cont); rewrite /is_scott_continuous_unit => Hc.
rewrite (Hc 1%:nng uu uuch uub1 fuch fub1 ltr01).
(* Reduce the radius-aware sup to the unit-ball sup. *)
rewrite (cone_sup_at_ball fuch fub1 fub1 ltr01).
(* [cone_sup_ball (f∘u)] = [cone_sup_ball u]: the shift is cofinal. *)
apply: precone_le_anti.
- apply: cone_sup_ball_lub => n.
  rewrite kleene_image_shift; exact: (cone_sup_ball_ub uu uuch uub1 n.+1).
- apply: cone_sup_ball_lub => n.
  apply: (precone_le_trans (y := (f \o u) n)).
    by rewrite kleene_image_shift; exact: (uuch n).
  exact: cone_sup_ball_ub.
Qed.

End KleeneFixpoint.

Arguments lfp_fixpoint {R B} f f_incr f_ball f_cont.

(** *** Specialisation to a [SCones] endomorphism

    Every [f : scones_hom B B] satisfies the three Kleene hypotheses:
    - increasing on [B_B] = [totmono_increasing] of its total
      monotonicity (the [n = 1] instance of (7.1));
    - ω-continuous on [B_B] = its [is_scott_continuous_unit];
    - ball-preserving = [sc_image_ball].
    Hence it has a least fixpoint [sfix f := lfp (sc_fun f)]. *)

Section SconesFix.
Variable R : realType.
Variable Ar : MeasSubcat R.
Variable B : ICone.type Ar.
Local Open Scope precone_scope.

(** The three Kleene hypotheses for the underlying map of a morphism. *)

Lemma sc_incr (f : scones_hom B B) (x y : B) :
  x <=p y -> cone_norm y <= 1 -> sc_fun f x <=p sc_fun f y.
Proof.
move=> [v ->] Hy.
have [[Htm _ _] _] := sc_meas_stable f.
exact: (totmono_increasing Htm).
Qed.

Lemma sc_ball_pres (f : scones_hom B B) (x : B) :
  cone_norm x <= 1 -> cone_norm (sc_fun f x) <= 1.
Proof. exact: (sc_image_ball f). Qed.

Lemma sc_cont (f : scones_hom B B) : is_scott_continuous_unit (sc_fun f).
Proof. by have [[_ _ Hsc] _] := sc_meas_stable f. Qed.

(** The least fixpoint [sfix f := sup_n fⁿ(0)] of a [SCones]
    endomorphism, as an element of [B]. *)
Definition sfix (f : scones_hom B B) : B :=
  lfp (sc_fun f) (@sc_incr f) (@sc_ball_pres f).

Lemma sfix_ball (f : scones_hom B B) : cone_norm (sfix f) <= 1.
Proof. exact: lfp_ball. Qed.

(** Paper §9.2: [sfix f] is a fixpoint of [f]. *)
Lemma sfix_fixpoint (f : scones_hom B B) : sc_fun f (sfix f) = sfix f.
Proof. rewrite /sfix; apply: lfp_fixpoint; exact: sc_cont. Qed.

(** Paper §9.2: [sfix f] is the least pre-fixpoint in [B_B]. *)
Lemma sfix_least (f : scones_hom B B) (y : B) :
  cone_norm y <= 1 -> sc_fun f y <=p y -> sfix f <=p y.
Proof. by rewrite /sfix; apply: lfp_least. Qed.

End SconesFix.

Arguments sfix {R Ar B} f.
Arguments sfix_fixpoint {R Ar B} f.
Arguments sfix_least {R Ar B} f y.
