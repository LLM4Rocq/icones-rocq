(**md**************************************************************************)
(** * ω-continuity prerequisites for the CBV value fixpoint — CBV §6 (prep)

    Prerequisites for the CBV value fixpoint construction
    ([theories/homs/em_fix.v]).  We package the genuinely-new ω-continuity
    facts at the icones / EM(!) level that the fixpoint formula needs.

    The fundamental construction is:

    - [coalg_hom_sup_pack G P u uch ub1 Hcoalg]: take an ω-chain of
      bundled coalgebra morphisms whose underlying [linhom_car]s are in
      the unit ball, and produce a bundled [coalg_hom G P] whose
      underlying [icones_hom] is the linhom-cone supremum.

    The proof uses:
    - the existing [linhom_sup_ball] (a sup of a linhom-chain is a
      linhom_car of norm ≤ 1, [theories/homs/linhom.v]);
    - the bridge [linhom_icones] / [icones_to_linhom] of
      [tensor_hom_iso.v] / [seely.v] turning a norm-≤-1 linhom_car into
      an icones_hom;
    - the ω-continuity of the icones_homs [linhom_post_icones g] and
      [linhom_pre_icones h] (which IS the ω-continuity of the cones_hom_fun
      of any icones_hom).

    The headline ω-continuity facts (all stated at the linhom level, where
    the [cone_sup_ball] of [linhom_car] is the genuine pointwise sup
    [linhom_sup_ball]):

    - [linhom_post_icones_sup] : [g ∘ (sup u) = sup (g ∘ u)] for
      [g : icones_hom D1 D2] and an ω-chain [u] in the unit ball of
      [linhom_car C D1].
    - [linhom_pre_icones_sup] : [(sup u) ∘ h = sup (u ∘ h)] for
      [h : icones_hom C2 C1].

    Combining these with [is_coalg_mor]'s point-free shape gives the
    headline [coalg_hom_sup_is_mor]: the [is_coalg_mor] equation passes
    through the linhom supremum.  Hence [coalg_hom_sup_pack] builds a
    well-formed [coalg_hom].

    Author: Guillaume Baudart <guillaume.baudart@inria.fr>. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import measurable_structure measurable_function.

Require Import Icones.prelude.nonneg_extra.
Require Import Icones.cones.precone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.cone.
Require Import Icones.cones.omega_general.
Require Import Icones.cones.cone_cat.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_cat.
Require Import Icones.stable.totmono.
Require Import Icones.stable.scones_cat.
Require Import Icones.homs.linhom.
Require Import Icones.homs.linhom_functor.
Require Import Icones.homs.exp_adjunction.
Require Import Icones.homs.bang.
Require Import Icones.homs.seely_defs.
Require Import Icones.homs.seely.
Require Import Icones.homs.coalgebra.
Require Import Icones.homs.em_cat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** Common shorthands and the [icones_to_linhom] helper

    We re-derive a local [icones_to_linhom] (the one in [tensor_hom_iso.v]
    has the same signature but lives in a heavier import chain).  Norm
    bound from [cones_hom_norm_le1] in [icone_cat.v]. *)

Section IConesToLinhomLocal.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : ICone.type Ar.

Local Notation Lfun h := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

Variable h : icones_hom Ar B C.

Local Lemma i2l_bd : exists M : R, forall x : B, cone_norm x <= 1 ->
    cone_norm (Lfun h x) <= M.
Proof.
exists 1 => x Hx; apply: le_trans Hx; exact: cones_hom_norm_le1.
Qed.

Local Definition i2l_pre : linhom_pre Ar B C :=
  MkLinhomPre (Lfun h)
    (@cones_hom_linear R _ _ (mcones_hom_cones (icones_hom_mcones h)))
    (@cones_hom_continuous R _ _ (mcones_hom_cones (icones_hom_mcones h)))
    i2l_bd
    (fun X g Hg => mcones_hom_pres_path (icones_hom_mcones h) X g Hg).

Local Lemma i2l_int_pres
    (X : ar_obj Ar) (β : ar_carrier Ar X -> B)
    (Hβ : is_measurable_path β)
    (µ : fmeas R (ar_carrier Ar X)) :
  linhom_pre_fun i2l_pre (icone_integral β Hβ µ) =
  icone_integral
    (fun r => linhom_pre_fun i2l_pre (β r))
    (linhom_pre_pres_path i2l_pre X β Hβ) µ.
Proof.
rewrite /i2l_pre /= (icones_hom_pres_int h X β Hβ µ).
by congr icone_integral; exact: Prop_irrelevance.
Qed.

Definition icones_as_linhom : linhom_car Ar B C :=
  MkLinhom i2l_pre i2l_int_pres.

Lemma icones_as_linhomE (x : B) : linhom_fun icones_as_linhom x = Lfun h x.
Proof. by []. Qed.

Lemma icones_as_linhom_norm_le1 : cone_norm icones_as_linhom <= 1.
Proof.
rewrite -[cone_norm _]/(linhom_norm icones_as_linhom).
apply: linhom_norm_sup_lub => x Hx.
by apply: le_trans (cones_hom_norm_le1 _ x) _.
Qed.

End IConesToLinhomLocal.

Arguments icones_as_linhom {R Ar B C} h.
Arguments icones_as_linhomE {R Ar B C} h.
Arguments icones_as_linhom_norm_le1 {R Ar B C} h.

(** ** ω-continuity of pre/post composition by an icones_hom

    These are CONSEQUENCES (NOT new theorems) of the fact that
    [linhom_post_icones g] is an icones_hom, hence its underlying
    [cones_hom_fun] is ω-continuous on the unit ball.  We expose the
    equation in the form we need downstream. *)

Section LinhomPostPreSup.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

(** Post-composition by an icones_hom [g] preserves linhom-cone suprema. *)
Lemma linhom_post_icones_sup (C D1 D2 : ICone.type Ar)
    (g : icones_hom Ar D1 D2)
    (u : nat -> linhom_car Ar C D1)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, cone_norm (u n) <= 1)
    (gch : forall n, precone_le (linhom_post g (u n)) (linhom_post g (u n.+1)))
    (gub : forall n, cone_norm (linhom_post g (u n)) <= 1) :
  linhom_post g (cone_sup_ball u uch ub1) =
  cone_sup_ball (linhom_post g \o u) gch gub.
Proof.
set hh := @linhom_post_icones R Ar C _ _ g.
have Hcont :
    is_omega_continuous (cones_hom_fun
       (mcones_hom_cones (icones_hom_mcones hh))).
  exact: cones_hom_continuous.
have HE : Lfun hh (cone_sup_ball u uch ub1) =
          linhom_post g (cone_sup_ball u uch ub1).
  exact: linhom_post_iconesE.
rewrite -HE (Hcont u uch ub1 gch gub).
apply: precone_le_anti.
- apply: cone_sup_ball_lub => n.
  exact: (cone_sup_ball_ub (linhom_post g \o u) gch gub n).
- apply: cone_sup_ball_lub => n.
  exact: (cone_sup_ball_ub _ gch gub n).
Qed.

(** Pre-composition by an icones_hom [h] preserves linhom-cone suprema. *)
Lemma linhom_pre_icones_sup (C1 C2 D : ICone.type Ar)
    (h : icones_hom Ar C2 C1)
    (u : nat -> linhom_car Ar C1 D)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, cone_norm (u n) <= 1)
    (hch : forall n, precone_le (linhom_pre_act h (u n)) (linhom_pre_act h (u n.+1)))
    (hub : forall n, cone_norm (linhom_pre_act h (u n)) <= 1) :
  linhom_pre_act h (cone_sup_ball u uch ub1) =
  cone_sup_ball (linhom_pre_act h \o u) hch hub.
Proof.
set hh := @linhom_pre_icones R Ar _ _ D h.
have Hcont :
    is_omega_continuous (cones_hom_fun
       (mcones_hom_cones (icones_hom_mcones hh))).
  exact: cones_hom_continuous.
have HE : Lfun hh (cone_sup_ball u uch ub1) =
          linhom_pre_act h (cone_sup_ball u uch ub1).
  exact: linhom_pre_iconesE.
rewrite -HE (Hcont u uch ub1 hch hub).
apply: precone_le_anti.
- apply: cone_sup_ball_lub => n.
  exact: (cone_sup_ball_ub (linhom_pre_act h \o u) hch hub n).
- apply: cone_sup_ball_lub => n.
  exact: (cone_sup_ball_ub _ hch hub n).
Qed.

End LinhomPostPreSup.

Arguments linhom_post_icones_sup {R Ar C D1 D2}.
Arguments linhom_pre_icones_sup {R Ar C1 C2 D}.

(** ** ω-continuity of [prom] — Paper §9

    The promotion [x ↦ x! = sc_fun (nl B) x] is ω-continuous on the unit
    ball of [B] with image in the unit ball of [!B].  This is the
    [is_scott_continuous_unit] field of [nl B]'s [sc_meas_stable], reduced
    via [cone_sup_at_ball] (image radius = 1, since [‖x!‖ ≤ 1] for
    [‖x‖ ≤ 1] by [prom_ball]). *)

Section PromContinuous.
Variables (R : realType) (Ar : MeasSubcat R).

Lemma prom_omega_cont (B : ICone.type Ar)
    (y : nat -> B)
    (ych : forall n, precone_le (y n) (y n.+1))
    (yub1 : forall n, cone_norm (y n) <= 1)
    (pch : forall n, precone_le (prom (y n)) (prom (y n.+1)))
    (pub1 : forall n, cone_norm (prom (y n)) <= 1) :
  prom (cone_sup_ball y ych yub1) =
  cone_sup_ball (prom \o y) pch pub1.
Proof.
have [[_ _ Hsc] _] := sc_meas_stable (nl B).
move: Hsc; rewrite /is_scott_continuous_unit => Hsc.
have pubM : forall n, cone_norm ((prom \o y) n) <= (1%:nng : {nonneg R})%:num.
  by move=> n /=; exact: pub1.
have HE : prom (cone_sup_ball y ych yub1) =
          cone_sup_at (u := prom \o y) pch pubM ltr01.
  exact: (Hsc 1%:nng y ych yub1 pch pubM ltr01).
by rewrite HE (cone_sup_at_ball pch pub1 pubM ltr01).
Qed.

End PromContinuous.

Arguments prom_omega_cont {R Ar B} y.

(** ** ω-continuity of [bang_fmap] — the workhorse for [coalg_hom_sup]

    [bang_fmap] commutes with linhom-cone suprema, in the sense that

      [bang_fmap (linhom_icones (sup u_n)) = linhom_icones (sup (bang_fmap u_n))].

    The PROOF: both sides are norm-≤-1 linhom_car [!B → !C] elements;
    by [bang_ext_linhom] it suffices to check agreement on every [x!]
    ([‖x‖ ≤ 1]).

    - LHS at [x!]: [bang_fmap_prom] gives [(linhom_fun (sup u_n) x)!];
      by [linhom_sup_fun_unitE] this is [(sup_n (linhom_fun u_n x))!].
    - RHS at [x!]: [linhom_sup_fun_unitE] gives [sup_n (bang_fmap u_n x!)];
      [bang_fmap_prom] reduces each to [(linhom_fun u_n x)!]; the whole
      sup is [sup_n ((linhom_fun u_n x)!)].

    These are equal by [prom_omega_cont] applied to the unit-ball chain
    [n ↦ linhom_fun u_n x : C]. *)

Section BangFmapContinuous.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

(** "Lift" of an icones_hom along [bang_fmap], as a linhom_car of norm
    ≤ 1.  This is the [linhom_car]-level shadow of [bang_fmap], used to
    state ω-continuity. *)
Definition bang_fmap_lin (B C : ICone.type Ar)
    (f : icones_hom Ar B C) : linhom_car Ar (Bang Ar B) (Bang Ar C) :=
  icones_as_linhom (bang_fmap f).

Lemma bang_fmap_lin_norm_le1 (B C : ICone.type Ar) (f : icones_hom Ar B C) :
  cone_norm (bang_fmap_lin f) <= 1.
Proof. exact: icones_as_linhom_norm_le1. Qed.

(** Pointwise reading on promoted points: [bang_fmap_lin f x! = (f x)!]. *)
Lemma bang_fmap_lin_prom (B C : ICone.type Ar)
    (f : icones_hom Ar B C) (x : B) :
  cone_norm x <= 1 ->
  linhom_fun (bang_fmap_lin f) (prom x) = prom (Lfun f x).
Proof. by move=> Hx; rewrite /bang_fmap_lin icones_as_linhomE bang_fmap_prom. Qed.

(** **The headline ω-continuity of [bang_fmap]** at the linhom level.

    Given a unit-ball ω-chain [u_n] of [linhom_car B C], let
    [Sicones := linhom_icones (norm-bound of [linhom_sup_ball ...]) :
                  icones_hom B C] be the icones_hom packaging of the sup,
    and let [B_n := bang_fmap_lin (linhom_icones (ub1 n))].  Then
    [icones_as_linhom (bang_fmap Sicones)] equals the linhom-cone sup of
    the [B_n] chain. *)

Lemma bang_fmap_lin_omega_cont (B C : ICone.type Ar)
    (u : nat -> linhom_car Ar B C)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, cone_norm (u n) <= 1)
    (LHS_norm : cone_norm (linhom_sup_ball u uch ub1) <= 1)
    (B_n := fun n => bang_fmap_lin (linhom_icones (u n) (ub1 n)))
    (bch : forall n, precone_le (B_n n) (B_n n.+1))
    (bub1 : forall n, cone_norm (B_n n) <= 1) :
  bang_fmap_lin (linhom_icones _ LHS_norm) =
  linhom_sup_ball B_n bch bub1.
Proof.
apply: (bang_ext_linhom _ _ (bang_fmap_lin_norm_le1 _)
                            (linhom_sup_ball_norm B_n bch bub1)).
move=> x Hx.
(* LHS at [x!]: [bang_fmap_prom] reduces it to [(linhom_fun S x)!]. *)
rewrite (bang_fmap_lin_prom (linhom_icones _ LHS_norm) Hx).
(* Underlying value [linhom_fun S x = linhom_sup_fun uch ub1 x] (definitional);
   then by [linhom_sup_fun_unitE] this is the pointwise [cone_sup_ball]. *)
have LHS_eq : Lfun (linhom_icones _ LHS_norm) x =
              linhom_sup_fun uch ub1 x.
  by rewrite -[Lfun _ x]/(linhom_fun (linhom_sup_ball u uch ub1) x).
rewrite LHS_eq (linhom_sup_fun_unitE uch ub1 Hx) linhom_sup_unitE.
(* RHS at [x!]: [linhom_fun (linhom_sup_ball B_n ...) x! = linhom_sup_fun ... x!]
   which, since [‖x!‖ ≤ 1], equals [cone_sup_ball (n => B_n n at x!)]. *)
have prom_ub : cone_norm (prom x) <= 1 by exact: prom_ball.
rewrite -[linhom_fun (linhom_sup_ball B_n bch bub1) (prom x)]
        /(linhom_sup_fun bch bub1 (prom x)).
rewrite (linhom_sup_fun_unitE bch bub1 prom_ub) linhom_sup_unitE.
(* Both sides are now [cone_sup_ball] over [Bang Ar C].  Compute the RHS
   chain: [linhom_fun (B_n n) x! = (linhom_fun (u n) x)!] by
   [bang_fmap_lin_prom]. *)
have RHSch_eq : forall n,
    linhom_fun (B_n n) (prom x) = prom (linhom_fun (u n) x).
  by move=> n; rewrite /B_n bang_fmap_lin_prom //; exact: icones_as_linhomE.
(* The two [cone_sup_ball]s have definitionally-equal underlying chains:
   LHS chain: [n ↦ prom (linhom_fun (u n) x)] (from [prom_omega_cont]).
   RHS chain: [n ↦ linhom_fun (B_n n) (prom x)] = [n ↦ prom (linhom_fun (u n) x)]
              (by [RHSch_eq]). *)
pose w (n : nat) : C := linhom_fun (u n) x.
have wch : forall n, precone_le (w n) (w n.+1).
  by move=> n; rewrite /w; exact: linhom_sup_pw_chain uch x n.
have wub1 : forall n, cone_norm (w n) <= 1.
  move=> n; rewrite /w.
  apply: (linhom_sup_pw_ub1 (u := u)) => //; exact: Hx.
have pwch : forall n, precone_le (prom (w n)) (prom (w n.+1)).
  by move=> n; rewrite /w; have := linhom_sup_pw_chain bch (prom x) n; rewrite !RHSch_eq.
have pwub1 : forall n, cone_norm (prom (w n)) <= 1.
  by move=> n; exact: prom_ball.
(* The LHS, after pre-rewrites, is [prom (cone_sup_ball (n => linhom_fun (u n) x) ...)]
   for the syntactically-fixed chain/bound witnesses from [linhom_sup_unitE].
   The RHS is [cone_sup_ball (n => linhom_fun (B_n n) (prom x)) ...] with
   the latter chain being [n => prom (linhom_fun (u n) x)] (by [RHSch_eq]).
   Both [cone_sup_ball]s are determined by their underlying chain (up to
   the witness, which is proof-irrelevant by [precone_le_anti]).

   We close by [prom_omega_cont] (which pushes [prom] through the LHS
   [cone_sup_ball]) and [precone_le_anti] over the [cone_sup_ball]s with
   chains [n => prom (linhom_fun (u n) x)] vs.
   [n => linhom_fun (B_n n) (prom x)] (which are pointwise-equal via
   [RHSch_eq]). *)
rewrite (prom_omega_cont (fun n => linhom_fun (u n) x) _ _ pwch pwub1).
apply: precone_le_anti.
- apply: cone_sup_ball_lub => n.
  rewrite -[((prom \o (fun n0 : nat => linhom_fun (u n0) x)) n)]
          /(prom (linhom_fun (u n) x)).
  rewrite -RHSch_eq.
  exact: cone_sup_ball_ub.
- apply: cone_sup_ball_lub => n.
  rewrite -[(fun n0 : nat => linhom_fun (B_n n0) (prom x)) n]
          /(linhom_fun (B_n n) (prom x)).
  rewrite RHSch_eq.
  exact: (cone_sup_ball_ub _ pwch pwub1 n).
Qed.

End BangFmapContinuous.
