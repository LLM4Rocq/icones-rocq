(**md**************************************************************************)
(** * ω-continuity prerequisites for the CBV value fixpoint — CBV §6 (prep)

    *** PPL CBV chapter infrastructure

    This file is NOT part of the Ehrhard-Geoffroy 2025 formalization.
    It provides ω-continuity infrastructure for the CBV value-fixpoint
    construction [Yfix_value_cond] in [theories/programs/infra/em_fix.v],
    which underlies the [ne_fix] constructor of the CBV PPL.

    Key lemmas: [bang_fmap_lin_omega_cont], [prom_omega_cont],
    [linhom_pre/post_icones_sup], [tensor_mor_omega_cont_R],
    [tensor_mor_R_lin_incr].

    ---

    Prerequisites for the CBV value fixpoint construction
    ([theories/programs/infra/em_fix.v]).  We package the genuinely-new ω-continuity
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
Require Import Icones.homs.tensor.
Require Import Icones.homs.smcc.
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

(** ** Pure-tensor extensionality at the [linhom_car] level

    Two norm-[≤1] linear maps [φ, ψ : B ⊗ C ⊸ D] agreeing on every pure
    tensor [x ⊗p y] (no norm restriction on [x], [y]) are equal.
    Package each as an [icones_hom] via [linhom_icones]; the [icones_hom]
    level [tensor_ext] (Paper Prop 5.14) yields their equality; then
    [linhom_eq] transports back. *)

Section TensorExtLinhom.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

Lemma tensor_ext_linhom (B C D : ICone.type Ar)
    (phi psi : linhom_car Ar (tensor Ar B C) D)
    (Hphi : cone_norm phi <= 1) (Hpsi : cone_norm psi <= 1) :
  (forall (x : B) (y : C),
     linhom_fun phi (ptensor x y) = linhom_fun psi (ptensor x y)) ->
  phi = psi.
Proof.
move=> Hpp.
have Heq : linhom_icones phi Hphi = linhom_icones psi Hpsi.
  apply: tensor_ext => x y.
  by rewrite !linhom_iconesE; exact: Hpp.
apply: linhom_eq => z.
by rewrite -(linhom_iconesE phi Hphi z) -(linhom_iconesE psi Hpsi z) Heq.
Qed.

End TensorExtLinhom.

Arguments tensor_ext_linhom {R Ar B C D} phi psi Hphi Hpsi.

(** ** ω-continuity of [tensor_mor (icones_id G) ·] — the workhorse for [Yfix_value]

    Given a unit-ball ω-chain [u_n : linhom_car C1 C2], the icones_hom
    [tensor_mor (icones_id G) (linhom_icones (sup u_n) LHS_norm)] equals
    (at the [icones_as_linhom] level) the linhom-cone supremum of
    [n ↦ icones_as_linhom (tensor_mor (icones_id G) (linhom_icones u_n (ub1 n)))].

    The proof mirrors [bang_fmap_lin_omega_cont]: by [tensor_ext_linhom]
    it suffices to check both sides at every pure tensor [x ⊗p y] (any
    [x : G], [y : C1], in fact we use the unit-ball [‖y‖ ≤ 1] case after
    a scaling argument).  At a pure tensor:
    - LHS at [x ⊗p y] = [x ⊗p (Lfun (linhom_icones (sup u_n) _) y)]
                      = [x ⊗p (linhom_fun (sup u_n) y)]
                      = [x ⊗p (cone_sup_ball (n ↦ linhom_fun u_n y) ...)]
      (by [tensor_morE] + [linhom_sup_fun_unitE] on unit-ball [y]).
    - RHS at [x ⊗p y] = [linhom_sup_fun (T_n) (x ⊗p y)]
                      = [cone_sup_ball (n ↦ linhom_fun (T_n n) (x ⊗p y))]
                      = [cone_sup_ball (n ↦ x ⊗p (linhom_fun u_n y))]
      (by [linhom_sup_fun_unitE] + [tensor_morE]).
    Both are equal by ω-continuity of the linhom [tau G C2 x] on the
    unit-ball chain [n ↦ linhom_fun u_n y]; [tau G C2 x] is a [linhom_car]
    (hence has [linhom_pre_continuous]). *)

Section TensorMorIdLinOmegaCont.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

(** "Linhom-shadow" of [tensor_mor (icones_id G) f] for [f : C1 → C2]:
    the [icones_as_linhom] packaging of [tensor_mor (icones_id G) f] as a
    [linhom_car (G ⊗ C1) (G ⊗ C2)]. *)
Definition tensor_mor_R_lin (G C1 C2 : ICone.type Ar)
    (f : icones_hom Ar C1 C2) :
    linhom_car Ar (tensor Ar G C1) (tensor Ar G C2) :=
  icones_as_linhom (tensor_mor (icones_id Ar G) f).

Lemma tensor_mor_R_lin_norm_le1 (G C1 C2 : ICone.type Ar)
    (f : icones_hom Ar C1 C2) :
  cone_norm (tensor_mor_R_lin G f) <= 1.
Proof. exact: icones_as_linhom_norm_le1. Qed.

(** Pointwise reading on a pure tensor [x ⊗p y]:
    [tensor_mor_R_lin G f (x ⊗p y) = x ⊗p (f y)]. *)
Lemma tensor_mor_R_lin_ptensor (G C1 C2 : ICone.type Ar)
    (f : icones_hom Ar C1 C2) (x : G) (y : C1) :
  linhom_fun (tensor_mor_R_lin G f) (ptensor x y) = ptensor x (Lfun f y).
Proof.
rewrite /tensor_mor_R_lin icones_as_linhomE tensor_morE.
by rewrite -[Lfun (icones_id Ar G) x]/x.
Qed.

(** **The headline ω-continuity of [tensor_mor (icones_id G) ·]** at the linhom level.

    Given a unit-ball ω-chain [u_n] of [linhom_car C1 C2], let
    [T_n := tensor_mor_R_lin G (linhom_icones (u n) (ub1 n)) :
                                linhom_car (G ⊗ C1) (G ⊗ C2)].  Then
    [tensor_mor_R_lin G (linhom_icones (sup u_n) LHS_norm)] equals the
    linhom-cone sup of the [T_n] chain. *)
Lemma tensor_mor_omega_cont_R (G C1 C2 : ICone.type Ar)
    (u : nat -> linhom_car Ar C1 C2)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, cone_norm (u n) <= 1)
    (LHS_norm : cone_norm (linhom_sup_ball u uch ub1) <= 1)
    (T_n := fun n => tensor_mor_R_lin G (linhom_icones (u n) (ub1 n)))
    (tch : forall n, precone_le (T_n n) (T_n n.+1))
    (tub1 : forall n, cone_norm (T_n n) <= 1) :
  tensor_mor_R_lin G (linhom_icones _ LHS_norm) =
  linhom_sup_ball T_n tch tub1.
Proof.
apply: (tensor_ext_linhom _ _ (tensor_mor_R_lin_norm_le1 _ _)
                              (linhom_sup_ball_norm T_n tch tub1)).
move=> x y.
(* LHS at [x ⊗p y]: [tensor_mor_R_lin G (linhom_icones (sup u_n)) (x ⊗p y) =
   x ⊗p Lfun (linhom_icones (sup u_n) LHS_norm) y = x ⊗p (linhom_fun (sup u_n) y)]. *)
rewrite tensor_mor_R_lin_ptensor.
have LHS_eq : Lfun (linhom_icones _ LHS_norm) y =
              linhom_fun (linhom_sup_ball u uch ub1) y by [].
rewrite LHS_eq.
(* RHS at [x ⊗p y]: unfold the linhom-sup. *)
rewrite -[linhom_fun (linhom_sup_ball T_n tch tub1) _]
        /(linhom_sup_fun tch tub1 (ptensor x y)).
(* Cases on whether [y] is in the unit ball or not; the pure-tensor is
   linear in [y], so we can reduce to the unit-ball case via the standard
   scaling trick if needed.  Easier: split on [cnorm y]. *)
have ptensor_xy_norm : cone_norm (ptensor x y) <= cone_norm x * cone_norm y
  by exact: tensor_norm_le.
(* The proof goes via two-sided [precone_le_anti] over [cone_sup_ball]s. *)
(* Reduce [y] to unit-ball by scaling.  Let [r := cnorm y + 1] (always > 0),
   [rinv := r^-1], [y' := rinv •: y].  Then [cnorm y' <= 1], and by
   linearity in the right slot ([ptensorZr]), [x ⊗p y = r •: (x ⊗p y')]. *)
set rinv := cnorm_succ_inv_nng y.
set r := cnorm_succ_nng y.
set y' := precone_scale rinv y.
have y'_ub : cone_norm y' <= 1 by exact: cnorm_inv_unit.
have y_eq : y = precone_scale r y' by rewrite /y' cnorm_succ_scaleK.
(* Rewrite [x ⊗p y = r •: (x ⊗p y')] on both sides, then by linearity of
   [linhom_fun] in the input (which is what [linhom_sup_fun] also respects)
   both reduce to [r •: ...]; cancel [r] and work at unit-ball [y']. *)
(* For the LHS, [x ⊗p (linhom_fun (sup u) y) = x ⊗p (linhom_fun (sup u) (r •: y'))
   = x ⊗p (r •: linhom_fun (sup u) y')] (by linearity of the linhom in input)
   [= r •: (x ⊗p linhom_fun (sup u) y')] (by [ptensorZr]). *)
have LHS_lin : linhom_fun (linhom_sup_ball u uch ub1) y =
               precone_scale r (linhom_fun (linhom_sup_ball u uch ub1) y').
  rewrite y_eq /linhom_fun.
  by have [_ _ HZ] :=
    linhom_pre_linear (linhom_pre_of (linhom_sup_ball u uch ub1)); rewrite HZ.
rewrite LHS_lin ptensorZr.
(* For the RHS, [linhom_sup_fun tch tub1 (x ⊗p y) = linhom_sup_fun tch tub1 (r •: (x ⊗p y'))
   = r •: linhom_sup_fun tch tub1 (x ⊗p y')] (by linearity of the sup-linhom). *)
have RHS_lin : linhom_sup_fun tch tub1 (ptensor x y) =
               precone_scale r (linhom_sup_fun tch tub1 (ptensor x y')).
  rewrite {1}y_eq ptensorZr.
  have [_ _ HZ] := linhom_pre_linear
                     (linhom_pre_of (linhom_sup_ball T_n tch tub1)).
  exact: HZ.
rewrite RHS_lin.
(* Cancel the [r] scaling on both sides. *)
congr (precone_scale _ _).
(* Now work at unit-ball [y']. *)
(* LHS: [x ⊗p linhom_fun (sup u) y' = x ⊗p (cone_sup_ball (n ↦ linhom_fun u_n y') ...)]
   (by [linhom_sup_fun_unitE]).  Then by ω-continuity of [tau G C2 x] as a linhom
   (its underlying [linhom_pre_fun] is ω-continuous), push [x ⊗p] through the sup. *)
have LHS_at_y' : linhom_fun (linhom_sup_ball u uch ub1) y' =
                 linhom_sup_unit uch ub1 y'_ub
  by exact: linhom_sup_fun_unitE.
rewrite LHS_at_y' linhom_sup_unitE.
(* RHS at unit-ball [x ⊗p y']: need [cone_norm (x ⊗p y') <= 1] to apply
   [linhom_sup_fun_unitE].  This requires unit-ball [x]; we'll do another
   scaling step on [x]. *)
set xinv := cnorm_succ_inv_nng x.
set xr := cnorm_succ_nng x.
set x' := precone_scale xinv x.
have x'_ub : cone_norm x' <= 1 by exact: cnorm_inv_unit.
have x_eq : x = precone_scale xr x' by rewrite /x' cnorm_succ_scaleK.
have xy'_norm : cone_norm (ptensor x' y') <= 1.
  apply: (le_trans (tensor_norm_le _ _)).
  apply: mulr_ile1 => //; exact: cone_norm_ge0.
(* For the LHS we have [x ⊗p (cone_sup_ball ...)].  Rewrite [x = xr •: x'],
   distribute by [ptensorZl], then push [xr •:] outside the [cone_sup_ball]
   via [cone_sup_ball_scale]; remains to push [x' ⊗p ·] through the sup. *)
rewrite x_eq ptensorZl.
(* RHS at [(xr •: x') ⊗p y']: rewrite [(xr •: x') ⊗p y' = xr •: (x' ⊗p y')]
   by [ptensorZl], then pull [xr •:] outside [linhom_sup_fun] by linearity. *)
have RHS_xrEq : linhom_sup_fun tch tub1 (ptensor (precone_scale xr x') y') =
                precone_scale xr (linhom_sup_fun tch tub1 (ptensor x' y')).
  rewrite ptensorZl.
  have [_ _ HZ] := linhom_pre_linear
                     (linhom_pre_of (linhom_sup_ball T_n tch tub1)).
  exact: HZ.
rewrite RHS_xrEq.
have RHS_at_xy' : linhom_sup_fun tch tub1 (ptensor x' y') =
                  linhom_sup_unit tch tub1 xy'_norm
  by exact: linhom_sup_fun_unitE.
rewrite RHS_at_xy' linhom_sup_unitE.
(* Cancel the [xr •:] on both sides. *)
congr (precone_scale _ _).
(* Both sides are [cone_sup_ball] over [tensor Ar G C2].  Their chains:
   LHS chain = [n ↦ ptensor x' (linhom_fun (u n) y')] (after [ptensor_x'] push through)
   RHS chain = [n ↦ linhom_fun (T_n n) (ptensor x' y')]
             = [n ↦ ptensor x' (linhom_fun (u n) y')] by [tensor_mor_R_lin_ptensor].
   To bridge, apply ω-continuity of [tau G C2 x'] (a linhom) on the
   unit-ball chain [n ↦ linhom_fun (u n) y'] (which IS in the unit ball by
   [linhom_sup_pw_ub1]). *)
pose w (n : nat) : C2 := linhom_fun (u n) y'.
have wch : forall n, precone_le (w n) (w n.+1)
  by move=> n; rewrite /w; exact: linhom_sup_pw_chain uch y' n.
have wub1 : forall n, cone_norm (w n) <= 1
  by move=> n; rewrite /w; apply: linhom_sup_pw_ub1 => //.
(* The linhom [tau G C2 x'] is ω-continuous; its underlying function applied to
   a chain reduces sup at the chain.  [linhom_fun (tau G C2 x') = ptensor x']
   by definition. *)
have ptensor_x'_cont : is_omega_continuous (fun v : C2 => ptensor x' v).
  by exact: (linhom_pre_continuous (linhom_pre_of (tau G C2 x'))).
have pch : forall n, precone_le (ptensor x' (w n)) (ptensor x' (w n.+1)).
  move=> n; rewrite /w.
  apply: (linear_increasing (f := ptensor x'));
    last by exact: wch.
  exact: (linhom_pre_linear (linhom_pre_of (tau G C2 x'))).
have pub1 : forall n, cone_norm (ptensor x' (w n)) <= 1.
  move=> n; apply: (le_trans (tensor_norm_le _ _)).
  apply: mulr_ile1; first exact: cone_norm_ge0.
  - exact: cone_norm_ge0.
  - exact: x'_ub.
  - exact: wub1.
(* Bridge the [cone_sup_ball] witnesses: the LHS sup is over the SAME
   chain as [w], but with different proof witnesses (proof-irrelevant). *)
have heq : cone_sup_ball (fun n => linhom_fun (u n) y')
             [eta linhom_sup_pw_chain uch y'] (linhom_sup_pw_ub1 ub1 y'_ub) =
           cone_sup_ball w wch wub1.
  apply: precone_le_anti.
    by apply: cone_sup_ball_lub => n; exact: cone_sup_ball_ub.
  by apply: cone_sup_ball_lub => n; exact: cone_sup_ball_ub.
rewrite heq.
rewrite (ptensor_x'_cont w wch wub1 pch pub1).
(* Now both sides are [cone_sup_ball] over [tensor G C2] with the SAME chain
   (modulo [tensor_mor_R_lin_ptensor]); close by [precone_le_anti]. *)
apply: precone_le_anti.
- apply: cone_sup_ball_lub => n /=.
  (* LHS chain at n: [ptensor x' (linhom_fun (u n) y')] = [linhom_fun (T_n n) (ptensor x' y')]
     by [tensor_mor_R_lin_ptensor]. *)
  have HE : ptensor x' (linhom_fun (u n) y') =
            linhom_fun (T_n n) (ptensor x' y').
    rewrite /T_n /=.
    by rewrite (tensor_mor_R_lin_ptensor (linhom_icones (u n) (ub1 n)) x' y').
  rewrite HE.
  exact: cone_sup_ball_ub.
- apply: cone_sup_ball_lub => n.
  have HE : linhom_fun (T_n n) (ptensor x' y') =
            ptensor x' (linhom_fun (u n) y').
    rewrite /T_n.
    by rewrite (tensor_mor_R_lin_ptensor (linhom_icones (u n) (ub1 n)) x' y').
  rewrite HE.
  exact: (cone_sup_ball_ub _ pch pub1 n).
Qed.

End TensorMorIdLinOmegaCont.

Arguments tensor_mor_R_lin {R Ar} G {C1 C2} f.
Arguments tensor_mor_R_lin_norm_le1 {R Ar} G {C1 C2} f.
Arguments tensor_mor_R_lin_ptensor {R Ar} G {C1 C2} f x y.
Arguments tensor_mor_omega_cont_R {R Ar} G {C1 C2} u uch ub1 LHS_norm.

(** ** Monotonicity of [tensor_mor (icones_id G) ·] — the workhorse for Yfix_fun

    Dual to [tensor_mor_omega_cont_R] (ω-continuity).  Given a
    [precone_le prev1 prev2] of [linhom_car C1 C2] (with both norms
    [≤ 1]), the [linhom_car]-shadow [tensor_mor_R_lin G ·] is monotone
    in its argument.

    **Proof outline.**  Unpack [precone_le prev1 prev2] to a witness
    [δ : linhom_car C1 C2] with [prev2 = prev1 + δ].  [δ ≤p prev2]
    (witness [prev1] via commutativity), hence [‖δ‖ ≤ ‖prev2‖ ≤ 1]
    by [cone_normp].  The witness for the goal [precone_le] is
    [tensor_mor_R_lin G (linhom_icones δ Hδ)].  The required equation
    [tensor_mor_R_lin G prev2_ic = tensor_mor_R_lin G prev1_ic +
    tensor_mor_R_lin G δ_ic] reduces — via the 1/2 scaling trick — to
    a pure-tensor check covered by [tensor_ext_linhom].  After scaling
    both sides by 1/2 (each summand of the RHS now has norm ≤ 1/2,
    total ≤ 1; the LHS has norm ≤ 1/2), [tensor_ext_linhom] applies,
    and the pure-tensor equation [x ⊗p (prev2 y) = (x ⊗p (prev1 y)) +
    (x ⊗p (δ y))] holds by [tensor_mor_R_lin_ptensor] +
    right-additivity of [x ⊗p ·] (linhom_pre_linear of [tau G C2 x]). *)

Section TensorMorRLinIncr.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

Lemma tensor_mor_R_lin_incr (G C1 C2 : ICone.type Ar)
    (prev1 prev2 : linhom_car Ar C1 C2)
    (H1 : cone_norm prev1 <= 1) (H2 : cone_norm prev2 <= 1) :
  precone_le prev1 prev2 ->
  precone_le (tensor_mor_R_lin G (linhom_icones prev1 H1))
             (tensor_mor_R_lin G (linhom_icones prev2 H2)).
Proof.
move=> Hle.
case: Hle => δ Hδ.
have δ_le_prev2 : precone_le δ prev2.
  by exists prev1; rewrite Hδ; symmetry; exact: precone_addC.
have δ_norm : cone_norm δ <= 1.
  by apply: le_trans H2; exact: cone_normp.
exists (tensor_mor_R_lin G (linhom_icones δ δ_norm)).
(* Replace [precone_add] on linhom_car by the concrete [linhom_add]. *)
have <- : linhom_add (tensor_mor_R_lin G (linhom_icones prev1 H1))
                     (tensor_mor_R_lin G (linhom_icones δ δ_norm)) =
          precone_add (tensor_mor_R_lin G (linhom_icones prev1 H1))
                      (tensor_mor_R_lin G (linhom_icones δ δ_norm))
  by [].
(* Half/two setup for the scaling trick. *)
have half_ge0 : 0 <= ((2 : R)^-1) by rewrite invr_ge0 ler0n.
pose half : {nonneg R} := NngNum half_ge0.
have two_ge0 : 0 <= ((2 : R)) by rewrite ler0n.
pose two : {nonneg R} := NngNum two_ge0.
have half_le1 : half%:num <= 1.
  by rewrite /= invf_le1// ?ler1n//; exact: ltr0Sn.
have two_half_eq : (two%:num * half%:num)%:nng = 1%:nng :> {nonneg R}.
  by apply: val_inj => /=; rewrite mulfV// gt_eqF// ltr0Sn.
(* Scale both sides by [1 = two * half]. *)
rewrite -[X in X = _]linhom_scale_1.
rewrite -[X in _ = X]linhom_scale_1.
rewrite -[in X in X = _]two_half_eq linhom_scale_A.
rewrite -[in X in _ = X]two_half_eq linhom_scale_A.
congr (linhom_scale two _).
rewrite linhom_scale_DAr.
(* Now both sides have norm ≤ 1 after [half] scaling.  Apply
   [tensor_ext_linhom] to reduce to a pure-tensor check. *)
have prev2_lin_norm : linhom_norm (tensor_mor_R_lin G (linhom_icones prev2 H2)) <= 1
  by exact: tensor_mor_R_lin_norm_le1.
have prev1_lin_norm : linhom_norm (tensor_mor_R_lin G (linhom_icones prev1 H1)) <= 1
  by exact: tensor_mor_R_lin_norm_le1.
have δ_lin_norm : linhom_norm (tensor_mor_R_lin G (linhom_icones δ δ_norm)) <= 1
  by exact: tensor_mor_R_lin_norm_le1.
have LHS_norm :
  cone_norm (linhom_scale half (tensor_mor_R_lin G (linhom_icones prev2 H2))) <= 1.
  rewrite -[cone_norm _]/(linhom_norm _) linhom_normh.
  rewrite -[X in _ <= X]mulr1; apply: ler_pM => //.
  exact: linhom_norm_ge0.
have RHS_norm :
  cone_norm (linhom_add
    (linhom_scale half (tensor_mor_R_lin G (linhom_icones prev1 H1)))
    (linhom_scale half (tensor_mor_R_lin G (linhom_icones δ δ_norm)))) <= 1.
  rewrite -[cone_norm _]/(linhom_norm _).
  apply: le_trans (linhom_normt _ _) _.
  rewrite !linhom_normh.
  have e2 : half%:num * 1 + half%:num * 1 = 1.
    by rewrite mulr1 -mulr2n -mulr_natr /= mulVf// gt_eqF// ltr0Sn.
  rewrite -e2; apply: lerD; apply: ler_pM => //; exact: linhom_norm_ge0.
apply: (tensor_ext_linhom _ _ LHS_norm RHS_norm).
move=> x y.
(* Pointwise reading at [x ⊗p y].  LHS: [half •: (x ⊗p (prev2 y))]. *)
have LHS_pt :
  linhom_fun (linhom_scale half (tensor_mor_R_lin G (linhom_icones prev2 H2)))
             (ptensor x y) =
  precone_scale half (ptensor x (linhom_fun prev2 y)).
  rewrite /linhom_fun /= /linhom_scale_fun.
  congr (precone_scale half _).
  by rewrite -[linhom_fun _ _]/(linhom_fun (tensor_mor_R_lin G (linhom_icones prev2 H2)) (ptensor x y)) tensor_mor_R_lin_ptensor linhom_iconesE.
rewrite LHS_pt.
(* RHS pointwise. *)
have RHS_pt :
  linhom_fun (linhom_add
    (linhom_scale half (tensor_mor_R_lin G (linhom_icones prev1 H1)))
    (linhom_scale half (tensor_mor_R_lin G (linhom_icones δ δ_norm))))
    (ptensor x y) =
  precone_add (precone_scale half (ptensor x (linhom_fun prev1 y)))
              (precone_scale half (ptensor x (linhom_fun δ y))).
  rewrite /linhom_fun /= /linhom_add_fun /linhom_scale_fun.
  congr (precone_add _ _); congr (precone_scale half _).
  - by rewrite -[linhom_fun _ _]/(linhom_fun (tensor_mor_R_lin G (linhom_icones prev1 H1)) (ptensor x y)) tensor_mor_R_lin_ptensor linhom_iconesE.
  - by rewrite -[linhom_fun _ _]/(linhom_fun (tensor_mor_R_lin G (linhom_icones δ δ_norm)) (ptensor x y)) tensor_mor_R_lin_ptensor linhom_iconesE.
rewrite RHS_pt.
(* Now: half •: x ⊗p (prev2 y) = (half •: (x ⊗p prev1 y)) + (half •: (x ⊗p δ y)). *)
(* Use Hδ: prev2 = prev1 + δ, hence prev2(y) = prev1(y) + δ(y). *)
have prev2_y :
  linhom_fun prev2 y = precone_add (linhom_fun prev1 y) (linhom_fun δ y).
  by have /(congr1 (fun h => linhom_fun h y)) /= := Hδ.
rewrite prev2_y.
(* x ⊗p (a + b) = (x ⊗p a) + (x ⊗p b) by linearity of tau B C x. *)
have tau_lin :
  ptensor x (precone_add (linhom_fun prev1 y) (linhom_fun δ y)) =
  precone_add (ptensor x (linhom_fun prev1 y)) (ptensor x (linhom_fun δ y)).
  rewrite /ptensor /linhom_fun.
  by have [_ HD _] := linhom_pre_linear (linhom_pre_of (tau G C2 x)); exact: HD.
rewrite tau_lin.
(* half •: (a + b) = (half •: a) + (half •: b). *)
exact: precone_scale_DAr.
Qed.

End TensorMorRLinIncr.

Arguments tensor_mor_R_lin_incr {R Ar} G {C1 C2} prev1 prev2 H1 H2.
