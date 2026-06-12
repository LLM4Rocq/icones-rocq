(**md**************************************************************************)
(** * [em_fix_value] — the seeded CBV value-fixpoint combinator

    *** BEYOND THE PAPER — PPL CBV chapter infrastructure

    This file is NOT part of the Ehrhard-Geoffroy 2025 formalization
    (paper §9.2 has [Yfix] at SCones level for CBN; the CBV value
    fixpoint is paper-level folklore, not in the literature).

    *** Why this file exists: the naive zero-seeded iteration is degenerate

    Section [CbvFixDegeneracy] below records, as a theorem, that the
    naive zero-seeded Kleene iteration of [em_fix.v]'s linear step
    [Phi_fun] — the previous CBV value-fixpoint operator, since removed
    from [em_fix.v] — is the ZERO linhom: always, for every diagonal
    [diag] and every body [M] ([Phi_fun_lfp_eq0] = [Phi_fun_zero] + the
    generic [lfp_eq0] of [stable/fixpoint.v]).  Structurally: [Phi_fun]
    is LINEAR in the previous iterate, so it preserves the linhom
    cone-zero seed, and the least fixpoint collapses to [0].  The bottom
    of a CBV function VALUE type is NOT the cone-zero of [!L]: it is the
    promoted zero [prom 0], the diverging-function value (of
    [e_bang]-mass one).

    *** The repaired combinator (expert recipe, 2026-06-10)

    We build the fixpoint COMBINATOR as a morphism of [!]-coalgebras

      [fix_comb : EM( !(!A ⊸ !A), !A )]

    (domain/codomain are the COFREE coalgebras), determined on promoted
    points [F!] for [F] in the unit ball of [!A ⊸ !A] by

      [fix_comb (F!) = (sup_n x_n)!]   where
      [x_0 = 0 : A],  [x_{n+1} = der (F (x_n !))]

    — the INTERLEAVED Kleene chain: [x ↦ der (F (x!))] is monotone
    ([nl] analytic, [F] and [der] linear) from the genuine bottom
    [0 : A], so no degeneracy.

    The two expert obligations:

    (a) the formula extends to a genuine coalgebra morphism.  Route:
        the assignment [F ↦ sup_n x_n] is the composite of [SCones]
        morphisms

          [fix_value := Yfix_A ∘ curry (Ev ∘ ⟨lts(der∘F)∘π₁, nl∘π₂⟩)]

        ([stable/fixpoint.v]'s §9.2 combinator [Yfix : (A ⇒ₛ A) → A],
        the CCC combinators of [stable/scones_ccc.v], and the
        linear-to-stable lift [linhom_to_stablehom] of
        [stable/diag_bilinear_tensor.v]).  A stable map [(!A⊸!A) → A]
        IS a linear map [!(!A⊸!A) ⊸ A] via the SAFT hom-bijection
        ([lin]/[Theta], [homs/bang.v]); then [adj_psi] of the [U ⊣ !̃]
        adjunction packages the linear map as the EM-morphism
        [fix_comb] into the cofree coalgebra — coalgebra-morphism-ness
        is BY CONSTRUCTION.

    (b) when [F] is itself a coalgebra morphism [!A → !A], the formula
        simplifies to the LITERAL chain: [fix_comb (F!) =
        sup_n F^n(0!)] ([fix_coalg_simpl]) — the interleaved and the
        literal chains coincide because coalgebraic [F] sends promoted
        points to promoted points ([fix_setlike_prom]).

    *** Exported interface (consumed by the wiring phase)

    - [kleene_from] / [lfp_from] — generic SEEDED Kleene core on any
      cone, with hypothesis [b0 <=p f b0] replacing the [precone_le0]
      base of [em_fix.v]'s zero-seeded [linhom_lfp] (gate finding 2).
    - [fix_chain F n] — the interleaved chain, with [_0]/[_S]/[_ball]/
      [_chain] access lemmas ([fix_chain_S] is the per-iterate law).
    - [fix_value : scones_hom (!A ⊸ !A) A] with [fix_value_E] (value =
      sup of the interleaved chain), [fix_value_unfold] (the fixpoint
      equation [der (F ((fix_value F)!)) = fix_value F]).
    - [fix_lin := lin fix_value] with [fix_lin_promE].
    - [fix_comb := adj_psi fix_lin : coalg_hom !̃(!A⊸!A) !̃A] with
      [fix_comb_mor], [fix_prom_E] (the prom-point computation law).
    - Obligation (b): [fix_coalg_simpl], [fix_unfold_coalg].
    - Non-degeneracy: [fix_prom_neq0] (the combinator NEVER returns the
      zero of [!A] on promoted bodies — contrast [Phi_fun_lfp_eq0]),
      and the identity-body witness [fix_id_E] / [fix_id_nontrivial]:
      the fix of the identity body is the diverging value [0!], which
      is provably nonzero.

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
Require Import Icones.mcones.path.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_cat.
Require Import Icones.icones.examples_icone.
Require Import Icones.stable.totmono.
Require Import Icones.stable.stablehom.
Require Import Icones.stable.scones_cat.
Require Import Icones.stable.scones_ccc.
Require Import Icones.stable.fixpoint.
Require Import Icones.stable.stab_lin_swap.
Require Import Icones.stable.diag_bilinear_tensor.
Require Import Icones.homs.linhom.
Require Import Icones.homs.linhom_functor.
Require Import Icones.homs.bilin.
Require Import Icones.homs.exp_adjunction.
Require Import Icones.homs.bang_construct.
Require Import Icones.homs.bang.
Require Import Icones.homs.seely_defs.
Require Import Icones.homs.seely.
Require Import Icones.homs.coalgebra.
Require Import Icones.homs.em_cat.
Require Import Icones.homs.em_seely_comonoid.
(* NOTE: the tensor stack comes AFTER the Seely/EM stack on purpose:
   [seely.v] and [tensor_hom_iso.v] both export a [linhom_icones]
   constant; the §1 degeneracy proofs must see [tensor_hom_iso]'s (the
   one [em_fix.v]'s lemma statements use). *)
Require Import Icones.homs.tensor.
Require Import Icones.homs.tensor_construct.
Require Import Icones.homs.smcc.
Require Import Icones.homs.tensor_iso.
Require Import Icones.homs.tensor_hom_iso.
Require Import Icones.programs.infra.em_fix.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** [prom] is by definition the underlying map of [nl] — recorded as an
    equation BEFORE the [Opaque] block below. *)
Lemma promE (R : realType) (Ar : MeasSubcat R) (B : ICone.type Ar) (x : B) :
  sc_fun (nl B) x = prom x.
Proof. by []. Qed.

(* Block aggressive unfolding of the SAFT comonad data: [dig], [der],
   [bang_fmap] are [lin]-composites, so a naive [rewrite !Lfun_comp]
   recurses into the [Bang] construction internals. *)
Local Opaque dig der prom bang_fmap.

(** ** §1 — The degeneracy record: the zero-seeded Kleene iteration of
       the naive linear step is [0], always

    The honest record of WHY the seeded combinator of §3 exists (gate
    M-R.0, confirmed 2026-06-10).  [em_fix.v]'s [Phi_fun] is linear in
    the previous iterate, so it kills the linhom cone-zero seed
    ([Phi_fun_zero] — the linearity content) and the zero-seeded least
    fixpoint [linhom_lfp (Phi_fun diag M)] — the operator that used to
    be [em_fix.v]'s CBV value-fixpoint, removed after this proof — is
    [0] by the generic [lfp_eq0] of [stable/fixpoint.v]
    ([Phi_fun_lfp_eq0]). *)

Section CbvFixDegeneracy.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (Gamma B : ICone.type Ar).
Variable diag : icones_hom Ar Gamma (tensor Ar Gamma Gamma).
Variable M : icones_hom Ar (tensor Ar Gamma B) B.

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

(** The cone-zero of any linhom cone is in the unit ball. *)
Lemma zero_ball (C D : ICone.type Ar) :
  cone_norm (precone_zero : linhom_car Ar C D) <= 1.
Proof. by rewrite cone_norm0. Qed.

(** [linhom_fun] of the cone-zero is the pointwise zero (named so that
    [rewrite] picks it up — gate finding 3). *)
Lemma linhom_fun_zero (C D : ICone.type Ar) (x : C) :
  linhom_fun (precone_zero : linhom_car Ar C D) x = precone_zero.
Proof. by []. Qed.

(** [icones_id] is the identity function (named — gate finding 3). *)
Lemma icones_idE (C : ICone.type Ar) (x : C) :
  Lfun (icones_id Ar C) x = x.
Proof. by []. Qed.

(** [tensor.v]'s pure tensor (the one in [tensor_mor_R_lin_ptensor])
    vanishes on a right zero — by linearity of [tau C D x].  NB: this is
    a DIFFERENT constant from [tensor_hom_iso.v]'s [ptensor], whose
    exported [ptensor_0l]/[ptensor_0r] do NOT rewrite it (gate
    finding 1). *)
Lemma ptensor_zero_r (C D : ICone.type Ar) (x : C) :
  ptensor x (precone_zero : D) = precone_zero.
Proof.
rewrite ptensorE.
by have [Z0 _ _] := linhom_pre_linear (linhom_pre_of (tau C D x)).
Qed.

(** STEP A: [id_Γ ⊗ 0 = 0] at the linhom level. *)
Lemma tensor_mor_R_lin_zero :
  tensor_mor_R_lin Gamma
    (linhom_icones (precone_zero : linhom_car Ar Gamma B) (zero_ball _ _)) =
  precone_zero.
Proof.
apply: (tensor_ext_linhom _ _ (tensor_mor_R_lin_norm_le1 _ _) (zero_ball _ _)).
move=> x y.
rewrite tensor_mor_R_lin_ptensor linhom_iconesE linhom_fun_zero ptensor_zero_r.
by rewrite linhom_fun_zero.
Qed.

(** STEP B: the Kleene step kills zero. *)
Lemma Phi_fun_zero : Phi_fun diag M precone_zero = precone_zero.
Proof.
rewrite (Phi_fun_unit diag M precone_zero (zero_ball _ _)) /Phi_fun_safe.
rewrite tensor_mor_R_lin_zero.
apply: linhom_eq => g.
rewrite /linhom_post /linhom_pre_act !linhom_map_funE.
rewrite linhom_fun_zero icones_idE.
have [M0 _ _] := cones_hom_linear (mcones_hom_cones (icones_hom_mcones M)).
by rewrite M0 linhom_fun_zero.
Qed.

(** STEP C: every Kleene iterate is zero. *)
Lemma kleene_lin_Phi_fun_eq0 n :
  kleene_lin (Phi_fun diag M) n = precone_zero.
Proof.
elim: n => [|n IH] //.
by rewrite kleene_lin_S IH Phi_fun_zero.
Qed.

(** STEP D: the zero-seeded Kleene iteration of the naive linear step
    [Phi_fun] is the zero linhom — DEGENERACY.  This is the operator
    that used to be [em_fix.v]'s CBV value-fixpoint (removed after this
    proof); the collapse is the generic [lfp_eq0] of
    [stable/fixpoint.v] applied to the linearity content
    [Phi_fun_zero]. *)
Lemma Phi_fun_lfp_eq0 :
  linhom_lfp (Phi_fun diag M) (Phi_fun_incr diag M) (Phi_fun_ball diag M) =
  precone_zero.
Proof. exact: lfp_eq0 Phi_fun_zero. Qed.

End CbvFixDegeneracy.

Arguments zero_ball {R Ar} C D.
Arguments linhom_fun_zero {R Ar C D} x.
Arguments icones_idE {R Ar C} x.
Arguments ptensor_zero_r {R Ar C D} x.
Arguments tensor_mor_R_lin_zero {R Ar} Gamma B.
Arguments Phi_fun_zero {R Ar Gamma B} diag M.
Arguments kleene_lin_Phi_fun_eq0 {R Ar Gamma B} diag M n.
Arguments Phi_fun_lfp_eq0 {R Ar Gamma B} diag M.

(** ** §2 — Seeded Kleene core on a cone

    The generic Kleene chain [iter n f b0] for an ARBITRARY seed [b0]
    with [b0 <=p f b0] replacing the [precone_le0] base of the
    zero-seeded chains ([stable/fixpoint.v]'s [kleene], [em_fix.v]'s
    [kleene_lin]).  Stated on a bare [coneType] so it covers both
    cone-point chains (the literal chain [F^n(0!)] of obligation (b))
    and linhom-level chains. *)

Section SeededKleene.
Variable R : realType.
Variable B : coneType R.

Variable f : B -> B.
Variable b0 : B.
Hypothesis f_incr : forall x y : B,
  precone_le x y -> cone_norm y <= 1 -> precone_le (f x) (f y).
Hypothesis f_ball : forall x : B, cone_norm x <= 1 -> cone_norm (f x) <= 1.
Hypothesis b0_ball : cone_norm b0 <= 1.
Hypothesis b0_le : precone_le b0 (f b0).

(** The seeded Kleene chain [n ↦ fⁿ(b0)]. *)
Definition kleene_from (n : nat) : B := iter n f b0.

Lemma kleene_from_0 : kleene_from 0 = b0. Proof. by []. Qed.

Lemma kleene_from_S n : kleene_from n.+1 = f (kleene_from n).
Proof. by rewrite /kleene_from iterS. Qed.

Lemma kleene_from_ball n : cone_norm (kleene_from n) <= 1.
Proof.
elim: n => [|n IH]; first by rewrite kleene_from_0.
by rewrite kleene_from_S; exact: f_ball.
Qed.

Lemma kleene_from_chain n : precone_le (kleene_from n) (kleene_from n.+1).
Proof.
elim: n => [|n IH]; first by rewrite kleene_from_0 kleene_from_S kleene_from_0.
rewrite ![kleene_from _.+1]kleene_from_S; apply: f_incr => //.
rewrite -kleene_from_S; exact: kleene_from_ball.
Qed.

(** The seeded least-fixpoint candidate (sup of the seeded chain). *)
Definition lfp_from : B :=
  cone_sup_ball kleene_from kleene_from_chain kleene_from_ball.

Lemma lfp_from_ball : cone_norm lfp_from <= 1.
Proof. exact: cone_sup_ball_norm. Qed.

Lemma kleene_from_le_lfp n : precone_le (kleene_from n) lfp_from.
Proof. exact: cone_sup_ball_ub. Qed.

(** The fixpoint equation, under ω-continuity of [f] on the ball. *)
Hypothesis f_cont : is_omega_continuous f.

Lemma lfp_from_fixpoint : f lfp_from = lfp_from.
Proof.
rewrite /lfp_from.
have fuch n : precone_le ((f \o kleene_from) n) ((f \o kleene_from) n.+1).
  by rewrite /comp; apply: f_incr;
    [exact: kleene_from_chain | exact: kleene_from_ball].
have fub1 n : cone_norm ((f \o kleene_from) n) <= 1.
  by rewrite /comp; apply: f_ball; exact: kleene_from_ball.
rewrite (@f_cont kleene_from kleene_from_chain kleene_from_ball fuch fub1).
apply: precone_le_anti.
- apply: cone_sup_ball_lub => n.
  rewrite -[(f \o kleene_from) n]/(f (kleene_from n)) -kleene_from_S.
  exact: (cone_sup_ball_ub kleene_from kleene_from_chain
            kleene_from_ball n.+1).
- apply: cone_sup_ball_lub => n.
  apply: (precone_le_trans (y := (f \o kleene_from) n)).
    by rewrite -[(f \o kleene_from) n]/(f (kleene_from n)) -kleene_from_S;
      exact: kleene_from_chain.
  exact: cone_sup_ball_ub.
Qed.

End SeededKleene.

Arguments kleene_from {R B} f b0 n.
Arguments kleene_from_S {R B} f b0 n.
Arguments kleene_from_ball {R B f b0} f_ball b0_ball n.
Arguments kleene_from_chain {R B f b0} f_incr f_ball b0_ball b0_le n.
Arguments lfp_from {R B f b0} f_incr f_ball b0_ball b0_le.
Arguments lfp_from_fixpoint {R B f b0} f_incr f_ball b0_ball b0_le f_cont.

(** ** §3 — The CBV value-fixpoint combinator

    Fix [A : ICone.type Ar].  Write [!A := Bang Ar A] and
    [LL := !A ⊸ !A] (the cone of LINEAR endo-bodies). *)

Section FixCombinator.
Variables (R : realType) (Ar : MeasSubcat R).
Variable A : ICone.type Ar.

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation BA := (Bang Ar A).
Local Notation LL := (linhom_car Ar (Bang Ar A) (Bang Ar A)).

(** *** §3.1 — The interleaved chain [x_0 = 0, x_{n+1} = der (F (x_n!))] *)

Definition fix_chain (F : LL) (n : nat) : A :=
  iter n (fun x : A => Lfun (der A) (linhom_fun F (prom x)))
         (precone_zero : A).

Lemma fix_chain_0 (F : LL) : fix_chain F 0 = precone_zero.
Proof. by []. Qed.

(** Per-iterate access law (M4-facing). *)
Lemma fix_chain_S (F : LL) (n : nat) :
  fix_chain F n.+1 = Lfun (der A) (linhom_fun F (prom (fix_chain F n))).
Proof. by rewrite /fix_chain iterS. Qed.

Section FixChainFacts.
Variable F : LL.
Hypothesis HF : cone_norm F <= 1.

(** One step of the interleaved iteration stays in the ball. *)
Lemma fix_step_ball (x : A) :
  cone_norm x <= 1 ->
  cone_norm (Lfun (der A) (linhom_fun F (prom x))) <= 1.
Proof.
move=> Hx.
apply: le_trans (cones_hom_norm_le1 _ _) _.
apply: le_trans (linhom_norm_apply_le HF (prom x)) _.
by rewrite mul1r; exact: prom_ball.
Qed.

Lemma fix_chain_ball n : cone_norm (fix_chain F n) <= 1.
Proof.
elim: n => [|n IH]; first by rewrite fix_chain_0 cone_norm0.
by rewrite fix_chain_S; exact: fix_step_ball.
Qed.

(** Promotion is monotone on the unit ball ([nl] is totally monotone). *)
Lemma prom_incr (x y : A) :
  precone_le x y -> cone_norm y <= 1 ->
  precone_le (prom x) (prom y).
Proof.
have [[Htm _ _] _] := sc_meas_stable (nl A).
exact: (tm_incr_le Htm).
Qed.

(** One step of the interleaved iteration is monotone on the ball:
    [prom] analytic (totally monotone), [F] and [der] linear. *)
Lemma fix_step_incr (x y : A) :
  precone_le x y -> cone_norm y <= 1 ->
  precone_le (Lfun (der A) (linhom_fun F (prom x)))
             (Lfun (der A) (linhom_fun F (prom y))).
Proof.
move=> Hxy Hy.
have Hp : precone_le (prom x) (prom y) by exact: prom_incr.
have HFp : precone_le (linhom_fun F (prom x)) (linhom_fun F (prom y)).
  by apply: linear_increasing Hp; exact: (linhom_pre_linear (linhom_pre_of F)).
apply: linear_increasing HFp.
exact: cones_hom_linear.
Qed.

Lemma fix_chain_chain n :
  precone_le (fix_chain F n) (fix_chain F n.+1).
Proof.
elim: n => [|n IH]; first by rewrite fix_chain_0; exact: precone_le0.
rewrite 2!fix_chain_S.
by apply: fix_step_incr => //; exact: fix_chain_ball.
Qed.

End FixChainFacts.

(** *** §3.2 — The stable body [F ↦ (x ↦ der (F (x!)))] via the CCC

    Built entirely from existing [SCones] morphisms, so total
    monotonicity / ω-continuity / path-measurability come for free:

    - [fix_lts : LL → (!A ⇒ₛ A)], [F ↦ lts (der ∘ F)] — the
      linear-to-stable lift precomposed with the (linear) action
      [linhom_post (der A)];
    - [fix_step := Ev ∘ ⟨fix_lts ∘ π₁, nl ∘ π₂⟩ : LL × A → A];
    - [fix_body := curry fix_step : LL → (A ⇒ₛ A)]. *)

Definition fix_lts_fun (F : LL) : stablehom BA A :=
  linhom_to_stablehom (linhom_post (der A) F).

Lemma fix_lts_fun_ball (F : LL) :
  cone_norm F <= 1 -> cone_norm (fix_lts_fun F) <= 1.
Proof.
move=> HF.
apply: le_trans (linhom_to_stablehom_norm_le _) _.
rewrite -linhom_post_iconesE.
exact: le_trans (cones_hom_norm_le1 _ _) HF.
Qed.

Lemma fix_lts_fun_meas_stable : is_meas_stable fix_lts_fun.
Proof.
apply: (meas_stable_comp_post (linhom_post_icones (der A))
          (linhom_to_stablehom (B := BA) (C := A))).
exact: linhom_to_stablehom_meas_stable.
Qed.

Lemma fix_lts_norm_le1 : sc_norm (sc_clamp fix_lts_fun) <= 1.
Proof.
apply: sc_norm_lub => F HF.
rewrite (sc_clamp_ball HF).
exact: fix_lts_fun_ball.
Qed.

Definition fix_lts : scones_hom LL (stablehom BA A) :=
  MkSconesHom (sc_clamp fix_lts_fun)
              (sc_clamp_meas_stable fix_lts_fun_meas_stable)
              fix_lts_norm_le1
              (sc_clamp_offball_field _).

Lemma fix_lts_E (F : LL) :
  cone_norm F <= 1 -> sc_fun fix_lts F = fix_lts_fun F.
Proof. by move=> HF; rewrite /fix_lts /= (sc_clamp_ball HF). Qed.

(** Projections out of the product [LL × A]. *)
Local Notation pF := (scones_proj (sprod_fam LL A) true).
Local Notation px := (scones_proj (sprod_fam LL A) false).

Definition fix_step : scones_hom (sprod LL A) A :=
  scones_comp (Ev BA A)
    (scpair (scones_comp fix_lts pF) (scones_comp (nl A) px)).

(** Pointwise computation of the step on the ball. *)
Lemma fix_step_E (F : LL) (x : A) :
  cone_norm F <= 1 -> cone_norm x <= 1 ->
  sc_fun fix_step (sprod_pair F x) =
  Lfun (der A) (linhom_fun F (prom x)).
Proof.
move=> HF Hx.
have Hp : cone_norm (sprod_pair F x) <= 1 by exact: sprod_pair_norm_le1.
have [HpFv HpxV] := sproj_ball Hp.
rewrite sprod_fstE in HpFv; rewrite sprod_sndE in HpxV.
rewrite /fix_step (scomp_ball _ _ Hp).
rewrite (scpair_ball _ _ Hp).
rewrite (scomp_ball _ _ Hp) HpFv (fix_lts_E HF).
rewrite (scomp_ball _ _ Hp) HpxV.
rewrite promE.
rewrite (Ev_pair (fix_lts_fun F) (prom x)); last first.
  by apply: sprod_pair_norm_le1;
    [exact: fix_lts_fun_ball | exact: prom_ball].
rewrite /fix_lts_fun (linhom_to_stablehom_E _ _ (prom_ball Hx)).
rewrite /linhom_post linhom_map_funE.
by rewrite icones_idE.
Qed.

Definition fix_body : scones_hom LL (stablehom A A) :=
  curry fix_step.

Lemma fix_body_E (F : LL) (x : A) :
  cone_norm F <= 1 -> cone_norm x <= 1 ->
  sh_fun (sc_fun fix_body F) x =
  Lfun (der A) (linhom_fun F (prom x)).
Proof.
move=> HF Hx.
by rewrite /fix_body (curry_appE fix_step F x HF Hx) (fix_step_E HF Hx).
Qed.

(** *** §3.3 — [Yfix] evaluates to the zero-seeded Kleene sup

    [stable/fixpoint.v] builds [Yfix] as the least fixpoint of the
    higher-order [Z]-combinator; here we identify its VALUE at a
    unit-ball [f : A ⇒ₛ A] with the supremum of the plain Kleene chain
    [n ↦ fⁿ(0)] (evaluation at [f] is a linear ω-continuous map on the
    stablehom cone, so it passes through the [sfix] supremum). *)

Definition yfix_chain (f : stablehom A A) (n : nat) : A :=
  iter n (sh_fun f) (precone_zero : A).

Lemma yfix_chain_ball (f : stablehom A A) (Hf : cone_norm f <= 1) n :
  cone_norm (yfix_chain f n) <= 1.
Proof.
elim: n => [|n IH]; first by rewrite /yfix_chain /= cone_norm0.
rewrite /yfix_chain iterS.
apply: le_trans (sh_norm_ub f _ IH) _.
exact: Hf.
Qed.

Lemma yfix_chain_chain (f : stablehom A A) (Hf : cone_norm f <= 1) n :
  precone_le (yfix_chain f n) (yfix_chain f n.+1).
Proof.
have [[Htm _ _] _] := sh_meas_stable f.
elim: n => [|n IH]; first by exact: precone_le0.
rewrite /yfix_chain !iterS.
apply: (tm_incr_le Htm IH).
exact: yfix_chain_ball.
Qed.

(** The [Z]-combinator iterates, evaluated at [f], are the plain Kleene
    iterates of [f]. *)
Lemma Zcomb_kleene_at (f : stablehom A A) (Hf : cone_norm f <= 1) n :
  sh_fun (kleene (sc_fun (Zcomb A)) n) f = yfix_chain f n.
Proof.
elim: n => [|n IH]; first by [].
rewrite [kleene _ n.+1](kleeneS _ n).
rewrite (ZE (kleene_ball (@sc_ball_pres _ _ _ (Zcomb A)) n) Hf).
by rewrite IH /yfix_chain iterS.
Qed.

(** THE identification: [Yfix f = sup_n fⁿ(0)] for unit-ball [f]. *)
Lemma Yfix_kleeneE (f : stablehom A A) (Hf : cone_norm f <= 1) :
  sc_fun (Yfix A) f =
  cone_sup_ball (yfix_chain f) (yfix_chain_chain Hf) (yfix_chain_ball Hf).
Proof.
rewrite (YfixE f) /Yfix_elt /sfix /lfp.
set u := kleene (sc_fun (Zcomb A)).
set uch := kleene_chain _ _.
set ub1 := kleene_ball _.
have fuch n : precone_le (sh_eval_at_fun f (u n)) (sh_eval_at_fun f (u n.+1)).
  by rewrite /sh_eval_at_fun; exact: sh_le_pointwise (uch n) f.
have fub1 n : cone_norm (sh_eval_at_fun f (u n)) <= 1.
  rewrite /sh_eval_at_fun.
  by apply: le_trans (sh_norm_ub (u n) f Hf) _; exact: ub1.
rewrite -[sh_fun (cone_sup_ball u uch ub1) f]
        /(sh_eval_at_fun f (cone_sup_ball u uch ub1)).
rewrite ((@sh_eval_at_continuous R Ar (stablehom A A) A f)
           u uch ub1 fuch fub1).
apply: precone_le_anti.
- apply: cone_sup_ball_lub => n.
  rewrite -[(sh_eval_at_fun f \o u) n]/(sh_fun (u n) f).
  rewrite (Zcomb_kleene_at Hf n).
  exact: cone_sup_ball_ub.
- apply: cone_sup_ball_lub => n.
  rewrite -(Zcomb_kleene_at Hf n).
  rewrite -[sh_fun (u n) f]/((sh_eval_at_fun f \o u) n).
  exact: cone_sup_ball_ub.
Qed.

(** *** §3.4 — The value map [fix_value : (!A ⊸ !A) → A] in [SCones] *)

Definition fix_value : scones_hom LL A :=
  scones_comp (Yfix A) fix_body.

Lemma fix_value_ball (F : LL) :
  cone_norm F <= 1 -> cone_norm (sc_fun fix_value F) <= 1.
Proof. exact: sc_image_ball. Qed.

(** The defining computation: [fix_value F] is the sup of the
    INTERLEAVED chain. *)
Lemma fix_value_E (F : LL) (HF : cone_norm F <= 1) :
  sc_fun fix_value F =
  cone_sup_ball (fix_chain F) (fix_chain_chain HF) (fix_chain_ball HF).
Proof.
rewrite /fix_value (scomp_ball _ _ HF).
set f := sc_fun fix_body F.
have Hf : cone_norm f <= 1 by exact: (sc_image_ball fix_body HF).
rewrite (Yfix_kleeneE Hf).
have HE n : yfix_chain f n = fix_chain F n.
  elim: n => [|n IH] //.
  rewrite /yfix_chain iterS -/(yfix_chain f n) IH fix_chain_S.
  by rewrite /f (fix_body_E HF (fix_chain_ball HF n)).
apply: precone_le_anti.
- apply: cone_sup_ball_lub => n.
  rewrite HE; exact: cone_sup_ball_ub.
- apply: cone_sup_ball_lub => n.
  rewrite -(HE n); exact: cone_sup_ball_ub.
Qed.

(** The fixpoint equation of the value map (from [Yfix_fix]). *)
Lemma fix_value_unfold (F : LL) (HF : cone_norm F <= 1) :
  Lfun (der A) (linhom_fun F (prom (sc_fun fix_value F))) =
  sc_fun fix_value F.
Proof.
rewrite /fix_value (scomp_ball _ _ HF).
set f := sc_fun fix_body F.
have Hf : cone_norm f <= 1 by exact: (sc_image_ball fix_body HF).
have HY : cone_norm (sc_fun (Yfix A) f) <= 1.
  exact: (sc_image_ball (Yfix A) Hf).
have := Yfix_fix f Hf.
by rewrite /f (fix_body_E HF HY).
Qed.

(** *** §3.5 — The linear extension [fix_lin] (the lin/nl bridge)

    A stable map [(!A ⊸ !A) → A] IS a linear map [!(!A ⊸ !A) ⊸ A]:
    [lin]/[Theta] of the SAFT construction ([homs/bang.v]).  This is
    obligation (a)'s "linear extension to the whole Bang", obtained by
    the universal property — no fresh order analysis of the SAFT [Bang]
    is needed. *)

Definition fix_lin : icones_hom Ar (Bang Ar LL) A := lin fix_value.

(** On promoted points, [fix_lin] computes the value map. *)
Lemma fix_lin_promE (F : LL) (HF : cone_norm F <= 1) :
  Lfun fix_lin (prom F) = sc_fun fix_value F.
Proof.
have H := Theta_prom (lin fix_value) F HF.
rewrite ThetaK in H.
by rewrite /fix_lin -H.
Qed.

(** *** §3.6 — The combinator [fix_comb] as an EM-morphism

    [fix_comb := adj_psi fix_lin : EM(!̃(!A⊸!A), !̃A)] — a coalgebra
    morphism BY CONSTRUCTION (obligation (a) discharged). *)

Definition fix_comb :
    coalg_hom (bang_cofree (linhom_car Ar (Bang Ar A) (Bang Ar A)))
              (bang_cofree A) :=
  adj_psi (P := bang_cofree LL) fix_lin.

Lemma fix_comb_mor :
  ch_mor fix_comb = icones_comp (bang_fmap fix_lin) (dig LL).
Proof. by []. Qed.

(** The prom-point computation law — the expert's defining formula. *)
Lemma fix_prom_E (F : LL) (HF : cone_norm F <= 1) :
  Lfun (ch_mor fix_comb) (prom F) = prom (sc_fun fix_value F).
Proof.
rewrite fix_comb_mor Lfun_comp (dig_prom _ HF).
rewrite (bang_fmap_prom fix_lin _ (prom_ball HF)).
by rewrite (fix_lin_promE HF).
Qed.

(** Norm bound (the underlying [icones_hom] is norm-decreasing). *)
Lemma fix_comb_norm (v : Bang Ar LL) :
  cone_norm (Lfun (ch_mor fix_comb) v) <= cone_norm v.
Proof. exact: cones_hom_norm_le1. Qed.

(** *** §3.7 — Non-degeneracy

    On EVERY promoted body the combinator returns a promoted point of
    [!A], which is NEVER the cone-zero (its [e_bang]-mass is [one1]).
    Contrast [Phi_fun_lfp_eq0]. *)

Lemma prom_neq0 (x : A) :
  cone_norm x <= 1 -> prom x <> (precone_zero : Bang Ar A).
Proof.
move=> Hx Heq.
have H1 : Lfun (e_bang A) (prom x) = one1 by exact: e_bang_prom.
have [Z0 _ _] := cones_hom_linear
  (mcones_hom_cones (icones_hom_mcones (e_bang A))).
rewrite Heq Z0 in H1.
have := congr1 (fun z : cone_one_car Ar => (c1_val z)%:num) H1.
by rewrite /= => /esym /eqP; rewrite oner_eq0.
Qed.

Lemma fix_prom_neq0 (F : LL) (HF : cone_norm F <= 1) :
  Lfun (ch_mor fix_comb) (prom F) <> precone_zero.
Proof.
rewrite (fix_prom_E HF).
by apply: prom_neq0; exact: fix_value_ball.
Qed.

End FixCombinator.

Arguments fix_chain {R Ar A} F n.
Arguments fix_chain_S {R Ar A} F n.
Arguments fix_chain_ball {R Ar A F} HF n.
Arguments fix_chain_chain {R Ar A F} HF n.
Arguments fix_value {R Ar} A.
Arguments fix_value_E {R Ar A F} HF.
Arguments fix_value_unfold {R Ar A F} HF.
Arguments fix_value_ball {R Ar A} F.
Arguments fix_lin {R Ar} A.
Arguments fix_lin_promE {R Ar A F} HF.
Arguments fix_comb {R Ar} A.
Arguments fix_comb_mor {R Ar} A.
Arguments fix_prom_E {R Ar A F} HF.
Arguments fix_prom_neq0 {R Ar A F} HF.
Arguments prom_neq0 {R Ar A x}.

(** ** §4 — Obligation (b): the coalgebraic-case simplification

    When [F] (as an [icones_hom] [!A → !A]) is itself a morphism of
    [!]-coalgebras, the interleaved chain promotes to the LITERAL chain
    [F^n(0!)], and the combinator computes its supremum — the naive
    Kleene iteration seeded at the diverging value [0!].  This is the
    regression anchor identifying [fix_comb] with the old
    [em_fix_arr.v]-style Bang-level iteration. *)

Section FixCoalgebraic.
Variables (R : realType) (Ar : MeasSubcat R).
Variable A : ICone.type Ar.

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation BA := (Bang Ar A).
Local Notation LL := (linhom_car Ar (Bang Ar A) (Bang Ar A)).

Variable F : LL.
Hypothesis HF : cone_norm F <= 1.
Hypothesis Fcoalg :
  is_coalg_mor (bang_cofree A) (bang_cofree A) (linhom_icones F HF).

(** A coalgebraic body maps promoted points to promoted points:
    [F(y!) = (der (F (y!)))!]. *)
Lemma fix_setlike_prom (y : A) (Hy : cone_norm y <= 1) :
  linhom_fun F (prom y) =
  prom (Lfun (der A) (linhom_fun F (prom y))).
Proof.
set w := linhom_fun F (prom y).
have Hw : cone_norm w <= 1.
  apply: le_trans (linhom_norm_apply_le HF (prom y)) _.
  by rewrite mul1r; exact: prom_ball.
(* Step 1: [dig (F (y!)) = (F (y!))!] from the coalg-mor equation.
   NB: controlled single rewrites only — a greedy [!Lfun_comp] would
   recurse into the SAFT internals of [dig]/[bang_fmap]. *)
have HC := congr1 (fun h : icones_hom Ar BA (Bang Ar BA) =>
                     Lfun h (prom y)) Fcoalg.
have HL : Lfun (icones_comp (coalg_str (bang_cofree A))
                            (linhom_icones F HF)) (prom y) =
          Lfun (dig A) w.
  by rewrite Lfun_comp linhom_iconesE.
have HR : Lfun (icones_comp (bang_fmap (linhom_icones F HF))
                            (coalg_str (bang_cofree A))) (prom y) =
          prom w.
  rewrite Lfun_comp (dig_prom _ Hy).
  rewrite (bang_fmap_prom (linhom_icones F HF) _ (prom_ball Hy)).
  by rewrite linhom_iconesE.
have Hdig : Lfun (dig A) w = prom w by rewrite -HL HC HR.
(* Step 2: apply [!der]; LHS gives [w] (right counit), RHS [der w]!. *)
have H2 := congr1 (Lfun (bang_fmap (der A))) Hdig.
rewrite (bang_fmap_prom (der A) _ Hw) in H2.
rewrite -[Lfun (bang_fmap (der A)) (Lfun (dig A) w)]
        /(Lfun (icones_comp (bang_fmap (der A)) (dig A)) w) in H2.
rewrite (comonad_counitR A) icones_idE in H2.
exact: H2.
Qed.

(** The literal chain is the promoted interleaved chain. *)
Lemma fix_iter_promE (n : nat) :
  iter n (linhom_fun F) (prom (precone_zero : A)) =
  prom (fix_chain F n).
Proof.
elim: n => [|n IH]; first by [].
rewrite iterS IH.
rewrite (fix_setlike_prom (fix_chain_ball HF n)).
by rewrite -fix_chain_S.
Qed.

(** The seeded-Kleene hypotheses for the literal chain
    [n ↦ Fⁿ(0!)] in [!A]. *)

Lemma fix_lit_incr (x y : BA) :
  precone_le x y -> cone_norm y <= 1 ->
  precone_le (linhom_fun F x) (linhom_fun F y).
Proof.
move=> Hxy _.
by apply: linear_increasing Hxy; exact: (linhom_pre_linear (linhom_pre_of F)).
Qed.

Lemma fix_lit_ball (x : BA) :
  cone_norm x <= 1 -> cone_norm (linhom_fun F x) <= 1.
Proof.
move=> Hx.
apply: le_trans (linhom_norm_apply_le HF x) _.
by rewrite mul1r.
Qed.

Lemma fix_seed_ball : cone_norm (prom (precone_zero : A)) <= 1.
Proof. by apply: prom_ball; rewrite cone_norm0. Qed.

(** The seed-order [0! <=p F(0!)] — the base case that the zero-seeded
    [linhom_lfp] could never provide (gate finding 2). *)
Lemma fix_seed_le :
  precone_le (prom (precone_zero : A))
             (linhom_fun F (prom (precone_zero : A))).
Proof.
rewrite (fix_setlike_prom (y := precone_zero)); last by rewrite cone_norm0.
have [[Htm _ _] _] := sc_meas_stable (nl A).
apply: (tm_incr_le Htm); first exact: precone_le0.
have := fix_chain_ball HF 1.
by rewrite fix_chain_S fix_chain_0.
Qed.

(** **Obligation (b)**: on a coalgebraic body, the combinator is the
    supremum of the literal chain [n ↦ Fⁿ(0!)] (seeded Kleene in [!A]). *)
Lemma fix_coalg_simpl :
  Lfun (ch_mor (fix_comb A)) (prom F) =
  lfp_from (f := linhom_fun F) (b0 := prom (precone_zero : A))
    fix_lit_incr fix_lit_ball fix_seed_ball fix_seed_le.
Proof.
rewrite (fix_prom_E HF) (fix_value_E HF) /lfp_from.
(* Push [prom] (= [nl A], Scott-continuous on the ball) through the
   interleaved sup. *)
have [[Htm _ Hsc] _] := sc_meas_stable (nl A).
have pch n : precone_le (sc_fun (nl A) (fix_chain F n))
                        (sc_fun (nl A) (fix_chain F n.+1)).
  by apply: (tm_incr_le Htm);
    [exact: fix_chain_chain | exact: fix_chain_ball].
have pb1 n : cone_norm (sc_fun (nl A) (fix_chain F n)) <= 1.
  by apply: (sc_image_ball (nl A)); exact: fix_chain_ball.
move: (Hsc); rewrite /is_scott_continuous_unit => Hc.
rewrite -promE.
rewrite (Hc 1%:nng (fix_chain F) (fix_chain_chain HF) (fix_chain_ball HF)
            pch pb1 ltr01).
rewrite (cone_sup_at_ball pch pb1 pb1 ltr01).
(* Identify the promoted interleaved chain with the literal chain. *)
apply: precone_le_anti.
- apply: cone_sup_ball_lub => n.
  rewrite promE -(fix_iter_promE n).
  rewrite -[iter n (linhom_fun F) _]
          /(kleene_from (linhom_fun F) (prom (precone_zero : A)) n).
  exact: cone_sup_ball_ub.
- apply: cone_sup_ball_lub => n.
  rewrite -[kleene_from _ _ n]/(iter n (linhom_fun F) (prom precone_zero)).
  rewrite (fix_iter_promE n) -promE.
  exact: cone_sup_ball_ub.
Qed.

(** The !A-level unfolding for coalgebraic bodies:
    [F (fix_comb (F!)) = fix_comb (F!)]. *)
Lemma fix_unfold_coalg :
  linhom_fun F (Lfun (ch_mor (fix_comb A)) (prom F)) =
  Lfun (ch_mor (fix_comb A)) (prom F).
Proof.
rewrite (fix_prom_E HF).
rewrite (fix_setlike_prom (fix_value_ball F HF)).
by rewrite (fix_value_unfold HF).
Qed.

End FixCoalgebraic.

Arguments fix_setlike_prom {R Ar A F} HF Fcoalg {y}.
Arguments fix_iter_promE {R Ar A F} HF Fcoalg n.
Arguments fix_coalg_simpl {R Ar A F} HF Fcoalg.
Arguments fix_unfold_coalg {R Ar A F} HF Fcoalg.

(** ** §5 — The identity-body witness

    The simplest honest instance: the identity body [id : !A ⊸ !A] IS a
    coalgebra morphism, its interleaved chain is constantly [0] (since
    [der (0!) = 0]), so [fix_comb (id!) = 0!] — the DIVERGING value, a
    promoted point of [e_bang]-mass one, provably NONZERO.  This is the
    abstract form of the plan's DoD witness: the combinator does not
    collapse, it returns the correct bottom-of-the-value-type. *)

Section FixIdentity.
Variables (R : realType) (Ar : MeasSubcat R).
Variable A : ICone.type Ar.

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation BA := (Bang Ar A).
Local Notation LL := (linhom_car Ar (Bang Ar A) (Bang Ar A)).

(** The identity body, as a linhom point. *)
Definition fix_idF : LL :=
  icones_to_linhom (icones_id Ar BA).

Lemma fix_idF_ball : cone_norm fix_idF <= 1.
Proof. exact: icones_to_linhom_norm_le1. Qed.

Lemma fix_idF_E (v : BA) : linhom_fun fix_idF v = v.
Proof. by rewrite /fix_idF icones_to_linhomE icones_idE. Qed.

(** The interleaved chain of the identity body is constantly [0]. *)
Lemma fix_chain_id (n : nat) : fix_chain fix_idF n = precone_zero.
Proof.
elim: n => [|n IH]; first by rewrite fix_chain_0.
rewrite fix_chain_S IH fix_idF_E.
by rewrite (der_prom (precone_zero : A)) // cone_norm0.
Qed.

(** [fix_comb (id!) = 0!] — the diverging value. *)
Lemma fix_id_E :
  Lfun (ch_mor (fix_comb A)) (prom fix_idF) = prom (precone_zero : A).
Proof.
rewrite (fix_prom_E fix_idF_ball) (fix_value_E fix_idF_ball).
congr (prom _).
apply: precone_le_anti.
- apply: cone_sup_ball_lub => n.
  rewrite fix_chain_id; exact: precone_le_refl.
- exact: precone_le0.
Qed.

(** The witness: the fix of the identity body is NOT zero. *)
Lemma fix_id_nontrivial :
  Lfun (ch_mor (fix_comb A)) (prom fix_idF) <> precone_zero.
Proof. exact: (fix_prom_neq0 fix_idF_ball). Qed.

End FixIdentity.

Arguments fix_idF {R Ar} A.
Arguments fix_id_E {R Ar} A.
Arguments fix_id_nontrivial {R Ar} A.
