(**md**************************************************************************)
(** * Rejection sampling denotes the normalised posterior — the headline

    BEYOND THE PAPER.  This file is NOT part of the Ehrhard-Geoffroy
    2025 formalization (paper §2-§9).  It assembles the full semantic
    analysis of the rejection-sampling program [ex_reject] of
    [theories/programs/examples.v]
    [[
       let rec rs accept :=
         let x = sample m in
         if Bernoulli (Meas{f} x) then accept x else rs accept
       in rs (λ y. y)
    ]]
    under the CBV interpreter [eD] of [theories/programs/ppl_cbv.v]: a
    HIGHER-ORDER (the recursive function abstracts over the acceptance
    continuation), PROBABILISTIC (continuous [sample] + value-dependent
    coin [ne_bernoulli_f]), NON-TERMINATING (rejection recurses, and
    may loop forever) program, whose denotation we identify in closed
    form.

    Writing [ν := ⟦ex_reject⟧(one1) : FMeas R_obj],
    [If := ∫ f dµ] and [IUf U := ∫_U f dµ], the results are:

    - [ex_reject_master] : [If * ν(U) = IUf U]  — unconditionally
      (graceful at [If = 0]);
    - [ex_reject_is_normalised_posterior] : [0 < If] implies
      [ν(U) = IUf U / If]  — the normalised posterior of the prior [µ]
      given the soft acceptance predicate [f];
    - [ex_reject_posterior_simple] : [If = 1] implies [ν(U) = IUf U];
    - [ex_reject_mass_one] : [0 < If] implies [ν(setT) = 1] — the
      sampler terminates almost surely whenever acceptance has
      positive mass;
    - [ex_reject_zero] : [f ≡ 0] implies [ν = 0] — certain rejection
      diverges.

    The proof is the 6-step reduction chain of the plan:
    1. [ex_reject_app_E] — the outer application of the promoted
       fixpoint to the identity continuation collapses ([der ∘ prom]
       cancels BEFORE any continuity argument).
    2. [ex_reject_sup_E] — [ν] is the [cone_sup_ball] of the
       per-iterate measures [ν_n] (evaluation at a point commutes with
       the Kleene supremum: linhom-cone sups are pointwise).
    3. [ex_reject_iter_S] — the Kleene step: [ν_{n+1}] is the inner
       let-if body evaluated at the extended setlike environment.
    4. [ex_reject_inner_at_dirac] — at the environment [γ ⊗ δ_r] the
       branch dispatch computes: THEN gives [(f r)·δ_r], ELSE gives
       [(1 - f r)·ν_n] (the recursive call at the same continuation).
    5. [ex_reject_iter_mass] — the mass recurrence
       [ν_{n+1}(U) = IUf U + (1 - If)·ν_n(U)] via the let-at-sample
       Pettis integral law.
    6. The theorems, via the affine-cascade closed form and the
       sup-mass bridge of [theories/programs/infra/affine_cascade.v].

    Supporting kit (generic, §1): [adj_psi_at_setlike] (the [U ⊣ !̃]
    packaging promotes at setlike points), [if_icones_at] (the
    if-then-else dispatch at setlike points), [linhom_fun_sup_ball]
    (pointwise reading of the linhom-cone supremum),
    [cone_sup_ball_irr] (the ball-sup does not depend on the chain
    witnesses).

    See also: [theories/programs/infra/em_fix_value.v] (the seeded
    value-fixpoint combinator), [theories/programs/infra/
    cbv_fix_unfold.v] (the recursion-unfolding laws),
    [theories/programs/infra/let_sample_law.v] (the let-at-sample
    integral law), [theories/programs/infra/affine_cascade.v] (the
    scalar cascade), [theories/programs/infra/cbv_anchors.v] (the
    setlike kit).

    Author: Guillaume Baudart <guillaume.baudart@inria.fr>. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp Require Import lra.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals constructive_ereal.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import ereal.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import measure dirac_measure numfun.
From mathcomp.analysis Require Import lebesgue_integral_definition.
From mathcomp.analysis Require Import lebesgue_integral_nonneg.
From mathcomp.analysis Require Import lebesgue_integral_monotone_convergence.
From mathcomp.analysis Require Import topology normedtype sequences.
Import numFieldTopology.Exports.

From Stdlib Require Import Strings.String.

Require Import Icones.cones.precone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.cone.
Require Import Icones.cones.cone_cat.
Require Import Icones.programs.infra.bool_cone.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.mcones.path.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_integral.
Require Import Icones.icones.examples_icone.
Require Import Icones.icones.icone_cat.
Require Import Icones.stable.scones_cat.
Require Import Icones.stable.scones_ccc.
Require Import Icones.homs.icones_iso.
Require Import Icones.homs.linhom.
Require Import Icones.homs.linhom_functor.
Require Import Icones.homs.bilin.
Require Import Icones.homs.tensor.
Require Import Icones.homs.tensor_construct.
Require Import Icones.homs.smcc.
Require Import Icones.homs.exp_adjunction.
Require Import Icones.homs.bang.
Require Import Icones.homs.seely_defs.
Require Import Icones.homs.seely.
Require Import Icones.homs.tensor_hom_iso.
Require Import Icones.programs.infra.bool_case_hom.
Require Import Icones.homs.coalgebra.
Require Import Icones.programs.infra.bool_cone_coalg.
Require Import Icones.homs.fmeas_lax.
Require Import Icones.homs.em_cat.
Require Import Icones.homs.em_seely_comonoid.
Require Import Icones.homs.em_cartesian.
Require Import Icones.programs.infra.cbv_adjunction.
Require Import Icones.programs.ppl.
Require Import Icones.programs.infra.em_fix.
Require Import Icones.programs.infra.em_fix_mr.
Require Import Icones.programs.infra.em_fix_value.
Require Import Icones.programs.ppl_cbv.
Require Import Icones.programs.infra.cbv_anchors.
Require Import Icones.programs.infra.cbv_fix_unfold.
Require Import Icones.programs.infra.let_sample_law.
Require Import Icones.programs.infra.affine_cascade.
Require Import Icones.programs.examples.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Opaque tensor_mor tensor_assoc tensor_lunit tensor_runit tensor_braid
       ptensor tau Seely2.
Local Opaque dig der prom bang_fmap d_bang e_bang unit_cofree_str Coalg
       tens_cofree_str m_bang.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** §1 — Generic kit: setlike computation laws and pointwise sups *)

Section HeadlineKit.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '!'" := (prom x) (at level 2, format "x '!'").

(** The [U ⊣ !̃] packaging [adj_psi g] PROMOTES at setlike unit-ball
    points: [adj_psi(g)(γ) = (g γ)!]. *)
Lemma adj_psi_at_setlike (P : Coalgebra Ar) (B : ICone.type Ar)
    (g : icones_hom Ar (coalg_obj P) B) (gam : coalg_obj P) :
  cone_norm gam <= 1 ->
  Lfun (coalg_str P) gam = gam! ->
  Lfun (ch_mor (adj_psi (P := P) g)) gam = (Lfun g gam)!.
Proof.
move=> Hg Hs.
rewrite (adj_psi_morE g) (Lfun_comp (bang_fmap g) (coalg_str P) gam) Hs.
exact: (bang_fmap_prom g _ Hg).
Qed.

(** The if-then-else dispatch computes at setlike unit-ball points:
    [⟦if b then m else n⟧(γ) = bool_case (b γ) (m γ) (n γ)] — the
    weighted co-pairing of the two branches by the scrutinee's
    sub-probability. *)
Lemma if_icones_at (G A : Coalgebra Ar)
    (m n : icones_hom Ar (coalg_obj G) (coalg_obj A))
    (b : icones_hom Ar (coalg_obj G) (coalg_obj (@bool_cone_coalg R Ar)))
    (gam : coalg_obj G) :
  cone_norm gam <= 1 ->
  Lfun (coalg_str G) gam = gam! ->
  Lfun (if_icones m n b) gam =
  bool_case (Lfun b gam) (Lfun m gam) (Lfun n gam).
Proof.
move=> Hg Hs.
rewrite /if_icones Lfun_comp.
rewrite /em_pair_mor (Lfun_comp
  (tensor_mor (icones_id Ar (coalg_obj G)) b) (coalg_d G) gam).
rewrite (coalg_d_setlike Hg Hs) tensor_morE icones_idE.
rewrite /if_under (Lfun_comp (tensor_uncurry _)
  (iso_fwd (tensor_braid (coalg_obj G) (bool_cone_car Ar)))
  (gam ⊗p Lfun b gam)).
rewrite tensor_braidEp tensor_uncurryE.
by rewrite linhom_iconesE bool_case_linhomE.
Qed.

(** The ball-sup of a chain does not depend on the chain/ball
    witnesses (it is THE least upper bound). *)
Lemma cone_sup_ball_irr (B : coneType R) (u : nat -> B)
    (c1 c2 : forall n, precone_le (u n) (u n.+1))
    (b1 b2 : forall n, cone_norm (u n) <= 1) :
  cone_sup_ball u c1 b1 = cone_sup_ball u c2 b2.
Proof.
apply: precone_le_anti.
- apply: cone_sup_ball_lub => n; exact: cone_sup_ball_ub.
- apply: cone_sup_ball_lub => n; exact: cone_sup_ball_ub.
Qed.

(** Linhom-cone suprema are POINTWISE: evaluating the ball-sup of a
    chain of linear maps at a unit-ball point is the ball-sup of the
    evaluations (for any witnesses of the evaluated chain). *)
Lemma linhom_fun_sup_ball (C D : ICone.type Ar)
    (u : nat -> linhom_car Ar C D)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, cone_norm (u n) <= 1)
    (x : C) (Hx : cone_norm x <= 1)
    (pwch : forall n,
        precone_le (linhom_fun (u n) x) (linhom_fun (u n.+1) x))
    (pwub : forall n, cone_norm (linhom_fun (u n) x) <= 1) :
  linhom_fun (cone_sup_ball u uch ub1) x =
  cone_sup_ball (fun n => linhom_fun (u n) x) pwch pwub.
Proof.
have -> : cone_sup_ball u uch ub1 = linhom_sup_ball u uch ub1 by [].
have -> : linhom_fun (linhom_sup_ball u uch ub1) x
          = linhom_sup_fun uch ub1 x by [].
rewrite (linhom_sup_fun_unitE uch ub1 Hx) (linhom_sup_unitE uch ub1 Hx).
exact: cone_sup_ball_irr.
Qed.

End HeadlineKit.

Arguments adj_psi_at_setlike {R Ar P B} g {gam}.
Arguments if_icones_at {R Ar G A} m n b {gam}.
Arguments cone_sup_ball_irr {R B u} c1 c2 b1 b2.
Arguments linhom_fun_sup_ball {R Ar C D u} uch ub1 {x} Hx pwch pwub.

(** *** The application clause at a setlike point (generic over the real
    object and its carrier casts; reused by every example rider —
    [probObj]-parameterised or not — for the THEN/ELSE branches in
    step 4).  Kept generic over a free [R_obj] so the [probObj]-based
    riders (where [R_obj := po_robj P]) AND the still-[R_obj]-based
    even/odd rider share the same lemma. *)
Section AppAtSetlike.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation "x '!'" := (prom x) (at level 2, format "x '!'").
Local Notation eD_cbv' :=
  (@eD_cbv R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation Lty t1 t2 :=
  (linhom_car Ar (coalg_obj (tyD_cbv t1)) (coalg_obj (tyD_cbv t2))).

Lemma eD_app_at_setlike (G : named_ctx Ar) (t1 t2 : ppl_type Ar)
    (F : @named_expr R Ar R_obj G (tfun t1 t2))
    (X : @named_expr R Ar R_obj G t1)
    (gam : coalg_obj (ctxD_cbv (drop_names G))) :
  cone_norm gam <= 1 ->
  Lfun (coalg_str (ctxD_cbv (drop_names G))) gam = gam! ->
  Lfun (eD_cbv' (ne_app F X)) gam =
  linhom_fun (Lfun (der (Lty t1 t2)) (Lfun (eD_cbv' F) gam))
             (Lfun (eD_cbv' X) gam).
Proof.
move=> Hg Hs.
rewrite eD_app_E.
rewrite (Lfun_comp (tensor_uncurry (icones_id Ar (Lty t1 t2)))
  (icones_comp
    (tensor_mor (der (Lty t1 t2)) (icones_id Ar (coalg_obj (tyD_cbv t1))))
    (em_pair_mor (eD_cbv' F) (eD_cbv' X))) gam).
rewrite (Lfun_comp
  (tensor_mor (der (Lty t1 t2)) (icones_id Ar (coalg_obj (tyD_cbv t1))))
  (em_pair_mor (eD_cbv' F) (eD_cbv' X)) gam).
rewrite /em_pair_mor (Lfun_comp (tensor_mor (eD_cbv' F) (eD_cbv' X))
  (coalg_d (ctxD_cbv (drop_names G))) gam).
rewrite (coalg_d_setlike Hg Hs) tensor_morE tensor_morE icones_idE.
by rewrite tensor_uncurryE icones_idE.
Qed.

End AppAtSetlike.

Arguments eD_app_at_setlike {R Ar R_obj} R_carrier_eq R_carrier_meas
  R_to_carrier_meas {G t1 t2 F X gam}.

(** ** §2 — The rejection-sampling reduction chain *)

Section RejectHeadline.
Variables (R : realType) (Ar : MeasSubcat R).
(* Reparameterized over the bundled [probObj]. *)
Variable (P : probObj Ar).
Local Notation R_obj := (po_robj P).
Local Notation R_carrier_eq := (po_robj_eq P).
Local Notation R_carrier_meas := (po_robj_meas P).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

(** The prior: a bundled sub-probability, assumed of unit mass. *)
Variable (m : pmeas Ar R_obj).
Local Notation mu := (pm_meas m).
Local Notation Hmu_ball := (pm_ball m).
Hypothesis Hmu1 : fmeas_mu mu [set: ar_carrier Ar R_obj] = 1%E.

(** The soft acceptance predicate: a BUNDLED [[0,1]]-valued density.
    The three projections are exposed under their historical names so
    the proof bodies below read unchanged. *)
Variable (d : udensity R).
Local Notation f := (ud_f d).
Local Notation Hf_meas := (ud_meas d).
Local Notation Hf_ge0 := (ud_ge0 d).
Local Notation Hf_le1 := (ud_le1 d).

(** The bundle factoring of [d] into the probability object, the
    clean [tProb]-coin map behind [Bern (ToProb d #"x")]. *)
Local Notation rj_phi := (po_into P f Hf_meas Hf_ge0 Hf_le1).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '!'" := (prom x) (at level 2, format "x '!'").
Local Notation eD_cbv' :=
  (@eD_cbv R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation eD' :=
  (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation cR := (carrier_to_R R_carrier_eq).
Local Notation tR' := (tR R_obj).
Local Notation Lty t1 t2 :=
  (linhom_car Ar (coalg_obj (tyD_cbv t1)) (coalg_obj (tyD_cbv t2))).

(** *** Syntactic decomposition of [ex_reject] — all definitional

    The [let rec] surface form elaborates to a [ne_let] binding the
    fixpoint under ["rs"], whose continuation applies the bound
    recursive sampler to the identity acceptance continuation. *)

(** The identity acceptance continuation [λ y. y], in the [let rec]
    continuation context. *)
Definition reject_lam_id :
    @named_expr R Ar R_obj
      (("rs"%string, tfun (tfun tR' tR') tR') :: nil) (tfun tR' tR') :=
  [ \ "y" ::: tR' => # "y" ].

(** The test-and-dispatch body under the sample binder. *)
Definition reject_if :
    @named_expr R Ar R_obj
      (("x"%string, tR') :: ("accept"%string, tfun tR' tR') ::
       ("rs"%string, tfun (tfun tR' tR') tR') :: nil) tR' :=
  [ if Bern (ToProb {rj_phi} # "x")
    then # "accept" @ # "x"
    else # "rs" @ # "accept" ].

Lemma ex_reject_decomp :
  ex_reject m d =
  ne_let "rs" (ne_fix "rs" (ex_reject_body m d))
    (ne_app (ne_var (nv_head "rs" (tfun (tfun tR' tR') tR') nil))
            reject_lam_id).
Proof. by []. Qed.

Lemma ex_reject_body_decomp :
  ex_reject_body m d =
  ne_lam "accept" (ex_reject_inner m d).
Proof. by []. Qed.

Lemma ex_reject_inner_decomp :
  ex_reject_inner m d =
  ne_let "x" (ne_sample mu Hmu_ball) reject_if.
Proof. by []. Qed.

(** The variable body of the identity continuation. *)
Definition reject_id_var :
    @named_expr R Ar R_obj
      (("y"%string, tR') ::
       ("rs"%string, tfun (tfun tR' tR') tR') :: nil) tR' :=
  [ # "y" ].

Lemma reject_lam_id_decomp : reject_lam_id = ne_lam "y" reject_id_var.
Proof. by []. Qed.

Let Hone : cone_norm (one1 : cone_one_car Ar) <= 1.
Proof. by rewrite one1_norm. Qed.

(** *** The semantic objects: the body's endo-function [W₀], the
    [let rec] environment, and the continuation value [a₀ = ℓ!] *)

(** [W₀ := curry ⟦body⟧ (one1) : !L₁ ⊸ !L₁] — the recursion body's
    endo-function at the closed environment ([L₁ := U⟦(R→R)→R⟧]). *)
Definition reject_W0 :
    linhom_car Ar (Bang Ar (Lty (tfun tR' tR') tR'))
                  (Bang Ar (Lty (tfun tR' tR') tR')) :=
  Lfun (tensor_curry
         (eD_cbv' (ex_reject_body m d)))
       one1.

Lemma reject_W0_ball : cone_norm reject_W0 <= 1.
Proof. exact: le_trans (cones_hom_norm_le1 _ _) Hone. Qed.

(** The promoted fixpoint value is a setlike unit-ball point. *)
Lemma reject_fix_prom_ball :
  cone_norm ((sc_fun (fix_value (Lty (tfun tR' tR') tR')) reject_W0)!) <= 1.
Proof. exact: prom_ball (fix_value_ball reject_W0 reject_W0_ball). Qed.

Lemma reject_fix_prom_setlike :
  Lfun (coalg_str (tyD_cbv (tfun (tfun tR' tR') tR')))
       ((sc_fun (fix_value (Lty (tfun tR' tR') tR')) reject_W0)!) =
  ((sc_fun (fix_value (Lty (tfun tR' tR') tR')) reject_W0)!)!.
Proof.
rewrite -[tyD_cbv (tfun (tfun tR' tR') tR')]
        /(bang_cofree (Lty (tfun tR' tR') tR')) bang_cofree_str.
exact: (dig_prom _ (fix_value_ball reject_W0 reject_W0_ball)).
Qed.

(** The [let rec] continuation environment: ["rs"] bound to the
    promoted fixpoint value. *)
Definition reject_env0 :
    coalg_obj (ctxD_cbv (drop_names
      (("rs"%string, tfun (tfun tR' tR') tR') :: nil))) :=
  one1 ⊗p (sc_fun (fix_value (Lty (tfun tR' tR') tR')) reject_W0)!.

Lemma reject_env0_ball : cone_norm reject_env0 <= 1.
Proof.
by rewrite /reject_env0 tensor_normME one1_norm mul1r reject_fix_prom_ball.
Qed.

Lemma reject_env0_setlike :
  Lfun (coalg_str (ctxD_cbv (drop_names
         (("rs"%string, tfun (tfun tR' tR') tR') :: nil))))
       reject_env0 = reject_env0!.
Proof.
exact: (coalg_str_tensor_setlike (P:=EM_term)
          (Q:=tyD_cbv (tfun (tfun tR' tR') tR'))
          Hone reject_fix_prom_ball coalg_str_one1
          reject_fix_prom_setlike).
Qed.

(** [ℓ] — the function value of the identity continuation: the linear
    map [⟦λy.y⟧] is closed over the [let rec] environment. *)
Definition reject_acc : Lty tR' tR' :=
  Lfun (tensor_curry (eD_cbv' reject_id_var)) reject_env0.

(** [a₀ := ℓ!] — the PROMOTED identity continuation, the function
    value the fixpoint is applied to. *)
Definition reject_arg : coalg_obj (tyD_cbv (tfun tR' tR')) := reject_acc!.

Lemma reject_acc_ball : cone_norm reject_acc <= 1.
Proof. exact: le_trans (cones_hom_norm_le1 _ _) reject_env0_ball. Qed.

(** [ℓ] IS the identity function on measures. *)
Lemma reject_acc_E (x : coalg_obj (tyD_cbv tR')) :
  linhom_fun reject_acc x = x.
Proof.
rewrite /reject_acc tensor_curryE.
apply: (eq_trans (y := Lfun (em_proj2_mor (R:=R)
  (ctxD_cbv (drop_names (("rs"%string, tfun (tfun tR' tR') tR') :: nil)))
  (FMeas_coalgebra R_obj)) (reject_env0 ⊗p x))).
  by [].
exact: (em_proj2_morE reject_env0_ball reject_env0_setlike).
Qed.

Lemma reject_arg_ball : cone_norm reject_arg <= 1.
Proof. exact: prom_ball reject_acc_ball. Qed.

(** [a₀] is a setlike point of the cofree function-type coalgebra. *)
Lemma reject_arg_setlike :
  Lfun (coalg_str (tyD_cbv (tfun tR' tR'))) reject_arg = reject_arg!.
Proof.
rewrite -[tyD_cbv (tfun tR' tR')]/(bang_cofree (Lty tR' tR'))
        bang_cofree_str /reject_arg.
exact: (dig_prom _ reject_acc_ball).
Qed.

Lemma reject_arg_E :
  Lfun (eD_cbv' reject_lam_id) reject_env0 = reject_arg.
Proof.
rewrite reject_lam_id_decomp eD_lam_E.
by rewrite (adj_psi_at_setlike (tensor_curry (eD_cbv' reject_id_var))
              reject_env0_ball reject_env0_setlike).
Qed.

(** *** Step 1 — the [let rec] binding collapses: the let pairs the
    promoted fixpoint value onto the environment, the head-variable
    lookup recovers it, and [der ∘ prom] cancels BEFORE any continuity
    argument, leaving the fixpoint VALUE applied to the (promoted)
    identity continuation. *)

Local Notation reject_denot :=
  (linhom_fun (ex_reject_cbv P R_to_carrier_meas m d) one1).

Lemma ex_reject_app_E :
  reject_denot =
  linhom_fun (sc_fun (fix_value (Lty (tfun tR' tR') tR')) reject_W0)
             reject_arg.
Proof.
rewrite /ex_reject_cbv /eD icones_to_linhomE ex_reject_decomp.
have HoneG : cone_norm
    (one1 : coalg_obj (ctxD_cbv (drop_names (nil : named_ctx Ar)))) <= 1.
  by rewrite one1_norm.
rewrite (eD_let_at_setlike "rs"
          (ne_fix "rs" (ex_reject_body m d))
          (ne_app (ne_var (nv_head "rs" (tfun (tfun tR' tR') tR') nil))
                  reject_lam_id)
          HoneG coalg_str_one1).
rewrite (eD_fix_at_setlike "rs"
          (ex_reject_body m d)
          HoneG coalg_str_one1).
rewrite (eD_app_at_setlike R_carrier_eq R_carrier_meas R_to_carrier_meas reject_env0_ball reject_env0_setlike).
rewrite (eD_var_head_at_setlike "rs"
          (t := tfun (tfun tR' tR') tR')
          ((sc_fun (fix_value (Lty (tfun tR' tR') tR')) reject_W0)!)
          HoneG coalg_str_one1).
rewrite reject_arg_E.
by rewrite (der_prom _ (fix_value_ball reject_W0 reject_W0_ball)).
Qed.

(** *** Step 2 — the denotation is the sup of the per-iterate measures

    [ν_n := (fix_chain W₀ n)(a₀)] — the n-th Kleene iterate of the
    recursion body, applied to the identity continuation. *)

Definition reject_iter (n : nat) : coalg_obj (tyD_cbv tR') :=
  linhom_fun (fix_chain reject_W0 n) reject_arg.

Lemma reject_iter_chain n : precone_le (reject_iter n) (reject_iter n.+1).
Proof.
exact: (linhom_le_pointwise (fix_chain_chain reject_W0_ball n) reject_arg).
Qed.

Lemma reject_iter_ball n : cone_norm (reject_iter n) <= 1.
Proof.
apply: le_trans
  (linhom_norm_apply_le (fix_chain_ball reject_W0_ball n) reject_arg) _.
by rewrite mul1r reject_arg_ball.
Qed.

(** Evaluation at [a₀] commutes with the Kleene supremum because
    linhom-cone sups are pointwise ([linhom_fun_sup_ball]). *)
Lemma ex_reject_sup_E :
  reject_denot =
  cone_sup_ball reject_iter reject_iter_chain reject_iter_ball.
Proof.
rewrite ex_reject_app_E (fix_value_E reject_W0_ball).
rewrite (linhom_fun_sup_ball (fix_chain_chain reject_W0_ball)
  (fix_chain_ball reject_W0_ball) reject_arg_ball
  reject_iter_chain reject_iter_ball).
by [].
Qed.

(** *** Step 3 — the Kleene step is the inner body at the extended
    setlike environment *)

Lemma fix_chain_prom_ball n :
  cone_norm ((fix_chain reject_W0 n)!) <= 1.
Proof. exact: prom_ball (fix_chain_ball reject_W0_ball n). Qed.

Lemma fix_chain_prom_setlike n :
  Lfun (coalg_str (tyD_cbv (tfun (tfun tR' tR') tR')))
       ((fix_chain reject_W0 n)!) = ((fix_chain reject_W0 n)!)!.
Proof.
rewrite -[tyD_cbv (tfun (tfun tR' tR') tR')]
        /(bang_cofree (Lty (tfun tR' tR') tR')) bang_cofree_str.
exact: (dig_prom _ (fix_chain_ball reject_W0_ball n)).
Qed.

(** The one-variable environment binding ["rs"] to the n-th promoted
    iterate is a setlike unit-ball point. *)
Lemma reject_env_ball n :
  cone_norm (one1 ⊗p (fix_chain reject_W0 n)!) <= 1.
Proof.
by rewrite tensor_normME one1_norm mul1r fix_chain_prom_ball.
Qed.

Lemma reject_env_setlike n :
  Lfun (coalg_str (ctxD_cbv (drop_names
         (("rs"%string, tfun (tfun tR' tR') tR') :: nil))))
       (one1 ⊗p (fix_chain reject_W0 n)!) =
  (one1 ⊗p (fix_chain reject_W0 n)!)!.
Proof.
exact: (coalg_str_tensor_setlike (P:=EM_term)
          (Q:=tyD_cbv (tfun (tfun tR' tR') tR'))
          Hone (fix_chain_prom_ball n) coalg_str_one1
          (fix_chain_prom_setlike n)).
Qed.

(** The recursion body at the promoted iterate: the [λaccept]-packaging
    PROMOTES the curried inner body at the extended environment. *)
Lemma reject_W0_at_prom n :
  linhom_fun reject_W0 ((fix_chain reject_W0 n)!) =
  (Lfun (tensor_curry
          (eD_cbv' (ex_reject_inner m d)))
     (one1 ⊗p (fix_chain reject_W0 n)!))!.
Proof.
rewrite {1}/reject_W0 tensor_curryE ex_reject_body_decomp eD_lam_E.
exact: (adj_psi_at_setlike
  (P:=ctxD_cbv (drop_names (("rs"%string, tfun (tfun tR' tR') tR') :: nil)))
  _ (reject_env_ball n) (reject_env_setlike n)).
Qed.

Lemma ex_reject_iter_S n :
  reject_iter n.+1 =
  Lfun (eD_cbv' (ex_reject_inner m d))
       ((one1 ⊗p (fix_chain reject_W0 n)!) ⊗p reject_arg).
Proof.
rewrite /reject_iter fix_chain_S reject_W0_at_prom.
rewrite (der_prom _ (le_trans (cones_hom_norm_le1 _ _)
                              (reject_env_ball n))).
exact: tensor_curryE.
Qed.

(** *** Step 4 — the inner if-body at the Dirac environment

    At the environment [γ_n ⊗ a₀ ⊗ δ_r] the branch dispatch computes:
    the scrutinee is [Bernoulli (f r)], the THEN branch returns the
    accepted sample [δ_r] (the identity continuation applied to the
    bound variable), the ELSE branch is the RECURSIVE CALL at the same
    continuation — which is exactly the previous iterate [ν_n]. *)

(** The three variables of [reject_if], as standalone terms. *)
Definition reject_var_x :
    @named_expr R Ar R_obj
      (("x"%string, tR') :: ("accept"%string, tfun tR' tR') ::
       ("rs"%string, tfun (tfun tR' tR') tR') :: nil) tR' :=
  [ # "x" ].

Definition reject_var_acc :
    @named_expr R Ar R_obj
      (("x"%string, tR') :: ("accept"%string, tfun tR' tR') ::
       ("rs"%string, tfun (tfun tR' tR') tR') :: nil) (tfun tR' tR') :=
  [ # "accept" ].

Definition reject_var_rs :
    @named_expr R Ar R_obj
      (("x"%string, tR') :: ("accept"%string, tfun tR' tR') ::
       ("rs"%string, tfun (tfun tR' tR') tR') :: nil)
      (tfun (tfun tR' tR') tR') :=
  [ # "rs" ].

(** The clean coin's underlying [tProb] argument: the acceptance
    density [d] pushed through the bundle factoring [po_into] at the
    sampled variable. *)
Local Notation reject_coin_arg := (ne_to_prob rj_phi reject_var_x).

Lemma reject_if_decomp :
  reject_if =
  ne_if tR' (ne_bernoulli_p (po_density P) (po_density_meas P)
               (po_ge0 P) (po_le1 P) reject_coin_arg)
        (ne_app reject_var_acc reject_var_x)
        (ne_app reject_var_rs reject_var_acc).
Proof. by []. Qed.

(** The inner-let context point [γ_n ⊗ a₀] and its Dirac extension. *)
Definition reject_env2 (n : nat) :
    coalg_obj (ctxD_cbv (drop_names
      (("accept"%string, tfun tR' tR') ::
       ("rs"%string, tfun (tfun tR' tR') tR') :: nil))) :=
  (one1 ⊗p (fix_chain reject_W0 n)!) ⊗p reject_arg.

Definition reject_env3 (n : nat) (r : ar_carrier Ar R_obj) :
    coalg_obj (ctxD_cbv (drop_names
      (("x"%string, tR') :: ("accept"%string, tfun tR' tR') ::
       ("rs"%string, tfun (tfun tR' tR') tR') :: nil))) :=
  reject_env2 n ⊗p dirac_fmeas r.

Lemma reject_env2_ball n : cone_norm (reject_env2 n) <= 1.
Proof.
rewrite /reject_env2 tensor_normME.
by rewrite mulr_ile1 ?cone_norm_ge0 ?reject_env_ball ?reject_arg_ball.
Qed.

Lemma reject_env2_setlike n :
  Lfun (coalg_str (ctxD_cbv (drop_names
         (("accept"%string, tfun tR' tR') ::
          ("rs"%string, tfun (tfun tR' tR') tR') :: nil))))
       (reject_env2 n) = (reject_env2 n)!.
Proof.
exact: (coalg_str_tensor_setlike
          (P:=ctxD_cbv (drop_names
                (("rs"%string, tfun (tfun tR' tR') tR') :: nil)))
          (Q:=tyD_cbv (tfun tR' tR'))
          (reject_env_ball n) reject_arg_ball
          (reject_env_setlike n) reject_arg_setlike).
Qed.

Lemma reject_env3_ball n r : cone_norm (reject_env3 n r) <= 1.
Proof.
rewrite /reject_env3 tensor_normME.
by rewrite mulr_ile1 ?cone_norm_ge0 ?reject_env2_ball ?dirac_fmeas_norm_le1.
Qed.

Lemma reject_env3_setlike n r :
  Lfun (coalg_str (ctxD_cbv (drop_names
         (("x"%string, tR') :: ("accept"%string, tfun tR' tR') ::
          ("rs"%string, tfun (tfun tR' tR') tR') :: nil))))
       (reject_env3 n r) = (reject_env3 n r)!.
Proof.
exact: (coalg_str_tensor_setlike
          (P:=ctxD_cbv (drop_names
                (("accept"%string, tfun tR' tR') ::
                 ("rs"%string, tfun (tfun tR' tR') tR') :: nil)))
          (Q:=FMeas_coalgebra R_obj)
          (reject_env2_ball n) (dirac_fmeas_norm_le1 r)
          (reject_env2_setlike n) (Coalg_dirac R_obj r)).
Qed.

(** The variable projections at the Dirac environment. *)
Lemma reject_var_x_E n r :
  Lfun (eD_cbv' reject_var_x) (reject_env3 n r) = dirac_fmeas r.
Proof.
apply: (eq_trans (y := Lfun (em_proj2_mor (R:=R)
  (ctxD_cbv (drop_names
     (("accept"%string, tfun tR' tR') ::
      ("rs"%string, tfun (tfun tR' tR') tR') :: nil)))
  (FMeas_coalgebra R_obj)) (reject_env3 n r))).
  by [].
exact: (em_proj2_morE (reject_env2_ball n) (reject_env2_setlike n)).
Qed.

Lemma reject_var_acc_E n r :
  Lfun (eD_cbv' reject_var_acc) (reject_env3 n r) = reject_arg.
Proof.
apply: (eq_trans (y := Lfun (icones_comp
  (em_proj2_mor (R:=R)
     (ctxD_cbv (drop_names
        (("rs"%string, tfun (tfun tR' tR') tR') :: nil)))
     (tyD_cbv (tfun tR' tR')))
  (em_proj1_mor (R:=R)
     (ctxD_cbv (drop_names
        (("accept"%string, tfun tR' tR') ::
         ("rs"%string, tfun (tfun tR' tR') tR') :: nil)))
     (FMeas_coalgebra R_obj))) (reject_env3 n r))).
  by [].
rewrite Lfun_comp.
rewrite (em_proj1_morE (Q:=FMeas_coalgebra R_obj)
           (dirac_fmeas_norm_le1 r) (Coalg_dirac R_obj r)).
exact: (em_proj2_morE (P:=ctxD_cbv (drop_names
          (("rs"%string, tfun (tfun tR' tR') tR') :: nil)))
          (reject_env_ball n) (reject_env_setlike n)).
Qed.

Lemma reject_var_rs_E n r :
  Lfun (eD_cbv' reject_var_rs) (reject_env3 n r) =
  (fix_chain reject_W0 n)!.
Proof.
apply: (eq_trans (y := Lfun (icones_comp
  (icones_comp
    (em_proj2_mor (R:=R) EM_term (tyD_cbv (tfun (tfun tR' tR') tR')))
    (em_proj1_mor (R:=R)
       (ctxD_cbv (drop_names
          (("rs"%string, tfun (tfun tR' tR') tR') :: nil)))
       (tyD_cbv (tfun tR' tR'))))
  (em_proj1_mor (R:=R)
     (ctxD_cbv (drop_names
        (("accept"%string, tfun tR' tR') ::
         ("rs"%string, tfun (tfun tR' tR') tR') :: nil)))
     (FMeas_coalgebra R_obj))) (reject_env3 n r))).
  by [].
rewrite Lfun_comp Lfun_comp.
rewrite (em_proj1_morE (Q:=FMeas_coalgebra R_obj)
           (dirac_fmeas_norm_le1 r) (Coalg_dirac R_obj r)).
rewrite (em_proj1_morE (Q:=tyD_cbv (tfun tR' tR'))
           reject_arg_ball reject_arg_setlike).
exact: (em_proj2_morE (P:=EM_term) Hone coalg_str_one1).
Qed.

(** The scrutinee at [δ_r] is the [f r]-coin (the bundled
    [ne_bernoulli_f] node desugared directly — no clamp transport —
    then [bern_lift_dirac]). *)
Lemma reject_scrut_E n r :
  Lfun (eD_cbv' (ne_bernoulli_p (po_density P) (po_density_meas P)
                   (po_ge0 P) (po_le1 P) reject_coin_arg))
       (reject_env3 n r) =
  bernoulli (f (cR r)) (Hf_ge0 (cR r)) (Hf_le1 (cR r)).
Proof.
(* Clean-surface coin leaf: push the sampled real through the bundle
   factoring [po_into f] and read off the [f r]-coin with
   [bern_lift_P]; [po_into_E] recovers [f r]. *)
rewrite eD_bernoulli_p_E Lfun_comp.
rewrite -[bern_lift_g _ _ _]/(bern_lift_P P).
rewrite eD_to_prob_E Lfun_comp.
rewrite reject_var_x_E FMeas_fmap_dirac bern_lift_P_dirac.
apply: bool_cone_eq; apply: val_inj => /=; by rewrite /po_density po_into_E.
Qed.

(** THEN: the identity continuation applied to the bound sample. *)
Lemma reject_then_E n r :
  Lfun (eD_cbv' (ne_app reject_var_acc reject_var_x)) (reject_env3 n r) =
  dirac_fmeas r.
Proof.
rewrite (eD_app_at_setlike R_carrier_eq R_carrier_meas R_to_carrier_meas (reject_env3_ball n r)
           (reject_env3_setlike n r)).
rewrite reject_var_acc_E reject_var_x_E.
rewrite (der_prom _ reject_acc_ball).
exact: reject_acc_E.
Qed.

(** ELSE: the recursive call at the same continuation IS the previous
    iterate. *)
Lemma reject_else_E n r :
  Lfun (eD_cbv' (ne_app reject_var_rs reject_var_acc)) (reject_env3 n r) =
  reject_iter n.
Proof.
rewrite (eD_app_at_setlike R_carrier_eq R_carrier_meas R_to_carrier_meas (reject_env3_ball n r)
           (reject_env3_setlike n r)).
rewrite reject_var_rs_E reject_var_acc_E.
by rewrite (der_prom _ (fix_chain_ball reject_W0_ball n)).
Qed.

Lemma ex_reject_inner_at_dirac n r :
  Lfun (eD_cbv' reject_if) (reject_env3 n r) =
  bool_case (bernoulli (Ar:=Ar) (f (cR r)) (Hf_ge0 (cR r)) (Hf_le1 (cR r)))
            (dirac_fmeas r) (reject_iter n).
Proof.
rewrite reject_if_decomp eD_if_E.
rewrite (if_icones_at
  (eD_cbv' (ne_app reject_var_acc reject_var_x))
  (eD_cbv' (ne_app reject_var_rs reject_var_acc))
  (eD_cbv' (ne_bernoulli_p (po_density P) (po_density_meas P)
              (po_ge0 P) (po_le1 P) reject_coin_arg))
  (reject_env3_ball n r) (reject_env3_setlike n r)).
by rewrite reject_scrut_E reject_then_E reject_else_E.
Qed.

(** *** Step 5 — the mass recurrence

    [ν_{n+1}(U) = ∫_U f dµ + (1 - ∫ f dµ) · ν_n(U)] via the
    let-at-sample Pettis integral law, with the acceptance and
    rejection weights accounted by [∫(1-f) dµ = 1 - ∫f dµ] (the prior
    has unit mass). *)

Local Open Scope ereal_scope.

(** [If] / [IUf U] abbreviate the acceptance-mass integrals in the
    PROOFS only ([only parsing]); the headline STATEMENTS below spell the
    integrals out explicitly so the reader sees the real measure
    [fmeas_mu mu] and integrand [(f (cR ·))%:E]. *)
Local Notation If :=
  (\int[fmeas_mu mu]_(r in [set: ar_carrier Ar R_obj]) (f (cR r))%:E)
  (only parsing).
Local Notation IUf U :=
  (\int[fmeas_mu mu]_(r in U) (f (cR r))%:E) (only parsing).

Let f_cR_meas : measurable_fun [set: ar_carrier Ar R_obj]
    (fun r => f (cR r)).
Proof. exact: (bern_f_cR_meas R_carrier_meas Hf_meas). Qed.

Lemma reject_If_ge0 : 0 <= If.
Proof. by apply: integral_ge0 => r _; rewrite lee_fin Hf_ge0. Qed.

Lemma reject_If_le1 : If <= 1.
Proof.
apply: (le_trans (y := \int[fmeas_mu mu]_(r in [set: ar_carrier Ar R_obj])
                        (cst 1%:E) r)).
  apply: ge0_le_integral => //.
  - by move=> r _; rewrite lee_fin Hf_ge0.
  - by apply/measurable_EFinP; exact: f_cR_meas.
  - by move=> r _; rewrite lee_fin Hf_le1.
by rewrite integral_cst// mul1e Hmu1.
Qed.

Lemma reject_If_fin : If \is a fin_num.
Proof.
rewrite ge0_fin_numE ?reject_If_ge0//.
by apply: le_lt_trans reject_If_le1 _; rewrite ltey.
Qed.

Lemma reject_IUf_ge0 U : measurable U -> 0 <= IUf U.
Proof. by move=> mU; apply: integral_ge0 => r _; rewrite lee_fin Hf_ge0. Qed.

Lemma reject_IUf_le_If U : measurable U -> IUf U <= If.
Proof.
move=> mU; apply: ge0_subset_integral => //.
- by apply/measurable_EFinP; exact: f_cR_meas.
- by move=> r _; rewrite lee_fin Hf_ge0.
Qed.

Lemma reject_IUf_fin U : measurable U -> IUf U \is a fin_num.
Proof.
move=> mU; rewrite ge0_fin_numE ?reject_IUf_ge0//.
apply: le_lt_trans (reject_IUf_le_If mU) _.
by apply: le_lt_trans reject_If_le1 _; rewrite ltey.
Qed.

(** The rejection weight: [∫ (1 - f) dµ = 1 - ∫ f dµ] at [µ(setT)=1]. *)
Lemma reject_int_onem :
  \int[fmeas_mu mu]_(r in [set: ar_carrier Ar R_obj])
     ((1 - f (cR r))%R)%:E = ((1 - fine If)%R)%:E.
Proof.
have Honem_meas : measurable_fun [set: ar_carrier Ar R_obj]
    (fun r => ((1 - f (cR r))%R)%:E).
  apply/measurable_EFinP.
  by apply: measurable_funB => //; exact: f_cR_meas.
have Hsum : If + \int[fmeas_mu mu]_(r in [set: ar_carrier Ar R_obj])
                   ((1 - f (cR r))%R)%:E = 1.
  rewrite -ge0_integralD//; first last.
  - by move=> r _; rewrite lee_fin subr_ge0 Hf_le1.
  - by apply/measurable_EFinP; exact: f_cR_meas.
  - by move=> r _; rewrite lee_fin Hf_ge0.
  under eq_integral => r _.
    rewrite -EFinD addrCA subrr addr0.
    over.
  by rewrite integral_cst// mul1e Hmu1.
have := congr1 (fun z => z - If) Hsum.
rewrite addeC addeK ?reject_If_fin// => ->.
by rewrite -{1}(fineK reject_If_fin) -EFinB.
Qed.

(** The mass of one branch dispatch. *)
Lemma reject_case_mass n r U (mU : measurable U) :
  fmeas_mu (bool_case
    (bernoulli (Ar:=Ar) (f (cR r)) (Hf_ge0 (cR r)) (Hf_le1 (cR r)))
    (dirac_fmeas r) (reject_iter n)) U =
  ((f (cR r) * \1_U r + (1 - f (cR r)) *
      fine (fmeas_mu (reject_iter n) U))%R)%:E.
Proof.
have -> : (bool_case
    (bernoulli (Ar:=Ar) (f (cR r)) (Hf_ge0 (cR r)) (Hf_le1 (cR r)))
    (dirac_fmeas r) (reject_iter n) : fmeas R (ar_carrier Ar R_obj)) =
  fmeas_add
    (fmeas_scale (NngNum (Hf_ge0 (cR r))) (dirac_fmeas r))
    (fmeas_scale (NngNum (subr_ge0_le1 (f (cR r)) (Hf_le1 (cR r))))
       (reject_iter n)).
  by [].
rewrite fmeas_addE 2!fmeas_scaleE (dirac_fmeas_E r mU) diracE/=.
rewrite -(fineK (fmeas_fin (reject_iter n) U mU)).
by rewrite -2!EFinM -EFinD indicE.
Qed.

Lemma ex_reject_iter_mass n U (mU : measurable U) :
  fmeas_mu (reject_iter n.+1) U =
  IUf U + ((1 - fine If)%R)%:E * fmeas_mu (reject_iter n) U.
Proof.
have Hiter : reject_iter n.+1 =
    linhom_fun (eD' (ne_let "x"%string (ne_sample mu Hmu_ball) reject_if))
               (reject_env2 n).
  rewrite ex_reject_iter_S ex_reject_inner_decomp.
  by rewrite /eD icones_to_linhomE.
rewrite Hiter.
rewrite (eD_let_sample_mu_E R_carrier_meas R_to_carrier_meas Hmu_ball
           reject_if (reject_env2 n) mU).
set c := fine (fmeas_mu (reject_iter n) U).
under eq_integral => r _.
  rewrite ex_reject_inner_at_dirac (reject_case_mass n r mU)/= EFinD.
  over.
have Hc0 : (0 <= c)%R by rewrite /c fine_ge0// measure_ge0.
have m1 : measurable_fun [set: ar_carrier Ar R_obj]
    (fun r => ((f (cR r) * \1_U r)%R)%:E).
  apply/measurable_EFinP; apply: measurable_funM => //.
have m2 : measurable_fun [set: ar_carrier Ar R_obj]
    (fun r => (((1 - f (cR r)) * fine (fmeas_mu (reject_iter n) U))%R)%:E).
  apply/measurable_EFinP; apply: measurable_funM => //.
  by apply: measurable_funB => //; exact: f_cR_meas.
rewrite ge0_integralD//; first last.
- by move=> r _; rewrite lee_fin mulr_ge0// ?subr_ge0 ?Hf_le1.
- by move=> r _; rewrite lee_fin mulr_ge0// Hf_ge0.
congr (_ + _).
- rewrite [RHS](integral_mkcond U) epatch_indic.
  apply: eq_integral => r _.
  by rewrite /= EFinM.
- under eq_integral => r _.
    rewrite EFinM.
    over.
  rewrite ge0_integralZr//; first last.
  - by move=> x _; rewrite lee_fin subr_ge0 Hf_le1.
  - by apply/measurable_EFinP; apply: measurable_funB => //;
       exact: f_cR_meas.
  rewrite reject_int_onem.
  by rewrite (fineK (fmeas_fin (reject_iter n) U mU)).
Qed.

(** *** Step 6 — the headline theorems *)

Lemma reject_iter_0 : reject_iter 0 = precone_zero.
Proof. by rewrite /reject_iter fix_chain_0 linhom_fun_zero. Qed.

Lemma reject_iter_0_mass U : fmeas_mu (reject_iter 0) U = 0.
Proof.
have -> : (reject_iter 0 : fmeas R (ar_carrier Ar R_obj)) = fmeas_zero.
  by rewrite reject_iter_0.
exact: fmeas_zeroE.
Qed.

(** Main result: when acceptance has positive mass, rejection
    sampling denotes the NORMALISED POSTERIOR
    [ν(U) = (∫_U f dµ) / (∫ f dµ)]. *)
Theorem ex_reject_is_normalised_posterior :
  0 < \int[fmeas_mu mu]_(x in [set: ar_carrier Ar R_obj]) ((f (cR x))%:E) ->
  forall U, measurable U ->
  fmeas_mu reject_denot U =
  ((fine (\int[fmeas_mu mu]_(x in U) ((f (cR x))%:E))
    / fine (\int[fmeas_mu mu]_(x in [set: ar_carrier Ar R_obj])
              ((f (cR x))%:E)))%R)%:E.
Proof.
move=> HIf U mU.
rewrite ex_reject_sup_E.
pose x := fun n => fine (fmeas_mu (reject_iter n) U).
have Hx0 : x 0%N = 0%R by rewrite /x reject_iter_0_mass.
have HxS : forall n,
    x n.+1 = (fine (IUf U) + (1 - fine If) * x n)%R.
  move=> n; rewrite /x (ex_reject_iter_mass n mU).
  rewrite fineD ?reject_IUf_fin//; last first.
    by rewrite fin_numM// (fmeas_fin (reject_iter n) U mU).
  by rewrite fineM// (fmeas_fin (reject_iter n) U mU).
have Hq0 : (0 <= 1 - fine If)%R.
  by rewrite subr_ge0 -lee_fin (fineK reject_If_fin) reject_If_le1.
have Hq1 : (1 - fine If < 1)%R.
  rewrite ltrBlDr ltrDl.
  by rewrite fine_gt0// HIf/= (le_lt_trans reject_If_le1)// ltey.
have Hcvg := affine_iter_cvg (fine (IUf U)) (1 - fine If) Hq0 Hx0 HxS Hq1.
apply: (fmeas_kleene_sup_U_E reject_iter_chain reject_iter_ball mU).
have HE : (fun n => fmeas_mu (reject_iter n) U) = (fun n => (x n)%:E).
  by apply/funext => n; rewrite /x fineK// (fmeas_fin (reject_iter n) U mU).
rewrite HE.
by rewrite -[in X in _ --> X](subKr 1 (fine If)).
Qed.

(** The division-free master form — unconditional, graceful at
    [∫ f dµ = 0]. *)
Theorem ex_reject_master U : measurable U ->
  \int[fmeas_mu mu]_(x in [set: ar_carrier Ar R_obj]) ((f (cR x))%:E)
    * fmeas_mu reject_denot U
  = \int[fmeas_mu mu]_(x in U) ((f (cR x))%:E).
Proof.
move=> mU.
have := reject_If_ge0; rewrite le_eqVlt => /orP[/eqP HIf0 | HIfpos].
- rewrite -HIf0 mul0e.
  apply/esym/eqP; rewrite eq_le reject_IUf_ge0// andbT.
  by rewrite (le_trans (reject_IUf_le_If mU))// -HIf0.
- rewrite (ex_reject_is_normalised_posterior HIfpos mU).
  have HfI_neq0 : fine If != 0%R.
    by rewrite gt_eqF// fine_gt0// HIfpos/=
       (le_lt_trans reject_If_le1)// ltey.
  rewrite -{1}(fineK reject_If_fin) -EFinM.
  by rewrite mulrC mulfVK// (fineK (reject_IUf_fin mU)).
Qed.

(** When the acceptance density already integrates to [1], the
    denotation is the un-normalised reweighted prior itself. *)
Theorem ex_reject_posterior_simple :
  \int[fmeas_mu mu]_(x in [set: ar_carrier Ar R_obj]) ((f (cR x))%:E) = 1 ->
  forall U, measurable U ->
  fmeas_mu reject_denot U = \int[fmeas_mu mu]_(x in U) ((f (cR x))%:E).
Proof.
move=> HIf1 U mU.
by rewrite -(ex_reject_master mU) HIf1 mul1e.
Qed.

(** Almost-sure termination: positive acceptance mass gives a
    PROBABILITY distribution. *)
Theorem ex_reject_mass_one :
  0 < \int[fmeas_mu mu]_(x in [set: ar_carrier Ar R_obj]) ((f (cR x))%:E) ->
  fmeas_mu reject_denot [set: ar_carrier Ar R_obj] = 1.
Proof.
move=> HIf.
rewrite (ex_reject_is_normalised_posterior HIf measurableT).
rewrite divff// ?gt_eqF// fine_gt0// HIf/=.
by rewrite (le_lt_trans reject_If_le1)// ltey.
Qed.

(** Certain rejection diverges: at [f ≡ 0] the denotation is the zero
    measure. *)
Theorem ex_reject_zero :
  (forall r : R, f r = 0%R) -> reject_denot = precone_zero.
Proof.
move=> Hf0.
have HIUf0 : forall U : set (ar_carrier Ar R_obj), IUf U = 0.
  move=> U.
  under eq_integral => r _ do rewrite Hf0.
  exact: integral0.
have Hmass : forall n (U : set (ar_carrier Ar R_obj)),
    measurable U -> fmeas_mu (reject_iter n) U = 0.
  elim=> [ | n IH] U mU; first exact: reject_iter_0_mass.
  by rewrite (ex_reject_iter_mass n mU) IH// mule0 adde0 HIUf0.
apply: fmeas_eq => U mU.
rewrite ex_reject_sup_E.
rewrite (fmeas_kleene_sup_U_E reject_iter_chain reject_iter_ball mU
          (l := 0)).
  by rewrite -[precone_zero]/(fmeas_zero : fmeas R (ar_carrier Ar R_obj))
       fmeas_zeroE.
have HE : (fun n => fmeas_mu (reject_iter n) U) = (fun n => (0 : \bar R)).
  by apply/funext => n; rewrite Hmass.
rewrite HE.
exact: cvg_cst.
Qed.

End RejectHeadline.

(** ** §3 — Rider: [ex_almost_loop] — parameterised partial divergence

    The same reduction-chain skeleton on the simpler program
    [[
       (let rec l = λ_. if Bernoulli(p) then () else l ()) ()
    ]]
    (no [sample] inside the iterate): the denotation at [tunit] is a
    scalar (a point of the unit cone), whose mass is the termination
    probability.  Dichotomy: [0 < p] gives mass [1] (almost-sure
    termination), [p = 0] gives the zero point (certain divergence). *)

Section AlmostLoopRider.
Variables (R : realType) (Ar : MeasSubcat R).
(* Reparameterized over the bundled [probObj]: the real object and its
   carrier casts come from [P], the clean [tProb] surface's bundle. *)
Variable (P : probObj Ar).
Local Notation R_obj := (po_robj P).
Local Notation R_carrier_eq := (po_robj_eq P).
Local Notation R_carrier_meas := (po_robj_meas P).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

(** The divergence parameter as a BUNDLED probability; its scalar and
    bounds are exposed under their historical names. *)
Variable (pr : prob R).
Local Notation p := (pr_val pr).
Local Notation Hp0 := (pr_ge0 pr).
Local Notation Hp1 := (pr_le1 pr).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '!'" := (prom x) (at level 2, format "x '!'").
Local Notation eD_cbv' :=
  (@eD_cbv R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation eD' :=
  (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation Lty t1 t2 :=
  (linhom_car Ar (coalg_obj (tyD_cbv t1)) (coalg_obj (tyD_cbv t2))).

(** *** Syntactic decomposition *)

Definition al_var_l :
    @named_expr R Ar R_obj
      (("_"%string, tunit) :: ("l"%string, tfun tunit tunit) :: nil)
      (tfun tunit tunit) :=
  [ # "l" ].

Definition al_if :
    @named_expr R Ar R_obj
      (("_"%string, tunit) :: ("l"%string, tfun tunit tunit) :: nil)
      tunit :=
  [ if Bern (Const pr [| 0%R |]) then () else # "l" @ () ].

Lemma ex_almost_loop_decomp :
  ex_almost_loop (P := P) pr =
  ne_let "l" (ne_fix "l" (ex_almost_loop_body (P := P) pr))
    (ne_app (ne_var (nv_head "l" (tfun tunit tunit) nil)) ne_tt).
Proof. by []. Qed.

Lemma ex_almost_loop_body_decomp :
  ex_almost_loop_body (P := P) pr = ne_lam "_" al_if.
Proof. by []. Qed.

(** The clean coin's underlying [tProb] argument: the constant
    [pr_val pr] pushed through the bundle's factoring [po_into] at the
    real literal [0]. *)
Local Notation al_coin_arg :=
  (ne_to_prob (po_into P (cst (pr_val pr)) (measurable_cst (pr_val pr))
                 (fun=> pr_ge0 pr) (fun=> pr_le1 pr)) (ne_real 0%R)).

Lemma al_if_decomp :
  al_if = ne_if tunit
            (ne_bernoulli_p (po_density P) (po_density_meas P)
               (po_ge0 P) (po_le1 P) al_coin_arg)
            ne_tt
            (ne_app al_var_l ne_tt).
Proof. by []. Qed.

Let Hone : cone_norm (one1 : cone_one_car Ar) <= 1.
Proof. by rewrite one1_norm. Qed.

(** *** The reduction chain (steps 1-4, mirrored) *)

Definition al_W0 :
    linhom_car Ar (Bang Ar (Lty tunit tunit))
                  (Bang Ar (Lty tunit tunit)) :=
  Lfun (tensor_curry (eD_cbv' (ex_almost_loop_body (P := P) pr)))
       one1.

Lemma al_W0_ball : cone_norm al_W0 <= 1.
Proof. exact: le_trans (cones_hom_norm_le1 _ _) Hone. Qed.

(** The promoted fixpoint value is a setlike unit-ball point, so the
    [let rec] continuation environment is one too. *)
Lemma al_fix_prom_ball :
  cone_norm ((sc_fun (fix_value (Lty tunit tunit)) al_W0)!) <= 1.
Proof. exact: prom_ball (fix_value_ball al_W0 al_W0_ball). Qed.

Lemma al_fix_prom_setlike :
  Lfun (coalg_str (tyD_cbv (tfun tunit tunit)))
       ((sc_fun (fix_value (Lty tunit tunit)) al_W0)!) =
  ((sc_fun (fix_value (Lty tunit tunit)) al_W0)!)!.
Proof.
rewrite -[tyD_cbv (tfun tunit tunit)]
        /(bang_cofree (Lty tunit tunit)) bang_cofree_str.
exact: (dig_prom _ (fix_value_ball al_W0 al_W0_ball)).
Qed.

Definition al_env0 :
    coalg_obj (ctxD_cbv (drop_names
      (("l"%string, tfun tunit tunit) :: nil))) :=
  one1 ⊗p (sc_fun (fix_value (Lty tunit tunit)) al_W0)!.

Lemma al_env0_ball : cone_norm al_env0 <= 1.
Proof.
by rewrite /al_env0 tensor_normME one1_norm mul1r al_fix_prom_ball.
Qed.

Lemma al_env0_setlike :
  Lfun (coalg_str (ctxD_cbv (drop_names
         (("l"%string, tfun tunit tunit) :: nil)))) al_env0 = al_env0!.
Proof.
exact: (coalg_str_tensor_setlike (P:=EM_term)
          (Q:=tyD_cbv (tfun tunit tunit))
          Hone al_fix_prom_ball coalg_str_one1 al_fix_prom_setlike).
Qed.

Definition al_iter (n : nat) : cone_one_car Ar :=
  linhom_fun (fix_chain al_W0 n) one1.

Lemma al_iter_chain n : precone_le (al_iter n) (al_iter n.+1).
Proof.
exact: (linhom_le_pointwise (fix_chain_chain al_W0_ball n) one1).
Qed.

Lemma al_iter_ball n : cone_norm (al_iter n) <= 1.
Proof.
apply: le_trans
  (linhom_norm_apply_le (fix_chain_ball al_W0_ball n) one1) _.
by rewrite mul1r Hone.
Qed.

Local Notation al_denot :=
  (linhom_fun (ex_almost_loop_cbv P R_to_carrier_meas pr)
     one1).

Lemma ex_almost_loop_app_E :
  al_denot =
  linhom_fun (sc_fun (fix_value (Lty tunit tunit)) al_W0) one1.
Proof.
rewrite /ex_almost_loop_cbv /eD icones_to_linhomE ex_almost_loop_decomp.
have HoneG : cone_norm
    (one1 : coalg_obj (ctxD_cbv (drop_names (nil : named_ctx Ar)))) <= 1.
  by rewrite one1_norm.
rewrite (eD_let_at_setlike "l"
          (ne_fix "l" (ex_almost_loop_body (P := P) pr))
          (ne_app (ne_var (nv_head "l" (tfun tunit tunit) nil)) ne_tt)
          HoneG coalg_str_one1).
rewrite (eD_fix_at_setlike "l" (ex_almost_loop_body (P := P) pr)
          HoneG coalg_str_one1).
rewrite (eD_app_at_setlike R_carrier_eq R_carrier_meas R_to_carrier_meas al_env0_ball al_env0_setlike).
rewrite (eD_var_head_at_setlike "l"
          (t := tfun tunit tunit)
          ((sc_fun (fix_value (Lty tunit tunit)) al_W0)!)
          HoneG coalg_str_one1).
rewrite (eD_tt_at_setlike al_env0_ball al_env0_setlike).
by rewrite (der_prom _ (fix_value_ball al_W0 al_W0_ball)).
Qed.

Lemma ex_almost_loop_sup_E :
  al_denot = cone_sup_ball al_iter al_iter_chain al_iter_ball.
Proof.
rewrite ex_almost_loop_app_E (fix_value_E al_W0_ball).
rewrite (linhom_fun_sup_ball (fix_chain_chain al_W0_ball)
  (fix_chain_ball al_W0_ball) Hone al_iter_chain al_iter_ball).
by [].
Qed.

Lemma al_chain_prom_ball n : cone_norm ((fix_chain al_W0 n)!) <= 1.
Proof. exact: prom_ball (fix_chain_ball al_W0_ball n). Qed.

Lemma al_chain_prom_setlike n :
  Lfun (coalg_str (tyD_cbv (tfun tunit tunit)))
       ((fix_chain al_W0 n)!) = ((fix_chain al_W0 n)!)!.
Proof.
rewrite -[tyD_cbv (tfun tunit tunit)]
        /(bang_cofree (Lty tunit tunit)) bang_cofree_str.
exact: (dig_prom _ (fix_chain_ball al_W0_ball n)).
Qed.

Lemma al_env_ball n :
  cone_norm (one1 ⊗p (fix_chain al_W0 n)!) <= 1.
Proof.
by rewrite tensor_normME one1_norm mul1r al_chain_prom_ball.
Qed.

Lemma al_env_setlike n :
  Lfun (coalg_str (ctxD_cbv (drop_names
         (("l"%string, tfun tunit tunit) :: nil))))
       (one1 ⊗p (fix_chain al_W0 n)!) =
  (one1 ⊗p (fix_chain al_W0 n)!)!.
Proof.
exact: (coalg_str_tensor_setlike (P:=EM_term)
          (Q:=tyD_cbv (tfun tunit tunit))
          Hone (al_chain_prom_ball n) coalg_str_one1
          (al_chain_prom_setlike n)).
Qed.

Lemma al_W0_at_prom n :
  linhom_fun al_W0 ((fix_chain al_W0 n)!) =
  (Lfun (tensor_curry (eD_cbv' al_if))
     (one1 ⊗p (fix_chain al_W0 n)!))!.
Proof.
rewrite {1}/al_W0 tensor_curryE ex_almost_loop_body_decomp eD_lam_E.
exact: (adj_psi_at_setlike
  (P:=ctxD_cbv (drop_names (("l"%string, tfun tunit tunit) :: nil)))
  _ (al_env_ball n) (al_env_setlike n)).
Qed.

Lemma ex_almost_loop_iter_S n :
  al_iter n.+1 =
  Lfun (eD_cbv' al_if)
       ((one1 ⊗p (fix_chain al_W0 n)!) ⊗p one1).
Proof.
rewrite /al_iter fix_chain_S al_W0_at_prom.
rewrite (der_prom _ (le_trans (cones_hom_norm_le1 _ _) (al_env_ball n))).
exact: tensor_curryE.
Qed.

Definition al_env3 (n : nat) :
    coalg_obj (ctxD_cbv (drop_names
      (("_"%string, tunit) :: ("l"%string, tfun tunit tunit) :: nil))) :=
  (one1 ⊗p (fix_chain al_W0 n)!) ⊗p one1.

Lemma al_env3_ball n : cone_norm (al_env3 n) <= 1.
Proof.
rewrite /al_env3 tensor_normME.
by rewrite mulr_ile1 ?cone_norm_ge0 ?al_env_ball ?Hone.
Qed.

Lemma al_env3_setlike n :
  Lfun (coalg_str (ctxD_cbv (drop_names
         (("_"%string, tunit) :: ("l"%string, tfun tunit tunit) :: nil))))
       (al_env3 n) = (al_env3 n)!.
Proof.
exact: (coalg_str_tensor_setlike
          (P:=ctxD_cbv (drop_names
                (("l"%string, tfun tunit tunit) :: nil)))
          (Q:=EM_term)
          (al_env_ball n) Hone (al_env_setlike n) coalg_str_one1).
Qed.

Lemma al_var_l_E n :
  Lfun (eD_cbv' al_var_l) (al_env3 n) = (fix_chain al_W0 n)!.
Proof.
apply: (eq_trans (y := Lfun (icones_comp
  (em_proj2_mor (R:=R) EM_term (tyD_cbv (tfun tunit tunit)))
  (em_proj1_mor (R:=R)
     (ctxD_cbv (drop_names (("l"%string, tfun tunit tunit) :: nil)))
     EM_term)) (al_env3 n))).
  by [].
rewrite Lfun_comp.
rewrite (em_proj1_morE (Q:=EM_term) Hone coalg_str_one1).
exact: (em_proj2_morE (P:=EM_term) Hone coalg_str_one1).
Qed.

Lemma al_tt_E n :
  Lfun (eD_cbv' (@ne_tt R Ar R_obj
         (("_"%string, tunit) :: ("l"%string, tfun tunit tunit) :: nil)))
       (al_env3 n) = one1.
Proof.
rewrite eD_tt_E.
apply: (eq_trans (y := Lfun (coalg_e (ctxD_cbv (drop_names
  (("_"%string, tunit) :: ("l"%string, tfun tunit tunit) :: nil))))
  (al_env3 n))).
  by [].
exact: (coalg_e_setlike (al_env3_ball n) (al_env3_setlike n)).
Qed.

(** The recursive call at the unit argument IS the previous iterate. *)
Lemma al_else_E n :
  Lfun (eD_cbv' (ne_app al_var_l ne_tt)) (al_env3 n) = al_iter n.
Proof.
rewrite (eD_app_at_setlike R_carrier_eq R_carrier_meas R_to_carrier_meas (al_env3_ball n) (al_env3_setlike n)).
rewrite al_var_l_E al_tt_E.
by rewrite (der_prom _ (fix_chain_ball al_W0_ball n)).
Qed.

(** *** Clean-surface coin leaf

    The clean [tProb] constant coin [Bern (Const pr [|0|])] denotes, at
    any setlike unit-ball environment, the SAME [bernoulli p] cone as
    the legacy constant coin [Bernoulli pr]: the real literal [0] is the
    Dirac [δ_0], pushed by the bundle factoring [po_into (cst p)] to
    [δ_(po_into 0)], on which the carrier-density Bernoulli lift
    [bern_lift_P] reads off [bernoulli (po_density P (po_into 0))], and
    [po_into_E] computes that density back to [pr_val pr = p]. *)
Lemma al_coin_E n :
  Lfun (eD_cbv' (ne_bernoulli_p (po_density P) (po_density_meas P)
                   (po_ge0 P) (po_le1 P) al_coin_arg))
       (al_env3 n) = bernoulli (Ar:=Ar) p Hp0 Hp1.
Proof.
rewrite eD_bernoulli_p_E Lfun_comp.
rewrite -[bern_lift_g _ _ _]/(bern_lift_P P).
rewrite eD_to_prob_E Lfun_comp.
rewrite eD_real_E /real_icones (const_iconesE (al_env3_ball n) (al_env3_setlike n)).
rewrite FMeas_fmap_dirac bern_lift_P_dirac.
apply: bool_cone_eq; apply: val_inj => /=; by rewrite /po_density po_into_E.
Qed.

(** The Kleene step is the affine combination
    [ν_{n+1} = p·1 + (1-p)·ν_n]. *)
Lemma al_step n :
  al_iter n.+1 =
  bool_case (bernoulli (Ar:=Ar) p Hp0 Hp1) one1 (al_iter n).
Proof.
rewrite ex_almost_loop_iter_S al_if_decomp eD_if_E.
rewrite (if_icones_at
  (eD_cbv' (@ne_tt R Ar R_obj
     (("_"%string, tunit) :: ("l"%string, tfun tunit tunit) :: nil)))
  (eD_cbv' (ne_app al_var_l ne_tt))
  (eD_cbv' (ne_bernoulli_p (po_density P) (po_density_meas P)
              (po_ge0 P) (po_le1 P) al_coin_arg))
  (al_env3_ball n) (al_env3_setlike n)).
by rewrite al_tt_E al_else_E al_coin_E.
Qed.

(** *** The scalar cascade and the dichotomy theorems *)

Lemma al_iter_0 : al_iter 0 = precone_zero.
Proof. by rewrite /al_iter fix_chain_0 linhom_fun_zero. Qed.

Definition al_val (n : nat) : R := ((c1_val (al_iter n))%:num)%R.

Lemma al_val_0 : al_val 0%N = 0%R.
Proof. by rewrite /al_val al_iter_0. Qed.

Lemma al_norm n : cone_norm (al_iter n) = al_val n.
Proof. by []. Qed.

Lemma al_val_S n : al_val n.+1 = (p + (1 - p) * al_val n)%R.
Proof. by rewrite /al_val al_step /= mulr1. Qed.

(** Almost-sure termination at positive flip probability: the
    denotation has full mass. *)
Theorem ex_almost_loop_cbv_mass_one : (0 < p)%R ->
  cone_norm al_denot = 1%R.
Proof.
move=> Hp.
apply/le_anti/andP; split.
- by rewrite ex_almost_loop_sup_E cone_sup_ball_norm.
- have Hq0 : (0 <= 1 - p)%R by rewrite subr_ge0 Hp1.
  have Hq1 : (1 - p < 1)%R by rewrite ltrBlDr ltrDl.
  have Hcvg := affine_iter_cvg_real p (1 - p) Hq0 al_val_0 al_val_S Hq1.
  rewrite subKr divff ?gt_eqF// in Hcvg.
  have HK : forall n, (al_val n <= cone_norm al_denot)%R.
    move=> n; rewrite -al_norm ex_almost_loop_sup_E.
    apply: cone_normp; exact: cone_sup_ball_ub.
  rewrite -(cvg_lim (@Rhausdorff R) Hcvg).
  apply: limr_le.
  + by apply/cvg_ex; exists 1%R.
  + by apply: nearW => n; exact: HK.
Qed.

(** Certain divergence at [p = 0]: the chain is constantly zero. *)
Theorem ex_almost_loop_cbv_zero : p = 0%R -> al_denot = precone_zero.
Proof.
move=> Hp.
have Hbern : bernoulli (Ar:=Ar) p Hp0 Hp1 = bool_dirac_false.
  by apply: bool_cone_eq; apply: val_inj => /=; rewrite Hp ?subr0.
have Hiter0 : forall n, al_iter n = precone_zero.
  elim=> [ | n IH]; first exact: al_iter_0.
  by rewrite al_step Hbern bool_case_false IH.
rewrite ex_almost_loop_sup_E.
apply: precone_le_anti.
- apply: cone_sup_ball_lub => n.
  rewrite Hiter0; exact: precone_le_refl.
- exact: precone_le0.
Qed.

(** A norm-one element of the one-dimensional unit cone is the unit
    point: [cone_one_car Ar] is a thin wrapper around a nonnegative
    scalar, so [cone_norm x = (c1_val x)%:num] and [one1] is the
    scalar [1]. *)
Lemma cone_one_norm_eq1 (x : cone_one_car Ar) :
  cone_norm x = 1%R -> x = one1.
Proof.
rewrite /cone_norm/= /c1_norm => Hx.
by apply: cone_one_eq; apply: val_inj; rewrite /= Hx.
Qed.

(** Almost-sure termination at positive flip probability pins the CBV
    denotation as the unit point [one1] (the Dirac on the one-point
    space), strengthening [ex_almost_loop_cbv_mass_one] from the total
    mass to the cone element itself. *)
Theorem ex_almost_loop_cbv_dirac : (0 < p)%R -> al_denot = one1.
Proof. by move=> Hp; apply: cone_one_norm_eq1; exact: ex_almost_loop_cbv_mass_one. Qed.

End AlmostLoopRider.

(** ** §4 — Rider: [ex_geom] — the geometric counter has total mass [1]

    The same skeleton on
    [[
       (let rec g = λ_. if Bernoulli(½) then 0 else 1 + g ()) ()
    ]]
    — the iterate is [ν_{n+1} = ½·δ_0 + ½·(δ_1 + ν_n)] where the ELSE
    branch shifts the recursive call by [1] through the arithmetic
    lift; the translation-mass invariance [add_lift_mass] reduces the
    mass cascade to [x_{n+1} = ½ + ½·x_n], whose limit is [1]: the
    geometric counter terminates almost surely. *)

Section GeomRider.
Variables (R : realType) (Ar : MeasSubcat R).
(* Reparameterized over the bundled [probObj]: the real object and its
   carrier casts come from [P]. *)
Variable (P : probObj Ar).
Local Notation R_obj := (po_robj P).
Local Notation R_carrier_eq := (po_robj_eq P).
Local Notation R_carrier_meas := (po_robj_meas P).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '!'" := (prom x) (at level 2, format "x '!'").
Local Notation eD_cbv' :=
  (@eD_cbv R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation eD' :=
  (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation cR := (carrier_to_R R_carrier_eq).
Local Notation tR' := (tR R_obj).
Local Notation Lty t1 t2 :=
  (linhom_car Ar (coalg_obj (tyD_cbv t1)) (coalg_obj (tyD_cbv t2))).

(** *** Syntactic decomposition *)

Definition g_var :
    @named_expr R Ar R_obj
      (("_"%string, tunit) :: ("g"%string, tfun tunit tR') :: nil)
      (tfun tunit tR') :=
  [ # "g" ].

Definition g_if :
    @named_expr R Ar R_obj
      (("_"%string, tunit) :: ("g"%string, tfun tunit tR') :: nil) tR' :=
  [ if Bernoulli [| (1 / 2 : R) |]
    then [| 0%R |]
    else [| 1%R |] + # "g" @ () ].

Lemma ex_geom_decomp :
  (ex_geom : @named_expr R Ar R_obj nil tR') =
  ne_let "g" (ne_fix "g" (ex_geom_body : @named_expr R Ar R_obj _ _))
    (ne_app (ne_var (nv_head "g" (tfun tunit tR') nil)) ne_tt).
Proof. by []. Qed.

Lemma ex_geom_body_decomp :
  (ex_geom_body : @named_expr R Ar R_obj _ _) = ne_lam "_" g_if.
Proof. by []. Qed.

(** The fair coin's underlying constant-literal Bernoulli: success
    probability [1/2] with the [[0,1]] bounds discharged by [lra]
    (the [Bernoulli [| (1/2 : R) |]] surface form). *)
Local Notation g_coin :=
  (ne_bernoulli (Ar:=Ar) (R_obj:=R_obj)
     (G := ("_"%string, tunit) :: ("g"%string, tfun tunit tR') :: nil)
     (1 / 2 : R) (bernoulli_half_ge0 R) (bernoulli_half_le1 R)).

Lemma g_if_decomp :
  g_if = ne_if tR'
           g_coin
           (ne_real 0%R)
           (ne_add (ne_real 1%R) (ne_app g_var ne_tt)).
Proof.
rewrite /g_if /=; congr (ne_if _ (ne_bernoulli _ _ _) _ _);
  exact: bool_irrelevance.
Qed.

Let Hone : cone_norm (one1 : cone_one_car Ar) <= 1.
Proof. by rewrite one1_norm. Qed.

(** *** The reduction chain (steps 1-4, mirrored) *)

Definition g_W0 :
    linhom_car Ar (Bang Ar (Lty tunit tR')) (Bang Ar (Lty tunit tR')) :=
  Lfun (tensor_curry
         (eD_cbv' (ex_geom_body : @named_expr R Ar R_obj _ _))) one1.

Lemma g_W0_ball : cone_norm g_W0 <= 1.
Proof. exact: le_trans (cones_hom_norm_le1 _ _) Hone. Qed.

(** The promoted fixpoint value is a setlike unit-ball point, so the
    [let rec] continuation environment is one too. *)
Lemma g_fix_prom_ball :
  cone_norm ((sc_fun (fix_value (Lty tunit tR')) g_W0)!) <= 1.
Proof. exact: prom_ball (fix_value_ball g_W0 g_W0_ball). Qed.

Lemma g_fix_prom_setlike :
  Lfun (coalg_str (tyD_cbv (tfun tunit tR')))
       ((sc_fun (fix_value (Lty tunit tR')) g_W0)!) =
  ((sc_fun (fix_value (Lty tunit tR')) g_W0)!)!.
Proof.
rewrite -[tyD_cbv (tfun tunit tR')]
        /(bang_cofree (Lty tunit tR')) bang_cofree_str.
exact: (dig_prom _ (fix_value_ball g_W0 g_W0_ball)).
Qed.

Definition g_env0 :
    coalg_obj (ctxD_cbv (drop_names
      (("g"%string, tfun tunit tR') :: nil))) :=
  one1 ⊗p (sc_fun (fix_value (Lty tunit tR')) g_W0)!.

Lemma g_env0_ball : cone_norm g_env0 <= 1.
Proof.
by rewrite /g_env0 tensor_normME one1_norm mul1r g_fix_prom_ball.
Qed.

Lemma g_env0_setlike :
  Lfun (coalg_str (ctxD_cbv (drop_names
         (("g"%string, tfun tunit tR') :: nil)))) g_env0 = g_env0!.
Proof.
exact: (coalg_str_tensor_setlike (P:=EM_term)
          (Q:=tyD_cbv (tfun tunit tR'))
          Hone g_fix_prom_ball coalg_str_one1 g_fix_prom_setlike).
Qed.

Definition g_iter (n : nat) : coalg_obj (tyD_cbv tR') :=
  linhom_fun (fix_chain g_W0 n) one1.

Lemma g_iter_chain n : precone_le (g_iter n) (g_iter n.+1).
Proof.
exact: (linhom_le_pointwise (fix_chain_chain g_W0_ball n) one1).
Qed.

Lemma g_iter_ball n : cone_norm (g_iter n) <= 1.
Proof.
apply: le_trans
  (linhom_norm_apply_le (fix_chain_ball g_W0_ball n) one1) _.
by rewrite mul1r Hone.
Qed.

Local Notation g_denot :=
  (linhom_fun (ex_geom_cbv P R_to_carrier_meas) one1).

Lemma ex_geom_app_E :
  g_denot = linhom_fun (sc_fun (fix_value (Lty tunit tR')) g_W0) one1.
Proof.
rewrite /ex_geom_cbv /eD icones_to_linhomE ex_geom_decomp.
have HoneG : cone_norm
    (one1 : coalg_obj (ctxD_cbv (drop_names (nil : named_ctx Ar)))) <= 1.
  by rewrite one1_norm.
rewrite (eD_let_at_setlike "g"
          (ne_fix "g" (ex_geom_body : @named_expr R Ar R_obj _ _))
          (ne_app (ne_var (nv_head "g" (tfun tunit tR') nil)) ne_tt)
          HoneG coalg_str_one1).
rewrite (eD_fix_at_setlike "g" (ex_geom_body : @named_expr R Ar R_obj _ _)
          HoneG coalg_str_one1).
rewrite (eD_app_at_setlike R_carrier_eq R_carrier_meas R_to_carrier_meas g_env0_ball g_env0_setlike).
rewrite (eD_var_head_at_setlike "g"
          (t := tfun tunit tR')
          ((sc_fun (fix_value (Lty tunit tR')) g_W0)!)
          HoneG coalg_str_one1).
rewrite (eD_tt_at_setlike g_env0_ball g_env0_setlike).
by rewrite (der_prom _ (fix_value_ball g_W0 g_W0_ball)).
Qed.

Lemma ex_geom_sup_E :
  g_denot = cone_sup_ball g_iter g_iter_chain g_iter_ball.
Proof.
rewrite ex_geom_app_E (fix_value_E g_W0_ball).
rewrite (linhom_fun_sup_ball (fix_chain_chain g_W0_ball)
  (fix_chain_ball g_W0_ball) Hone g_iter_chain g_iter_ball).
by [].
Qed.

Lemma g_chain_prom_ball n : cone_norm ((fix_chain g_W0 n)!) <= 1.
Proof. exact: prom_ball (fix_chain_ball g_W0_ball n). Qed.

Lemma g_chain_prom_setlike n :
  Lfun (coalg_str (tyD_cbv (tfun tunit tR')))
       ((fix_chain g_W0 n)!) = ((fix_chain g_W0 n)!)!.
Proof.
rewrite -[tyD_cbv (tfun tunit tR')]
        /(bang_cofree (Lty tunit tR')) bang_cofree_str.
exact: (dig_prom _ (fix_chain_ball g_W0_ball n)).
Qed.

Lemma g_env_ball n :
  cone_norm (one1 ⊗p (fix_chain g_W0 n)!) <= 1.
Proof.
by rewrite tensor_normME one1_norm mul1r g_chain_prom_ball.
Qed.

Lemma g_env_setlike n :
  Lfun (coalg_str (ctxD_cbv (drop_names
         (("g"%string, tfun tunit tR') :: nil))))
       (one1 ⊗p (fix_chain g_W0 n)!) =
  (one1 ⊗p (fix_chain g_W0 n)!)!.
Proof.
exact: (coalg_str_tensor_setlike (P:=EM_term)
          (Q:=tyD_cbv (tfun tunit tR'))
          Hone (g_chain_prom_ball n) coalg_str_one1
          (g_chain_prom_setlike n)).
Qed.

Lemma g_W0_at_prom n :
  linhom_fun g_W0 ((fix_chain g_W0 n)!) =
  (Lfun (tensor_curry (eD_cbv' g_if))
     (one1 ⊗p (fix_chain g_W0 n)!))!.
Proof.
rewrite {1}/g_W0 tensor_curryE ex_geom_body_decomp eD_lam_E.
exact: (adj_psi_at_setlike
  (P:=ctxD_cbv (drop_names (("g"%string, tfun tunit tR') :: nil)))
  _ (g_env_ball n) (g_env_setlike n)).
Qed.

Lemma ex_geom_iter_S n :
  g_iter n.+1 =
  Lfun (eD_cbv' g_if) ((one1 ⊗p (fix_chain g_W0 n)!) ⊗p one1).
Proof.
rewrite /g_iter fix_chain_S g_W0_at_prom.
rewrite (der_prom _ (le_trans (cones_hom_norm_le1 _ _) (g_env_ball n))).
exact: tensor_curryE.
Qed.

Definition g_env3 (n : nat) :
    coalg_obj (ctxD_cbv (drop_names
      (("_"%string, tunit) :: ("g"%string, tfun tunit tR') :: nil))) :=
  (one1 ⊗p (fix_chain g_W0 n)!) ⊗p one1.

Lemma g_env3_ball n : cone_norm (g_env3 n) <= 1.
Proof.
rewrite /g_env3 tensor_normME.
by rewrite mulr_ile1 ?cone_norm_ge0 ?g_env_ball ?Hone.
Qed.

Lemma g_env3_setlike n :
  Lfun (coalg_str (ctxD_cbv (drop_names
         (("_"%string, tunit) :: ("g"%string, tfun tunit tR') :: nil))))
       (g_env3 n) = (g_env3 n)!.
Proof.
exact: (coalg_str_tensor_setlike
          (P:=ctxD_cbv (drop_names (("g"%string, tfun tunit tR') :: nil)))
          (Q:=EM_term)
          (g_env_ball n) Hone (g_env_setlike n) coalg_str_one1).
Qed.

Lemma g_var_E n :
  Lfun (eD_cbv' g_var) (g_env3 n) = (fix_chain g_W0 n)!.
Proof.
apply: (eq_trans (y := Lfun (icones_comp
  (em_proj2_mor (R:=R) EM_term (tyD_cbv (tfun tunit tR')))
  (em_proj1_mor (R:=R)
     (ctxD_cbv (drop_names (("g"%string, tfun tunit tR') :: nil)))
     EM_term)) (g_env3 n))).
  by [].
rewrite Lfun_comp.
rewrite (em_proj1_morE (Q:=EM_term) Hone coalg_str_one1).
exact: (em_proj2_morE (P:=EM_term) Hone coalg_str_one1).
Qed.

Lemma g_tt_E n :
  Lfun (eD_cbv' (@ne_tt R Ar R_obj
         (("_"%string, tunit) :: ("g"%string, tfun tunit tR') :: nil)))
       (g_env3 n) = one1.
Proof.
rewrite eD_tt_E.
apply: (eq_trans (y := Lfun (coalg_e (ctxD_cbv (drop_names
  (("_"%string, tunit) :: ("g"%string, tfun tunit tR') :: nil))))
  (g_env3 n))).
  by [].
exact: (coalg_e_setlike (g_env3_ball n) (g_env3_setlike n)).
Qed.

Lemma g_then_E n :
  Lfun (eD_cbv' (@ne_real R Ar R_obj
         (("_"%string, tunit) :: ("g"%string, tfun tunit tR') :: nil) 0%R))
       (g_env3 n) =
  dirac_fmeas (R_to_carrier R_carrier_eq 0%R).
Proof.
rewrite eD_real_E /real_icones.
by rewrite (const_iconesE (g_env3_ball n) (g_env3_setlike n)).
Qed.

Lemma g_one_E n :
  Lfun (eD_cbv' (@ne_real R Ar R_obj
         (("_"%string, tunit) :: ("g"%string, tfun tunit tR') :: nil) 1%R))
       (g_env3 n) =
  dirac_fmeas (R_to_carrier R_carrier_eq 1%R).
Proof.
rewrite eD_real_E /real_icones.
by rewrite (const_iconesE (g_env3_ball n) (g_env3_setlike n)).
Qed.

Lemma g_call_E n :
  Lfun (eD_cbv' (ne_app g_var ne_tt)) (g_env3 n) = g_iter n.
Proof.
rewrite (eD_app_at_setlike R_carrier_eq R_carrier_meas R_to_carrier_meas (g_env3_ball n) (g_env3_setlike n)).
rewrite g_var_E g_tt_E.
by rewrite (der_prom _ (fix_chain_ball g_W0_ball n)).
Qed.

(** ELSE: the shifted recursive call [1 + g ()]. *)
Lemma g_else_E n :
  Lfun (eD_cbv' (ne_add (ne_real 1%R) (ne_app g_var ne_tt))) (g_env3 n) =
  Lfun (@add_lift R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas)
       (dirac_fmeas (R_to_carrier R_carrier_eq 1%R) ⊗p g_iter n).
Proof.
rewrite eD_add_E.
rewrite (Lfun_comp
  (@add_lift R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas)
  (em_pair_mor (eD_cbv' (ne_real 1%R)) (eD_cbv' (ne_app g_var ne_tt)))
  (g_env3 n)).
rewrite /em_pair_mor (Lfun_comp
  (tensor_mor (eD_cbv' (ne_real 1%R)) (eD_cbv' (ne_app g_var ne_tt)))
  (coalg_d (ctxD_cbv (drop_names
     (("_"%string, tunit) :: ("g"%string, tfun tunit tR') :: nil))))
  (g_env3 n)).
rewrite (coalg_d_setlike (g_env3_ball n) (g_env3_setlike n)) tensor_morE.
by rewrite g_one_E g_call_E.
Qed.

(** *** Constant-literal coin leaf

    The fair coin [Bernoulli [| (1/2 : R) |]] denotes, at any setlike
    unit-ball environment, the [bernoulli (1/2)] cone directly: the
    constant-coin denotation pin [eD_bernoulli_E] rewrites the leaf to
    the constant [icones_hom] [bernoulli_icones … (1/2)], which
    [const_iconesE] evaluates to [bernoulli (1/2)] at the setlike
    environment.  No [tProb]/[po_into]/[bern_lift_P] detour. *)
Lemma g_coin_E n :
  Lfun (eD_cbv' g_coin) (g_env3 n) =
  bernoulli (Ar:=Ar) (1 / 2 : R) (bernoulli_half_ge0 R) (bernoulli_half_le1 R).
Proof.
rewrite eD_bernoulli_E.
exact: (const_iconesE (g_env3_ball n) (g_env3_setlike n)).
Qed.

Lemma g_step n :
  g_iter n.+1 =
  bool_case (bernoulli (Ar:=Ar) (1 / 2 : R) (bernoulli_half_ge0 R)
               (bernoulli_half_le1 R))
    (dirac_fmeas (R_to_carrier R_carrier_eq 0%R))
    (Lfun (@add_lift R Ar R_obj R_carrier_eq R_carrier_meas
             R_to_carrier_meas)
       (dirac_fmeas (R_to_carrier R_carrier_eq 1%R) ⊗p g_iter n)).
Proof.
rewrite ex_geom_iter_S g_if_decomp eD_if_E.
rewrite (if_icones_at
  (eD_cbv' (@ne_real R Ar R_obj
     (("_"%string, tunit) :: ("g"%string, tfun tunit tR') :: nil) 0%R))
  (eD_cbv' (ne_add (ne_real 1%R) (ne_app g_var ne_tt)))
  (eD_cbv' g_coin)
  (g_env3_ball n) (g_env3_setlike n)).
by rewrite g_then_E g_else_E g_coin_E.
Qed.

(** *** The half-half cascade and the mass-one theorem *)

Local Open Scope ereal_scope.

(** *** Per-[U] pushforward evaluation

    Generalises [ppl.v::FMeas_fmap_setT_E] from [setT] to an arbitrary
    measurable [U]: the pushforward [FMeas_fmap φ] of a measure [ν]
    evaluates at [U] by integrating the Dirac masses [δ_(φ r)(U)]
    against [ν], which is the indicator of [φ ⁻¹` U]. *)
Lemma FMeas_fmap_U_E (X Y : ar_obj Ar) (φ : ar_hom Ar X Y)
    (ν : fmeas R (ar_carrier Ar X))
    (U : set (ar_carrier Ar Y)) (mU : measurable U) :
  fmeas_mu (Lfun (FMeas_fmap φ) ν) U =
  fmeas_mu ν (φ @^-1` U).
Proof.
have HE : Lfun (FMeas_fmap φ) ν =
    icone_integral (path_fun (push_dirac_path φ))
                   (path_is_path (push_dirac_path φ)) ν.
  by rewrite /FMeas_fmap (linhom_iconesE _ (FMeas_fmap_norm_le1 φ) ν).
rewrite HE.
rewrite (distributions.icone_integral_fmeas_E
           (path_is_path (push_dirac_path φ)) ν mU).
have mpreU : measurable (φ @^-1` U).
  have H := measurable_funPT φ measurableT U mU.
  by rewrite setTI in H.
under eq_integral => r _.
  have -> : fmeas_mu (path_fun (push_dirac_path φ) r) U
          = fmeas_mu (dirac_fmeas (φ r) : FMeas Y) U by [].
  rewrite (dirac_fmeas_E (φ r) mU) diracE/=.
  have -> : ((φ r \in U)%:R)%:E = (\1_(φ @^-1` U) r)%:E :> \bar R.
    by rewrite indicE.
  over.
by rewrite integral_indic// setIT.
Qed.

(** The shift map [+a] on the real carrier, [s_shift a c = a + c]. *)
Local Notation s_shift a :=
  (fun c : ar_carrier Ar R_obj =>
     R_to_carrier R_carrier_eq (a + carrier_to_R R_carrier_eq c)).

(** Per-[U] evaluation of the arithmetic shift [add_lift (δ_a ⊗ ν)]:
    adding the constant [a] to each sample is the pushforward of [ν]
    along [+a].  This is the per-[U] refinement of [ppl.v::add_lift_mass]
    (the [U = setT] case). *)
Lemma add_lift_dirac_U (a : R) (ν : fmeas R (ar_carrier Ar R_obj))
    (U : set (ar_carrier Ar R_obj)) (mU : measurable U) :
  fmeas_mu (Lfun (@add_lift R Ar R_obj R_carrier_eq R_carrier_meas
                   R_to_carrier_meas)
              (dirac_fmeas (R_to_carrier R_carrier_eq a) ⊗p ν)) U =
  fmeas_mu ν ((s_shift a) @^-1` U).
Proof.
set am := @add_meas R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas.
set apc := (ar_prod_cast (R:=R) (Ar:=Ar) (X:=R_obj) (Y:=R_obj)).
rewrite /add_lift.
rewrite -[Lfun _ _]/(Lfun (FMeas_fmap am)
  (Lfun (fmeas_lax R_obj R_obj)
    (dirac_fmeas (R_to_carrier R_carrier_eq a) ⊗p ν))).
have maddU : measurable (am @^-1` U).
  have H := measurable_funPT am measurableT U mU.
  by rewrite setTI in H.
rewrite (FMeas_fmap_U_E am _ mU).
rewrite (fmeas_lax_E (dirac_fmeas (R_to_carrier R_carrier_eq a)) ν).
rewrite (fmeas_lax_preE (dirac_fmeas (R_to_carrier R_carrier_eq a)) ν
           (am @^-1` U) maddU).
have mprecast : measurable (apc @^-1` (am @^-1` U)).
  have Hc := ar_prod_cast_meas Ar R_obj R_obj.
  have H := Hc measurableT (am @^-1` U) maddU.
  by rewrite setTI in H.
rewrite (fubini.fmeas_prodE _ _ (apc @^-1` (am @^-1` U)) mprecast).
(* The product measure on a general set is the iterated integral of
   the [ν]-sections against the outer Dirac, which collapses to the
   section at [R_to_carrier a]. *)
rewrite -[lebesgue_integral_fubini.product_measure1 _ _ _]/(
  \int[fubini.fmeas_fin_view (dirac_fmeas (R_to_carrier R_carrier_eq a))]_x
   (fubini.fmeas_fin_view ν) (xsection (apc @^-1` (am @^-1` U)) x)).
have eq_xint :
    \int[fubini.fmeas_fin_view (dirac_fmeas (R_to_carrier R_carrier_eq a))]_x
       (fubini.fmeas_fin_view ν) (xsection (apc @^-1` (am @^-1` U)) x)
    = \int[\d_(R_to_carrier R_carrier_eq a)]_x
       (fubini.fmeas_fin_view ν) (xsection (apc @^-1` (am @^-1` U)) x).
  apply: eq_measure_integral => W mW _.
  transitivity (fmeas_mu (dirac_fmeas (R_to_carrier R_carrier_eq a)) W).
    exact: (fubini.fmeas_fin_viewE (dirac_fmeas (R_to_carrier R_carrier_eq a))
              W mW).
  exact: (dirac_fmeas_E _ mW).
have ms_sec : measurable_fun [set: ar_carrier Ar R_obj]
    (fun x => fubini.fmeas_fin_view ν (xsection (apc @^-1` (am @^-1` U)) x)).
  exact: (lebesgue_integral_fubini.measurable_fun_xsection
            (fubini.fmeas_fin_view ν) mprecast).
rewrite eq_xint (integral_dirac _ measurableT ms_sec).
rewrite diracT mul1e.
rewrite (fubini.fmeas_fin_viewE ν); last first.
  exact: (measurable_xsection _ mprecast).
congr (fmeas_mu ν _).
apply/seteqP; split=> y; rewrite /xsection/= inE /am /apc /preimage/=
  (add_meas_cast R_carrier_meas R_to_carrier_meas (R_to_carrier R_carrier_eq a) y)
  R_to_carrierK//.
Qed.

Lemma g_iter_0 : g_iter 0 = precone_zero.
Proof. by rewrite /g_iter fix_chain_0 linhom_fun_zero. Qed.

Definition g_val (n : nat) : R :=
  fine (fmeas_mu (g_iter n) [set: ar_carrier Ar R_obj]).

Lemma g_val_0 : g_val 0%N = 0%R.
Proof.
rewrite /g_val.
have -> : (g_iter 0 : fmeas R (ar_carrier Ar R_obj)) = fmeas_zero.
  by rewrite g_iter_0.
by rewrite fmeas_zeroE.
Qed.

(** The mass recurrence [x_{n+1} = ½ + ½·x_n]: the THEN Dirac has
    unit mass, and the shifted recursive call has the mass of the
    previous iterate by translation invariance ([add_lift_mass]). *)
Lemma g_val_S n : g_val n.+1 = (1 / 2 + (1 / 2) * g_val n)%R.
Proof.
rewrite /g_val g_step.
have -> : (bool_case (bernoulli (Ar:=Ar) (1 / 2 : R) (bernoulli_half_ge0 R)
               (bernoulli_half_le1 R))
    (dirac_fmeas (R_to_carrier R_carrier_eq 0%R))
    (Lfun (@add_lift R Ar R_obj R_carrier_eq R_carrier_meas
             R_to_carrier_meas)
       (dirac_fmeas (R_to_carrier R_carrier_eq 1%R) ⊗p g_iter n))
    : fmeas R (ar_carrier Ar R_obj)) =
  fmeas_add
    (fmeas_scale (NngNum (bernoulli_half_ge0 R))
       (dirac_fmeas (R_to_carrier R_carrier_eq 0%R)))
    (fmeas_scale (NngNum (subr_ge0_le1 (1 / 2 : R) (bernoulli_half_le1 R)))
       (Lfun (@add_lift R Ar R_obj R_carrier_eq R_carrier_meas
                R_to_carrier_meas)
          (dirac_fmeas (R_to_carrier R_carrier_eq 1%R) ⊗p g_iter n))).
  by [].
rewrite fmeas_addE 2!fmeas_scaleE dirac_fmeas_setT_E mule1.
rewrite add_lift_mass.
rewrite fineD//; first last.
  by rewrite fin_numM// fmeas_setT_fin.
rewrite fineM// ?fmeas_setT_fin//=.
congr (_ + _ * _)%R.
by rewrite {1}(splitr (1 : R)) addrK.
Qed.

(** Almost-sure termination of the geometric counter: the CBV
    denotation is a PROBABILITY distribution. *)
Theorem ex_geom_cbv_mass_one :
  fmeas_mu g_denot [set: ar_carrier Ar R_obj] = 1.
Proof.
rewrite ex_geom_sup_E.
apply: (fmeas_kleene_sup_U_E g_iter_chain g_iter_ball measurableT).
have HE : (fun n => fmeas_mu (g_iter n) [set: ar_carrier Ar R_obj]) =
          (fun n => (g_val n)%:E).
  by apply/funext => n; rewrite /g_val fineK// fmeas_setT_fin.
rewrite HE.
exact: (affine_iter_cvg_half g_val_0 g_val_S).
Qed.

(** *** The geometric distribution: [⟦ex_geom⟧ = Σ_k (1/2)^(k+1) δ_k]

    The per-iterate scaffolding above pins not just the total mass but
    the full per-set behaviour: the [n]-th Kleene iterate is the
    truncated geometric law [Σ_{k<n} (1/2)^(k+1) δ_k], and the
    denotation is its limit. *)

(** The embedded atom [k ∈ ℕ] as a point of the real carrier. *)
Local Notation gpt k := (R_to_carrier R_carrier_eq (k%:R : R)).

(** The geometric weight [(1/2)^(k+1)] as an ereal. *)
Local Notation geom_w k := (((1 / 2 : R) ^+ k.+1)%:E).

(** [add_lift] shifts the atom index by one: [s_shift 1] maps
    [gpt k] to [gpt k.+1]. *)
Lemma g_shift_atom (k : nat) (U : set (ar_carrier Ar R_obj))
    (mU : measurable U) :
  fmeas_mu (dirac_fmeas (gpt k)) ((s_shift (1 : R)) @^-1` U) =
  fmeas_mu (dirac_fmeas (gpt k.+1)) U.
Proof.
have ms : measurable_fun [set: ar_carrier Ar R_obj] (s_shift (1 : R)).
  apply: measurableT_comp; first exact: R_to_carrier_meas.
  apply: measurable_funD; first exact: measurable_cst.
  exact: (carrier_to_R_meas R_carrier_meas).
have mpre : measurable ((s_shift (1 : R)) @^-1` U).
  have H := ms measurableT _ mU.
  by rewrite setTI in H.
rewrite (dirac_fmeas_E (gpt k) mpre).
rewrite (dirac_fmeas_E (gpt k.+1) mU).
rewrite !diracE.
congr (_%:R)%:E; congr (nat_of_bool _).
by congr (_ \in U); rewrite /preimage/= R_to_carrierK -natr1 addrC.
Qed.

(** Per-[U] iterate recurrence: the measure refinement of [g_val_S].
    The THEN branch contributes [(1/2) δ_0]; the ELSE branch the
    previous iterate pushed forward by [+1]. *)
Lemma g_iter_U_S n (U : set (ar_carrier Ar R_obj)) (mU : measurable U) :
  fmeas_mu (g_iter n.+1) U =
  (1 / 2)%:E * fmeas_mu (dirac_fmeas (gpt 0%N)) U
  + (1 / 2)%:E * fmeas_mu (g_iter n) ((s_shift (1 : R)) @^-1` U).
Proof.
rewrite g_step.
have -> : (bool_case (bernoulli (Ar:=Ar) (1 / 2 : R) (bernoulli_half_ge0 R)
               (bernoulli_half_le1 R))
    (dirac_fmeas (R_to_carrier R_carrier_eq 0%R))
    (Lfun (@add_lift R Ar R_obj R_carrier_eq R_carrier_meas
             R_to_carrier_meas)
       (dirac_fmeas (R_to_carrier R_carrier_eq 1%R) ⊗p g_iter n))
    : fmeas R (ar_carrier Ar R_obj)) =
  fmeas_add
    (fmeas_scale (NngNum (bernoulli_half_ge0 R))
       (dirac_fmeas (R_to_carrier R_carrier_eq 0%R)))
    (fmeas_scale (NngNum (subr_ge0_le1 (1 / 2 : R) (bernoulli_half_le1 R)))
       (Lfun (@add_lift R Ar R_obj R_carrier_eq R_carrier_meas
                R_to_carrier_meas)
          (dirac_fmeas (R_to_carrier R_carrier_eq 1%R) ⊗p g_iter n))).
  by [].
rewrite fmeas_addE 2!fmeas_scaleE/=.
rewrite (add_lift_dirac_U 1%R (g_iter n) mU).
have -> : ((1 - 1 / 2)%R : R) = (1 / 2)%R
  by rewrite {1}(splitr (1 : R)) addrK.
have -> : (gpt 0%N) = R_to_carrier R_carrier_eq 0%R by rewrite mulr0n.
by [].
Qed.

(** Closed form: the [n]-th iterate is the truncated geometric law. *)
Lemma g_iter_closed n (U : set (ar_carrier Ar R_obj)) (mU : measurable U) :
  fmeas_mu (g_iter n) U =
  \sum_(k < n) geom_w k * fmeas_mu (dirac_fmeas (gpt k)) U.
Proof.
elim: n U mU => [ | n IH] U mU.
  rewrite big_ord0.
  have -> : (g_iter 0 : fmeas R (ar_carrier Ar R_obj)) = fmeas_zero
    by rewrite g_iter_0.
  by rewrite fmeas_zeroE.
have ms : measurable_fun [set: ar_carrier Ar R_obj] (s_shift (1 : R)).
  apply: measurableT_comp; first exact: R_to_carrier_meas.
  apply: measurable_funD; first exact: measurable_cst.
  exact: (carrier_to_R_meas R_carrier_meas).
have mpre : measurable ((s_shift (1 : R)) @^-1` U).
  have H := ms measurableT _ mU.
  by rewrite setTI in H.
rewrite (g_iter_U_S n mU) (IH _ mpre).
rewrite big_ord_recl/= expr1 mulr0n; congr (_ + _).
under [RHS]eq_bigr => i _ do rewrite /bump/= add1n.
rewrite ge0_sume_distrr; last first.
  move=> i _.
  by rewrite mule_ge0// ?lee_fin ?exprn_ge0// ?divr_ge0// measure_ge0.
apply: eq_bigr => i _.
by rewrite (g_shift_atom i mU) muleA -EFinM -exprS.
Qed.

(** The geometric series limit: the partial sums of the geometric
    weights converge to the full ereal series. *)
Lemma g_iter_series_cvg (U : set (ar_carrier Ar R_obj))
    (mU : measurable U) :
  fmeas_mu (g_iter n) U @[n --> \oo] -->
    \sum_(k <oo) geom_w k * fmeas_mu (dirac_fmeas (gpt k)) U.
Proof.
have HE : (fun n => fmeas_mu (g_iter n) U) =
          (fun n => \sum_(0 <= k < n)
             geom_w k * fmeas_mu (dirac_fmeas (gpt k)) U).
  by apply/funext => n; rewrite big_mkord; exact: g_iter_closed.
rewrite HE.
apply: (is_cvg_nneseries (N := 0%N)) => k _ _.
by rewrite mule_ge0// ?measure_ge0// lee_fin exprn_ge0// divr_ge0.
Qed.

(** The distribution identity: the CBV denotation of [ex_geom]
    evaluates on every measurable [U] as the geometric series
    [Σ_k (1/2)^(k+1) δ_k(U)]. *)
Theorem ex_geom_cbv_distribution (U : set (ar_carrier Ar R_obj))
    (mU : measurable U) :
  fmeas_mu g_denot U =
  \sum_(k <oo) geom_w k * fmeas_mu (dirac_fmeas (gpt k)) U.
Proof.
rewrite ex_geom_sup_E.
apply: (fmeas_kleene_sup_U_E g_iter_chain g_iter_ball mU).
exact: g_iter_series_cvg.
Qed.

(** The atoms are distinct: [gpt] is injective, since [R_to_carrier]
    has the left inverse [carrier_to_R] and [_%:R] is injective on
    [nat]. *)
Lemma gpt_inj : injective (fun k : nat => gpt k).
Proof.
move=> i j /(congr1 (carrier_to_R R_carrier_eq)).
rewrite !R_to_carrierK => Hij.
by apply/eqP; rewrite -(eqr_nat R) Hij eqxx.
Qed.

(** The embedded atom set is measurable: it is the [carrier_to_R]
    preimage of the (measurable) real singleton [{k%:R}]. *)
Lemma measurable_gpt (k : nat) : measurable [set gpt k].
Proof.
have -> : [set gpt k] = carrier_to_R R_carrier_eq @^-1` [set (k%:R : R)].
  apply/seteqP; split=> c.
    by move=> ->; rewrite /preimage/= R_to_carrierK.
  rewrite /preimage/= => Hc.
  by rewrite -(carrier_to_RK R_carrier_eq c) Hc.
have m1 : measurable [set (k%:R : R)] by rewrite -set_itv1.
rewrite -[X in measurable X]setTI.
exact: (carrier_to_R_meas R_carrier_meas measurableT m1).
Qed.

(** The probability mass function: the denotation assigns mass exactly
    [(1/2)^(k+1)] to each embedded natural [k]. *)
Theorem ex_geom_cbv_pmf (k : nat) :
  fmeas_mu g_denot [set gpt k] = ((1 / 2 : R) ^+ k.+1)%:E.
Proof.
have mpt : measurable [set gpt k] by exact: measurable_gpt.
have hge0 : forall j : nat,
    0 <= geom_w j * fmeas_mu (dirac_fmeas (gpt j)) [set gpt k].
  move=> j.
  by rewrite mule_ge0// ?measure_ge0// lee_fin exprn_ge0// divr_ge0.
rewrite (ex_geom_cbv_distribution mpt).
rewrite (nneseriesD1 (n := k) (P := xpredT) (fun j _ => hge0 j) isT).
have -> : geom_w k * fmeas_mu (dirac_fmeas (gpt k)) [set gpt k]
        = ((1 / 2 : R) ^+ k.+1)%:E.
  rewrite (dirac_fmeas_E _ mpt) diracE/= mem_set// mulr1n mule1//.
rewrite [X in _ + X](_ : _ = 0) ?adde0//.
apply: (eseries0 (N := 0%N)) => j _; rewrite andTb => Hjk.
rewrite (dirac_fmeas_E _ mpt) diracE/=.
have -> : (gpt j \in [set gpt k]) = false.
  apply: memNset => /= /gpt_inj Heq.
  by rewrite Heq eqxx in Hjk.
by rewrite mulr0n mule0.
Qed.

End GeomRider.

(** ** §4 — Rider: [ex_even_odd] — the mutual-recursion witness diverges

    The [fix_mr] pair
    [[
       fix_mr p : (1→1) × (1→1) in (λn. snd p n, λn. fst p n)
    ]]
    is delegation-only: each component immediately calls the other,
    with no base case.  The zero-seeded Kleene chain of the conjugated
    body therefore stays at the cone-zero forever, so the fixpoint
    VALUE at the base cone [free_base pair_ty = (1⊸1) & (1⊸1)] is the
    cone-zero.  The pair denotation is the backward image of the
    PROMOTED zero ([0! ⊗ 0!], the pair of promoted-zero functions —
    itself never the cone-zero, by [eD_fix_mr_prod_at_setlike_neq0]),
    but each projection applied to the unit argument [()] runs the
    promoted-zero function and lands in the cone-zero of the unit cone:
    [ex_even @ ()] and [ex_odd @ ()] have mass [0]. *)

Section ExEvenOddRider.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '!'" := (prom x) (at level 2, format "x '!'").
Local Notation eD_cbv' :=
  (@eD_cbv R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation eD' :=
  (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation L := (linhom_car Ar (coalg_obj (tyD_cbv (@tunit R Ar)))
                                    (coalg_obj (tyD_cbv (@tunit R Ar)))).
Local Notation pair_ty :=
  (tprod (tfun (@tunit R Ar) tunit) (tfun tunit tunit)).

Let Hone : cone_norm (one1 : cone_one_car Ar) <= 1.
Proof. by rewrite one1_norm. Qed.

(** *** A morphism out of the one-dimensional unit cone is determined
    by its value at the unit point *)

(** Every point of [cone_one_car Ar] is a scalar multiple of [one1]. *)
Lemma cone_one_scale_rep (x : cone_one_car Ar) :
  x = precone_scale (c1_val x) (one1 : cone_one_car Ar).
Proof. by apply: cone_one_eq; apply: val_inj => /=; rewrite mulr1. Qed.

(** A linhom from [cone_one_car Ar] that vanishes at [one1] is the
    zero linhom: [cone_one_car] is one-dimensional, so a linear map is
    pinned by its value at [one1]. *)
Lemma linhom_cone_one_zero (D : ICone.type Ar)
    (f : linhom_car Ar (cone_one_car Ar) D) :
  linhom_fun f one1 = precone_zero -> f = precone_zero.
Proof.
move=> Hf; apply: linhom_eq => x; rewrite linhom_fun_zero.
have [_ _ HZ] := linhom_pre_linear (linhom_pre_of f).
rewrite [in LHS](cone_one_scale_rep x).
rewrite -[linhom_fun f (c1_val x *: one1)%PC]/(f (c1_val x *: one1)%PC) HZ.
by rewrite -[f one1]/(linhom_fun f one1) Hf precone_scale_0r.
Qed.

(** *** The conjugated body and its zero-seeded Kleene chain *)

(** The decomposition iso [tyD_cbv pair_ty ≅ !̃((1⊸1) & (1⊸1))]. *)
Local Notation eo_iso := (free_decomp pair_ty erefl).
Local Notation eo_bwd := (ch_mor (ci_bwd eo_iso)).
Local Notation eo_fwd := (ch_mor (ci_fwd eo_iso)).

(** The body of the [fix_mr], conjugated by the decomposition iso —
    the endofunction whose value-fixpoint is taken at the base cone. *)
Definition eo_W0 :
    linhom_car Ar (Bang Ar (sprod L L)) (Bang Ar (sprod L L)) :=
  linhom_map_fun eo_bwd eo_fwd
    (Lfun (tensor_curry (eD_cbv' (ex_even_odd_body : @named_expr R Ar R_obj _ _)))
          one1).

Lemma eo_W0_ball : cone_norm eo_W0 <= 1.
Proof.
apply: le_trans (linhom_map_norm_le1 _ _ _) _.
exact: le_trans (cones_hom_norm_le1 _ _) Hone.
Qed.

(** The pairing of the two cone-zeros is the cone-zero of the product
    cone (componentwise). *)
Lemma sprod_pair_zero :
  sprod_pair (precone_zero : L) (precone_zero : L) = precone_zero.
Proof. by apply: cones_prod_eq => -[]. Qed.

(** The decomposition iso, forward, sends the pair of promoted zeros to
    the promoted product zero (the Seely-2 forward on pure tensors). *)
Let Hzero : cone_norm (precone_zero : L) <= 1.
Proof. by rewrite cone_norm0. Qed.

Lemma eo_fwd_tensor0 :
  Lfun eo_fwd ((precone_zero : L)! ⊗p (precone_zero : L)!) =
  (precone_zero : sprod L L)!.
Proof.
rewrite -[eo_fwd]/(icones_comp (ch_mor (ci_fwd (seely2_em_iso L L)))
  (ch_mor (ci_fwd (coalg_iso_prod
     (coalg_iso_id (tyD_cbv (tfun (@tunit R Ar) tunit)))
     (coalg_iso_id (tyD_cbv (tfun (@tunit R Ar) tunit))))))).
rewrite Lfun_comp tensor_morE.
rewrite -[ch_mor (ci_fwd (coalg_iso_id (tyD_cbv (tfun (@tunit R Ar) tunit))))]
        /(icones_id Ar (coalg_obj (tyD_cbv (tfun (@tunit R Ar) tunit)))).
rewrite !icones_idE.
rewrite -[ch_mor (ci_fwd (seely2_em_iso L L))]/(iso_fwd (Seely2 L L)).
by rewrite (Seely2E (precone_zero : L) (precone_zero : L) Hzero Hzero)
   sprod_pair_zero.
Qed.

(** The decomposition iso, backward, sends the promoted product zero to
    the pair of promoted zeros (inverse of [eo_fwd_tensor0]). *)
Lemma eo_bwd_prom0 :
  Lfun eo_bwd ((precone_zero : sprod L L)!) =
  (precone_zero : L)! ⊗p (precone_zero : L)!.
Proof.
have Hcan : forall x, Lfun eo_bwd (Lfun eo_fwd x) = x.
  move=> x.
  rewrite -[Lfun eo_bwd (Lfun eo_fwd x)]/(Lfun (icones_comp eo_bwd eo_fwd) x).
  by rewrite (ci_fwdK eo_iso) icones_idE.
by rewrite -eo_fwd_tensor0; exact: Hcan.
Qed.

(** The body environment [one1 ⊗ (0! ⊗ 0!)] is a setlike unit-ball
    point: the rec-bound pair value is the pair of promoted zeros. *)
Lemma eo_env_ball :
  cone_norm (one1 ⊗p ((precone_zero : L)! ⊗p (precone_zero : L)!)) <= 1.
Proof.
rewrite tensor_normME one1_norm mul1r tensor_normME.
by apply: mulr_ile1; rewrite ?cone_norm_ge0// (prom_ball Hzero).
Qed.

(** Each promoted-zero function component is setlike in the cofree
    coalgebra [tyD_cbv (1→1)]. *)
Lemma eo_comp_setlike :
  Lfun (coalg_str (tyD_cbv (tfun (@tunit R Ar) tunit))) ((precone_zero : L)!) =
  ((precone_zero : L)!)!.
Proof.
rewrite -[tyD_cbv (tfun (@tunit R Ar) tunit)]/(bang_cofree L) bang_cofree_str.
exact: (dig_prom _ Hzero).
Qed.

Lemma eo_pair_ball :
  cone_norm ((precone_zero : L)! ⊗p (precone_zero : L)!) <= 1.
Proof.
by rewrite tensor_normME; apply: mulr_ile1; rewrite ?cone_norm_ge0// (prom_ball Hzero).
Qed.

(** The pair of promoted zeros is setlike in [tyD_cbv pair_ty]. *)
Lemma eo_pair_setlike :
  Lfun (coalg_str (tyD_cbv pair_ty))
       ((precone_zero : L)! ⊗p (precone_zero : L)!) =
  ((precone_zero : L)! ⊗p (precone_zero : L)!)!.
Proof.
rewrite -[tyD_cbv pair_ty]/(EM_prod (tyD_cbv (tfun (@tunit R Ar) tunit))
                                    (tyD_cbv (tfun (@tunit R Ar) tunit))).
exact: (coalg_str_tensor_setlike (P:=tyD_cbv (tfun (@tunit R Ar) tunit))
          (Q:=tyD_cbv (tfun (@tunit R Ar) tunit))
          (prom_ball Hzero) (prom_ball Hzero) eo_comp_setlike eo_comp_setlike).
Qed.

Lemma eo_env_setlike :
  Lfun (coalg_str (ctxD_cbv (drop_names ((("p"%string, pair_ty) :: nil)))))
       (one1 ⊗p ((precone_zero : L)! ⊗p (precone_zero : L)!)) =
  (one1 ⊗p ((precone_zero : L)! ⊗p (precone_zero : L)!))!.
Proof.
rewrite -[ctxD_cbv (drop_names [:: ("p"%string, pair_ty)])]
        /(EM_prod EM_term (tyD_cbv pair_ty)).
exact: (coalg_str_tensor_setlike (P:=EM_term) (Q:=tyD_cbv pair_ty)
          Hone eo_pair_ball coalg_str_one1 eo_pair_setlike).
Qed.

(** *** The two components evaluate to the promoted-zero function

    The body environment is [one1 ⊗ (0! ⊗ 0!)]; each component lambda
    is [λn. snd/fst p n], whose curried body is the cone-zero map: it
    looks up the [0!] component of [p], runs [der 0! = 0], the zero
    linhom, on the unit argument. *)

Lemma eo_lam_a_zero :
  Lfun (eD_cbv' (ex_even_odd_lam_a : @named_expr R Ar R_obj _ _))
       (one1 ⊗p ((precone_zero : L)! ⊗p (precone_zero : L)!)) =
  (precone_zero : L)!.
Proof.
rewrite /ex_even_odd_lam_a eD_lam_E.
set g := (tensor_curry _).
rewrite (adj_psi_at_setlike g eo_env_ball eo_env_setlike).
congr (prom _); rewrite /g.
apply: linhom_cone_one_zero; rewrite tensor_curryE.
have Hext_ball :
  cone_norm ((one1 ⊗p ((precone_zero : L)! ⊗p (precone_zero : L)!)) ⊗p one1)
    <= 1.
  by rewrite tensor_normME one1_norm mulr1 eo_env_ball.
have Hext_s :
  Lfun (coalg_str (ctxD_cbv (drop_names
          [:: ("n"%string, @tunit R Ar); ("p"%string, pair_ty)])))
       ((one1 ⊗p ((precone_zero : L)! ⊗p (precone_zero : L)!)) ⊗p one1) =
  ((one1 ⊗p ((precone_zero : L)! ⊗p (precone_zero : L)!)) ⊗p one1)!.
  rewrite -[ctxD_cbv (drop_names
            [:: ("n"%string, @tunit R Ar); ("p"%string, pair_ty)])]
          /(EM_prod (ctxD_cbv (drop_names [:: ("p"%string, pair_ty)]))
                    (tyD_cbv (@tunit R Ar))).
  exact: (coalg_str_tensor_setlike
            (P:=ctxD_cbv (drop_names [:: ("p"%string, pair_ty)]))
            (Q:=tyD_cbv (@tunit R Ar))
            eo_env_ball Hone eo_env_setlike coalg_str_one1).
rewrite (eD_app_at_setlike
           (G := [:: ("n"%string, @tunit R Ar); ("p"%string, pair_ty)])
           (t1 := tunit) (t2 := tunit)
           R_carrier_eq R_carrier_meas R_to_carrier_meas Hext_ball Hext_s).
have Hp_E :
  Lfun (eD_cbv' ([# "p"] : @named_expr R Ar R_obj
          [:: ("n"%string, @tunit R Ar); ("p"%string, pair_ty)] pair_ty))
       ((one1 ⊗p ((precone_zero : L)! ⊗p (precone_zero : L)!)) ⊗p one1) =
  (precone_zero : L)! ⊗p (precone_zero : L)!.
  apply: (eq_trans (y := Lfun (icones_comp
    (em_proj2_mor (R:=R) EM_term (tyD_cbv pair_ty))
    (em_proj1_mor (R:=R) (ctxD_cbv (drop_names [:: ("p"%string, pair_ty)]))
       (tyD_cbv (@tunit R Ar))))
    ((one1 ⊗p ((precone_zero : L)! ⊗p (precone_zero : L)!)) ⊗p one1))).
    by [].
  rewrite Lfun_comp.
  rewrite (em_proj1_morE (Q:=tyD_cbv (@tunit R Ar)) Hone coalg_str_one1).
  exact: (em_proj2_morE (P:=EM_term) Hone coalg_str_one1).
have Hsnd_E :
  Lfun (eD_cbv' ([snd # "p"] : @named_expr R Ar R_obj
          [:: ("n"%string, @tunit R Ar); ("p"%string, pair_ty)]
          (tfun (@tunit R Ar) tunit)))
       ((one1 ⊗p ((precone_zero : L)! ⊗p (precone_zero : L)!)) ⊗p one1) =
  (precone_zero : L)!.
  rewrite eD_snd_E Lfun_comp Hp_E.
  exact: (em_proj2_morE (P:=tyD_cbv (tfun (@tunit R Ar) tunit))
            (prom_ball Hzero) eo_comp_setlike).
rewrite Hsnd_E (der_prom _ Hzero).
exact: linhom_fun_zero.
Qed.

Lemma eo_lam_b_zero :
  Lfun (eD_cbv' (ex_even_odd_lam_b : @named_expr R Ar R_obj _ _))
       (one1 ⊗p ((precone_zero : L)! ⊗p (precone_zero : L)!)) =
  (precone_zero : L)!.
Proof.
rewrite /ex_even_odd_lam_b eD_lam_E.
set g := (tensor_curry _).
rewrite (adj_psi_at_setlike g eo_env_ball eo_env_setlike).
congr (prom _); rewrite /g.
apply: linhom_cone_one_zero; rewrite tensor_curryE.
have Hext_ball :
  cone_norm ((one1 ⊗p ((precone_zero : L)! ⊗p (precone_zero : L)!)) ⊗p one1)
    <= 1.
  by rewrite tensor_normME one1_norm mulr1 eo_env_ball.
have Hext_s :
  Lfun (coalg_str (ctxD_cbv (drop_names
          [:: ("n"%string, @tunit R Ar); ("p"%string, pair_ty)])))
       ((one1 ⊗p ((precone_zero : L)! ⊗p (precone_zero : L)!)) ⊗p one1) =
  ((one1 ⊗p ((precone_zero : L)! ⊗p (precone_zero : L)!)) ⊗p one1)!.
  rewrite -[ctxD_cbv (drop_names
            [:: ("n"%string, @tunit R Ar); ("p"%string, pair_ty)])]
          /(EM_prod (ctxD_cbv (drop_names [:: ("p"%string, pair_ty)]))
                    (tyD_cbv (@tunit R Ar))).
  exact: (coalg_str_tensor_setlike
            (P:=ctxD_cbv (drop_names [:: ("p"%string, pair_ty)]))
            (Q:=tyD_cbv (@tunit R Ar))
            eo_env_ball Hone eo_env_setlike coalg_str_one1).
rewrite (eD_app_at_setlike
           (G := [:: ("n"%string, @tunit R Ar); ("p"%string, pair_ty)])
           (t1 := tunit) (t2 := tunit)
           R_carrier_eq R_carrier_meas R_to_carrier_meas Hext_ball Hext_s).
have Hp_E :
  Lfun (eD_cbv' ([# "p"] : @named_expr R Ar R_obj
          [:: ("n"%string, @tunit R Ar); ("p"%string, pair_ty)] pair_ty))
       ((one1 ⊗p ((precone_zero : L)! ⊗p (precone_zero : L)!)) ⊗p one1) =
  (precone_zero : L)! ⊗p (precone_zero : L)!.
  apply: (eq_trans (y := Lfun (icones_comp
    (em_proj2_mor (R:=R) EM_term (tyD_cbv pair_ty))
    (em_proj1_mor (R:=R) (ctxD_cbv (drop_names [:: ("p"%string, pair_ty)]))
       (tyD_cbv (@tunit R Ar))))
    ((one1 ⊗p ((precone_zero : L)! ⊗p (precone_zero : L)!)) ⊗p one1))).
    by [].
  rewrite Lfun_comp.
  rewrite (em_proj1_morE (Q:=tyD_cbv (@tunit R Ar)) Hone coalg_str_one1).
  exact: (em_proj2_morE (P:=EM_term) Hone coalg_str_one1).
have Hfst_E :
  Lfun (eD_cbv' ([fst # "p"] : @named_expr R Ar R_obj
          [:: ("n"%string, @tunit R Ar); ("p"%string, pair_ty)]
          (tfun (@tunit R Ar) tunit)))
       ((one1 ⊗p ((precone_zero : L)! ⊗p (precone_zero : L)!)) ⊗p one1) =
  (precone_zero : L)!.
  rewrite eD_fst_E Lfun_comp Hp_E.
  exact: (em_proj1_morE (Q:=tyD_cbv (tfun (@tunit R Ar) tunit))
            (prom_ball Hzero) eo_comp_setlike).
rewrite Hfst_E (der_prom _ Hzero).
exact: linhom_fun_zero.
Qed.

(** *** The decisive fixpoint step: the conjugated body fixes the
    promoted product zero *)

(** The (un-conjugated) body, applied to the pair of promoted zeros,
    returns it unchanged: the two components are independently the
    promoted-zero function. *)
Lemma eo_body_tensor0 :
  linhom_fun
    (Lfun (tensor_curry
       (eD_cbv' (ex_even_odd_body : @named_expr R Ar R_obj _ _))) one1)
    ((precone_zero : L)! ⊗p (precone_zero : L)!) =
  (precone_zero : L)! ⊗p (precone_zero : L)!.
Proof.
rewrite tensor_curryE /ex_even_odd_body eD_pair_E.
rewrite /em_pair_mor Lfun_comp
  (coalg_d_setlike (P:=ctxD_cbv (drop_names [:: ("p"%string, pair_ty)]))
     eo_env_ball eo_env_setlike) tensor_morE.
by congr (_ ⊗p _); [exact: eo_lam_a_zero | exact: eo_lam_b_zero].
Qed.

(** The conjugated body fixes the promoted product zero. *)
Lemma eo_W0_prom0 :
  linhom_fun eo_W0 ((precone_zero : sprod L L)!) =
  (precone_zero : sprod L L)!.
Proof.
rewrite /eo_W0 linhom_map_funE eo_bwd_prom0 eo_body_tensor0.
exact: eo_fwd_tensor0.
Qed.

(** *** The zero-seeded Kleene chain and the fixpoint value *)

(** Every iterate of the interleaved chain is the cone-zero: the seed
    is [0], and [eo_W0_prom0] keeps the step at [der 0! = 0]. *)
Lemma even_odd_iter_zero n : fix_chain eo_W0 n = precone_zero.
Proof.
elim: n => [ | n IH]; first exact: fix_chain_0.
rewrite fix_chain_S IH eo_W0_prom0.
by rewrite (der_prom (precone_zero : sprod L L)) // cone_norm0.
Qed.

(** Hence the fixpoint value at the base cone is the cone-zero. *)
Lemma ex_even_odd_fix_value_zero :
  sc_fun (fix_value (free_base pair_ty)) eo_W0 = precone_zero.
Proof.
rewrite (fix_value_E eo_W0_ball).
apply: precone_le_anti.
- by apply: cone_sup_ball_lub => n; rewrite even_odd_iter_zero; exact: precone_le_refl.
- exact: precone_le0.
Qed.

(** *** The pair denotation and the two projection runs *)

(** The closed pair denotation is the backward image of the promoted
    base-cone zero, i.e. the pair of promoted-zero functions [0! ⊗ 0!].
    (It is NOT the cone-zero — see [eD_fix_mr_prod_at_setlike_neq0]; the
    divergence shows up only after projecting and applying.) *)
Lemma ex_even_odd_pair_cbv_value :
  Lfun (eD_cbv' (ex_even_odd_pair : @named_expr R Ar R_obj nil pair_ty))
       one1 =
  (precone_zero : L)! ⊗p (precone_zero : L)!.
Proof.
rewrite -[ex_even_odd_pair]/(ne_fix_mr "p" pair_ty erefl
  (ex_even_odd_body : @named_expr R Ar R_obj _ _)).
rewrite (eD_fix_mr_prod_at_setlike "p" (erefl : is_free_coalg_type pair_ty)
  (ex_even_odd_body : @named_expr R Ar R_obj _ _) Hone coalg_str_one1).
rewrite -/eo_W0 ex_even_odd_fix_value_zero.
exact: eo_bwd_prom0.
Qed.

(** The first projection at the unit argument: [ex_even @ ()] denotes
    the cone-zero of the unit cone (mass [0]). *)
Definition ex_even_run :
    @named_expr R Ar R_obj nil (@tunit R Ar) :=
  ne_app (ex_even : @named_expr R Ar R_obj nil (tfun tunit tunit)) ne_tt.

Definition ex_odd_run :
    @named_expr R Ar R_obj nil (@tunit R Ar) :=
  ne_app (ex_odd : @named_expr R Ar R_obj nil (tfun tunit tunit)) ne_tt.

(** [ex_even = fst pair] evaluates to the promoted-zero function. *)
Lemma ex_even_cbv_fun_zero :
  Lfun (eD_cbv' (ex_even : @named_expr R Ar R_obj nil (tfun tunit tunit)))
       one1 = (precone_zero : L)!.
Proof.
rewrite -[ex_even]/(ne_fst (ex_even_odd_pair : @named_expr R Ar R_obj _ _)).
rewrite eD_fst_E Lfun_comp ex_even_odd_pair_cbv_value.
exact: (em_proj1_morE (Q:=tyD_cbv (tfun (@tunit R Ar) tunit))
          (prom_ball Hzero) eo_comp_setlike).
Qed.

(** [ex_odd = snd pair] evaluates to the promoted-zero function. *)
Lemma ex_odd_cbv_fun_zero :
  Lfun (eD_cbv' (ex_odd : @named_expr R Ar R_obj nil (tfun tunit tunit)))
       one1 = (precone_zero : L)!.
Proof.
rewrite -[ex_odd]/(ne_snd (ex_even_odd_pair : @named_expr R Ar R_obj _ _)).
rewrite eD_snd_E Lfun_comp ex_even_odd_pair_cbv_value.
exact: (em_proj2_morE (P:=tyD_cbv (tfun (@tunit R Ar) tunit))
          (prom_ball Hzero) eo_comp_setlike).
Qed.

(** The even component diverges: [ex_even @ ()] has mass [0]. *)
Theorem ex_even_cbv_diverges :
  Lfun (eD_cbv' ex_even_run) one1 = precone_zero.
Proof.
rewrite /ex_even_run.
rewrite (eD_app_at_setlike (G := nil) (t1 := @tunit R Ar) (t2 := tunit)
           R_carrier_eq R_carrier_meas R_to_carrier_meas Hone coalg_str_one1).
rewrite ex_even_cbv_fun_zero (der_prom _ Hzero).
exact: linhom_fun_zero.
Qed.

(** The odd component diverges: [ex_odd @ ()] has mass [0]. *)
Theorem ex_odd_cbv_diverges :
  Lfun (eD_cbv' ex_odd_run) one1 = precone_zero.
Proof.
rewrite /ex_odd_run.
rewrite (eD_app_at_setlike (G := nil) (t1 := @tunit R Ar) (t2 := tunit)
           R_carrier_eq R_carrier_meas R_to_carrier_meas Hone coalg_str_one1).
rewrite ex_odd_cbv_fun_zero (der_prom _ Hzero).
exact: linhom_fun_zero.
Qed.

End ExEvenOddRider.
