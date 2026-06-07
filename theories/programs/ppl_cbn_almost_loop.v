(**md*** BEYOND THE PAPER — CBN PPL [ex_almost_loop p] mass closure

    THE HEADLINES.  [ex_almost_loop_p_CBN_mass_one_if_pos] (when
    [p > 0]) and [ex_almost_loop_p_CBN_mass_zero_if_zero] (when
    [p = 0]): the CBN-side fixpoint of the parameterised partial-
    termination operator [phi_almost_loop_p] has the expected mass.

    ** Strategy

    Direct lift of [theories/programs/ppl_cbn_geom.v]'s [phi_CBN_geom]
    Kleene cascade, with two adjustments:

    - The Bernoulli scrutinee becomes the [p]-parameter Bernoulli
      (instead of [1/2]).
    - The ELSE branch becomes the IDENTITY on [FMeas R_obj] (instead
      of [shift_lift 1]): the recursive call [l ()] returns the
      recursive value DIRECTLY, with no [+ δ_1] postprocessing.

    The per-iterate decomposition becomes
    [[
       phi_almost_loop_p μ
         = if Bernoulli(p) then δ_0 else μ
         = p *: δ_0 + (1 - p) *: μ.
    ]]
    Hence [mass(kleene^n) = 1 - (1 - p)^n].

    - When [p > 0]: [(1 - p) < 1], so [(1 - p)^n → 0] and
      [mass → 1].
    - When [p = 0]: [(1 - p)^n = 1] for all [n], so
      [mass = 0] uniformly.

    ** Author

    Guillaume Baudart <guillaume.baudart@inria.fr>. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals signed constructive_ereal.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import measure dirac_measure.
From mathcomp.analysis Require Import sequences ereal normedtype topology.

From Stdlib Require Import Strings.String.

Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.cone_cat.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.mcones.path.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_cat.
Require Import Icones.homs.linhom.
Require Import Icones.homs.bilin.
Require Import Icones.homs.coalgebra.
Require Import Icones.homs.seely_defs.
Require Import Icones.homs.seely.
Require Import Icones.programs.infra.bool_cone.
Require Import Icones.stable.totmono.
Require Import Icones.stable.stablehom.
Require Import Icones.stable.scones_cat.
Require Import Icones.stable.fixpoint.
Require Import Icones.stable.scones_ccc.
Require Import Icones.programs.infra.bool_case_hom.
Require Import Icones.programs.infra.bool_case_scones.
Require Import Icones.programs.ppl.
Require Import Icones.programs.examples.
Require Import Icones.programs.ppl_cbn.
Require Import Icones.programs.ppl_cbn_eff.
Require Import Icones.programs.ppl_cbn_bool.
Require Import Icones.programs.ppl_cbn_arith.
Require Import Icones.programs.ppl_cbn_headlines.
Require Import Icones.programs.ppl_cbn_geom.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** §1 — The [p]-parameterised [phi_almost_loop_p] operator

    Mirrors [phi_CBN_geom] of [ppl_cbn_geom.v], but parameterised by
    a continuation probability [p] (and its bounds), with the ELSE
    branch replaced by the identity on [FMeas R_obj]. *)

Section PhiAlmostLoopP.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.

Variable (p : R).
Hypothesis Hp_ge0 : (0 <= p)%R.
Hypothesis Hp_le1 : (p <= 1)%R.

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

(** *** Bernoulli scrutinee — constant Bernoulli([p]). *)
Definition bern_branch_p : scones_hom (FMeas R_obj) (bool_cone_car Ar) :=
  scones_const (FMeas R_obj)
    (bernoulli p Hp_ge0 Hp_le1)
    (bernoulli_norm_le1 p Hp_ge0 Hp_le1).

Lemma bern_branch_p_E (mu : FMeas R_obj) :
  (cone_norm mu <= 1)%R ->
  sc_fun bern_branch_p mu = bernoulli p Hp_ge0 Hp_le1.
Proof.
move=> Hmu.
exact: (scones_const_E
          (bernoulli_norm_le1 p Hp_ge0 Hp_le1) mu Hmu).
Qed.

(** *** THEN branch — constant [δ_0]. *)
Definition then_branch_p : scones_hom (FMeas R_obj) (FMeas R_obj) :=
  scones_const (FMeas R_obj)
    (dirac_fmeas (R_to_carrier R_carrier_eq 0%R) : FMeas R_obj)
    (dirac_fmeas_norm_le1 (R_to_carrier R_carrier_eq 0%R)).

Lemma then_branch_p_E (mu : FMeas R_obj) :
  (cone_norm mu <= 1)%R ->
  sc_fun then_branch_p mu =
  dirac_fmeas (R_to_carrier R_carrier_eq 0%R).
Proof.
move=> Hmu.
exact: (scones_const_E
          (dirac_fmeas_norm_le1 (R_to_carrier R_carrier_eq 0%R)) mu Hmu).
Qed.

(** *** ELSE branch — identity (the recursive call returns its arg). *)
Definition else_branch_p : scones_hom (FMeas R_obj) (FMeas R_obj) :=
  scones_id (FMeas R_obj).

Lemma else_branch_p_E (mu : FMeas R_obj) :
  (cone_norm mu <= 1)%R ->
  sc_fun else_branch_p mu = mu.
Proof.
move=> Hmu.
by rewrite /else_branch_p /scones_id /= (sc_clamp_ball Hmu).
Qed.

(** *** Inline [if] combinator on [FMeas R_obj].  Direct lift of
       [phi_CBN_geom]'s §4 construction. *)

Local Notation Gc := (FMeas R_obj).
Local Notation A := (FMeas R_obj).
Local Notation B := (bool_cone_car Ar).
Local Notation Sh := (stablehom Gc A).

Lemma sc_to_sh_cone_norm_le1_FMeas_p (f : scones_hom Gc A) :
  (cone_norm (sc_to_sh f) <= 1)%R.
Proof.
rewrite -[cone_norm _]/(sh_norm (sc_to_sh f)).
apply: sh_norm_lub => x Hx.
exact: sc_image_ball.
Qed.

Definition phi_alp_if_linhom : linhom_car Ar B Sh :=
  bool_case_linhom (sc_to_sh then_branch_p) (sc_to_sh else_branch_p)
                   (sc_to_sh_cone_norm_le1_FMeas_p then_branch_p)
                   (sc_to_sh_cone_norm_le1_FMeas_p else_branch_p).

Lemma phi_alp_if_linhom_norm_le1 :
  (cone_norm phi_alp_if_linhom <= 1)%R.
Proof. exact: bool_case_linhom_norm_le1. Qed.

Definition phi_alp_if_scones_B_Sh : scones_hom B Sh :=
  ders (linhom_icones phi_alp_if_linhom phi_alp_if_linhom_norm_le1).

Definition phi_alp_if_scones_Gc_Sh : scones_hom Gc Sh :=
  scones_comp phi_alp_if_scones_B_Sh bern_branch_p.

Definition phi_almost_loop_p : scones_hom Gc A :=
  scones_comp (Ev Gc A) (spair phi_alp_if_scones_Gc_Sh (scones_id Gc)).

(** Pointwise reduction rule on the unit ball.  Mirrors
    [phi_CBN_geom_E]. *)
Lemma phi_almost_loop_p_E (mu : FMeas R_obj) :
  (cone_norm mu <= 1)%R ->
  sc_fun phi_almost_loop_p mu =
  @bool_case R Ar (FMeas R_obj)
    (bernoulli p Hp_ge0 Hp_le1)
    (dirac_fmeas (R_to_carrier R_carrier_eq 0%R))
    mu.
Proof.
move=> Hmu.
rewrite /phi_almost_loop_p.
rewrite (scomp_ball _ _ Hmu).
have Hpair : sc_fun (spair phi_alp_if_scones_Gc_Sh (scones_id Gc)) mu
           = sprod_pair (sc_fun phi_alp_if_scones_Gc_Sh mu)
                         (sc_fun (scones_id Gc) mu).
  exact: scpair_ball.
rewrite Hpair.
have Hid : sc_fun (scones_id Gc) mu = mu.
  by rewrite /scones_id /= (sc_clamp_ball Hmu).
rewrite Hid.
have Hinner :
    sc_fun phi_alp_if_scones_Gc_Sh mu =
    sc_fun phi_alp_if_scones_B_Sh (sc_fun bern_branch_p mu).
  by rewrite /phi_alp_if_scones_Gc_Sh (scomp_ball _ _ Hmu).
rewrite Hinner.
have Hbe : (cone_norm (sc_fun bern_branch_p mu) <= 1)%R
  by exact: sc_image_ball.
have HB : sc_fun phi_alp_if_scones_B_Sh (sc_fun bern_branch_p mu)
        = linhom_fun phi_alp_if_linhom (sc_fun bern_branch_p mu).
  rewrite /phi_alp_if_scones_B_Sh /ders /= (sc_clamp_ball Hbe).
  by rewrite /linhom_icones /=.
rewrite HB.
have HSh_ball :
  (cone_norm (linhom_fun phi_alp_if_linhom (sc_fun bern_branch_p mu)) <= 1)%R.
  have step :=
    linhom_norm_apply_le phi_alp_if_linhom_norm_le1
                          (sc_fun bern_branch_p mu).
  rewrite mul1r in step.
  exact: (le_trans step Hbe).
have Hpair_ball : (cone_norm (sprod_pair
    (linhom_fun phi_alp_if_linhom (sc_fun bern_branch_p mu)) mu) <= 1)%R.
  exact: sprod_pair_norm_le1.
rewrite (Ev_pair _ _ Hpair_ball).
have Hlin :
    linhom_fun phi_alp_if_linhom (sc_fun bern_branch_p mu) =
    bool_case (sc_fun bern_branch_p mu)
              (sc_to_sh then_branch_p) (sc_to_sh else_branch_p).
  by rewrite /phi_alp_if_linhom /=.
rewrite Hlin.
rewrite (bern_branch_p_E Hmu).
rewrite /bool_case /=.
rewrite /stm_add /stm_scale /sh_fun /=.
by rewrite !(sc_clamp_ball Hmu).
Qed.

End PhiAlmostLoopP.

Arguments bern_branch_p {R Ar R_obj} p Hp_ge0 Hp_le1.
Arguments then_branch_p {R Ar R_obj} R_carrier_eq.
Arguments else_branch_p {R Ar R_obj}.
Arguments phi_almost_loop_p {R Ar R_obj}
  R_carrier_eq p Hp_ge0 Hp_le1.
Arguments phi_almost_loop_p_E {R Ar R_obj}
  R_carrier_eq p Hp_ge0 Hp_le1 mu.

(** ** §2 — Kleene cascade for [phi_almost_loop_p] *)

Section KleeneCascadeP.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.

Variable (p : R).
Hypothesis Hp_ge0 : (0 <= p)%R.
Hypothesis Hp_le1 : (p <= 1)%R.

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

Local Notation phi_alp' :=
  (phi_almost_loop_p R_carrier_eq p Hp_ge0 Hp_le1).

Definition kleene_alp (n : nat) : FMeas R_obj :=
  kleene (sc_fun phi_alp') n.

Lemma kleene_alp_0 : kleene_alp 0 = (precone_zero : FMeas R_obj).
Proof. by rewrite /kleene_alp. Qed.

Lemma kleene_alp_S (n : nat) :
  kleene_alp n.+1 = sc_fun phi_alp' (kleene_alp n).
Proof. by rewrite /kleene_alp -kleeneS. Qed.

Lemma kleene_alp_ball (n : nat) :
  (cone_norm (kleene_alp n) <= 1)%R.
Proof.
elim: n => [ | n IH ].
- by rewrite kleene_alp_0 cone_norm0 ler01.
- rewrite kleene_alp_S; exact: sc_image_ball.
Qed.

(** Per-iterate decomposition.  On the unit ball,
    [kleene_alp (n+1) = p *: δ_0 + (1 - p) *: kleene_alp n]. *)
Lemma kleene_alp_S_E (n : nat) :
  kleene_alp n.+1 =
  (precone_add
    (precone_scale (NngNum Hp_ge0)
       (dirac_fmeas (R_to_carrier R_carrier_eq 0%R) : FMeas R_obj))
    (precone_scale (NngNum (onem_ge0 p Hp_le1))
       (kleene_alp n : FMeas R_obj)) : FMeas R_obj).
Proof.
rewrite kleene_alp_S.
rewrite (phi_almost_loop_p_E R_carrier_eq p Hp_ge0 Hp_le1
                              (kleene_alp n) (kleene_alp_ball n)).
by rewrite /bool_case /=.
Qed.

(** Mass recurrence:
    [mass(kleene^(n+1)) = p + (1 - p) · mass(kleene^n)]. *)
Local Open Scope ereal_scope.
Lemma kleene_alp_S_mass (n : nat) :
  fmeas_mu (kleene_alp n.+1) [set: ar_carrier Ar R_obj]
  = (p%:E + (1 - p)%R%:E *
     fmeas_mu (kleene_alp n) [set: ar_carrier Ar R_obj])%E.
Proof.
rewrite kleene_alp_S_E.
rewrite -[precone_add _ _]/(fmeas_add
   (precone_scale (NngNum Hp_ge0)
      (dirac_fmeas (R_to_carrier R_carrier_eq 0%R) : FMeas R_obj))
   (precone_scale (NngNum (onem_ge0 p Hp_le1))
      (kleene_alp n : FMeas R_obj))).
rewrite fmeas_addE.
rewrite -[precone_scale (NngNum Hp_ge0) (dirac_fmeas _)]
        /(fmeas_scale (NngNum Hp_ge0)
                      (dirac_fmeas (R_to_carrier R_carrier_eq 0%R) : FMeas R_obj)).
rewrite -[precone_scale (NngNum (onem_ge0 p Hp_le1)) (kleene_alp n : FMeas R_obj)]
        /(fmeas_scale (NngNum (onem_ge0 p Hp_le1)) (kleene_alp n : FMeas R_obj)).
rewrite !fmeas_scaleE.
by rewrite dirac_fmeas_setT_E mule1.
Qed.

(** Closed-form mass [mass(kleene^n) = 1 - (1 - p)^n]. *)
Lemma kleene_alp_mass_closed (n : nat) :
  fmeas_mu (kleene_alp n) [set: ar_carrier Ar R_obj]
  = (1 - (1 - p)^+n : R)%R%:E.
Proof.
elim: n => [ | n IH ].
- by rewrite kleene_alp_0 expr0 subrr fmeas_zeroE.
- rewrite kleene_alp_S_mass IH.
  rewrite -EFinM -EFinD.
  congr (_%:E).
  rewrite exprSr.
  rewrite [in LHS]mulrBr [in LHS]mulr1.
  rewrite addrA.
  have eq1 : (p + (1 - p) = 1)%R by rewrite addrCA subrr addr0.
  by rewrite eq1 mulrC.
Qed.

(** Mass convergence when [p > 0]: [mass(kleene^n) → 1]. *)
Lemma kleene_alp_mass_cvg_if_pos :
  (0 < p)%R ->
  fmeas_mu (kleene_alp n) [set: ar_carrier Ar R_obj]
    @[n --> \oo] --> (1 : \bar R).
Proof.
move=> Hp_pos.
under eq_fun => n do rewrite kleene_alp_mass_closed.
rewrite (_ : (1 : \bar R) = ((1 - 0)%R : R)%R%:E); last by rewrite subr0.
apply: cvg_EFin.
  by apply: nearW => n; rewrite //=.
apply: cvgB.
- exact: cvg_cst.
- apply: cvg_expr.
  (* |1 - p| < 1.  Since 0 <= 1-p <= 1 and p > 0, [1 - p < 1]. *)
  have H1mp_ge0 : (0 <= 1 - p)%R by exact: onem_ge0.
  rewrite ger0_norm //.
  by rewrite ltrBlDr -ltrBlDl subrr.
Qed.

(** Mass convergence when [p = 0]: [mass(kleene^n) = 0] for all [n]. *)
Lemma kleene_alp_mass_eq_zero_if_zero (n : nat) :
  p = 0%R ->
  fmeas_mu (kleene_alp n) [set: ar_carrier Ar R_obj] = 0%E.
Proof.
move=> Hp_zero.
rewrite kleene_alp_mass_closed.
rewrite Hp_zero subr0 expr1n subrr.
by [].
Qed.
Local Close Scope ereal_scope.

End KleeneCascadeP.

Arguments kleene_alp {R Ar R_obj}
  R_carrier_eq p Hp_ge0 Hp_le1 n.
Arguments kleene_alp_0 {R Ar R_obj}
  R_carrier_eq p Hp_ge0 Hp_le1.
Arguments kleene_alp_S {R Ar R_obj}
  R_carrier_eq p Hp_ge0 Hp_le1 n.
Arguments kleene_alp_ball {R Ar R_obj}
  R_carrier_eq p Hp_ge0 Hp_le1 n.
Arguments kleene_alp_S_E {R Ar R_obj}
  R_carrier_eq p Hp_ge0 Hp_le1 n.
Arguments kleene_alp_S_mass {R Ar R_obj}
  R_carrier_eq p Hp_ge0 Hp_le1 n.
Arguments kleene_alp_mass_closed {R Ar R_obj}
  R_carrier_eq p Hp_ge0 Hp_le1 n.
Arguments kleene_alp_mass_cvg_if_pos {R Ar R_obj}
  R_carrier_eq p Hp_ge0 Hp_le1.
Arguments kleene_alp_mass_eq_zero_if_zero {R Ar R_obj}
  R_carrier_eq p Hp_ge0 Hp_le1 n.

(** ** §3 — THE HEADLINES *)

Section ExAlmostLoopPCBNFixMass.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.

Variable (p : R).
Hypothesis Hp_ge0 : (0 <= p)%R.
Hypothesis Hp_le1 : (p <= 1)%R.

Local Notation phi_alp' :=
  (phi_almost_loop_p R_carrier_eq p Hp_ge0 Hp_le1).
Local Notation kleene_alp' :=
  (kleene_alp R_carrier_eq p Hp_ge0 Hp_le1).

Definition ex_almost_loop_p_CBN_fix : FMeas R_obj := sfix phi_alp'.

Local Open Scope ereal_scope.

(** *** Headline 1 — when [p > 0], the fixpoint has mass 1. *)
Theorem ex_almost_loop_p_CBN_mass_one_if_pos :
  (0 < p)%R ->
  fmeas_mu ex_almost_loop_p_CBN_fix [set: ar_carrier Ar R_obj] = 1%:E.
Proof.
move=> Hp_pos.
rewrite /ex_almost_loop_p_CBN_fix /sfix /lfp.
have HE :
  cone_sup_ball (kleene phi_alp')
                (kleene_chain (sc_incr phi_alp') (sc_ball_pres phi_alp'))
                (kleene_ball (sc_ball_pres phi_alp')) =
  fmeas_sup_ball
    (kleene_chain (sc_incr phi_alp') (sc_ball_pres phi_alp'))
    (kleene_ball (sc_ball_pres phi_alp'))
  by [].
rewrite HE.
rewrite (fmeas_sup_ballE _ _ measurableT).
have Hsupcvg : fmeas_mu (kleene phi_alp' n) [set: ar_carrier Ar R_obj]
                 @[n --> \oo]
                 --> fmeas_sup_meas_fun
                       (kleene_chain (sc_incr phi_alp')
                                     (sc_ball_pres phi_alp'))
                       [set: ar_carrier Ar R_obj].
  by apply: fmeas_sup_cvg; exact: measurableT.
have Hcvg1 :=
  kleene_alp_mass_cvg_if_pos R_carrier_eq p Hp_ge0 Hp_le1 Hp_pos.
have := @cvg_unique _ (@ereal_hausdorff R) _ _ _ _ Hsupcvg Hcvg1.
by move=> ->.
Qed.

(** *** Headline 2 — when [p = 0], the fixpoint has mass 0. *)
Theorem ex_almost_loop_p_CBN_mass_zero_if_zero :
  p = 0%R ->
  fmeas_mu ex_almost_loop_p_CBN_fix [set: ar_carrier Ar R_obj] = 0%E.
Proof.
move=> Hp_zero.
rewrite /ex_almost_loop_p_CBN_fix /sfix /lfp.
have HE :
  cone_sup_ball (kleene phi_alp')
                (kleene_chain (sc_incr phi_alp') (sc_ball_pres phi_alp'))
                (kleene_ball (sc_ball_pres phi_alp')) =
  fmeas_sup_ball
    (kleene_chain (sc_incr phi_alp') (sc_ball_pres phi_alp'))
    (kleene_ball (sc_ball_pres phi_alp'))
  by [].
rewrite HE.
rewrite (fmeas_sup_ballE _ _ measurableT).
(* The chain is the zero chain, so its sup is 0.  Equivalently,
   every iterate has mass 0; pass to the limit. *)
have Hsupcvg : fmeas_mu (kleene phi_alp' n) [set: ar_carrier Ar R_obj]
                 @[n --> \oo]
                 --> fmeas_sup_meas_fun
                       (kleene_chain (sc_incr phi_alp')
                                     (sc_ball_pres phi_alp'))
                       [set: ar_carrier Ar R_obj].
  by apply: fmeas_sup_cvg; exact: measurableT.
have Hzero_eq : forall n, fmeas_mu (kleene phi_alp' n)
                            [set: ar_carrier Ar R_obj] = 0%E.
  move=> n.
  exact: kleene_alp_mass_eq_zero_if_zero R_carrier_eq p Hp_ge0 Hp_le1 n Hp_zero.
have Hcvg0 : fmeas_mu (kleene phi_alp' n) [set: ar_carrier Ar R_obj]
               @[n --> \oo] --> (0 : \bar R).
  apply: cvg_near_cst.
  by apply: nearW => n; exact: Hzero_eq.
have := @cvg_unique _ (@ereal_hausdorff R) _ _ _ _ Hsupcvg Hcvg0.
by move=> ->.
Qed.
Local Close Scope ereal_scope.

End ExAlmostLoopPCBNFixMass.

Arguments ex_almost_loop_p_CBN_fix {R Ar R_obj}
  R_carrier_eq p Hp_ge0 Hp_le1.
Arguments ex_almost_loop_p_CBN_mass_one_if_pos {R Ar R_obj}
  R_carrier_eq p Hp_ge0 Hp_le1.
Arguments ex_almost_loop_p_CBN_mass_zero_if_zero {R Ar R_obj}
  R_carrier_eq p Hp_ge0 Hp_le1.
