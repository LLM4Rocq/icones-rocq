(**md*** BEYOND THE PAPER — CBN PPL Bernoulli-cascade framework

    Shared mathematical core of [ppl_cbn_geom.v] and
    [ppl_cbn_almost_loop.v].

    ** Operator scheme

    Given:
    - a Bernoulli parameter [p] with [0 <= p <= 1],
    - a "halt" value [halt : FMeas R_obj] in the unit ball whose
      total mass is [1] (typically a Dirac),
    - a continuation operator [cont_op : scones_hom (FMeas R_obj)
      (FMeas R_obj)] which preserves the total mass on the unit ball
      (i.e. [mass(cont_op μ) = mass μ] for [‖μ‖ ≤ 1]),

    the framework builds the [SCones] endomorphism
    [[
        phi_bcascade μ
          = if Bernoulli(p) then halt else cont_op μ
          = p *: halt + (1 - p) *: cont_op μ
    ]]
    and exposes:

    - [phi_bcascade : scones_hom (FMeas R_obj) (FMeas R_obj)],
    - [phi_bcascade_E] : pointwise reduction on the unit ball,
    - [kleene_bcascade n] : the Kleene chain at [precone_zero],
    - [kleene_bcascade_S_E] : the [precone_add]/[precone_scale]
      decomposition,
    - [kleene_bcascade_S_mass] : the recurrence [mass(k^{n+1}) =
      p + (1 - p) · mass(k^n)],
    - [kleene_bcascade_mass_closed] : the closed form
      [mass(k^n) = 1 - (1 - p)^n],
    - [kleene_bcascade_mass_cvg_if_pos] : convergence to [1] when
      [p > 0],
    - [kleene_bcascade_mass_eq_zero_if_zero] : per-iterate
      vanishing when [p = 0],
    - [sfix_bcascade_mass_one_if_pos] /
      [sfix_bcascade_mass_zero_if_zero] : the [sfix] headlines.

    Instantiate at [p := 1/2], [halt := δ_0], [cont_op := shift_scones 1]
    to recover [ex_geom_CBN_mass_one].  Instantiate at [p := p],
    [halt := δ_0], [cont_op := scones_id] to recover both
    [ex_almost_loop_p_CBN_mass_*] headlines.

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
Require Import Icones.programs.ppl_cbn.
Require Import Icones.programs.ppl_cbn_eff.
Require Import Icones.programs.ppl_cbn_bool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** §1 — The Bernoulli-cascade operator [phi_bcascade] *)

Section PhiBCascade.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).

Variable (p : R).
Hypothesis Hp_ge0 : (0 <= p)%R.
Hypothesis Hp_le1 : (p <= 1)%R.

Variable (halt : FMeas R_obj).
Hypothesis Hhalt_ball : (cone_norm halt <= 1)%R.

Variable (cont_op : scones_hom (FMeas R_obj) (FMeas R_obj)).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

(** *** Bernoulli scrutinee — the constant Bernoulli([p]) value. *)

Definition bern_branch_bc : scones_hom (FMeas R_obj) (bool_cone_car Ar) :=
  scones_const (FMeas R_obj)
    (bernoulli p Hp_ge0 Hp_le1)
    (bernoulli_norm_le1 p Hp_ge0 Hp_le1).

Lemma bern_branch_bc_E (mu : FMeas R_obj) :
  (cone_norm mu <= 1)%R ->
  sc_fun bern_branch_bc mu = bernoulli p Hp_ge0 Hp_le1.
Proof.
move=> Hmu.
exact: (scones_const_E
          (bernoulli_norm_le1 p Hp_ge0 Hp_le1) mu Hmu).
Qed.

(** *** THEN branch — the constant [halt] value. *)

Definition then_branch_bc : scones_hom (FMeas R_obj) (FMeas R_obj) :=
  scones_const (FMeas R_obj) halt Hhalt_ball.

Lemma then_branch_bc_E (mu : FMeas R_obj) :
  (cone_norm mu <= 1)%R ->
  sc_fun then_branch_bc mu = halt.
Proof.
move=> Hmu.
exact: (scones_const_E Hhalt_ball mu Hmu).
Qed.

(** *** ELSE branch — the user-supplied continuation operator. *)

Definition else_branch_bc : scones_hom (FMeas R_obj) (FMeas R_obj) :=
  cont_op.

(** *** Inline [if] combinator on [FMeas R_obj].  Replays the
    [phi_CBN_geom] §4 construction at the abstract level. *)

Local Notation Gc := (FMeas R_obj).
Local Notation A := (FMeas R_obj).
Local Notation B := (bool_cone_car Ar).
Local Notation Sh := (stablehom Gc A).

Lemma sc_to_sh_cone_norm_le1_FMeas_bc (f : scones_hom Gc A) :
  (cone_norm (sc_to_sh f) <= 1)%R.
Proof.
rewrite -[cone_norm _]/(sh_norm (sc_to_sh f)).
apply: sh_norm_lub => x Hx.
exact: sc_image_ball.
Qed.

Definition phi_bc_if_linhom : linhom_car Ar B Sh :=
  bool_case_linhom (sc_to_sh then_branch_bc) (sc_to_sh else_branch_bc)
                   (sc_to_sh_cone_norm_le1_FMeas_bc then_branch_bc)
                   (sc_to_sh_cone_norm_le1_FMeas_bc else_branch_bc).

Lemma phi_bc_if_linhom_norm_le1 :
  (cone_norm phi_bc_if_linhom <= 1)%R.
Proof. exact: bool_case_linhom_norm_le1. Qed.

Definition phi_bc_if_scones_B_Sh : scones_hom B Sh :=
  ders (linhom_icones phi_bc_if_linhom phi_bc_if_linhom_norm_le1).

Definition phi_bc_if_scones_Gc_Sh : scones_hom Gc Sh :=
  scones_comp phi_bc_if_scones_B_Sh bern_branch_bc.

Definition phi_bcascade : scones_hom Gc A :=
  scones_comp (Ev Gc A) (spair phi_bc_if_scones_Gc_Sh (scones_id Gc)).

(** Pointwise reduction rule on the unit ball.  Mirrors
    [phi_CBN_geom_E] / [phi_almost_loop_p_E]. *)
Lemma phi_bcascade_E (mu : FMeas R_obj) :
  (cone_norm mu <= 1)%R ->
  sc_fun phi_bcascade mu =
  @bool_case R Ar (FMeas R_obj)
    (bernoulli p Hp_ge0 Hp_le1)
    halt
    (sc_fun cont_op mu).
Proof.
move=> Hmu.
rewrite /phi_bcascade.
rewrite (scomp_ball _ _ Hmu).
have Hpair : sc_fun (spair phi_bc_if_scones_Gc_Sh (scones_id Gc)) mu
           = sprod_pair (sc_fun phi_bc_if_scones_Gc_Sh mu)
                         (sc_fun (scones_id Gc) mu).
  exact: scpair_ball.
rewrite Hpair.
have Hid : sc_fun (scones_id Gc) mu = mu.
  by rewrite /scones_id /= (sc_clamp_ball Hmu).
rewrite Hid.
have Hinner :
    sc_fun phi_bc_if_scones_Gc_Sh mu =
    sc_fun phi_bc_if_scones_B_Sh (sc_fun bern_branch_bc mu).
  by rewrite /phi_bc_if_scones_Gc_Sh (scomp_ball _ _ Hmu).
rewrite Hinner.
have Hbe : (cone_norm (sc_fun bern_branch_bc mu) <= 1)%R
  by exact: sc_image_ball.
have HB : sc_fun phi_bc_if_scones_B_Sh (sc_fun bern_branch_bc mu)
        = linhom_fun phi_bc_if_linhom (sc_fun bern_branch_bc mu).
  rewrite /phi_bc_if_scones_B_Sh /ders /= (sc_clamp_ball Hbe).
  by rewrite /linhom_icones /=.
rewrite HB.
have HSh_ball :
  (cone_norm (linhom_fun phi_bc_if_linhom (sc_fun bern_branch_bc mu)) <= 1)%R.
  have step :=
    linhom_norm_apply_le phi_bc_if_linhom_norm_le1
                          (sc_fun bern_branch_bc mu).
  rewrite mul1r in step.
  exact: (le_trans step Hbe).
have Hpair_ball : (cone_norm (sprod_pair
    (linhom_fun phi_bc_if_linhom (sc_fun bern_branch_bc mu)) mu) <= 1)%R.
  exact: sprod_pair_norm_le1.
rewrite (Ev_pair _ _ Hpair_ball).
have Hlin :
    linhom_fun phi_bc_if_linhom (sc_fun bern_branch_bc mu) =
    bool_case (sc_fun bern_branch_bc mu)
              (sc_to_sh then_branch_bc) (sc_to_sh else_branch_bc).
  by rewrite /phi_bc_if_linhom /=.
rewrite Hlin.
rewrite (bern_branch_bc_E Hmu).
rewrite /bool_case /=.
rewrite /stm_add /stm_scale /sh_fun /=.
by rewrite (sc_clamp_ball Hmu).
Qed.

End PhiBCascade.

Arguments bern_branch_bc {R Ar R_obj} p Hp_ge0 Hp_le1.
Arguments then_branch_bc {R Ar R_obj} halt Hhalt_ball.
Arguments else_branch_bc {R Ar R_obj} cont_op.
Arguments phi_bcascade {R Ar R_obj} p Hp_ge0 Hp_le1 halt Hhalt_ball cont_op.
Arguments phi_bcascade_E {R Ar R_obj} p Hp_ge0 Hp_le1 halt Hhalt_ball cont_op mu.

(** ** §2 — Kleene cascade *)

Section KleeneBCascade.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).

Variable (p : R).
Hypothesis Hp_ge0 : (0 <= p)%R.
Hypothesis Hp_le1 : (p <= 1)%R.

Variable (halt : FMeas R_obj).
Hypothesis Hhalt_ball : (cone_norm halt <= 1)%R.
Hypothesis Hhalt_mass : (fmeas_mu halt [set: ar_carrier Ar R_obj] = 1%E).

Variable (cont_op : scones_hom (FMeas R_obj) (FMeas R_obj)).
Hypothesis Hcont_mass : forall mu : FMeas R_obj,
  (cone_norm mu <= 1)%R ->
  (fmeas_mu (sc_fun cont_op mu) [set: ar_carrier Ar R_obj]
   = fmeas_mu mu [set: ar_carrier Ar R_obj])%E.

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

Local Notation phi_bc' :=
  (phi_bcascade p Hp_ge0 Hp_le1 halt Hhalt_ball cont_op).

Definition kleene_bcascade (n : nat) : FMeas R_obj :=
  kleene (sc_fun phi_bc') n.

Lemma kleene_bcascade_0 :
  kleene_bcascade 0 = (precone_zero : FMeas R_obj).
Proof. by rewrite /kleene_bcascade. Qed.

Lemma kleene_bcascade_S (n : nat) :
  kleene_bcascade n.+1 = sc_fun phi_bc' (kleene_bcascade n).
Proof. by rewrite /kleene_bcascade -kleeneS. Qed.

Lemma kleene_bcascade_ball (n : nat) :
  (cone_norm (kleene_bcascade n) <= 1)%R.
Proof.
elim: n => [ | n IH ].
- by rewrite kleene_bcascade_0 cone_norm0 ler01.
- rewrite kleene_bcascade_S; exact: sc_image_ball.
Qed.

(** Per-iterate decomposition.  On the unit ball,
    [k(n+1) = p *: halt + (1 - p) *: cont_op(k(n))]. *)
Lemma kleene_bcascade_S_E (n : nat) :
  kleene_bcascade n.+1 =
  (precone_add
    (precone_scale (NngNum Hp_ge0) (halt : FMeas R_obj))
    (precone_scale (NngNum (onem_ge0 p Hp_le1))
       (sc_fun cont_op (kleene_bcascade n) : FMeas R_obj))
   : FMeas R_obj).
Proof.
rewrite kleene_bcascade_S.
rewrite (phi_bcascade_E p Hp_ge0 Hp_le1 halt Hhalt_ball cont_op
                         (kleene_bcascade n) (kleene_bcascade_ball n)).
by rewrite /bool_case /=.
Qed.

(** Mass recurrence:
    [mass(k(n+1)) = p + (1 - p) · mass(k(n))]. *)
Local Open Scope ereal_scope.
Lemma kleene_bcascade_S_mass (n : nat) :
  fmeas_mu (kleene_bcascade n.+1) [set: ar_carrier Ar R_obj]
  = (p%:E + (1 - p)%R%:E *
       fmeas_mu (kleene_bcascade n) [set: ar_carrier Ar R_obj])%E.
Proof.
rewrite kleene_bcascade_S_E.
rewrite -[precone_add _ _]/(fmeas_add
   (precone_scale (NngNum Hp_ge0) (halt : FMeas R_obj))
   (precone_scale (NngNum (onem_ge0 p Hp_le1))
      (sc_fun cont_op (kleene_bcascade n) : FMeas R_obj))).
rewrite fmeas_addE.
rewrite -[precone_scale (NngNum Hp_ge0) halt]
        /(fmeas_scale (NngNum Hp_ge0) (halt : FMeas R_obj)).
rewrite -[precone_scale (NngNum (onem_ge0 p Hp_le1)) (sc_fun cont_op _ : FMeas R_obj)]
        /(fmeas_scale (NngNum (onem_ge0 p Hp_le1))
                      (sc_fun cont_op (kleene_bcascade n) : FMeas R_obj)).
rewrite !fmeas_scaleE.
rewrite Hhalt_mass mule1.
by rewrite (Hcont_mass (kleene_bcascade_ball n)).
Qed.

(** Closed-form mass [mass(k(n)) = 1 - (1 - p)^n]. *)
Lemma kleene_bcascade_mass_closed (n : nat) :
  fmeas_mu (kleene_bcascade n) [set: ar_carrier Ar R_obj]
  = (1 - (1 - p)^+n : R)%R%:E.
Proof.
elim: n => [ | n IH ].
- by rewrite kleene_bcascade_0 expr0 subrr fmeas_zeroE.
- rewrite kleene_bcascade_S_mass IH.
  rewrite -EFinM -EFinD.
  congr (_%:E).
  rewrite exprSr.
  rewrite [in LHS]mulrBr [in LHS]mulr1.
  rewrite addrA.
  have eq1 : (p + (1 - p) = 1)%R by rewrite addrCA subrr addr0.
  by rewrite eq1 mulrC.
Qed.

(** Mass convergence when [p > 0]: [mass(k(n)) → 1]. *)
Lemma kleene_bcascade_mass_cvg_if_pos :
  (0 < p)%R ->
  fmeas_mu (kleene_bcascade n) [set: ar_carrier Ar R_obj]
    @[n --> \oo] --> (1 : \bar R).
Proof.
move=> Hp_pos.
under eq_fun => n do rewrite kleene_bcascade_mass_closed.
rewrite (_ : (1 : \bar R) = ((1 - 0)%R : R)%R%:E); last by rewrite subr0.
apply: cvg_EFin.
  by apply: nearW => n; rewrite //=.
apply: cvgB.
- exact: cvg_cst.
- apply: cvg_expr.
  have H1mp_ge0 : (0 <= 1 - p)%R by exact: onem_ge0.
  rewrite ger0_norm //.
  by rewrite ltrBlDr -ltrBlDl subrr.
Qed.

(** Per-iterate vanishing when [p = 0]. *)
Lemma kleene_bcascade_mass_eq_zero_if_zero (n : nat) :
  p = 0%R ->
  fmeas_mu (kleene_bcascade n) [set: ar_carrier Ar R_obj] = 0%E.
Proof.
move=> Hp_zero.
rewrite kleene_bcascade_mass_closed.
rewrite Hp_zero subr0 expr1n subrr.
by [].
Qed.
Local Close Scope ereal_scope.

End KleeneBCascade.

Arguments kleene_bcascade {R Ar R_obj} p Hp_ge0 Hp_le1 halt Hhalt_ball cont_op n.
Arguments kleene_bcascade_0
  {R Ar R_obj} p Hp_ge0 Hp_le1 halt Hhalt_ball cont_op.
Arguments kleene_bcascade_S
  {R Ar R_obj} p Hp_ge0 Hp_le1 halt Hhalt_ball cont_op n.
Arguments kleene_bcascade_ball
  {R Ar R_obj} p Hp_ge0 Hp_le1 halt Hhalt_ball cont_op n.
Arguments kleene_bcascade_S_E
  {R Ar R_obj} p Hp_ge0 Hp_le1 halt Hhalt_ball cont_op n.
Arguments kleene_bcascade_S_mass
  {R Ar R_obj} p Hp_ge0 Hp_le1 halt Hhalt_ball Hhalt_mass cont_op Hcont_mass n.
Arguments kleene_bcascade_mass_closed
  {R Ar R_obj} p Hp_ge0 Hp_le1 halt Hhalt_ball Hhalt_mass cont_op Hcont_mass n.
Arguments kleene_bcascade_mass_cvg_if_pos
  {R Ar R_obj} p Hp_ge0 Hp_le1 halt Hhalt_ball Hhalt_mass cont_op Hcont_mass.
Arguments kleene_bcascade_mass_eq_zero_if_zero
  {R Ar R_obj} p Hp_ge0 Hp_le1 halt Hhalt_ball Hhalt_mass cont_op Hcont_mass n.

(** ** §3 — Headlines on [sfix phi_bcascade] *)

Section SfixBCascadeMass.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).

Variable (p : R).
Hypothesis Hp_ge0 : (0 <= p)%R.
Hypothesis Hp_le1 : (p <= 1)%R.

Variable (halt : FMeas R_obj).
Hypothesis Hhalt_ball : (cone_norm halt <= 1)%R.
Hypothesis Hhalt_mass : (fmeas_mu halt [set: ar_carrier Ar R_obj] = 1%E).

Variable (cont_op : scones_hom (FMeas R_obj) (FMeas R_obj)).
Hypothesis Hcont_mass : forall mu : FMeas R_obj,
  (cone_norm mu <= 1)%R ->
  (fmeas_mu (sc_fun cont_op mu) [set: ar_carrier Ar R_obj]
   = fmeas_mu mu [set: ar_carrier Ar R_obj])%E.

Local Notation phi_bc' :=
  (phi_bcascade p Hp_ge0 Hp_le1 halt Hhalt_ball cont_op).

Definition sfix_bcascade : FMeas R_obj := sfix phi_bc'.

Local Open Scope ereal_scope.

(** Generic identification of [sfix] mass as the [fmeas_sup_meas_fun]
    of the Kleene chain at [setT]. *)
Lemma sfix_bcascade_mass_E :
  fmeas_mu sfix_bcascade [set: ar_carrier Ar R_obj] =
  fmeas_sup_meas_fun
    (kleene_chain (sc_incr phi_bc') (sc_ball_pres phi_bc'))
    [set: ar_carrier Ar R_obj].
Proof.
rewrite /sfix_bcascade /sfix /lfp.
have HE :
  cone_sup_ball (kleene phi_bc')
                (kleene_chain (sc_incr phi_bc')
                              (sc_ball_pres phi_bc'))
                (kleene_ball (sc_ball_pres phi_bc')) =
  fmeas_sup_ball
    (kleene_chain (sc_incr phi_bc') (sc_ball_pres phi_bc'))
    (kleene_ball (sc_ball_pres phi_bc'))
  by [].
rewrite HE.
by rewrite (fmeas_sup_ballE _ _ measurableT).
Qed.

(** Convergence of the per-iterate masses to the sup-mass. *)
Lemma sfix_bcascade_sup_cvg :
  fmeas_mu (kleene phi_bc' n) [set: ar_carrier Ar R_obj]
    @[n --> \oo] -->
  fmeas_sup_meas_fun
    (kleene_chain (sc_incr phi_bc') (sc_ball_pres phi_bc'))
    [set: ar_carrier Ar R_obj].
Proof. by apply: fmeas_sup_cvg; exact: measurableT. Qed.

(** *** Headline 1 — when [p > 0], [sfix] has mass [1]. *)
Theorem sfix_bcascade_mass_one_if_pos :
  (0 < p)%R ->
  fmeas_mu sfix_bcascade [set: ar_carrier Ar R_obj] = 1%:E.
Proof.
move=> Hp_pos.
rewrite sfix_bcascade_mass_E.
have Hsupcvg := sfix_bcascade_sup_cvg.
have Hcvg1 :=
  kleene_bcascade_mass_cvg_if_pos
    p Hp_ge0 Hp_le1 halt Hhalt_ball Hhalt_mass cont_op Hcont_mass Hp_pos.
have := @cvg_unique _ (@ereal_hausdorff R) _ _ _ _ Hsupcvg Hcvg1.
by move=> ->.
Qed.

(** *** Headline 2 — when [p = 0], [sfix] has mass [0]. *)
Theorem sfix_bcascade_mass_zero_if_zero :
  p = 0%R ->
  fmeas_mu sfix_bcascade [set: ar_carrier Ar R_obj] = 0%E.
Proof.
move=> Hp_zero.
rewrite sfix_bcascade_mass_E.
have Hsupcvg := sfix_bcascade_sup_cvg.
have Hzero_eq : forall n, fmeas_mu (kleene phi_bc' n)
                            [set: ar_carrier Ar R_obj] = 0%E.
  move=> n.
  exact: kleene_bcascade_mass_eq_zero_if_zero
           p Hp_ge0 Hp_le1 halt Hhalt_ball Hhalt_mass cont_op Hcont_mass n Hp_zero.
have Hcvg0 : fmeas_mu (kleene phi_bc' n) [set: ar_carrier Ar R_obj]
               @[n --> \oo] --> (0 : \bar R).
  apply: cvg_near_cst.
  by apply: nearW => n; exact: Hzero_eq.
have := @cvg_unique _ (@ereal_hausdorff R) _ _ _ _ Hsupcvg Hcvg0.
by move=> ->.
Qed.
Local Close Scope ereal_scope.

End SfixBCascadeMass.

Arguments sfix_bcascade {R Ar R_obj} p Hp_ge0 Hp_le1 halt Hhalt_ball cont_op.
Arguments sfix_bcascade_mass_one_if_pos
  {R Ar R_obj} p Hp_ge0 Hp_le1 halt Hhalt_ball Hhalt_mass cont_op Hcont_mass.
Arguments sfix_bcascade_mass_zero_if_zero
  {R Ar R_obj} p Hp_ge0 Hp_le1 halt Hhalt_ball Hhalt_mass cont_op Hcont_mass.
