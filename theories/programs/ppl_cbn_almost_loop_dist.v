(**md*** BEYOND THE PAPER — CBN PPL [ex_almost_loop p] DISTRIBUTION
    headlines (not just mass).

    THE HEADLINES.
    - [ex_almost_loop_p_CBN_is_dirac_zero] (when [p > 0]): the CBN
      fixpoint of [ex_almost_loop p] IS the Dirac measure at
      [R_to_carrier 0] (as an [FMeas R_obj] equality, not just a
      total-mass equality).
    - [ex_almost_loop_p_CBN_is_zero_if_zero] (when [p = 0]): the CBN
      fixpoint IS the zero measure.

    ** Strategy

    Per-iterate, with [cont_op := scones_id]:
    [[
       kleene_bcascade n = (1 - (1 - p)^n) *: δ_0   (in [FMeas R_obj])
    ]]
    so at every measurable [U],
    [[
       fmeas_mu (kleene_bcascade n) U
         = (1 - (1 - p)^n) * fmeas_mu δ_0 U.
    ]]
    Taking sup as [n -> oo]: when [p > 0], [(1 - p)^n -> 0] so the
    prefactor [(1 - (1 - p)^n) -> 1] and we get [fmeas_mu δ_0 U].
    Apply [fmeas_eq] to conclude measure equality.

    When [p = 0], every iterate has mass zero pointwise, so the sup
    is the zero measure.

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
Require Import Icones.programs.infra.cbn_bernoulli_cascade.
Require Import Icones.programs.ppl_cbn_almost_loop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** §1 — Per-iterate pointwise identity (witness-polymorphic).

    For [cont_op := scones_id], every Kleene iterate is the scalar
    [(1 - (1 - p)^n)] times the [halt] Dirac measure.  Stated
    pointwise on every measurable set to feed the [fmeas_eq] /
    [fmeas_sup_cvg] machinery. *)

Section AlmostLoopDist.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.

Variable (p : R).
Hypothesis Hp_ge0 : (0 <= p)%R.
Hypothesis Hp_le1 : (p <= 1)%R.

Local Notation halt_alp_ :=
  (dirac_fmeas (R_to_carrier R_carrier_eq 0%R) : FMeas R_obj).

Local Open Scope ereal_scope.

(** Pointwise per-iterate identity (witness-polymorphic in the
    unit-ball witness for [halt_alp_]). *)
Lemma kleene_alp_pointwise (Hh : (cone_norm halt_alp_ <= 1)%R)
    (n : nat) (U : set (ar_carrier Ar R_obj)) :
  measurable U ->
  fmeas_mu
    (kleene_bcascade p Hp_ge0 Hp_le1 halt_alp_ Hh
                     (scones_id (FMeas R_obj)) n) U
  = (1 - (1 - p)^+n)%R%:E * fmeas_mu halt_alp_ U.
Proof.
move=> mU.
elim: n => [/= |n IH].
- by rewrite expr0 subrr mul0e.
- rewrite kleene_bcascade_S_E.
  rewrite -[precone_add _ _]/(fmeas_add
     (precone_scale (NngNum Hp_ge0) (halt_alp_ : FMeas R_obj))
     (precone_scale (NngNum (onem_ge0 p Hp_le1))
        (sc_fun (scones_id (FMeas R_obj))
                (kleene_bcascade p Hp_ge0 Hp_le1 halt_alp_ Hh
                                  (scones_id (FMeas R_obj)) n)
         : FMeas R_obj))).
  rewrite fmeas_addE.
  rewrite -[precone_scale (NngNum Hp_ge0) halt_alp_]
          /(fmeas_scale (NngNum Hp_ge0) (halt_alp_ : FMeas R_obj)).
  rewrite fmeas_scaleE.
  rewrite -[precone_scale (NngNum (onem_ge0 p Hp_le1)) _]
          /(fmeas_scale (NngNum (onem_ge0 p Hp_le1)) _).
  rewrite fmeas_scaleE.
  have Hkball :
    (cone_norm (kleene_bcascade p Hp_ge0 Hp_le1 halt_alp_ Hh
                (scones_id (FMeas R_obj)) n) <= 1)%R
    by exact: kleene_bcascade_ball.
  rewrite /scones_id /= (sc_clamp_ball Hkball).
  rewrite IH muleA.
  have Hfin : halt_alp_ U \is a fin_num by exact: fmeas_fin.
  have eq1 : (p + (1 - p) = 1)%R by rewrite addrCA subrr addr0.
  rewrite -[((1 - p)%:E * (1 - (1 - p)^+n)%:E)]EFinM.
  rewrite -muleDl//.
  rewrite -EFinD.
  congr (_%:E * _).
  rewrite mulrBr mulr1 addrA eq1.
  by rewrite -exprS.
Qed.

End AlmostLoopDist.

(** ** §2 — Geometric prefactor [(1 - (1-p)^n)] converges to [1].

    A small helper isolating the standard "Bernoulli prefactor →1"
    argument used by both the [p > 0] headline below and the parallel
    geometric headline in [ppl_cbn_geom_dist.v]. *)

Section GeomPrefactor.
Variables (R : realType).

Local Open Scope ereal_scope.

Lemma cvg_geom_prefactor (p : R) (Hp_ge0 : (0 <= p)%R) (Hp_le1 : (p <= 1)%R)
    (Hp_pos : (0 < p)%R) :
  (1 - (1 - p) ^+ n)%R%:E @[n --> \oo] --> (1 : \bar R).
Proof.
rewrite (_ : (1 : \bar R) = ((1 - 0)%R : R)%R%:E); last by rewrite subr0.
apply: cvg_EFin; first by apply: nearW.
apply: cvgB; first exact: cvg_cst.
apply: cvg_expr.
have H1mp_ge0 : (0 <= 1 - p)%R by exact: onem_ge0.
rewrite ger0_norm //.
by rewrite ltrBlDr -ltrBlDl subrr.
Qed.

Lemma cvg_geom_factor_to_one (p : R) (Hp_ge0 : (0 <= p)%R)
    (Hp_le1 : (p <= 1)%R) (Hp_pos : (0 < p)%R) (c : \bar R) :
  c \is a fin_num ->
  (1 - (1 - p)^+n)%R%:E * c @[n --> \oo] --> c.
Proof.
move=> Hcfin.
rewrite -[X in _ --> X](mul1e c).
apply: cvgeZr; first exact: Hcfin.
exact: cvg_geom_prefactor.
Qed.

End GeomPrefactor.

(** ** §3 — Headline: when [p > 0], the CBN fixpoint IS [δ_0]. *)

Section AlmostLoopHL.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.

Variable (p : R).
Hypothesis Hp_ge0 : (0 <= p)%R.
Hypothesis Hp_le1 : (p <= 1)%R.

Local Notation halt_alp_ :=
  (dirac_fmeas (R_to_carrier R_carrier_eq 0%R) : FMeas R_obj).

Local Open Scope ereal_scope.

(** Shared setup: identification of the [sfix] mass at [U] as the
    sup-mass of the Kleene chain, plus the convergence of the iterates
    to the sup at [U]. *)
Let almost_loop_kleene_setup (U : set (ar_carrier Ar R_obj)) (mU : measurable U) :
  let Hh := halt_alp_ball R_carrier_eq in
  let phi_bc' :=
    phi_bcascade p Hp_ge0 Hp_le1 _ Hh (scones_id (FMeas R_obj)) in
  fmeas_mu (ex_almost_loop_p_CBN_fix R_carrier_eq p Hp_ge0 Hp_le1) U =
  fmeas_sup_meas_fun
    (kleene_chain (sc_incr phi_bc') (sc_ball_pres phi_bc')) U
  /\
  (fmeas_mu (kleene phi_bc' n) U @[n --> \oo] -->
   fmeas_sup_meas_fun
     (kleene_chain (sc_incr phi_bc') (sc_ball_pres phi_bc')) U).
Proof.
split.
- rewrite /ex_almost_loop_p_CBN_fix /sfix_bcascade /sfix /lfp.
  by rewrite (fmeas_sup_ballE _ _ mU).
- exact: fmeas_sup_cvg.
Qed.

(** *** HEADLINE [p > 0]. *)
Theorem ex_almost_loop_p_CBN_is_dirac_zero :
  (0 < p)%R ->
  ex_almost_loop_p_CBN_fix R_carrier_eq p Hp_ge0 Hp_le1 = halt_alp_.
Proof.
move=> Hp_pos.
apply: fmeas_eq => U mU.
set Hh := halt_alp_ball R_carrier_eq.
set phi_bc' := phi_bcascade p Hp_ge0 Hp_le1 _ Hh (scones_id (FMeas R_obj)).
have [HE Hcvg] := almost_loop_kleene_setup mU.
rewrite HE.
have Hcvg' :
  fmeas_mu (kleene phi_bc' n) U @[n --> \oo] --> fmeas_mu halt_alp_ U.
  under eq_fun => n0 do
    rewrite -[kleene phi_bc' n0]/(kleene_bcascade p Hp_ge0 Hp_le1 halt_alp_ Hh
                                    (scones_id (FMeas R_obj)) n0)
            (kleene_alp_pointwise _ _ Hh n0 mU).
  apply: (cvg_geom_factor_to_one Hp_ge0 Hp_le1 Hp_pos).
  exact: fmeas_fin.
have := @cvg_unique _ (@ereal_hausdorff R) _ _ _ _ Hcvg Hcvg'.
by move=> ->.
Qed.

(** *** HEADLINE [p = 0]. *)
Theorem ex_almost_loop_p_CBN_is_zero_if_zero :
  p = 0%R ->
  ex_almost_loop_p_CBN_fix R_carrier_eq p Hp_ge0 Hp_le1 =
  (precone_zero : FMeas R_obj).
Proof.
move=> Hp_zero.
apply: fmeas_eq => U mU.
set Hh := halt_alp_ball R_carrier_eq.
set phi_bc' := phi_bcascade p Hp_ge0 Hp_le1 _ Hh (scones_id (FMeas R_obj)).
have [HE Hcvg] := almost_loop_kleene_setup mU.
rewrite HE.
have Hzero : forall n, fmeas_mu (kleene phi_bc' n) U = 0.
  move=> n.
  rewrite -[kleene phi_bc' n]/(kleene_bcascade p Hp_ge0 Hp_le1 halt_alp_ Hh
                                 (scones_id (FMeas R_obj)) n).
  rewrite (kleene_alp_pointwise _ _ Hh n mU).
  by rewrite Hp_zero subr0 expr1n subrr mul0e.
have Hcvg' :
  fmeas_mu (kleene phi_bc' n) U @[n --> \oo] --> (0 : \bar R)
  by apply: cvg_near_cst; apply: nearW => n; exact: Hzero.
have := @cvg_unique _ (@ereal_hausdorff R) _ _ _ _ Hcvg Hcvg'.
rewrite -[fmeas_mu precone_zero U]/(fmeas_mu fmeas_zero U) fmeas_zeroE.
by move=> ->.
Qed.

End AlmostLoopHL.

Arguments ex_almost_loop_p_CBN_is_dirac_zero
  {R Ar R_obj} R_carrier_eq p Hp_ge0 Hp_le1.
Arguments ex_almost_loop_p_CBN_is_zero_if_zero
  {R Ar R_obj} R_carrier_eq p Hp_ge0 Hp_le1.
