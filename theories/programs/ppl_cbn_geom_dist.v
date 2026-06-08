(**md*** BEYOND THE PAPER — CBN PPL [ex_geom] is the GEOMETRIC
    DISTRIBUTION (pointwise PMF identity).

    THE HEADLINE.  [ex_geom_CBN_PMF] : for every natural number [k],
    the CBN fixpoint of the surface program [ex_geom] of
    [theories/programs/examples.v] assigns mass exactly
    [((1/2)^(k+1))] to the singleton [{R_to_carrier k%:R}].  This is
    the pointwise probability-mass-function characterisation of the
    geometric distribution with parameter [1/2].

    ** Strategy

    We characterise each Kleene iterate [k(n)] at the [FMeas R_obj]
    level by an explicit recursive partial-sum measure
    [[
       partial_geom n
         = (1/2)^n *: δ_{(n-1)%:R}
         + (1/2)^(n-1) *: δ_{(n-2)%:R}
         + ...
         + (1/2)^1 *: δ_{0%:R}
    ]]
    The key step is the **measure-equality**
    [kleene_geom_partial]: [k(n) = partial_geom n].  This uses:
    - [shift_lift] is LINEAR (proved here from
      [linhom_pre_linear] via the [linhom_icones] packaging),
    - [shift_lift_dirac] (already shipped) gives
      [shift_lift 1 (δ_r) = δ_(1 + r)].
    These two together let us prove
    [shift_partial_geom] :
       [Lfun (shift_lift 1) (partial_geom n) = partial_geom_shifted n],
    where [partial_geom_shifted] is the "shifted" partial sum
    [Σ (1/2)^{j+1} *: δ_{(j+1)%:R}].

    From [partial_geom_shifted] we then derive
    [half_shifted_eq] :
       [(1/2)*:δ_0 + (1/2)*:partial_geom_shifted n = partial_geom n.+1],
    which combined with [kleene_bcascade_S_E] gives the inductive step
    [k(n+1) = partial_geom (n+1)].

    Once we have [k(n) = partial_geom n], the PMF at the singleton
    [{R_to_carrier k%:R}] is read off by [partial_geom_pmf]:
    for [k < n] the answer is [(1/2)^{k+1}]; for [k >= n] it is [0].
    Taking [n -> oo] via [fmeas_sup_cvg]: the per-iterate values are
    eventually [(1/2)^{k+1}] (for [n > k]), so the sup is
    [(1/2)^{k+1}].  Combine with [cvg_unique] to identify the
    [sfix]-level value.

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
Require Import Icones.homs.tensor_hom_iso.
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
Require Import Icones.programs.ppl_cbn_geom.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** §1 — Setup: explicit partial-sum measures *)

Section GeomDist.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

(** [geom_coef k = (1/2)^{k+1}] as a nonneg scalar. *)
Definition geom_coef (k : nat) : {nonneg R} :=
  (((1 / 2)%R ^+ k.+1)%:nng).

(** [partial_geom n] is the explicit finite-sum measure
    [Σ_{j < n} (1/2)^{j+1} *: δ_{R_to_carrier j%:R}].
    Built recursively so the head exposes the [n-1] term, matching
    the structure of [kleene_bcascade] iterates. *)
Fixpoint partial_geom (n : nat) : FMeas R_obj :=
  match n with
  | 0%N => precone_zero
  | k.+1 => precone_add
            (precone_scale (geom_coef k)
                           (dirac_fmeas (R_to_carrier R_carrier_eq k%:R)
                            : FMeas R_obj))
            (partial_geom k)
  end.

Local Open Scope ereal_scope.

(** ** §2 — Singleton measurability + Dirac PMF *)

(** Measurability of [R_to_carrier r]-singletons.  We pull back
    [{r}] (singleton in [R], measurable by [measurable_set1]) along
    [carrier_to_R] (measurable by [carrier_to_R_meas]). *)
Lemma R_to_carrier_singleton_meas (r : R) :
  measurable [set R_to_carrier R_carrier_eq r].
Proof.
have rwset : [set R_to_carrier R_carrier_eq r] =
             (carrier_to_R R_carrier_eq) @^-1` [set r].
  apply: funext => x; rewrite propeqE; split.
  - by move=> -> /=; rewrite R_to_carrierK.
  - by move=> /= H; rewrite -[x](carrier_to_RK R_carrier_eq) H.
rewrite rwset.
have ctoR_meas :
    measurable_fun [set: ar_carrier Ar R_obj] (carrier_to_R R_carrier_eq)
  by exact: carrier_to_R_meas.
have := ctoR_meas measurableT [set r] (measurable_set1 r).
by rewrite setTI.
Qed.

(** Dirac at a real-cast point evaluated against a real-cast
    singleton: equality iff the underlying reals match. *)
Lemma dirac_fmeas_singleton_eq (a b : R) :
  fmeas_mu (dirac_fmeas (R_to_carrier R_carrier_eq a) : FMeas R_obj)
           [set R_to_carrier R_carrier_eq b]
  = (if a == b then 1%R else 0%R)%R%:E.
Proof.
have mU : measurable [set R_to_carrier R_carrier_eq b]
  by exact: R_to_carrier_singleton_meas.
rewrite dirac_fmeas_E// diracE.
have inH : (R_to_carrier R_carrier_eq a \in
              [set R_to_carrier R_carrier_eq b])
        = (a == b).
  apply/idP/idP.
  - rewrite inE => /= /(congr1 (carrier_to_R R_carrier_eq)).
    by rewrite !R_to_carrierK => ->.
  - by move=> /eqP -> ; rewrite inE /=.
by rewrite inH; case: (a == b).
Qed.

(** ** §3 — PMF of [partial_geom] at integer-valued singletons. *)

Lemma partial_geom_pmf (n k : nat) :
  fmeas_mu (partial_geom n)
           [set R_to_carrier R_carrier_eq k%:R]
  = if (k < n)%N then ((1 / 2)%R ^+ k.+1)%R%:E else 0.
Proof.
elim: n => [/= |n IH].
- by [].
- rewrite [partial_geom _]/=.
  rewrite -[precone_add _ _]/(fmeas_add
     (precone_scale (geom_coef n)
        (dirac_fmeas (R_to_carrier R_carrier_eq n%:R) : FMeas R_obj))
     (partial_geom n)).
  rewrite fmeas_addE.
  rewrite -[precone_scale (geom_coef n) _]
          /(fmeas_scale (geom_coef n)
             (dirac_fmeas (R_to_carrier R_carrier_eq n%:R) : FMeas R_obj)).
  rewrite fmeas_scaleE.
  rewrite (dirac_fmeas_singleton_eq n%:R k%:R).
  rewrite IH eqr_nat.
  case: (ltngtP k n) => Hkn /=.
  - rewrite mule0 add0e.
    by rewrite ltnW.
  - rewrite mule0 add0e.
    have -> : (k < n.+1)%N = false by rewrite ltnNge (leq_trans _ Hkn).
    by [].
  - rewrite Hkn ltnSn.
    by rewrite mule1 adde0 /geom_coef.
Qed.

(** ** §4 — Linearity of [Lfun (shift_lift 1)] *)

(** A "shifted" partial-sum measure
    [Σ_{j < n} (1/2)^{j+1} *: δ_{R_to_carrier (j+1)%:R}],
    obtained by applying [shift_lift 1] to [partial_geom n]. *)
Fixpoint partial_geom_shifted (n : nat) : FMeas R_obj :=
  match n with
  | 0%N => precone_zero
  | k.+1 => precone_add
            (precone_scale (geom_coef k)
                           (dirac_fmeas (R_to_carrier R_carrier_eq k.+1%:R)
                            : FMeas R_obj))
            (partial_geom_shifted k)
  end.

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

(** Linearity of [Lfun (shift_lift 1)] : extracted from
    [linhom_pre_linear] via the [linhom_icones] equality
    [linhom_iconesE]. *)
Lemma shift_lift_lin :
  is_linear
    (Lfun (shift_lift R_carrier_eq R_carrier_meas R_to_carrier_meas 1)).
Proof.
rewrite /shift_lift /FMeas_fmap.
set phi := int_to_linhom _.
set Hphi := FMeas_fmap_norm_le1 _.
have rw : forall x : FMeas R_obj,
  cones_hom_fun (mcones_hom_cones (icones_hom_mcones (linhom_icones phi Hphi))) x
  = linhom_fun phi x
  by move=> x; exact: linhom_iconesE.
have philin : is_linear (linhom_fun phi) by exact: linhom_pre_linear.
split.
- by rewrite rw; case: philin.
- by move=> x y; rewrite !rw; case: philin => _ ->.
- by move=> r x; rewrite !rw; case: philin => _ _ ->.
Qed.

(** [Lfun (shift_lift 1)] propagates through [partial_geom n]:
    pure linearity + [shift_lift_dirac]. *)
Lemma shift_partial_geom (n : nat) :
  Lfun (shift_lift R_carrier_eq R_carrier_meas R_to_carrier_meas 1)
       (partial_geom n) = partial_geom_shifted n.
Proof.
have [lin0 linD linZ] := shift_lift_lin.
elim: n => [/= |n IH].
- exact: lin0.
- rewrite [partial_geom _]/=.
  rewrite linD linZ.
  rewrite (shift_lift_dirac _ _ _ 1 n%:R).
  rewrite IH.
  rewrite [partial_geom_shifted _.+1]/=.
  congr (precone_add _ _).
  congr (precone_scale _ _).
  congr (dirac_fmeas _).
  congr (R_to_carrier _ _).
  by rewrite addrC -natr1.
Qed.

(** ** §5 — Coefficient arithmetic on [(1/2)] *)

Definition half_nng : {nonneg R} := geom_coef 0.

Lemma half_nng_E : (half_nng%:num = 1 / 2)%R.
Proof. by rewrite /half_nng /geom_coef /= expr1. Qed.

Local Close Scope ereal_scope.

Lemma half_geom_coef_eq (n : nat) :
  (half_nng%:num * (geom_coef n)%:num)%:nng = geom_coef n.+1.
Proof. by apply: val_inj => /=; rewrite -exprS. Qed.

Local Open Scope ereal_scope.

(** ** §6 — The shift-recovery lemma. *)

(** [(1/2)*:δ_0 + (1/2)*:partial_geom_shifted n = partial_geom (n+1)].
    This is the key arithmetic on the partial-sum structure,
    proved by induction on [n] using precone-axiom rearrangements. *)
Lemma half_shifted_eq (n : nat) :
  precone_add
    (precone_scale half_nng
       (dirac_fmeas (R_to_carrier R_carrier_eq 0%R) : FMeas R_obj))
    (precone_scale half_nng (partial_geom_shifted n))
  = partial_geom n.+1.
Proof.
elim: n => [/= |n IH].
- by rewrite precone_scale_0r.
- rewrite [partial_geom_shifted _.+1]/=.
  rewrite precone_scale_DAr.
  rewrite precone_addA.
  rewrite (precone_addC (half_nng *: dirac_fmeas _)%PC).
  rewrite -precone_addA.
  rewrite IH.
  rewrite [partial_geom n.+2]/=.
  congr (precone_add _ _).
  rewrite -precone_scale_A.
  by rewrite (half_geom_coef_eq n).
Qed.

(** ** §7 — The per-iterate measure equality. *)

(** Each Kleene iterate of the [ex_geom] cascade is the corresponding
    [partial_geom].  This is the workhorse — closed via three
    nested ingredients:
    - [kleene_bcascade_S_E] for the recurrence,
    - [shift_scones_E] to peel off the unit-ball clamp,
    - [shift_partial_geom] for the pushforward step,
    - [half_shifted_eq] for the bookkeeping. *)
Lemma kleene_geom_partial (Hh : (cone_norm
   (dirac_fmeas (R_to_carrier R_carrier_eq 0%R) : FMeas R_obj) <= 1)%R)
    (n : nat) :
  kleene_bcascade (1 / 2)%R (phase4_half_ge0 R) (phase4_half_le1 R)
    (dirac_fmeas (R_to_carrier R_carrier_eq 0%R) : FMeas R_obj) Hh
    (shift_scones R_carrier_eq R_carrier_meas R_to_carrier_meas 1)
    n
  = partial_geom n.
Proof.
elim: n => [/= |n IH].
- by [].
- rewrite kleene_bcascade_S_E.
  rewrite IH.
  have Hkball : (cone_norm (partial_geom n) <= 1)%R.
    rewrite -IH; exact: kleene_bcascade_ball.
  rewrite shift_scones_E//.
  rewrite shift_partial_geom.
  set H' := NngNum (phase4_half_ge0 R).
  set H'' := NngNum (onem_ge0 (1 / 2)%R (phase4_half_le1 R)).
  have eq_h_h : H' = half_nng by apply: val_inj => /=.
  have eq_h''_h : H'' = half_nng.
    apply: val_inj => /=.
    by rewrite expr1 [X in (X - _)%R]splitr addrK.
  rewrite eq_h_h eq_h''_h.
  exact: half_shifted_eq.
Qed.

(** ** §8 — THE HEADLINE. *)

(** *** [ex_geom_CBN_fix] is the geometric distribution with parameter
       [1/2]: pointwise PMF [(1/2)^{k+1}] at [R_to_carrier k%:R]. *)
Theorem ex_geom_CBN_PMF (k : nat) :
  fmeas_mu (ex_geom_CBN_fix R_carrier_eq R_carrier_meas R_to_carrier_meas)
           [set R_to_carrier R_carrier_eq k%:R]
  = ((1 / 2)%R ^+ k.+1)%R%:E.
Proof.
set Hh := halt_geom_ball R_carrier_eq.
set phi_geom :=
  phi_bcascade (1 / 2)%R (phase4_half_ge0 R) (phase4_half_le1 R) _ Hh
    (shift_scones R_carrier_eq R_carrier_meas R_to_carrier_meas 1).
have mU : measurable [set R_to_carrier R_carrier_eq k%:R]
  by exact: R_to_carrier_singleton_meas.
have HE : fmeas_mu
   (ex_geom_CBN_fix R_carrier_eq R_carrier_meas R_to_carrier_meas)
   [set R_to_carrier R_carrier_eq k%:R] =
  fmeas_sup_meas_fun (kleene_chain (sc_incr phi_geom) (sc_ball_pres phi_geom))
                     [set R_to_carrier R_carrier_eq k%:R].
  rewrite /ex_geom_CBN_fix /sfix_bcascade /sfix /lfp.
  by rewrite (fmeas_sup_ballE _ _ mU).
rewrite HE.
have Hcvg :
  fmeas_mu (kleene phi_geom n) [set R_to_carrier R_carrier_eq k%:R]
    @[n --> \oo] -->
  fmeas_sup_meas_fun (kleene_chain (sc_incr phi_geom) (sc_ball_pres phi_geom))
                     [set R_to_carrier R_carrier_eq k%:R]
  by exact: fmeas_sup_cvg.
have rwlemma : forall m : nat,
  fmeas_mu (kleene phi_geom m) [set R_to_carrier R_carrier_eq k%:R] =
  (if (k < m)%N then ((1 / 2)%R ^+ k.+1)%R%:E else 0).
  move=> m.
  rewrite -[kleene phi_geom m]/(kleene_bcascade (1 / 2)%R
                                (phase4_half_ge0 R) (phase4_half_le1 R)
                                (dirac_fmeas (R_to_carrier R_carrier_eq 0)
                                 : FMeas R_obj) Hh
                                (shift_scones R_carrier_eq
                                  R_carrier_meas R_to_carrier_meas 1) m).
  rewrite (kleene_geom_partial Hh).
  exact: partial_geom_pmf.
have Hcvg' :
  fmeas_mu (kleene phi_geom n) [set R_to_carrier R_carrier_eq k%:R]
    @[n --> \oo] --> ((1 / 2)%R ^+ k.+1)%R%:E.
  apply: cvg_near_cst.
  exists k.+1 => /=; first by [].
  move=> m Hm.
  rewrite rwlemma.
  have -> : (k < m)%N = true by [].
  by [].
have := @cvg_unique _ (@ereal_hausdorff R) _ _ _ _ Hcvg Hcvg'.
by move=> ->.
Qed.

End GeomDist.

Arguments ex_geom_CBN_PMF
  {R Ar R_obj} R_carrier_eq R_carrier_meas R_to_carrier_meas k.
