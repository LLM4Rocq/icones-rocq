(**md*** BEYOND THE PAPER — CBV PPL [ex_geom] is the GEOMETRIC
    DISTRIBUTION (pointwise PMF identity at the Bang level).

    THE HEADLINE.  [ex_geom_arr_is_geometric_distribution] : for
    every natural number [k], the CBV/Bang fixpoint extraction
    [Lfun (der FMeas) (linhom_fun (Lfun (der L_geom) Yfix_arr) one1)]
    of the surface program [ex_geom] of
    [theories/programs/examples.v] assigns mass exactly
    [((1/2)^(k+1))] to the singleton [{R_to_carrier k%:R}].  This is
    the pointwise probability-mass-function characterisation of the
    geometric distribution with parameter [1/2], at the CBV side
    parallel to [ex_geom_CBN_PMF].

    ** Strategy

    We characterise each Bang-level Kleene iterate [F_arr n] (from
    [em_fix_arr.v]) by an explicit recursive partial-sum measure
    [[
       partial_geom n
         = (1/2)^n *: δ_{(n-1)%:R}
         + (1/2)^(n-1) *: δ_{(n-2)%:R}
         + ...
         + (1/2)^1 *: δ_{0%:R}
    ]]
    The key step is the per-iterate identity
    [F_arr_pointwise]: [F_arr n = partial_geom n].

    The per-iterate decomposition (proved in [em_fix_arr.v §5.9])
    is [F_arr_S_E_via_witness]:
    [[
      F_arr (n+1) = (1/2) *: δ_0
                  + (1/2) *: add_lift (δ_1, F_arr n).
    ]]
    Combined with the right-linearity of [Lfun add_lift] in the
    [ptensor] right slot, and [add_lift_dirac] giving
    [add_lift (δ_1, δ_{k%:R}) = δ_{(k+1)%:R}], we prove
    [add_lift_partial_geom]:
    [[
      add_lift (δ_1, partial_geom n) = partial_geom_shifted n,
    ]]
    where [partial_geom_shifted n = Σ (1/2)^{j+1} *: δ_{(j+1)%:R}].
    Then [half_shifted_eq] (analogous to the CBN-side lemma) closes
    the induction.

    Once we have [F_arr n = partial_geom n], the PMF at the
    singleton [{R_to_carrier k%:R}] is read off by
    [partial_geom_pmf]: for [k < n] the answer is [(1/2)^{k+1}];
    for [k >= n] it is [0].  Taking [n -> oo] via [fmeas_sup_cvg]:
    the per-iterate values are eventually [(1/2)^{k+1}] (for
    [n > k]), so the sup is [(1/2)^{k+1}].  We then transport this
    sup-level value back to [Yfix_arr]-level via the chain of three
    pushforwards [derL_Yfix_E] / [linhom_at_one_sup_E] /
    [derFMeas_one_sup_E] from [em_fix_arr.v §5.14], composed with
    [F_arr_sup] (the sup of the [F_arr] chain).

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
Require Import Icones.cones.omega_general.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.mcones.path.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_cat.
Require Import Icones.icones.examples_icone.
Require Import Icones.homs.linhom.
Require Import Icones.homs.bilin.
Require Import Icones.homs.linhom_functor.
Require Import Icones.homs.tensor.
Require Import Icones.homs.tensor_iso.
Require Import Icones.homs.smcc.
Require Import Icones.homs.exp_adjunction.
Require Import Icones.homs.bang.
Require Import Icones.homs.seely_defs.
Require Import Icones.homs.seely.
Require Import Icones.homs.coalgebra.
Require Import Icones.homs.em_cat.
Require Import Icones.homs.em_cartesian.
Require Import Icones.homs.em_seely_comonoid.
Require Import Icones.programs.infra.bool_cone.
Require Import Icones.programs.infra.bool_case_hom.
Require Import Icones.programs.infra.cbv_adjunction.
Require Import Icones.programs.infra.case_em_red.
Require Import Icones.programs.infra.curry_kbind.
Require Import Icones.programs.infra.em_continuity.
Require Import Icones.programs.infra.em_fix.
Require Import Icones.programs.infra.ex_geom_step.
Require Import Icones.programs.infra.em_fix_arr.
Require Import Icones.programs.cbv.
Require Import Icones.programs.ppl.
Require Import Icones.programs.examples.
Require Import Icones.programs.infra.geom_dist_infra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** §1 — Setup

    The shared infrastructure ([partial_geom], [partial_geom_shifted],
    [R_to_carrier_singleton_meas], [dirac_fmeas_singleton_eq],
    [partial_geom_pmf], [half_shifted_eq], [geom_coef], [half_nng],
    [half_geom_coef_eq]) lives in
    [theories/programs/infra/geom_dist_infra.v] — shared with the CBN
    parallel [theories/programs/ppl_cbn_geom_dist.v]. *)

Section ExGeomArrDist.
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

Local Notation tR' := (tR R_obj).

Let L_geom : ICone.type Ar :=
  linhom_car Ar (coalg_obj (EM_term : Coalgebra Ar))
               (coalg_obj (Tobj (tyD tR' : Coalgebra Ar))).

Local Notation kleene_arr' :=
  (@kleene_arr R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas).
Local Notation F_arr' :=
  (@F_arr R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas).
Local Notation Yfix_arr' :=
  (@Yfix_arr R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas).

Local Notation partial_geom' := (partial_geom R_carrier_eq).
Local Notation partial_geom_shifted' := (partial_geom_shifted R_carrier_eq).
Local Notation geom_coef' := (geom_coef (R := R)).
Local Notation half_nng' := (half_nng (R := R)).
Local Notation R_to_carrier_singleton_meas' :=
  (R_to_carrier_singleton_meas R_carrier_eq R_carrier_meas).
Local Notation partial_geom_pmf' :=
  (partial_geom_pmf R_carrier_eq R_carrier_meas).
Local Notation half_shifted_eq' := (half_shifted_eq R_carrier_eq).

Local Open Scope ereal_scope.

(** ** §2 — [add_lift (δ_1, _)] right-linearity. *)

(** [add_lift_one] is the right-section [m ↦ add_lift (δ_1 ⊗p m)] at
    the constant left point [δ_1].  The composition of a tensor with
    a fixed left coordinate (linear in [m] via [tau]'s linhom slot)
    and the [icones_hom] [add_lift] (linear). *)
Definition add_lift_one_fun (m : FMeas R_obj) : FMeas R_obj :=
  Lfun (@add_lift R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas)
       (ptensor (B := FMeas R_obj) (C := FMeas R_obj)
                (dirac_fmeas (R_to_carrier R_carrier_eq 1%R)) m).

Local Close Scope ereal_scope.

(** Right-linearity of [m ↦ add_lift(δ_1 ⊗p m)]. *)
Lemma add_lift_one_fun_lin : is_linear add_lift_one_fun.
Proof.
rewrite /add_lift_one_fun.
have [Hal0 HalD HalZ] := cones_hom_linear
  (mcones_hom_cones (icones_hom_mcones
    (@add_lift R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas))).
have tau_lin :=
  linhom_pre_linear (linhom_pre_of (tau (FMeas R_obj) (FMeas R_obj)
    (dirac_fmeas (R_to_carrier R_carrier_eq 1%R) : FMeas R_obj))).
split.
- rewrite -[ptensor _ _]/(linhom_fun (tau (FMeas R_obj) (FMeas R_obj)
    (dirac_fmeas (R_to_carrier R_carrier_eq 1%R) : FMeas R_obj))
    (precone_zero : FMeas R_obj)).
  rewrite -[linhom_fun _ _]/(linhom_pre_fun
    (linhom_pre_of (tau (FMeas R_obj) (FMeas R_obj)
       (dirac_fmeas (R_to_carrier R_carrier_eq 1%R) : FMeas R_obj)))
    (precone_zero : FMeas R_obj)).
  case: tau_lin => -> _ _.
  exact: Hal0.
- move=> x y.
  rewrite -[ptensor _ (precone_add x y)]
          /(linhom_fun (tau (FMeas R_obj) (FMeas R_obj)
             (dirac_fmeas (R_to_carrier R_carrier_eq 1%R) : FMeas R_obj))
             (precone_add x y)).
  rewrite -[linhom_fun _ (precone_add x y)]
          /(linhom_pre_fun
             (linhom_pre_of (tau (FMeas R_obj) (FMeas R_obj)
               (dirac_fmeas (R_to_carrier R_carrier_eq 1%R) : FMeas R_obj)))
             (precone_add x y)).
  case: tau_lin => _ -> _.
  exact: HalD.
- move=> r x.
  rewrite -[ptensor _ (precone_scale r x)]
          /(linhom_fun (tau (FMeas R_obj) (FMeas R_obj)
             (dirac_fmeas (R_to_carrier R_carrier_eq 1%R) : FMeas R_obj))
             (precone_scale r x)).
  rewrite -[linhom_fun _ (precone_scale r x)]
          /(linhom_pre_fun
             (linhom_pre_of (tau (FMeas R_obj) (FMeas R_obj)
               (dirac_fmeas (R_to_carrier R_carrier_eq 1%R) : FMeas R_obj)))
             (precone_scale r x)).
  case: tau_lin => _ _ ->.
  exact: HalZ.
Qed.

(** Dirac-at-shifted result of [add_lift(δ_1, δ_{k%:R})]. *)
Lemma add_lift_one_dirac_k (k : nat) :
  add_lift_one_fun (dirac_fmeas (R_to_carrier R_carrier_eq k%:R)
                   : FMeas R_obj)
  = dirac_fmeas (R_to_carrier R_carrier_eq k.+1%:R) :> FMeas R_obj.
Proof.
rewrite /add_lift_one_fun.
rewrite (@add_lift_dirac R Ar R_obj
  R_carrier_eq R_carrier_meas R_to_carrier_meas 1%R k%:R).
congr (dirac_fmeas _).
congr (R_to_carrier _ _).
by rewrite -natr1 addrC.
Qed.

(** [add_lift(δ_1, _)] propagates through [partial_geom n]:
    pure linearity + [add_lift_one_dirac_k]. *)
Lemma add_lift_partial_geom (n : nat) :
  add_lift_one_fun (partial_geom' n) = partial_geom_shifted' n.
Proof.
have [lin0 linD linZ] := add_lift_one_fun_lin.
elim: n => [/= |n IH].
- exact: lin0.
- rewrite [partial_geom' _]/=.
  rewrite linD linZ.
  rewrite add_lift_one_dirac_k.
  by rewrite IH.
Qed.

(** ** §3 — The per-iterate measure equality. *)

Local Close Scope ereal_scope.

(** Each [F_arr]-iterate is the corresponding [partial_geom].
    Inductive step uses [F_arr_S_E_via_witness] +
    [F_lift_eq_F_arr] (in [em_fix_arr.v §5.9]) for the
    recurrence, [add_lift_partial_geom] for the shifted pushforward
    step, and [half_shifted_eq] for the bookkeeping. *)
Lemma F_arr_pointwise (n : nat) : F_arr' n = partial_geom' n.
Proof.
elim: n => [/= |n IH].
- exact: (@F_arr_0_E R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas).
- have [u [Hu_eq Hu_norm]] := @kleene_arr_is_prom R Ar R_obj
    R_carrier_eq R_carrier_meas R_to_carrier_meas n.
  rewrite (F_arr_S_E_via_witness Hu_eq Hu_norm).
  (* Goal: precone_add (precone_scale (1/2)%:nng δ_0)
            (precone_scale (1/2)%:nng (else_branch_fmeas u))
          = partial_geom n.+1.
     [else_branch_fmeas u = add_lift (δ_1, F_lift u)] by defn,
     and [F_lift u = F_arr n] by [F_lift_eq_F_arr]; combined with IH:
     else_branch_fmeas u = add_lift_one_fun (partial_geom n) =
                            partial_geom_shifted n. *)
  have Hels :
      else_branch_fmeas R_carrier_meas R_to_carrier_meas u
      = partial_geom_shifted' n.
    rewrite -[else_branch_fmeas _ _ _]/(add_lift_one_fun (F_lift u)).
    rewrite (F_lift_eq_F_arr Hu_eq Hu_norm).
    rewrite IH.
    exact: add_lift_partial_geom.
  rewrite Hels.
  set H' := NngNum (phase4_half_ge0 R).
  set H'' := NngNum (onem_ge0 (1 / 2)%R (phase4_half_le1 R)).
  have eq_h_h : H' = half_nng' by apply: val_inj => /=.
  have eq_h''_h : H'' = half_nng'.
    apply: val_inj => /=.
    by rewrite expr1 [X in (X - _)%R]splitr addrK.
  rewrite eq_h_h eq_h''_h.
  exact: half_shifted_eq'.
Qed.

(** ** §4 — THE HEADLINE. *)

Local Open Scope ereal_scope.

(** *** [ex_geom_arr_is_geometric_distribution] : the CBV/Bang
       fixpoint extraction of [ex_geom] is the geometric
       distribution with parameter [1/2] — pointwise PMF
       [(1/2)^{k+1}] at [R_to_carrier k%:R]. *)
Theorem ex_geom_arr_is_geometric_distribution (k : nat) :
  fmeas_mu
    (Lfun (der (FMeas R_obj))
          (linhom_fun (Lfun (der L_geom) Yfix_arr')
                      (one1 : cone_one_car Ar)))
    [set R_to_carrier R_carrier_eq k%:R]
  = ((1 / 2)%R ^+ k.+1)%R%:E.
Proof.
have mU : measurable [set R_to_carrier R_carrier_eq k%:R]
  by exact: R_to_carrier_singleton_meas'.
(* Step 1.  Push the three pushforwards through Yfix_arr's
   cone_sup_ball, reducing to F_arr_sup. *)
rewrite (@derL_Yfix_E R Ar R_obj
  R_carrier_eq R_carrier_meas R_to_carrier_meas).
rewrite (@linhom_at_one_sup_E R Ar R_obj
  R_carrier_eq R_carrier_meas R_to_carrier_meas).
rewrite (@derFMeas_one_sup_E R Ar R_obj
  R_carrier_eq R_carrier_meas R_to_carrier_meas).
(* Step 2. Read the sup at the measurable singleton as a limit. *)
have HsupE :
    fmeas_mu (cone_sup_ball F_arr'
                (@F_arr_chain R Ar R_obj
                  R_carrier_eq R_carrier_meas R_to_carrier_meas)
                (@F_arr_ball R Ar R_obj
                  R_carrier_eq R_carrier_meas R_to_carrier_meas))
             [set R_to_carrier R_carrier_eq k%:R] =
    fmeas_sup_meas_fun (@F_arr_chain R Ar R_obj
                          R_carrier_eq R_carrier_meas R_to_carrier_meas)
                       [set R_to_carrier R_carrier_eq k%:R].
  by rewrite (fmeas_sup_ballE _ _ mU).
rewrite HsupE.
(* Step 3. The sequence (fmeas_mu (F_arr n) [singleton]) converges
   to the sup. *)
have Hcvg :
  fmeas_mu (F_arr' n) [set R_to_carrier R_carrier_eq k%:R]
    @[n --> \oo] -->
  fmeas_sup_meas_fun (@F_arr_chain R Ar R_obj
                        R_carrier_eq R_carrier_meas R_to_carrier_meas)
                     [set R_to_carrier R_carrier_eq k%:R]
  by exact: fmeas_sup_cvg.
(* Step 4. The sequence (fmeas_mu (partial_geom n) [singleton])
   is eventually constant equal to (1/2)^{k+1}. *)
have rwlemma : forall m : nat,
    fmeas_mu (F_arr' m) [set R_to_carrier R_carrier_eq k%:R] =
    (if (k < m)%N then ((1 / 2)%R ^+ k.+1)%R%:E else 0).
  move=> m.
  rewrite F_arr_pointwise.
  exact: partial_geom_pmf'.
have Hcvg' :
  fmeas_mu (F_arr' n) [set R_to_carrier R_carrier_eq k%:R]
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

Local Close Scope ereal_scope.

End ExGeomArrDist.

Arguments ex_geom_arr_is_geometric_distribution
  {R Ar R_obj} R_carrier_eq R_carrier_meas R_to_carrier_meas k.
