(**md**************************************************************************)
(** * [ex_almost_loop_step] — cone_one_car-level cascade for
        [ex_almost_loop p].  CBV-side mass headlines.

    This file ships the CBV-side analogue of
    [ppl_cbn_almost_loop.v]'s headline closure for the parameterised
    partial-termination example [ex_almost_loop p].  We deliver
    AXIOM-FREE (modulo the three boolp axioms):

    *** What is delivered.

    1. Per-iterate convex decomposition at the [cone_one_car] level:
       for any witness [u : L_loop] with [cone_norm u ≤ 1],
       [[
         Lfun (der (cone_one_car Ar))
              (linhom_fun
                 (Lfun (der L_loop)
                       (Step_loop_p one1 (prom u)))
                 one1)
         = precone_add (precone_scale p one1)
                       (precone_scale (1 - p) (F_lift_loop u))
       ]]
       (in [cone_one_car Ar]).  Mirrors §5.8 of [em_fix_arr.v] for
       the FMeas-level geometric cascade, here at scalar level.

    2. Per-iterate scalar recurrence:
       [[
         (c1_val (F_arr_loop_p p Hp_ge0 Hp_le1 n.+1))%:num
         = p + (1 - p) * (c1_val (F_arr_loop_p p Hp_ge0 Hp_le1 n))%:num.
       ]]

    3. Closed-form scalar mass:
       [[
         (c1_val (F_arr_loop_p p Hp_ge0 Hp_le1 n))%:num = 1 - (1 - p)^n.
       ]]

    4. ω-continuity of [Step_loop_p one1] and the seed-order
       [prom 0_L_loop ≤p Step_loop_p one1 (prom 0_L_loop)] (so the
       Kleene chain is increasing in the [Bang]-cone order).

    5. Sup convergence via [nondecreasing_cvgn]:
       [[
         (c1_val (F_arr_loop_p p Hp_ge0 Hp_le1 n))%:num @[n --> oo]
           --> sup [set (c1_val (F_arr_loop_p p Hp_ge0 Hp_le1 n))%:num
                        | n in [set: nat]]
       ]]
       and the [c1_sup_ball] reading of the sup.

    6. THE TWO HEADLINES (the parallel of
       [ex_almost_loop_p_CBN_mass_one_if_pos] /
       [ex_almost_loop_p_CBN_mass_zero_if_zero] for CBV):
       [[
         ex_almost_loop_p_arr_mass_one_if_pos :
           (0 < p)%R ->
           (c1_val (F_arr_loop_p_sup p Hp_ge0 Hp_le1))%:num = 1%R.
         ex_almost_loop_p_arr_mass_zero_if_zero :
           (p = 0)%R ->
           (c1_val (F_arr_loop_p_sup p Hp_ge0 Hp_le1))%:num = 0%R.
       ]]
       where [F_arr_loop_p_sup] is the [c1_sup_ball] of the increasing
       chain [F_arr_loop_p _ _ _ n].

    *** Author

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
Require Import Icones.icones.icone_integral.
Require Import Icones.icones.icone_cat.
Require Import Icones.icones.examples_icone.
Require Import Icones.stable.totmono.
Require Import Icones.stable.scones_cat.
Require Import Icones.homs.icones_iso.
Require Import Icones.homs.linhom.
Require Import Icones.homs.bilin.
Require Import Icones.homs.linhom_functor.
Require Import Icones.homs.tensor.
Require Import Icones.homs.tensor_iso.
Require Import Icones.homs.tensor_hom_iso.
Require Import Icones.homs.smcc.
Require Import Icones.homs.exp_adjunction.
Require Import Icones.homs.bang.
Require Import Icones.homs.fmeas_lax.
Require Import Icones.homs.seely_defs.
Require Import Icones.homs.seely.
Require Import Icones.homs.coalgebra.
Require Import Icones.homs.em_cat.
Require Import Icones.homs.em_cartesian.
Require Import Icones.homs.em_seely_comonoid.
Require Import Icones.programs.infra.cbv_adjunction.
Require Import Icones.programs.infra.cbv_outer_pt.
Require Import Icones.programs.infra.bool_cone.
Require Import Icones.programs.infra.bool_case_hom.
Require Import Icones.programs.infra.case_em_red.
Require Import Icones.programs.infra.curry_kbind.
Require Import Icones.programs.infra.em_fix.
Require Import Icones.programs.infra.ex_loop_arr.
Require Import Icones.programs.infra.ex_almost_loop_arr.
Require Import Icones.programs.cbv.
Require Import Icones.programs.ppl.
Require Import Icones.programs.examples.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** Section setup *)

Section ExAlmostLoopStep.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Variable (p : R).
Hypothesis (Hp_ge0 : (0 <= p)%R).
Hypothesis (Hp_le1 : (p <= 1)%R).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

Local Notation eD' :=
  (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas).

(** Recap of the [Let]-bound section variables from
    [ex_almost_loop_arr.v]; redeclared as [Let] so the cascade can
    reference [L_loop], [funT_loop], [G_loop] directly. *)
Let L_loop : ICone.type Ar :=
  linhom_car Ar (coalg_obj (EM_term : Coalgebra Ar))
               (coalg_obj (Tobj (EM_term : Coalgebra Ar))).

Let funT_loop : Coalgebra Ar := bang_cofree L_loop.

Local Notation G_loop :=
  (EM_prod (EM_prod (EM_term : Coalgebra Ar) funT_loop)
           (EM_term : Coalgebra Ar)).

(** Local THEN/ELSE notations matching [ex_almost_loop_arr.v]. *)
Local Notation then_e :=
  (@ne_tt R Ar R_obj
     (("_"%string, tunit) :: ("l"%string, tfun tunit tunit) :: nil)).

Local Notation else_e :=
  (ne_app (ne_var (nv_tail "_"%string tunit _
                    (nv_head "l"%string (tfun tunit tunit) nil)))
          ne_tt).

(** ** §1 — THEN-branch evaluation at the outer pt

    For any [u : L_loop] with [cone_norm u ≤ 1], the THEN-branch
    [ne_tt] evaluates at [at_outer_pt_u u] to [prom one1]: by
    [eD_tt], [eD' ne_tt = coalg_comp (tunit_eta EM_term) (em_term_mor _)];
    by [Lfun_ch_mor_const_kleisli_at] applied at [one1 : cone_one_car],
    the result is [prom one1] (after [coalg_e_G_on_outer_pt_u_E]
    reduces the [coalg_e G_loop] subterm to [one1]).

    This mirrors §0's [Lfun_ch_mor_then_e_at_outer_pt_E] in
    [ex_geom_step.v] but at the [cone_one_car] level (where the
    constant value is [one1], not [dirac_fmeas 0]). *)

(** [cone_norm_one1] (= 1) / [cone_norm_one1_le1] / [linhom_fun_precone_add_E]
    / [linhom_fun_precone_scale_E] now come from [cbv_outer_pt.v]. *)

Local Notation cone_norm_one1_step := (cone_norm_one1 (R:=R) (Ar:=Ar)).
Local Notation cone_norm_one1_le1_step := (cone_norm_one1_le1 (R:=R) (Ar:=Ar)).
Local Notation linhom_fun_precone_add_E_alp :=
  (@linhom_fun_precone_add_E R Ar).
Local Notation linhom_fun_precone_scale_E_alp :=
  (@linhom_fun_precone_scale_E R Ar).

Lemma Lfun_ch_mor_then_e_at_outer_pt_u_E
    (u : L_loop) (Hu : cone_norm u <= 1) :
  Lfun (ch_mor (eD' then_e))
       (@at_outer_pt_u R Ar L_loop u)
  = prom (one1 : cone_one_car Ar).
Proof.
rewrite (eD_tt (("_"%string, tunit) :: ("l"%string, tfun tunit tunit) :: nil)).
rewrite -[ch_mor (coalg_comp _ _)]
        /(icones_comp (ch_mor (tunit_eta EM_term))
                      (ch_mor (em_term_mor (ctxD (drop_names
                          (("_"%string, tunit)
                           :: ("l"%string, tfun tunit tunit) :: nil)))))).
rewrite -[Lfun (icones_comp _ _) _]
        /(Lfun (ch_mor (tunit_eta EM_term))
               (Lfun (ch_mor (em_term_mor _))
                     (@at_outer_pt_u R Ar L_loop u))).
rewrite -[ch_mor (em_term_mor _)]/(coalg_e G_loop).
rewrite (@coalg_e_G_on_outer_pt_u_E R Ar L_loop u Hu).
rewrite -[ch_mor (tunit_eta EM_term)]/(coalg_str (EM_term : Coalgebra Ar)).
rewrite -[coalg_str EM_term]/(unit_cofree_str (Ar:=Ar)) unit_cofree_str_one1.
by [].
Qed.

(** Post-[der] form: [Lfun (der cone_one) (prom one1) = one1]. *)
Lemma der_Lfun_ch_mor_then_e_at_outer_pt_u_E
    (u : L_loop) (Hu : cone_norm u <= 1) :
  Lfun (der (cone_one_car Ar))
       (Lfun (ch_mor (eD' then_e))
             (@at_outer_pt_u R Ar L_loop u))
  = (one1 : cone_one_car Ar).
Proof.
rewrite (Lfun_ch_mor_then_e_at_outer_pt_u_E Hu).
exact: (der_prom (B := cone_one_car Ar) one1 cone_norm_one1_le1_step).
Qed.

(** ** §2 — ELSE-branch via [ex_loop_arr]'s
    [Lfun_ch_mor_app_l_tt_at_outer_pt_u_E]

    The ELSE-branch [#l @ ()] at [at_outer_pt_u u] evaluates to
    [prom (F_lift_loop u)], directly from [ex_loop_arr.v]'s lemma
    [Lfun_ch_mor_app_l_tt_at_outer_pt_u_E].  Use it as-is.

    Post-[der] form: [Lfun (der cone_one) (prom (F_lift_loop u)) =
    F_lift_loop u] (by [der_prom] + norm bound). *)

Lemma F_lift_loop_norm_le1
    (u : L_loop) (Hu : cone_norm u <= 1) :
  cone_norm (@F_lift_loop R Ar u) <= 1.
Proof.
rewrite /F_lift_loop.
apply: le_trans (cones_hom_norm_le1 _ _) _.
apply: le_trans (linhom_norm_apply_le Hu _) _.
by rewrite cone_norm_one1_step mulr1.
Qed.

Lemma der_Lfun_ch_mor_else_e_at_outer_pt_u_E
    (u : L_loop) (Hu : cone_norm u <= 1) :
  Lfun (der (cone_one_car Ar))
       (Lfun (ch_mor (eD' else_e))
             (@at_outer_pt_u R Ar L_loop u))
  = @F_lift_loop R Ar u.
Proof.
rewrite (@Lfun_ch_mor_app_l_tt_at_outer_pt_u_E R Ar R_obj
           R_carrier_eq R_carrier_meas R_to_carrier_meas u Hu).
exact: (der_prom (B := cone_one_car Ar) _ (F_lift_loop_norm_le1 Hu)).
Qed.

(** ** §3 — [Lfun (ch_mor (convex_combination then_e else_e))] at
        [at_outer_pt_u u]

    Mirror of §5.7 of [em_fix_arr.v].  By [Lfun_ch_mor_adj_psi_at] +
    [coalg_str_G_on_outer_pt_u_E] + [bang_fmap_prom] applied to the
    [convex_combination] (which is [adj_psi convex_icones]). *)

(** [cone_norm_at_outer_pt_u_step] retained as a thin alias of
    [cbv_outer_pt.cone_norm_at_outer_pt_u_le1] for backward source
    compatibility. *)
Local Notation cone_norm_at_outer_pt_u_step :=
  (@cone_norm_at_outer_pt_u_le1 R Ar L_loop _).

Lemma Lfun_ch_mor_convex_at_outer_pt_u_E
    (u : L_loop) (Hu : cone_norm u <= 1) :
  Lfun (ch_mor (convex_combination (eD' then_e) (eD' else_e)
                                   Hp_ge0 Hp_le1))
       (@at_outer_pt_u R Ar L_loop u)
  = prom (Lfun (convex_icones (eD' then_e) (eD' else_e)
                              Hp_ge0 Hp_le1)
               (@at_outer_pt_u R Ar L_loop u)).
Proof.
rewrite /convex_combination.
rewrite (Lfun_ch_mor_adj_psi_at
           (convex_icones (eD' then_e) (eD' else_e) Hp_ge0 Hp_le1)
           (@at_outer_pt_u R Ar L_loop u)).
rewrite (@coalg_str_G_on_outer_pt_u_E R Ar L_loop u Hu).
have Hbnd : cone_norm (@at_outer_pt_u R Ar L_loop u) <= 1
  by exact: (cone_norm_at_outer_pt_u_le1 (L:=L_loop) Hu).
by rewrite (bang_fmap_prom
              (convex_icones (eD' then_e) (eD' else_e) Hp_ge0 Hp_le1)
              _ Hbnd).
Qed.

(** ** §4 — [Lfun convex_icones] at [at_outer_pt_u u] as pointwise sum
        decomposition

    Mirrors §5.7's [Lfun_convex_icones_at_outer_pt_u_E] from
    [em_fix_arr.v]: [convex_icones = der (cone_one_car Ar) ∘
    convex_icones_bang] and [convex_icones_bang] is [bool_case
    (bernoulli p) a_lh b_lh]. *)

Lemma Lfun_convex_icones_at_outer_pt_u_E
    (u : L_loop) (Hu : cone_norm u <= 1) :
  Lfun (convex_icones (eD' then_e) (eD' else_e) Hp_ge0 Hp_le1)
       (@at_outer_pt_u R Ar L_loop u)
  = Lfun (der (cone_one_car Ar))
         (precone_add
            (precone_scale (NngNum Hp_ge0)
              (Lfun (ch_mor (eD' then_e))
                    (@at_outer_pt_u R Ar L_loop u)))
            (precone_scale (NngNum (onem_ge0 p Hp_le1))
              (Lfun (ch_mor (eD' else_e))
                    (@at_outer_pt_u R Ar L_loop u)))).
Proof.
have Hinner :
  Lfun (convex_icones_bang (eD' then_e) (eD' else_e) Hp_ge0 Hp_le1)
       (@at_outer_pt_u R Ar L_loop u)
  = precone_add
      (precone_scale (NngNum Hp_ge0)
        (Lfun (ch_mor (eD' then_e))
              (@at_outer_pt_u R Ar L_loop u)))
      (precone_scale (NngNum (onem_ge0 p Hp_le1))
        (Lfun (ch_mor (eD' else_e))
              (@at_outer_pt_u R Ar L_loop u))).
  rewrite -[Lfun (convex_icones_bang _ _ _ _) _]
          /(linhom_fun (convex_linhom (eD' then_e) (eD' else_e)
                                      Hp_ge0 Hp_le1)
                       (@at_outer_pt_u R Ar L_loop u)).
  rewrite convex_linhomE /bool_case.
  rewrite linhom_fun_precone_add_E_alp.
  rewrite !linhom_fun_precone_scale_E_alp.
  congr (precone_add (precone_scale _ _) (precone_scale _ _));
    by apply: nngnum_inj.
rewrite -[LHS]/(Lfun (der (cone_one_car Ar))
                     (Lfun (convex_icones_bang (eD' then_e) (eD' else_e)
                                               Hp_ge0 Hp_le1)
                           (@at_outer_pt_u R Ar L_loop u))).
by rewrite Hinner.
Qed.

(** ** §5 — Eval-at-one1 form (post-der, post-eval-at-one1)

    Mirror of §5.7 of [em_fix_arr.v]:
    [linhom_fun (Lfun (der L_loop) (Step_loop_p one1 (prom u))) one1
     = Lfun (ch_mor (convex_combination then_e else_e)) (at_outer_pt_u u)]. *)

Lemma cone_norm_K_alp_le1
    (u : L_loop) (Hu : cone_norm u <= 1) :
  cone_norm
    (Lfun (tensor_curry (ch_mor (convex_combination (eD' then_e)
                                    (eD' else_e) Hp_ge0 Hp_le1)))
          (ptensor one1 (prom u))) <= 1.
Proof.
apply: le_trans (cones_hom_norm_le1 _ _) _.
apply: le_trans (tensor_norm_le _ _) _.
rewrite -[1]mulr1; apply: ler_pM.
- exact: cone_norm_ge0.
- exact: cone_norm_ge0.
- by rewrite cone_norm_one1_le1_step.
- exact: prom_ball Hu.
Qed.

(** Body inner [if Bernoulli(p) then ne_tt else l()] equals convex
    combination of THEN/ELSE branches with weight [p].  This is the
    [body_inner_p_via_convex] lemma from [ex_almost_loop_arr.v]. *)
Lemma body_inner_p_via_convex_step :
  eD' (ne_if tunit
        (ne_bernoulli (R := R) (Ar := Ar) (R_obj := R_obj)
                      (G := ("_"%string, tunit)
                            :: ("l"%string, tfun tunit tunit) :: nil)
                      p Hp_ge0 Hp_le1)
        then_e else_e)
  = convex_combination (eD' then_e) (eD' else_e) Hp_ge0 Hp_le1.
Proof.
exact: (case_em_bernoulli (eD' then_e) (eD' else_e) Hp_ge0 Hp_le1).
Qed.

(** Step_loop_p one1 (prom u) reduces (using lam_coalg_at_one_prom_loop)
    to [prom (Lfun (tensor_curry (ch_mor (body_inner))) (one1 ⊗p prom u))].
    Then by [body_inner_p_via_convex_step], we get the convex form. *)
Lemma Step_loop_p_one_prom_u_E
    (u : L_loop) (Hu : cone_norm u <= 1) :
  @Step_loop_p R Ar R_obj
     R_carrier_eq R_carrier_meas R_to_carrier_meas
     p Hp_ge0 Hp_le1 one1 (prom u) =
  prom (Lfun (tensor_curry (ch_mor (convex_combination (eD' then_e)
                                      (eD' else_e) Hp_ge0 Hp_le1)))
             (ptensor one1 (prom u))).
Proof.
rewrite (@Step_loop_p_E R Ar R_obj
           R_carrier_eq R_carrier_meas R_to_carrier_meas
           p Hp_ge0 Hp_le1 one1 (prom u)).
rewrite -body_inner_p_via_convex_step.
exact: (@lam_coalg_at_one_prom_loop R Ar
          _ u Hu).
Qed.

(** Post-[der] form of Step_loop_p one1 (prom u): extract the inner
    [tensor_curry (ch_mor convex)] (one1 ⊗p prom u). *)
Lemma der_Step_loop_p_one_prom_u_E
    (u : L_loop) (Hu : cone_norm u <= 1) :
  Lfun (der L_loop)
       (@Step_loop_p R Ar R_obj
          R_carrier_eq R_carrier_meas R_to_carrier_meas
          p Hp_ge0 Hp_le1 one1 (prom u))
  = Lfun (tensor_curry (ch_mor (convex_combination (eD' then_e)
                                  (eD' else_e) Hp_ge0 Hp_le1)))
         (ptensor one1 (prom u)).
Proof.
rewrite (Step_loop_p_one_prom_u_E Hu).
exact: (der_prom (B := L_loop) _ (cone_norm_K_alp_le1 Hu)).
Qed.

(** Eval-at-one1 form. *)
Lemma linhom_fun_der_Step_loop_p_one1_u_E
    (u : L_loop) (Hu : cone_norm u <= 1) :
  linhom_fun
    (Lfun (der L_loop) (@Step_loop_p R Ar R_obj
                           R_carrier_eq R_carrier_meas R_to_carrier_meas
                           p Hp_ge0 Hp_le1 one1 (prom u)))
    (one1 : cone_one_car Ar)
  = Lfun (ch_mor (convex_combination (eD' then_e) (eD' else_e)
                                     Hp_ge0 Hp_le1))
         (@at_outer_pt_u R Ar L_loop u).
Proof.
rewrite (der_Step_loop_p_one_prom_u_E Hu).
rewrite /at_outer_pt_u.
exact: (tensor_curryE
          (B := coalg_obj (EM_prod (EM_term : Coalgebra Ar) funT_loop))
          (C := coalg_obj (EM_term : Coalgebra Ar))
          (D := coalg_obj (Tobj (EM_term : Coalgebra Ar)))
          (ch_mor (convex_combination (eD' then_e) (eD' else_e)
                                      Hp_ge0 Hp_le1))
          (ptensor one1 (prom u)) one1).
Qed.

(** Combined cone_one_car-level form: the same eval-at-one1, post-der,
    written as a precone_add of scaled branches. *)
Lemma der_cone_one_linhom_der_Step_E_u
    (u : L_loop) (Hu : cone_norm u <= 1) :
  Lfun (der (cone_one_car Ar))
       (linhom_fun
          (Lfun (der L_loop)
                (@Step_loop_p R Ar R_obj
                   R_carrier_eq R_carrier_meas R_to_carrier_meas
                   p Hp_ge0 Hp_le1 one1 (prom u)))
          (one1 : cone_one_car Ar))
  = Lfun (der (cone_one_car Ar))
         (precone_add
            (precone_scale (NngNum Hp_ge0)
              (Lfun (ch_mor (eD' then_e))
                    (@at_outer_pt_u R Ar L_loop u)))
            (precone_scale (NngNum (onem_ge0 p Hp_le1))
              (Lfun (ch_mor (eD' else_e))
                    (@at_outer_pt_u R Ar L_loop u)))).
Proof.
rewrite (linhom_fun_der_Step_loop_p_one1_u_E Hu).
rewrite (Lfun_ch_mor_convex_at_outer_pt_u_E Hu).
have Hnorm : cone_norm
                (Lfun (convex_icones (eD' then_e) (eD' else_e)
                                     Hp_ge0 Hp_le1)
                      (@at_outer_pt_u R Ar L_loop u)) <= 1.
  apply: le_trans (cones_hom_norm_le1 _ _) _.
  exact: cone_norm_at_outer_pt_u_step.
rewrite (der_prom (B := cone_one_car Ar) _ Hnorm).
exact: (Lfun_convex_icones_at_outer_pt_u_E Hu).
Qed.

(** ** §6 — Per-iterate cone_one_car decomposition via witness u *)

Lemma F_arr_loop_p_S_E_via_u
    (u : L_loop) (Hu : cone_norm u <= 1) :
  Lfun (der (cone_one_car Ar))
       (linhom_fun
          (Lfun (der L_loop)
                (@Step_loop_p R Ar R_obj
                   R_carrier_eq R_carrier_meas R_to_carrier_meas
                   p Hp_ge0 Hp_le1 one1 (prom u)))
          (one1 : cone_one_car Ar))
  = precone_add
      (precone_scale (NngNum Hp_ge0) (one1 : cone_one_car Ar))
      (precone_scale (NngNum (onem_ge0 p Hp_le1))
        (@F_lift_loop R Ar u)).
Proof.
rewrite (der_cone_one_linhom_der_Step_E_u Hu).
have [_ HderD HderZ] :=
  cones_hom_linear
    (mcones_hom_cones (icones_hom_mcones (der (cone_one_car Ar)))).
rewrite HderD !HderZ.
rewrite (der_Lfun_ch_mor_then_e_at_outer_pt_u_E Hu).
rewrite (der_Lfun_ch_mor_else_e_at_outer_pt_u_E Hu).
by [].
Qed.

(** ** §7 — Kleene chain: every iterate is a [prom] (with norm bound)

    Mirror of [ex_loop_arr.v]'s [kleene_arr_loop_is_prom]. *)

Lemma Step_loop_p_of_prom_norm
    (u : L_loop) (Hu : cone_norm u <= 1) :
  exists v : L_loop,
    @Step_loop_p R Ar R_obj
       R_carrier_eq R_carrier_meas R_to_carrier_meas
       p Hp_ge0 Hp_le1 one1 (prom u) = prom v /\ cone_norm v <= 1.
Proof.
exists (Lfun (tensor_curry (ch_mor (convex_combination (eD' then_e)
                                      (eD' else_e) Hp_ge0 Hp_le1)))
             (ptensor one1 (prom u))).
split.
- exact: Step_loop_p_one_prom_u_E Hu.
- exact: cone_norm_K_alp_le1 Hu.
Qed.

Lemma kleene_arr_loop_p_is_prom (n : nat) :
  exists u : L_loop,
    @kleene_arr_loop_p R Ar R_obj
      R_carrier_eq R_carrier_meas R_to_carrier_meas
      p Hp_ge0 Hp_le1 n = prom u /\ cone_norm u <= 1.
Proof.
elim: n => [ |n IH].
- exists (precone_zero : L_loop); split.
  + by rewrite kleene_arr_loop_p_0.
  + by rewrite cone_norm0 ler01.
- destruct IH as [u [Hu_eq Hu_norm]].
  destruct (Step_loop_p_of_prom_norm Hu_norm) as [v [Hv_eq Hv_norm]].
  exists v; split.
  + by rewrite kleene_arr_loop_p_S Hu_eq.
  + exact: Hv_norm.
Qed.

(** ** §8 — Per-iterate cone_one_car decomposition for F_arr_loop_p *)

Lemma F_lift_eq_F_arr_loop_p (n : nat) (u : L_loop)
    (Hu_eq : @kleene_arr_loop_p R Ar R_obj
                R_carrier_eq R_carrier_meas R_to_carrier_meas
                p Hp_ge0 Hp_le1 n = prom u)
    (Hu_norm : cone_norm u <= 1) :
  @F_lift_loop R Ar u =
  @F_arr_loop_p R Ar R_obj
    R_carrier_eq R_carrier_meas R_to_carrier_meas p Hp_ge0 Hp_le1 n.
Proof.
rewrite /F_lift_loop /F_arr_loop_p Hu_eq.
by rewrite (der_prom (B := L_loop) u Hu_norm).
Qed.

Lemma F_arr_loop_p_S_E (n : nat) :
  @F_arr_loop_p R Ar R_obj
    R_carrier_eq R_carrier_meas R_to_carrier_meas p Hp_ge0 Hp_le1 n.+1
  = precone_add
      (precone_scale (NngNum Hp_ge0) (one1 : cone_one_car Ar))
      (precone_scale (NngNum (onem_ge0 p Hp_le1))
        (@F_arr_loop_p R Ar R_obj
           R_carrier_eq R_carrier_meas R_to_carrier_meas
           p Hp_ge0 Hp_le1 n)).
Proof.
have [u [Hu_eq Hu_norm]] := kleene_arr_loop_p_is_prom n.
rewrite -[F_arr_loop_p _ _ _ n.+1]/(Lfun (der (cone_one_car Ar))
                                       (linhom_fun
                                          (Lfun (der L_loop)
                                                (@kleene_arr_loop_p R Ar R_obj
                                                   R_carrier_eq R_carrier_meas
                                                   R_to_carrier_meas
                                                   p Hp_ge0 Hp_le1 n.+1))
                                          (one1 : cone_one_car Ar))).
rewrite kleene_arr_loop_p_S Hu_eq.
rewrite (F_arr_loop_p_S_E_via_u Hu_norm).
by rewrite (F_lift_eq_F_arr_loop_p Hu_eq Hu_norm).
Qed.

(** ** §9 — Per-iterate SCALAR recurrence

    [(c1_val (F_arr_loop_p n+1))%:num = p + (1-p) * (c1_val (F_arr_loop_p n))%:num]. *)

Lemma F_arr_loop_p_S_c1_val (n : nat) :
  (c1_val (@F_arr_loop_p R Ar R_obj
             R_carrier_eq R_carrier_meas R_to_carrier_meas
             p Hp_ge0 Hp_le1 n.+1))%:num
  = (p + (1 - p) * (c1_val (@F_arr_loop_p R Ar R_obj
                              R_carrier_eq R_carrier_meas R_to_carrier_meas
                              p Hp_ge0 Hp_le1 n))%:num)%R.
Proof.
rewrite F_arr_loop_p_S_E.
rewrite /precone_add /precone_scale /=.
by rewrite mulr1.
Qed.

(** ** §10 — Closed-form scalar mass:
    [(c1_val (F_arr_loop_p n))%:num = 1 - (1 - p)^n]. *)

Lemma F_arr_loop_p_c1_val_closed (n : nat) :
  (c1_val (@F_arr_loop_p R Ar R_obj
             R_carrier_eq R_carrier_meas R_to_carrier_meas
             p Hp_ge0 Hp_le1 n))%:num
  = (1 - (1 - p)^+n)%R.
Proof.
elim: n => [ |n IH]; first by rewrite F_arr_loop_p_0_E expr0 subrr.
rewrite F_arr_loop_p_S_c1_val IH.
rewrite exprSr mulrBr mulr1 addrA.
have eq1 : (p + (1 - p) = 1)%R by rewrite addrCA subrr addr0.
by rewrite eq1 mulrC.
Qed.

(** ** §11 — Monotonicity of F_arr_loop_p (in the precone order)

    By induction; uses linearity of [Lfun (der ...) ] and [linhom_fun]. *)

Lemma F_arr_loop_p_chain (n : nat) :
  precone_le (@F_arr_loop_p R Ar R_obj
                R_carrier_eq R_carrier_meas R_to_carrier_meas
                p Hp_ge0 Hp_le1 n)
             (@F_arr_loop_p R Ar R_obj
                R_carrier_eq R_carrier_meas R_to_carrier_meas
                p Hp_ge0 Hp_le1 n.+1).
Proof.
apply/c1_leE.
rewrite !F_arr_loop_p_c1_val_closed.
rewrite lerD2l lerNl opprK exprSr.
have H1mp_ge0 : (0 <= 1 - p)%R by exact: onem_ge0.
have H1mp_le1 : (1 - p <= 1)%R by rewrite lerBlDr lerDl.
have Hn_ge0 : (0 <= (1 - p)^+n)%R by rewrite exprn_ge0.
rewrite -[X in _ <= X]mul1r mulrC mul1r.
by apply: ler_piMl.
Qed.

Lemma F_arr_loop_p_ball (n : nat) :
  cone_norm (@F_arr_loop_p R Ar R_obj
                R_carrier_eq R_carrier_meas R_to_carrier_meas
                p Hp_ge0 Hp_le1 n) <= 1.
Proof.
rewrite /cone_norm /= /c1_norm F_arr_loop_p_c1_val_closed.
rewrite lerBlDr lerDl.
by rewrite exprn_ge0 ?onem_ge0.
Qed.

(** ** §12 — Sup of the F_arr_loop_p chain at the cone_one_car level *)

Definition F_arr_loop_p_sup : cone_one_car Ar :=
  c1_sup_ball (@F_arr_loop_p_chain) (@F_arr_loop_p_ball).

Lemma F_arr_loop_p_sup_E :
  (c1_val F_arr_loop_p_sup)%:num =
  sup [set (c1_val (@F_arr_loop_p R Ar R_obj
                      R_carrier_eq R_carrier_meas R_to_carrier_meas
                      p Hp_ge0 Hp_le1 n))%:num | n in [set: nat]].
Proof. exact: c1_sup_ball_E. Qed.

(** ** §13 — Convergence of the scalar chain

    By [nondecreasing_cvgn]: the chain [n ↦ (c1_val (F_arr_loop_p n))%:num]
    is nondecreasing (from F_arr_loop_p_chain) and bounded (by 1, from
    F_arr_loop_p_ball).  Its limit equals its supremum. *)

Lemma F_arr_loop_p_chain_homo :
  {homo (fun n => (c1_val (@F_arr_loop_p R Ar R_obj
                             R_carrier_eq R_carrier_meas R_to_carrier_meas
                             p Hp_ge0 Hp_le1 n))%:num)
   : n m / (n <= m)%N >-> (n <= m)%R}.
Proof.
apply/nondecreasing_seqP => n.
have /c1_leE := @F_arr_loop_p_chain n.
by [].
Qed.

Lemma F_arr_loop_p_chain_ub :
  has_ubound (range (fun n => (c1_val (@F_arr_loop_p R Ar R_obj
                                         R_carrier_eq R_carrier_meas
                                         R_to_carrier_meas
                                         p Hp_ge0 Hp_le1 n))%:num)).
Proof.
exists 1 => x [n _ <-].
have := @F_arr_loop_p_ball n.
by rewrite /cone_norm /= /c1_norm.
Qed.

(** ** §14 *)

(** Headline 1 — when [p > 0], the [c1_val] of the chain sup is 1.

    By [nondecreasing_cvgn], the chain converges to the sup; by closed-
    form expression, it also converges to [1] (since [(1-p)^n → 0]); by
    Hausdorff-uniqueness, sup = 1. *)
Theorem ex_almost_loop_p_arr_mass_one_if_pos :
  (0 < p)%R ->
  (c1_val F_arr_loop_p_sup)%:num = 1%R.
Proof.
move=> Hp_pos.
rewrite F_arr_loop_p_sup_E.
have sup_cvg := nondecreasing_cvgn F_arr_loop_p_chain_homo
                                    F_arr_loop_p_chain_ub.
have eq_extr :
  (fun n => (c1_val (@F_arr_loop_p R Ar R_obj
                       R_carrier_eq R_carrier_meas R_to_carrier_meas
                       p Hp_ge0 Hp_le1 n))%:num)
  = (fun n => (1 - (1 - p)^+n)%R).
  by apply: funext => n; exact: F_arr_loop_p_c1_val_closed.
have closed_cvg :
  (fun n => (c1_val (@F_arr_loop_p R Ar R_obj
                       R_carrier_eq R_carrier_meas R_to_carrier_meas
                       p Hp_ge0 Hp_le1 n))%:num)
    x @[x --> \oo] --> (1%R : R^o).
  rewrite eq_extr.
  have step2_cvg : (((1 - p) ^+ n)%R : R^o) @[n --> \oo] --> (0%R : R^o).
    apply: cvg_expr.
    have H1mp_ge0 : (0 <= 1 - p)%R by exact: onem_ge0.
    rewrite ger0_norm //.
    by rewrite ltrBlDr -ltrBlDl subrr.
  have step1_cvg : (fun _ : nat => (1%R : R^o)) x @[x --> \oo] --> (1%R : R^o)
    by exact: cvg_cst.
  have step3 := cvgB step1_cvg step2_cvg.
  have HF : Filter (@eventually) by exact: eventually_filter.
  have step3' := step3 HF.
  move: step3'.
  have ->: ((fun (_ : nat) => (1 : R^o)) - [eta GRing.exp (1 - p)])%R
         = (fun n => (1 - (1-p)^+n)%R) by [].
  have to_one : (1 - 0 : R^o)%R = 1%R by rewrite subr0.
  by rewrite to_one.
exact: (@cvg_unique R^o (@Rhausdorff R) _ _ _ _ sup_cvg closed_cvg).
Qed.

(** Headline 2 — when [p = 0], the [c1_val] of the chain sup is 0. *)
Theorem ex_almost_loop_p_arr_mass_zero_if_zero :
  p = 0%R ->
  (c1_val F_arr_loop_p_sup)%:num = 0%R.
Proof.
move=> Hp_zero.
rewrite F_arr_loop_p_sup_E.
have sup_cvg := nondecreasing_cvgn F_arr_loop_p_chain_homo
                                    F_arr_loop_p_chain_ub.
have eq_extr :
  (fun n => (c1_val (@F_arr_loop_p R Ar R_obj
                       R_carrier_eq R_carrier_meas R_to_carrier_meas
                       p Hp_ge0 Hp_le1 n))%:num)
  = (fun _ : nat => 0%R).
  apply: funext => n; rewrite F_arr_loop_p_c1_val_closed Hp_zero.
  by rewrite subr0 expr1n subrr.
have zero_cvg :
  (fun n => (c1_val (@F_arr_loop_p R Ar R_obj
                       R_carrier_eq R_carrier_meas R_to_carrier_meas
                       p Hp_ge0 Hp_le1 n))%:num)
    x @[x --> \oo] --> (0%R : R^o).
  rewrite eq_extr.
  exact: (@cvg_cst _ (0%R : R^o) nat \oo eventually_filter).
exact: (@cvg_unique R^o (@Rhausdorff R) _ _ _ _ sup_cvg zero_cvg).
Qed.

End ExAlmostLoopStep.

Arguments F_arr_loop_p_sup {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}
  p Hp_ge0 Hp_le1.
Arguments ex_almost_loop_p_arr_mass_one_if_pos
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} p Hp_ge0 Hp_le1.
Arguments ex_almost_loop_p_arr_mass_zero_if_zero
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} p Hp_ge0 Hp_le1.
