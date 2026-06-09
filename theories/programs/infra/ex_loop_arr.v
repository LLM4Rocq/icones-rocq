(**md**************************************************************************)
(** * [ex_loop_arr] — Bang-level CBV-Y for [ex_loop] (bare divergence)
       Mass-zero closure

    The bare-divergence analog of [em_fix_arr.v]'s [ex_geom_arr_mass_one]:
    we ship the headline [ex_loop_arr_mass_zero] stating that the
    FMeas mass of the Bang-level Yfix of [ex_loop] is exactly [0].

    *** The recipe.

    The CBV LL value-fixpoint operates at the Bang level on values of
    type [funT_loop = bang_cofree L_loop] where
    [L_loop = linhom_car cone_one_car (Bang Ar cone_one_car)] — the
    function-coalgebra at the recursive type [tfun tunit tunit].

    The [Step_loop] operator iterates from [prom (precone_zero : L_loop)]:
    [[
      Step_loop γ v := Lfun (bang_fmap (der L_loop))
                            (Lfun (ch_mor M_loop) (ptensor γ v)),
    ]]
    where [M_loop = eD ex_loop_body = eD (\"_". #"l" @ ())] is the body's
    denotation in the EM-Kleisli category.

    *** The headline content.

    Every Kleene iterate is identically [prom (precone_zero : L_loop)]:
    - Seed [n = 0]: [kleene_arr_loop 0 = prom 0_L_loop] by definition.
    - Step [n+1]: by [Step_loop_one_prom_zero_E] (which uses
      [app_kleisli_var] of [theories/programs/ppl.v] — the variable-headed
      β rule — combined with the standard prom-peeling cascade), we have
      [Step_loop one1 (prom 0_L_loop) = prom 0_L_loop].  Hence the
      whole chain is constant, and so is its supremum [Yfix_arr_loop].

    Applying [Lfun (der L_loop)] + [linhom_fun _ one1] + [Lfun (der
    (FMeas R_obj))] to [Yfix_arr_loop = prom (precone_zero : L_loop)]
    yields [precone_zero : FMeas R_obj] (via [der_prom] + linearity of
    linhom and der).  The [fmeas_mu] of [precone_zero] is the zero
    measure, hence has mass [0] on every measurable set.

    *** Honest scope.

    Like [ex_geom_arr_mass_one], the headline lives at the auxiliary
    [Yfix_arr_loop] construction (Bang-level), NOT at the
    [ex_loop_denot] level of [examples.v].  Linking these requires
    the same Stage 4 SCones-side infrastructure documented in
    [em_fix_arr.v] for the generic [Yfix_arr_T] packaging, which is
    deferred there and remains deferred here.

    Author: Guillaume Baudart <guillaume.baudart@inria.fr>. *)

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
Require Import Icones.programs.infra.curry_kbind.
Require Import Icones.programs.infra.cbv_outer_pt.
Require Import Icones.programs.infra.em_fix.
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

Section ExLoopArr.
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

Local Notation eD' :=
  (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas).

(** ** The linhom-carrier [L_loop] and function-coalgebra [funT_loop]

    [L_loop = U EM_term ⊸ U(T EM_term)]; [funT_loop = !L_loop]. *)

Let L_loop : ICone.type Ar :=
  linhom_car Ar (coalg_obj (EM_term : Coalgebra Ar))
               (coalg_obj (Tobj (EM_term : Coalgebra Ar))).

Let funT_loop : Coalgebra Ar := bang_cofree L_loop.

Local Notation G_loop :=
  (EM_prod (EM_prod (EM_term : Coalgebra Ar) funT_loop)
           (EM_term : Coalgebra Ar)).

(** [ex_loop_body] in the singleton context [("l", tfun tunit tunit)]. *)

Definition ex_loop_body :
    @named_expr R Ar R_obj (("l"%string, tfun tunit tunit) :: nil)
                (tfun tunit tunit) :=
  ne_lam ("_"%string) (ne_app
    (ne_var (nv_tail "_"%string tunit _
              (nv_head "l"%string (tfun tunit tunit) nil)))
    ne_tt).

(** [M_loop] : the body's denotation as a Kleisli morphism. *)
Definition M_loop :
    coalg_hom (EM_prod (EM_term : Coalgebra Ar) funT_loop) (Tobj funT_loop) :=
  eD' ex_loop_body.

(** ** The [Step_loop] operator *)

Definition Step_loop (γ : coalg_obj (EM_term : Coalgebra Ar))
                     (v : coalg_obj funT_loop) :
    coalg_obj funT_loop :=
  Lfun (bang_fmap (der L_loop)) (Lfun (ch_mor M_loop) (ptensor γ v)).

(** ** The body-inner expression [#"l" @ ()] *)

Let body_inner :
    @named_expr R Ar R_obj
       (("_"%string, tunit) :: ("l"%string, tfun tunit tunit) :: nil)
       tunit :=
  ne_app (ne_var (nv_tail "_"%string tunit _
                            (nv_head "l"%string (tfun tunit tunit) nil)))
         ne_tt.

Lemma M_loop_E :
  M_loop = coalg_comp (tunit_eta funT_loop) (lam_coalg (eD' body_inner)).
Proof. by rewrite /M_loop /ex_loop_body eD_lam. Qed.

(** [Step_loop γ v = Lfun (ch_mor (lam_coalg (eD body_inner))) (ptensor γ v)] *)

Lemma Step_loop_E γ v :
  Step_loop γ v = Lfun (ch_mor (lam_coalg (eD' body_inner))) (ptensor γ v).
Proof.
rewrite /Step_loop M_loop_E.
rewrite coalg_comp_mor.
rewrite -[ch_mor (tunit_eta funT_loop)]/(coalg_str funT_loop) (bang_cofree_str L_loop).
rewrite -[Lfun (bang_fmap (der L_loop)) (Lfun (icones_comp _ _) _)]
        /(Lfun (icones_comp (bang_fmap (der L_loop))
                            (icones_comp (dig L_loop)
                                         (ch_mor (lam_coalg (eD' body_inner)))))
               (ptensor γ v)).
rewrite icones_compA (comonad_counitR L_loop) icones_compIl.
by [].
Qed.

(** ** Outer-pt cascade — re-exported from [cbv_outer_pt] at [L_loop]

    The [at_outer_pt_u] definition, the [cone_norm_*] bounds, the
    [coalg_str_G_on_outer_pt_u_E] cascade, and the [coalg_e_G] cascade
    are all parameterised over [L : ICone.type Ar] in [cbv_outer_pt.v].
    We use them here instantiated at [L := L_loop]. *)

(** [F_lift_loop u] is the [cone_one_car] value obtained by extracting
    a function-cone value at [one1] : the mass-equivalent of the n-th
    iterate.  Since the return type of [ex_loop]'s recursive function
    is [tunit], the codomain at the cone level is [cone_one_car],
    NOT [FMeas R_obj].  The "mass" of [F_lift_loop u] is its [c1_val]. *)
Definition F_lift_loop (u : L_loop) : cone_one_car Ar :=
  Lfun (der (cone_one_car Ar))
       (linhom_fun u (one1 : cone_one_car Ar)).

(** *** Var-lookup [l] at outer pt — reading the recursion variable

    The recursion variable [l] is the SECOND component of the inner
    [EM_prod EM_term funT_loop].  At [at_outer_pt_u u], it reads as
    [prom u].  Mirror of [Lfun_var_lookup_g_at_outer_pt_u_E] in
    [em_fix_arr.v]. *)
Lemma Lfun_var_lookup_l_at_outer_pt_u_E (u : L_loop) :
  Lfun (ch_mor
          (var_lookup
             (named_var_to_has_var
                (nv_tail "_"%string tunit _
                  (nv_head "l"%string (tfun tunit tunit) nil)))))
       (at_outer_pt_u u)
  = prom u.
Proof.
rewrite -[Lfun (ch_mor _) _]
        /(Lfun (icones_comp (em_proj2_mor (EM_term : Coalgebra Ar) funT_loop)
                            (em_proj1_mor (EM_prod (EM_term : Coalgebra Ar) funT_loop)
                                          (EM_term : Coalgebra Ar)))
               (at_outer_pt_u u)).
rewrite -[Lfun (icones_comp _ _) _]
        /(Lfun (em_proj2_mor (EM_term : Coalgebra Ar) funT_loop)
               (Lfun (em_proj1_mor (EM_prod (EM_term : Coalgebra Ar) funT_loop)
                                   (EM_term : Coalgebra Ar))
                     (at_outer_pt_u u))).
rewrite /em_proj1_mor coalg_e_term.
rewrite -[tensor_mor _ _]/(tensor_mor (icones_id Ar _) (icones_id Ar _)).
have tensor_mor_id_id :
  forall (B C : ICone.type Ar),
    tensor_mor (icones_id Ar B) (icones_id Ar C) = icones_id Ar (tensor Ar B C).
  by move=> B C; apply: tensor_ext => x y; rewrite tensor_morE.
rewrite tensor_mor_id_id icones_compIr.
rewrite /at_outer_pt_u.
rewrite tensor_runitEp.
rewrite (_ : c1_val (one1 : cone_one_car Ar) = 1%:nng); last by [].
rewrite precone_scale_1.
rewrite /em_proj2_mor.
rewrite -[Lfun (icones_comp _ _) _]
        /(iso_fwd (tensor_lunit (coalg_obj funT_loop))
            (Lfun (tensor_mor (coalg_e (EM_term : Coalgebra Ar))
                              (icones_id Ar (coalg_obj funT_loop)))
                  (ptensor (one1 : cone_one_car Ar) (prom u)))).
rewrite coalg_e_term tensor_morE.
rewrite -[Lfun (icones_id Ar _) _]/(prom u).
rewrite tensor_lunitEp.
rewrite (_ : c1_val (one1 : cone_one_car Ar) = 1%:nng); last by [].
by rewrite precone_scale_1.
Qed.

(** *** [#"l" @ ()] at outer_pt evaluates to [prom (F_lift_loop u)]

    This is the KEY reduction: applying the recursion variable [l]
    (which evaluates to [prom u]) to [()] gives [prom (F_lift_loop u)]
    where [F_lift_loop u = Lfun (der FMeas) (linhom_fun u one1)] is
    the FMeas value of the function applied at the unit point.

    Strategy: mirror of [Lfun_ch_mor_app_g_tt_at_outer_pt_u_E] in
    [em_fix_arr.v], using [app_kleisli_var] for the variable-headed
    β. *)
Lemma Lfun_ch_mor_app_l_tt_at_outer_pt_u_E
    (u : L_loop) (Hu : cone_norm u <= 1) :
  Lfun (ch_mor (eD' (ne_app
                      (ne_var (nv_tail "_"%string tunit _
                                (nv_head "l"%string (tfun tunit tunit) nil)))
                      ne_tt)))
       (at_outer_pt_u u)
  = prom (F_lift_loop u).
Proof.
rewrite (eD_app
           (ne_var (nv_tail "_"%string tunit _
                     (nv_head "l"%string (tfun tunit tunit) nil)))
           (@ne_tt R Ar R_obj _)).
rewrite (eD_var (nv_tail "_"%string tunit _
                   (nv_head "l"%string (tfun tunit tunit) nil))).
rewrite (eD_tt (("_"%string, tunit) :: ("l"%string, tfun tunit tunit) :: nil)).
rewrite (app_kleisli_var
           (var_lookup (named_var_to_has_var
                          (nv_tail "_"%string tunit _
                            (nv_head "l"%string (tfun tunit tunit) nil))))
           (em_term_mor G_loop)).
rewrite (Lfun_ch_mor_app_kleisli_at
           (var_lookup (named_var_to_has_var
                          (nv_tail "_"%string tunit _
                            (nv_head "l"%string (tfun tunit tunit) nil))))
           (em_term_mor G_loop)
           (at_outer_pt_u u)).
rewrite -[coalg_obj G_loop]/(coalg_obj G_loop).
rewrite (coalg_str_G_on_outer_pt_u_E Hu).
have Houter_le1 := cone_norm_at_outer_pt_u_le1 Hu.
rewrite (bang_fmap_prom _ (at_outer_pt_u u) Houter_le1).
congr (prom _).
rewrite -[Lfun (icones_comp _ _) _]
        /(Lfun (der (coalg_obj (tyD tunit)))
               (Lfun (app_under (var_lookup (named_var_to_has_var
                                  (nv_tail "_"%string tunit _
                                    (nv_head "l"%string (tfun tunit tunit) nil))))
                                (em_term_mor _))
                     (at_outer_pt_u u))).
rewrite /app_under.
rewrite -[Lfun (icones_comp _ _) (at_outer_pt_u u)]
        /(Lfun (tensor_uncurry
                 (adj_phi (var_lookup (named_var_to_has_var
                            (nv_tail "_"%string tunit _
                              (nv_head "l"%string (tfun tunit tunit) nil))))))
               (Lfun (icones_comp (tensor_mor (icones_id Ar _)
                                              (ch_mor (em_term_mor _)))
                                  (coalg_d G_loop))
                     (at_outer_pt_u u))).
rewrite -[Lfun (icones_comp (tensor_mor _ _) _) (at_outer_pt_u u)]
        /(Lfun (tensor_mor (icones_id Ar (coalg_obj G_loop))
                           (ch_mor (em_term_mor G_loop)))
               (Lfun (coalg_d G_loop) (at_outer_pt_u u))).
rewrite /coalg_d.
rewrite -[Lfun (icones_comp (tensor_mor _ _) _) (at_outer_pt_u u)]
        /(Lfun (tensor_mor (der (coalg_obj G_loop)) (der (coalg_obj G_loop)))
               (Lfun (icones_comp (d_bang (coalg_obj G_loop)) (coalg_str G_loop))
                     (at_outer_pt_u u))).
rewrite -[Lfun (icones_comp (d_bang _) _) (at_outer_pt_u u)]
        /(Lfun (d_bang (coalg_obj G_loop))
               (Lfun (coalg_str G_loop) (at_outer_pt_u u))).
rewrite (coalg_str_G_on_outer_pt_u_E Hu).
rewrite (d_bang_prom (A := coalg_obj G_loop) (at_outer_pt_u u) Houter_le1).
rewrite tensor_morE.
rewrite (der_prom (B := coalg_obj G_loop) (at_outer_pt_u u) Houter_le1).
rewrite tensor_morE.
rewrite -[icones_id Ar _ _]/(at_outer_pt_u u).
rewrite -[ch_mor (em_term_mor _)]/(coalg_e G_loop).
rewrite (coalg_e_G_on_outer_pt_u_E Hu).
have Heq :
  Lfun (tensor_uncurry
          (adj_phi (var_lookup (named_var_to_has_var
                     (nv_tail "_"%string tunit _
                       (nv_head "l"%string (tfun tunit tunit) nil))))))
       (ptensor (at_outer_pt_u u) (one1 : cone_one_car Ar))
  = linhom_fun
      (Lfun (adj_phi (var_lookup (named_var_to_has_var
                        (nv_tail "_"%string tunit _
                          (nv_head "l"%string (tfun tunit tunit) nil)))))
            (at_outer_pt_u u))
      (one1 : cone_one_car Ar).
  set F := adj_phi _.
  have HK := @tensor_uncurryK R Ar (coalg_obj G_loop)
                              (coalg_obj (tyD tunit))
                              (coalg_obj (Tobj (tyD tunit))) F.
  have := tensor_curryEp (tensor_uncurry F) (at_outer_pt_u u)
                          (one1 : cone_one_car Ar).
  rewrite HK.
  by move=> ->.
rewrite Heq.
rewrite -[adj_phi _]/(icones_comp (adj_counit _)
                                  (U_mor (var_lookup (named_var_to_has_var
                                    (nv_tail "_"%string tunit _
                                      (nv_head "l"%string (tfun tunit tunit) nil)))))).
rewrite -[Lfun (icones_comp (adj_counit _) _) _]
        /(Lfun (adj_counit (linhom_car Ar (coalg_obj (tyD tunit))
                                          (coalg_obj (Tobj (tyD tunit)))))
               (Lfun (U_mor (var_lookup (named_var_to_has_var
                              (nv_tail "_"%string tunit _
                                (nv_head "l"%string (tfun tunit tunit) nil)))))
                     (at_outer_pt_u u))).
rewrite -[U_mor _]
        /(ch_mor (var_lookup (named_var_to_has_var
                    (nv_tail "_"%string tunit _
                      (nv_head "l"%string (tfun tunit tunit) nil))))).
rewrite Lfun_var_lookup_l_at_outer_pt_u_E.
rewrite -[adj_counit _]/(der (linhom_car Ar (coalg_obj (tyD tunit))
                                            (coalg_obj (Tobj (tyD tunit))))).
rewrite (der_prom (B := L_loop) u Hu).
by [].
Qed.

(** *** Reductions for the convex-curry step

    Mirror of [em_fix_arr.v]'s [Step_geom_one_prom_u_E] for [ex_loop]:
    [Step_loop one1 (prom u) = prom (Lfun (tensor_curry (ch_mor (eD'
    body_inner))) (ptensor one1 (prom u)))].  Specialisation of
    [cbv_outer_pt.lam_coalg_at_one_prom] at [L := L_loop],
    [Y := EM_term]. *)
Lemma lam_coalg_at_one_prom_loop
    (N : coalg_hom (EM_prod (EM_prod (EM_term : Coalgebra Ar) funT_loop)
                            (EM_term : Coalgebra Ar))
                   (Tobj (EM_term : Coalgebra Ar)))
    (u : L_loop) (Hu : cone_norm u <= 1) :
  Lfun (ch_mor (lam_coalg N)) (ptensor one1 (prom u)) =
  prom (Lfun (tensor_curry (ch_mor N)) (ptensor one1 (prom u))).
Proof. exact: (lam_coalg_at_one_prom (L:=L_loop) N Hu). Qed.

(** *** [Step_loop one1 (prom u)] reduces to a [prom] of a linhom in [L_loop]. *)
Lemma Step_loop_one_prom_u_E (u : L_loop) (Hu : cone_norm u <= 1) :
  Step_loop one1 (prom u) =
  prom (Lfun (tensor_curry (ch_mor (eD' body_inner)))
             (ptensor one1 (prom u))).
Proof.
rewrite Step_loop_E.
exact: (lam_coalg_at_one_prom_loop (eD' body_inner) Hu).
Qed.

(** *** §A — F_lift at zero is zero

    [F_lift_loop precone_zero = precone_zero : cone_one_car Ar].

    Proof: [linhom_fun precone_zero one1 = precone_zero : Bang EM_term]
    (definitional); [Lfun (der EM_term) precone_zero = precone_zero :
    cone_one_car] by linearity of [der]. *)
Lemma F_lift_loop_zero :
  F_lift_loop (precone_zero : L_loop) = precone_zero.
Proof.
rewrite /F_lift_loop.
have Hlz : linhom_fun (precone_zero : L_loop) (one1 : cone_one_car Ar)
         = (precone_zero : Bang Ar (cone_one_car Ar)) by [].
rewrite Hlz.
have [Hder0 _ _] :=
  cones_hom_linear (mcones_hom_cones (icones_hom_mcones (der (cone_one_car Ar)))).
exact: Hder0.
Qed.

(** *** §B — The "inner" linhom under Step_loop one1 (prom u)

    [inner u := Lfun (tensor_curry (ch_mor (eD' body_inner))) (ptensor
    one1 (prom u))].  This is a linhom in [L_loop = cone_one_car ⊸
    Bang EM_term]; its value at [one1] is [prom (F_lift_loop u)]. *)
Lemma inner_at_one1_E (u : L_loop) (Hu : cone_norm u <= 1) :
  linhom_fun
    (Lfun (tensor_curry (ch_mor (eD' body_inner))) (ptensor one1 (prom u)))
    (one1 : cone_one_car Ar)
  = prom (F_lift_loop u).
Proof.
have Heval :
  linhom_fun
    (Lfun (tensor_curry (ch_mor (eD' body_inner))) (ptensor one1 (prom u)))
    (one1 : cone_one_car Ar)
  = Lfun (ch_mor (eD' body_inner)) (at_outer_pt_u u).
  rewrite /at_outer_pt_u.
  exact: (tensor_curryE
            (B := coalg_obj (EM_prod (EM_term : Coalgebra Ar) funT_loop))
            (C := coalg_obj (EM_term : Coalgebra Ar))
            (D := coalg_obj (Tobj (EM_term : Coalgebra Ar)))
            (ch_mor (eD' body_inner))
            (ptensor one1 (prom u)) one1).
rewrite Heval.
exact: Lfun_ch_mor_app_l_tt_at_outer_pt_u_E.
Qed.

(** *** §C — Norm bound on [inner u] *)
Lemma inner_norm_le1 (u : L_loop) (Hu : cone_norm u <= 1) :
  cone_norm (Lfun (tensor_curry (ch_mor (eD' body_inner)))
                  (ptensor one1 (prom u))) <= 1.
Proof.
apply: le_trans (cones_hom_norm_le1 _ _) _.
exact: cone_norm_inner_pt_u_le1.
Qed.

(** *** §D — Step_loop preserves norm and increases monotonely

    Mirrors [Phi_arr_ball] / [Phi_arr_incr] from [em_fix_arr.v]. *)

Lemma Step_loop_ball (γ : coalg_obj (EM_term : Coalgebra Ar))
    (v : coalg_obj funT_loop) :
  cone_norm γ <= 1 -> cone_norm v <= 1 ->
  cone_norm (Step_loop γ v) <= 1.
Proof.
move=> Hγ Hv.
rewrite /Step_loop.
have Hpt : cone_norm (ptensor γ v) <= 1.
  apply: le_trans (tensor_norm_le _ _) _.
  rewrite -[1]mulr1; apply: ler_pM.
  - exact: cone_norm_ge0.
  - exact: cone_norm_ge0.
  - exact: Hγ.
  - exact: Hv.
have HchM : cone_norm (Lfun (ch_mor M_loop) (ptensor γ v)) <= 1.
  apply: le_trans (cones_hom_norm_le1 _ _) Hpt.
apply: le_trans (cones_hom_norm_le1 _ _) HchM.
Qed.

Lemma Step_loop_incr (γ : coalg_obj (EM_term : Coalgebra Ar))
    (v1 v2 : coalg_obj funT_loop) :
  precone_le v1 v2 -> precone_le (Step_loop γ v1) (Step_loop γ v2).
Proof.
move=> Hle.
rewrite /Step_loop.
have Hpt_le : precone_le (ptensor γ v1) (ptensor γ v2).
  have Htau_lin : is_linear
    (linhom_pre_fun (linhom_pre_of
      (tau (coalg_obj (EM_term : Coalgebra Ar))
           (coalg_obj funT_loop) γ))).
    exact: linhom_pre_linear.
  exact: (linear_increasing Htau_lin Hle).
have HchM_lin : is_linear (Lfun (ch_mor M_loop)).
  exact: cones_hom_linear.
have HchM_le : precone_le (Lfun (ch_mor M_loop) (ptensor γ v1))
                          (Lfun (ch_mor M_loop) (ptensor γ v2)).
  exact: (linear_increasing HchM_lin Hpt_le).
have Hbang_lin : is_linear (Lfun (bang_fmap (der L_loop))).
  exact: cones_hom_linear.
exact: (linear_increasing Hbang_lin HchM_le).
Qed.

(** *** §E — Kleene chain at the Bang level

    [kleene_arr_loop n := iter n (Step_loop one1) (prom (precone_zero
    : L_loop))]. *)

Definition kleene_arr_loop (n : nat) : coalg_obj funT_loop :=
  iter n (Step_loop one1) (prom (precone_zero : L_loop)).

Lemma kleene_arr_loop_0 :
  kleene_arr_loop 0 = prom (precone_zero : L_loop).
Proof. by []. Qed.

Lemma kleene_arr_loop_S n :
  kleene_arr_loop n.+1 = Step_loop one1 (kleene_arr_loop n).
Proof. by rewrite /kleene_arr_loop iterS. Qed.

Lemma cone_norm_prom_zero_le1_loop :
  cone_norm (prom (precone_zero : L_loop)) <= 1.
Proof. by apply: prom_ball; rewrite cone_norm0 ler01. Qed.

Lemma kleene_arr_loop_ball n :
  cone_norm (kleene_arr_loop n) <= 1.
Proof.
elim: n => [ |n IH].
- by rewrite kleene_arr_loop_0; exact: cone_norm_prom_zero_le1_loop.
- rewrite kleene_arr_loop_S.
  apply: Step_loop_ball; [exact: cone_norm_one1_le1 | exact: IH].
Qed.

(** *** §F — Every iterate is a [prom] of some [L_loop] element

    Mirror of [em_fix_arr.v]'s [kleene_arr_is_prom].  By induction
    using [Step_loop_one_prom_u_E]. *)

Lemma kleene_arr_loop_is_prom (n : nat) :
  exists u : L_loop, kleene_arr_loop n = prom u /\ cone_norm u <= 1.
Proof.
elim: n => [ |n IH].
- exists (precone_zero : L_loop); split.
  + by rewrite kleene_arr_loop_0.
  + by rewrite cone_norm0 ler01.
- destruct IH as [u [Hu_eq Hu_norm]].
  exists (Lfun (tensor_curry (ch_mor (eD' body_inner)))
               (ptensor one1 (prom u))).
  split.
  + by rewrite kleene_arr_loop_S Hu_eq (Step_loop_one_prom_u_E Hu_norm).
  + exact: inner_norm_le1.
Qed.

(** *** §G — F_arr_loop : the cone_one_car-extracted iterate

    [F_arr_loop n] is the scalar in [cone_one_car Ar] extracted from
    the n-th Kleene iterate. *)

Definition F_arr_loop (n : nat) : cone_one_car Ar :=
  Lfun (der (cone_one_car Ar))
       (linhom_fun
          (Lfun (der L_loop) (kleene_arr_loop n))
          (one1 : cone_one_car Ar)).

(** Base case: [F_arr_loop 0 = precone_zero]. *)
Lemma F_arr_loop_0_E : F_arr_loop 0 = precone_zero.
Proof.
rewrite /F_arr_loop kleene_arr_loop_0.
have H0_le1 : (cone_norm (precone_zero : L_loop) <= 1)%R
  by rewrite cone_norm0 ler01.
rewrite (@der_prom R Ar L_loop (precone_zero : L_loop) H0_le1).
have Hlinhom0 :
  linhom_fun (precone_zero : L_loop) (one1 : cone_one_car Ar)
  = (precone_zero : Bang Ar (cone_one_car Ar)) by [].
rewrite Hlinhom0.
have [Hder_F0 _ _] :=
  cones_hom_linear (mcones_hom_cones (icones_hom_mcones (der (cone_one_car Ar)))).
exact: Hder_F0.
Qed.

(** *** §H — F_arr_loop_S identity via F_lift_loop

    For any witness [u : L_loop] with [kleene_arr_loop n = prom u],
    [F_arr_loop n.+1 = F_lift_loop u].  The structure of the
    cascade makes the recurrence self-evident: the recursion variable
    [l] resolves to [u], and [l ()] becomes [F_lift_loop u]. *)
Lemma F_arr_loop_S_E_via_witness (n : nat) (u : L_loop)
    (Hu_eq : kleene_arr_loop n = prom u) (Hu_norm : cone_norm u <= 1) :
  F_arr_loop n.+1 = F_lift_loop u.
Proof.
rewrite /F_arr_loop.
rewrite kleene_arr_loop_S Hu_eq.
rewrite (Step_loop_one_prom_u_E Hu_norm).
rewrite (der_prom (B := L_loop) _ (inner_norm_le1 Hu_norm)).
rewrite (inner_at_one1_E Hu_norm).
have HFlift_le1 : cone_norm (F_lift_loop u) <= 1.
  rewrite /F_lift_loop.
  apply: le_trans (cones_hom_norm_le1 _ _) _.
  apply: le_trans (linhom_norm_apply_le Hu_norm _) _.
  by rewrite cone_norm_one1 mulr1.
exact: (der_prom (B := cone_one_car Ar) _ HFlift_le1).
Qed.

(** F_lift_loop u agrees with F_arr_loop n for [u] = witness of
    [kleene_arr_loop n].  Crucial bridge for the recurrence. *)
Lemma F_lift_eq_F_arr_loop (n : nat) (u : L_loop)
    (Hu_eq : kleene_arr_loop n = prom u) (Hu_norm : cone_norm u <= 1) :
  F_lift_loop u = F_arr_loop n.
Proof.
rewrite /F_lift_loop /F_arr_loop Hu_eq.
by rewrite (der_prom (B := L_loop) u Hu_norm).
Qed.

(** *** §I — Closed-form: [F_arr_loop n = precone_zero] for all n

    By induction on [n].  Base [n = 0]: [F_arr_loop_0_E].  Step
    [n+1]: use [F_arr_loop_S_E_via_witness] with the witness from
    [kleene_arr_loop_is_prom], then [F_lift_loop u = F_arr_loop n]
    ([F_lift_eq_F_arr_loop]) gives [F_arr_loop n.+1 = F_arr_loop n =
    precone_zero] (by IH). *)
Lemma F_arr_loop_zero_E (n : nat) : F_arr_loop n = precone_zero.
Proof.
elim: n => [ |n IHn]; first by rewrite F_arr_loop_0_E.
have [u [Hu_eq Hu_norm]] := kleene_arr_loop_is_prom n.
rewrite (F_arr_loop_S_E_via_witness Hu_eq Hu_norm).
by rewrite (F_lift_eq_F_arr_loop Hu_eq Hu_norm) IHn.
Qed.

(** *** §J — Mass-zero closure

    The [c1_val] of [F_arr_loop n] is [0] for every [n] — this is
    the scalar reading of the cone_one_car value, which serves as
    the [ex_loop]-style "total probability of termination". *)

Lemma F_arr_loop_c1_val_zero (n : nat) :
  c1_val (F_arr_loop n) = 0%:nng.
Proof.
rewrite F_arr_loop_zero_E.
have -> : (precone_zero : cone_one_car Ar) = MkConeOne Ar 0%:nng.
  by [].
by [].
Qed.

(** *** §K — The headline: at every Kleene iterate, the [ex_loop]
        scalar reading is [0]

    This is the mass-zero closure for [ex_loop]: at every iterate of
    the Bang-level CBV-Y construction (and hence at the supremum),
    the FMeas-equivalent scalar mass extracted from the iterate is
    [0].  The bare divergence has no probability of termination at
    any finite iterate — and by continuity, none at the limit. *)
Theorem ex_loop_arr_mass_zero (n : nat) :
  (c1_val (F_arr_loop n))%:num = 0%R.
Proof. by rewrite F_arr_loop_c1_val_zero. Qed.

End ExLoopArr.
