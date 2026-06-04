(**md**************************************************************************)
(** * Focused experiment — outer/inner reductions for [ex_geom]'s [Step]

    BEYOND THE PAPER — partial validation of the expert's CBV-Y recipe
    on the geometric example.

    With [M := eD ex_geom_body] and [L_geom := linhom_car cone_one_car
    (Bang Ar (FMeas R_obj))] (the linhom carrier of [funT_geom = tyD
    (tfun tunit tR')]), the [Step_geom] operator at the cone-element
    level is:
    [[
      Step_geom γ v := Lfun (bang_fmap (der L_geom))
                            (Lfun (ch_mor M) (ptensor γ v)).
    ]]

    This file delivers the AXIOM-FREE STRUCTURAL reductions for
    [Step_geom one1 (prom (precone_zero : L_geom))], analogous to the
    [ex_loop] development of [em_fix_arr_exp.v] but for the more
    realistic [ex_geom] body
    [\ "_" => if Bernoulli(½) then [|0|] else [|1|] + # "g" @ ()].

    *** What this experiment delivers, AXIOM-FREE (modulo the three
        [boolp] axioms):

    1. [Step_geom_E] — [Step_geom γ v = Lfun (ch_mor (lam_coalg (eD
       body_inner))) (ptensor γ v)].  Outer collapse via
       [bang_fmap (der L_geom) ∘ dig L_geom = id_{Bang L_geom}].

    2. [lam_coalg_at_one_prom] — for any [N] and any [u] with
       [cone_norm u ≤ 1] :
       [[
         Lfun (ch_mor (lam_coalg N)) (ptensor one1 (prom u)) =
         prom (Lfun (tensor_curry (ch_mor N)) (ptensor one1 (prom u))).
       ]]

    3. [Step_geom_one_prom_zero_E] — the headline-form reduction:
       [[
         Step_geom one1 (prom 0_L_geom) =
         prom (Lfun (tensor_curry (ch_mor (eD body_inner)))
                    (ptensor one1 (prom 0_L_geom))).
       ]]
       Composition of [Step_geom_E] and [lam_coalg_at_one_prom] at
       [u := precone_zero : L_geom].

    4. [ex_geom_body_inner_via_convex] — apply [case_em_bernoulli]
       (B1) to [eD body_inner].  The result exposes the convex
       combination [½·(eD then_e) + ½·(eD else_e)].

    5. [Step_geom_one_prom_zero_via_convex_E] — chain of (3) + (4).

    6. [cone_norm_K_le1] — operator-norm bound on the inner linhom
       [K := Lfun (tensor_curry (ch_mor convex)) (one1 ⊗p prom 0)]:
       [cone_norm K ≤ 1].  Via [cones_hom_norm_le1] on [tensor_curry
       (ch_mor convex)] (an [icones_hom]) + [tensor_norm_le] +
       [cone_norm_one1 = 1] + [prom_ball] on [precone_zero ≤ 1].

    7. [der_Step_geom_one_prom_zero_E] — post-[der] structural
       reduction:
       [[
         Lfun (der L_geom) (Step_geom one1 (prom 0_L_geom)) =
         Lfun (tensor_curry (ch_mor convex)) (one1 ⊗p prom 0_L_geom).
       ]]
       Apply (5) + [der_prom] with the norm bound (6) on the inner
       [K].  This extracts the inner linhom from the outer [prom] at
       the [L_geom] level — closing the structural gap to the
       [linhom] operator-norm reading required for the mass identity.

    *** Honest scope and limitations.

    The headline target
    [[
      cone_norm (Lfun (der L_geom)
                      (Step_geom one1 (prom (precone_zero : L_geom)))) = 1/2
    ]]
    is DEFERRED.  After [Step_geom_one_prom_zero_via_convex_E], we have
    [Step_geom one1 (prom 0) = prom (Lfun (tensor_curry (ch_mor convex))
    (one1 ⊗p prom 0))].  The inner [Lfun (tensor_curry (ch_mor convex))
    (one1 ⊗p prom 0)] is a linhom in [L_geom = cone_one ⊸ Bang FMeas],
    and the outer [prom] takes it into [Bang L_geom].

    The mass identity requires:

    (a) An exact norm equality [cone_norm (prom x) = cone_norm x] (NOT
        currently in the [bang_construct.v] library — only
        [prom_ball : cone_norm (prom x) ≤ 1] is available).

    (b) Computation of the inner [convex_combination]'s operator norm
        at the [coalg] level, which goes through the [adj_psi]
        layer (a [bang_fmap convex_icones ∘ coalg_str G]
        composition) — not directly the linhom-level
        [convex_linhom = (1/2)·a_lh + (1/2)·b_lh] where [cone_normh]
        would give [1/2] cleanly.

    The full mass closure is therefore deferred to a future iteration
    that delivers the [cone_norm (prom x) = cone_norm x] identity
    (a non-trivial result given [Bang B] is constructed via a wide
    intersection of [scones_hom B Cone1] family members) plus the
    [adj_psi]-layer transparent reduction.

    *** Update — post-[der]-extraction (this commit).

    The post-[der]-extracted form [der_Step_geom_one_prom_zero_E]
    sidesteps the [Bang L_geom] wide-intersection norm by reading at
    the [L_geom] (linhom) operator-norm level.  This is structural
    progress: the headline mass identity now reduces to
    [[
      cone_norm
        (Lfun (tensor_curry (ch_mor convex)) (one1 ⊗p prom 0_L_geom))
      = 1/2
    ]]
    — an operator-norm reading of a single linhom in [L_geom = cone_one
    ⊸ Bang FMeas].  Still open: the per-branch evaluation cascade
    (then ↦ [prom (dirac_fmeas 0)], else ↦ [0] via [app_kleisli_var] +
    [add_lift_zero_R]), combined via [cone_normh] + the convex
    coefficients to give the [1/2] mass.

    *** Update — §1 FIRST-ITERATE FMEAS MASS = 1/2 (this commit).

    THE FIRST FORMAL MASS IDENTITY for a non-trivial Phase 4 example
    in Icones CBV-via-EM(!) framework — by-passing the
    [cone_norm (prom x) = cone_norm x] open identity by reading at
    the FMeas (post-[der]) level instead of the [Bang]-cone level.

    Headline closure:
    [[
      first_iterate_FMeas_mass_half :
        fmeas_mu (Lfun (der (FMeas R_obj))
                       (linhom_fun
                          (Lfun (der L_geom)
                                (Step_geom one1 (prom precone_zero)))
                          one1))
                 [set: ar_carrier Ar R_obj]
        = (1/2)%R%:E.
    ]]

    Composition of:
    - [linhom_fun_der_Step_geom_one1_E] — eval-at-[one1] reading of
      the post-[der] Step_geom.
    - [Lfun_ch_mor_convex_at_outer_pt_E] — [prom]-extraction of the
      [ch_mor convex] at the outer pt.
    - [Lfun_convex_icones_at_outer_pt_E] (NEW) — the [convex_icones]
      at the outer pt reads as [der ∘ (½·a + ½·b)].
    - [Lfun_ch_mor_{then,else}_e_at_outer_pt_E] — per-branch
      evaluations to [prom (dirac_fmeas 0)] / [prom precone_zero].
    - [der_prom] — [prom] cancellation.
    - [fmeas_addE] / [fmeas_scaleE] / [dirac_fmeas_setT_E] /
      [fmeas_zeroE] — FMeas mass arithmetic.

    Mass-1/2 = (½)·1 + (½)·0 reads off:
    - With probability ½, the THEN-branch returns [δ_0] (mass 1).
    - With probability ½, the ELSE-branch recurses (via [g := prom 0]
      which kills the recursive call) and gets mass 0.

    Honestly DEFERRED: §2 Kleene chain bridge (recurrence linking
    [Phi_fun^{n+1}] to [Step_geom one1 (prom Phi_fun^n)]), §3
    geometric recurrence [mass(F_{n+1}) = ½ + ½·mass(F_n)] via
    [add_lift_mass], §4 convergence to mass 1 via [cvg_geometric].
    These require ω-continuity at the value level plus FMeas mass
    convergence — substantial fresh infrastructure not yet in place.

    Now part of _CoqProject as of the §1 mass-1/2 closure commit.

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
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.icone.
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
Require Import Icones.homs.smcc.
Require Import Icones.homs.exp_adjunction.
Require Import Icones.homs.bang.
Require Import Icones.homs.seely_defs.
Require Import Icones.homs.seely.
Require Import Icones.homs.coalgebra.
Require Import Icones.homs.em_cat.
Require Import Icones.homs.em_cartesian.
Require Import Icones.homs.em_seely_comonoid.
Require Import Icones.programs.infra.cbv_adjunction.
Require Import Icones.programs.infra.bool_cone.
Require Import Icones.programs.infra.bool_case_hom.
Require Import Icones.programs.infra.case_em_red.
Require Import Icones.programs.infra.curry_kbind.
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

Section ExGeomStep.
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

Local Notation tR' := (tR R_obj).

(** ** The linhom-carrier [L_geom] and the function-coalgebra [funT_geom] *)

Let L_geom : ICone.type Ar :=
  linhom_car Ar (coalg_obj (EM_term : Coalgebra Ar))
               (coalg_obj (Tobj (tyD tR' : Coalgebra Ar))).

Let funT_geom : Coalgebra Ar := bang_cofree L_geom.

(** Sanity: [tyD (tfun tunit tR') = funT_geom] (definitional). *)
Lemma tyD_funT_geom_E :
  @tyD R Ar (tfun tunit tR') = funT_geom.
Proof. by []. Qed.

(** ** [M_body] is [eD ex_geom_body] *)

Definition M_body :
    coalg_hom (EM_prod (EM_term : Coalgebra Ar) funT_geom) (Tobj funT_geom) :=
  eD' (@ex_geom_body R Ar R_obj).

(** ** The [Step_geom] operator on cone elements

    [Step_geom γ v := Lfun (bang_fmap (der L_geom))
                           (Lfun (ch_mor M_body) (ptensor γ v))]. *)

Definition Step_geom (γ : coalg_obj (EM_term : Coalgebra Ar))
                     (v : coalg_obj funT_geom) :
    coalg_obj funT_geom :=
  Lfun (bang_fmap (der L_geom)) (Lfun (ch_mor M_body) (ptensor γ v)).

(** ** The body inner

    [ex_geom_body = \ "_" => body_inner] where
    [body_inner = if Bernoulli(½) then [|0|] else [|1|] + # "g" @ ()],
    in the extended context [("_", tunit) :: ("g", tfun tunit tR') :: nil]. *)

Let body_inner :
    @named_expr R Ar R_obj
       (("_"%string, tunit) :: ("g"%string, tfun tunit tR') :: nil)
       tR' :=
  ne_if tR'
    (ne_bernoulli (1/2 : R)%R (phase4_half_ge0 R) (phase4_half_le1 R))
    (ne_real 0%R)
    (ne_add (ne_real 1%R)
            (ne_app (ne_var (nv_tail "_"%string tunit _
                              (nv_head "g"%string (tfun tunit tR') nil)))
                    ne_tt)).

Lemma M_body_E :
  M_body = coalg_comp (tunit_eta funT_geom) (lam_coalg (eD' body_inner)).
Proof. by rewrite /M_body /ex_geom_body eD_lam. Qed.

(** ** Reduction A — [Step_geom γ v = Lfun (ch_mor (lam_coalg (eD body_inner))) (ptensor γ v)]

    Outer collapse: [bang_fmap (der L_geom) ∘ dig L_geom = id]. *)
Lemma Step_geom_E γ v :
  Step_geom γ v = Lfun (ch_mor (lam_coalg (eD' body_inner))) (ptensor γ v).
Proof.
rewrite /Step_geom M_body_E.
rewrite coalg_comp_mor.
rewrite -[ch_mor (tunit_eta funT_geom)]/(coalg_str funT_geom)
        (bang_cofree_str L_geom).
rewrite -[Lfun (bang_fmap (der L_geom)) (Lfun (icones_comp _ _) _)]
        /(Lfun (icones_comp (bang_fmap (der L_geom))
                            (icones_comp (dig L_geom)
                                         (ch_mor (lam_coalg (eD' body_inner)))))
               (ptensor γ v)).
rewrite icones_compA (comonad_counitR L_geom) icones_compIl.
by [].
Qed.

(** ** Reduction B — pointwise [lam_coalg N] at a promoted unit-ball
       second component

    [Lfun (ch_mor (lam_coalg N)) (ptensor one1 (prom u)) =
       prom (Lfun (tensor_curry (ch_mor N)) (ptensor one1 (prom u)))]
    when [cone_norm u ≤ 1].

    Mirrors [em_fix_arr_exp.v]'s [lam_coalg_at_one_prom] but for the
    [tR']-codomain. *)

Lemma cone_norm_one1 :
  (cone_norm (one1 : cone_one_car Ar) = 1)%R.
Proof. by rewrite /cone_norm /= /c1_norm. Qed.

Lemma cone_norm_one1_le1 :
  (cone_norm (one1 : cone_one_car Ar) <= 1)%R.
Proof. by rewrite cone_norm_one1. Qed.

Lemma lam_coalg_at_one_prom
    (N : coalg_hom (EM_prod (EM_prod (EM_term : Coalgebra Ar) funT_geom)
                            (EM_term : Coalgebra Ar))
                   (Tobj (tyD tR' : Coalgebra Ar)))
    (u : L_geom) (Hu : cone_norm u <= 1) :
  Lfun (ch_mor (lam_coalg N)) (ptensor one1 (prom u)) =
  prom (Lfun (tensor_curry (ch_mor N)) (ptensor one1 (prom u))).
Proof.
rewrite /lam_coalg /lam_under.
rewrite -[ch_mor (adj_psi _)]
        /(icones_comp (bang_fmap (tensor_curry (ch_mor N)))
                      (coalg_str (EM_prod (EM_term : Coalgebra Ar) funT_geom))).
rewrite -[Lfun (icones_comp _ _) (ptensor _ _)]
        /(Lfun (bang_fmap (tensor_curry (ch_mor N)))
               (Lfun (coalg_str (EM_prod (EM_term : Coalgebra Ar) funT_geom))
                     (ptensor one1 (prom u)))).
rewrite (EM_prod_str_E (EM_term : Coalgebra Ar) funT_geom) /EM_prod_str.
rewrite -[Lfun (icones_comp _ _) (ptensor _ _)]
        /(Lfun (m_bang (coalg_obj EM_term) (coalg_obj funT_geom))
               (Lfun (tensor_mor (coalg_str EM_term) (coalg_str funT_geom))
                     (ptensor one1 (prom u)))).
rewrite tensor_morE.
rewrite -[coalg_str EM_term]/(unit_cofree_str (Ar:=Ar)) unit_cofree_str_one1.
rewrite (bang_cofree_str L_geom) (dig_prom (B:=L_geom) u Hu).
rewrite (m_bang_prom (x:=one1) (y:=prom u)
                     cone_norm_one1_le1 (prom_ball Hu)).
have Hone_prom : cone_norm (ptensor one1 (prom u)) <= 1.
  apply: le_trans (tensor_norm_le _ _) _.
  rewrite -[1]mulr1; apply: ler_pM.
  - exact: cone_norm_ge0.
  - exact: cone_norm_ge0.
  - by rewrite cone_norm_one1.
  - exact: (prom_ball Hu).
by rewrite (bang_fmap_prom (tensor_curry (ch_mor N))
                           (ptensor one1 (prom u)) Hone_prom).
Qed.

(** [precone_zero : L_geom] has cone norm 0. *)
Lemma cone_norm_zero_L_geom_le1 :
  (cone_norm (precone_zero : L_geom) <= 1)%R.
Proof. by rewrite cone_norm0 ler01. Qed.

(** The structural reduction of [Step_geom one1 (prom 0_L_geom)]. *)
Theorem Step_geom_one_prom_zero_E :
  Step_geom one1 (prom (precone_zero : L_geom)) =
  prom (Lfun (tensor_curry (ch_mor (eD' body_inner)))
             (ptensor one1 (prom (precone_zero : L_geom)))).
Proof.
rewrite Step_geom_E.
exact: (lam_coalg_at_one_prom (eD' body_inner) cone_norm_zero_L_geom_le1).
Qed.

(** ** Reduction C — replace [eD body_inner] by its convex-combination form

    [eD body_inner = kbind_ext (case_em (eD then_e) (eD else_e)) (eD bernoulli)]
    by definition of [eD] on [ne_if].  Applying [case_em_bernoulli] (B1):
    [[
       eD body_inner = convex_combination (eD then_e) (eD else_e) ½ ½.
    ]]
    This is the inner reduction that exposes the [precone_scale (1/2) ·]
    structure of the geometric body. *)

(** The "then 0" branch's denotation. *)
Let then_e :
    @named_expr R Ar R_obj
       (("_"%string, tunit) :: ("g"%string, tfun tunit tR') :: nil) tR' :=
  ne_real 0%R.

(** The "else 1 + g()" branch's denotation. *)
Let else_e :
    @named_expr R Ar R_obj
       (("_"%string, tunit) :: ("g"%string, tfun tunit tR') :: nil) tR' :=
  ne_add (ne_real 1%R)
         (ne_app (ne_var (nv_tail "_"%string tunit _
                           (nv_head "g"%string (tfun tunit tR') nil)))
                 ne_tt).

Lemma body_inner_E :
  body_inner = ne_if tR' (ne_bernoulli (1/2 : R)%R
                            (phase4_half_ge0 R) (phase4_half_le1 R))
                          then_e else_e.
Proof. by []. Qed.

(** Apply [case_em_bernoulli] (B1) to [eD body_inner].  The result
    exposes the convex combination [½·(eD then_e) + ½·(eD else_e)]. *)
Lemma ex_geom_body_inner_via_convex :
  eD' body_inner =
  convex_combination (eD' then_e) (eD' else_e)
                     (phase4_half_ge0 R) (phase4_half_le1 R).
Proof.
rewrite /body_inner /=.
exact: (case_em_bernoulli (eD' then_e) (eD' else_e)
                          (phase4_half_ge0 R) (phase4_half_le1 R)).
Qed.

(** The Step_geom reduction with the convex-combination form
    of [eD body_inner] substituted in. *)
Theorem Step_geom_one_prom_zero_via_convex_E :
  Step_geom one1 (prom (precone_zero : L_geom)) =
  prom (Lfun (tensor_curry
              (ch_mor (convex_combination (eD' then_e) (eD' else_e)
                                          (phase4_half_ge0 R)
                                          (phase4_half_le1 R))))
             (ptensor one1 (prom (precone_zero : L_geom)))).
Proof.
rewrite Step_geom_one_prom_zero_E.
by rewrite ex_geom_body_inner_via_convex.
Qed.

(** ** Honest scope — the mass-identity blocker

    The headline target
    [[
      cone_norm (Step_geom one1 (prom (precone_zero : L_geom))) = (1/2)%R
    ]]
    reduces (via [Step_geom_one_prom_zero_via_convex_E]) to
    [[
      cone_norm (prom (Lfun (tensor_curry (ch_mor convex))
                            (one1 ⊗p prom 0))) = 1/2.
    ]]
    The inner [Lfun (tensor_curry (ch_mor convex)) (one1 ⊗p prom 0)]
    is a linhom in [L_geom = cone_one ⊸ Bang FMeas].  Its operator
    norm is the supremum (over [s : cone_one_car] in the unit ball) of
    [cone_norm (linhom_fun ... s)].

    At the LINHOM level, [convex_linhom = (1/2)·a_lh + (1/2)·b_lh]
    (from [bool_case (bernoulli ½) a_lh b_lh]).  If we could prove
    [b_lh = 0] (the else-branch vanishes when [g := prom 0]) and
    [cone_norm a_lh = 1], then [cone_normh] would give the inner
    [cone_norm = 1/2].  But pushing this through:

    1. The convex-combination LINHOM value here is at the [coalg]
       level (via [adj_psi] of [convex_icones]), with an extra
       [bang_fmap] / [coalg_str] layer.

    2. The outer [prom : L_geom → Bang L_geom] does NOT satisfy
       [cone_norm (prom x) = cone_norm x] — the codomain [Bang B]
       inherits its norm from the [wi_obj] equaliser embedding into
       a cone product of [fs_dom k]s, which gives only the
       inequality [cone_norm (prom x) ≤ cone_norm x] via
       [prom_ball].

    The headline [cone_norm = 1/2] therefore requires NEW
    infrastructure (a [cone_norm (prom x) = cone_norm x] identity,
    which is not currently in [bang_construct.v] / [bang.v]) — and
    would furthermore need to compute the convex-combination's
    operator-norm at the [coalg] level (not just at the [linhom]
    level, where [cone_normh] is directly available).

    This file delivers the AXIOM-FREE STRUCTURAL reductions ending
    at [der_Step_geom_one_prom_zero_E] (post-[der] extraction).  The
    mass identity [cone_norm = 1/2] is honestly DEFERRED, pending the
    per-branch evaluation cascade. *)

(** ** Reduction D — post-[der] extraction to the [L_geom] level

    Apply [der_prom] to the outer [prom] of (5).  The inner linhom
    [K := Lfun (tensor_curry (ch_mor convex)) (one1 ⊗p prom 0_L_geom)]
    has norm [≤ 1] by [cones_hom_norm_le1] on [tensor_curry (ch_mor
    convex)] (an [icones_hom]) applied to [one1 ⊗p prom 0] whose
    [cone_norm] is bounded by [cone_norm one1 · cone_norm (prom 0) ≤
    1 · 1 = 1]. *)

(** Norm bound on the inner linhom [K]. *)
Lemma cone_norm_K_le1 :
  cone_norm
    (Lfun (tensor_curry
            (ch_mor (convex_combination (eD' then_e) (eD' else_e)
                                        (phase4_half_ge0 R)
                                        (phase4_half_le1 R))))
          (ptensor one1 (prom (precone_zero : L_geom))))
  <= 1.
Proof.
have Hone_prom : cone_norm (ptensor one1 (prom (precone_zero : L_geom))) <= 1.
  apply: le_trans (tensor_norm_le _ _) _.
  rewrite -[1]mulr1; apply: ler_pM.
  - exact: cone_norm_ge0.
  - exact: cone_norm_ge0.
  - by rewrite cone_norm_one1.
  - exact: (prom_ball cone_norm_zero_L_geom_le1).
exact: le_trans (cones_hom_norm_le1 _ _) Hone_prom.
Qed.

(** Post-[der] structural reduction.  Combine (5) with [der_prom]
    using the norm bound (6) on the inner linhom [K]. *)
Theorem der_Step_geom_one_prom_zero_E :
  Lfun (der L_geom) (Step_geom one1 (prom (precone_zero : L_geom)))
  = Lfun (tensor_curry
           (ch_mor (convex_combination (eD' then_e) (eD' else_e)
                                       (phase4_half_ge0 R)
                                       (phase4_half_le1 R))))
        (ptensor one1 (prom (precone_zero : L_geom))).
Proof.
rewrite Step_geom_one_prom_zero_via_convex_E.
exact: (der_prom (B := L_geom) _ cone_norm_K_le1).
Qed.

(** ** Reduction E — eval1 form (post-der, post-eval-at-one1)
    BEYOND THE PAPER — Phase 4 evaluation tier.

    Combine the post-[der] reduction [der_Step_geom_one_prom_zero_E]
    with [tensor_curryE] (Class-3 pointwise) to obtain a flat
    [Bang(FMeas)]-element form: the linhom-value at [one1] of the
    [tensor_curry]-result equals the [ch_mor convex] evaluated at
    [(one1 ⊗ prom 0) ⊗ one1].

    This is the direct evaluation of the per-branch outputs of the
    convex combination at the recursive-call argument, packaged as a
    single [Bang FMeas]-element.

    Reads:
    [[
      linhom_fun (Lfun (der L_geom) (Step_geom one1 (prom 0))) one1
      = Lfun (ch_mor convex) ((one1 ⊗ prom 0) ⊗ one1).
    ]]
*)
Theorem linhom_fun_der_Step_geom_one1_E :
  linhom_fun
    (Lfun (der L_geom)
          (Step_geom one1 (prom (precone_zero : L_geom))))
    one1
  = Lfun (ch_mor (convex_combination (eD' then_e) (eD' else_e)
                                     (phase4_half_ge0 R)
                                     (phase4_half_le1 R)))
        (ptensor (ptensor one1 (prom (precone_zero : L_geom))) one1).
Proof.
rewrite der_Step_geom_one_prom_zero_E.
exact: (tensor_curryE
          (B := coalg_obj (EM_prod (EM_term : Coalgebra Ar) funT_geom))
          (C := coalg_obj (EM_term : Coalgebra Ar))
          (D := coalg_obj (Tobj (tyD tR' : Coalgebra Ar)))
          (ch_mor (convex_combination (eD' then_e) (eD' else_e)
                                      (phase4_half_ge0 R)
                                      (phase4_half_le1 R)))
          (ptensor one1 (prom (precone_zero : L_geom))) one1).
Qed.

(** ** Reduction F — operator-norm reduction to the [Bang(FMeas)] level
    BEYOND THE PAPER — Phase 4 evaluation tier.

    The operator-norm of the inner linhom [Lfun (tensor_curry (ch_mor
    convex)) (one1 ⊗ prom 0_L_geom)] (an element of [L_geom = cone_one
    ⊸ Bang FMeas]) equals the cone-norm of its evaluation at [one1]
    (by [linhom_norm_one1_E], the [linhom_norm = pointwise-at-one1]
    identity for the unit-cone source) — which by reduction E equals
    [cone_norm (Lfun (ch_mor convex) ((one1 ⊗ prom 0) ⊗ one1))].

    THIS IS THE OPERATOR-NORM SIDE of the headline mass-1/2 identity.
    Combined with the [cone_norm = linhom_norm] identity for L_geom
    elements (definitional via the [linhom_car] HB instance — see
    [cone_norm/linhom_norm] in [linhom.v]):
    [[
      cone_norm (Lfun (der L_geom) (Step_geom one1 (prom 0_L_geom)))
      = cone_norm (Lfun (ch_mor convex) ((one1 ⊗ prom 0) ⊗ one1)).
    ]]

    What remains: per-branch evaluation of [Lfun (ch_mor convex) ((one1
    ⊗ prom 0) ⊗ one1)] = convex-combination of [then_e]'s
    [dirac_fmeas 0] (mass 1) and [else_e]'s recursive-call image (mass
    0 at [g := prom 0_L_geom] since the dereliction destroys the
    promotion).  Half · 1 + half · 0 = half. *)
Theorem cone_norm_der_Step_geom_E :
  cone_norm (Lfun (der L_geom)
                  (Step_geom one1 (prom (precone_zero : L_geom))))
  = cone_norm (Lfun (ch_mor (convex_combination (eD' then_e) (eD' else_e)
                                                (phase4_half_ge0 R)
                                                (phase4_half_le1 R)))
                    (ptensor
                       (ptensor one1 (prom (precone_zero : L_geom)))
                       one1)).
Proof.
rewrite -linhom_fun_der_Step_geom_one1_E.
(* Goal: cone_norm (Lfun (der L_geom) (Step_geom one1 (prom 0)))
       = cone_norm (linhom_fun (Lfun (der L_geom) ...) one1) *)
rewrite -[cone_norm (Lfun (der L_geom) _)]/(linhom_norm _).
exact: linhom_norm_one1_E.
Qed.

(** ** Reduction G — coalg_str on the (one1 ⊗ prom 0) ⊗ one1 pure tensor
    BEYOND THE PAPER — Phase 4 evaluation tier.

    Compute [Lfun (coalg_str G) ((one1 ⊗ prom 0) ⊗ one1)] where [G =
    EM_prod (EM_prod EM_term funT_geom) EM_term].  The cascade:

    1. [coalg_str (EM_prod _ _) = m_bang ∘ (coalg_str ⊗ coalg_str)] —
       both factors apply nicely:
       - inner [coalg_str (EM_prod EM_term funT_geom)] on [one1 ⊗ prom 0]
         again reduces (same pattern) to [prom (one1 ⊗ prom 0)];
       - outer [coalg_str EM_term] on [one1] is [unit_cofree_str one1
         = prom one1];
       - outer [coalg_str funT_geom] on [prom 0] is [dig L_geom (prom 0)
         = prom (prom 0)] (with [cone_norm 0 ≤ 1] discharged).
       Then [m_bang] of two [prom]s is the [prom] of their tensor by
       [m_bang_prom].

    The result is [prom ((one1 ⊗ prom 0) ⊗ one1)] in [Bang(coalg_obj G)]. *)

Local Notation G_geom :=
  (EM_prod (EM_prod (EM_term : Coalgebra Ar) funT_geom)
           (EM_term : Coalgebra Ar)).

Lemma cone_norm_inner_pt_le1 :
  (cone_norm
    (ptensor (one1 : cone_one_car Ar) (prom (precone_zero : L_geom)))
    <= 1)%R.
Proof.
apply: le_trans (tensor_norm_le _ _) _.
rewrite -[1]mulr1; apply: ler_pM.
- exact: cone_norm_ge0.
- exact: cone_norm_ge0.
- by rewrite cone_norm_one1.
- exact: (prom_ball cone_norm_zero_L_geom_le1).
Qed.

Lemma cone_norm_outer_pt_le1 :
  (cone_norm
    (ptensor
       (ptensor (one1 : cone_one_car Ar) (prom (precone_zero : L_geom)))
       (one1 : cone_one_car Ar))
    <= 1)%R.
Proof.
apply: le_trans (tensor_norm_le _ _) _.
rewrite -[1]mulr1; apply: ler_pM.
- exact: cone_norm_ge0.
- exact: cone_norm_ge0.
- exact: cone_norm_inner_pt_le1.
- exact: cone_norm_one1_le1.
Qed.

Theorem coalg_str_G_on_outer_pt_E :
  Lfun (coalg_str G_geom)
       (ptensor
          (ptensor (one1 : cone_one_car Ar) (prom (precone_zero : L_geom)))
          (one1 : cone_one_car Ar))
  = prom
      (ptensor
         (ptensor (one1 : cone_one_car Ar) (prom (precone_zero : L_geom)))
         (one1 : cone_one_car Ar)).
Proof.
rewrite (EM_prod_str_E (EM_prod (EM_term : Coalgebra Ar) funT_geom)
                       (EM_term : Coalgebra Ar)) /EM_prod_str.
rewrite -[Lfun (icones_comp _ _) _]
        /(Lfun (m_bang (coalg_obj _) (coalg_obj _))
               (Lfun (tensor_mor _ _) _)).
rewrite tensor_morE.
(* Reduce inner coalg_str EM_prod EM_term funT_geom on (one1 ⊗ prom 0). *)
have Hinner : Lfun (coalg_str (EM_prod (EM_term : Coalgebra Ar) funT_geom))
                   (ptensor (one1 : cone_one_car Ar)
                            (prom (precone_zero : L_geom)))
            = prom (ptensor (one1 : cone_one_car Ar)
                            (prom (precone_zero : L_geom))).
  rewrite (EM_prod_str_E (EM_term : Coalgebra Ar) funT_geom) /EM_prod_str.
  rewrite -[Lfun (icones_comp _ _) _]
          /(Lfun (m_bang (coalg_obj _) (coalg_obj _))
                 (Lfun (tensor_mor _ _) _)).
  rewrite tensor_morE.
  rewrite -[coalg_str EM_term]/(unit_cofree_str (Ar:=Ar)) unit_cofree_str_one1.
  rewrite (bang_cofree_str L_geom)
          (dig_prom (B:=L_geom) (precone_zero : L_geom)
                    cone_norm_zero_L_geom_le1).
  by rewrite (m_bang_prom (x:=one1) (y:=prom (precone_zero : L_geom))
                          cone_norm_one1_le1
                          (prom_ball cone_norm_zero_L_geom_le1)).
rewrite Hinner.
(* Reduce outer coalg_str EM_term on one1. *)
rewrite -[coalg_str EM_term]/(unit_cofree_str (Ar:=Ar)) unit_cofree_str_one1.
(* Now apply m_bang_prom. *)
by rewrite (m_bang_prom (x:=ptensor (one1 : cone_one_car Ar)
                                    (prom (precone_zero : L_geom)))
                        (y:=one1)
                        cone_norm_inner_pt_le1 cone_norm_one1_le1).
Qed.

(** ** Reduction H — Lfun (ch_mor convex) at the outer pt
    BEYOND THE PAPER — Phase 4 evaluation tier.

    Combines [Lfun_ch_mor_adj_psi_at] (Class 1), [coalg_str_G_on_outer_pt_E]
    above, and [bang_fmap_prom] to read [Lfun (ch_mor convex)] at the outer
    pure-tensor as a [prom] of [Lfun convex_icones] at the same point.

    Reads:
    [[
      Lfun (ch_mor convex) ((one1 ⊗ prom 0_L_geom) ⊗ one1)
      = prom (Lfun convex_icones ((one1 ⊗ prom 0_L_geom) ⊗ one1)).
    ]]
*)
Theorem Lfun_ch_mor_convex_at_outer_pt_E :
  Lfun (ch_mor (convex_combination (eD' then_e) (eD' else_e)
                                   (phase4_half_ge0 R)
                                   (phase4_half_le1 R)))
       (ptensor
          (ptensor (one1 : cone_one_car Ar) (prom (precone_zero : L_geom)))
          (one1 : cone_one_car Ar))
  = prom (Lfun (convex_icones (eD' then_e) (eD' else_e)
                              (phase4_half_ge0 R) (phase4_half_le1 R))
               (ptensor
                  (ptensor (one1 : cone_one_car Ar)
                           (prom (precone_zero : L_geom)))
                  (one1 : cone_one_car Ar))).
Proof.
rewrite /convex_combination.
rewrite (Lfun_ch_mor_adj_psi_at
           (convex_icones (eD' then_e) (eD' else_e)
                          (phase4_half_ge0 R) (phase4_half_le1 R))
           (ptensor
              (ptensor (one1 : cone_one_car Ar)
                       (prom (precone_zero : L_geom)))
              (one1 : cone_one_car Ar))).
rewrite coalg_str_G_on_outer_pt_E.
by rewrite (bang_fmap_prom
              (convex_icones (eD' then_e) (eD' else_e)
                             (phase4_half_ge0 R) (phase4_half_le1 R))
              _ cone_norm_outer_pt_le1).
Qed.

(** ** Reduction I — full chain: cone_norm of post-[der] Step_geom = cone_norm of prom of convex_icones at outer pt
    BEYOND THE PAPER — Phase 4 evaluation tier.

    Compose [cone_norm_der_Step_geom_E] with [Lfun_ch_mor_convex_at_outer_pt_E].

    [[
      cone_norm (Lfun (der L_geom) (Step_geom one1 (prom 0_L_geom)))
      = cone_norm (prom (Lfun convex_icones ((one1 ⊗ prom 0) ⊗ one1))).
    ]]

    THIS IS THE STRUCTURAL ENDPOINT of the per-branch evaluation cascade.
    The remaining gap to the headline mass identity [= 1/2] is the EXACT
    [prom_norm] equation [cone_norm (prom x) = cone_norm x], which IS the
    open identity flagged in [bang.v] lines 201-225.  Combined with the
    convex-decomposition pointwise reading at [convex_icones], the
    headline would close. *)
Theorem cone_norm_der_Step_geom_via_prom_convex_icones_E :
  cone_norm (Lfun (der L_geom)
                  (Step_geom one1 (prom (precone_zero : L_geom))))
  = cone_norm
      (prom (Lfun (convex_icones (eD' then_e) (eD' else_e)
                                 (phase4_half_ge0 R)
                                 (phase4_half_le1 R))
                  (ptensor
                     (ptensor (one1 : cone_one_car Ar)
                              (prom (precone_zero : L_geom)))
                     (one1 : cone_one_car Ar)))).
Proof.
rewrite cone_norm_der_Step_geom_E.
by rewrite Lfun_ch_mor_convex_at_outer_pt_E.
Qed.

(** ** Reduction J — coalg_e evaluation at the outer pt
    BEYOND THE PAPER — Phase 4 evaluation tier.

    Evaluate [Lfun (coalg_e G_geom) ((one1 ⊗ prom 0_L_geom) ⊗ one1)
    = one1]: the unit-cone counit of the cartesian comonoid sends any
    [coalg_str]-promoted element to [one1].

    Useful for the [const_kleisli]-based [eD'] branches (reals,
    samples), where the eventual reduction lands at [lin_pt c (one1) = c]
    via [lin_pt_unit]. *)
Theorem coalg_e_G_on_outer_pt_E :
  Lfun (coalg_e G_geom)
       (ptensor
          (ptensor (one1 : cone_one_car Ar) (prom (precone_zero : L_geom)))
          (one1 : cone_one_car Ar))
  = one1.
Proof.
set z := ptensor
          (ptensor (one1 : cone_one_car Ar) (prom (precone_zero : L_geom)))
          (one1 : cone_one_car Ar).
have Hz_le1 : cone_norm z <= 1 by exact: cone_norm_outer_pt_le1.
have Hcs : Lfun (coalg_str G_geom) z = prom z by exact: coalg_str_G_on_outer_pt_E.
transitivity (Lfun (e_bang (coalg_obj G_geom)) (Lfun (coalg_str G_geom) z));
  first by [].
rewrite Hcs.
exact: (@e_bang_prom R Ar (coalg_obj G_geom) z Hz_le1).
Qed.

(** ** Reduction K — ELSE-branch evaluation cascade
    BEYOND THE PAPER — Phase 4 evaluation tier.

    Evaluate the ELSE-branch [else_e := 1 + g()] at the outer point
    [(one1 ⊗ prom 0_L_geom) ⊗ one1].  With [g] bound to the diverging
    value [prom 0_L_geom], the variable-headed call [g()] reduces (via
    [app_kleisli_var] + [der_prom] on [prom 0_L_geom]) to [0] in
    [FMeas R_obj]; then bilinearity of [add_lift] at zero
    ([add_lift_zero_R]) makes the whole sum [0].

    Post-[der] form (in [FMeas R_obj]):
    [[
      Lfun (der (FMeas R_obj)) (Lfun (ch_mor (eD' else_e)) at_outer_pt)
      = precone_zero.
    ]]
    Full form (in [Bang (FMeas R_obj)] = [coalg_obj (Tobj tR')]):
    [[
      Lfun (ch_mor (eD' else_e)) at_outer_pt = prom precone_zero.
    ]]

    Companion to the THEN-branch evaluation lemma (worked in parallel). *)

(** Auxiliary: the zero element has cone-norm ≤ 1.  Used as a norm hypothesis
    for [m_bang_prom] / [bang_fmap_prom] / [der_prom] on zero arguments. *)
Lemma cone_norm0_le1 (P : ICone.type Ar) :
  (cone_norm (precone_zero : P) <= 1)%R.
Proof. by rewrite cone_norm0 ler01. Qed.

(** Outer point — package the [(one1 ⊗ prom 0) ⊗ one1] used throughout. *)
Let at_outer_pt :
    coalg_obj (EM_prod (EM_prod (EM_term : Coalgebra Ar) funT_geom)
                        (EM_term : Coalgebra Ar)) :=
  ptensor (ptensor (one1 : cone_one_car Ar) (prom (precone_zero : L_geom)))
          (one1 : cone_one_car Ar).

(** *** Var lookup of "g" at the outer pt evaluates to [prom 0_L_geom]. *)
Lemma Lfun_var_lookup_g_at_outer_pt_E :
  Lfun (ch_mor
          (var_lookup
             (named_var_to_has_var
                (nv_tail "_"%string tunit _
                  (nv_head "g"%string (tfun tunit tR') nil)))))
       at_outer_pt
  = prom (precone_zero : L_geom).
Proof.
(* var_lookup (nv_tail .. (nv_head ..)) =
   coalg_comp (em_proj2 EM_term funT_geom)
              (em_proj1 (EM_prod EM_term funT_geom) EM_term).  *)
rewrite -[Lfun (ch_mor _) _]
        /(Lfun (icones_comp (em_proj2_mor (EM_term : Coalgebra Ar) funT_geom)
                            (em_proj1_mor (EM_prod (EM_term : Coalgebra Ar) funT_geom)
                                          (EM_term : Coalgebra Ar)))
               at_outer_pt).
rewrite -[Lfun (icones_comp _ _) _]
        /(Lfun (em_proj2_mor (EM_term : Coalgebra Ar) funT_geom)
               (Lfun (em_proj1_mor (EM_prod (EM_term : Coalgebra Ar) funT_geom)
                                   (EM_term : Coalgebra Ar))
                     at_outer_pt)).
(* Step 1: em_proj1 at outer_pt = ptensor one1 (prom 0).
   em_proj1_mor P Q = iso_fwd (tensor_runit P) ∘ tensor_mor id (coalg_e Q).
   coalg_e EM_term = id.  So em_proj1_mor P EM_term = iso_fwd (tensor_runit P). *)
rewrite /em_proj1_mor coalg_e_term.
rewrite -[tensor_mor _ _]/(tensor_mor (icones_id Ar _) (icones_id Ar _)).
have tensor_mor_id_id :
  forall (B C : ICone.type Ar),
    tensor_mor (icones_id Ar B) (icones_id Ar C) = icones_id Ar (tensor Ar B C).
  move=> B C; apply: tensor_ext => x y; by rewrite tensor_morE.
rewrite tensor_mor_id_id icones_compIr.
rewrite /at_outer_pt.
rewrite tensor_runitEp.
rewrite (_ : c1_val (one1 : cone_one_car Ar) = 1%:nng); last by [].
rewrite precone_scale_1.
(* Step 2: em_proj2 (ptensor one1 (prom 0)) = prom 0.
   em_proj2_mor P Q = iso_fwd (tensor_lunit Q) ∘ tensor_mor (coalg_e P) id. *)
rewrite /em_proj2_mor.
rewrite -[Lfun (icones_comp _ _) _]
        /(iso_fwd (tensor_lunit (coalg_obj funT_geom))
            (Lfun (tensor_mor (coalg_e (EM_term : Coalgebra Ar))
                              (icones_id Ar (coalg_obj funT_geom)))
                  (ptensor (one1 : cone_one_car Ar)
                           (prom (precone_zero : L_geom))))).
rewrite coalg_e_term tensor_morE.
rewrite -[Lfun (icones_id Ar _) _]/(prom (precone_zero : L_geom)).
rewrite tensor_lunitEp.
rewrite (_ : c1_val (one1 : cone_one_car Ar) = 1%:nng); last by [].
by rewrite precone_scale_1.
Qed.

(** *** [eD' (#g)] evaluated at outer_pt = [prom (prom 0_L_geom)]. *)
Lemma Lfun_ch_mor_ne_var_g_at_outer_pt_E :
  Lfun (ch_mor (eD' (ne_var (nv_tail "_"%string tunit _
                              (nv_head "g"%string (tfun tunit tR') nil)))))
       at_outer_pt
  = prom (prom (precone_zero : L_geom)).
Proof.
rewrite (eD_var (nv_tail "_"%string tunit _
                  (nv_head "g"%string (tfun tunit tR') nil))).
rewrite -[ch_mor (coalg_comp _ _)]
        /(icones_comp
            (ch_mor (tunit_eta (tyD (tfun tunit tR'))))
            (ch_mor (var_lookup (named_var_to_has_var
                                   (nv_tail "_"%string tunit _
                                     (nv_head "g"%string (tfun tunit tR') nil)))))).
rewrite -[Lfun (icones_comp _ _) _]
        /(Lfun (ch_mor (tunit_eta (tyD (tfun tunit tR'))))
               (Lfun (ch_mor (var_lookup (named_var_to_has_var
                                            (nv_tail "_"%string tunit _
                                              (nv_head "g"%string (tfun tunit tR') nil)))))
                     at_outer_pt)).
rewrite Lfun_var_lookup_g_at_outer_pt_E.
(* Now ch_mor (tunit_eta funT_geom) = coalg_str funT_geom = dig L_geom
   (by bang_cofree_str).  Apply dig_prom on prom 0_L_geom. *)
rewrite -[ch_mor (tunit_eta _)]/(coalg_str funT_geom).
rewrite (bang_cofree_str L_geom).
exact: (dig_prom (B:=L_geom) (precone_zero : L_geom)
                  cone_norm_zero_L_geom_le1).
Qed.

(** *** Crucial: the application [g()] at outer_pt evaluates to [prom 0].

    By [app_kleisli_var], the [eD] image is [app_kleisli (var_lookup g)
    (em_term_mor _)].  Then [Lfun_ch_mor_app_kleisli_at] +
    [coalg_str_G_on_outer_pt_E] + the structural reductions of
    [app_under] at the outer pt — using [der_prom] on the [prom 0_L_geom]
    extracted from the variable — give [prom precone_zero]. *)
Lemma Lfun_ch_mor_app_g_tt_at_outer_pt_E :
  Lfun (ch_mor (eD' (ne_app
                      (ne_var (nv_tail "_"%string tunit _
                                (nv_head "g"%string (tfun tunit tR') nil)))
                      ne_tt)))
       at_outer_pt
  = prom (precone_zero : FMeas R_obj).
Proof.
(* Step 1: eD' (ne_app (#g) ne_tt) = app_kleisli (var_lookup g)
   (em_term_mor _), via app_kleisli_var. *)
rewrite (eD_app
           (ne_var (nv_tail "_"%string tunit _
                     (nv_head "g"%string (tfun tunit tR') nil)))
           (@ne_tt R Ar R_obj _)).
rewrite (eD_var (nv_tail "_"%string tunit _
                   (nv_head "g"%string (tfun tunit tR') nil))).
rewrite (eD_tt (("_"%string, tunit) :: ("g"%string, tfun tunit tR') :: nil)).
rewrite (app_kleisli_var
           (var_lookup (named_var_to_has_var
                          (nv_tail "_"%string tunit _
                            (nv_head "g"%string (tfun tunit tR') nil))))
           (em_term_mor G_geom)).
(* Step 2: Reduce ch_mor (app_kleisli F V) at outer_pt via
   Lfun_ch_mor_app_kleisli_at. *)
rewrite (Lfun_ch_mor_app_kleisli_at
           (var_lookup (named_var_to_has_var
                          (nv_tail "_"%string tunit _
                            (nv_head "g"%string (tfun tunit tR') nil))))
           (em_term_mor G_geom)
           at_outer_pt).
(* Now goal: Lfun (bang_fmap (icones_comp (der (coalg_obj (tyD tR')))
                                         (app_under F V)))
                  (Lfun (coalg_str G_geom) at_outer_pt) = prom precone_zero.
   Apply coalg_str_G_on_outer_pt_E + bang_fmap_prom. *)
rewrite -[coalg_obj G_geom]/(coalg_obj G_geom).
rewrite (coalg_str_G_on_outer_pt_E).
rewrite (bang_fmap_prom _ at_outer_pt cone_norm_outer_pt_le1).
congr (prom _).
(* Goal: Lfun (icones_comp (der FMeas) (app_under F V)) at_outer_pt
       = precone_zero.
   Unfold the icones_comp: Lfun (der FMeas) (Lfun (app_under F V) at_outer_pt). *)
rewrite -[Lfun (icones_comp _ _) _]
        /(Lfun (der (coalg_obj (tyD tR')))
               (Lfun (app_under (var_lookup (named_var_to_has_var
                                  (nv_tail "_"%string tunit _
                                    (nv_head "g"%string (tfun tunit tR') nil))))
                                (em_term_mor _))
                     at_outer_pt)).
(* Now reduce app_under F V at the point.
   app_under F V = tensor_uncurry (adj_phi F) ∘ tensor_mor id (ch_mor V)
                                              ∘ coalg_d G_geom. *)
rewrite /app_under.
rewrite -[Lfun (icones_comp _ _) at_outer_pt]
        /(Lfun (tensor_uncurry
                 (adj_phi (var_lookup (named_var_to_has_var
                            (nv_tail "_"%string tunit _
                              (nv_head "g"%string (tfun tunit tR') nil))))))
               (Lfun (icones_comp (tensor_mor (icones_id Ar _)
                                              (ch_mor (em_term_mor _)))
                                  (coalg_d G_geom))
                     at_outer_pt)).
rewrite -[Lfun (icones_comp (tensor_mor _ _) _) at_outer_pt]
        /(Lfun (tensor_mor (icones_id Ar (coalg_obj G_geom))
                           (ch_mor (em_term_mor G_geom)))
               (Lfun (coalg_d G_geom) at_outer_pt)).
(* coalg_d G_geom = tensor_mor (der G) (der G) ∘ d_bang ∘ coalg_str G.
   Apply to at_outer_pt step by step. *)
rewrite /coalg_d.
rewrite -[Lfun (icones_comp (tensor_mor _ _) _) at_outer_pt]
        /(Lfun (tensor_mor (der (coalg_obj G_geom)) (der (coalg_obj G_geom)))
               (Lfun (icones_comp (d_bang (coalg_obj G_geom)) (coalg_str G_geom))
                     at_outer_pt)).
rewrite -[Lfun (icones_comp (d_bang _) _) at_outer_pt]
        /(Lfun (d_bang (coalg_obj G_geom))
               (Lfun (coalg_str G_geom) at_outer_pt)).
rewrite coalg_str_G_on_outer_pt_E.
rewrite (d_bang_prom (A := coalg_obj G_geom) at_outer_pt cone_norm_outer_pt_le1).
rewrite tensor_morE.
rewrite (der_prom (B := coalg_obj G_geom) at_outer_pt cone_norm_outer_pt_le1).
(* Now: Lfun (tensor_mor id (ch_mor (em_term_mor _))) (ptensor at_outer_pt at_outer_pt) *)
rewrite tensor_morE.
rewrite -[icones_id Ar _ _]/at_outer_pt.
rewrite -[ch_mor (em_term_mor _)]/(coalg_e G_geom).
rewrite coalg_e_G_on_outer_pt_E.
(* Now: Lfun (tensor_uncurry (adj_phi (var_lookup g)))
              (ptensor at_outer_pt one1) *)
(* By tensor_uncurry's behaviour: tensor_uncurry h (x ⊗ y) = (h x) y.
   Specifically, by tensor_curry/uncurry adjunction and tensor_curryE:
   tensor_uncurry (adj_phi F) (x ⊗ one1) = linhom_fun ((adj_phi F) x) one1
   when we have (adj_phi F) x : linhom_car _.  But the structural shape
   passes through tensor_curryK first.  Use tensor_curryE on
   adj_phi F = tensor_curry (tensor_uncurry (adj_phi F)) via tensor_curryK. *)
have Heq :
  Lfun (tensor_uncurry
          (adj_phi (var_lookup (named_var_to_has_var
                     (nv_tail "_"%string tunit _
                       (nv_head "g"%string (tfun tunit tR') nil))))))
       (ptensor at_outer_pt (one1 : cone_one_car Ar))
  = linhom_fun
      (Lfun (adj_phi (var_lookup (named_var_to_has_var
                        (nv_tail "_"%string tunit _
                          (nv_head "g"%string (tfun tunit tR') nil)))))
            at_outer_pt)
      (one1 : cone_one_car Ar).
  set F := adj_phi _.
  have HK := @tensor_uncurryK R Ar (coalg_obj G_geom)
                              (coalg_obj (tyD tunit))
                              (coalg_obj (Tobj (tyD tR'))) F.
  have := tensor_curryEp (tensor_uncurry F) at_outer_pt (one1 : cone_one_car Ar).
  rewrite HK.
  by move=> ->.
rewrite Heq.
(* Now: Lfun (adj_phi (var_lookup g)) at_outer_pt.
   adj_phi h = der (codomain) ∘ ch_mor h.  Compute via the var_lookup
   reduction. *)
rewrite -[adj_phi _]/(icones_comp (adj_counit _)
                                  (U_mor (var_lookup (named_var_to_has_var
                                    (nv_tail "_"%string tunit _
                                      (nv_head "g"%string (tfun tunit tR') nil)))))).
rewrite -[Lfun (icones_comp (adj_counit _) _) _]
        /(Lfun (adj_counit (linhom_car Ar (coalg_obj (tyD tunit))
                                          (coalg_obj (Tobj (tyD tR')))))
               (Lfun (U_mor (var_lookup (named_var_to_has_var
                              (nv_tail "_"%string tunit _
                                (nv_head "g"%string (tfun tunit tR') nil)))))
                     at_outer_pt)).
rewrite -[U_mor _]
        /(ch_mor (var_lookup (named_var_to_has_var
                    (nv_tail "_"%string tunit _
                      (nv_head "g"%string (tfun tunit tR') nil))))).
rewrite Lfun_var_lookup_g_at_outer_pt_E.
rewrite -[adj_counit _]/(der (linhom_car Ar (coalg_obj (tyD tunit))
                                            (coalg_obj (Tobj (tyD tR'))))).
rewrite (der_prom (B := L_geom)
                  (precone_zero : L_geom)
                  cone_norm_zero_L_geom_le1).
(* Goal: Lfun (der (FMeas R_obj)) (linhom_fun (precone_zero : L_geom) one1)
       = precone_zero : FMeas R_obj.
   Step 1: linhom_fun (precone_zero : L_geom) one1 = (precone_zero : Bang FMeas)
           by definition of the zero linhom.
   Step 2: Lfun (der ...) precone_zero = precone_zero by linearity of der. *)
have Hz_eval :
  linhom_fun (precone_zero : L_geom) (one1 : cone_one_car Ar)
  = (precone_zero : Bang Ar (FMeas R_obj)).
  by [].
rewrite Hz_eval.
have [Hder0 _ _] :=
  cones_hom_linear
    (mcones_hom_cones
      (icones_hom_mcones (der (FMeas R_obj)))).
exact: Hder0.
Qed.

(** *** ELSE-branch evaluation (full form) — the headline lemma.

    [Lfun (ch_mor (eD' else_e)) at_outer_pt = prom precone_zero] in
    [Bang (FMeas R_obj)].  By [eD_add], the [eD' else_e] image is
    [add_lift ∘ bang_m ∘ em_pair (eD' (ne_real 1)) (eD' app_g_tt)];
    we evaluate the [add_lift]-wrap at the [(?, prom precone_zero)]-shape
    coming from the previous lemma, via bilinearity of [add_lift]. *)
Theorem Lfun_ch_mor_else_e_at_outer_pt_E :
  Lfun (ch_mor (eD' else_e)) at_outer_pt
  = prom (precone_zero : FMeas R_obj).
Proof.
rewrite /else_e.
rewrite (eD_add
           (R_obj := R_obj)
           (G := ("_"%string, tunit) :: ("g"%string, tfun tunit tR') :: nil)
           (ne_real (G := ("_"%string, tunit)
                            :: ("g"%string, tfun tunit tR') :: nil) 1%R)
           (ne_app (ne_var (nv_tail "_"%string tunit _
                            (nv_head "g"%string (tfun tunit tR') nil)))
                   ne_tt)).
(* eD' else_e =
   coalg_comp (bang_cofree_hom add_lift)
              (coalg_comp (bang_m (FMeas R_obj) (FMeas R_obj))
                          (em_pair (eD' (ne_real 1)) (eD' app_g_tt))). *)
rewrite -[ch_mor (coalg_comp (bang_cofree_hom _) _)]
        /(icones_comp (bang_fmap (@add_lift _ _ _ R_carrier_eq
                                               R_carrier_meas R_to_carrier_meas))
                      (ch_mor (coalg_comp
                                 (bang_m (FMeas R_obj) (FMeas R_obj))
                                 (em_pair _ _)))).
rewrite -[Lfun (icones_comp _ _) _]
        /(Lfun (bang_fmap (@add_lift _ _ _ R_carrier_eq
                                        R_carrier_meas R_to_carrier_meas))
               (Lfun (ch_mor (coalg_comp
                                (bang_m (FMeas R_obj) (FMeas R_obj))
                                (em_pair _ _)))
                     at_outer_pt)).
rewrite -[ch_mor (coalg_comp (bang_m _ _) _)]
        /(icones_comp (m_bang (FMeas R_obj) (FMeas R_obj))
                      (em_pair_mor (ch_mor (eD' (@ne_real R Ar R_obj
                                                  (("_"%string, tunit)
                                                    :: ("g"%string, tfun tunit tR') :: nil) 1%R)))
                                   (ch_mor (eD'
                                             (ne_app
                                                (ne_var (nv_tail "_"%string tunit _
                                                          (nv_head "g"%string (tfun tunit tR') nil)))
                                                ne_tt))))).
rewrite -[Lfun (icones_comp (m_bang _ _) _) _]
        /(Lfun (m_bang (FMeas R_obj) (FMeas R_obj))
               (Lfun (em_pair_mor (Z := G_geom)
                                  (P := Tobj (tyD tR'))
                                  (Q := Tobj (tyD tR'))
                                  (ch_mor (eD' (@ne_real R Ar R_obj
                                                  (("_"%string, tunit)
                                                    :: ("g"%string, tfun tunit tR') :: nil) 1%R)))
                                  (ch_mor (eD'
                                            (ne_app
                                               (ne_var (nv_tail "_"%string tunit _
                                                         (nv_head "g"%string (tfun tunit tR') nil)))
                                               ne_tt))))
                     at_outer_pt)).
(* Reduce Lfun (em_pair_mor f g) at_outer_pt to ptensor (Lfun f at_outer_pt)
   (Lfun g at_outer_pt) via coalg_d on outer_pt = ptensor at_outer_pt at_outer_pt
   (computed via coalg_str_G_on_outer_pt_E + d_bang_prom + tensor_morE + der_prom). *)
rewrite /em_pair_mor.
rewrite -[Lfun (icones_comp (tensor_mor _ _) _) _]
        /(Lfun (tensor_mor
                  (ch_mor (eD' (@ne_real R Ar R_obj
                                  (("_"%string, tunit)
                                    :: ("g"%string, tfun tunit tR') :: nil) 1%R)))
                  (ch_mor (eD'
                            (ne_app
                               (ne_var (nv_tail "_"%string tunit _
                                         (nv_head "g"%string (tfun tunit tR') nil)))
                               ne_tt))))
               (Lfun (coalg_d G_geom) at_outer_pt)).
rewrite /coalg_d.
rewrite -[Lfun (icones_comp (tensor_mor _ _) _) _]
        /(Lfun (tensor_mor (der (coalg_obj G_geom)) (der (coalg_obj G_geom)))
               (Lfun (icones_comp (d_bang (coalg_obj G_geom)) (coalg_str G_geom))
                     at_outer_pt)).
rewrite -[Lfun (icones_comp (d_bang _) _) _]
        /(Lfun (d_bang (coalg_obj G_geom))
               (Lfun (coalg_str G_geom) at_outer_pt)).
rewrite coalg_str_G_on_outer_pt_E.
rewrite (d_bang_prom (A := coalg_obj G_geom) at_outer_pt cone_norm_outer_pt_le1).
rewrite tensor_morE.
rewrite (der_prom (B := coalg_obj G_geom) at_outer_pt cone_norm_outer_pt_le1).
rewrite tensor_morE.
rewrite Lfun_ch_mor_app_g_tt_at_outer_pt_E.
(* Goal: Lfun (bang_fmap add_lift) (Lfun (m_bang FMeas FMeas)
            (ptensor (Lfun (ch_mor (eD' (ne_real 1))) at_outer_pt)
                     (prom precone_zero)))
       = prom precone_zero. *)
(* Need: cone_norm (Lfun (ch_mor (eD' (ne_real 1))) at_outer_pt) ≤ 1
   and cone_norm (prom precone_zero) ≤ 1.  Both elements are in
   Bang (FMeas R_obj) — for the latter use prom_ball.  For the former,
   it's the image of a coalg_hom on an outer_pt with norm ≤ 1, and
   cones_hom_norm_le1 gives the bound. *)
set u1 := Lfun (ch_mor (eD'
                         (@ne_real R Ar R_obj
                            (("_"%string, tunit)
                              :: ("g"%string, tfun tunit tR') :: nil) 1%R)))
              at_outer_pt.
have Hu1 : cone_norm u1 <= 1.
  rewrite /u1.
  apply: le_trans (cones_hom_norm_le1 _ _) _.
  exact: cone_norm_outer_pt_le1.
have Hu2 : cone_norm (prom (precone_zero : FMeas R_obj)) <= 1.
  apply: (prom_ball (x := precone_zero : FMeas R_obj)).
  by rewrite cone_norm0.
(* m_bang on a ptensor of two unit-ball points in Bang(FMeas):
   we need (Lfun (ch_mor (eD' real_1)) at_outer_pt) and
   (prom precone_zero) both to be in unit-ball OF Bang (FMeas), so
   that we can apply m_bang's structural identity.  But m_bang doesn't
   have a direct identity at arbitrary points — only at PROM points.
   So we need to use a different approach: directly apply der_nat +
   der_m_bang to peel things off, then add_lift_zero_R. *)
(* Strategy: rewrite via:
   bang_fmap add_lift = (linearity of !) but we don't have such an
   identity at arbitrary ball points.  Use linearity of add_lift +
   the fact that the SECOND argument (prom precone_zero) gets killed
   by m_bang's interaction with the zero coordinate.

   Cleaner approach: m_bang's underlying icones_hom maps to Bang (A⊗B);
   on ptensor x y with y = prom 0, the chain m_bang ∘ (id ⊗ prom_0)
   collapses through tensor's bilinearity at zero.  Actually, simplest:
   m_bang is a linear (icones) morphism, so it commutes with precone_scale
   and additivity.  In particular Lfun (m_bang) (ptensor x precone_zero)
   = precone_zero via ptensor_0r + linearity of m_bang.

   But (prom precone_zero) ≠ precone_zero in Bang (FMeas)!
   prom precone_zero is the promotion of 0, NOT the zero of Bang. *)
(* So we must reduce m_bang at (x, prom 0) differently.
   But here we want the FINAL result, not m_bang's intermediate.
   Use the alternative: bang_fmap add_lift at (m_bang (x, prom 0))
   — via der_nat: cones_hom_funCompose to push der through bang_fmap. *)
(* Actually the cleanest path: instead of using m_bang's identity,
   use the FACT that we'll combine with bang_fmap add_lift and then
   if the WHOLE thing is reduced to the right shape... *)
(* Cleanest path: use eD' (ne_real 1) reduction first.  eD' (ne_real 1)
   = real_kleisli 1 = const_kleisli _ (dirac_fmeas (R_to_carrier 1)) _
   = adj_psi (const_icones _ (dirac_fmeas ...) _).  Then
   ch_mor (adj_psi g) = bang_fmap g ∘ coalg_str.  So at at_outer_pt:
   Lfun (ch_mor (eD' (ne_real 1))) at_outer_pt
   = Lfun (bang_fmap (const_icones _ _ _)) (Lfun (coalg_str G_geom) at_outer_pt)
   = Lfun (bang_fmap (const_icones _ _ _)) (prom at_outer_pt)
   = prom (Lfun (const_icones _ _ _) at_outer_pt)            -- bang_fmap_prom
   = prom (dirac_fmeas (R_to_carrier 1))                      -- const_icones at one1
*)
rewrite /u1.
rewrite (eD_real
           (G := ("_"%string, tunit) :: ("g"%string, tfun tunit tR') :: nil) 1%R).
set ci := const_icones G_geom
            (dirac_fmeas (R_to_carrier R_carrier_eq 1%R))
            (dirac_fmeas_norm_le1 (R_to_carrier R_carrier_eq 1%R)).
have Hreal_at :
  Lfun (ch_mor (@real_kleisli R Ar R_obj R_carrier_eq G_geom 1%R))
       at_outer_pt
  = prom (Lfun ci at_outer_pt).
  rewrite -[ch_mor (@real_kleisli _ _ _ _ _ _)]
          /(icones_comp (bang_fmap ci) (coalg_str G_geom)).
  rewrite -[Lfun (icones_comp _ _) at_outer_pt]
          /(Lfun (bang_fmap ci) (Lfun (coalg_str G_geom) at_outer_pt)).
  rewrite coalg_str_G_on_outer_pt_E.
  exact: (bang_fmap_prom ci at_outer_pt cone_norm_outer_pt_le1).
rewrite Hreal_at.
(* Now u1 = prom (Lfun (const_icones ...) at_outer_pt).  Apply m_bang_prom. *)
set d1 := Lfun (const_icones _ _ _) at_outer_pt.
have Hd1 : cone_norm d1 <= 1.
  rewrite /d1.
  apply: le_trans (cones_hom_norm_le1 _ _) _.
  exact: cone_norm_outer_pt_le1.
rewrite (m_bang_prom (A := FMeas R_obj) (B := FMeas R_obj)
                     (x := d1) (y := precone_zero : FMeas R_obj)
                     Hd1 (cone_norm0_le1 _)).
rewrite (bang_fmap_prom _ (ptensor d1 (precone_zero : FMeas R_obj))).
(* Goal: prom (Lfun add_lift (ptensor d1 precone_zero)) = prom precone_zero. *)
- by rewrite (add_lift_zero_R d1).
- (* cone_norm bound on (ptensor d1 precone_zero) *)
  apply: le_trans (tensor_norm_le _ _) _.
  rewrite -[1]mulr1; apply: ler_pM.
  + exact: cone_norm_ge0.
  + exact: cone_norm_ge0.
  + exact: Hd1.
  + by rewrite cone_norm0.
Qed.

(** *** Post-[der] form of the ELSE-branch evaluation. *)
Theorem der_Lfun_ch_mor_else_e_at_outer_pt_E :
  Lfun (der (FMeas R_obj))
       (Lfun (ch_mor (eD' else_e)) at_outer_pt)
  = precone_zero.
Proof.
rewrite Lfun_ch_mor_else_e_at_outer_pt_E.
exact: (der_prom (B := FMeas R_obj)
                  (precone_zero : FMeas R_obj) (cone_norm0_le1 _)).
Qed.


(** ** Reduction L — THEN-branch evaluation at the outer point
    BEYOND THE PAPER — Phase 4 evaluation tier.

    Companion to ELSE.  Evaluates [then_e := ne_real 0%R] at
    [at_outer_pt].  Result: [prom (dirac_fmeas 0)]. *)
Theorem Lfun_ch_mor_then_e_at_outer_pt_E :
  Lfun (ch_mor (eD' then_e))
       (ptensor
          (ptensor (one1 : cone_one_car Ar) (prom (precone_zero : L_geom)))
          (one1 : cone_one_car Ar))
  = prom (dirac_fmeas (R_to_carrier R_carrier_eq 0%R) : FMeas R_obj).
Proof.
rewrite /then_e (eD_real 0%R).
rewrite /real_kleisli.
set c := (dirac_fmeas (R_to_carrier R_carrier_eq 0%R) : FMeas R_obj).
set Hc := dirac_fmeas_norm_le1 _.
rewrite (Lfun_ch_mor_const_kleisli_at c Hc _).
rewrite coalg_str_G_on_outer_pt_E.
have Hbnd : (cone_norm
              (ptensor
                 (ptensor (one1 : cone_one_car Ar)
                          (prom (precone_zero : L_geom)))
                 (one1 : cone_one_car Ar)
              : coalg_obj G_geom) <= 1)%R
  by exact: cone_norm_outer_pt_le1.
rewrite (bang_fmap_prom (const_icones _ c Hc) _ Hbnd).
rewrite -[Lfun (const_icones _ _ _) _]
        /(Lfun (linhom_icones (lin_pt c) (lin_pt_norm_le1 c Hc))
               (Lfun (coalg_e G_geom) _)).
rewrite coalg_e_G_on_outer_pt_E.
rewrite linhom_iconesE.
rewrite -[one1]/(MkConeOne Ar 1%:nng).
by rewrite lin_pt_unit.
Qed.

(** ** Reduction L' — post-[der] THEN-branch evaluation *)
Theorem der_Lfun_ch_mor_then_e_at_outer_pt_E :
  Lfun (der (FMeas R_obj))
       (Lfun (ch_mor (eD' then_e))
             (ptensor
                (ptensor (one1 : cone_one_car Ar)
                         (prom (precone_zero : L_geom)))
                (one1 : cone_one_car Ar)))
  = (dirac_fmeas (R_to_carrier R_carrier_eq 0%R) : FMeas R_obj).
Proof.
rewrite Lfun_ch_mor_then_e_at_outer_pt_E.
exact: (der_prom (B := FMeas R_obj) _
          (dirac_fmeas_norm_le1 (R_to_carrier R_carrier_eq 0%R))).
Qed.

(** ** §1 — First-iterate FMeas mass = 1/2
    BEYOND THE PAPER — Phase 4 mass-1 closure.

    THE HEADLINE FIRST-ITERATE MASS IDENTITY.

    Combining the per-branch THEN/ELSE evaluations (which evaluate to
    [dirac_fmeas 0] / [precone_zero] respectively after [der]),
    [case_em_bernoulli] (B1, the convex-combination reduction), and the
    structural reductions for [Step_geom] from §0, we read off the
    FMeas mass of the first iterate of [ex_geom] (with the recursive
    function [g] bound to the value [prom precone_zero]).

    The mass is exactly [1/2]: with probability [1/2] the body returns
    [δ_0] (mass 1), and with probability [1/2] it recurses and gets
    mass [0] (since [g := prom 0] makes the recursive call return 0).

    Form:
    [[
       fmeas_mu (Lfun (der (FMeas R_obj))
                      (linhom_fun
                         (Lfun (der L_geom)
                               (Step_geom one1 (prom precone_zero)))
                         one1))
                setT = (1/2)%R%:E.
    ]] *)

(** *** Step 1 — Evaluate [ch_mor (convex_combination then_e else_e)]
       at the outer pt as a sum (pointwise) of the two branches.

    Combining [Lfun_ch_mor_convex_at_outer_pt_E] (which gives a
    [prom (Lfun convex_icones at_outer_pt)] form) with the pointwise
    decomposition of [convex_icones = der A ∘ convex_icones_bang] +
    [convex_linhomE] (which equals [bool_case bernoulli then_lh else_lh]).
    By [der_prom] applied to the outer [prom], extract the inner
    [Lfun convex_icones at_outer_pt] as a [precone_add] of the scaled
    branches. *)
(** Auxiliary lemma: [linhom_fun] of [precone_add] decomposes pointwise. *)
Lemma linhom_fun_precone_add_E (C D : ICone.type Ar)
    (f g : linhom_car Ar C D) (x : C) :
  linhom_fun (precone_add f g) x =
  precone_add (linhom_fun f x) (linhom_fun g x).
Proof. by []. Qed.

(** Auxiliary lemma: [linhom_fun] of [precone_scale] decomposes pointwise. *)
Lemma linhom_fun_precone_scale_E (C D : ICone.type Ar)
    (r : {nonneg R}) (f : linhom_car Ar C D) (x : C) :
  linhom_fun (precone_scale r f) x =
  precone_scale r (linhom_fun f x).
Proof. by []. Qed.

Lemma Lfun_convex_icones_at_outer_pt_E :
  Lfun (convex_icones (eD' then_e) (eD' else_e)
                      (phase4_half_ge0 R) (phase4_half_le1 R))
       (ptensor
          (ptensor (one1 : cone_one_car Ar) (prom (precone_zero : L_geom)))
          (one1 : cone_one_car Ar))
  = Lfun (der (FMeas R_obj))
         (precone_add
            (precone_scale (NngNum (phase4_half_ge0 R))
              (Lfun (ch_mor (eD' then_e)) at_outer_pt))
            (precone_scale (NngNum (onem_ge0 (1/2)%R (phase4_half_le1 R)))
              (Lfun (ch_mor (eD' else_e)) at_outer_pt))).
Proof.
(* Compute the inner [Lfun convex_icones_bang at_outer_pt] in terms of
   the per-branch linhoms.  Since
     convex_icones_bang = linhom_icones (bool_case (bernoulli p) a_lh b_lh) _
   we have
     Lfun convex_icones_bang at_outer_pt
   = linhom_fun (bool_case (bernoulli p) a_lh b_lh) at_outer_pt
   = (linhom-linearity over precone_add + precone_scale)
     precone_add (precone_scale p (Lfun (ch_mor then_e) at_outer_pt))
                 (precone_scale (1-p) (Lfun (ch_mor else_e) at_outer_pt)).
   Then [Lfun convex_icones = Lfun (der A) ∘ Lfun convex_icones_bang]
   gives the goal. *)
have Hinner :
  Lfun (convex_icones_bang (eD' then_e) (eD' else_e)
                           (phase4_half_ge0 R)
                           (phase4_half_le1 R))
       at_outer_pt
  = precone_add
      (precone_scale (NngNum (phase4_half_ge0 R))
        (Lfun (ch_mor (eD' then_e)) at_outer_pt))
      (precone_scale (NngNum (onem_ge0 (1/2)%R (phase4_half_le1 R)))
        (Lfun (ch_mor (eD' else_e)) at_outer_pt)).
  rewrite -[Lfun (convex_icones_bang _ _ _ _) _]
          /(linhom_fun (convex_linhom (eD' then_e) (eD' else_e)
                                      (phase4_half_ge0 R)
                                      (phase4_half_le1 R))
                       at_outer_pt).
  rewrite convex_linhomE /bool_case.
  (* Push linhom_fun through precone_add + precone_scale. *)
  rewrite linhom_fun_precone_add_E.
  rewrite !linhom_fun_precone_scale_E.
  congr (precone_add (precone_scale _ _) (precone_scale _ _));
    by apply: nngnum_inj.
rewrite -[LHS]/(Lfun (der (FMeas R_obj))
                     (Lfun (convex_icones_bang (eD' then_e) (eD' else_e)
                                               (phase4_half_ge0 R)
                                               (phase4_half_le1 R))
                           at_outer_pt)).
by rewrite Hinner.
Qed.

(** *** Step 2 — derive the post-[der] form of the FMeas value via
       the convex evaluation. *)
Lemma der_FMeas_linhom_der_Step_E :
  Lfun (der (FMeas R_obj))
       (linhom_fun
          (Lfun (der L_geom)
                (Step_geom one1 (prom (precone_zero : L_geom))))
          (one1 : cone_one_car Ar))
  = Lfun (der (FMeas R_obj))
         (precone_add
            (precone_scale (NngNum (phase4_half_ge0 R))
              (Lfun (ch_mor (eD' then_e)) at_outer_pt))
            (precone_scale (NngNum (onem_ge0 (1/2)%R (phase4_half_le1 R)))
              (Lfun (ch_mor (eD' else_e)) at_outer_pt))).
Proof.
rewrite linhom_fun_der_Step_geom_one1_E.
rewrite Lfun_ch_mor_convex_at_outer_pt_E.
have Hnorm : cone_norm
                (Lfun (convex_icones (eD' then_e) (eD' else_e)
                                     (phase4_half_ge0 R)
                                     (phase4_half_le1 R))
                      (ptensor
                         (ptensor (one1 : cone_one_car Ar)
                                  (prom (precone_zero : L_geom)))
                         (one1 : cone_one_car Ar))) <= 1.
  apply: le_trans (cones_hom_norm_le1 _ _) _.
  exact: cone_norm_outer_pt_le1.
rewrite (der_prom (B := FMeas R_obj) _ Hnorm).
exact: Lfun_convex_icones_at_outer_pt_E.
Qed.

(** *** Step 3 — Apply [der] linearity to push it inside the
       [precone_add] + [precone_scale] structure, then substitute the
       per-branch THEN ([prom (dirac_fmeas 0)]) / ELSE
       ([prom precone_zero]) evaluations.

    After the rewrites, we land at:
    [[
       (1/2) · dirac_fmeas (R_to_carrier 0) + (1/2) · precone_zero
    ]]
    in [FMeas R_obj]. *)
Lemma der_FMeas_linhom_der_Step_E_branches :
  Lfun (der (FMeas R_obj))
       (linhom_fun
          (Lfun (der L_geom)
                (Step_geom one1 (prom (precone_zero : L_geom))))
          (one1 : cone_one_car Ar))
  = precone_add
      (precone_scale (NngNum (phase4_half_ge0 R))
        (dirac_fmeas (R_to_carrier R_carrier_eq 0%R) : FMeas R_obj))
      (precone_scale (NngNum (onem_ge0 (1/2)%R (phase4_half_le1 R)))
        (precone_zero : FMeas R_obj)).
Proof.
rewrite der_FMeas_linhom_der_Step_E.
(* Apply linearity of der (FMeas R_obj) to push it inside add/scale. *)
have [_ HderD HderZ] :=
  cones_hom_linear
    (mcones_hom_cones (icones_hom_mcones (der (FMeas R_obj)))).
rewrite HderD !HderZ.
(* Now both branches are [Lfun (der ∘ ch_mor) at_outer_pt = der (prom ...)] *)
(* THEN-branch: rewrite via Lfun_ch_mor_then_e_at_outer_pt_E and der_prom *)
rewrite Lfun_ch_mor_then_e_at_outer_pt_E.
rewrite (der_prom (B := FMeas R_obj) _
                  (dirac_fmeas_norm_le1 (R_to_carrier R_carrier_eq 0%R))).
(* ELSE-branch: rewrite via Lfun_ch_mor_else_e_at_outer_pt_E and der_prom *)
rewrite Lfun_ch_mor_else_e_at_outer_pt_E.
rewrite (der_prom (B := FMeas R_obj) (precone_zero : FMeas R_obj)
                  (cone_norm0_le1 _)).
by [].
Qed.

(** *** Step 4 — Extract the mass [= 1/2] via [fmeas_addE] +
       [fmeas_scaleE] + [dirac_fmeas_setT_E] + [fmeas_zeroE].

    The two summands evaluate as:
    - [(1/2) · δ_(R_to_carrier 0)] has mass [1/2]
    - [(1/2) · 0] has mass [0]

    Sum: [1/2]. *)
Theorem first_iterate_FMeas_mass_half :
  fmeas_mu (Lfun (der (FMeas R_obj))
                 (linhom_fun
                    (Lfun (der L_geom)
                          (Step_geom one1 (prom (precone_zero : L_geom))))
                    (one1 : cone_one_car Ar)))
           [set: ar_carrier Ar R_obj]
  = @EFin R (1 / 2)%R.
Proof.
rewrite der_FMeas_linhom_der_Step_E_branches.
(* Goal: fmeas_mu (fmeas_add (fmeas_scale (1/2) δ_0) (fmeas_scale (1/2) 0)) setT
       = (1/2)%R%:E *)
rewrite -[precone_add _ _]/(fmeas_add
   (precone_scale (NngNum (phase4_half_ge0 R))
                  (dirac_fmeas (R_to_carrier R_carrier_eq 0%R) : FMeas R_obj))
   (precone_scale (NngNum (onem_ge0 (1/2)%R (phase4_half_le1 R)))
                  (precone_zero : FMeas R_obj))).
rewrite fmeas_addE.
rewrite -[precone_scale _ (dirac_fmeas _)]
        /(fmeas_scale (NngNum (phase4_half_ge0 R))
                      (dirac_fmeas (R_to_carrier R_carrier_eq 0%R) : FMeas R_obj)).
rewrite -[precone_scale _ (precone_zero : FMeas R_obj)]
        /(fmeas_scale (NngNum (onem_ge0 (1/2)%R (phase4_half_le1 R)))
                      (fmeas_zero : FMeas R_obj)).
rewrite fmeas_scale_0r.
rewrite fmeas_scaleE.
rewrite dirac_fmeas_setT_E.
rewrite fmeas_zeroE.
rewrite mule1.
by rewrite adde0.
Qed.

End ExGeomStep.

Arguments Step_geom
  {R Ar R_obj} R_carrier_eq R_carrier_meas R_to_carrier_meas γ v.
Arguments Step_geom_E
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} γ v.
Arguments Step_geom_one_prom_zero_E
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}.
Arguments ex_geom_body_inner_via_convex
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}.
Arguments Step_geom_one_prom_zero_via_convex_E
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}.
Arguments cone_norm_K_le1
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}.
Arguments der_Step_geom_one_prom_zero_E
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}.
Arguments linhom_fun_der_Step_geom_one1_E
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}.
Arguments cone_norm_der_Step_geom_E
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}.
Arguments cone_norm_inner_pt_le1
  {R Ar R_obj}.
Arguments cone_norm_outer_pt_le1
  {R Ar R_obj}.
Arguments coalg_str_G_on_outer_pt_E
  {R Ar R_obj}.
Arguments Lfun_ch_mor_convex_at_outer_pt_E
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}.
Arguments cone_norm_der_Step_geom_via_prom_convex_icones_E
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}.
Arguments coalg_e_G_on_outer_pt_E
  {R Ar R_obj}.
Arguments Lfun_var_lookup_g_at_outer_pt_E
  {R Ar R_obj}.
Arguments Lfun_ch_mor_ne_var_g_at_outer_pt_E
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}.
Arguments Lfun_ch_mor_app_g_tt_at_outer_pt_E
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}.
Arguments Lfun_ch_mor_else_e_at_outer_pt_E
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}.
Arguments der_Lfun_ch_mor_else_e_at_outer_pt_E
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}.
Arguments Lfun_ch_mor_then_e_at_outer_pt_E
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}.
Arguments der_Lfun_ch_mor_then_e_at_outer_pt_E
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}.
Arguments linhom_fun_precone_add_E
  {R Ar C D} f g x.
Arguments linhom_fun_precone_scale_E
  {R Ar C D} r f x.
Arguments Lfun_convex_icones_at_outer_pt_E
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}.
Arguments der_FMeas_linhom_der_Step_E
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}.
Arguments der_FMeas_linhom_der_Step_E_branches
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}.
Arguments first_iterate_FMeas_mass_half
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}.
