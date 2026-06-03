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

    Standalone experiment file, NOT in _CoqProject.

    Author: Guillaume Baudart <guillaume.baudart@inria.fr>. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals signed.
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
Require Import Icones.homs.linhom.
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
