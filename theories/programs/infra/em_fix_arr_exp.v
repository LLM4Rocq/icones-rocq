(**md**************************************************************************)
(** * Focused experiment — outer reductions for [ex_loop]'s [Step]

    BEYOND THE PAPER — partial validation of the expert's CBV-Y recipe.

    The CBV LL expert (Melliès) recommends: "[ch_mor body] is the [f]
    whose fixpoint we want.  It must be promoted, otherwise it doesn't
    work.  And we must start from [!0], not from [0]."

    This standalone experiment tests whether, for [ex_loop]'s body
    [\ "_" ::: tunit => # "l" @ ()] (the simplest Phase 4 body), the
    value [prom precone_zero : Bang Ar L] is a FIXPOINT of the natural
    [Step] operator constructed from the body's denotation.

    With [M := eD body] and [L := linhom_car cone_one_car (Bang
    cone_one_car)] (the linhom carrier of [funT = tyD (tfun tunit
    tunit)]), the [Step] operator at the cone-element level is:
    [[
      Step γ v := Lfun (bang_fmap (der L)) (Lfun (ch_mor M) (ptensor γ v)).
    ]]

    Headline question: [Step one1 (prom precone_zero) =?= prom
    precone_zero].

    *** What this experiment delivers, AXIOM-FREE (modulo the three
        [boolp] axioms):

    1. [Step_E] — [Step γ v = Lfun (ch_mor (lam_coalg (eD
       body_inner))) (ptensor γ v)].  Outer collapse via
       [bang_fmap (der L) ∘ dig L = id_{Bang L}] (the comonad
       [comonad_counitR L] right-counit law) after rewriting
       [ch_mor M = dig L ∘ ch_mor (lam_coalg body_inner)] by
       [eD_lam] + [bang_cofree_str].  PURELY categorical: holds
       for ALL [γ, v], no ball / unit-ball hypotheses required.

    2. [lam_coalg_at_one_prom] — for any [N] and any [u] with
       [cone_norm u <= 1] :
       [[
         Lfun (ch_mor (lam_coalg N)) (ptensor one1 (prom u)) =
         prom (Lfun (tensor_curry (ch_mor N)) (ptensor one1 (prom u))).
       ]]
       Via [adj_psi] = [bang_fmap ∘ coalg_str], combined with
       [coalg_str (EM_prod EM_term funT) = m_bang ∘ (unit_cofree_str
       ⊗ dig L)], [unit_cofree_str_one1], [dig_prom], [m_bang_prom],
       and [bang_fmap_prom].

    3. [Step_one_prom_zero_E] — the headline-form reduction:
       [[
         Step one1 (prom 0_L) =
         prom (Lfun (tensor_curry (ch_mor (eD body_inner)))
                    (ptensor one1 (prom 0_L))).
       ]]
       Composition of [Step_E] and [lam_coalg_at_one_prom] at
       [u := precone_zero : L].

    *** Honest scope and limitations.

    The headline equality [Step one1 (prom 0_L) = prom 0_L] is NOT
    closed in this file.  After [Step_one_prom_zero_E], the
    remaining (sufficient) condition is the residual
    [[
      Lfun (tensor_curry (ch_mor (eD body_inner)))
           (ptensor one1 (prom (precone_zero : L)))
        = precone_zero : L.
    ]]
    Carrying it out requires unfolding [body_inner = ne_app
    (ne_var "l") ne_tt] through [eD_app + eD_var + eD_tt + app_pair
    + app_kleisli + app_under + bang_m + em_pair + tensor_uncurry +
    adj_phi + adj_psi] — i.e. building a new VARIABLE-headed
    β-reduction lemma [app_kleisli_var] analogous to the existing
    [app_kleisli_lam] (which handles LAMBDA-headed application).
    No such lemma exists in the library.  This is the same
    bottleneck that blocks [em_fix_arr.v]'s mass-zero proof (see
    [em_fix_arr.v] lines 53-83).

    What this experiment validates: the OUTER structure of the
    expert's recipe (promote the body, seed at [!0]) IS consistent
    end-to-end and the two outer reductions hold axiom-free.  The
    INNER reduction (whether the body-with-[l]-bound-to-zero
    evaluates to the zero closure) is the residual question; once
    [app_kleisli_var] is in hand, [Step_one_prom_zero_E] will close
    the headline equality in three lines.

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
Require Import Icones.programs.cbv.
Require Import Icones.programs.ppl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** Section setup *)

Section ExLoopStepExp.
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

(** ** The linhom-carrier [L] and the function-coalgebra [funT] *)

Let L : ICone.type Ar :=
  linhom_car Ar (coalg_obj (EM_term : Coalgebra Ar))
               (coalg_obj (Tobj (EM_term : Coalgebra Ar))).

Let funT : Coalgebra Ar := bang_cofree L.

(** Sanity: [tyD (tfun tunit tunit) = funT] (definitional). *)
Lemma tyD_funT_E :
  @tyD R Ar (tfun tunit tunit) = funT.
Proof. by []. Qed.

(** ** [ex_loop]'s body in the singleton context [("l", tfun tunit tunit)] *)

Definition ex_loop_body :
    @named_expr R Ar R_obj (("l"%string, tfun tunit tunit) :: nil)
                (tfun tunit tunit) :=
  ne_lam ("_"%string) (ne_app
    (ne_var (nv_tail "_"%string tunit _
              (nv_head "l"%string (tfun tunit tunit) nil)))
    ne_tt).

(** [M] is the body's denotation : [coalg_hom (EM_prod EM_term funT)
    (Tobj funT)]. *)
Definition M_body :
    coalg_hom (EM_prod (EM_term : Coalgebra Ar) funT) (Tobj funT) :=
  eD' ex_loop_body.

(** ** The [Step] operator on cone elements

    [Step γ v := Lfun (bang_fmap (der L)) (Lfun (ch_mor M) (ptensor γ v))]. *)

Definition Step (γ : coalg_obj (EM_term : Coalgebra Ar))
                (v : coalg_obj funT) :
    coalg_obj funT :=
  Lfun (bang_fmap (der L)) (Lfun (ch_mor M_body) (ptensor γ v)).

(** ** Reduction A — [Step γ v = Lfun (ch_mor (lam_coalg (eD body_inner))) (ptensor γ v)]

    By [eD_lam] : [eD body = coalg_comp (tunit_eta funT) (lam_coalg
    (eD body_inner))], hence [ch_mor M = dig L ∘ ch_mor (lam_coalg
    body_inner)] (since [coalg_str funT = dig L]).  Then
    [bang_fmap (der L) ∘ dig L = id_{Bang L}] by [comonad_counitR],
    collapsing the outer extract. *)

(** The body inner is [# "l" @ ()] in the extended context. *)
Let body_inner :
    @named_expr R Ar R_obj
       (("_"%string, tunit) :: ("l"%string, tfun tunit tunit) :: nil)
       tunit :=
  ne_app (ne_var (nv_tail "_"%string tunit _
                            (nv_head "l"%string (tfun tunit tunit) nil)))
         ne_tt.

Lemma M_body_E :
  M_body = coalg_comp (tunit_eta funT) (lam_coalg (eD' body_inner)).
Proof. by rewrite /M_body /ex_loop_body eD_lam. Qed.

(** Outer collapse: [bang_fmap (der L) ∘ dig L = id]. *)
Lemma outer_collapse :
  icones_comp (bang_fmap (der L)) (coalg_str funT) =
  icones_id Ar (Bang Ar L).
Proof.
rewrite (bang_cofree_str L).
exact: (comonad_counitR L).
Qed.

(** Reduction A: pointwise collapse of the outer [bang_fmap der ∘
    dig].  Crucial: this DOES NOT depend on [γ] or [v] being any
    specific point — purely categorical. *)
Lemma Step_E γ v :
  Step γ v = Lfun (ch_mor (lam_coalg (eD' body_inner))) (ptensor γ v).
Proof.
rewrite /Step M_body_E.
rewrite coalg_comp_mor.
rewrite -[ch_mor (tunit_eta funT)]/(coalg_str funT) (bang_cofree_str L).
rewrite -[Lfun (bang_fmap (der L)) (Lfun (icones_comp _ _) _)]
        /(Lfun (icones_comp (bang_fmap (der L))
                            (icones_comp (dig L)
                                         (ch_mor (lam_coalg (eD' body_inner)))))
               (ptensor γ v)).
rewrite icones_compA (comonad_counitR L) icones_compIl.
by [].
Qed.

(** ** Reduction B — pointwise [lam_coalg N] at a promoted unit-ball
       second component

    [Lfun (ch_mor (lam_coalg N)) (ptensor one1 (prom u)) =
       prom (Lfun (tensor_curry (ch_mor N)) (ptensor one1 (prom u)))]
    when [cone_norm u ≤ 1], the underlying argument
    being a promoted point of [Bang L].

    Proof:
    [ch_mor (lam_coalg N) = bang_fmap (tensor_curry (ch_mor N)) ∘
                            coalg_str (EM_prod EM_term funT)].
    [coalg_str (EM_prod EM_term funT) = m_bang ∘ (unit_cofree_str ⊗ dig L)].
    At [ptensor one1 (prom u)]:
      [(unit_cofree_str ⊗ dig L)(ptensor one1 (prom u))
         = unit_cofree_str(one1) ⊗p dig L(prom u)
         = one1! ⊗p (prom u)!]
    by [unit_cofree_str_one1] + [dig_prom].
    Then [m_bang (one1! ⊗p (prom u)!) = (ptensor one1 (prom u))!] by
    [m_bang_prom].  Finally [bang_fmap (tensor_curry (ch_mor N))]
    applied to [(ptensor one1 (prom u))!] equals [prom (tensor_curry (ch_mor
    N) (ptensor one1 (prom u)))] by [bang_fmap_prom]. *)

Lemma cone_norm_one1 :
  (cone_norm (one1 : cone_one_car Ar) = 1)%R.
Proof. by rewrite /cone_norm /= /c1_norm. Qed.

Lemma cone_norm_one1_le1 :
  (cone_norm (one1 : cone_one_car Ar) <= 1)%R.
Proof. by rewrite cone_norm_one1. Qed.

Lemma lam_coalg_at_one_prom
    (N : coalg_hom (EM_prod (EM_prod (EM_term : Coalgebra Ar) funT)
                            (EM_term : Coalgebra Ar))
                   (Tobj (EM_term : Coalgebra Ar)))
    (u : L) (Hu : cone_norm u <= 1) :
  Lfun (ch_mor (lam_coalg N)) (ptensor one1 (prom u)) =
  prom (Lfun (tensor_curry (ch_mor N)) (ptensor one1 (prom u))).
Proof.
rewrite /lam_coalg /lam_under.
rewrite -[ch_mor (adj_psi _)]/(icones_comp (bang_fmap (tensor_curry (ch_mor N)))
                                            (coalg_str (EM_prod (EM_term : Coalgebra Ar) funT))).
rewrite -[Lfun (icones_comp _ _) (ptensor _ _)]
        /(Lfun (bang_fmap (tensor_curry (ch_mor N)))
               (Lfun (coalg_str (EM_prod (EM_term : Coalgebra Ar) funT))
                     (ptensor one1 (prom u)))).
rewrite (EM_prod_str_E (EM_term : Coalgebra Ar) funT) /EM_prod_str.
rewrite -[Lfun (icones_comp _ _) (ptensor _ _)]
        /(Lfun (m_bang (coalg_obj EM_term) (coalg_obj funT))
               (Lfun (tensor_mor (coalg_str EM_term) (coalg_str funT))
                     (ptensor one1 (prom u)))).
rewrite tensor_morE.
rewrite -[coalg_str EM_term]/(unit_cofree_str (Ar:=Ar)) unit_cofree_str_one1.
rewrite (bang_cofree_str L) (dig_prom (B:=L) u Hu).
rewrite (m_bang_prom (x:=one1) (y:=prom u) cone_norm_one1_le1 (prom_ball Hu)).
have Hone_prom : cone_norm (ptensor one1 (prom u)) <= 1.
  apply: le_trans (tensor_norm_le _ _) _.
  rewrite -[1]mulr1; apply: ler_pM.
  - exact: cone_norm_ge0.
  - exact: cone_norm_ge0.
  - by rewrite cone_norm_one1.
  - exact: (prom_ball Hu).
by rewrite (bang_fmap_prom (tensor_curry (ch_mor N)) (ptensor one1 (prom u)) Hone_prom).
Qed.

(** ** Reduction C — full chain to a clean residual

    Combining [Step_E] with [lam_coalg_at_one_prom] at [u :=
    precone_zero : L] reduces the headline goal
    [Step one1 (prom (precone_zero : L)) = prom (precone_zero : L)]
    to the clean residual
    [Lfun (tensor_curry (ch_mor (eD body_inner))) (one1 ⊗p prom 0_L)
     = precone_zero : L].

    The residual is a pointwise equality between two LINHOMs in
    [L = cone_one ⊸ Bang cone_one], which by [linhom_eq] /
    [tensor_curryE] further reduces to
    [forall s : cone_one_car,
       (ch_mor (eD body_inner)) ((one1 ⊗p prom 0_L) ⊗p s) =
       precone_zero : Bang cone_one_car].

    That is: the body inner's denotation, applied to the
    promoted-zero context [(((), prom 0_L), s)], produces the zero
    point in [Bang cone_one_car].

    This residual requires a NEW β-reduction lemma for [eD (ne_app
    (ne_var "l") ne_tt)] — a "variable in head position" β-rule,
    distinct from the [eD_app_lam_subst] lemma (which handles
    LAMBDA in head position).  No such lemma currently exists in
    the library; constructing it requires unfolding [eD_app] +
    [eD_var] + [eD_tt] through [kcomp] / [app_pair] / [app_kleisli]
    / [app_under] + the [bang_m] / [em_pair] / [tensor_uncurry] /
    [adj_phi] / [adj_psi] chains — exactly the chase that
    [em_fix_arr.v]'s prototype investigation deferred (see
    [em_fix_arr.v] lines 53-83).

    Honest scope of this experiment: the EXPERT's RECIPE (promote
    body, seed at [!0]) reduces END-TO-END for the OUTER structure
    of [ex_loop]'s [Step] operator — the two outer reductions are
    axiom-free.  The INNER reduction (evaluating the body's
    denotation at the promoted-zero context) is the bottleneck;
    it is the same bottleneck that blocks [em_fix_arr.v]'s mass-zero
    proof.  Resolving it requires either:

    (a) a new categorical β-rule for variable-headed applications,
        proved through the same machinery as [eD_app_lam_subst],
    (b) an alternative route via [adj_phi] that absorbs [prom]
        into [der] (the [tmul]/[app_kleisli] path),
    (c) reformulating the experiment to AVOID the variable-headed
        application — e.g. compute [Step γ v] for [v := lam_coalg]
        of some inner body, where [app_kleisli_lam] applies directly.

    What we deliver, axiom-free:
    [[
      Step_E : Step γ v = Lfun (ch_mor (lam_coalg (eD body_inner)))
                                (ptensor γ v).
      lam_coalg_at_one_prom :
        forall N u, cone_norm u <= 1 ->
        Lfun (ch_mor (lam_coalg N)) (ptensor one1 (prom u)) =
        prom (Lfun (tensor_curry (ch_mor N)) (ptensor one1 (prom u))).
    ]]

    These two compose to give the clean chain
    [[
      Step one1 (prom 0_L)
        = Lfun (ch_mor (lam_coalg (eD body_inner))) (one1 ⊗p prom 0_L)
        = prom (Lfun (tensor_curry (ch_mor (eD body_inner)))
                     (one1 ⊗p prom 0_L)).
    ]]

    So the headline question reduces — axiom-free — to the value
    of [Lfun (tensor_curry (ch_mor (eD body_inner))) (one1 ⊗p prom
    0_L)].  We deliver this reduction below as [Step_one_prom_zero_E]. *)

(** [precone_zero : L] has cone norm 0. *)
Lemma cone_norm_zeroL_le1 :
  (cone_norm (precone_zero : L) <= 1)%R.
Proof. by rewrite cone_norm0 ler01. Qed.

(** The full reduction of [Step one1 (prom 0_L)].  Axiom-free. *)
Theorem Step_one_prom_zero_E :
  Step one1 (prom (precone_zero : L)) =
  prom (Lfun (tensor_curry (ch_mor (eD' body_inner)))
             (ptensor one1 (prom (precone_zero : L)))).
Proof.
rewrite Step_E.
exact: (lam_coalg_at_one_prom (eD' body_inner) cone_norm_zeroL_le1).
Qed.

End ExLoopStepExp.

Arguments Step {R Ar R_obj} R_carrier_eq R_carrier_meas R_to_carrier_meas γ v.
Arguments Step_one_prom_zero_E {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}.
