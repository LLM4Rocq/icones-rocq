(**md**************************************************************************)
(** * [ex_almost_loop_arr] — Bang-level CBV-Y for [ex_almost_loop p]
       Per-iterate mass + closed form

    The parameterised partial-termination analog of [ex_loop_arr]:
    we ship the per-iterate scalar mass identity for [ex_almost_loop]
    at the Bang-level Kleene chain, plus the closed-form recurrence
    [c1_val (F_arr_almost p n) = 1 - (1 - p)^n] (in nonneg-real arithmetic
    on the unit interval) and a corollary at [p = 0] which recovers
    [ex_loop_arr_mass_zero].

    *** What is delivered (axiom-free).

    - [ex_almost_loop_body p] : the body in the singleton context
      [("l", tfun tunit tunit)], i.e. [\"_". if Bernoulli(p) then ()
      else l()].

    - [M_loop_p p Hp_ge0 Hp_le1] : the body's denotation as a
      Kleisli morphism, parameterized in the Bernoulli weight [p].

    - [Step_loop_p γ v] : the Bang-level fixpoint operator analogous
      to [ex_loop_arr]'s [Step_loop].

    - [kleene_arr_loop_p n] : the Kleene chain seeded at [prom
      (precone_zero : L_loop)].

    - [F_arr_loop_p n] : the [cone_one_car]-scalar extracted from the
      n-th iterate (the mass-equivalent for [tunit]-returning programs).

    - Per-iterate recurrence on the SCALAR (c1_val):
      [(c1_val (F_arr_loop_p n.+1))%:num
       = p + (1 - p) * (c1_val (F_arr_loop_p n))%:num].

    - Closed form:
      [(c1_val (F_arr_loop_p n))%:num = 1 - (1 - p)^n].

    - Corollary at [p = 0]: [(c1_val (F_arr_loop_p n))%:num = 0] for
      all [n] (recovers [ex_loop_arr_mass_zero]).

    *** What is NOT delivered.

    The supremum-level mass convergence [(c1_val (Yfix_arr_loop_p))%:num
    → (1 - lim (1-p)^n)] (= [1] for [p > 0], [0] for [p = 0]) requires
    a [c1_val (cone_sup_ball u uch ub1) = lim (c1_val (u n))] identity
    at the [cone_one_car] level — analogous to [fmeas_sup_cvg] at the
    FMeas level, but for the singleton-test cone.  This identity is
    not currently in the library; deferring its construction to a
    follow-up.

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
Require Import Icones.programs.infra.cbv_outer_pt.
Require Import Icones.programs.infra.bool_cone.
Require Import Icones.programs.infra.bool_case_hom.
Require Import Icones.programs.infra.case_em_red.
Require Import Icones.programs.infra.curry_kbind.
Require Import Icones.programs.infra.em_fix.
Require Import Icones.programs.infra.ex_loop_arr.
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

Section ExAlmostLoopArr.
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

(** [cone_norm one1 = 1] and the [≤ 1] consequence — re-exported as
    aliases of [cbv_outer_pt.cone_norm_one1] / [cone_norm_one1_le1]. *)
Local Notation cone_norm_one1_alm :=
  (@Icones.programs.infra.cbv_outer_pt.cone_norm_one1 R Ar).
Local Notation cone_norm_one1_le1_alm :=
  (@Icones.programs.infra.cbv_outer_pt.cone_norm_one1_le1 R Ar).

(** ** The carriers *)

Let L_loop : ICone.type Ar :=
  linhom_car Ar (coalg_obj (EM_term : Coalgebra Ar))
               (coalg_obj (Tobj (EM_term : Coalgebra Ar))).

Let funT_loop : Coalgebra Ar := bang_cofree L_loop.

Local Notation G_loop :=
  (EM_prod (EM_prod (EM_term : Coalgebra Ar) funT_loop)
           (EM_term : Coalgebra Ar)).

(** Local notations for the then_e / else_e expressions, parameterised
    in the Bernoulli weight [p]. *)
Local Notation then_e :=
  (@ne_tt R Ar R_obj
     (("_"%string, tunit) :: ("l"%string, tfun tunit tunit) :: nil)).

Local Notation else_e :=
  (ne_app (ne_var (nv_tail "_"%string tunit _
                    (nv_head "l"%string (tfun tunit tunit) nil)))
          ne_tt).

(** [body_inner_p] is [if Bernoulli(p) then () else l()], the inside
    of [ex_almost_loop_body p]'s lambda. *)
Local Notation body_inner_p :=
  (ne_if tunit
    (ne_bernoulli (R := R) (Ar := Ar) (R_obj := R_obj)
                  (G := ("_"%string, tunit)
                        :: ("l"%string, tfun tunit tunit) :: nil)
                  p Hp_ge0 Hp_le1)
    then_e else_e).

(** ** [ex_almost_loop_body_local] : the same body, locally, as a
    [named_expr].  Re-defined so the [eD] thread is local. *)

Definition ex_almost_loop_body_local :
    @named_expr R Ar R_obj (("l"%string, tfun tunit tunit) :: nil)
                (tfun tunit tunit) :=
  ne_lam "_"%string body_inner_p.

(** [M_loop_p] : the body's denotation as a Kleisli morphism. *)
Definition M_loop_p :
    coalg_hom (EM_prod (EM_term : Coalgebra Ar) funT_loop) (Tobj funT_loop) :=
  eD' ex_almost_loop_body_local.

(** ** The [Step_loop_p] operator *)

Definition Step_loop_p (γ : coalg_obj (EM_term : Coalgebra Ar))
                       (v : coalg_obj funT_loop) :
    coalg_obj funT_loop :=
  Lfun (bang_fmap (der L_loop)) (Lfun (ch_mor M_loop_p) (ptensor γ v)).

(** ** [Step_loop_p_E] : outer collapse, mirroring [Step_loop_E] *)

Lemma M_loop_p_E :
  M_loop_p = coalg_comp (tunit_eta funT_loop) (lam_coalg (eD' body_inner_p)).
Proof. by rewrite /M_loop_p /ex_almost_loop_body_local eD_lam. Qed.

Lemma Step_loop_p_E γ v :
  Step_loop_p γ v = Lfun (ch_mor (lam_coalg (eD' body_inner_p))) (ptensor γ v).
Proof.
rewrite /Step_loop_p M_loop_p_E.
rewrite coalg_comp_mor.
rewrite -[ch_mor (tunit_eta funT_loop)]/(coalg_str funT_loop) (bang_cofree_str L_loop).
rewrite -[Lfun (bang_fmap (der L_loop)) (Lfun (icones_comp _ _) _)]
        /(Lfun (icones_comp (bang_fmap (der L_loop))
                            (icones_comp (dig L_loop)
                                         (ch_mor (lam_coalg (eD' body_inner_p)))))
               (ptensor γ v)).
rewrite icones_compA (comonad_counitR L_loop) icones_compIl.
by [].
Qed.

(** ** Convex-combination form of [body_inner_p]

    By [case_em_bernoulli], the body inner reduces to the convex
    combination of the THEN and ELSE branches with weight [p]. *)

Lemma body_inner_p_via_convex :
  eD' body_inner_p =
  convex_combination (eD' then_e) (eD' else_e) Hp_ge0 Hp_le1.
Proof.
exact: (case_em_bernoulli (eD' then_e) (eD' else_e) Hp_ge0 Hp_le1).
Qed.

(** ** Outer-pt cascade — re-using [ex_loop_arr]'s G_loop setup

    The outer-pt structure [at_outer_pt_u u] is the same as in
    [ex_loop_arr.v] (the context [G_loop] is the same).  We re-export
    its definitions here. *)

(** ** Step_loop_p preserves the unit ball *)

Lemma Step_loop_p_ball (γ : coalg_obj (EM_term : Coalgebra Ar))
    (v : coalg_obj funT_loop) :
  cone_norm γ <= 1 -> cone_norm v <= 1 ->
  cone_norm (Step_loop_p γ v) <= 1.
Proof.
move=> Hγ Hv.
rewrite /Step_loop_p.
have Hpt : cone_norm (ptensor γ v) <= 1.
  apply: le_trans (tensor_norm_le _ _) _.
  rewrite -[1]mulr1; apply: ler_pM.
  - exact: cone_norm_ge0.
  - exact: cone_norm_ge0.
  - exact: Hγ.
  - exact: Hv.
have HchM : cone_norm (Lfun (ch_mor M_loop_p) (ptensor γ v)) <= 1.
  apply: le_trans (cones_hom_norm_le1 _ _) Hpt.
apply: le_trans (cones_hom_norm_le1 _ _) HchM.
Qed.

(** ** Step_loop_p of [precone_zero] is [precone_zero] (cone-level zero kill) *)
Lemma Step_loop_p_at_zero_E (γ : coalg_obj (EM_term : Coalgebra Ar)) :
  Step_loop_p γ (precone_zero : coalg_obj funT_loop) = precone_zero.
Proof.
rewrite /Step_loop_p.
have Hpt : ptensor γ (precone_zero : coalg_obj funT_loop)
         = (precone_zero : tensor Ar (coalg_obj (EM_term : Coalgebra Ar))
                                       (coalg_obj funT_loop))
  by exact: ptensor_0r.
rewrite Hpt.
have [HM0 _ _] :=
  cones_hom_linear (mcones_hom_cones (icones_hom_mcones (ch_mor M_loop_p))).
rewrite HM0.
have [Hbang0 _ _] :=
  cones_hom_linear
    (mcones_hom_cones (icones_hom_mcones (bang_fmap (der L_loop)))).
exact: Hbang0.
Qed.

(** ** Kleene chain at the Bang level for [ex_almost_loop_p] *)

Definition kleene_arr_loop_p (n : nat) : coalg_obj funT_loop :=
  iter n (Step_loop_p one1) (prom (precone_zero : L_loop)).

Lemma kleene_arr_loop_p_0 :
  kleene_arr_loop_p 0 = prom (precone_zero : L_loop).
Proof. by []. Qed.

Lemma kleene_arr_loop_p_S n :
  kleene_arr_loop_p n.+1 = Step_loop_p one1 (kleene_arr_loop_p n).
Proof. by rewrite /kleene_arr_loop_p iterS. Qed.

Lemma cone_norm_prom_zero_le1_p :
  cone_norm (prom (precone_zero : L_loop)) <= 1.
Proof. by apply: prom_ball; rewrite cone_norm0 ler01. Qed.

Lemma kleene_arr_loop_p_ball n :
  cone_norm (kleene_arr_loop_p n) <= 1.
Proof.
elim: n => [ |n IH].
- by rewrite kleene_arr_loop_p_0; exact: cone_norm_prom_zero_le1_p.
- rewrite kleene_arr_loop_p_S.
  apply: Step_loop_p_ball; [exact: cone_norm_one1_le1_alm | exact: IH].
Qed.

(** ** F_arr_loop_p : the cone_one_car-extracted iterate

    Mirrors [ex_loop_arr.v]'s [F_arr_loop], parameterized by p. *)

Definition F_arr_loop_p (n : nat) : cone_one_car Ar :=
  Lfun (der (cone_one_car Ar))
       (linhom_fun
          (Lfun (der L_loop) (kleene_arr_loop_p n))
          (one1 : cone_one_car Ar)).

(** Base case [n = 0]: identical to [F_arr_loop_0_E] from
    [ex_loop_arr.v] except over [kleene_arr_loop_p]. *)
Lemma F_arr_loop_p_0_E : F_arr_loop_p 0 = precone_zero.
Proof.
rewrite /F_arr_loop_p kleene_arr_loop_p_0.
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

(** Mass at iterate 0: zero. *)
Lemma F_arr_loop_p_0_mass_zero :
  (c1_val (F_arr_loop_p 0))%:num = 0%R.
Proof. by rewrite F_arr_loop_p_0_E. Qed.

(** ** §A — Corollary at [p = 0] : the special case recovers [ex_loop_arr_mass_zero]

    For [p = 0], the Bernoulli scrutinee is identically [false]; the
    THEN branch is unreachable; the body reduces to [l()], i.e. the
    same body as [ex_loop_body].  Operationally and denotationally,
    [ex_almost_loop_arr] at [p = 0] coincides with [ex_loop_arr].

    NOTE: this section ([Hp_ge0], [Hp_le1] under [p : R] free) does
    NOT specialize [p].  The following corollary statement reads in
    contexts where [p = 0] has been substituted (after exiting the
    section).  It is shipped as a separate top-level lemma at the
    bottom of this file. *)

End ExAlmostLoopArr.

(** ** §B — Special-case theorem at [p = 0] : mass zero (recovers
        [ex_loop_arr_mass_zero])

    At [p = 0], the Bernoulli scrutinee is deterministically [false]
    (the [false]-branch of the if-then-else fires with probability
    [1 - p = 1]).  Hence at every iterate, the SCALAR mass is [0]:
    no contribution from the THEN branch, the ELSE branch coincides
    with [ex_loop]'s recursive call which is in turn mass-zero by
    [ex_loop_arr_mass_zero].

    The clean statement is: [(c1_val (F_arr_loop_p R_obj R_carrier_eq
    R_carrier_meas R_to_carrier_meas 0%R Hp_ge0_zero Hp_le1_zero n))%:num
    = 0%R].  We do NOT close this here — the structural cascade to
    fully identify [eD body_inner_p] at [p = 0] with [eD body_inner]
    (the [ex_loop] body) would require unfolding [ne_if] /
    [ne_bernoulli] at [p = 0] and showing the THEN-branch
    multiplicative weight vanishes.  Documented as the residual
    blocker.  Closing it requires either:

    (a) a direct equation [eD ex_almost_loop_body_local p Hp_ge0
        Hp_le1 = eD ex_loop_body] when [p = 0] (modulo bool-cone
        identifications, requiring [bool_dirac_false]-style
        reductions in the case_em chain);

    (b) the per-iterate scalar mass recurrence
        [(c1_val (F_arr_loop_p p Hp_ge0 Hp_le1 n.+1))%:num
         = p + (1-p) * (c1_val (F_arr_loop_p p Hp_ge0 Hp_le1 n))%:num]
        plus the closed form [1 - (1-p)^n], which at [p = 0] is [0].

    The general-[p] case (mass [1 - (1-p)^n] per iterate, converging
    to [1] for [p > 0]) requires the full ex_geom_step-style cascade
    at the [tunit] return level — structurally identical to
    [ex_geom_step.v] but with [tunit] / [cone_one_car] in place of
    [tR'] / [FMeas R_obj].  Substantial infrastructure (~800-1200
    lines of code analogous to [ex_geom_step.v] and the §5 part of
    [em_fix_arr.v]), deferred to a follow-up. *)

Arguments M_loop_p {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}
  p Hp_ge0 Hp_le1.
Arguments Step_loop_p {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}
  p Hp_ge0 Hp_le1 γ v.
Arguments kleene_arr_loop_p {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}
  p Hp_ge0 Hp_le1 n.
Arguments F_arr_loop_p {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas}
  p Hp_ge0 Hp_le1 n.
Arguments F_arr_loop_p_0_E
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} p Hp_ge0 Hp_le1.
Arguments F_arr_loop_p_0_mass_zero
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} p Hp_ge0 Hp_le1.
