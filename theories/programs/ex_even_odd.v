(**md*** [ex_even_odd] — the mutual-recursion witness diverges

    BEYOND THE PAPER.  This file is NOT part of the Ehrhard-Geoffroy
    2025 formalization (paper §2-§9).  It is one headline CBV program
    of the chapter; the six-step reduction-chain skeleton it runs on is
    documented once, for the rejection sampler, in
    [theories/programs/ex_reject_headline.v].

    The [fix_mr] pair of [theories/programs/examples.v]
    [[
       fix_mr p : (1→1) × (1→1) in (λn. snd p n, λn. fst p n)
    ]]
    is delegation-only: each component immediately calls the other,
    with no base case.  The zero-seeded Kleene chain of the conjugated
    body therefore stays at the cone-zero forever, so the fixpoint
    VALUE at the base cone [free_base pair_ty = (1⊸1) & (1⊸1)] is the
    cone-zero.  The pair denotation is the backward image of the
    PROMOTED zero ([0! ⊗ 0!], the pair of promoted-zero functions —
    itself never the cone-zero, by [eD_fix_mr_prod_at_setlike_neq0]),
    but each projection applied to the unit argument [()] runs the
    promoted-zero function and lands in the cone-zero of the unit cone.

    Results:
    - [ex_even_odd_fix_value_zero] : the seeded fixpoint VALUE is the
      cone-zero;
    - [ex_even_odd_pair_cbv_value] : the pair denotes [0! ⊗p 0!];
    - [ex_even_cbv_diverges] / [ex_odd_cbv_diverges] : both
      projections applied to [()] have mass [0].

    Supporting kit: [theories/programs/infra/cbv_anchors.v] (the
    setlike-point kit), [theories/programs/infra/em_fix_mr.v] (the
    mutual-recursion fixpoint, via the Seely isomorphism),
    [theories/programs/infra/em_fix_value.v] (the seeded
    value-fixpoint combinator).

    Author: Guillaume Baudart <guillaume.baudart@inria.fr>. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals constructive_ereal.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import ereal.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import measure dirac_measure numfun.
From mathcomp.analysis Require Import lebesgue_integral_definition.
From mathcomp.analysis Require Import lebesgue_integral_nonneg.
From mathcomp.analysis Require Import lebesgue_integral_monotone_convergence.
From mathcomp.analysis Require Import topology normedtype sequences.
Import numFieldTopology.Exports.

From Stdlib Require Import Strings.String.

Require Import Icones.prelude.geom_series.
Require Import Icones.cones.precone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.cone.
Require Import Icones.cones.cone_cat.
Require Import Icones.cones.omega_general.
Require Import Icones.icones.bool_cone.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.mcones.path.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_integral.
Require Import Icones.icones.examples_icone.
Require Import Icones.icones.icone_cat.
Require Import Icones.stable.scones_cat.
Require Import Icones.stable.scones_ccc.
Require Import Icones.homs.icones_iso.
Require Import Icones.homs.linhom.
Require Import Icones.homs.linhom_functor.
Require Import Icones.homs.bilin.
Require Import Icones.homs.tensor.
Require Import Icones.homs.tensor_construct.
Require Import Icones.homs.smcc.
Require Import Icones.exp.exp_adjunction.
Require Import Icones.exp.bang.
Require Import Icones.exp.seely_defs.
Require Import Icones.exp.seely.
Require Import Icones.homs.tensor_hom_iso.
Require Import Icones.exp.bool_case_hom.
Require Import Icones.exp.coalgebra.
Require Import Icones.programs.infra.bool_cone_coalg.
Require Import Icones.cbv.fmeas_lax.
Require Import Icones.cbv.em_cat.
Require Import Icones.cbv.em_seely_comonoid.
Require Import Icones.cbv.em_cartesian.
Require Import Icones.cbv.cbv_adjunction.
Require Import Icones.programs.ppl.
Require Import Icones.programs.infra.em_fix.
Require Import Icones.programs.infra.em_fix_mr.
Require Import Icones.programs.infra.em_fix_value.
Require Import Icones.programs.ppl_cbv.
Require Import Icones.programs.infra.cbv_anchors.
Require Import Icones.programs.infra.cbv_fix_unfold.
Require Import Icones.programs.infra.let_sample_law.
Require Import Icones.programs.examples.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Opaque tensor_mor tensor_assoc tensor_lunit tensor_runit tensor_braid
       ptensor tau Seely2.
Local Opaque dig der prom bang_fmap d_bang e_bang unit_cofree_str Coalg
       tens_cofree_str m_bang.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section ExEvenOddRider.
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
Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '!'" := (prom x) (at level 2, format "x '!'").
Local Notation eD_cbv' :=
  (@eD_cbv R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation eD' :=
  (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation L := (linhom_car Ar (coalg_obj (tyD_cbv (@tunit R Ar)))
                                    (coalg_obj (tyD_cbv (@tunit R Ar)))).
Local Notation pair_ty :=
  (tprod (tfun (@tunit R Ar) tunit) (tfun tunit tunit)).

Let Hone : cone_norm (one1 : cone_one_car Ar) <= 1.
Proof. by rewrite one1_norm. Qed.

(** *** A morphism out of the one-dimensional unit cone is determined
    by its value at the unit point *)

(** Every point of [cone_one_car Ar] is a scalar multiple of [one1]. *)
Lemma cone_one_scale_rep (x : cone_one_car Ar) :
  x = precone_scale (c1_val x) (one1 : cone_one_car Ar).
Proof. by apply: cone_one_eq; apply: val_inj => /=; rewrite mulr1. Qed.

(** A linhom from [cone_one_car Ar] that vanishes at [one1] is the
    zero linhom: [cone_one_car] is one-dimensional, so a linear map is
    pinned by its value at [one1]. *)
Lemma linhom_cone_one_zero (D : ICone.type Ar)
    (f : linhom_car Ar (cone_one_car Ar) D) :
  linhom_fun f one1 = precone_zero -> f = precone_zero.
Proof.
move=> Hf; apply: linhom_eq => x; rewrite linhom_fun_zero.
have [_ _ HZ] := linhom_pre_linear (linhom_pre_of f).
rewrite [in LHS](cone_one_scale_rep x).
rewrite -[linhom_fun f (c1_val x *: one1)%PC]/(f (c1_val x *: one1)%PC) HZ.
by rewrite -[f one1]/(linhom_fun f one1) Hf precone_scale_0r.
Qed.

(** *** The conjugated body and its zero-seeded Kleene chain *)

(** The decomposition iso [tyD_cbv pair_ty ≅ !̃((1⊸1) & (1⊸1))]. *)
Local Notation eo_iso := (free_decomp pair_ty erefl).
Local Notation eo_bwd := (ch_mor (ci_bwd eo_iso)).
Local Notation eo_fwd := (ch_mor (ci_fwd eo_iso)).

(** The body of the [fix_mr], conjugated by the decomposition iso —
    the endofunction whose value-fixpoint is taken at the base cone. *)
Definition eo_W0 :
    linhom_car Ar (Bang Ar (sprod L L)) (Bang Ar (sprod L L)) :=
  linhom_map_fun eo_bwd eo_fwd
    (Lfun (tensor_curry (eD_cbv' (ex_even_odd_body : @named_expr R Ar R_obj _ _)))
          one1).

Lemma eo_W0_ball : cone_norm eo_W0 <= 1.
Proof.
apply: le_trans (linhom_map_norm_le1 _ _ _) _.
exact: le_trans (cones_hom_norm_le1 _ _) Hone.
Qed.

(** The pairing of the two cone-zeros is the cone-zero of the product
    cone (componentwise). *)
Lemma sprod_pair_zero :
  sprod_pair (precone_zero : L) (precone_zero : L) = precone_zero.
Proof. by apply: cones_prod_eq => -[]. Qed.

(** The decomposition iso, forward, sends the pair of promoted zeros to
    the promoted product zero (the Seely-2 forward on pure tensors). *)
Let Hzero : cone_norm (precone_zero : L) <= 1.
Proof. by rewrite cone_norm0. Qed.

Lemma eo_fwd_tensor0 :
  Lfun eo_fwd ((precone_zero : L)! ⊗p (precone_zero : L)!) =
  (precone_zero : sprod L L)!.
Proof.
rewrite -[eo_fwd]/(icones_comp (ch_mor (ci_fwd (seely2_em_iso L L)))
  (ch_mor (ci_fwd (coalg_iso_prod
     (coalg_iso_id (tyD_cbv (tfun (@tunit R Ar) tunit)))
     (coalg_iso_id (tyD_cbv (tfun (@tunit R Ar) tunit))))))).
rewrite Lfun_comp tensor_morE.
rewrite -[ch_mor (ci_fwd (coalg_iso_id (tyD_cbv (tfun (@tunit R Ar) tunit))))]
        /(icones_id Ar (coalg_obj (tyD_cbv (tfun (@tunit R Ar) tunit)))).
rewrite !icones_idE.
rewrite -[ch_mor (ci_fwd (seely2_em_iso L L))]/(iso_fwd (Seely2 L L)).
by rewrite (Seely2E (precone_zero : L) (precone_zero : L) Hzero Hzero)
   sprod_pair_zero.
Qed.

(** The decomposition iso, backward, sends the promoted product zero to
    the pair of promoted zeros (inverse of [eo_fwd_tensor0]). *)
Lemma eo_bwd_prom0 :
  Lfun eo_bwd ((precone_zero : sprod L L)!) =
  (precone_zero : L)! ⊗p (precone_zero : L)!.
Proof.
have Hcan : forall x, Lfun eo_bwd (Lfun eo_fwd x) = x.
  move=> x.
  rewrite -[Lfun eo_bwd (Lfun eo_fwd x)]/(Lfun (icones_comp eo_bwd eo_fwd) x).
  by rewrite (ci_fwdK eo_iso) icones_idE.
by rewrite -eo_fwd_tensor0; exact: Hcan.
Qed.

(** The body environment [one1 ⊗ (0! ⊗ 0!)] is a setlike unit-ball
    point: the rec-bound pair value is the pair of promoted zeros. *)
Lemma eo_env_ball :
  cone_norm (one1 ⊗p ((precone_zero : L)! ⊗p (precone_zero : L)!)) <= 1.
Proof.
rewrite tensor_normME one1_norm mul1r tensor_normME.
by apply: mulr_ile1; rewrite ?cone_norm_ge0// (prom_ball Hzero).
Qed.

(** Each promoted-zero function component is setlike in the cofree
    coalgebra [tyD_cbv (1→1)]. *)
Lemma eo_comp_setlike :
  Lfun (coalg_str (tyD_cbv (tfun (@tunit R Ar) tunit))) ((precone_zero : L)!) =
  ((precone_zero : L)!)!.
Proof.
rewrite -[tyD_cbv (tfun (@tunit R Ar) tunit)]/(bang_cofree L) bang_cofree_str.
exact: (dig_prom _ Hzero).
Qed.

Lemma eo_pair_ball :
  cone_norm ((precone_zero : L)! ⊗p (precone_zero : L)!) <= 1.
Proof.
by rewrite tensor_normME; apply: mulr_ile1; rewrite ?cone_norm_ge0// (prom_ball Hzero).
Qed.

(** The pair of promoted zeros is setlike in [tyD_cbv pair_ty]. *)
Lemma eo_pair_setlike :
  Lfun (coalg_str (tyD_cbv pair_ty))
       ((precone_zero : L)! ⊗p (precone_zero : L)!) =
  ((precone_zero : L)! ⊗p (precone_zero : L)!)!.
Proof.
rewrite -[tyD_cbv pair_ty]/(EM_prod (tyD_cbv (tfun (@tunit R Ar) tunit))
                                    (tyD_cbv (tfun (@tunit R Ar) tunit))).
exact: (coalg_str_tensor_setlike (P:=tyD_cbv (tfun (@tunit R Ar) tunit))
          (Q:=tyD_cbv (tfun (@tunit R Ar) tunit))
          (prom_ball Hzero) (prom_ball Hzero) eo_comp_setlike eo_comp_setlike).
Qed.

Lemma eo_env_setlike :
  Lfun (coalg_str (ctxD_cbv (drop_names ((("p"%string, pair_ty) :: nil)))))
       (one1 ⊗p ((precone_zero : L)! ⊗p (precone_zero : L)!)) =
  (one1 ⊗p ((precone_zero : L)! ⊗p (precone_zero : L)!))!.
Proof.
rewrite -[ctxD_cbv (drop_names [:: ("p"%string, pair_ty)])]
        /(EM_prod EM_term (tyD_cbv pair_ty)).
exact: (coalg_str_tensor_setlike (P:=EM_term) (Q:=tyD_cbv pair_ty)
          Hone eo_pair_ball coalg_str_one1 eo_pair_setlike).
Qed.

(** *** The two components evaluate to the promoted-zero function

    The body environment is [one1 ⊗ (0! ⊗ 0!)]; each component lambda
    is [λn. snd/fst p n], whose curried body is the cone-zero map: it
    looks up the [0!] component of [p], runs [der 0! = 0], the zero
    linhom, on the unit argument. *)

(** The body environment extended with the (unit) argument binder
    ["n"] — the point at which the lambda body is read. *)
Local Notation eo_env2 :=
  ((one1 ⊗p ((precone_zero : L)! ⊗p (precone_zero : L)!)) ⊗p one1)
  (only parsing).

Lemma eo_env2_ball : cone_norm eo_env2 <= 1.
Proof. by rewrite tensor_normME one1_norm mulr1 eo_env_ball. Qed.

Lemma eo_env2_setlike :
  Lfun (coalg_str (ctxD_cbv (drop_names
          [:: ("n"%string, @tunit R Ar); ("p"%string, pair_ty)])))
       eo_env2 = eo_env2!.
Proof.
rewrite -[ctxD_cbv (drop_names
          [:: ("n"%string, @tunit R Ar); ("p"%string, pair_ty)])]
        /(EM_prod (ctxD_cbv (drop_names [:: ("p"%string, pair_ty)]))
                  (tyD_cbv (@tunit R Ar))).
exact: (coalg_str_tensor_setlike
          (P:=ctxD_cbv (drop_names [:: ("p"%string, pair_ty)]))
          (Q:=tyD_cbv (@tunit R Ar))
          eo_env_ball Hone eo_env_setlike coalg_str_one1).
Qed.

(** The rec-bound variable ["p"] projects the pair of promoted zeros. *)
Lemma eo_var_p_at :
  Lfun (eD_cbv' ([# "p"] : @named_expr R Ar R_obj
          [:: ("n"%string, @tunit R Ar); ("p"%string, pair_ty)] pair_ty))
       eo_env2 =
  (precone_zero : L)! ⊗p (precone_zero : L)!.
Proof.
apply: (eq_trans (y := Lfun (icones_comp
  (em_proj2_mor (R:=R) EM_term (tyD_cbv pair_ty))
  (em_proj1_mor (R:=R) (ctxD_cbv (drop_names [:: ("p"%string, pair_ty)]))
     (tyD_cbv (@tunit R Ar))))
  eo_env2)).
  by [].
rewrite Lfun_comp.
rewrite (em_proj1_morE (Q:=tyD_cbv (@tunit R Ar)) Hone coalg_str_one1).
exact: (em_proj2_morE (P:=EM_term) Hone coalg_str_one1).
Qed.

(** Both components have the SAME shape [λn. q @ n], and the run does
    not look at [q] beyond its value: the [λn]-packaging promotes at
    the setlike body environment ([adj_psi_at_setlike]), the
    application clause computes there ([eD_app_at_setlike]), and
    [der 0! = 0] annihilates whatever argument follows.  The
    [fst]/[snd] difference between the twins is confined to the
    hypothesis [Hq]. *)
Lemma eo_lam_proj_zero
    (q : @named_expr R Ar R_obj
           [:: ("n"%string, @tunit R Ar); ("p"%string, pair_ty)]
           (tfun (@tunit R Ar) tunit))
    (a : @named_expr R Ar R_obj
           [:: ("n"%string, @tunit R Ar); ("p"%string, pair_ty)]
           (@tunit R Ar)) :
  Lfun (eD_cbv' q) eo_env2 = (precone_zero : L)! ->
  Lfun (eD_cbv' (ne_lam "n"%string (t1 := @tunit R Ar) (ne_app q a)))
       (one1 ⊗p ((precone_zero : L)! ⊗p (precone_zero : L)!)) =
  (precone_zero : L)!.
Proof.
move=> Hq.
rewrite eD_lam_E.
set g := (tensor_curry _).
rewrite (adj_psi_at_setlike g eo_env_ball eo_env_setlike).
congr (prom _); rewrite /g.
apply: linhom_cone_one_zero; rewrite tensor_curryE.
rewrite (eD_app_at_setlike
           (G := [:: ("n"%string, @tunit R Ar); ("p"%string, pair_ty)])
           (t1 := tunit) (t2 := tunit)
           R_carrier_eq R_carrier_meas R_to_carrier_meas
           eo_env2_ball eo_env2_setlike).
rewrite Hq (der_prom _ Hzero).
exact: linhom_fun_zero.
Qed.

Lemma eo_lam_a_zero :
  Lfun (eD_cbv' (ex_even_odd_lam_a : @named_expr R Ar R_obj _ _))
       (one1 ⊗p ((precone_zero : L)! ⊗p (precone_zero : L)!)) =
  (precone_zero : L)!.
Proof.
apply: eo_lam_proj_zero; rewrite eD_snd_E Lfun_comp eo_var_p_at.
exact: (em_proj2_morE (P:=tyD_cbv (tfun (@tunit R Ar) tunit))
          (prom_ball Hzero) eo_comp_setlike).
Qed.

Lemma eo_lam_b_zero :
  Lfun (eD_cbv' (ex_even_odd_lam_b : @named_expr R Ar R_obj _ _))
       (one1 ⊗p ((precone_zero : L)! ⊗p (precone_zero : L)!)) =
  (precone_zero : L)!.
Proof.
apply: eo_lam_proj_zero; rewrite eD_fst_E Lfun_comp eo_var_p_at.
exact: (em_proj1_morE (Q:=tyD_cbv (tfun (@tunit R Ar) tunit))
          (prom_ball Hzero) eo_comp_setlike).
Qed.

(** *** The decisive fixpoint step: the conjugated body fixes the
    promoted product zero *)

(** The (un-conjugated) body, applied to the pair of promoted zeros,
    returns it unchanged: the two components are independently the
    promoted-zero function. *)
Lemma eo_body_tensor0 :
  linhom_fun
    (Lfun (tensor_curry
       (eD_cbv' (ex_even_odd_body : @named_expr R Ar R_obj _ _))) one1)
    ((precone_zero : L)! ⊗p (precone_zero : L)!) =
  (precone_zero : L)! ⊗p (precone_zero : L)!.
Proof.
rewrite tensor_curryE /ex_even_odd_body eD_pair_E.
rewrite /em_pair_mor Lfun_comp
  (coalg_d_setlike (P:=ctxD_cbv (drop_names [:: ("p"%string, pair_ty)]))
     eo_env_ball eo_env_setlike) tensor_morE.
by congr (_ ⊗p _); [exact: eo_lam_a_zero | exact: eo_lam_b_zero].
Qed.

(** The conjugated body fixes the promoted product zero. *)
Lemma eo_W0_prom0 :
  linhom_fun eo_W0 ((precone_zero : sprod L L)!) =
  (precone_zero : sprod L L)!.
Proof.
rewrite /eo_W0 linhom_map_funE eo_bwd_prom0 eo_body_tensor0.
exact: eo_fwd_tensor0.
Qed.

(** *** The zero-seeded Kleene chain and the fixpoint value *)

(** Every iterate of the interleaved chain is the cone-zero: the seed
    is [0], and [eo_W0_prom0] keeps the step at [der 0! = 0]. *)
Lemma even_odd_iter_zero n : fix_chain eo_W0 n = precone_zero.
Proof.
elim: n => [ | n IH]; first exact: fix_chain_0.
rewrite fix_chain_S IH eo_W0_prom0.
by rewrite (der_prom (precone_zero : sprod L L)) // cone_norm0.
Qed.

(** Hence the fixpoint value at the base cone is the cone-zero. *)
Lemma ex_even_odd_fix_value_zero :
  sc_fun (fix_value (free_base pair_ty)) eo_W0 = precone_zero.
Proof.
rewrite (fix_value_E eo_W0_ball).
apply: precone_le_anti.
- by apply: cone_sup_ball_lub => n; rewrite even_odd_iter_zero; exact: precone_le_refl.
- exact: precone_le0.
Qed.

(** *** The pair denotation and the two projection runs *)

(** The closed pair denotation is the backward image of the promoted
    base-cone zero, i.e. the pair of promoted-zero functions [0! ⊗ 0!].
    (It is NOT the cone-zero — see [eD_fix_mr_prod_at_setlike_neq0]; the
    divergence shows up only after projecting and applying.) *)
Lemma ex_even_odd_pair_cbv_value :
  Lfun (eD_cbv' (ex_even_odd_pair : @named_expr R Ar R_obj nil pair_ty))
       one1 =
  (precone_zero : L)! ⊗p (precone_zero : L)!.
Proof.
rewrite -[ex_even_odd_pair]/(ne_fix_mr "p" pair_ty erefl
  (ex_even_odd_body : @named_expr R Ar R_obj _ _)).
rewrite (eD_fix_mr_prod_at_setlike "p" (erefl : is_free_coalg_type pair_ty)
  (ex_even_odd_body : @named_expr R Ar R_obj _ _) Hone coalg_str_one1).
rewrite -/eo_W0 ex_even_odd_fix_value_zero.
exact: eo_bwd_prom0.
Qed.

(** The first projection at the unit argument: [ex_even @ ()] denotes
    the cone-zero of the unit cone (mass [0]). *)
Definition ex_even_run :
    @named_expr R Ar R_obj nil (@tunit R Ar) :=
  ne_app (ex_even : @named_expr R Ar R_obj nil (tfun tunit tunit)) ne_tt.

Definition ex_odd_run :
    @named_expr R Ar R_obj nil (@tunit R Ar) :=
  ne_app (ex_odd : @named_expr R Ar R_obj nil (tfun tunit tunit)) ne_tt.

(** [ex_even = fst pair] evaluates to the promoted-zero function. *)
Lemma ex_even_cbv_fun_zero :
  Lfun (eD_cbv' (ex_even : @named_expr R Ar R_obj nil (tfun tunit tunit)))
       one1 = (precone_zero : L)!.
Proof.
rewrite -[ex_even]/(ne_fst (ex_even_odd_pair : @named_expr R Ar R_obj _ _)).
rewrite eD_fst_E Lfun_comp ex_even_odd_pair_cbv_value.
exact: (em_proj1_morE (Q:=tyD_cbv (tfun (@tunit R Ar) tunit))
          (prom_ball Hzero) eo_comp_setlike).
Qed.

(** [ex_odd = snd pair] evaluates to the promoted-zero function. *)
Lemma ex_odd_cbv_fun_zero :
  Lfun (eD_cbv' (ex_odd : @named_expr R Ar R_obj nil (tfun tunit tunit)))
       one1 = (precone_zero : L)!.
Proof.
rewrite -[ex_odd]/(ne_snd (ex_even_odd_pair : @named_expr R Ar R_obj _ _)).
rewrite eD_snd_E Lfun_comp ex_even_odd_pair_cbv_value.
exact: (em_proj2_morE (P:=tyD_cbv (tfun (@tunit R Ar) tunit))
          (prom_ball Hzero) eo_comp_setlike).
Qed.

(** The even component diverges: [ex_even @ ()] has mass [0]. *)
Theorem ex_even_cbv_diverges :
  Lfun (eD_cbv' ex_even_run) one1 = precone_zero.
Proof.
rewrite /ex_even_run.
rewrite (eD_app_at_setlike (G := nil) (t1 := @tunit R Ar) (t2 := tunit)
           R_carrier_eq R_carrier_meas R_to_carrier_meas Hone coalg_str_one1).
rewrite ex_even_cbv_fun_zero (der_prom _ Hzero).
exact: linhom_fun_zero.
Qed.

(** The odd component diverges: [ex_odd @ ()] has mass [0]. *)
Theorem ex_odd_cbv_diverges :
  Lfun (eD_cbv' ex_odd_run) one1 = precone_zero.
Proof.
rewrite /ex_odd_run.
rewrite (eD_app_at_setlike (G := nil) (t1 := @tunit R Ar) (t2 := tunit)
           R_carrier_eq R_carrier_meas R_to_carrier_meas Hone coalg_str_one1).
rewrite ex_odd_cbv_fun_zero (der_prom _ Hzero).
exact: linhom_fun_zero.
Qed.

End ExEvenOddRider.
