(**md**************************************************************************)
(** * Rejection sampling & conditioning over ANY model, with the acceptance
      test a PROGRAM predicate — the unified master theorem

    BEYOND THE PAPER.  This file is NOT part of the Ehrhard-Geoffroy
    2025 formalization (paper §2-§9).  It proves ONE unified master
    theorem for the clean [reject]/[condition] combinators of
    [theories/programs/reject_condition.v] (design doc
    [docs/hard_reject_condition.md]).

    The acceptance test is a PROGRAM predicate [f : b -> tbool],
    supplied as an argument exactly like the model [m : a -> b].  Since
    [tbool] denotes a point of the 2-point sub-probability cone
    ([tyD_cbv tbool = bool_cone_car]), the only quantity the
    combinators care about is the ACCEPTANCE PROBABILITY

       [t(x) := true-mass ⟦f x⟧ = (bc_t ⟦f x⟧)%:num ∈ [0,1]].

    Two regimes, ONE mechanism (design §1):
    - [f] deterministic (⟦f x⟧ a Dirac) ⟹ [t = 1_A] the accept-set
      indicator — HARD conditioning;
    - [f] a coin (⟦f x⟧ non-Dirac) ⟹ [t] a density — SOFT conditioning.

    ** The set-up (design §3-§4)

    The theorems quantify over the model VALUE [g!] (an arbitrary
    unit-ball linear map [g : U⟦ta⟧ ⊸ FMeas], the shape EVERY
    lambda-written model denotes), the predicate VALUE [fpred!]
    ([fpred : U⟦tb⟧ ⊸ U⟦tbool⟧], the shape every lambda-written
    predicate denotes), and the input VALUE [a₀] (a setlike unit-ball
    point).  Writing [ν_M := g(a₀) : FMeas] for the model's output
    sub-distribution, [m₀ := ν_M(setT)], [s_r := ⟦f⟧(δ_r) = fpred(δ_r)]
    for the acceptance distribution at [r], [t(r) := (bc_t s_r)%:num],
    [If := ∫ t dν_M], [IUf U := ∫_U t dν_M], the results are the
    accept-probability versions of the classical rejection identities.

    Totality (design §5, top subtlety): the [bool_case] else-weight is
    [bc_f s_r] — NOT [1 - bc_t s_r] — so to land the sub-probability
    normaliser [Z = 1 - m₀ + ∫ t] we assume the predicate is TOTAL,
    [∀ r, cone_norm s_r = 1] (i.e. [bc_t s_r + bc_f s_r = 1]).  This is
    faithful: BOTH doc regimes (a deterministic bool-Dirac and a
    bernoulli coin) are total.  The condition law ([∫ t]) needs NO
    totality.

    - [reject_model_master] : [(1 - m₀ + If) · ν(U) = IUf U]
      — division-free, unconditional;
    - [reject_model_is_normalised] / [reject_model_mass] /
      [reject_model_mass_one] / [reject_model_zero] — the normalised
      distribution, the total mass, almost-sure termination for
      probability models, and certain-rejection divergence;
    - [condition_model_E] / [condition_model_mass] — the conditioning
      law [ν_cond(U) = ∫_U t dν_M] and the evidence [∫ t dν_M];
    - the readable [reject_prog_*] / [condition_*] headlines over
      closed surface PROGRAMS, and [reject_normalises_condition]
      [Z · ⟦reject⟧ U = ⟦condition⟧ U].

    ** Proof skeleton (reuse of [ex_reject_headline.v] §1 kit)

    1. [reject_comb_val_E] / [reject_after_f_val_E] — strip the outer
       [λf] ([der∘prom]) and read the [fix "rx"] value at the setlike
       base environment [1 ⊗ fpred!].
    2. [reject_model_sup_E] — [ν] is the Kleene [cone_sup_ball] of the
       per-iterate measures [ν_n].
    3. [reject_model_iter_S] — the Kleene step is the inner let-if body
       at the extended setlike environment.
    4. [reject_model_if_at_dirac] — at [δ_r] the [if]-dispatch is
       [bool_case s_r (δ_r) (ν_n)] (via [if_icones_at]), with [s_r]
       the applied predicate value ([rm_scrut_E] through
       [eD_app_at_setlike]).
    5. [reject_model_iter_mass] — the mass recurrence
       [ν_{n+1}(U) = IUf U + (m₀ - If)·ν_n(U)] via the object-generic
       let-law [eD_let_int_obj] + [bc_t]/[bc_f] weights.
    6. the affine cascade [a := IUf U], [q := m₀ - If].

    See also: [theories/programs/reject_condition.v] (the clean
    combinators), [theories/programs/ex_reject_headline.v] (the §1
    setlike/sup kit reused here), [theories/programs/infra/bool_cone.v]
    ([bool_case], [bc_t]/[bc_f], [bool_coord_meas]),
    [theories/programs/infra/let_sample_law.v] (the general let-law),
    [theories/programs/infra/affine_cascade.v].

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

Require Import Icones.prelude.nonneg_extra.
Require Import Icones.cones.precone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.cone.
Require Import Icones.cones.cone_cat.
Require Import Icones.programs.infra.bool_cone.
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
Require Import Icones.homs.bilin.
Require Import Icones.homs.tensor.
Require Import Icones.homs.tensor_construct.
Require Import Icones.homs.smcc.
Require Import Icones.homs.exp_adjunction.
Require Import Icones.homs.bang.
Require Import Icones.homs.seely_defs.
Require Import Icones.homs.seely.
Require Import Icones.homs.tensor_hom_iso.
Require Import Icones.programs.infra.bool_case_hom.
Require Import Icones.homs.coalgebra.
Require Import Icones.programs.infra.bool_cone_coalg.
Require Import Icones.homs.fmeas_lax.
Require Import Icones.homs.em_cat.
Require Import Icones.homs.em_seely_comonoid.
Require Import Icones.homs.em_cartesian.
Require Import Icones.programs.infra.cbv_adjunction.
Require Import Icones.programs.ppl.
Require Import Icones.programs.infra.em_fix.
Require Import Icones.programs.infra.em_fix_value.
Require Import Icones.programs.ppl_cbv.
Require Import Icones.programs.infra.cbv_anchors.
Require Import Icones.programs.infra.cbv_fix_unfold.
Require Import Icones.programs.infra.let_sample_law.
Require Import Icones.programs.infra.affine_cascade.
Require Import Icones.programs.examples.
Require Import Icones.programs.ex_reject_headline.
Require Import Icones.programs.infra.cbv_marginals.
Require Import Icones.programs.reject_condition.

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

(** ** §1 — Kit: [Lfun] is monotone and ω-continuous *)

Section LfunKit.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

(** [Lfun] of an [ICones] morphism is monotone (linearity). *)
Lemma Lfun_le (B C : ICone.type Ar) (h : icones_hom Ar B C) (x y : B) :
  precone_le x y -> precone_le (Lfun h x) (Lfun h y).
Proof.
exact: (linear_increasing
          (cones_hom_linear (mcones_hom_cones (icones_hom_mcones h)))).
Qed.

(** [Lfun] of an [ICones] morphism commutes with ball-sups of chains. *)
Lemma Lfun_sup_ball (B C : ICone.type Ar) (h : icones_hom Ar B C)
    (u : nat -> B)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, cone_norm (u n) <= 1)
    (fuch : forall n, precone_le (Lfun h (u n)) (Lfun h (u n.+1)))
    (fub1 : forall n, cone_norm (Lfun h (u n)) <= 1) :
  Lfun h (cone_sup_ball u uch ub1) =
  cone_sup_ball (fun n => Lfun h (u n)) fuch fub1.
Proof.
rewrite (@cones_hom_continuous _ _ _
           (mcones_hom_cones (icones_hom_mcones h)) u uch ub1 fuch fub1).
exact: cone_sup_ball_irr.
Qed.

End LfunKit.

Arguments Lfun_le {R Ar B C} h {x y}.
Arguments Lfun_sup_ball {R Ar B C} h {u} uch ub1 fuch fub1.

(** ** §2 — [ne_fail] denotes the zero measure

    The clean [reject_condition.v::ne_fail] — a guarded diverging
    fixpoint [fix fail. λ_. fail ()] applied to [()] — denotes
    [precone_zero] at every setlike unit-ball environment.  Its Kleene
    chain from [⊥] is constant zero, so the sup is [precone_zero]. *)

Section FailZero.
Variables (R : realType) (Ar : MeasSubcat R) (P : probObj Ar).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier (po_robj_eq P)).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation eD_cbv' :=
  (@eD_cbv R Ar (po_robj P) (po_robj_eq P) (po_robj_meas P)
           R_to_carrier_meas _ _).
Local Notation "x '!'" := (prom x) (at level 2, format "x '!'").
Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.

Variables (G : named_ctx Ar) (t : ppl_type Ar).
Variable (gam : coalg_obj (ctxD_cbv (drop_names G))).
Hypothesis Hgam_ball : cone_norm gam <= 1.
Hypothesis Hgam_setlike :
  Lfun (coalg_str (ctxD_cbv (drop_names G))) gam = gam!.

Local Notation L :=
  (linhom_car Ar (coalg_obj (tyD_cbv tunit)) (coalg_obj (tyD_cbv t))).

(** Syntactic decomposition of [ne_fail] — all definitional. *)
Definition fvar : @named_expr R Ar (po_robj P)
    (("_"%string, tunit) :: ("fail"%string, tfun tunit t) :: G)
    (tfun tunit t) := [ # "fail" ].

Definition finner : @named_expr R Ar (po_robj P)
    (("_"%string, tunit) :: ("fail"%string, tfun tunit t) :: G) t :=
  [ {fvar} @ () ].

Definition fbody : @named_expr R Ar (po_robj P)
    (("fail"%string, tfun tunit t) :: G) (tfun tunit t) :=
  [ \ "_" ::: tunit => {finner} ].

Lemma ne_fail_decomp :
  @ne_fail R Ar (po_robj P) G t =
  ne_app (ne_fix "fail" fbody) (@ne_tt R Ar (po_robj P) G).
Proof. by []. Qed.

Lemma finner_decomp :
  finner = ne_app fvar (@ne_tt R Ar (po_robj P) _).
Proof. by []. Qed.

(** The body endofunction at the closed environment [gam]. *)
Definition F : linhom_car Ar (Bang Ar L) (Bang Ar L) :=
  Lfun (tensor_curry (eD_cbv' fbody)) gam.

Lemma HF_ball : cone_norm F <= 1.
Proof. exact: le_trans (cones_hom_norm_le1 _ _) Hgam_ball. Qed.

Let Hone1_ball : cone_norm (one1 : cone_one_car Ar) <= 1.
Proof. by rewrite one1_norm. Qed.

(** The "fail"-iterate environment tower. *)
Definition fenv1 (n : nat) :
    coalg_obj (ctxD_cbv (drop_names (("fail"%string, tfun tunit t) :: G))) :=
  gam ⊗p (fix_chain F n)!.

Definition fenv2 (n : nat) :
    coalg_obj (ctxD_cbv (drop_names
      (("_"%string, tunit) :: ("fail"%string, tfun tunit t) :: G))) :=
  fenv1 n ⊗p one1.

Lemma fix_chain_prom_ball n : cone_norm ((fix_chain F n)!) <= 1.
Proof. exact: prom_ball (fix_chain_ball HF_ball n). Qed.

Lemma fix_chain_prom_setlike n :
  Lfun (coalg_str (tyD_cbv (tfun tunit t))) ((fix_chain F n)!) =
  ((fix_chain F n)!)!.
Proof.
rewrite -[tyD_cbv (tfun tunit t)]/(bang_cofree L) bang_cofree_str.
exact: (dig_prom _ (fix_chain_ball HF_ball n)).
Qed.

Lemma fenv1_ball n : cone_norm (fenv1 n) <= 1.
Proof.
by rewrite /fenv1 tensor_normME mulr_ile1 ?cone_norm_ge0
   ?Hgam_ball ?fix_chain_prom_ball.
Qed.

Lemma fenv1_setlike n :
  Lfun (coalg_str (ctxD_cbv (drop_names (("fail"%string, tfun tunit t) :: G))))
       (fenv1 n) = (fenv1 n)!.
Proof.
exact: (coalg_str_tensor_setlike (P:=ctxD_cbv (drop_names G))
          (Q:=tyD_cbv (tfun tunit t)) Hgam_ball (fix_chain_prom_ball n)
          Hgam_setlike (fix_chain_prom_setlike n)).
Qed.

Lemma fenv2_ball n : cone_norm (fenv2 n) <= 1.
Proof.
by rewrite /fenv2 tensor_normME mulr_ile1 ?cone_norm_ge0
   ?fenv1_ball ?one1_norm.
Qed.

Lemma fenv2_setlike n :
  Lfun (coalg_str (ctxD_cbv (drop_names
      (("_"%string, tunit) :: ("fail"%string, tfun tunit t) :: G))))
       (fenv2 n) = (fenv2 n)!.
Proof.
exact: (coalg_str_tensor_setlike
          (P:=ctxD_cbv (drop_names (("fail"%string, tfun tunit t) :: G)))
          (Q:=tyD_cbv tunit) (fenv1_ball n) Hone1_ball
          (fenv1_setlike n) coalg_str_one1).
Qed.

(** The "fail" variable projects the promoted previous iterate. *)
Lemma fail_var_E n :
  Lfun (eD_cbv' fvar) (fenv2 n) = (fix_chain F n)!.
Proof.
apply: (eq_trans (y := Lfun (icones_comp
  (em_proj2_mor (R:=R) (ctxD_cbv (drop_names G)) (tyD_cbv (tfun tunit t)))
  (em_proj1_mor (R:=R)
     (ctxD_cbv (drop_names (("fail"%string, tfun tunit t) :: G)))
     (tyD_cbv tunit)))
  (fenv2 n))).
  by [].
rewrite Lfun_comp.
rewrite (em_proj1_morE (Q:=tyD_cbv tunit) Hone1_ball coalg_str_one1).
exact: (em_proj2_morE (P:=ctxD_cbv (drop_names G)) Hgam_ball Hgam_setlike).
Qed.

(** One Kleene step of the fail body, exposed at the [fenv1] environment. *)
Lemma fix_chain_S_E n :
  fix_chain F n.+1 = Lfun (tensor_curry (eD_cbv' finner)) (fenv1 n).
Proof.
rewrite fix_chain_S /F tensor_curryE.
rewrite -[gam ⊗p (fix_chain F n)!]/(fenv1 n).
rewrite -[fbody]/(ne_lam "_"%string finner) eD_lam_E.
rewrite (adj_psi_at_setlike (tensor_curry (eD_cbv' finner))
           (fenv1_ball n) (fenv1_setlike n)).
exact: (der_prom _ (le_trans (cones_hom_norm_le1 _ _) (fenv1_ball n))).
Qed.

(** Each iterate, applied to the unit input, is the zero measure. *)
Lemma fail_iter_zero n :
  linhom_fun (fix_chain F n) one1 = precone_zero.
Proof.
elim: n => [ | n IH].
  by rewrite fix_chain_0 linhom_fun_zero.
rewrite fix_chain_S_E tensor_curryE -[fenv1 n ⊗p one1]/(fenv2 n).
rewrite finner_decomp.
rewrite (eD_app_at_setlike (po_robj_eq P) (po_robj_meas P) R_to_carrier_meas
           (fenv2_ball n) (fenv2_setlike n)).
rewrite (eD_tt_at_setlike (fenv2_ball n) (fenv2_setlike n)).
rewrite fail_var_E.
by rewrite (der_prom _ (fix_chain_ball HF_ball n)).
Qed.

(** [ne_fail] denotes [precone_zero] at every setlike unit-ball
    environment. *)
Theorem ne_fail_zero :
  Lfun (eD_cbv' (@ne_fail R Ar (po_robj P) G t)) gam = precone_zero.
Proof.
rewrite ne_fail_decomp.
rewrite (eD_app_at_setlike (po_robj_eq P) (po_robj_meas P) R_to_carrier_meas
           Hgam_ball Hgam_setlike).
rewrite (eD_fix_at_setlike "fail"%string fbody Hgam_ball Hgam_setlike).
rewrite -/F (der_prom _ (fix_value_ball F HF_ball)).
rewrite (eD_tt_at_setlike Hgam_ball Hgam_setlike).
rewrite (fix_value_E HF_ball).
have pwch n : precone_le (linhom_fun (fix_chain F n) one1)
                         (linhom_fun (fix_chain F n.+1) one1).
  by rewrite !fail_iter_zero; exact: precone_le0.
have pwub n : cone_norm (linhom_fun (fix_chain F n) one1) <= 1.
  by rewrite fail_iter_zero cone_norm0.
rewrite (linhom_fun_sup_ball (fix_chain_chain HF_ball)
           (fix_chain_ball HF_ball) Hone1_ball pwch pwub).
apply: precone_le_anti; last exact: precone_le0.
by apply: cone_sup_ball_lub => n; rewrite fail_iter_zero; exact: precone_le0.
Qed.

End FailZero.

Arguments ne_fail_zero {R Ar P} R_to_carrier_meas {G t gam}.

(** ** §3 — The reject combinator: reduction chain and master theorem *)

Section RejectModel.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (P : probObj Ar).
Local Notation R_obj := (po_robj P).
Local Notation R_carrier_eq := (po_robj_eq P).
Local Notation R_carrier_meas := (po_robj_meas P).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

(** The model's input type: an ARBITRARY PPL type. *)
Variable (ta : ppl_type Ar).

(** The model's RETURN object [B]. *)
Variable (B : ar_obj Ar).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '!'" := (prom x) (at level 2, format "x '!'").
Local Notation eD_cbv' :=
  (@eD_cbv R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation eD' :=
  (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation cR := (carrier_to_R R_carrier_eq).
Local Notation tR' := (tR R_obj).
Local Notation tB := (tbase B).
Local Notation Lty t1 t2 :=
  (linhom_car Ar (coalg_obj (tyD_cbv t1)) (coalg_obj (tyD_cbv t2))).

(** Abbreviations: predicate, model, recursion types + their cones. *)
Local Notation tfb := (tfun tB tbool).
Local Notation tmod := (tfun ta tB).
Local Notation trec := (tfun tmod tmod).
Local Notation Bmod := (Lty ta tB).
Local Notation Lrec := (Lty tmod tmod).
Local Notation Lfb := (Lty tB tbool).

(** *** The semantic arguments: predicate [fpred!], model [g!], input [a₀] *)

(** The predicate VALUE: the promoted point of an arbitrary unit-ball
    linear map [fpred : U⟦tb⟧ ⊸ U⟦tbool⟧].  TOTALITY (design §5): the
    acceptance distribution at every Dirac is a probability. *)
Variable (fpred : Lfb).
Hypothesis Hf_ball : cone_norm fpred <= 1.
Hypothesis Hpred_total :
  forall r : ar_carrier Ar B, cone_norm (linhom_fun fpred (dirac_fmeas r)) = 1.

Variable (g : Bmod).
Hypothesis Hg_ball : cone_norm g <= 1.

Variable (a0 : coalg_obj (tyD_cbv ta)).
Hypothesis Ha_ball : cone_norm a0 <= 1.
Hypothesis Ha_setlike : Lfun (coalg_str (tyD_cbv ta)) a0 = a0!.

(** The acceptance distribution at a returned value [r] and its
    accept-probability [t(r)]. *)
Local Notation sdist r := (linhom_fun fpred (dirac_fmeas r)).

(** *** Syntactic decomposition of [ne_reject] — all definitional. *)

Local Notation ctx_f :=
  (("f"%string, tfb) :: nil).
Local Notation ctx_rx :=
  (("rx"%string, trec) :: ("f"%string, tfb) :: nil).
Local Notation ctx_m :=
  (("m"%string, tmod) :: ("rx"%string, trec) :: ("f"%string, tfb) :: nil).
Local Notation ctx_a :=
  (("a"%string, ta) :: ("m"%string, tmod) :: ("rx"%string, trec) ::
   ("f"%string, tfb) :: nil).
Local Notation ctx_x :=
  (("x"%string, tB) :: ("a"%string, ta) :: ("m"%string, tmod) ::
   ("rx"%string, trec) :: ("f"%string, tfb) :: nil).

Definition rm_body : @named_expr R Ar R_obj ctx_rx trec :=
  [ \ "m" ::: tmod =>
      \ "a" ::: ta =>
        (let "x" := # "m" @ # "a" in
         if (# "f" @ # "x") then # "x" else # "rx" @ # "m" @ # "a") ].

Definition rm_fun : @named_expr R Ar R_obj ctx_m tmod :=
  [ \ "a" ::: ta =>
      (let "x" := # "m" @ # "a" in
       if (# "f" @ # "x") then # "x" else # "rx" @ # "m" @ # "a") ].

Definition rm_inner : @named_expr R Ar R_obj ctx_a tB :=
  [ let "x" := # "m" @ # "a" in
    if (# "f" @ # "x") then # "x" else # "rx" @ # "m" @ # "a" ].

Definition rm_if : @named_expr R Ar R_obj ctx_x tB :=
  [ if (# "f" @ # "x") then # "x" else # "rx" @ # "m" @ # "a" ].

Definition rm_var_x : @named_expr R Ar R_obj ctx_x tB := [ # "x" ].
Definition rm_var_f4 : @named_expr R Ar R_obj ctx_x tfb := [ # "f" ].
Definition rm_var_a4 : @named_expr R Ar R_obj ctx_x ta := [ # "a" ].
Definition rm_var_m4 : @named_expr R Ar R_obj ctx_x tmod := [ # "m" ].
Definition rm_var_rs4 : @named_expr R Ar R_obj ctx_x trec := [ # "rx" ].
Definition rm_var_a3 : @named_expr R Ar R_obj ctx_a ta := [ # "a" ].
Definition rm_var_m3 : @named_expr R Ar R_obj ctx_a tmod := [ # "m" ].

Lemma ne_reject_decomp :
  @ne_reject R Ar R_obj ta tB = ne_lam "f" (ne_fix "rx" rm_body).
Proof. by []. Qed.

Lemma rm_body_decomp : rm_body = ne_lam "m" rm_fun.
Proof. by []. Qed.

Lemma rm_fun_decomp : rm_fun = ne_lam "a" rm_inner.
Proof. by []. Qed.

Lemma rm_inner_decomp :
  rm_inner = ne_let "x" (ne_app rm_var_m3 rm_var_a3) rm_if.
Proof. by []. Qed.

Lemma rm_if_decomp :
  rm_if =
  ne_if tB (ne_app rm_var_f4 rm_var_x)
        rm_var_x
        (ne_app (ne_app rm_var_rs4 rm_var_m4) rm_var_a4).
Proof. by []. Qed.

(** *** The semantic objects *)

Let Hone : cone_norm (one1 : cone_one_car Ar) <= 1.
Proof. by rewrite one1_norm. Qed.

(** The model's output distribution at the input. *)
Definition reject_model_dist : coalg_obj (tyD_cbv tB) := linhom_fun g a0.

(** The predicate value is a setlike unit-ball point. *)
Lemma rm_f_ball : cone_norm (fpred!) <= 1.
Proof. exact: prom_ball Hf_ball. Qed.

Lemma rm_f_setlike :
  Lfun (coalg_str (tyD_cbv tfb)) (fpred!) = (fpred!)!.
Proof.
rewrite -[tyD_cbv tfb]/(bang_cofree Lfb) bang_cofree_str.
exact: (dig_prom _ Hf_ball).
Qed.

(** The setlike base environment [1 ⊗ fpred!]. *)
Definition rm_env0 : coalg_obj (ctxD_cbv (drop_names ctx_f)) :=
  one1 ⊗p (fpred!).

Lemma rm_env0_ball : cone_norm rm_env0 <= 1.
Proof. by rewrite /rm_env0 tensor_normME one1_norm mul1r rm_f_ball. Qed.

Lemma rm_env0_setlike :
  Lfun (coalg_str (ctxD_cbv (drop_names ctx_f))) rm_env0 = rm_env0!.
Proof.
exact: (coalg_str_tensor_setlike (P:=EM_term) (Q:=tyD_cbv tfb)
          Hone rm_f_ball coalg_str_one1 rm_f_setlike).
Qed.

(** [W₀ := curry ⟦body⟧ (1 ⊗ fpred!) : !Lrec ⊸ !Lrec]. *)
Definition rm_W0 : linhom_car Ar (Bang Ar Lrec) (Bang Ar Lrec) :=
  Lfun (tensor_curry (eD_cbv' rm_body)) rm_env0.

Lemma rm_W0_ball : cone_norm rm_W0 <= 1.
Proof. exact: le_trans (cones_hom_norm_le1 _ _) rm_env0_ball. Qed.

(** The model value [g!] is a setlike unit-ball point. *)
Lemma rm_g_ball : cone_norm (g!) <= 1.
Proof. exact: prom_ball Hg_ball. Qed.

Lemma rm_g_setlike :
  Lfun (coalg_str (tyD_cbv tmod)) (g!) = (g!)!.
Proof.
rewrite -[tyD_cbv tmod]/(bang_cofree Bmod) bang_cofree_str.
exact: (dig_prom _ Hg_ball).
Qed.

(** *** Step 1 — the program value and the application collapses *)

(** [⟦ne_reject⟧(1)] = the promoted [λf]-stage. *)
Definition reject_comb_val : coalg_obj (tyD_cbv (tfun tfb trec)) :=
  Lfun (eD_cbv' (@ne_reject R Ar R_obj ta tB)) one1.

Lemma reject_comb_val_E :
  reject_comb_val =
  (Lfun (tensor_curry (eD_cbv' (ne_fix "rx" rm_body))) one1)!.
Proof.
rewrite /reject_comb_val ne_reject_decomp eD_lam_E.
exact: (adj_psi_at_setlike (tensor_curry (eD_cbv' (ne_fix "rx" rm_body)))
          Hone coalg_str_one1).
Qed.

(** The fixpoint value after applying to the predicate. *)
Definition reject_after_f_val : coalg_obj (tyD_cbv trec) :=
  Lfun (eD_cbv' (ne_fix "rx" rm_body)) rm_env0.

Lemma reject_after_f_val_E :
  reject_after_f_val = (sc_fun (fix_value Lrec) rm_W0)!.
Proof.
rewrite /reject_after_f_val (eD_fix_at_setlike "rx" rm_body
          rm_env0_ball rm_env0_setlike).
by rewrite -/rm_W0.
Qed.

(** Applying [⟦ne_reject⟧(1)] to [fpred!] gives the fixpoint value. *)
Lemma reject_comb_applied_f_E :
  linhom_fun (Lfun (der (Lty tfb trec)) reject_comb_val) (fpred!) =
  reject_after_f_val.
Proof.
rewrite reject_comb_val_E.
rewrite (der_prom _ (le_trans (cones_hom_norm_le1 _ _) Hone)).
by rewrite tensor_curryE.
Qed.

(** [ν] — the denotation of [(reject f m) a] at [f = fpred!],
    [m = g!], [a = a₀] (CBV application of the program value). *)
Definition reject_model_denot : coalg_obj (tyD_cbv tB) :=
  linhom_fun
    (Lfun (der Bmod)
       (linhom_fun (Lfun (der Lrec) reject_after_f_val) (g!)))
    a0.

Lemma reject_model_app_E :
  reject_model_denot =
  linhom_fun
    (Lfun (der Bmod)
       (linhom_fun (sc_fun (fix_value Lrec) rm_W0) (g!)))
    a0.
Proof.
rewrite /reject_model_denot reject_after_f_val_E.
by rewrite (der_prom _ (fix_value_ball rm_W0 rm_W0_ball)).
Qed.

(** *** Step 2 — the denotation is the sup of the per-iterate measures *)

Definition rm_chain (n : nat) : coalg_obj (tyD_cbv tmod) :=
  linhom_fun (fix_chain rm_W0 n) (g!).

Lemma rm_chain_chain n : precone_le (rm_chain n) (rm_chain n.+1).
Proof.
exact: (linhom_le_pointwise (fix_chain_chain rm_W0_ball n) (g!)).
Qed.

Lemma rm_chain_ball n : cone_norm (rm_chain n) <= 1.
Proof.
apply: le_trans
  (linhom_norm_apply_le (fix_chain_ball rm_W0_ball n) (g!)) _.
by rewrite mul1r rm_g_ball.
Qed.

Definition rm_der (n : nat) : Bmod := Lfun (der Bmod) (rm_chain n).

Lemma rm_der_chain n : precone_le (rm_der n) (rm_der n.+1).
Proof. exact: (Lfun_le (der Bmod) (rm_chain_chain n)). Qed.

Lemma rm_der_ball n : cone_norm (rm_der n) <= 1.
Proof. exact: le_trans (cones_hom_norm_le1 _ _) (rm_chain_ball n). Qed.

Definition reject_model_iter (n : nat) : coalg_obj (tyD_cbv tB) :=
  linhom_fun (rm_der n) a0.

Lemma rm_iter_chain n :
  precone_le (reject_model_iter n) (reject_model_iter n.+1).
Proof. exact: (linhom_le_pointwise (rm_der_chain n) a0). Qed.

Lemma rm_iter_ball n : cone_norm (reject_model_iter n) <= 1.
Proof.
apply: le_trans (linhom_norm_apply_le (rm_der_ball n) a0) _.
by rewrite mul1r Ha_ball.
Qed.

Lemma reject_model_sup_E :
  reject_model_denot =
  cone_sup_ball reject_model_iter rm_iter_chain rm_iter_ball.
Proof.
rewrite reject_model_app_E (fix_value_E rm_W0_ball).
rewrite (linhom_fun_sup_ball (fix_chain_chain rm_W0_ball)
  (fix_chain_ball rm_W0_ball) rm_g_ball rm_chain_chain rm_chain_ball).
rewrite (Lfun_sup_ball (der Bmod) rm_chain_chain rm_chain_ball
  rm_der_chain rm_der_ball).
rewrite (linhom_fun_sup_ball rm_der_chain rm_der_ball Ha_ball
  rm_iter_chain rm_iter_ball).
by [].
Qed.

(** *** Step 3 — the Kleene step at the extended setlike environment *)

Lemma rm_chain_prom_ball n : cone_norm ((fix_chain rm_W0 n)!) <= 1.
Proof. exact: prom_ball (fix_chain_ball rm_W0_ball n). Qed.

Lemma rm_chain_prom_setlike n :
  Lfun (coalg_str (tyD_cbv trec))
       ((fix_chain rm_W0 n)!) = ((fix_chain rm_W0 n)!)!.
Proof.
rewrite -[tyD_cbv trec]/(bang_cofree Lrec) bang_cofree_str.
exact: (dig_prom _ (fix_chain_ball rm_W0_ball n)).
Qed.

Definition rm_env1 (n : nat) :
    coalg_obj (ctxD_cbv (drop_names ctx_rx)) :=
  rm_env0 ⊗p (fix_chain rm_W0 n)!.

Definition rm_env2 (n : nat) :
    coalg_obj (ctxD_cbv (drop_names ctx_m)) :=
  rm_env1 n ⊗p (g!).

Definition rm_env3 (n : nat) :
    coalg_obj (ctxD_cbv (drop_names ctx_a)) :=
  rm_env2 n ⊗p a0.

Definition rm_env4 (n : nat) (r : ar_carrier Ar B) :
    coalg_obj (ctxD_cbv (drop_names ctx_x)) :=
  rm_env3 n ⊗p dirac_fmeas r.

Lemma rm_env1_ball n : cone_norm (rm_env1 n) <= 1.
Proof.
by rewrite /rm_env1 tensor_normME mulr_ile1 ?cone_norm_ge0
   ?rm_env0_ball ?rm_chain_prom_ball.
Qed.

Lemma rm_env1_setlike n :
  Lfun (coalg_str (ctxD_cbv (drop_names ctx_rx))) (rm_env1 n) =
  (rm_env1 n)!.
Proof.
exact: (coalg_str_tensor_setlike (P:=ctxD_cbv (drop_names ctx_f))
          (Q:=tyD_cbv trec)
          rm_env0_ball (rm_chain_prom_ball n) rm_env0_setlike
          (rm_chain_prom_setlike n)).
Qed.

Lemma rm_env2_ball n : cone_norm (rm_env2 n) <= 1.
Proof.
rewrite /rm_env2 tensor_normME.
by rewrite mulr_ile1 ?cone_norm_ge0 ?rm_env1_ball ?rm_g_ball.
Qed.

Lemma rm_env2_setlike n :
  Lfun (coalg_str (ctxD_cbv (drop_names ctx_m))) (rm_env2 n) =
  (rm_env2 n)!.
Proof.
exact: (coalg_str_tensor_setlike
          (P:=ctxD_cbv (drop_names ctx_rx)) (Q:=tyD_cbv tmod)
          (rm_env1_ball n) rm_g_ball (rm_env1_setlike n) rm_g_setlike).
Qed.

Lemma rm_env3_ball n : cone_norm (rm_env3 n) <= 1.
Proof.
rewrite /rm_env3 tensor_normME.
by rewrite mulr_ile1 ?cone_norm_ge0 ?rm_env2_ball ?Ha_ball.
Qed.

Lemma rm_env3_setlike n :
  Lfun (coalg_str (ctxD_cbv (drop_names ctx_a))) (rm_env3 n) =
  (rm_env3 n)!.
Proof.
exact: (coalg_str_tensor_setlike
          (P:=ctxD_cbv (drop_names ctx_m)) (Q:=tyD_cbv ta)
          (rm_env2_ball n) Ha_ball (rm_env2_setlike n) Ha_setlike).
Qed.

Lemma rm_env4_ball n r : cone_norm (rm_env4 n r) <= 1.
Proof.
rewrite /rm_env4 tensor_normME.
by rewrite mulr_ile1 ?cone_norm_ge0 ?rm_env3_ball ?dirac_fmeas_norm_le1.
Qed.

Lemma rm_env4_setlike n r :
  Lfun (coalg_str (ctxD_cbv (drop_names ctx_x))) (rm_env4 n r) =
  (rm_env4 n r)!.
Proof.
exact: (coalg_str_tensor_setlike
          (P:=ctxD_cbv (drop_names ctx_a)) (Q:=FMeas_coalgebra B)
          (rm_env3_ball n) (dirac_fmeas_norm_le1 r)
          (rm_env3_setlike n) (Coalg_dirac B r)).
Qed.

Lemma rm_W0_at_prom n :
  linhom_fun rm_W0 ((fix_chain rm_W0 n)!) =
  (Lfun (tensor_curry (eD_cbv' rm_fun)) (rm_env1 n))!.
Proof.
rewrite {1}/rm_W0 tensor_curryE rm_body_decomp eD_lam_E.
exact: (adj_psi_at_setlike (P:=ctxD_cbv (drop_names ctx_rx))
          _ (rm_env1_ball n) (rm_env1_setlike n)).
Qed.

Lemma rm_chain_S n :
  rm_chain n.+1 =
  Lfun (eD_cbv' (rm_fun))
       (rm_env2 n).
Proof.
rewrite /rm_chain fix_chain_S rm_W0_at_prom.
rewrite (der_prom _ (le_trans (cones_hom_norm_le1 _ _) (rm_env1_ball n))).
exact: tensor_curryE.
Qed.

Lemma rm_chain_S_prom n :
  rm_chain n.+1 =
  (Lfun (tensor_curry (eD_cbv' (rm_inner)))
     (rm_env2 n))!.
Proof.
rewrite rm_chain_S rm_fun_decomp eD_lam_E.
exact: (adj_psi_at_setlike (P:=ctxD_cbv (drop_names ctx_m))
          _ (rm_env2_ball n) (rm_env2_setlike n)).
Qed.

Lemma reject_model_iter_S n :
  reject_model_iter n.+1 =
  Lfun (eD_cbv' (rm_inner))
       (rm_env3 n).
Proof.
rewrite /reject_model_iter /rm_der rm_chain_S_prom.
rewrite (der_prom _ (le_trans (cones_hom_norm_le1 _ _) (rm_env2_ball n))).
exact: tensor_curryE.
Qed.

(** *** Step 4 — variable projections and the dispatch at the Dirac
    environment *)

Lemma rm_var_a3_E n :
  Lfun (eD_cbv' rm_var_a3) (rm_env3 n) = a0.
Proof.
apply: (eq_trans (y := Lfun (em_proj2_mor (R:=R)
  (ctxD_cbv (drop_names ctx_m)) (tyD_cbv ta)) (rm_env3 n))).
  by [].
exact: (em_proj2_morE (rm_env2_ball n) (rm_env2_setlike n)).
Qed.

Lemma rm_var_m3_E n :
  Lfun (eD_cbv' rm_var_m3) (rm_env3 n) = (g!).
Proof.
apply: (eq_trans (y := Lfun (icones_comp
  (em_proj2_mor (R:=R) (ctxD_cbv (drop_names ctx_rx)) (tyD_cbv tmod))
  (em_proj1_mor (R:=R) (ctxD_cbv (drop_names ctx_m)) (tyD_cbv ta)))
  (rm_env3 n))).
  by [].
rewrite Lfun_comp.
rewrite (em_proj1_morE (Q:=tyD_cbv ta) Ha_ball Ha_setlike).
exact: (em_proj2_morE (P:=ctxD_cbv (drop_names ctx_rx))
          (rm_env1_ball n) (rm_env1_setlike n)).
Qed.

Lemma rm_model_app_E n :
  Lfun (eD_cbv' (ne_app rm_var_m3 rm_var_a3)) (rm_env3 n) =
  reject_model_dist.
Proof.
rewrite (eD_app_at_setlike R_carrier_eq R_carrier_meas R_to_carrier_meas
           (rm_env3_ball n) (rm_env3_setlike n)).
rewrite rm_var_m3_E rm_var_a3_E.
by rewrite (der_prom _ Hg_ball).
Qed.

Lemma rm_var_x_E n r :
  Lfun (eD_cbv' rm_var_x) (rm_env4 n r) = dirac_fmeas r.
Proof.
apply: (eq_trans (y := Lfun (em_proj2_mor (R:=R)
  (ctxD_cbv (drop_names ctx_a)) (FMeas_coalgebra B)) (rm_env4 n r))).
  by [].
exact: (em_proj2_morE (rm_env3_ball n) (rm_env3_setlike n)).
Qed.

Lemma rm_var_a4_E n r :
  Lfun (eD_cbv' rm_var_a4) (rm_env4 n r) = a0.
Proof.
apply: (eq_trans (y := Lfun (icones_comp
  (em_proj2_mor (R:=R) (ctxD_cbv (drop_names ctx_m)) (tyD_cbv ta))
  (em_proj1_mor (R:=R) (ctxD_cbv (drop_names ctx_a))
     (FMeas_coalgebra B))) (rm_env4 n r))).
  by [].
rewrite Lfun_comp.
rewrite (em_proj1_morE (Q:=FMeas_coalgebra B)
           (dirac_fmeas_norm_le1 r) (Coalg_dirac B r)).
exact: (em_proj2_morE (P:=ctxD_cbv (drop_names ctx_m))
          (rm_env2_ball n) (rm_env2_setlike n)).
Qed.

Lemma rm_var_m4_E n r :
  Lfun (eD_cbv' rm_var_m4) (rm_env4 n r) = (g!).
Proof.
apply: (eq_trans (y := Lfun (icones_comp
  (icones_comp
    (em_proj2_mor (R:=R) (ctxD_cbv (drop_names ctx_rx)) (tyD_cbv tmod))
    (em_proj1_mor (R:=R) (ctxD_cbv (drop_names ctx_m)) (tyD_cbv ta)))
  (em_proj1_mor (R:=R) (ctxD_cbv (drop_names ctx_a))
     (FMeas_coalgebra B))) (rm_env4 n r))).
  by [].
rewrite Lfun_comp Lfun_comp.
rewrite (em_proj1_morE (Q:=FMeas_coalgebra B)
           (dirac_fmeas_norm_le1 r) (Coalg_dirac B r)).
rewrite (em_proj1_morE (Q:=tyD_cbv ta) Ha_ball Ha_setlike).
exact: (em_proj2_morE (P:=ctxD_cbv (drop_names ctx_rx))
          (rm_env1_ball n) (rm_env1_setlike n)).
Qed.

Lemma rm_var_rs4_E n r :
  Lfun (eD_cbv' rm_var_rs4) (rm_env4 n r) = (fix_chain rm_W0 n)!.
Proof.
apply: (eq_trans (y := Lfun (icones_comp
  (icones_comp
    (icones_comp
      (em_proj2_mor (R:=R) (ctxD_cbv (drop_names ctx_f)) (tyD_cbv trec))
      (em_proj1_mor (R:=R) (ctxD_cbv (drop_names ctx_rx))
         (tyD_cbv tmod)))
    (em_proj1_mor (R:=R) (ctxD_cbv (drop_names ctx_m)) (tyD_cbv ta)))
  (em_proj1_mor (R:=R) (ctxD_cbv (drop_names ctx_a))
     (FMeas_coalgebra B))) (rm_env4 n r))).
  by [].
rewrite Lfun_comp Lfun_comp Lfun_comp.
rewrite (em_proj1_morE (Q:=FMeas_coalgebra B)
           (dirac_fmeas_norm_le1 r) (Coalg_dirac B r)).
rewrite (em_proj1_morE (Q:=tyD_cbv ta) Ha_ball Ha_setlike).
rewrite (em_proj1_morE (Q:=tyD_cbv tmod) rm_g_ball rm_g_setlike).
exact: (em_proj2_morE (P:=ctxD_cbv (drop_names ctx_f))
          rm_env0_ball rm_env0_setlike).
Qed.

Lemma rm_var_f4_E n r :
  Lfun (eD_cbv' rm_var_f4) (rm_env4 n r) = (fpred!).
Proof.
apply: (eq_trans (y := Lfun (icones_comp
  (icones_comp
    (icones_comp
      (icones_comp
        (em_proj2_mor (R:=R) EM_term (tyD_cbv tfb))
        (em_proj1_mor (R:=R) (ctxD_cbv (drop_names ctx_f)) (tyD_cbv trec)))
      (em_proj1_mor (R:=R) (ctxD_cbv (drop_names ctx_rx)) (tyD_cbv tmod)))
    (em_proj1_mor (R:=R) (ctxD_cbv (drop_names ctx_m)) (tyD_cbv ta)))
  (em_proj1_mor (R:=R) (ctxD_cbv (drop_names ctx_a))
     (FMeas_coalgebra B))) (rm_env4 n r))).
  by [].
rewrite Lfun_comp Lfun_comp Lfun_comp Lfun_comp.
rewrite (em_proj1_morE (Q:=FMeas_coalgebra B)
           (dirac_fmeas_norm_le1 r) (Coalg_dirac B r)).
rewrite (em_proj1_morE (Q:=tyD_cbv ta) Ha_ball Ha_setlike).
rewrite (em_proj1_morE (Q:=tyD_cbv tmod) rm_g_ball rm_g_setlike).
rewrite (em_proj1_morE (Q:=tyD_cbv trec)
           (rm_chain_prom_ball n) (rm_chain_prom_setlike n)).
exact: (em_proj2_morE (P:=EM_term) Hone coalg_str_one1).
Qed.

(** The scrutinee at [δ_r] is the predicate applied to the produced
    value: [⟦f x⟧ = fpred(δ_r) = s_r] — the acceptance distribution. *)
Lemma rm_scrut_E n r :
  Lfun (eD_cbv' (ne_app rm_var_f4 rm_var_x)) (rm_env4 n r) = sdist r.
Proof.
rewrite (eD_app_at_setlike R_carrier_eq R_carrier_meas R_to_carrier_meas
           (rm_env4_ball n r) (rm_env4_setlike n r)).
rewrite rm_var_f4_E rm_var_x_E.
by rewrite (der_prom _ Hf_ball).
Qed.

Lemma rm_else_E n r :
  Lfun (eD_cbv' (ne_app (ne_app rm_var_rs4 rm_var_m4) rm_var_a4))
       (rm_env4 n r) =
  reject_model_iter n.
Proof.
rewrite (eD_app_at_setlike R_carrier_eq R_carrier_meas R_to_carrier_meas
           (rm_env4_ball n r) (rm_env4_setlike n r)).
rewrite (eD_app_at_setlike R_carrier_eq R_carrier_meas R_to_carrier_meas
           (rm_env4_ball n r) (rm_env4_setlike n r)).
rewrite rm_var_rs4_E rm_var_m4_E rm_var_a4_E.
by rewrite (der_prom _ (fix_chain_ball rm_W0_ball n)).
Qed.

Lemma reject_model_if_at_dirac n r :
  Lfun (eD_cbv' rm_if) (rm_env4 n r) =
  bool_case (sdist r) (dirac_fmeas r) (reject_model_iter n).
Proof.
rewrite rm_if_decomp eD_if_E.
rewrite (if_icones_at
  (eD_cbv' rm_var_x)
  (eD_cbv' (ne_app (ne_app rm_var_rs4 rm_var_m4) rm_var_a4))
  (eD_cbv' (ne_app rm_var_f4 rm_var_x))
  (rm_env4_ball n r) (rm_env4_setlike n r)).
by rewrite rm_scrut_E rm_var_x_E rm_else_E.
Qed.

(** *** Measurability of the accept-probability [t] and reject weight [bc_f]

    [r ↦ s_r] is a measurable path (Dirac path pushed through [fpred]);
    each [bool_cone] coordinate is then measurable. *)

Let rm_s_path :
  is_measurable_path (fun r : ar_carrier Ar B => linhom_fun fpred (dirac_fmeas r)).
Proof.
exact: (linhom_pre_pres_path (linhom_pre_of fpred) B dirac_fmeas
          (dirac_fmeas_is_path B)).
Qed.

Let rm_t_meas :
  measurable_fun [set: ar_carrier Ar B] (fun r => (bc_t (sdist r))%:num).
Proof. apply/measurable_EFinP; exact: (@bool_coord_meas _ _ _ _ rm_s_path true). Qed.

Let rm_bf_meas :
  measurable_fun [set: ar_carrier Ar B] (fun r => (bc_f (sdist r))%:num).
Proof. apply/measurable_EFinP; exact: (@bool_coord_meas _ _ _ _ rm_s_path false). Qed.

(** Totality: [bc_t s_r + bc_f s_r = 1], and hence [bc_t s_r ≤ 1]. *)
Let rm_total r : ((bc_t (sdist r))%:num + (bc_f (sdist r))%:num)%R = 1.
Proof. by move: (Hpred_total r); rewrite /cone_norm/= /bc_norm. Qed.

Let rm_t_le1 r : ((bc_t (sdist r))%:num <= 1)%R.
Proof. by rewrite -(rm_total r) lerDl nngnum_ge0. Qed.

(** *** Step 5 — the mass recurrence *)

Local Open Scope ereal_scope.

Local Notation If :=
  (\int[fmeas_mu reject_model_dist]_(r in [set: ar_carrier Ar B])
     ((bc_t (sdist r))%:num)%:E) (only parsing).
Local Notation IUf U :=
  (\int[fmeas_mu reject_model_dist]_(r in U)
     ((bc_t (sdist r))%:num)%:E) (only parsing).
Local Notation m0 :=
  (fine (fmeas_mu reject_model_dist [set: ar_carrier Ar B])).

(** [ν_M] is a sub-probability: total mass [m₀ ≤ 1]. *)
Lemma rm_dist_ball : (cone_norm reject_model_dist <= 1)%R.
Proof.
apply: le_trans (linhom_norm_apply_le Hg_ball a0) _.
by rewrite mul1r Ha_ball.
Qed.

Lemma rm_m0_le1 : (m0 <= 1)%R.
Proof. exact: rm_dist_ball. Qed.

Lemma rm_If_ge0 : 0 <= If.
Proof. by apply: integral_ge0 => r _; rewrite lee_fin nngnum_ge0. Qed.

Lemma rm_If_le_mass :
  If <= fmeas_mu reject_model_dist [set: ar_carrier Ar B].
Proof.
apply: (le_trans (y := \int[fmeas_mu reject_model_dist]_
                        (r in [set: ar_carrier Ar B]) (cst (1%:E : \bar R)) r)).
  apply: ge0_le_integral.
  - exact: measurableT.
  - by move=> r _; exact: nngnum_ge0.
  - by apply/measurable_EFinP; exact: rm_t_meas.
  - exact: measurable_cst.
  - by move=> r _; rewrite lee_fin rm_t_le1.
by rewrite integral_cst// mul1e.
Qed.

Lemma rm_If_fin : If \is a fin_num.
Proof.
rewrite ge0_fin_numE ?rm_If_ge0//.
apply: le_lt_trans rm_If_le_mass _.
by rewrite ltey_eq fmeas_setT_fin.
Qed.

Lemma rm_fine_If_le_m0 : (fine If <= m0)%R.
Proof.
apply: fine_le; [exact: rm_If_fin | | exact: rm_If_le_mass].
exact: fmeas_setT_fin.
Qed.

Lemma rm_IUf_ge0 U : measurable U -> 0 <= IUf U.
Proof. by move=> mU; apply: integral_ge0 => r _; rewrite lee_fin nngnum_ge0. Qed.

Lemma rm_IUf_le_If U : measurable U -> IUf U <= If.
Proof.
move=> mU; apply: ge0_subset_integral => //.
by apply/measurable_EFinP; exact: rm_t_meas.
Qed.

Lemma rm_IUf_fin U : measurable U -> IUf U \is a fin_num.
Proof.
move=> mU; rewrite ge0_fin_numE ?rm_IUf_ge0//.
apply: le_lt_trans (rm_IUf_le_If mU) _.
apply: le_lt_trans rm_If_le_mass _.
by rewrite ltey_eq fmeas_setT_fin.
Qed.

(** The rejected-AND-terminated weight: [∫ bc_f dν_M = m₀ - ∫ t dν_M]
    — this is where TOTALITY enters ([bc_t + bc_f = 1]). *)
Lemma rm_int_onem :
  \int[fmeas_mu reject_model_dist]_(r in [set: ar_carrier Ar B])
     ((bc_f (sdist r))%:num)%:E = ((m0 - fine If)%R)%:E.
Proof.
have ge0_t : forall x, [set: ar_carrier Ar B] x ->
    (0 <= ((bc_t (sdist x))%:num)%:E).
  by move=> x _; rewrite lee_fin nngnum_ge0.
have ge0_f : forall x, [set: ar_carrier Ar B] x ->
    (0 <= ((bc_f (sdist x))%:num)%:E).
  by move=> x _; rewrite lee_fin nngnum_ge0.
have meas_t : measurable_fun [set: ar_carrier Ar B]
    (fun r => ((bc_t (sdist r))%:num)%:E).
  by apply/measurable_EFinP; exact: rm_t_meas.
have meas_f : measurable_fun [set: ar_carrier Ar B]
    (fun r => ((bc_f (sdist r))%:num)%:E).
  by apply/measurable_EFinP; exact: rm_bf_meas.
have Hsum : If + \int[fmeas_mu reject_model_dist]_
                  (r in [set: ar_carrier Ar B])
                   ((bc_f (sdist r))%:num)%:E =
            fmeas_mu reject_model_dist [set: ar_carrier Ar B].
  rewrite -(ge0_integralD _ measurableT ge0_t meas_t ge0_f meas_f).
  under eq_integral => r _.
    rewrite -EFinD (rm_total r).
    over.
  by rewrite integral_cst// mul1e.
have := congr1 (fun z => z - If) Hsum.
rewrite (addeC If) addeK ?rm_If_fin// => ->.
rewrite -{1}(fineK (fmeas_setT_fin
               (reject_model_dist : fmeas R (ar_carrier Ar B)))).
by rewrite -{1}(fineK rm_If_fin) -EFinB.
Qed.

Lemma rm_case_mass n r U (mU : measurable U) :
  fmeas_mu (bool_case (sdist r)
    (dirac_fmeas r) (reject_model_iter n)) U =
  ((bc_t (sdist r))%:num * \1_U r + (bc_f (sdist r))%:num *
      fine (fmeas_mu (reject_model_iter n) U))%:E.
Proof.
have -> : (bool_case (sdist r)
    (dirac_fmeas r) (reject_model_iter n) : fmeas R (ar_carrier Ar B)) =
  fmeas_add
    (fmeas_scale (bc_t (sdist r)) (dirac_fmeas r))
    (fmeas_scale (bc_f (sdist r)) (reject_model_iter n)).
  by [].
rewrite fmeas_addE 2!fmeas_scaleE (dirac_fmeas_E r mU) diracE/=.
rewrite -(fineK (fmeas_fin (reject_model_iter n) U mU)).
by rewrite -2!EFinM -EFinD indicE.
Qed.

Lemma reject_model_iter_mass n U (mU : measurable U) :
  fmeas_mu (reject_model_iter n.+1) U =
  IUf U + ((m0 - fine If)%R)%:E * fmeas_mu (reject_model_iter n) U.
Proof.
have Hiter : reject_model_iter n.+1 =
    linhom_fun (eD' (ne_let "x"%string (ne_app rm_var_m3 rm_var_a3) rm_if))
               (rm_env3 n).
  rewrite reject_model_iter_S rm_inner_decomp.
  by rewrite /eD icones_to_linhomE.
rewrite Hiter.
rewrite (eD_let_int_obj R_carrier_meas R_to_carrier_meas
           (ne_app rm_var_m3 rm_var_a3) rm_if
           (rm_env3_ball n) (rm_env3_setlike n)).
rewrite (distributions.icone_integral_fmeas_E _ _ mU).
rewrite rm_model_app_E.
set c := fine (fmeas_mu (reject_model_iter n) U).
under eq_integral => r _.
  rewrite reject_model_if_at_dirac (rm_case_mass n r mU)/= EFinD.
  over.
have Hc0 : (0 <= c)%R by rewrite /c fine_ge0// measure_ge0.
have m1 : measurable_fun [set: ar_carrier Ar B]
    (fun r => ((bc_t (sdist r))%:num * \1_U r)%:E).
  apply/measurable_EFinP; apply: measurable_funM => //.
have m2 : measurable_fun [set: ar_carrier Ar B]
    (fun r => (((bc_f (sdist r))%:num) * c)%:E).
  apply/measurable_EFinP; apply: measurable_funM => //.
have ge0_m1 : forall x, [set: ar_carrier Ar B] x ->
    (0 <= ((bc_t (sdist x))%:num * \1_U x)%:E).
  by move=> x _; rewrite lee_fin mulr_ge0// nngnum_ge0.
have ge0_m2 : forall x, [set: ar_carrier Ar B] x ->
    (0 <= (((bc_f (sdist x))%:num) * c)%:E).
  by move=> x _; rewrite lee_fin mulr_ge0// nngnum_ge0.
have Hz : \int[fmeas_mu reject_model_dist]_(r in [set: ar_carrier Ar B])
            (((bc_f (sdist r))%:num)%:E * c%:E) =
          (\int[fmeas_mu reject_model_dist]_(r in [set: ar_carrier Ar B])
            ((bc_f (sdist r))%:num)%:E) * c%:E.
  apply: ge0_integralZr.
  - exact: measurableT.
  - by apply/measurable_EFinP; exact: rm_bf_meas.
  - by move=> x _; rewrite lee_fin nngnum_ge0.
  - by rewrite lee_fin; exact: Hc0.
rewrite (ge0_integralD _ measurableT ge0_m1 m1 ge0_m2 m2).
congr (_ + _).
- rewrite [RHS](integral_mkcond U) epatch_indic.
  apply: eq_integral => r _.
  by rewrite /= EFinM.
- under eq_integral => r _.
    rewrite EFinM.
    over.
  rewrite Hz rm_int_onem.
  by rewrite (fineK (fmeas_fin (reject_model_iter n) U mU)).
Qed.

(** *** Step 6 — the headline theorems *)

Lemma rm_iter_0 : reject_model_iter 0 = precone_zero.
Proof.
rewrite /reject_model_iter /rm_der /rm_chain fix_chain_0 linhom_fun_zero.
have [Z0 _ _] := cones_hom_linear
  (mcones_hom_cones (icones_hom_mcones (der Bmod))).
by rewrite Z0 linhom_fun_zero.
Qed.

Lemma rm_iter_0_mass U : fmeas_mu (reject_model_iter 0) U = 0.
Proof.
have -> : (reject_model_iter 0 : fmeas R (ar_carrier Ar B)) =
          fmeas_zero.
  by rewrite rm_iter_0.
exact: fmeas_zeroE.
Qed.

(** The master identity — division-free, unconditional. *)
Theorem reject_model_master_obj U (mU : measurable U) :
  ((1 - m0
      + fine (\int[fmeas_mu reject_model_dist]_(x in [set: ar_carrier Ar B])
                ((bc_t (sdist x))%:num)%:E))%R)%:E
    * fmeas_mu reject_model_denot U
  = \int[fmeas_mu reject_model_dist]_(x in U) ((bc_t (sdist x))%:num)%:E.
Proof.
have HnormE : (1 - m0 + fine If)%R = (1 - (m0 - fine If))%R.
  by rewrite opprB addrA addrAC.
rewrite HnormE.
pose xs := fun k => fine (fmeas_mu (reject_model_iter k) U).
have Hx0 : xs 0%N = 0%R by rewrite /xs rm_iter_0_mass.
have HxS : forall k,
    xs k.+1 = (fine (IUf U) + (m0 - fine If) * xs k)%R.
  move=> k; rewrite /xs (reject_model_iter_mass k mU).
  rewrite fineD ?rm_IUf_fin//; last first.
    by rewrite fin_numM// (fmeas_fin (reject_model_iter k) U mU).
  by rewrite fineM// (fmeas_fin (reject_model_iter k) U mU).
have Hq0 : (0 <= m0 - fine If)%R by rewrite subr_ge0 rm_fine_If_le_m0.
have Hq1 : (m0 - fine If <= 1)%R.
  apply: le_trans rm_m0_le1.
  by rewrite lerBlDr lerDl fine_ge0// rm_If_ge0.
have := Hq1; rewrite le_eqVlt => /orP[/eqP Hq_eq1 | Hq_lt1].
- have HfIf_ge0 : (0 <= fine If)%R by rewrite fine_ge0// rm_If_ge0.
  have Hm0_eq : (1 + fine If)%R = m0 by rewrite -Hq_eq1 subrK.
  have HfIf0 : fine If = 0%R.
    apply/le_anti/andP; split=> //.
    by rewrite -(lerD2l 1%R) addr0 Hm0_eq rm_m0_le1.
  have HIf0 : If = 0 by rewrite -(fineK rm_If_fin) HfIf0.
  have -> : IUf U = 0.
    apply/eqP; rewrite eq_le rm_IUf_ge0// andbT.
    by rewrite (le_trans (rm_IUf_le_If mU))// -HIf0.
  by rewrite Hq_eq1 subrr mul0e.
- have Hcvg := affine_iter_cvg (fine (IUf U)) (m0 - fine If)
                 Hq0 Hx0 HxS Hq_lt1.
  have HsupE : fmeas_mu reject_model_denot U =
      ((fine (IUf U) / (1 - (m0 - fine If)))%R)%:E.
    rewrite reject_model_sup_E.
    apply: (fmeas_kleene_sup_U_E rm_iter_chain rm_iter_ball mU).
    have HE : (fun k => fmeas_mu (reject_model_iter k) U) =
              (fun k => (xs k)%:E).
      apply/funext => k.
      by rewrite /xs fineK// (fmeas_fin (reject_model_iter k) U mU).
    by rewrite HE.
  rewrite HsupE -EFinM.
  have Hne : (1 - (m0 - fine If))%R != 0%R.
    by rewrite gt_eqF// subr_gt0.
  by rewrite mulrC mulfVK// (fineK (rm_IUf_fin mU)).
Qed.

Theorem reject_model_is_normalised_obj :
  (0 < 1 - m0
     + fine (\int[fmeas_mu reject_model_dist]_(x in [set: ar_carrier Ar B])
               ((bc_t (sdist x))%:num)%:E))%R ->
  forall U, measurable U ->
  fmeas_mu reject_model_denot U =
  ((fine (\int[fmeas_mu reject_model_dist]_(x in U) ((bc_t (sdist x))%:num)%:E)
    / (1 - m0
         + fine (\int[fmeas_mu reject_model_dist]_
                   (x in [set: ar_carrier Ar B])
                   ((bc_t (sdist x))%:num)%:E)))%R)%:E.
Proof.
move=> Hpos U mU.
have HmF : ((1 - m0 + fine If) *
            fine (fmeas_mu reject_model_denot U))%R = fine (IUf U).
  have := congr1 fine (reject_model_master_obj mU).
  by rewrite fineM// (fmeas_fin reject_model_denot U mU).
rewrite -(fineK (fmeas_fin reject_model_denot U mU)); congr (_%:E).
by rewrite -HmF mulrAC divff ?mul1r// gt_eqF.
Qed.

Theorem reject_model_mass_obj :
  (0 < 1 - m0
     + fine (\int[fmeas_mu reject_model_dist]_(x in [set: ar_carrier Ar B])
               ((bc_t (sdist x))%:num)%:E))%R ->
  fmeas_mu reject_model_denot [set: ar_carrier Ar B] =
  ((fine (\int[fmeas_mu reject_model_dist]_(x in [set: ar_carrier Ar B])
            ((bc_t (sdist x))%:num)%:E)
    / (1 - m0
         + fine (\int[fmeas_mu reject_model_dist]_
                   (x in [set: ar_carrier Ar B])
                   ((bc_t (sdist x))%:num)%:E)))%R)%:E.
Proof.
move=> Hpos; exact: (reject_model_is_normalised_obj Hpos measurableT).
Qed.

Theorem reject_model_mass_one_obj :
  m0 = 1%R ->
  0 < \int[fmeas_mu reject_model_dist]_(x in [set: ar_carrier Ar B])
        ((bc_t (sdist x))%:num)%:E ->
  fmeas_mu reject_model_denot [set: ar_carrier Ar B] = 1.
Proof.
move=> Hm01 HIf.
have HfIf : (0 < fine If)%R.
  rewrite fine_gt0// HIf/= (le_lt_trans rm_If_le_mass)//.
  by rewrite ltey_eq fmeas_setT_fin.
have Hpos : (0 < 1 - m0 + fine If)%R by rewrite Hm01 subrr add0r.
rewrite (reject_model_mass_obj Hpos) Hm01 subrr add0r divff// gt_eqF//.
Qed.

Theorem reject_model_zero_obj :
  (forall r : ar_carrier Ar B, (bc_t (sdist r))%:num = 0%R) ->
  reject_model_denot = precone_zero.
Proof.
move=> Hf0.
have HIUf0 : forall U : set (ar_carrier Ar B), IUf U = 0.
  move=> U.
  under eq_integral => r _ do rewrite Hf0.
  exact: integral0.
have Hmass : forall n (U : set (ar_carrier Ar B)),
    measurable U -> fmeas_mu (reject_model_iter n) U = 0.
  elim=> [ | n IH] U mU; first exact: rm_iter_0_mass.
  by rewrite (reject_model_iter_mass n mU) IH// mule0 adde0 HIUf0.
apply: fmeas_eq => U mU.
rewrite reject_model_sup_E.
rewrite (fmeas_kleene_sup_U_E rm_iter_chain rm_iter_ball mU (l := 0)).
  by rewrite -[precone_zero]/(fmeas_zero : fmeas R (ar_carrier Ar B))
       fmeas_zeroE.
have HE : (fun n => fmeas_mu (reject_model_iter n) U) =
          (fun n => (0 : \bar R)).
  by apply/funext => n; rewrite Hmass.
rewrite HE.
exact: cvg_cst.
Qed.

End RejectModel.

(** ** §4 — The condition combinator: soft conditioning of a model *)

Section ConditionModel.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (P : probObj Ar).
Local Notation R_obj := (po_robj P).
Local Notation R_carrier_eq := (po_robj_eq P).
Local Notation R_carrier_meas := (po_robj_meas P).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Variable (ta : ppl_type Ar).
Variable (B : ar_obj Ar).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '!'" := (prom x) (at level 2, format "x '!'").
Local Notation eD_cbv' :=
  (@eD_cbv R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation eD' :=
  (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation cR := (carrier_to_R R_carrier_eq).
Local Notation tR' := (tR R_obj).
Local Notation tB := (tbase B).
Local Notation Lty t1 t2 :=
  (linhom_car Ar (coalg_obj (tyD_cbv t1)) (coalg_obj (tyD_cbv t2))).

Local Notation tfb := (tfun tB tbool).
Local Notation tmod := (tfun ta tB).
Local Notation trec := (tfun tmod tmod).
Local Notation Bmod := (Lty ta tB).
Local Notation Lrec := (Lty tmod tmod).
Local Notation Lfb := (Lty tB tbool).

Variable (fpred : Lfb).
Hypothesis Hf_ball : cone_norm fpred <= 1.

Variable (g : Bmod).
Hypothesis Hg_ball : cone_norm g <= 1.

Variable (a0 : coalg_obj (tyD_cbv ta)).
Hypothesis Ha_ball : cone_norm a0 <= 1.
Hypothesis Ha_setlike : Lfun (coalg_str (tyD_cbv ta)) a0 = a0!.

Local Notation sdist r := (linhom_fun fpred (dirac_fmeas r)).

(** *** Syntactic decomposition of [ne_condition] — all definitional *)

Local Notation cctx_f :=
  (("f"%string, tfb) :: nil).
Local Notation cctx_m :=
  (("m"%string, tmod) :: ("f"%string, tfb) :: nil).
Local Notation cctx_a :=
  (("a"%string, ta) :: ("m"%string, tmod) :: ("f"%string, tfb) :: nil).
Local Notation cctx_x :=
  (("x"%string, tB) :: ("a"%string, ta) :: ("m"%string, tmod) ::
   ("f"%string, tfb) :: nil).
Local Notation cctx_u :=
  (("_"%string, tunit) :: ("x"%string, tB) :: ("a"%string, ta) ::
   ("m"%string, tmod) :: ("f"%string, tfb) :: nil).

Definition cm_var_m : @named_expr R Ar R_obj cctx_a tmod := [ # "m" ].
Definition cm_var_a : @named_expr R Ar R_obj cctx_a ta := [ # "a" ].
Definition cm_var_x : @named_expr R Ar R_obj cctx_x tB := [ # "x" ].
Definition cm_var_f : @named_expr R Ar R_obj cctx_x tfb := [ # "f" ].
Definition cm_ret : @named_expr R Ar R_obj cctx_u tB := [ # "x" ].

(** The clean assert node: [if (f x) then () else fail]. *)
Definition cm_assert : @named_expr R Ar R_obj cctx_x tunit :=
  [ if (# "f" @ # "x") then () else { ne_fail } ].

Definition cm_K : @named_expr R Ar R_obj cctx_x tB :=
  ne_let "_" cm_assert cm_ret.

Definition cc_fun : @named_expr R Ar R_obj cctx_m tmod :=
  [ \ "a" ::: ta =>
      (let "x" := # "m" @ # "a" in
       let "_" := (if (# "f" @ # "x") then () else { ne_fail }) in
       # "x") ].

Definition cc_after_f : @named_expr R Ar R_obj cctx_f trec :=
  [ \ "m" ::: tmod =>
      \ "a" ::: ta =>
        (let "x" := # "m" @ # "a" in
         let "_" := (if (# "f" @ # "x") then () else { ne_fail }) in
         # "x") ].

Definition cc_inner : @named_expr R Ar R_obj cctx_a tB :=
  [ let "x" := # "m" @ # "a" in
    let "_" := (if (# "f" @ # "x") then () else { ne_fail }) in
    # "x" ].

Lemma ne_condition_decomp :
  @ne_condition R Ar R_obj ta tB = ne_lam "f" cc_after_f.
Proof. by []. Qed.

Lemma cc_after_f_decomp : cc_after_f = ne_lam "m" cc_fun.
Proof. by []. Qed.

Lemma cc_fun_decomp : cc_fun = ne_lam "a" cc_inner.
Proof. by []. Qed.

Lemma cc_inner_decomp :
  cc_inner = ne_let "x" (ne_app cm_var_m cm_var_a) cm_K.
Proof. by []. Qed.

(** *** The semantic objects *)

Let Hone : cone_norm (one1 : cone_one_car Ar) <= 1.
Proof. by rewrite one1_norm. Qed.

Lemma cm_f_ball : cone_norm (fpred!) <= 1.
Proof. exact: prom_ball Hf_ball. Qed.

Lemma cm_f_setlike :
  Lfun (coalg_str (tyD_cbv tfb)) (fpred!) = (fpred!)!.
Proof.
rewrite -[tyD_cbv tfb]/(bang_cofree Lfb) bang_cofree_str.
exact: (dig_prom _ Hf_ball).
Qed.

Lemma cm_g_ball : cone_norm (g!) <= 1.
Proof. exact: prom_ball Hg_ball. Qed.

Lemma cm_g_setlike :
  Lfun (coalg_str (tyD_cbv tmod)) (g!) = (g!)!.
Proof.
rewrite -[tyD_cbv tmod]/(bang_cofree Bmod) bang_cofree_str.
exact: (dig_prom _ Hg_ball).
Qed.

(** *** Step 1 — the combinator value and the application collapses *)

Definition cond_env0 : coalg_obj (ctxD_cbv (drop_names cctx_f)) :=
  one1 ⊗p (fpred!).

Lemma cond_env0_ball : cone_norm cond_env0 <= 1.
Proof. by rewrite /cond_env0 tensor_normME one1_norm mul1r cm_f_ball. Qed.

Lemma cond_env0_setlike :
  Lfun (coalg_str (ctxD_cbv (drop_names cctx_f))) cond_env0 = cond_env0!.
Proof.
exact: (coalg_str_tensor_setlike (P:=EM_term) (Q:=tyD_cbv tfb)
          Hone cm_f_ball coalg_str_one1 cm_f_setlike).
Qed.

Definition cond_fun_lin : Lty tmod tmod :=
  Lfun (tensor_curry (eD_cbv' cc_fun)) cond_env0.

Lemma cond_fun_lin_ball : cone_norm cond_fun_lin <= 1.
Proof. exact: le_trans (cones_hom_norm_le1 _ _) cond_env0_ball. Qed.

Definition cond_comb_val : coalg_obj (tyD_cbv (tfun tfb trec)) :=
  Lfun (eD_cbv' (@ne_condition R Ar R_obj ta tB)) one1.

Lemma cond_comb_val_E :
  cond_comb_val = (Lfun (tensor_curry (eD_cbv' cc_after_f)) one1)!.
Proof.
rewrite /cond_comb_val ne_condition_decomp eD_lam_E.
exact: (adj_psi_at_setlike (tensor_curry (eD_cbv' cc_after_f))
          Hone coalg_str_one1).
Qed.

(** The [λm]-stage value after applying to the predicate. *)
Definition cond_after_f_val : coalg_obj (tyD_cbv trec) :=
  Lfun (eD_cbv' cc_after_f) cond_env0.

Lemma cond_after_f_val_E : cond_after_f_val = cond_fun_lin!.
Proof.
rewrite /cond_after_f_val cc_after_f_decomp eD_lam_E.
exact: (adj_psi_at_setlike (P:=ctxD_cbv (drop_names cctx_f))
          _ cond_env0_ball cond_env0_setlike).
Qed.

Lemma cond_comb_applied_f_E :
  linhom_fun (Lfun (der (Lty tfb trec)) cond_comb_val) (fpred!) =
  cond_after_f_val.
Proof.
rewrite cond_comb_val_E.
rewrite (der_prom _ (le_trans (cones_hom_norm_le1 _ _) Hone)).
by rewrite tensor_curryE.
Qed.

(** [ν_cond] — the denotation of [(condition f m) a]. *)
Definition cond_model_denot : coalg_obj (tyD_cbv tB) :=
  linhom_fun
    (Lfun (der Bmod)
       (linhom_fun (Lfun (der Lrec) cond_after_f_val) (g!)))
    a0.

(** *** Step 2 — collapse to the inner body at the extended env *)

Definition cond_env1 : coalg_obj (ctxD_cbv (drop_names cctx_m)) :=
  cond_env0 ⊗p (g!).

Definition cond_env2 : coalg_obj (ctxD_cbv (drop_names cctx_a)) :=
  cond_env1 ⊗p a0.

Definition cond_env3 (r : ar_carrier Ar B) :
    coalg_obj (ctxD_cbv (drop_names cctx_x)) :=
  cond_env2 ⊗p dirac_fmeas r.

Lemma cond_env1_ball : cone_norm cond_env1 <= 1.
Proof.
rewrite /cond_env1 tensor_normME.
by rewrite mulr_ile1 ?cone_norm_ge0 ?cond_env0_ball ?cm_g_ball.
Qed.

Lemma cond_env1_setlike :
  Lfun (coalg_str (ctxD_cbv (drop_names cctx_m))) cond_env1 =
  cond_env1!.
Proof.
exact: (coalg_str_tensor_setlike (P:=ctxD_cbv (drop_names cctx_f))
          (Q:=tyD_cbv tmod)
          cond_env0_ball cm_g_ball cond_env0_setlike cm_g_setlike).
Qed.

Lemma cond_env2_ball : cone_norm cond_env2 <= 1.
Proof.
rewrite /cond_env2 tensor_normME.
by rewrite mulr_ile1 ?cone_norm_ge0 ?cond_env1_ball ?Ha_ball.
Qed.

Lemma cond_env2_setlike :
  Lfun (coalg_str (ctxD_cbv (drop_names cctx_a))) cond_env2 =
  cond_env2!.
Proof.
exact: (coalg_str_tensor_setlike
          (P:=ctxD_cbv (drop_names cctx_m)) (Q:=tyD_cbv ta)
          cond_env1_ball Ha_ball cond_env1_setlike Ha_setlike).
Qed.

Lemma cond_env3_ball r : cone_norm (cond_env3 r) <= 1.
Proof.
rewrite /cond_env3 tensor_normME.
by rewrite mulr_ile1 ?cone_norm_ge0 ?cond_env2_ball ?dirac_fmeas_norm_le1.
Qed.

Lemma cond_env3_setlike r :
  Lfun (coalg_str (ctxD_cbv (drop_names cctx_x))) (cond_env3 r) =
  (cond_env3 r)!.
Proof.
exact: (coalg_str_tensor_setlike
          (P:=ctxD_cbv (drop_names cctx_a)) (Q:=FMeas_coalgebra B)
          cond_env2_ball (dirac_fmeas_norm_le1 r)
          cond_env2_setlike (Coalg_dirac B r)).
Qed.

Lemma cond_fun_at_g :
  linhom_fun cond_fun_lin (g!) =
  (Lfun (tensor_curry (eD_cbv' cc_inner)) cond_env1)!.
Proof.
rewrite /cond_fun_lin tensor_curryE cc_fun_decomp eD_lam_E.
exact: (adj_psi_at_setlike (P:=ctxD_cbv (drop_names cctx_m))
          _ cond_env1_ball cond_env1_setlike).
Qed.

Lemma cond_model_denot_E :
  cond_model_denot =
  Lfun (eD_cbv' cc_inner) cond_env2.
Proof.
rewrite /cond_model_denot cond_after_f_val_E.
rewrite (der_prom _ cond_fun_lin_ball) cond_fun_at_g.
rewrite (der_prom _ (le_trans (cones_hom_norm_le1 _ _) cond_env1_ball)).
exact: tensor_curryE.
Qed.

(** *** Step 3 — variable projections and the model application *)

Lemma cm_var_a_E :
  Lfun (eD_cbv' cm_var_a) cond_env2 = a0.
Proof.
apply: (eq_trans (y := Lfun (em_proj2_mor (R:=R)
  (ctxD_cbv (drop_names cctx_m)) (tyD_cbv ta)) cond_env2)).
  by [].
exact: (em_proj2_morE cond_env1_ball cond_env1_setlike).
Qed.

Lemma cm_var_m_E :
  Lfun (eD_cbv' cm_var_m) cond_env2 = (g!).
Proof.
apply: (eq_trans (y := Lfun (icones_comp
  (em_proj2_mor (R:=R) (ctxD_cbv (drop_names cctx_f)) (tyD_cbv tmod))
  (em_proj1_mor (R:=R) (ctxD_cbv (drop_names cctx_m)) (tyD_cbv ta)))
  cond_env2)).
  by [].
rewrite Lfun_comp.
rewrite (em_proj1_morE (Q:=tyD_cbv ta) Ha_ball Ha_setlike).
exact: (em_proj2_morE (P:=ctxD_cbv (drop_names cctx_f))
          cond_env0_ball cond_env0_setlike).
Qed.

Lemma cond_app_E :
  Lfun (eD_cbv' (ne_app cm_var_m cm_var_a)) cond_env2 =
  reject_model_dist g a0.
Proof.
rewrite (eD_app_at_setlike R_carrier_eq R_carrier_meas R_to_carrier_meas
           cond_env2_ball cond_env2_setlike).
rewrite cm_var_m_E cm_var_a_E.
by rewrite (der_prom _ Hg_ball).
Qed.

(** *** Step 4 — the assert-and-return continuation at [δ_r] *)

Lemma cm_var_x_E r :
  Lfun (eD_cbv' cm_var_x) (cond_env3 r) = dirac_fmeas r.
Proof.
apply: (eq_trans (y := Lfun (em_proj2_mor (R:=R)
  (ctxD_cbv (drop_names cctx_a)) (FMeas_coalgebra B)) (cond_env3 r))).
  by [].
exact: (em_proj2_morE cond_env2_ball cond_env2_setlike).
Qed.

Lemma cm_var_f_E r :
  Lfun (eD_cbv' cm_var_f) (cond_env3 r) = (fpred!).
Proof.
apply: (eq_trans (y := Lfun (icones_comp
  (icones_comp
    (icones_comp
      (em_proj2_mor (R:=R) EM_term (tyD_cbv tfb))
      (em_proj1_mor (R:=R) (ctxD_cbv (drop_names cctx_f)) (tyD_cbv tmod)))
    (em_proj1_mor (R:=R) (ctxD_cbv (drop_names cctx_m)) (tyD_cbv ta)))
  (em_proj1_mor (R:=R) (ctxD_cbv (drop_names cctx_a))
     (FMeas_coalgebra B))) (cond_env3 r))).
  by [].
rewrite Lfun_comp Lfun_comp Lfun_comp.
rewrite (em_proj1_morE (Q:=FMeas_coalgebra B)
           (dirac_fmeas_norm_le1 r) (Coalg_dirac B r)).
rewrite (em_proj1_morE (Q:=tyD_cbv ta) Ha_ball Ha_setlike).
rewrite (em_proj1_morE (Q:=tyD_cbv tmod) cm_g_ball cm_g_setlike).
exact: (em_proj2_morE (P:=EM_term) Hone coalg_str_one1).
Qed.

(** The scrutinee at [δ_r] is the acceptance distribution [s_r]. *)
Lemma cm_scrut_E r :
  Lfun (eD_cbv' (ne_app cm_var_f cm_var_x)) (cond_env3 r) = sdist r.
Proof.
rewrite (eD_app_at_setlike R_carrier_eq R_carrier_meas R_to_carrier_meas
           (cond_env3_ball r) (cond_env3_setlike r)).
rewrite cm_var_f_E cm_var_x_E.
by rewrite (der_prom _ Hf_ball).
Qed.

(** [assert (f x)] at [δ_r] weighs the unit point by [t(r) = bc_t s_r]:
    [bool_case s_r one1 ⟦fail⟧ = (bc_t s_r) · one1]. *)
Lemma cm_assert_E r :
  Lfun (eD_cbv' cm_assert) (cond_env3 r) =
  precone_scale (bc_t (sdist r)) one1.
Proof.
rewrite /cm_assert eD_if_E.
rewrite (if_icones_at
  (eD_cbv' (@ne_tt R Ar R_obj cctx_x))
  (eD_cbv' (@ne_fail R Ar R_obj cctx_x tunit))
  (eD_cbv' (ne_app cm_var_f cm_var_x))
  (cond_env3_ball r) (cond_env3_setlike r)).
rewrite cm_scrut_E.
rewrite (eD_tt_at_setlike (cond_env3_ball r) (cond_env3_setlike r)).
rewrite (ne_fail_zero R_to_carrier_meas (cond_env3_ball r) (cond_env3_setlike r)).
rewrite /bool_case precone_scale_0r precone_addC precone_add0.
by [].
Qed.

Lemma cm_ret_at r (s : cone_one_car Ar) :
  Lfun (eD_cbv' cm_ret) ((cond_env3 r) ⊗p s) =
  precone_scale (c1_val s) (dirac_fmeas r).
Proof.
apply: (eq_trans (y := Lfun (icones_comp
  (em_proj2_mor (R:=R) (ctxD_cbv (drop_names cctx_a))
     (FMeas_coalgebra B))
  (em_proj1_mor (R:=R) (ctxD_cbv (drop_names cctx_x)) EM_term))
  ((cond_env3 r) ⊗p s))).
  by [].
rewrite Lfun_comp.
rewrite (em_proj1_mor_unitE
  (P:=ctxD_cbv (drop_names cctx_x)) (cond_env3 r) s).
rewrite (Lfun_scaleE
  (em_proj2_mor (R:=R) (ctxD_cbv (drop_names cctx_a))
     (FMeas_coalgebra B))
  (c1_val s) (cond_env3 r)).
by rewrite (em_proj2_morE (P:=ctxD_cbv (drop_names cctx_a))
              cond_env2_ball cond_env2_setlike).
Qed.

Lemma cm_K_at_dirac r :
  Lfun (eD_cbv' cm_K) (cond_env3 r) =
  precone_scale (bc_t (sdist r)) (dirac_fmeas r).
Proof.
rewrite /cm_K eD_let_E.
rewrite (Lfun_comp (eD_cbv' cm_ret)
  (em_pair_mor
     (icones_id Ar (coalg_obj (ctxD_cbv (drop_names cctx_x))))
     (eD_cbv' cm_assert))
  (cond_env3 r)).
rewrite /em_pair_mor.
rewrite (Lfun_comp
  (tensor_mor
     (icones_id Ar (coalg_obj (ctxD_cbv (drop_names cctx_x))))
     (eD_cbv' cm_assert))
  (coalg_d (ctxD_cbv (drop_names cctx_x)))
  (cond_env3 r)).
rewrite (coalg_d_setlike (P:=ctxD_cbv (drop_names cctx_x))
  (cond_env3_ball r) (cond_env3_setlike r)).
rewrite (tensor_morE
  (icones_id Ar (coalg_obj (ctxD_cbv (drop_names cctx_x))))
  (eD_cbv' cm_assert)
  (cond_env3 r) (cond_env3 r)).
rewrite icones_idE cm_assert_E cm_ret_at.
congr (precone_scale _ (dirac_fmeas r)).
have -> : c1_val (precone_scale (bc_t (sdist r)) one1) =
          nng_mul (bc_t (sdist r)) 1%:nng by [].
by apply: nngnum_inj; rewrite nng_mulE mulr1.
Qed.

(** *** Step 5 — the conditioning law *)

Local Open Scope ereal_scope.

Theorem condition_model_E_obj (U : set (ar_carrier Ar B))
    (mU : measurable U) :
  fmeas_mu cond_model_denot U =
  \int[fmeas_mu (reject_model_dist g a0)]_(r in U) ((bc_t (sdist r))%:num)%:E.
Proof.
have Hinner : cond_model_denot =
    linhom_fun (eD' (ne_let "x"%string (ne_app cm_var_m cm_var_a) cm_K))
               cond_env2.
  rewrite cond_model_denot_E cc_inner_decomp.
  by rewrite /eD icones_to_linhomE.
rewrite Hinner.
rewrite (eD_let_int_obj R_carrier_meas R_to_carrier_meas
           (ne_app cm_var_m cm_var_a) cm_K
           cond_env2_ball cond_env2_setlike).
rewrite (distributions.icone_integral_fmeas_E _ _ mU).
rewrite cond_app_E.
under eq_integral => r _.
  rewrite cm_K_at_dirac fmeas_scaleE (dirac_fmeas_E r mU) diracE -EFinM /=.
  over.
rewrite [RHS](integral_mkcond U) epatch_indic.
apply: eq_integral => r _.
by rewrite /= EFinM.
Qed.

Theorem condition_model_mass_obj :
  fmeas_mu cond_model_denot [set: ar_carrier Ar B] =
  \int[fmeas_mu (reject_model_dist g a0)]_
     (r in [set: ar_carrier Ar B]) ((bc_t (sdist r))%:num)%:E.
Proof. exact: (condition_model_E_obj measurableT). Qed.

End ConditionModel.

(** ** §5 — Readable restatements over closed surface PROGRAMS

    [⟦ M ⟧] denotes the MEASURE of the closed [tR]-typed program [M].
    The predicate is a program [pred_prog := λx. Fbody] and the model a
    thunked program [model_prog := λ_. Mbody]; both arbitrary.  The
    master identity reads (with [ν_M := ⟦ model_run ⟧], [t(x) := true-mass
    ⟦Fbody[x]⟧]):
    [[
       (1 - ν_M(setT) + ∫ t dν_M) · ⟦ reject_prog ⟧ U = ∫_U t dν_M.
    ]] *)

Section ReadableHeadlines.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (P : probObj Ar).
Local Notation R_obj := (po_robj P).
Local Notation R_carrier_eq := (po_robj_eq P).
Local Notation R_carrier_meas := (po_robj_meas P).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation "x '!'" := (prom x) (at level 2, format "x '!'").
Local Notation eD_cbv' :=
  (@eD_cbv R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation eD' :=
  (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation cR := (carrier_to_R R_carrier_eq).
Local Notation tR' := (tR R_obj).
Local Notation Lty t1 t2 :=
  (linhom_car Ar (coalg_obj (tyD_cbv t1)) (coalg_obj (tyD_cbv t2))).

(** The semantic brackets: the measure of a closed [tR]-typed program. *)
Local Notation "⟦ M ⟧" :=
  (fmeas_mu (linhom_fun (eD' M) one1)) (at level 0, format "⟦ M ⟧").

(** The model body and the predicate body — arbitrary programs. *)
Variable (Mbody : @named_expr R Ar R_obj (("_"%string, tunit) :: nil) tR').
Variable (Fbody : @named_expr R Ar R_obj (("x"%string, tR') :: nil) tbool).

(** The closed programs. *)
Definition model_prog : @named_expr R Ar R_obj nil (tfun tunit tR') :=
  [ \ "_" ::: tunit => {Mbody} ].

Definition pred_prog : @named_expr R Ar R_obj nil (tfun tR' tbool) :=
  [ \ "x" ::: tR' => {Fbody} ].

Definition model_run : @named_expr R Ar R_obj nil tR' :=
  [ {model_prog} @ () ].

Definition reject_prog : @named_expr R Ar R_obj nil tR' :=
  [ {ne_reject tunit tR'} @ {pred_prog} @ {model_prog} @ () ].

Definition condition_prog : @named_expr R Ar R_obj nil tR' :=
  [ {ne_condition tunit tR'} @ {pred_prog} @ {model_prog} @ () ].

Let Hone : cone_norm (one1 : cone_one_car Ar) <= 1.
Proof. by rewrite one1_norm. Qed.

Let HoneG : cone_norm
    (one1 : coalg_obj (ctxD_cbv (drop_names (nil : named_ctx Ar)))) <= 1.
Proof. by rewrite one1_norm. Qed.

(** The underlying linear maps of the two program values. *)
Definition model_lin : Lty tunit tR' :=
  Lfun (tensor_curry (eD_cbv' Mbody)) one1.

Definition pred_lin : Lty tR' tbool :=
  Lfun (tensor_curry (eD_cbv' Fbody)) one1.

Lemma model_lin_ball : cone_norm model_lin <= 1.
Proof. exact: le_trans (cones_hom_norm_le1 _ _) Hone. Qed.

Lemma pred_lin_ball : cone_norm pred_lin <= 1.
Proof. exact: le_trans (cones_hom_norm_le1 _ _) Hone. Qed.

(** The acceptance probability of the program predicate. *)
Local Notation sdist r := (linhom_fun pred_lin (dirac_fmeas r)).

Lemma model_prog_val_E :
  Lfun (eD_cbv' model_prog) one1 = model_lin!.
Proof.
rewrite -[model_prog]/(ne_lam "_"%string Mbody) eD_lam_E.
by rewrite (adj_psi_at_setlike (tensor_curry (eD_cbv' Mbody))
              Hone coalg_str_one1).
Qed.

Lemma pred_prog_val_E :
  Lfun (eD_cbv' pred_prog) one1 = pred_lin!.
Proof.
rewrite -[pred_prog]/(ne_lam "x"%string Fbody) eD_lam_E.
by rewrite (adj_psi_at_setlike (tensor_curry (eD_cbv' Fbody))
              Hone coalg_str_one1).
Qed.

Lemma tt_val_E :
  Lfun (eD_cbv' (@ne_tt R Ar R_obj nil)) one1 = one1.
Proof.
rewrite eD_tt_E.
rewrite -[ch_mor (em_term_mor (ctxD_cbv (drop_names (nil : named_ctx Ar))))]
        /(coalg_e (EM_term : Coalgebra Ar)).
by rewrite coalg_e_term.
Qed.

Lemma model_run_val_E :
  Lfun (eD_cbv' model_run) one1 =
  reject_model_dist (ta := tunit) model_lin one1.
Proof.
rewrite -[model_run]/(ne_app model_prog (@ne_tt R Ar R_obj nil)).
rewrite (eD_app_at_setlike R_carrier_eq R_carrier_meas R_to_carrier_meas
           HoneG coalg_str_one1).
rewrite model_prog_val_E tt_val_E.
by rewrite (der_prom _ model_lin_ball).
Qed.

Lemma reject_prog_val_E :
  Lfun (eD_cbv' reject_prog) one1 =
  reject_model_denot R_to_carrier_meas pred_lin model_lin one1.
Proof.
rewrite -[reject_prog]/(ne_app
  (ne_app (ne_app (@ne_reject R Ar R_obj tunit tR') pred_prog) model_prog)
  (@ne_tt R Ar R_obj nil)).
rewrite (eD_app_at_setlike R_carrier_eq R_carrier_meas R_to_carrier_meas
           HoneG coalg_str_one1).
rewrite (eD_app_at_setlike R_carrier_eq R_carrier_meas R_to_carrier_meas
           HoneG coalg_str_one1).
rewrite (eD_app_at_setlike R_carrier_eq R_carrier_meas R_to_carrier_meas
           HoneG coalg_str_one1).
rewrite pred_prog_val_E model_prog_val_E tt_val_E.
rewrite /reject_model_denot.
by rewrite (reject_comb_applied_f_E R_to_carrier_meas tunit pred_lin).
Qed.

Lemma condition_prog_val_E :
  Lfun (eD_cbv' condition_prog) one1 =
  cond_model_denot R_to_carrier_meas pred_lin model_lin one1.
Proof.
rewrite -[condition_prog]/(ne_app
  (ne_app (ne_app (@ne_condition R Ar R_obj tunit tR') pred_prog) model_prog)
  (@ne_tt R Ar R_obj nil)).
rewrite (eD_app_at_setlike R_carrier_eq R_carrier_meas R_to_carrier_meas
           HoneG coalg_str_one1).
rewrite (eD_app_at_setlike R_carrier_eq R_carrier_meas R_to_carrier_meas
           HoneG coalg_str_one1).
rewrite (eD_app_at_setlike R_carrier_eq R_carrier_meas R_to_carrier_meas
           HoneG coalg_str_one1).
rewrite pred_prog_val_E model_prog_val_E tt_val_E.
rewrite /cond_model_denot.
by rewrite (cond_comb_applied_f_E R_to_carrier_meas tunit pred_lin).
Qed.

(** The linhom-level readings of the bridges. *)
Let model_run_lin_E :
  linhom_fun (eD' model_run) one1 =
  reject_model_dist (ta := tunit) model_lin one1.
Proof. by rewrite /eD icones_to_linhomE model_run_val_E. Qed.

Let reject_prog_lin_E :
  linhom_fun (eD' reject_prog) one1 =
  reject_model_denot R_to_carrier_meas pred_lin model_lin one1.
Proof. by rewrite /eD icones_to_linhomE reject_prog_val_E. Qed.

Let condition_prog_lin_E :
  linhom_fun (eD' condition_prog) one1 =
  cond_model_denot R_to_carrier_meas pred_lin model_lin one1.
Proof. by rewrite /eD icones_to_linhomE condition_prog_val_E. Qed.

(** Seal the interpreter-heavy program terms and their linear maps:
    past the bridge lemmas the theorems only mention them abstractly.
    Keeping them transparent makes [rewrite]/[exact] in the [⟦·⟧]-level
    restatements try to unify [eD' condition_prog] against
    [eD' reject_prog] / [eD' model_run] by unfolding the WHOLE
    interpreter on each (pathologically slow); as opaque constants the
    cross-comparisons fail fast on the head. *)
Local Opaque reject_prog condition_prog model_run model_prog pred_prog
  pred_lin model_lin eD eD_cbv.

Local Open Scope ereal_scope.

(** The predicate's TOTALITY, as a readable hypothesis (both doc
    regimes — a deterministic bool-Dirac and a bernoulli coin — are
    total; a generic program predicate may not be). *)
Variable
  (Hpred_total :
    forall r : ar_carrier Ar R_obj, cone_norm (sdist r) = 1%R).

(** The master identity, in math form. *)
Theorem reject_prog_master U (mU : measurable U) :
  ((1 - fine (⟦ model_run ⟧ [set: ar_carrier Ar R_obj])
      + fine (\int[⟦ model_run ⟧]_(x in [set: ar_carrier Ar R_obj])
                ((bc_t (sdist x))%:num)%:E))%R)%:E
    * ⟦ reject_prog ⟧ U
  = \int[⟦ model_run ⟧]_(x in U) ((bc_t (sdist x))%:num)%:E.
Proof.
rewrite model_run_lin_E reject_prog_lin_E.
exact: (reject_model_master_obj R_to_carrier_meas pred_lin_ball
          Hpred_total model_lin_ball Hone coalg_str_one1 mU).
Qed.

(** The normalised form. *)
Theorem reject_prog_is_normalised :
  (0 < 1 - fine (⟦ model_run ⟧ [set: ar_carrier Ar R_obj])
     + fine (\int[⟦ model_run ⟧]_(x in [set: ar_carrier Ar R_obj])
               ((bc_t (sdist x))%:num)%:E))%R ->
  forall U, measurable U ->
  ⟦ reject_prog ⟧ U =
  ((fine (\int[⟦ model_run ⟧]_(x in U) ((bc_t (sdist x))%:num)%:E)
    / (1 - fine (⟦ model_run ⟧ [set: ar_carrier Ar R_obj])
         + fine (\int[⟦ model_run ⟧]_(x in [set: ar_carrier Ar R_obj])
                   ((bc_t (sdist x))%:num)%:E)))%R)%:E.
Proof.
rewrite model_run_lin_E reject_prog_lin_E => Hpos U mU.
exact: (reject_model_is_normalised_obj R_to_carrier_meas pred_lin_ball
          Hpred_total model_lin_ball Hone coalg_str_one1 Hpos mU).
Qed.

(** Almost-sure termination for probability models. *)
Theorem reject_prog_mass_one :
  ⟦ model_run ⟧ [set: ar_carrier Ar R_obj] = 1 ->
  0 < \int[⟦ model_run ⟧]_(x in [set: ar_carrier Ar R_obj])
        ((bc_t (sdist x))%:num)%:E ->
  ⟦ reject_prog ⟧ [set: ar_carrier Ar R_obj] = 1.
Proof.
rewrite model_run_lin_E reject_prog_lin_E => Hm1 HIf.
apply: (reject_model_mass_one_obj R_to_carrier_meas pred_lin_ball
          Hpred_total model_lin_ball Hone coalg_str_one1 _ HIf).
by rewrite -[1%R]/(fine (1 : \bar R)) Hm1.
Qed.

(** Certain rejection diverges. *)
Theorem reject_prog_zero U :
  (forall r : ar_carrier Ar R_obj, (bc_t (sdist r))%:num = 0%R) ->
  ⟦ reject_prog ⟧ U = 0.
Proof.
rewrite reject_prog_lin_E => Hf0.
rewrite (reject_model_zero_obj R_to_carrier_meas pred_lin_ball
           Hpred_total model_lin_ball Hone coalg_str_one1 Hf0).
by rewrite -[precone_zero]/(fmeas_zero : fmeas R (ar_carrier Ar R_obj))
           fmeas_zeroE.
Qed.

(** The conditioning law, in math form. *)
Theorem condition_E U (mU : measurable U) :
  ⟦ condition_prog ⟧ U = \int[⟦ model_run ⟧]_(x in U) ((bc_t (sdist x))%:num)%:E.
Proof.
rewrite condition_prog_lin_E model_run_lin_E.
exact: (condition_model_E_obj R_to_carrier_meas pred_lin_ball
          model_lin_ball Hone coalg_str_one1 mU).
Qed.

(** The model evidence. *)
Theorem condition_prog_evidence :
  ⟦ condition_prog ⟧ [set: ar_carrier Ar R_obj] =
  \int[⟦ model_run ⟧]_(x in [set: ar_carrier Ar R_obj]) ((bc_t (sdist x))%:num)%:E.
Proof. exact: (condition_E measurableT). Qed.

(** The equivalence — rejection sampling computes the conditioned
    model's normalised distribution. *)
Theorem reject_normalises_condition U (mU : measurable U) :
  ((1 - fine (⟦ model_run ⟧ [set: ar_carrier Ar R_obj])
      + fine (\int[⟦ model_run ⟧]_(x in [set: ar_carrier Ar R_obj])
                ((bc_t (sdist x))%:num)%:E))%R)%:E
    * ⟦ reject_prog ⟧ U
  = ⟦ condition_prog ⟧ U.
(** Split through the shared integral so each subgoal mentions only ONE
    of [reject_prog]/[condition_prog] — they are structurally identical
    but for the buried combinator, so unifying [eD reject_prog] against
    [eD condition_prog] reduces the whole interpreter (pathologically
    slow). *)
Proof.
transitivity (\int[⟦ model_run ⟧]_(x in U) ((bc_t (sdist x))%:num)%:E).
- exact: (reject_prog_master mU).
- by rewrite (condition_E mU).
Qed.

(** The DIVISION form. *)
Theorem reject_prog_computes_condition :
  (0 < 1 - fine (⟦ model_run ⟧ [set: ar_carrier Ar R_obj])
     + fine (\int[⟦ model_run ⟧]_(x in [set: ar_carrier Ar R_obj])
               ((bc_t (sdist x))%:num)%:E))%R ->
  forall U, measurable U ->
  ⟦ reject_prog ⟧ U =
  ((fine (⟦ condition_prog ⟧ U)
    / (1 - fine (⟦ model_run ⟧ [set: ar_carrier Ar R_obj])
         + fine (\int[⟦ model_run ⟧]_(x in [set: ar_carrier Ar R_obj])
                   ((bc_t (sdist x))%:num)%:E)))%R)%:E.
Proof.
move=> Hpos U mU.
transitivity
  (((fine (\int[⟦ model_run ⟧]_(x in U) ((bc_t (sdist x))%:num)%:E)
     / (1 - fine (⟦ model_run ⟧ [set: ar_carrier Ar R_obj])
          + fine (\int[⟦ model_run ⟧]_(x in [set: ar_carrier Ar R_obj])
                    ((bc_t (sdist x))%:num)%:E)))%R)%:E).
- exact: (reject_prog_is_normalised Hpos mU).
- by rewrite (condition_E mU).
Qed.

(** The PROBABILITY-MODEL form. *)
Theorem reject_normalises_condition_prob U (mU : measurable U) :
  ⟦ model_run ⟧ [set: ar_carrier Ar R_obj] = 1 ->
  ⟦ condition_prog ⟧ [set: ar_carrier Ar R_obj] * ⟦ reject_prog ⟧ U
  = ⟦ condition_prog ⟧ U.
Proof.
move=> Hm1.
have HZ : ⟦ condition_prog ⟧ [set: ar_carrier Ar R_obj] =
          ((1 - fine (⟦ model_run ⟧ [set: ar_carrier Ar R_obj])
             + fine (\int[⟦ model_run ⟧]_(x in [set: ar_carrier Ar R_obj])
                       ((bc_t (sdist x))%:num)%:E))%R)%:E.
  rewrite condition_prog_evidence Hm1.
  have HIf_fin :
      (\int[⟦ model_run ⟧]_(x in [set: ar_carrier Ar R_obj])
         ((bc_t (sdist x))%:num)%:E) \is a fin_num.
    rewrite model_run_lin_E.
    exact: (rm_If_fin Hpred_total).
  by rewrite -[in LHS](fineK HIf_fin)/= subrr add0r.
rewrite [X in X * _]HZ.
exact: (reject_normalises_condition mU).
Qed.

End ReadableHeadlines.

(** ** §6 — Instance: the sampler model

    At [ta := tunit] and the lambda-written model [λ_. sample µ] with a
    unit-mass prior, [ν_M = µ] and [m₀ = 1]: the master identity
    specialises to the classical [∫ t dµ · ν(U) = ∫_U t dµ]. *)

Section SamplerInstance.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (P : probObj Ar).
Local Notation R_obj := (po_robj P).
Local Notation R_carrier_eq := (po_robj_eq P).
Local Notation R_carrier_meas := (po_robj_meas P).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Variable (m : pmeas Ar R_obj).
Local Notation mu := (pm_meas m).
Hypothesis Hmu1 : (fmeas_mu mu [set: ar_carrier Ar R_obj] = 1)%E.

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '!'" := (prom x) (at level 2, format "x '!'").
Local Notation eD_cbv' :=
  (@eD_cbv R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation cR := (carrier_to_R R_carrier_eq).
Local Notation tR' := (tR R_obj).
Local Notation Lty t1 t2 :=
  (linhom_car Ar (coalg_obj (tyD_cbv t1)) (coalg_obj (tyD_cbv t2))).
Local Notation Lfb := (Lty tR' tbool).

(** The acceptance predicate: an arbitrary unit-ball TOTAL predicate
    value (a deterministic bool-Dirac or a bernoulli coin). *)
Variable (fpred : Lfb).
Hypothesis Hf_ball : cone_norm fpred <= 1.
Hypothesis Hpred_total :
  forall r : ar_carrier Ar R_obj, cone_norm (linhom_fun fpred (dirac_fmeas r)) = 1.

Local Notation sdist r := (linhom_fun fpred (dirac_fmeas r)).

Let Hone : cone_norm (one1 : cone_one_car Ar) <= 1.
Proof. by rewrite one1_norm. Qed.

(** The sampler model's underlying linear map [g_µ]. *)
Definition sampler_lin : Lty tunit tR' :=
  Lfun (tensor_curry (eD_cbv' (ex_sampler_body m))) one1.

Lemma sampler_lin_ball : cone_norm sampler_lin <= 1.
Proof. exact: le_trans (cones_hom_norm_le1 _ _) Hone. Qed.

Lemma ex_sampler_decomp :
  ex_sampler m = ne_lam "_" (ex_sampler_body m).
Proof. by []. Qed.

Lemma sampler_val_E :
  Lfun (eD_cbv' (ex_sampler m)) one1 = sampler_lin!.
Proof.
rewrite ex_sampler_decomp eD_lam_E.
by rewrite (adj_psi_at_setlike
              (tensor_curry (eD_cbv' (ex_sampler_body m)))
              Hone coalg_str_one1).
Qed.

(** [ν_M = g_µ(1) = µ]. *)
Lemma sampler_out_E : linhom_fun sampler_lin one1 = mu.
Proof.
rewrite /sampler_lin tensor_curryE.
have Henv_ball : cone_norm
    ((one1 : cone_one_car Ar) ⊗p (one1 : cone_one_car Ar)) <= 1.
  by rewrite tensor_normME one1_norm mul1r.
have Henv_setlike :
    Lfun (coalg_str (ctxD_cbv (drop_names (("_"%string, tunit) :: nil))))
      ((one1 : cone_one_car Ar) ⊗p (one1 : cone_one_car Ar)) =
    ((one1 : cone_one_car Ar) ⊗p (one1 : cone_one_car Ar))!.
  exact: (coalg_str_tensor_setlike (P:=EM_term) (Q:=EM_term)
            Hone Hone coalg_str_one1 coalg_str_one1).
rewrite eD_sample_E.
exact: (const_iconesE (Z := ctxD_cbv (drop_names (("_"%string, tunit) :: nil)))
          Henv_ball Henv_setlike).
Qed.

Local Notation inst_denot :=
  (reject_model_denot R_to_carrier_meas fpred sampler_lin one1).

Local Open Scope ereal_scope.

(** The instance's model-output distribution is the prior. *)
Lemma inst_dist_E :
  reject_model_dist (ta := tunit) sampler_lin one1 = mu.
Proof. exact: sampler_out_E. Qed.

(** The sampler master identity: [∫ t dµ · ν(U) = ∫_U t dµ] — the
    combinator applied to the sampler model reproduces the classical
    rejection identity at [m₀ = 1]. *)
Theorem ex_reject_comb_sampler_master U (mU : measurable U) :
  ((\int[fmeas_mu mu]_(r in [set: ar_carrier Ar R_obj]) ((bc_t (sdist r))%:num)%:E) *
   fmeas_mu inst_denot U =
   \int[fmeas_mu mu]_(r in U) ((bc_t (sdist r))%:num)%:E)%E.
Proof.
have Hmaster := reject_model_master_obj R_to_carrier_meas Hf_ball
  Hpred_total sampler_lin_ball Hone coalg_str_one1 mU.
move: Hmaster; rewrite inst_dist_E.
have Hm0 : fine (fmeas_mu mu [set: ar_carrier Ar R_obj]) = 1%R.
  by rewrite Hmu1.
rewrite Hm0 subrr add0r.
have Hfin : (\int[fmeas_mu mu]_(r in [set: ar_carrier Ar R_obj])
              ((bc_t (sdist r))%:num)%:E) \is a fin_num.
  rewrite -inst_dist_E.
  exact: (rm_If_fin Hpred_total).
by rewrite (fineK Hfin).
Qed.

End SamplerInstance.

(** ** §7 — Compatibility: the public real-object anchor names

    Re-derives the public [reject_model_*] / [condition_model_*] names
    at the section variables — the anchors [docs]/[blueprint]
    reference. *)

Section RejectModelCompat.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (P : probObj Ar).
Local Notation R_obj := (po_robj P).
Local Notation R_carrier_eq := (po_robj_eq P).
Local Notation R_carrier_meas := (po_robj_meas P).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Variable (ta : ppl_type Ar).
Variable (B : ar_obj Ar).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation "x '!'" := (prom x) (at level 2, format "x '!'").
Local Notation cR := (carrier_to_R R_carrier_eq).
Local Notation tR' := (tR R_obj).
Local Notation tB := (tbase B).
Local Notation Lty t1 t2 :=
  (linhom_car Ar (coalg_obj (tyD_cbv t1)) (coalg_obj (tyD_cbv t2))).
Local Notation Lfb := (Lty tB tbool).

Variable (fpred : Lfb).
Hypothesis Hf_ball : cone_norm fpred <= 1.
Hypothesis Hpred_total :
  forall r : ar_carrier Ar B, cone_norm (linhom_fun fpred (dirac_fmeas r)) = 1.
Variable (g : Lty ta tB).
Hypothesis Hg_ball : cone_norm g <= 1.
Variable (a0 : coalg_obj (tyD_cbv ta)).
Hypothesis Ha_ball : cone_norm a0 <= 1.
Hypothesis Ha_setlike : Lfun (coalg_str (tyD_cbv ta)) a0 = prom a0.

Local Notation sdist r := (linhom_fun fpred (dirac_fmeas r)).

Local Open Scope ereal_scope.

Theorem reject_model_master U (mU : measurable U) :
  ((1 - fine (fmeas_mu (reject_model_dist g a0) [set: ar_carrier Ar B])
      + fine (\int[fmeas_mu (reject_model_dist g a0)]_
                (x in [set: ar_carrier Ar B]) ((bc_t (sdist x))%:num)%:E))%R)%:E
    * fmeas_mu (reject_model_denot R_to_carrier_meas fpred g a0) U
  = \int[fmeas_mu (reject_model_dist g a0)]_(x in U) ((bc_t (sdist x))%:num)%:E.
Proof.
exact: (reject_model_master_obj R_to_carrier_meas Hf_ball
          Hpred_total Hg_ball Ha_ball Ha_setlike mU).
Qed.

Theorem reject_model_is_normalised :
  (0 < 1 - fine (fmeas_mu (reject_model_dist g a0) [set: ar_carrier Ar B])
     + fine (\int[fmeas_mu (reject_model_dist g a0)]_
               (x in [set: ar_carrier Ar B]) ((bc_t (sdist x))%:num)%:E))%R ->
  forall U, measurable U ->
  fmeas_mu (reject_model_denot R_to_carrier_meas fpred g a0) U =
  ((fine (\int[fmeas_mu (reject_model_dist g a0)]_(x in U) ((bc_t (sdist x))%:num)%:E)
    / (1 - fine (fmeas_mu (reject_model_dist g a0) [set: ar_carrier Ar B])
         + fine (\int[fmeas_mu (reject_model_dist g a0)]_
                   (x in [set: ar_carrier Ar B]) ((bc_t (sdist x))%:num)%:E)))%R)%:E.
Proof.
exact: (reject_model_is_normalised_obj R_to_carrier_meas Hf_ball
          Hpred_total Hg_ball Ha_ball Ha_setlike).
Qed.

Theorem reject_model_mass :
  (0 < 1 - fine (fmeas_mu (reject_model_dist g a0) [set: ar_carrier Ar B])
     + fine (\int[fmeas_mu (reject_model_dist g a0)]_
               (x in [set: ar_carrier Ar B]) ((bc_t (sdist x))%:num)%:E))%R ->
  fmeas_mu (reject_model_denot R_to_carrier_meas fpred g a0)
    [set: ar_carrier Ar B] =
  ((fine (\int[fmeas_mu (reject_model_dist g a0)]_
            (x in [set: ar_carrier Ar B]) ((bc_t (sdist x))%:num)%:E)
    / (1 - fine (fmeas_mu (reject_model_dist g a0) [set: ar_carrier Ar B])
         + fine (\int[fmeas_mu (reject_model_dist g a0)]_
                   (x in [set: ar_carrier Ar B]) ((bc_t (sdist x))%:num)%:E)))%R)%:E.
Proof.
exact: (reject_model_mass_obj R_to_carrier_meas Hf_ball
          Hpred_total Hg_ball Ha_ball Ha_setlike).
Qed.

Theorem reject_model_mass_one :
  fine (fmeas_mu (reject_model_dist g a0) [set: ar_carrier Ar B]) = 1%R ->
  0 < \int[fmeas_mu (reject_model_dist g a0)]_
        (x in [set: ar_carrier Ar B]) ((bc_t (sdist x))%:num)%:E ->
  fmeas_mu (reject_model_denot R_to_carrier_meas fpred g a0)
    [set: ar_carrier Ar B] = 1.
Proof.
exact: (reject_model_mass_one_obj R_to_carrier_meas Hf_ball
          Hpred_total Hg_ball Ha_ball Ha_setlike).
Qed.

Theorem reject_model_zero :
  (forall r : ar_carrier Ar B, (bc_t (sdist r))%:num = 0%R) ->
  reject_model_denot R_to_carrier_meas fpred g a0 = precone_zero.
Proof.
exact: (reject_model_zero_obj R_to_carrier_meas Hf_ball
          Hpred_total Hg_ball Ha_ball Ha_setlike).
Qed.

Theorem condition_model_E (U : set (ar_carrier Ar B))
    (mU : measurable U) :
  fmeas_mu (cond_model_denot R_to_carrier_meas fpred g a0) U =
  \int[fmeas_mu (reject_model_dist g a0)]_(r in U) ((bc_t (sdist r))%:num)%:E.
Proof.
exact: (condition_model_E_obj R_to_carrier_meas Hf_ball
          Hg_ball Ha_ball Ha_setlike mU).
Qed.

Theorem condition_model_mass :
  fmeas_mu (cond_model_denot R_to_carrier_meas fpred g a0)
    [set: ar_carrier Ar B] =
  \int[fmeas_mu (reject_model_dist g a0)]_
     (r in [set: ar_carrier Ar B]) ((bc_t (sdist r))%:num)%:E.
Proof.
exact: (condition_model_mass_obj R_to_carrier_meas Hf_ball
          Hg_ball Ha_ball Ha_setlike).
Qed.

End RejectModelCompat.
