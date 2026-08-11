(**md *** PPL CBV chapter infrastructure — the recursion-unfolding equations

    BEYOND THE PAPER.  This file is NOT part of the Ehrhard-Geoffroy
    2025 formalization (paper §2-§9).  It states the SEMANTIC
    unfolding laws of the [ne_fix] clause of the CBV interpreter
    [eD_cbv] ([theories/programs/ppl_cbv.v]), now that the clause is
    the genuine seeded value-fixpoint composite

      [⟦fix s. body⟧ = fix_comb ∘ ⟦λ s. body⟧]

    ([fix_comb] of [theories/programs/infra/em_fix_value.v]).

    Why a separate file: the pointwise computations live at SETLIKE
    context points ([coalg_str Γ γ = γ!], the §9.7 "γ is a sub-Dirac"
    reading), whose kit ([coalg_str_one1], [coalg_str_tensor_setlike],
    [one1_norm]) is owned by [infra/cbv_anchors.v] — which imports
    [ppl_cbv.v], so the equations cannot live inside [ppl_cbv.v]'s
    [EDUnfold] section (import cycle).  [ppl_cbv.v] keeps only the
    DEFINITIONAL clause pins ([eD_fix_E] / [eD_fix_mr_E] /
    [eD_fix_mr_fun_E] / [eD_fix_mr_prod_E]).

    The equations (all at setlike unit-ball [γ], with
    [F_γ := curry ⟦body⟧ γ : !L ⊸ !L] the body's endo-function at [γ]
    and [L := U⟦t1⟧ ⊸ U⟦t2⟧]):

    - [eD_fix_at_setlike] — the prom-point COMPUTATION law:
      [⟦fix s. body⟧ γ = (fix_value F_γ)!], i.e. the denotation is the
      PROMOTED supremum of the interleaved Kleene chain
      [x_0 = 0, x_{n+1} = der (F_γ (x_n !))] ([fix_prom_E] +
      [fix_value_E] of [em_fix_value.v]).  In particular it is NEVER
      the cone-zero ([fix_prom_neq0]) — contrast the naive zero-seeded
      iteration, provably the zero linhom ([Phi_fun_lfp_eq0]).

    - [eD_fix_unfold] — the recursion equation (the name checked by the
      docs via [Print Assumptions eD_fix_unfold]):

        [( der (F_γ (⟦fix s. body⟧ γ)) )! = ⟦fix s. body⟧ γ]

      — one more body unfolding at the fixpoint value, re-promoted,
      is the fixpoint value ([fix_value_unfold]).

    - [eD_fix_mr_fun_at_setlike] / [eD_fix_mr_fun_unfold] — the same
      two laws for [ne_fix_mr] at a FUNCTION body type (the clause is
      the same composite).

    - [eD_fix_mr_prod_at_setlike] / [eD_fix_mr_prod_at_setlike_neq0] —
      the prom-point computation law and the non-degeneracy witness for
      [ne_fix_mr] at a PRODUCT of free types (the Seely-transported
      clause): the denotation at setlike [γ] is the backward transport
      of [(fix_value (conjugated F_γ))!] along the decomposition iso
      [free_decomp] ([fix_comb_iso_prom_E] of
      [theories/programs/infra/em_fix_mr.v]), and is never the
      cone-zero — the mutual-recursion fixpoint is GENUINE (contrast
      the retired zero-seeded placeholder, [Phi_fun_lfp_eq0]).

    - [eD_fix_unfold_closed] / [eD_fix_at_one1] — the closed-program
      ([Γ = nil], [γ = one1]) corollaries against the public linhom
      interpreter [eD].

    See also: [theories/programs/infra/em_fix_value.v] (the
    combinator, obligations (a)/(b), the degeneracy record),
    [theories/programs/infra/cbv_anchors.v] (the setlike kit). *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals signed constructive_ereal.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import measure dirac_measure.
From mathcomp.analysis Require Import lebesgue_integral_definition.
From mathcomp.analysis Require Import lebesgue_integral_nonneg.

From Stdlib Require Import Strings.String.

Require Import Icones.cones.precone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.cone.
Require Import Icones.cones.cone_cat.
Require Import Icones.icones.bool_cone.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.mcones.path.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.icone.
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
Require Import Icones.programs.infra.em_fix_value.
Require Import Icones.programs.infra.em_fix_mr.
Require Import Icones.programs.ppl_cbv.
Require Import Icones.programs.infra.cbv_anchors.

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

(** ** The generic engine: the [fix_comb ∘ adj_psi] composite at a
       setlike point *)

Section FixUnfoldEngine.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

(** [adj_psi]'s underlying morphism, pinned (definitional). *)
Lemma adj_psi_morE (P : Coalgebra Ar) (B : ICone.type Ar)
    (g : icones_hom Ar (coalg_obj P) B) :
  ch_mor (adj_psi g) = icones_comp (bang_fmap g) (coalg_str P).
Proof. by []. Qed.

(** At a setlike unit-ball point [γ] of [G0], the [ne_fix]-clause
    composite computes to the PROMOTED [fix_value] of the body's
    endo-function [h γ]: the [adj_psi] packaging promotes ([coalg_str]
    setlike + [bang_fmap_prom]), and [fix_comb] computes on promoted
    points by [fix_prom_E]. *)
Lemma fix_comp_at_setlike (G0 : Coalgebra Ar) (L : ICone.type Ar)
    (h : icones_hom Ar (coalg_obj G0)
           (linhom_car Ar (Bang Ar L) (Bang Ar L)))
    (gam : coalg_obj G0) :
  cone_norm gam <= 1 ->
  Lfun (coalg_str G0) gam = prom gam ->
  Lfun (icones_comp (ch_mor (fix_comb L)) (ch_mor (adj_psi (P := G0) h)))
    gam =
  prom (sc_fun (fix_value L) (Lfun h gam)).
Proof.
move=> Hg Hs.
(* Controlled, fully-instantiated rewrites only: an unkeyed
   [rewrite Lfun_comp] (or [adj_psi_morE]) would be captured by
   [ch_mor (fix_comb L)] — which delta-unfolds to an [adj_psi]
   composite — and recurse into the SAFT internals. *)
rewrite (Lfun_comp (ch_mor (fix_comb L)) (ch_mor (adj_psi (P := G0) h)) gam).
rewrite (adj_psi_morE h).
rewrite (Lfun_comp (bang_fmap h) (coalg_str G0) gam).
rewrite Hs (bang_fmap_prom h _ Hg).
have Hh : cone_norm (Lfun h gam) <= 1.
  exact: le_trans (cones_hom_norm_le1 _ _) Hg.
exact: (fix_prom_E Hh).
Qed.

(** The Seely-transported analogue: the [fix_comb_iso ∘ adj_psi]
    composite (the [ne_fix_mr]-at-[tprod] clause shape) at a setlike
    point — the [adj_psi] packaging promotes as above, and the
    transported combinator computes on promoted points by
    [em_fix_mr.v::fix_comb_iso_prom_E]. *)
Lemma fix_iso_comp_at_setlike (G0 : Coalgebra Ar)
    (P : Coalgebra Ar) (Z : ICone.type Ar)
    (iso : coalg_iso P (bang_cofree Z))
    (h : icones_hom Ar (coalg_obj G0)
           (linhom_car Ar (coalg_obj P) (coalg_obj P)))
    (gam : coalg_obj G0) :
  cone_norm gam <= 1 ->
  Lfun (coalg_str G0) gam = prom gam ->
  Lfun (icones_comp (ch_mor (fix_comb_iso iso))
                    (ch_mor (adj_psi (P := G0) h))) gam =
  Lfun (ch_mor (ci_bwd iso))
    (prom (sc_fun (fix_value Z)
       (linhom_map_fun (ch_mor (ci_bwd iso)) (ch_mor (ci_fwd iso))
          (Lfun h gam)))).
Proof.
move=> Hg Hs.
rewrite (Lfun_comp (ch_mor (fix_comb_iso iso))
                   (ch_mor (adj_psi (P := G0) h)) gam).
rewrite (adj_psi_morE h).
rewrite (Lfun_comp (bang_fmap h) (coalg_str G0) gam).
rewrite Hs (bang_fmap_prom h _ Hg).
have Hh : cone_norm (Lfun h gam) <= 1.
  exact: le_trans (cones_hom_norm_le1 _ _) Hg.
exact: (fix_comb_iso_prom_E iso Hh).
Qed.

End FixUnfoldEngine.

Arguments adj_psi_morE {R Ar P B} g.
Arguments fix_comp_at_setlike {R Ar G0 L} h {gam}.
Arguments fix_iso_comp_at_setlike {R Ar G0 P Z} iso h {gam}.

(** ** The unfolding laws of the interpreter's [ne_fix] / [ne_fix_mr]
       clauses *)

Section EDFixUnfold.
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
Local Notation eD_cbv' :=
  (@eD_cbv R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation eD' :=
  (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation Lty t1 t2 :=
  (linhom_car Ar (coalg_obj (tyD_cbv t1)) (coalg_obj (tyD_cbv t2))).

(** *** [ne_fix] *)

(** The prom-point computation law: at a setlike unit-ball context
    point [γ], the fixpoint denotation is the PROMOTED interleaved
    Kleene supremum [fix_value F_γ], where
    [F_γ = curry ⟦body⟧ γ : !L ⊸ !L]. *)
Lemma eD_fix_at_setlike (G : named_ctx Ar) (s : string)
    (t1 t2 : ppl_type Ar)
    (body : @named_expr R Ar R_obj ((s, tfun t1 t2) :: G) (tfun t1 t2))
    (gam : coalg_obj (ctxD_cbv (drop_names G))) :
  cone_norm gam <= 1 ->
  Lfun (coalg_str (ctxD_cbv (drop_names G))) gam = prom gam ->
  Lfun (eD_cbv' (ne_fix s body)) gam =
  prom (sc_fun (fix_value (Lty t1 t2))
         (Lfun (tensor_curry (eD_cbv' body)) gam)).
Proof.
move=> Hg Hs.
rewrite eD_fix_E.
exact: (fix_comp_at_setlike (tensor_curry (eD_cbv' body)) Hg Hs).
Qed.

(** The recursion equation: one more body unfolding at the fixpoint
    value, re-promoted, is the fixpoint value —
    [( der (F_γ (⟦fix s.body⟧ γ)) )! = ⟦fix s.body⟧ γ]. *)
Lemma eD_fix_unfold (G : named_ctx Ar) (s : string)
    (t1 t2 : ppl_type Ar)
    (body : @named_expr R Ar R_obj ((s, tfun t1 t2) :: G) (tfun t1 t2))
    (gam : coalg_obj (ctxD_cbv (drop_names G))) :
  cone_norm gam <= 1 ->
  Lfun (coalg_str (ctxD_cbv (drop_names G))) gam = prom gam ->
  prom (Lfun (der (Lty t1 t2))
         (linhom_fun (Lfun (tensor_curry (eD_cbv' body)) gam)
            (Lfun (eD_cbv' (ne_fix s body)) gam))) =
  Lfun (eD_cbv' (ne_fix s body)) gam.
Proof.
move=> Hg Hs.
rewrite (eD_fix_at_setlike body Hg Hs).
have HF : cone_norm (Lfun (tensor_curry (eD_cbv' body)) gam) <= 1.
  exact: le_trans (cones_hom_norm_le1 _ _) Hg.
by rewrite (fix_value_unfold HF).
Qed.

(** Non-degeneracy at every setlike unit-ball point: the fixpoint
    denotation is a promoted point, never the cone-zero — contrast
    [Phi_fun_lfp_eq0]. *)
Lemma eD_fix_at_setlike_neq0 (G : named_ctx Ar) (s : string)
    (t1 t2 : ppl_type Ar)
    (body : @named_expr R Ar R_obj ((s, tfun t1 t2) :: G) (tfun t1 t2))
    (gam : coalg_obj (ctxD_cbv (drop_names G))) :
  cone_norm gam <= 1 ->
  Lfun (coalg_str (ctxD_cbv (drop_names G))) gam = prom gam ->
  Lfun (eD_cbv' (ne_fix s body)) gam <> precone_zero.
Proof.
move=> Hg Hs.
rewrite (eD_fix_at_setlike body Hg Hs).
apply: prom_neq0.
apply: fix_value_ball.
exact: le_trans (cones_hom_norm_le1 _ _) Hg.
Qed.

(** *** [ne_fix_mr] at a function body type — the same two laws *)

Lemma eD_fix_mr_fun_at_setlike (G : named_ctx Ar) (s : string)
    (t1 t2 : ppl_type Ar) (Hfree : is_free_coalg_type (tfun t1 t2))
    (body : @named_expr R Ar R_obj ((s, tfun t1 t2) :: G) (tfun t1 t2))
    (gam : coalg_obj (ctxD_cbv (drop_names G))) :
  cone_norm gam <= 1 ->
  Lfun (coalg_str (ctxD_cbv (drop_names G))) gam = prom gam ->
  Lfun (eD_cbv' (ne_fix_mr s (tfun t1 t2) Hfree body)) gam =
  prom (sc_fun (fix_value (Lty t1 t2))
         (Lfun (tensor_curry (eD_cbv' body)) gam)).
Proof.
move=> Hg Hs.
rewrite eD_fix_mr_fun_E.
exact: (fix_comp_at_setlike (tensor_curry (eD_cbv' body)) Hg Hs).
Qed.

Lemma eD_fix_mr_fun_unfold (G : named_ctx Ar) (s : string)
    (t1 t2 : ppl_type Ar) (Hfree : is_free_coalg_type (tfun t1 t2))
    (body : @named_expr R Ar R_obj ((s, tfun t1 t2) :: G) (tfun t1 t2))
    (gam : coalg_obj (ctxD_cbv (drop_names G))) :
  cone_norm gam <= 1 ->
  Lfun (coalg_str (ctxD_cbv (drop_names G))) gam = prom gam ->
  prom (Lfun (der (Lty t1 t2))
         (linhom_fun (Lfun (tensor_curry (eD_cbv' body)) gam)
            (Lfun (eD_cbv' (ne_fix_mr s (tfun t1 t2) Hfree body)) gam))) =
  Lfun (eD_cbv' (ne_fix_mr s (tfun t1 t2) Hfree body)) gam.
Proof.
move=> Hg Hs.
rewrite (eD_fix_mr_fun_at_setlike Hfree body Hg Hs).
have HF : cone_norm (Lfun (tensor_curry (eD_cbv' body)) gam) <= 1.
  exact: le_trans (cones_hom_norm_le1 _ _) Hg.
by rewrite (fix_value_unfold HF).
Qed.

(** *** [ne_fix_mr] at a product body type — the transported laws

    With the Seely-transported combinator the same prom-point
    computation goes through at [tprod]: the denotation at a setlike
    context point is the BACKWARD-transported promoted [fix_value] of
    the conjugated body, and in particular it is never the cone-zero
    (the iso is injective) — the non-degeneracy witness that the
    mutual-recursion fixpoint is genuine (contrast the retired
    zero-seeded placeholder, [Phi_fun_lfp_eq0]). *)

Lemma eD_fix_mr_prod_at_setlike (G : named_ctx Ar) (s : string)
    (t1 t2 : ppl_type Ar) (Hfree : is_free_coalg_type (tprod t1 t2))
    (body : @named_expr R Ar R_obj
              ((s, tprod t1 t2) :: G) (tprod t1 t2))
    (gam : coalg_obj (ctxD_cbv (drop_names G))) :
  cone_norm gam <= 1 ->
  Lfun (coalg_str (ctxD_cbv (drop_names G))) gam = prom gam ->
  Lfun (eD_cbv' (ne_fix_mr s (tprod t1 t2) Hfree body)) gam =
  Lfun (ch_mor (ci_bwd (free_decomp (tprod t1 t2) Hfree)))
    (prom (sc_fun (fix_value (free_base (tprod t1 t2)))
       (linhom_map_fun
          (ch_mor (ci_bwd (free_decomp (tprod t1 t2) Hfree)))
          (ch_mor (ci_fwd (free_decomp (tprod t1 t2) Hfree)))
          (Lfun (tensor_curry (eD_cbv' body)) gam)))).
Proof.
move=> Hg Hs.
rewrite eD_fix_mr_prod_E.
exact: (fix_iso_comp_at_setlike (free_decomp (tprod t1 t2) Hfree)
          (tensor_curry (eD_cbv' body)) Hg Hs).
Qed.

(** Non-degeneracy at every setlike unit-ball point: the transported
    fixpoint denotation is the backward image of a promoted point under
    a coalgebra ISO, hence never the cone-zero. *)
Lemma eD_fix_mr_prod_at_setlike_neq0 (G : named_ctx Ar) (s : string)
    (t1 t2 : ppl_type Ar) (Hfree : is_free_coalg_type (tprod t1 t2))
    (body : @named_expr R Ar R_obj
              ((s, tprod t1 t2) :: G) (tprod t1 t2))
    (gam : coalg_obj (ctxD_cbv (drop_names G))) :
  cone_norm gam <= 1 ->
  Lfun (coalg_str (ctxD_cbv (drop_names G))) gam = prom gam ->
  Lfun (eD_cbv' (ne_fix_mr s (tprod t1 t2) Hfree body)) gam <>
  precone_zero.
Proof.
move=> Hg Hs.
rewrite (eD_fix_mr_prod_at_setlike Hfree body Hg Hs).
set iso := free_decomp (tprod t1 t2) Hfree.
set v := sc_fun _ _.
have Hv : cone_norm v <= 1.
  apply: fix_value_ball.
  apply: le_trans (linhom_map_norm_le1 _ _ _) _.
  exact: le_trans (cones_hom_norm_le1 _ _) Hg.
move=> Heq.
have := congr1 (Lfun (ch_mor (ci_fwd iso))) Heq.
rewrite -[Lfun (ch_mor (ci_fwd iso)) (Lfun (ch_mor (ci_bwd iso)) (prom v))]
        /(Lfun (icones_comp (ch_mor (ci_fwd iso)) (ch_mor (ci_bwd iso)))
            (prom v)).
rewrite (ci_bwdK iso).
rewrite -[Lfun (icones_id _ _) (prom v)]/(prom v).
have [Z0 _ _] := cones_hom_linear
  (mcones_hom_cones (icones_hom_mcones (ch_mor (ci_fwd iso)))).
rewrite Z0.
exact: prom_neq0 Hv.
Qed.

(** *** Setlike computation laws for the [let rec] elaboration

    The [let rec f x := M in K] sugar elaborates to
    [ne_let f (ne_fix f (ne_lam x M)) K]: relative to the bare
    application [(fix f. λx. M) N], the binding inserts one [ne_let]
    layer and one head-variable lookup.  The three laws below compute
    both at setlike unit-ball context points, so the headline
    reduction chains absorb the extra layer in three rewrites. *)

(** [ne_let] at a setlike point: the bound value is paired onto the
    environment ([coalg_d] collapses to the pure tensor). *)
Lemma eD_let_at_setlike (G : named_ctx Ar) (x : string)
    (t1 t2 : ppl_type Ar)
    (M : @named_expr R Ar R_obj G t1)
    (K : @named_expr R Ar R_obj ((x, t1) :: G) t2)
    (gam : coalg_obj (ctxD_cbv (drop_names G))) :
  cone_norm gam <= 1 ->
  Lfun (coalg_str (ctxD_cbv (drop_names G))) gam = prom gam ->
  Lfun (eD_cbv' (ne_let x M K)) gam =
  Lfun (eD_cbv' K) (ptensor gam (Lfun (eD_cbv' M) gam)).
Proof.
move=> Hg Hs.
rewrite eD_let_E.
rewrite (Lfun_comp (eD_cbv' K)
  (em_pair_mor (icones_id Ar (coalg_obj (ctxD_cbv (drop_names G))))
               (eD_cbv' M)) gam).
rewrite /em_pair_mor (Lfun_comp
  (tensor_mor (icones_id Ar (coalg_obj (ctxD_cbv (drop_names G))))
              (eD_cbv' M))
  (coalg_d (ctxD_cbv (drop_names G))) gam).
rewrite (coalg_d_setlike Hg Hs) tensor_morE icones_idE.
by [].
Qed.

(** Head-variable lookup at a pure tensor with a setlike discarded
    environment: the projection returns the bound value. *)
Lemma eD_var_head_at_setlike (G : named_ctx Ar) (x : string)
    (t : ppl_type Ar)
    (gam : coalg_obj (ctxD_cbv (drop_names G)))
    (v : coalg_obj (tyD_cbv t)) :
  cone_norm gam <= 1 ->
  Lfun (coalg_str (ctxD_cbv (drop_names G))) gam = prom gam ->
  Lfun (eD_cbv' (ne_var (nv_head x t G))) (ptensor gam v) = v.
Proof.
move=> Hg Hs.
apply: (eq_trans (y := Lfun (em_proj2_mor (R:=R)
  (ctxD_cbv (drop_names G)) (tyD_cbv t)) (ptensor gam v))).
  by [].
exact: (em_proj2_morE Hg Hs).
Qed.

(** The unit value at any setlike unit-ball environment is [one1]. *)
Lemma eD_tt_at_setlike (G : named_ctx Ar)
    (gam : coalg_obj (ctxD_cbv (drop_names G))) :
  cone_norm gam <= 1 ->
  Lfun (coalg_str (ctxD_cbv (drop_names G))) gam = prom gam ->
  Lfun (eD_cbv' (@ne_tt R Ar R_obj G)) gam = one1.
Proof.
move=> Hg Hs.
rewrite eD_tt_E.
apply: (eq_trans (y := Lfun (coalg_e (ctxD_cbv (drop_names G))) gam)).
  by [].
exact: (coalg_e_setlike Hg Hs).
Qed.

(** *** Closed programs — [Γ = nil], [γ = one1], public interpreter *)

(** The unit context point is setlike of norm [1]. *)
Let Hone : cone_norm (one1 : cone_one_car Ar) <= 1.
Proof. by rewrite one1_norm. Qed.

(** Closed prom-point computation against the public linhom [eD]. *)
Lemma eD_fix_at_one1 (s : string) (t1 t2 : ppl_type Ar)
    (body : @named_expr R Ar R_obj
              ((s, tfun t1 t2) :: nil) (tfun t1 t2)) :
  linhom_fun (eD' (ne_fix s body)) one1 =
  prom (sc_fun (fix_value (Lty t1 t2))
         (Lfun (tensor_curry (eD_cbv' body)) one1)).
Proof.
rewrite /eD icones_to_linhomE.
exact: (eD_fix_at_setlike body Hone coalg_str_one1).
Qed.

(** Closed recursion equation against the public linhom [eD]. *)
Lemma eD_fix_unfold_closed (s : string) (t1 t2 : ppl_type Ar)
    (body : @named_expr R Ar R_obj
              ((s, tfun t1 t2) :: nil) (tfun t1 t2)) :
  prom (Lfun (der (Lty t1 t2))
         (linhom_fun (Lfun (tensor_curry (eD_cbv' body)) one1)
            (linhom_fun (eD' (ne_fix s body)) one1))) =
  linhom_fun (eD' (ne_fix s body)) one1.
Proof.
rewrite /eD !icones_to_linhomE.
exact: (eD_fix_unfold body Hone coalg_str_one1).
Qed.

End EDFixUnfold.

Arguments eD_fix_at_setlike
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G} s
  {t1 t2} body {gam}.
Arguments eD_fix_unfold
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G} s
  {t1 t2} body {gam}.
Arguments eD_fix_at_setlike_neq0
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G} s
  {t1 t2} body {gam}.
Arguments eD_fix_mr_fun_at_setlike
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G} s
  {t1 t2} Hfree body {gam}.
Arguments eD_fix_mr_fun_unfold
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G} s
  {t1 t2} Hfree body {gam}.
Arguments eD_fix_mr_prod_at_setlike
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G} s
  {t1 t2} Hfree body {gam}.
Arguments eD_fix_mr_prod_at_setlike_neq0
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G} s
  {t1 t2} Hfree body {gam}.
Arguments eD_let_at_setlike
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G} x
  {t1 t2} M K {gam}.
Arguments eD_var_head_at_setlike
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G} x
  {t} {gam} v.
Arguments eD_tt_at_setlike
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G} {gam}.
Arguments eD_fix_at_one1
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} s
  {t1 t2} body.
Arguments eD_fix_unfold_closed
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} s
  {t1 t2} body.
