(**md**************************************************************************)
(** * A higher-order probabilistic PPL — single-sort, direct-style, multi-var
       De Bruijn, with Kleisli-exponential semantics in [EM(!)]

    This file ports the canonical mathcomp-qbs higher-order PPL
    ([mathcomp-qbs/theories/ppl_qbs.v] + [showcase/ppl_examples.v]) to the
    integrable-cones model, with the SAME calculus shape as the QBS port:

    - a single inductive [expr Γ τ] indexed by an intrinsically-typed,
      MULTI-VARIABLE De Bruijn context [Γ : ppl_ctx] and a type [τ :
      ppl_type];
    - direct-style application [e_app f x : expr Γ B], NOT fine-grain Moggi:
      the user-facing calculus matches a textbook QBS-style PPL, while the
      interpretation goes through the same EM(!)-Kleisli-exponential chain as
      [theories/programs/cbv.v] (= [Tobj = !̃ ∘ U]);
    - monadic [e_ret] / [e_bind] returning to the probability type [tprob τ];
    - a built-in measurable-space base [tbase X] for [X : ar_obj Ar], a unit
      type, binary products, and the higher-order arrow [tfun A B] = [!̃(U A
      ⊸ U B)] (the Kleisli exponential of the CBV computation monad).

    ** Scope of this commit (C-partial: NO arithmetic yet) **

    The full constructor list is in the [Inductive expr] below, but here is
    what is intentionally NOT in this version:

    - [e_add] : sum of two random variables of type [tprob tR];
    - [e_mul] : product of two random variables of type [tprob tR];
    - [ex_random_linear] : the QBS-style mixture example exercising [e_add]
      / [e_mul].

    These three pieces depend on the lax monoidal bundling of [FMeas]
    ([theories/homs/fmeas_lax.v]'s [icones_hom] wrapping the function-level
    [fmeas_lax_pre]), which is being added by a parallel agent.  A small
    follow-up integration commit will EXTEND the [Inductive expr] with the
    two arithmetic constructors and add the [ex_random_linear] example once
    the bundle lands.  This file is consistent and axiom-free WITHOUT
    [e_add]/[e_mul].

    ** The mathematical framework **

    Identical to [theories/programs/cbv.v]: the value category is the FULL
    Eilenberg–Moore category [EM(!)] of the exponential comonad
    ([em_cartesian.v]); the CBV computation monad is [T = !̃ ∘ U]
    ([Tobj] in [cbv.v]).  The Kleisli exponential for [T] gives the
    higher-order arrow type denotation
    [[
        ⟦tfun A B⟧ := !̃(U A ⊸ U B)
                    = bang_cofree (linhom_car Ar (coalg_obj ⟦A⟧)
                                                 (coalg_obj ⟦B⟧)).
    ]]
    See the header of [cbv.v] for the full discussion of the
    natural-bijection chain [Hom_EM(C×A, T B) ≅ Hom_EM(C, !̃(U A ⊸ U B))]
    realising lambda + application.

    ** Headline example — [ex_random_constant] **

    [[
        ex_random_constant ≜
          e_bind (e_sample µ) (e_ret (e_lam (e_var (hv_succ hv_zero))))
                : expr [] (tprob (tfun tR tR))
    ]]
    in the empty context: draw [c ~ µ : FMeas R], then return the constant
    function [λx.c] (whose body is the OUTER-bound variable, hence
    [hv_succ hv_zero] in the lambda body).  This is the QBS-paper-flagship
    "distribution over a function space" example, recovered here in the
    EM(!) Kleisli-exponential discipline.

    The three names [ex_random_constant], [ex_random_constant_denot] and
    [ex_random_constant_denot_E] are preserved (the README / blueprint /
    AUDITOR.md reference them). *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measure dirac_measure.

Require Import Icones.cones.precone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.cone.
Require Import Icones.cones.cone_cat.
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
Require Import Icones.homs.bilin.
Require Import Icones.homs.tensor.
Require Import Icones.homs.tensor_construct.
Require Import Icones.homs.smcc.
Require Import Icones.homs.exp_adjunction.
Require Import Icones.homs.bang.
Require Import Icones.homs.seely_defs.
Require Import Icones.homs.seely.
Require Import Icones.homs.coalgebra.
Require Import Icones.homs.em_cat.
Require Import Icones.homs.em_seely_comonoid.
Require Import Icones.homs.em_cartesian.
Require Import Icones.homs.cbv_adjunction.
Require Import Icones.programs.cbv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Opaque tensor_mor tensor_assoc tensor_lunit tensor_runit tensor_braid
       ptensor tau Seely2.
Opaque dig der prom bang_fmap d_bang e_bang unit_cofree_str Coalg
       tens_cofree_str m_bang.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** Types — single-sort PPL types, parameterised by [Ar] *)

Section Types.
Variable (R : realType) (Ar : MeasSubcat R).

Inductive ppl_type : Type :=
  | tunit
  | tbase (X : ar_obj Ar)
  | tprod (t1 t2 : ppl_type)
  | tfun  (t1 t2 : ppl_type)
  | tprob (t : ppl_type).

End Types.

Arguments ppl_type {R} Ar.
Arguments tunit {R Ar}.
Arguments tbase {R Ar} X.
Arguments tprod {R Ar} t1 t2.
Arguments tfun {R Ar} t1 t2.
Arguments tprob {R Ar} t.

(** ** Contexts and De Bruijn variable witnesses *)

Section Contexts.
Variable (R : realType) (Ar : MeasSubcat R).

Definition ppl_ctx : Type := list (ppl_type Ar).

(** [has_var G t]: a witness of "[t] is somewhere in [G]".  Intrinsic De
    Bruijn index: [hv_zero] points to the HEAD, [hv_succ] skips it. *)
Inductive has_var : ppl_ctx -> ppl_type Ar -> Type :=
  | hv_zero (G : ppl_ctx) (t : ppl_type Ar) : has_var (t :: G) t
  | hv_succ (G : ppl_ctx) (t s : ppl_type Ar) :
      has_var G t -> has_var (s :: G) t.

End Contexts.

Arguments ppl_ctx {R} Ar.
Arguments has_var {R Ar} G t.
Arguments hv_zero {R Ar G t}.
Arguments hv_succ {R Ar G t s} v.

(** ** Distinguished real-object section — for [e_real] and [e_score]

    The PPL has a distinguished real-valued base type [tR] = [tbase R_obj]
    for a chosen [R_obj : ar_obj Ar] whose carrier IS the realType [R].  The
    propositional cast [R_carrier_eq] is the witness; [e_real]/[e_score] use
    it to translate an [R]-literal to a value in [ar_carrier Ar R_obj].

    (No [e_add]/[e_mul] in this commit — the follow-up integration agent
    appends them.) *)

Section RealObj.
Variable (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.

(** Convert an [R] to an [ar_carrier Ar R_obj] via the propositional cast.
    Used by [e_real]/[e_score]. *)
Definition R_to_carrier (r : R) : ar_carrier Ar R_obj :=
  eq_rect_r (fun T : Type => T) r R_carrier_eq.

Definition tR : ppl_type Ar := tbase R_obj.

End RealObj.

Arguments R_to_carrier {R Ar R_obj} R_carrier_eq r.
Arguments tR {R Ar} R_obj.

(** ** Terms — single intrinsically-typed inductive [expr Γ τ]

    Notice we use DIRECT-style application [e_app : expr G (tfun t1 t2) ->
    expr G t1 -> expr G t2] (not Moggi fine-grain), matching the QBS-paper
    calculus shape; the Moggi monadic structure is uncovered by [eD] via the
    Kleisli-exponential chain.

    The constructors:
    - [e_var] : project a value from the De Bruijn context;
    - [e_tt] : the unit value [()];
    - [e_pair] / [e_fst] / [e_snd] : binary products;
    - [e_lam] : higher-order lambda (body is an [expr] in the extended
      context — IT IS NOT marked as a computation; the Moggi/Kleisli
      structure is in the SEMANTICS, not the syntax);
    - [e_app] : DIRECT application;
    - [e_ret] : monadic return [tprob t];
    - [e_bind] : monadic bind [do x <- m; k];
    - [e_sample] : sample from a fixed measure [µ : FMeas X];
    - [e_real] : real literal [r : R] of type [tR];
    - [e_score] : score by [r : R], returning [tprob tunit].

    *** TODO: NOT IN THIS COMMIT (follow-up agent appends them) ***

    The arithmetic constructors below are NOT YET in the inductive; they
    depend on the [icones_hom] bundling of [FMeas]'s lax monoidal pre-map
    that the parallel [theories/homs/fmeas_lax.v] agent is producing.  The
    follow-up integration agent will append:
    [[
       | e_add  : forall G, expr G (tprob tR) -> expr G (tprob tR) ->
                            expr G (tprob tR)
       | e_mul  : forall G, expr G (tprob tR) -> expr G (tprob tR) ->
                            expr G (tprob tR)
    ]]
    together with the example [ex_random_linear] that exercises them. *)
Section Syntax.
Variable (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.

Local Notation tR' := (tR R_obj).
Local Notation T := (@ppl_type R Ar).

Inductive expr : ppl_ctx Ar -> T -> Type :=
  | e_var   (G : ppl_ctx Ar) (t : T) :
      has_var G t -> expr G t
  | e_tt    (G : ppl_ctx Ar) : expr G tunit
  | e_pair  (G : ppl_ctx Ar) (t1 t2 : T) :
      expr G t1 -> expr G t2 -> expr G (tprod t1 t2)
  | e_fst   (G : ppl_ctx Ar) (t1 t2 : T) :
      expr G (tprod t1 t2) -> expr G t1
  | e_snd   (G : ppl_ctx Ar) (t1 t2 : T) :
      expr G (tprod t1 t2) -> expr G t2
  | e_lam   (G : ppl_ctx Ar) (t1 t2 : T) :
      expr (t1 :: G) t2 -> expr G (tfun t1 t2)
  | e_app   (G : ppl_ctx Ar) (t1 t2 : T) :
      expr G (tfun t1 t2) -> expr G t1 -> expr G t2
  | e_ret   (G : ppl_ctx Ar) (t : T) :
      expr G t -> expr G (tprob t)
  | e_bind  (G : ppl_ctx Ar) (t1 t2 : T) :
      expr G (tprob t1) -> expr (t1 :: G) (tprob t2) ->
      expr G (tprob t2)
  | e_sample (G : ppl_ctx Ar) (X : ar_obj Ar)
             (mu : fmeas R (ar_carrier Ar X)) :
      expr G (tprob (tbase X))
  | e_real  (G : ppl_ctx Ar) (r : R) : expr G tR'
  | e_score (G : ppl_ctx Ar) (r : R) : expr G (tprob tunit).

End Syntax.

Arguments expr {R Ar R_obj} G t.
Arguments e_var {R Ar R_obj G t} v.
Arguments e_tt {R Ar R_obj G}.
Arguments e_pair {R Ar R_obj G t1 t2} M N.
Arguments e_fst {R Ar R_obj G t1 t2} M.
Arguments e_snd {R Ar R_obj G t1 t2} M.
Arguments e_lam {R Ar R_obj G t1 t2} M.
Arguments e_app {R Ar R_obj G t1 t2} F X.
Arguments e_ret {R Ar R_obj G t} M.
Arguments e_bind {R Ar R_obj G t1 t2} M K.
Arguments e_sample {R Ar R_obj G X} mu.
Arguments e_real {R Ar R_obj G} r.
Arguments e_score {R Ar R_obj G} r.
