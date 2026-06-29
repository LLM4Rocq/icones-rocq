(* theories/programs/hard_reject.v
   First increment for docs/hard_reject_condition.md (hard/boolean rejection).
   Surface terms ONLY: no proofs, no edits to existing files, no new AST node.
   Predicates are program-level (Option B): a [tfun tb tbool] argument applied
   with plain [@].  Standalone check AFTER a full `make` (deps must be built):
     rocq c -Q theories Icones \
       -w -notation-overridden -w -projection-no-head-constant \
       -w -redundant-canonical-projection -w -hiding-delimiting-key \
       -w -ambiguous-paths -w -deprecated-since-mathcomp-analysis-1.9.0 \
       -w -deprecated-since-mathcomp-2.5.0 theories/programs/hard_reject.v *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals constructive_ereal.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import ereal.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import measure dirac_measure.
From mathcomp.analysis Require Import lebesgue_integral_definition numfun.
From mathcomp.analysis Require Import probability.
From Stdlib Require Import Strings.String.

Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.cone_cat.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.mcones.path.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_integral.
Require Import Icones.icones.icone_cat.
Require Import Icones.homs.linhom.
Require Import Icones.homs.bilin.
Require Import Icones.homs.tensor_hom_iso.
Require Import Icones.homs.exp_adjunction.
Require Import Icones.homs.bang.
Require Import Icones.homs.fmeas_lax.
Require Import Icones.homs.coalgebra.
Require Import Icones.homs.em_cat.
Require Import Icones.homs.em_seely_comonoid.
Require Import Icones.homs.em_cartesian.
Require Import Icones.programs.ppl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section HardRejectSurface.
Variables (R : realType) (Ar : MeasSubcat R).
(* [named_expr] is parameterised by a real object even when the term never
   mentions reals; these boolean terms are polymorphic in [R_obj]. *)
Variable (R_obj : ar_obj Ar).
Variable (ta : ppl_type Ar).
(* The model's return space is a base object [B]; the test predicate is a
   DETERMINISTIC meta-level measurable boolean [f : carrier B → bool]
   (NOT a program-level [tfun (tbase B) tbool] coin / predicate, and NOT
   a Bernoulli at a [{0,1}] density).  This is the clean [ne_test]
   surface (cf. docs/hard_reject_condition.md §4). *)
Variable (B : ar_obj Ar).
Variable (f : ar_carrier Ar B -> bool).
Hypothesis Hf : measurable_fun [set: ar_carrier Ar B] f.

Local Notation nexpr G t := (@named_expr R Ar R_obj G t).

(** [fail] : guarded diverging fixpoint, at ANY result type [t]
    (the CBV lambda-guard is mandatory; cf. ex_reject_comb's fix body).
    Denotes the zero sub-distribution (precone_zero). *)
Definition ne_fail {G : named_ctx Ar} {t : ppl_type Ar} : nexpr G t :=
  [ (fix "fail" ::: tfun tunit t in \ "_" ::: tunit => # "fail" @ ()) @ () ].

(** [assert] : tbool -> tunit,  \b. if b then () else fail. *)
Definition ne_assert : nexpr nil (tfun tbool tunit) :=
  [ \ "b" ::: tbool => (if # "b" then () else { ne_fail }) ].

(** [reject] : fix rx. \m. \a. let x = m a in
                 if Test{f} x then x else rx m a.
    The acceptance predicate [f] is now a DETERMINISTIC meta-level test
    applied via [ne_test] (surface [Test { f , Hf }]), replacing the
    program-level [#"f" @ #"x"] application. *)
Definition ne_reject :
    nexpr nil (tfun (tfun ta (tbase B)) (tfun ta (tbase B))) :=
  [ (fix "rx" ::: tfun (tfun ta (tbase B)) (tfun ta (tbase B)) in
      \ "m" ::: (tfun ta (tbase B)) =>
        \ "a" ::: ta =>
          (let "x" := # "m" @ # "a" in
           if Test { f , Hf } # "x" then # "x" else # "rx" @ # "m" @ # "a")) ].

(** [condition] : \m. \a. let x = m a in
                    let _ = (if Test{f} x then () else fail) in x. *)
Definition ne_condition :
    nexpr nil (tfun (tfun ta (tbase B)) (tfun ta (tbase B))) :=
  [ \ "m" ::: (tfun ta (tbase B)) =>
      \ "a" ::: ta =>
        (let "x" := # "m" @ # "a" in
         let "_" := (if Test { f , Hf } # "x" then () else { ne_fail }) in
         # "x") ].

End HardRejectSurface.

Arguments ne_fail {R Ar R_obj G t}.
Arguments ne_assert {R Ar R_obj}.
Arguments ne_reject {R Ar R_obj} ta {B} f Hf.
Arguments ne_condition {R Ar R_obj} ta {B} f Hf.
