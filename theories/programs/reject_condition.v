(* theories/programs/reject_condition.v
   Clean [reject]/[condition]/[assert]/[fail] combinators for
   docs/hard_reject_condition.md §2.

   The acceptance test is a PROGRAM predicate [f : tfun tb tbool], applied
   by ORDINARY application [# "f" @ # "x"] — there is NO [ne_test] and NO
   lift node.  Everything is built from [fix], [\], [@], [if], [()], [let]
   (the surface notations of Icones.programs.ppl).  Both the model
   [m : tfun ta tb] and the predicate [f : tfun tb tbool] are program
   arguments, and the return object [tb] (and input object [ta]) are
   Section variables — the combinators are fully generic in [ta -> tb].

   Standalone check AFTER a full `make` (deps must be built):
     rocq c -Q theories Icones \
       -w -notation-overridden -w -projection-no-head-constant \
       -w -redundant-canonical-projection -w -hiding-delimiting-key \
       -w -ambiguous-paths -w -deprecated-since-mathcomp-analysis-1.9.0 \
       -w -deprecated-since-mathcomp-2.5.0 theories/programs/reject_condition.v *)

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

Section RejectConditionSurface.
Variables (R : realType) (Ar : MeasSubcat R).
(* [named_expr] is parameterised by a real object even when the term never
   mentions reals; these terms are polymorphic in [R_obj]. *)
Variable (R_obj : ar_obj Ar).
(* Input and return objects are ARBITRARY [ppl_type]s: the model is a
   program [m : tfun ta tb], the predicate a program [f : tfun tb tbool],
   and [reject f m : tfun ta tb]. *)
Variables (ta tb : ppl_type Ar).

Local Notation nexpr G t := (@named_expr R Ar R_obj G t).

(** [fail] : guarded diverging fixpoint, at ANY result type [t]
    (the CBV lambda-guard is mandatory; [fix "fail". "fail"] would loop at
    definition time — recursion must pass through a value).  Its Kleene
    chain from [⊥] is constant, so it denotes the zero sub-distribution
    (precone_zero). *)
Definition ne_fail {G : named_ctx Ar} {t : ppl_type Ar} : nexpr G t :=
  [ (fix "fail" ::: tfun tunit t in \ "_" ::: tunit => # "fail" @ ()) @ () ].

(** [assert] : tbool -> tunit,  \b. if b then () else fail. *)
Definition ne_assert {G : named_ctx Ar} : nexpr G (tfun tbool tunit) :=
  [ \ "b" ::: tbool => (if # "b" then () else { ne_fail }) ].

(** [reject] : \f. fix rx. \m. \a. let x = m a in
                 if (f x) then x else rx m a.
    The acceptance predicate [f] is a PROGRAM [tfun tb tbool], applied by
    ordinary application [# "f" @ # "x"] — no [ne_test], no lift node.
    Parse pitfall (docs §2): the [fix ... in ...] block (level 80) MUST be
    parenthesised under the [\ "f" =>] binder (body slot at level 60). *)
Definition ne_reject :
    nexpr nil (tfun (tfun tb tbool) (tfun (tfun ta tb) (tfun ta tb))) :=
  [ \ "f" ::: tfun tb tbool =>
      ( fix "rx" ::: tfun (tfun ta tb) (tfun ta tb) in
          \ "m" ::: (tfun ta tb) =>
            \ "a" ::: ta =>
              (let "x" := # "m" @ # "a" in
               if (# "f" @ # "x") then # "x" else # "rx" @ # "m" @ # "a") ) ].

(** [condition] : \f. \m. \a. let x = m a in
                    let _ = (if (f x) then () else fail) in x.
    ([let _ = assert (f x) in x] is [if (f x) then () else fail], since a
    failed assert zeroes the mass whatever value follows.) *)
Definition ne_condition :
    nexpr nil (tfun (tfun tb tbool) (tfun (tfun ta tb) (tfun ta tb))) :=
  [ \ "f" ::: tfun tb tbool =>
      \ "m" ::: (tfun ta tb) =>
        \ "a" ::: ta =>
          (let "x" := # "m" @ # "a" in
           let "_" := (if (# "f" @ # "x") then () else { ne_fail }) in
           # "x") ].

End RejectConditionSurface.

Arguments ne_fail {R Ar R_obj G t}.
Arguments ne_assert {R Ar R_obj G}.
Arguments ne_reject {R Ar R_obj} ta tb.
Arguments ne_condition {R Ar R_obj} ta tb.
