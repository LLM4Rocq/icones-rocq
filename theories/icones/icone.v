(** * Integrable cones — Paper §4 (Def 4.3) — HB mixin and structure

    An *integrable* measurable cone is a measurable cone [B] such
    that, for every [Ar]-object [X], every measurable path
    [β : ar_carrier X -> B] and every finite measure [µ] on
    [ar_carrier X], there exists an integral of [β] over [µ] (in
    the sense of [path_integral_eq] from [pettis.v], paper Def 4.1).
    The uniqueness clause of Def 4.1 then turns this into the
    paper's [I^B_X : Path(X, B) × FMeas(X) → B] function.

    Paper reference: §4, p. 1:23–1:24, Definition 4.3.

    Coverage in this file:

    - [isICone R Ar B] — the HB mixin layered over [MCone R Ar B]
      asserting the existence-of-integral axiom.
    - [ICone R Ar] — the HB structure of integrable cones
      [{ B of isICone R Ar B & MCone R Ar B }]. Alias
      [iconeType Ar].
    - [icone_integral] — the actual integral value, packaged as a
      function of the (measurable) path and the measure. Paper's
      [I^B_X(β, µ)] for [B] integrable.
    - [icone_integralP] / [icone_integral_eqP] — specification and
      uniqueness, lifted from [pettis.v].

    Design notes.

    - The mixin asks only for *existence* of an integral. Its
      uniqueness is automatic (paper Def 4.1) via the (Mssep)
      axiom of the underlying [MCone] structure.

    - The mixin's existence quantifier mentions
      [is_measurable_path] as a precondition, matching the paper:
      [β ∈ Path(X, B)] is what makes the Pettis-style equation
      well-defined ([m ∘ β] is then a bounded measurable function).
      We make this precondition *explicit* even though no proof in
      this file consumes it: the witness theorems for [FMeas] and
      [Path] (M3 wave 2/3) will need it on hand.

    - This file *does not* prove that any specific cone is
      integrable. Instances for [FMeas(X)] (paper Thm 4.5),
      [Path(X, B)] (paper Thm 4.12), and the trivial [⊥] cone are
      deferred to subsequent M3 waves.
*)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import measurable_structure measurable_function.

Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.icones.pettis.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** The [isICone] HB mixin — Paper Def 4.3

    Layered over [MCone R Ar B]: every measurable path over every
    finite measure admits an integral. Concretely the field
    [icone_exists] states existence; uniqueness is handed back by
    [path_integral_eq_unique] from [pettis.v]. *)

HB.mixin Record isICone (R : realType) (Ar : MeasSubcat R) B
  of MCone R Ar B := {
  (** Paper Def 4.3: for every [Ar]-object [X], every measurable
      path [β : X → B] and every finite measure [µ] on [X], there
      is an integral [x : B] satisfying [path_integral_eq] of
      Def 4.1. *)
  icone_exists :
    forall (X : ar_obj Ar)
           (β : ar_carrier Ar X -> B),
      is_measurable_path β ->
      forall µ : fmeas R (ar_carrier Ar X),
        is_path_integrable β µ;
}.

HB.structure Definition ICone (R : realType) (Ar : MeasSubcat R) :=
  { B of isICone R Ar B & MCone R Ar B }.

(** Short alias for the structure type, mirroring [mconeType Ar]. *)
Notation iconeType Ar := (ICone.type Ar) (only parsing).

(** ** The integration operator — Paper Def 4.3 ([I^B_X])

    For an integrable cone [B], every triple [(X, β, µ)] (with [β]
    a measurable path) determines a unique integral. We package it
    as a Rocq function [icone_integral β Hβ µ : B] which agrees
    with the paper's [∫ β(r) µ(dr)] (or [I^B_X(β, µ)]). *)

Section ICOneIntegral.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (B : ICone.type Ar) (X : ar_obj Ar).
Variables (β : ar_carrier Ar X -> B) (Hβ : is_measurable_path β).
Variable µ : fmeas R (ar_carrier Ar X).

(** Paper Def 4.3: the value [I^B_X(β, µ)], obtained from
    [icone_exists] via [path_integral]. *)
Definition icone_integral : B :=
  path_integral (icone_exists X β Hβ µ).

(** Paper Def 4.1 / 4.3: the specification — [icone_integral]
    satisfies [path_integral_eq]. *)
Lemma icone_integralP : path_integral_eq β µ icone_integral.
Proof. exact: path_integralP. Qed.

(** Paper Def 4.1 / 4.3: any candidate satisfying the defining
    equation coincides with [icone_integral] (uniqueness). *)
Lemma icone_integral_eqP (x : B) :
  path_integral_eq β µ x -> x = icone_integral.
Proof. exact: path_integral_eqP. Qed.

End ICOneIntegral.

Arguments icone_integral {R Ar B X} β Hβ µ.
Arguments icone_integralP {R Ar B X} β Hβ µ.
Arguments icone_integral_eqP {R Ar B X} β Hβ µ.
