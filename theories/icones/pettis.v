(** * Pettis-style integral of a measurable path — Paper §4 (Def 4.1)

    Given a measurable cone [B], an [Ar]-object [X], a function
    [β : ar_carrier X -> B] and a finite measure [µ] on [ar_carrier X],
    we describe what it *means* for an element [x : B] to be the
    integral of [β] over [µ]: for every arity-0 test
    [m ∈ mcone_M (ar_zero Ar)] on [B],

      [test_fun m s x = ∫_{r ∈ X} m s (β r) dµ]   (paper's Def 4.1).

    By the singleton property of [ar_zero], the dependence on [s] is
    vacuous; the universal form is kept for convenience.

    Paper reference: §4, p. 1:23, Definition 4.1 ("integral of [β]
    over [µ]").

    Coverage in this file:

    - [path_integral_eq] — Prop-level specification of "[x] is *an*
      integral of [β] over [µ]". Paper Def 4.1.
    - [path_integral_eq_unique] — Paper Def 4.1's uniqueness clause:
      an integral, if it exists, is unique (by (Mssep) on [B]).
    - [path_integral] — the integral *value* given an existence
      witness; built via [cid].
    - [path_integralP] — the specification lemma:
      [path_integral_eq B X β µ (path_integral B X β µ hex)].
    - [path_integral_eq_unique_R] — uniqueness of the integral value
      against any candidate satisfying [path_integral_eq].

    Design notes.

    - The integrand fed to [\int[mu]_(r in setT) _] is the
      [\bar R]-valued function [(test_fun m s (β r))%:E]. Each
      [test_fun m s (β r) : R] is bounded by [cone_norm (β r)]
      via [test_norm_le], so the integrand is finite-valued.
      We take the [fine] of the integral to land back in [R].

    - We do *not* prove here that any cone admits integrals — that's
      the content of [isICone] (in [icone.v]) and the witness
      theorems for [FMeas(X)], [Path(X, B)] (paper Thms 4.5 / 4.12,
      proved in [theories/icones/examples_icone.v]).

    - We use mathcomp-analysis's generic Lebesgue integral
      [integral mu D f] (notation [\int[mu]_(r in D) f]); we feed it
      [fmeas_mu µ : {measure set X -> \bar R}] as the measure
      argument (mathcomp-analysis only needs the measure-projection,
      not the [{finite_measure ...}] bundle).
*)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.reals Require Import reals constructive_ereal.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import ereal.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measure.
From mathcomp.analysis Require Import lebesgue_integral_definition.

Require Import Icones.prelude.nonneg_extra.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** The defining predicate of a Pettis integral — Paper Def 4.1 *)

Section PathIntegralEq.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (B : MCone.type Ar) (X : ar_obj Ar).
Variables (β : ar_carrier Ar X -> B) (µ : fmeas R (ar_carrier Ar X)).

(** Paper Def 4.1: [x : B] is an integral of [β] over [µ] iff for
    every test [m] at arity 0 picked up by [mcone_M] and every
    "point" [s] of the singleton carrier [ar_carrier (ar_zero Ar)],

      [test_fun m s x
         = fine (\int[µ]_(r in [set: X]) (test_fun m s (β r))%:E)].

    Since [ar_zero] is a singleton, the universal quantifier over
    [s] is essentially vacuous; we keep it to mirror the paper's
    notation without committing to a chosen base point. *)
Definition path_integral_eq (x : B) : Prop :=
  forall m : test_of Ar (ar_zero Ar) B,
    mcone_M (ar_zero Ar) m ->
    forall s : ar_carrier Ar (ar_zero Ar),
      test_fun m s x =
        fine (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X])
                 (test_fun m s (β r))%:E).

End PathIntegralEq.

Arguments path_integral_eq {R Ar B X} β µ x.

(** ** Uniqueness — Paper Def 4.1 (last sentence)

    "[B]y (Mssep) if such an integral [x] exists, it is unique". *)

Section PathIntegralUnique.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (B : MCone.type Ar) (X : ar_obj Ar).
Variables (β : ar_carrier Ar X -> B) (µ : fmeas R (ar_carrier Ar X)).

(** Paper Def 4.1: uniqueness of the integral, immediate from
    (Mssep) on [B] — two integrals satisfy the same equation for
    every [m ∈ mcone_M (ar_zero Ar)] evaluated at [ar_zero_pt],
    hence are separated to be equal. *)
Lemma path_integral_eq_unique (x1 x2 : B) :
  path_integral_eq β µ x1 -> path_integral_eq β µ x2 -> x1 = x2.
Proof.
move=> H1 H2; apply: mcone_M_sep => m mM.
by rewrite (H1 m mM (ar_zero_pt Ar)) (H2 m mM (ar_zero_pt Ar)).
Qed.

End PathIntegralUnique.

Arguments path_integral_eq_unique {R Ar B X β µ x1 x2}.

(** ** The integral value — Paper Def 4.1 (notational packaging)

    Once we know that *some* [x : B] witnesses [path_integral_eq],
    we extract it via [cid]. The notation [path_integral β µ hex]
    plays the role of the paper's [∫ β(r) µ(dr)]. *)

Section PathIntegralVal.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (B : MCone.type Ar) (X : ar_obj Ar).
Variables (β : ar_carrier Ar X -> B) (µ : fmeas R (ar_carrier Ar X)).

(** Paper Def 4.1: the integral value, conditional on an existence
    witness. Implemented via [cid] (classical indefinite
    description) — no [choiceType] structure on [B] is required. *)
Definition path_integral (hex : exists x : B, path_integral_eq β µ x) : B :=
  proj1_sig (cid hex).

(** Paper Def 4.1: the specification — [path_integral β µ hex]
    satisfies the defining equation. *)
Lemma path_integralP (hex : exists x : B, path_integral_eq β µ x) :
  path_integral_eq β µ (path_integral hex).
Proof. by rewrite /path_integral; case: (cid hex). Qed.

(** Paper Def 4.1: any candidate satisfying the defining equation
    coincides with [path_integral]. *)
Lemma path_integral_eqP
  (hex : exists x : B, path_integral_eq β µ x) (x : B) :
  path_integral_eq β µ x -> x = path_integral hex.
Proof.
move=> Hx; apply: path_integral_eq_unique Hx _.
exact: path_integralP.
Qed.

End PathIntegralVal.

Arguments path_integral {R Ar B X β µ}.
Arguments path_integralP {R Ar B X β µ}.
Arguments path_integral_eqP {R Ar B X β µ}.

(** ** Existence as a property of [(β, µ)]

    For convenience, the existence-of-an-integral predicate is
    abbreviated as [is_path_integrable]. The notion of an
    *integrable cone* (paper Def 4.3) — where every measurable path
    over every finite measure has an integral — is packaged in
    [icone.v] as the HB mixin [isICone]. *)

Section IsPathIntegrable.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (B : MCone.type Ar) (X : ar_obj Ar).

(** Paper §4 (text around Def 4.1): a pair [(β, µ)] is integrable
    when it admits an integral in [B]. Paper Def 4.3 is the
    universal closure of this predicate over all [X], [β], [µ]. *)
Definition is_path_integrable
  (β : ar_carrier Ar X -> B) (µ : fmeas R (ar_carrier Ar X)) : Prop :=
  exists x : B, path_integral_eq β µ x.

End IsPathIntegrable.

Arguments is_path_integrable {R Ar B X} β µ.

(** ** Downstream witnesses — Paper Thms 4.5 / 4.12

    The two integrability witnesses for the running examples live in
    [theories/icones/examples_icone.v], where the corresponding
    measurable cones are already in scope:

    - Thm 4.5: [FMeas(X)] is an integrable cone (paper §4, p. 1:24).
      Concretely, for [Y ∈ Ar], [κ ∈ Path(Y, FMeas(X))] and
      [ν ∈ FMeas(Y)], the assignment
      [µ(U) = ∫_{s ∈ Y} κ(s)(U) dν(s)] yields a finite measure on
      [X] which is *the* integral of [κ] over [ν] in [FMeas(X)].

    - Thm 4.12: [Path(X, B)] is integrable when [B] is. The
      pointwise integral is the integral in the path cone.

    Stating these here would require importing [fmeas]'s and
    [path]'s [MCone] instances; the statements live downstream
    where those instances are in scope. *)
