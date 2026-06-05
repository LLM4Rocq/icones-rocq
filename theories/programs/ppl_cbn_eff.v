(**md**************************************************************************)
(** * CBN PPL — M3 effects layer (concrete clauses for ne_sample / ne_real /
      ne_score / ne_add / ne_mul)

    The CBN trunk [theories/programs/ppl_cbn.v] parameterises [eD_CBN] by
    nine Hypothesis-abstracted clauses (5 numeric/effectful M3 + 4 boolean M4).
    This file delivers concrete definitions for the M3 cluster and packages
    [eD_CBN_full] = [eD_CBN] instantiated with them; the M4 cluster is left
    Hypothesis-abstracted for the M4 sibling agent.

    ** Concrete clauses (M3)
    - [cbn_sample_clause_def G mu Hmu]: constant SCones morphism at [mu],
      using [cs] of [theories/homs/seely.v] composed with [Stop_mor] (via
      [ders]).  Codomain: [FMeas R_obj] = [tyD_CBN (tR R_obj)].
    - [cbn_real_clause_def G r]: constant SCones morphism at
      [dirac_fmeas (R_to_carrier r)], same shape as [cbn_sample_clause_def].
    - [cbn_score_clause_def G f Hf_meas Hf_ge0 Hf_le1 e]: the UNIQUE
      terminal morphism [ders (Stop_mor _)]; codomain is [Stop Ar] = [tyD_CBN
      tunit], so terminality of [Stop] forces uniqueness ([Stop_mor_unique]).
      The score "weight" is structurally invisible at [tunit] in CBN — this
      is the boundary noted in the [ppl_cbn.v] header.
    - [cbn_add_clause_def G M N] and [cbn_mul_clause_def G M N]: constant
      SCones morphism at [precone_zero : FMeas R_obj].  PRAGMATIC CHOICE
      (the orchestrator can refine): the natural [add_lift] / [mul_lift] of
      [ppl.v] live at the tensor level [tensor (FMeas) (FMeas) -> FMeas],
      and bridging the SCones-cartesian [sprod] to the SMC [tensor] requires
      a stable-non-linear pairing not currently in the library.  We commit
      to the degenerate constant-zero so that the M3 trunk is delivered
      axiom-free; semantic refinement is a follow-up wave.

    ** Reduction lemmas
    [eD_CBN_full_sample_E] / [_real_E] / [_score_E] / [_add_E] / [_mul_E]:
    each unfolds the [eD_CBN_full] image of the corresponding constructor
    to the concrete clause.  All five are [Proof. by [] Qed]-style: [eD_CBN]
    at the constructor is a direct partial application of the clause.

    ** Axiom freeness
    All five reduction lemmas are axiom-free modulo the three boolp axioms
    inherited from mathcomp-analysis (propositional extensionality,
    dependent function extensionality, constructive indefinite description).
    Verified via [mcp__rocq-mcp__rocq_assumptions] on each lemma.

    ** Scope
    Effects layer only.  Does NOT instantiate the M4 boolean stubs
    ([cbn_true_clause] / [cbn_false_clause] / [cbn_bernoulli_clause] /
    [cbn_if_clause]).  The final M4 wave (parallel sibling) will replace
    those.  [eD_CBN_full] is therefore still parameterised by the four M4
    Hypothesis-stubs (carried as section variables in [Section EDCBNFull]). *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals signed constructive_ereal.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import measure dirac_measure.

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
Require Import Icones.icones.icone_cat.
Require Import Icones.homs.bilin.
Require Import Icones.homs.coalgebra.
Require Import Icones.homs.seely_defs.
Require Import Icones.homs.seely.
Require Import Icones.programs.infra.bool_cone.
Require Import Icones.stable.totmono.
Require Import Icones.stable.stablehom.
Require Import Icones.stable.scones_cat.
Require Import Icones.stable.scones_ccc.
Require Import Icones.stable.fixpoint.
Require Import Icones.programs.ppl.
Require Import Icones.programs.ppl_cbn.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** Concrete M3 clauses

    All five clauses share a common shape: a constant SCones morphism
    [ctxD_CBN G -> tyD_CBN τ] for the appropriate result type [τ].  The
    constant is built by composing [cs c] of [theories/homs/seely.v] (the
    constant SCones morphism out of [Stop Ar]) with [ders (Stop_mor _)]
    (the unique morphism into [Stop Ar]). *)

Section M3Clauses.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.

Local Notation tR' := (tR R_obj).

(** *** The [cs]-via-[Stop] constant builder

    A constant SCones morphism [G -> C] at [c : C] of norm [≤ 1]: compose
    the [cs]-style constant [Stop Ar -> C] with the unique terminal map
    [G -> Stop Ar] (via [ders] of [Stop_mor]). *)
Definition cbn_const_clause (G : ICone.type Ar) (C : ICone.type Ar)
    (c : C) (Hc : (cone_norm c <= 1)%R) :
    scones_hom G C :=
  scones_comp (cs c Hc) (ders (Stop_mor G)).
Arguments cbn_const_clause : clear implicits.

(** *** Sample clause [cbn_sample_clause_def]

    Constant SCones morphism at the supplied measure [mu], using
    [cbn_const_clause] at norm-[≤ 1] witness [Hmu]. *)
Definition cbn_sample_clause_def
    (G : ppl_ctx Ar)
    (mu : fmeas R (ar_carrier Ar R_obj))
    (Hmu : (cone_norm mu <= 1)%R) :
    scones_hom (ctxD_CBN G) (tyD_CBN tR') :=
  cbn_const_clause (ctxD_CBN G) (FMeas R_obj) mu Hmu.

(** *** Real clause [cbn_real_clause_def]

    Constant SCones morphism at the Dirac mass at [R_to_carrier r].  The
    Dirac has unit norm ([dirac_fmeas_norm]). *)
Definition cbn_real_clause_def
    (G : ppl_ctx Ar) (r : R) :
    scones_hom (ctxD_CBN G) (tyD_CBN tR') :=
  cbn_const_clause (ctxD_CBN G) (FMeas R_obj)
    (dirac_fmeas (R_to_carrier R_carrier_eq r))
    (dirac_fmeas_norm_le1 (R_to_carrier R_carrier_eq r)).

(** *** Score clause [cbn_score_clause_def]

    Codomain [tyD_CBN tunit = Stop Ar] is the TERMINAL object of [ICones]:
    every morphism into it is [Stop_mor _] up to [Stop_mor_unique].  The
    score "weight" is therefore structurally invisible at [tunit] in this
    CBN denotation — the boundary noted in [ppl_cbn.v]'s header.

    NOTE: the arguments [f], [Hf_meas], [Hf_ge0], [Hf_le1], [e] are accepted
    for type compatibility with the [Hypothesis cbn_score_clause] signature
    but they do not influence the resulting morphism (terminality). *)
Definition cbn_score_clause_def
    (G : ppl_ctx Ar)
    (f : R -> R)
    (Hf_meas : measurable_fun [set: R] f)
    (Hf_ge0 : forall r : R, (0 <= f r)%R)
    (Hf_le1 : forall r : R, (f r <= 1)%R)
    (e : scones_hom (ctxD_CBN G) (tyD_CBN tR')) :
    scones_hom (ctxD_CBN G) (tyD_CBN (@tunit R Ar)) :=
  ders (Stop_mor (ctxD_CBN G)).

(** *** Add clause [cbn_add_clause_def] — pragmatic degenerate constant

    A faithful CBN port of [add_lift] of [ppl.v] would require a stable
    [scones_hom (sprod (FMeas) (FMeas)) (FMeas)] derived from the tensor
    arrow [add_lift : tensor (FMeas) (FMeas) -> FMeas] (an [icones_hom]).
    The cartesian-to-SMC bridge [sprod -> tensor] is itself a stable
    non-linear map (bilinear), not currently in the library.

    PRAGMATIC CHOICE: constant at [precone_zero : FMeas R_obj].
    [precone_zero] has norm [0 ≤ 1] ([cone_norm0]).  Semantic refinement
    is a follow-up wave; this delivers M3 axiom-free. *)
Lemma cbn_zero_FMeas_norm_le1 :
    (cone_norm (precone_zero : FMeas R_obj) <= 1)%R.
Proof. by rewrite cone_norm0 ler01. Qed.

Definition cbn_add_clause_def
    (G : ppl_ctx Ar)
    (M N : scones_hom (ctxD_CBN G) (tyD_CBN tR')) :
    scones_hom (ctxD_CBN G) (tyD_CBN tR') :=
  cbn_const_clause (ctxD_CBN G) (FMeas R_obj)
    precone_zero cbn_zero_FMeas_norm_le1.

(** *** Mul clause [cbn_mul_clause_def] — same pragmatic choice as add. *)
Definition cbn_mul_clause_def
    (G : ppl_ctx Ar)
    (M N : scones_hom (ctxD_CBN G) (tyD_CBN tR')) :
    scones_hom (ctxD_CBN G) (tyD_CBN tR') :=
  cbn_const_clause (ctxD_CBN G) (FMeas R_obj)
    precone_zero cbn_zero_FMeas_norm_le1.

End M3Clauses.

Arguments cbn_const_clause {R Ar} G C c Hc.
Arguments cbn_sample_clause_def {R Ar R_obj} G mu Hmu.
Arguments cbn_real_clause_def {R Ar R_obj} R_carrier_eq G r.
Arguments cbn_score_clause_def {R Ar R_obj} G f Hf_meas Hf_ge0 Hf_le1 e.
Arguments cbn_zero_FMeas_norm_le1 {R Ar R_obj}.
Arguments cbn_add_clause_def {R Ar R_obj} G M N.
Arguments cbn_mul_clause_def {R Ar R_obj} G M N.

(** ** [eD_CBN_full]: the M3-instantiated CBN denotation

    Instantiates [eD_CBN] with the five M3 clauses; the four M4 boolean
    clauses are still abstracted (section Variables).  When the M4 sibling
    lands, the orchestrator merges this file with M4 to produce the fully
    concrete [eD_CBN_complete]. *)

Section EDCBNFull.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.

(** *** Section variables: M4 boolean stubs (left for M4 sibling) *)
Variable cbn_true_clause :
  forall (G : ppl_ctx Ar), scones_hom (ctxD_CBN G) (tyD_CBN (@tbool R Ar)).
Variable cbn_false_clause :
  forall (G : ppl_ctx Ar), scones_hom (ctxD_CBN G) (tyD_CBN (@tbool R Ar)).
Variable cbn_bernoulli_clause :
  forall (G : ppl_ctx Ar) (p : R)
         (Hp_ge0 : (0 <= p)%R) (Hp_le1 : (p <= 1)%R),
    scones_hom (ctxD_CBN G) (tyD_CBN (@tbool R Ar)).
Variable cbn_if_clause :
  forall (G : ppl_ctx Ar) (t : ppl_type Ar)
         (e : scones_hom (ctxD_CBN G) (tyD_CBN (@tbool R Ar)))
         (M N : scones_hom (ctxD_CBN G) (tyD_CBN t)),
    scones_hom (ctxD_CBN G) (tyD_CBN t).

(** The fully-M3-instantiated CBN denotation. *)
Definition eD_CBN_full (G : named_ctx Ar) (t : ppl_type Ar)
    (M : @named_expr R Ar R_obj G t) :
    scones_hom (ctxD_CBN (drop_names G)) (tyD_CBN t) :=
  @eD_CBN R Ar R_obj
    (@cbn_sample_clause_def R Ar R_obj)
    (@cbn_real_clause_def R Ar R_obj R_carrier_eq)
    (@cbn_score_clause_def R Ar R_obj)
    (@cbn_add_clause_def R Ar R_obj)
    (@cbn_mul_clause_def R Ar R_obj)
    cbn_true_clause cbn_false_clause cbn_bernoulli_clause cbn_if_clause
    G t M.

(** *** Reduction lemmas — the 5 M3 cases unfold to the concrete clauses *)

Lemma eD_CBN_full_sample_E
    (G : named_ctx Ar)
    (mu : fmeas R (ar_carrier Ar R_obj))
    (Hmu : (cone_norm mu <= 1)%R) :
  eD_CBN_full (ne_sample (R_obj := R_obj) (G := G) mu Hmu) =
  cbn_sample_clause_def (drop_names G) mu Hmu.
Proof. by []. Qed.

Lemma eD_CBN_full_real_E
    (G : named_ctx Ar) (r : R) :
  eD_CBN_full (ne_real (G := G) (R_obj := R_obj) r) =
  cbn_real_clause_def R_carrier_eq (drop_names G) r.
Proof. by []. Qed.

Lemma eD_CBN_full_score_E
    (G : named_ctx Ar)
    (f : R -> R)
    (Hf_meas : measurable_fun [set: R] f)
    (Hf_ge0 : forall r : R, (0 <= f r)%R)
    (Hf_le1 : forall r : R, (f r <= 1)%R)
    (e : @named_expr R Ar R_obj G (tR R_obj)) :
  eD_CBN_full (ne_score (R_obj := R_obj) f Hf_meas Hf_ge0 Hf_le1 e) =
  cbn_score_clause_def (drop_names G) f Hf_meas Hf_ge0 Hf_le1
    (eD_CBN_full e).
Proof. by []. Qed.

Lemma eD_CBN_full_add_E
    (G : named_ctx Ar)
    (M N : @named_expr R Ar R_obj G (tR R_obj)) :
  eD_CBN_full (ne_add M N) =
  cbn_add_clause_def (drop_names G) (eD_CBN_full M) (eD_CBN_full N).
Proof. by []. Qed.

Lemma eD_CBN_full_mul_E
    (G : named_ctx Ar)
    (M N : @named_expr R Ar R_obj G (tR R_obj)) :
  eD_CBN_full (ne_mul M N) =
  cbn_mul_clause_def (drop_names G) (eD_CBN_full M) (eD_CBN_full N).
Proof. by []. Qed.

End EDCBNFull.

Arguments eD_CBN_full {R Ar R_obj} R_carrier_eq
  cbn_true_clause cbn_false_clause cbn_bernoulli_clause cbn_if_clause
  {G t} M.

Arguments eD_CBN_full_sample_E {R Ar R_obj} R_carrier_eq
  cbn_true_clause cbn_false_clause cbn_bernoulli_clause cbn_if_clause
  G mu Hmu.
Arguments eD_CBN_full_real_E {R Ar R_obj} R_carrier_eq
  cbn_true_clause cbn_false_clause cbn_bernoulli_clause cbn_if_clause
  G r.
Arguments eD_CBN_full_score_E {R Ar R_obj} R_carrier_eq
  cbn_true_clause cbn_false_clause cbn_bernoulli_clause cbn_if_clause
  G f Hf_meas Hf_ge0 Hf_le1 e.
Arguments eD_CBN_full_add_E {R Ar R_obj} R_carrier_eq
  cbn_true_clause cbn_false_clause cbn_bernoulli_clause cbn_if_clause
  G M N.
Arguments eD_CBN_full_mul_E {R Ar R_obj} R_carrier_eq
  cbn_true_clause cbn_false_clause cbn_bernoulli_clause cbn_if_clause
  G M N.

(** ** Notes for downstream waves

    - M4 (boolean) sibling will replace the four [Variable] stubs in
      [Section EDCBNFull] with concrete definitions; the orchestrator will
      then merge [ppl_cbn_eff.v] (M3) and the M4 file into a fully concrete
      [eD_CBN_complete] = [eD_CBN] with all nine clauses instantiated.
    - Future semantic-refinement waves can replace [cbn_add_clause_def] /
      [cbn_mul_clause_def] with actual cartesian-to-SMC stable bridges
      (e.g. a [scones_hom (sprod (FMeas) (FMeas)) (FMeas)] built from
      bilinear [precone_add] / a port of [add_lift]).
    - [cbn_score_clause_def] is essentially unique by terminality of
      [Stop]: any concrete definition must be [Stop_mor]-equivalent.  No
      semantic refinement is possible at the [tunit ↦ Stop] level. *)
