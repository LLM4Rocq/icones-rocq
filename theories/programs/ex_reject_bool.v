(**md**************************************************************************)
(** * Boolean rejection / conditioning — the {0,1}-indicator instances

    BEYOND THE PAPER.  This file is NOT part of the Ehrhard-Geoffroy 2025
    formalization.  It is the FIRST INCREMENT of the generalization
    programme of [docs/hard_reject_condition.md] (sections 6-7): the
    BOOLEAN reject/condition headlines, derived as INSTANCES of the SOFT
    master theorem of [theories/programs/ex_reject_model.v] specialised
    at a {0,1}-valued test function.

    ** The reduction

    Fix a measurable predicate on the value space as a measurable accept
    SET [P_acc : set R].  Its indicator [f := \1_P_acc] is a measurable,
    [[0,1]]-valued real map, hence packs into a [testfn] bundle
    ([ind_testfn], the {0,1} clone of [gt0_ind]).  Writing [cR] for the
    carrier-to-[R] coercion and [A := cR^{-1}(P_acc)] for the carrier
    accept set, the BRIDGE is the integral of an indicator:
    [[
       \int[mu]_(x in U) (f (cR x))%:E = mu (A `&` U)         (If_bool)
    ]]
    a one-line consequence of [integral_indic].  Specialising the soft
    theorems of [ex_reject_model.v] at this [f] turns every
    [\int f dnu_M] into [nu_M A] and every [\int_U f dnu_M] into
    [nu_M (A `&` U)], giving the boolean headlines (with
    [Z := 1 - nu_M(setT) + nu_M(A)] the normaliser):

    - [reject_bool_master]            : [Z · reject(U) = nu_M (A `&` U)]
    - [reject_bool_is_normalised]     : [reject(U) = nu_M(A `&` U) / Z]
    - [reject_bool_mass]              : [reject(setT) = nu_M(A) / Z]
    - [reject_bool_mass_one]          : [reject(setT) = 1] (prob. model)
    - [reject_bool_zero]              : [reject(U) = 0] (empty accept set)
    - [condition_bool_E]             : [cond(U) = nu_M (A `&` U)]
    - [condition_bool_evidence]      : [cond(setT) = nu_M(A)] (evidence)
    - [reject_normalises_condition_bool] : [Z · reject(U) = cond(U)]

    The construction edits NO existing proof: it only INSTANTIATES the
    already-proved soft theorems. *)
(***************************************************************************)

From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import reals constructive_ereal ereal measure numfun.
From mathcomp Require Import measurable_realfun lebesgue_integral_definition.
From Stdlib Require Import Strings.String.
From Icones Require Import mcones.ar mcones.fmeas homs.linhom homs.seely.
From Icones Require Import programs.ppl programs.ppl_cbv programs.ex_reject_model.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** The {0,1}-indicator test-function builder

    An exact clone of [gt0_ind] / [gauss_*] (ppl.v): a measurable accept
    SET [P_acc] yields the [[0,1]]-valued indicator [\1_P_acc], packed
    into the bundled [testfn] record.  The carrier map is fixed at
    [R -> R] (so the ring is determined) and its projections are the
    [{0,1}]-bound witnesses. *)
Section IndKit.
Variable (R : realType).
Variable (P_acc : set R).
Hypothesis mPacc : measurable P_acc.

Definition indf : R -> R := \1_P_acc.

Lemma indf_meas : measurable_fun [set: R] indf.
Proof. exact: (measurable_indic mPacc). Qed.

Lemma indf_ge0 (r : R) : (0 <= indf r)%R.
Proof. by rewrite /indf indicE; case: (_ \in _). Qed.

Lemma indf_le1 (r : R) : (indf r <= 1)%R.
Proof. by rewrite /indf indicE; case: (_ \in _); rewrite ?ler01. Qed.

Definition ind_testfn : testfn R := mk_testfn indf indf_meas indf_ge0 indf_le1.

End IndKit.

Arguments ind_testfn {R} P_acc mPacc.

(** ** The boolean headlines

    Mirror the section interface of [ReadableHeadlines] (ex_reject_model.v):
    only the minimal plumbing [R, Ar, P, R_to_carrier_meas, Mbody] plus
    the accept set [P_acc] and its measurability.  The soft test function
    is fixed to the indicator bundle [f0 := ind_testfn P_acc mPacc]. *)
Section BoolHeadlines.
Variables (R : realType) (Ar : MeasSubcat R) (P : probObj Ar).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier (po_robj_eq P)).
Variable (P_acc : set R).
Hypothesis mPacc : measurable P_acc.
Variable (Mbody :
  @named_expr R Ar (po_robj P) (("_"%string, tunit) :: nil) (tR (po_robj P))).

(** The carrier-to-[R] coercion and the indicator test bundle. *)
Local Notation cR := (carrier_to_R (po_robj_eq P)).
Local Notation f0 := (ind_testfn P_acc mPacc).

(** The three program denotations, in the exact [eD]-shape printed by the
    soft headlines after section close (the measurability implicits of
    [eD] are supplied by name — they are not inferrable on their own). *)
Local Notation nu_M :=
  (fmeas_mu (linhom_fun (eD (R_carrier_meas := po_robj_meas P)
     (R_to_carrier_meas := R_to_carrier_meas) (model_run (P:=P) Mbody)) one1)).
Local Notation reject :=
  (fmeas_mu (linhom_fun (eD (R_carrier_meas := po_robj_meas P)
     (R_to_carrier_meas := R_to_carrier_meas) (reject_prog (P:=P) f0 Mbody)) one1)).
Local Notation cond :=
  (fmeas_mu (linhom_fun (eD (R_carrier_meas := po_robj_meas P)
     (R_to_carrier_meas := R_to_carrier_meas) (condition_prog (P:=P) f0 Mbody)) one1)).

(** The carrier ACCEPT SET [A := cR^{-1}(P_acc)], measurable because [cR]
    ([= po_robj_meas P]) is measurable. *)
Definition A : set (ar_carrier Ar (po_robj P)) := cR @^-1` P_acc.

Lemma mA : measurable A.
Proof.
have H := (po_robj_meas P) measurableT P_acc mPacc; rewrite setTI in H; exact: H.
Qed.

(** The indicator bundle's carrier map IS [\1_P_acc] (definitionally, via
    the primitive [test_fun] projection). *)
Lemma f0E (r : R) : f0 r = \1_P_acc r.
Proof. by []. Qed.

Local Open Scope ereal_scope.

(** *** The bridge — the integral of the {0,1}-test is the measure of the
    accept set restricted to the domain. *)
Lemma If_bool (mu : measure (ar_carrier Ar (po_robj P)) R)
    U (mU : measurable U) :
  \int[mu]_(x in U) (f0 (cR x))%:E = mu (A `&` U).
Proof.
rewrite -(integral_indic mu mU mA); apply: eq_integral => x _.
by rewrite f0E !indicE.
Qed.

Lemma If_bool_setT (mu : measure (ar_carrier Ar (po_robj P)) R) :
  \int[mu]_(x in [set: ar_carrier Ar (po_robj P)]) (f0 (cR x))%:E = mu A.
Proof. by rewrite (If_bool mu setT measurableT) setIT. Qed.

(** *** Boolean reject headlines — instances of [reject_prog_*]. *)

(** The master identity, boolean form:
    [[
       (1 - nu_M(setT) + nu_M(A)) · reject(U) = nu_M (A `&` U).
    ]] *)
Theorem reject_bool_master U (mU : measurable U) :
  ((1 - fine (nu_M setT) + fine (nu_M A))%R)%:E * reject U = nu_M (A `&` U).
Proof.
have H := reject_prog_master R_to_carrier_meas f0 Mbody mU.
rewrite (If_bool nu_M U mU) (If_bool_setT nu_M) in H.
exact: H.
Qed.

(** The normalised form (loop makes progress):
    [[
       reject(U) = nu_M(A `&` U) / (1 - nu_M(setT) + nu_M(A)).
    ]] *)
Theorem reject_bool_is_normalised :
  (0 < 1 - fine (nu_M setT) + fine (nu_M A))%R ->
  forall U, measurable U ->
  reject U =
  ((fine (nu_M (A `&` U))
    / (1 - fine (nu_M setT) + fine (nu_M A)))%R)%:E.
Proof.
rewrite -(If_bool_setT nu_M) => Hpos U mU.
rewrite -(If_bool nu_M U mU).
exact: (reject_prog_is_normalised Hpos mU).
Qed.

(** Total mass, normalised form:
    [[
       reject(setT) = nu_M(A) / (1 - nu_M(setT) + nu_M(A)).
    ]] *)
Theorem reject_bool_mass :
  (0 < 1 - fine (nu_M setT) + fine (nu_M A))%R ->
  reject setT =
  ((fine (nu_M A) / (1 - fine (nu_M setT) + fine (nu_M A)))%R)%:E.
Proof.
move=> Hpos; have H := reject_bool_is_normalised Hpos setT measurableT.
rewrite setIT in H; exact: H.
Qed.

(** Almost-sure termination for probability models:
    [[
       nu_M(setT) = 1  ->  0 < nu_M(A)  ->  reject(setT) = 1.
    ]] *)
Theorem reject_bool_mass_one : nu_M setT = 1 -> 0 < nu_M A -> reject setT = 1.
Proof.
move=> Hm1 HA; apply: (reject_prog_mass_one Hm1).
by rewrite (If_bool_setT nu_M).
Qed.

(** Certain rejection diverges: an EMPTY accept set forces the zero
    measure, whatever the model does:
    [[
       P_acc = set0  ->  reject(U) = 0.
    ]] *)
Theorem reject_bool_zero U : P_acc = set0 -> reject U = 0.
Proof.
move=> HP0; apply: reject_prog_zero => r.
by rewrite f0E indicE HP0 in_set0.
Qed.

(** *** Boolean condition headlines — instances of [condition_*]. *)

(** The conditioning law, boolean form:
    [[
       cond(U) = nu_M (A `&` U).
    ]] *)
Theorem condition_bool_E U (mU : measurable U) : cond U = nu_M (A `&` U).
Proof. by rewrite (condition_E R_to_carrier_meas f0 Mbody mU) (If_bool nu_M U mU). Qed.

(** The model EVIDENCE: the conditioned model's total mass is [nu_M(A)]. *)
Theorem condition_bool_evidence : cond setT = nu_M A.
Proof.
have H := condition_bool_E setT measurableT; rewrite setIT in H; exact: H.
Qed.

(** The equivalence — rejection sampling computes the conditioned model's
    normalised distribution (division-free):
    [[
       (1 - nu_M(setT) + nu_M(A)) · reject(U) = cond(U).
    ]] *)
Theorem reject_normalises_condition_bool U (mU : measurable U) :
  ((1 - fine (nu_M setT) + fine (nu_M A))%R)%:E * reject U = cond U.
Proof. by rewrite (condition_bool_E U mU); exact: (reject_bool_master U mU). Qed.

(** The DIVISION form against the conditioned model:
    [[
       reject(U) = cond(U) / (1 - nu_M(setT) + nu_M(A)).
    ]] *)
Theorem reject_computes_condition_bool :
  (0 < 1 - fine (nu_M setT) + fine (nu_M A))%R ->
  forall U, measurable U ->
  reject U =
  ((fine (cond U) / (1 - fine (nu_M setT) + fine (nu_M A)))%R)%:E.
Proof.
move=> Hpos U mU; rewrite (condition_bool_E U mU).
exact: (reject_bool_is_normalised Hpos U mU).
Qed.

(** The PROBABILITY-MODEL form: for a unit-mass model the normaliser is
    the model evidence, so
    [[
       cond(setT) · reject(U) = cond(U).
    ]] *)
Theorem reject_normalises_condition_prob_bool U (mU : measurable U) :
  nu_M setT = 1 -> cond setT * reject U = cond U.
Proof. move=> Hm1; exact: (reject_normalises_condition_prob f0 mU Hm1). Qed.

End BoolHeadlines.
