(**md*** CBN PPL chapter M4 (boolean cascade)

    This file is NOT part of the Ehrhard-Geoffroy 2025 formalization
    (paper §2-§9). It is the M4 wave of the call-by-name PPL trunk
    [theories/programs/ppl_cbn.v]: the four boolean stubs
    [cbn_true_clause], [cbn_false_clause], [cbn_bernoulli_clause] and
    [cbn_if_clause] are replaced by concrete CBN denotations native to
    [SCones].  The remaining M3 stubs (sample, real, score, add, mul)
    are still section-variable-bound in [eD_CBN_bool]; a parallel M3
    wave fills them. *)

(** * The boolean clauses [cbn_true / false / bernoulli / if]

    Three constants and one [if]-then-else combinator on
    [bool_cone_car Ar = ⟦tbool⟧].  Constants ([true]/[false]/[Bernoulli])
    are constant SCones-arrows at the corresponding [bool_cone_car]
    element ([bool_dirac_true]/[bool_dirac_false]/[bernoulli p]); built
    from the standalone [scones_const] combinator of
    [theories/programs/infra/bool_case_scones.v].

    The [if]-then-else clause [cbn_if_clause] takes:
    - [e : scones_hom G B] (the boolean scrutinee), with
      [B := bool_cone_car Ar];
    - [M, N : scones_hom G A] (the two branches), where
      [A := tyD_CBN t].

    Result: [scones_hom G A] semantically computing
    [bool_case (sc_fun e g) (sc_fun M g) (sc_fun N g)] on the unit ball
    of [G].  Construction uses the SCones internal hom [stablehom G A]:
    M, N are viewed as POINTS [Mh, Nh] of [stablehom G A] (via
    [sc_to_sh] of [theories/homs/seely.v]); both have stablehom norm
    [≤ 1] (= operator norm) by [sc_norm_le1].  Then
    [bool_case_linhom Mh Nh] of [theories/programs/infra/bool_case_hom.v]
    is a linear [linhom_car B (stablehom G A)]; via [linhom_icones] and
    [ders] this lifts to a [scones_hom B (stablehom G A)].  Pre-compose
    with [e] to get [scones_hom G (stablehom G A)], then evaluate
    diagonally against [scones_id G] via [Ev]-after-[spair].  THIS IS
    THE GENUINE NEW COMBINATOR of the M4 wave.

    The four reduction lemmas
    [eD_CBN_bool_{true,false,bernoulli,if}_E] are axiom-free unfoldings
    against the [eD_CBN] definition. *)

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
Require Import Icones.homs.linhom.
Require Import Icones.homs.coalgebra.
Require Import Icones.homs.seely_defs.
Require Import Icones.programs.infra.bool_cone.
Require Import Icones.stable.totmono.
Require Import Icones.stable.stablehom.
Require Import Icones.stable.scones_cat.
Require Import Icones.stable.fixpoint.
Require Import Icones.homs.seely.
Require Import Icones.stable.scones_ccc.
Require Import Icones.programs.infra.bool_case_hom.
Require Import Icones.programs.infra.bool_case_scones.
Require Import Icones.programs.ppl.
Require Import Icones.programs.examples.
Require Import Icones.programs.ppl_cbn.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** [cbn_true_clause_def] / [cbn_false_clause_def]
    — constant SCones-arrows at [bool_dirac_true] / [bool_dirac_false] *)

Section CbnBoolConstants.
Variables (R : realType) (Ar : MeasSubcat R).

(** The constant [true] clause: the constant SCones-arrow at
    [bool_dirac_true].  Both Diracs have norm [1], so they lie on the
    unit ball, and the standalone [scones_const] of
    [bool_case_scones.v] delivers the SCones-arrow. *)
Definition cbn_true_clause_def (G : ppl_ctx Ar) :
    scones_hom (ctxD_CBN G) (bool_cone_car Ar) :=
  scones_const (ctxD_CBN G) bool_dirac_true bool_dirac_true_norm_le1.

(** The constant [false] clause. *)
Definition cbn_false_clause_def (G : ppl_ctx Ar) :
    scones_hom (ctxD_CBN G) (bool_cone_car Ar) :=
  scones_const (ctxD_CBN G) bool_dirac_false bool_dirac_false_norm_le1.

(** The Bernoulli clause at parameter [p ∈ [0, 1]]: the constant
    SCones-arrow at [bernoulli p Hp_ge0 Hp_le1].  Its norm is [1]
    ([bernoulli_norm]), so the standalone constant applies. *)
Definition cbn_bernoulli_clause_def (G : ppl_ctx Ar) (p : R)
    (Hp_ge0 : (0 <= p)%R) (Hp_le1 : (p <= 1)%R) :
    scones_hom (ctxD_CBN G) (bool_cone_car Ar) :=
  scones_const (ctxD_CBN G) (bernoulli p Hp_ge0 Hp_le1)
               (bernoulli_norm_le1 p Hp_ge0 Hp_le1).

End CbnBoolConstants.

Arguments cbn_true_clause_def {R Ar} G.
Arguments cbn_false_clause_def {R Ar} G.
Arguments cbn_bernoulli_clause_def {R Ar} G p Hp_ge0 Hp_le1.

(** ** [cbn_bernoulli_f_clause_def] — degenerate zero clause

    The CBN reading of the VALUE-DEPENDENT Bernoulli
    [ne_bernoulli_f f Hf_meas Hf_ge0 Hf_le1 e]: the constant
    SCones-arrow at [precone_zero : bool_cone_car Ar].

    DEGENERATE BY DESIGN, consistent with the option-(γ) M3 choice for
    [cbn_add_clause_def] / [cbn_mul_clause_def] ([ppl_cbn_eff.v]): an
    honest CBN clause would need the scrutinee's value, i.e. the same
    cartesian-to-SMC stable bridge that blocks the arithmetic clauses.
    The arguments are accepted for type compatibility with the
    [Hypothesis cbn_bernoulli_f_clause] signature of [ppl_cbn.v] but do
    not influence the morphism.  The honest semantics lives on the CBV
    side ([ppl_cbv.v]'s [bern_lift] composite). *)

Section CbnBernoulliFClause.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).

Definition cbn_bernoulli_f_clause_def
    (G : ppl_ctx Ar)
    (f : R -> R)
    (Hf_meas : measurable_fun [set: R] f)
    (Hf_ge0 : forall r : R, (0 <= f r)%R)
    (Hf_le1 : forall r : R, (f r <= 1)%R)
    (e : scones_hom (ctxD_CBN G) (tyD_CBN (tR R_obj))) :
    scones_hom (ctxD_CBN G) (bool_cone_car Ar) :=
  scones_const (ctxD_CBN G) (precone_zero : bool_cone_car Ar)
               (precone_zero_norm_le1 (bool_cone_car Ar)).

End CbnBernoulliFClause.

Arguments cbn_bernoulli_f_clause_def {R Ar R_obj} G f
  Hf_meas Hf_ge0 Hf_le1 e.

(** ** [cbn_if_clause_def] — the [if]-then-else combinator

    Given:
    - [G : ppl_ctx Ar] and [t : ppl_type Ar];
    - [e : scones_hom (ctxD_CBN G) (bool_cone_car Ar)] the boolean
      scrutinee;
    - [M, N : scones_hom (ctxD_CBN G) (tyD_CBN t)] the two branches;

    deliver [scones_hom (ctxD_CBN G) (tyD_CBN t)] semantically
    computing [bool_case (sc_fun e g) (sc_fun M g) (sc_fun N g)] on
    the unit ball of [ctxD_CBN G].

    Construction:
    1. View [M, N] as points of [stablehom (ctxD_CBN G) (tyD_CBN t)]
       via [sc_to_sh].  Both have stablehom-cone-norm [≤ 1] from
       [sc_norm_le1].
    2. [bool_case_linhom (sc_to_sh M) (sc_to_sh N) HMh HNh] gives a
       [linhom_car (bool_cone_car Ar) (stablehom (ctxD_CBN G) (tyD_CBN t))].
    3. Bridge via [linhom_icones] + [ders] to
       [scones_hom (bool_cone_car Ar) (stablehom (ctxD_CBN G) (tyD_CBN t))].
    4. Pre-compose with [e] to get
       [scones_hom (ctxD_CBN G) (stablehom (ctxD_CBN G) (tyD_CBN t))].
    5. Diagonal-evaluate against [scones_id (ctxD_CBN G)] via
       [Ev]-after-[spair] to land in [scones_hom (ctxD_CBN G) (tyD_CBN t)]. *)

Section CbnIfClause.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (G : ppl_ctx Ar).
Variable (t : ppl_type Ar).

Local Notation Gc := (ctxD_CBN G).
Local Notation A := (tyD_CBN t).
Local Notation B := (bool_cone_car Ar).
Local Notation Sh := (stablehom Gc A).

(** Step 1: a [scones_hom Gc A] viewed as a point of [Sh] via
    [sc_to_sh] has stablehom-cone-norm [≤ 1].  The two normsets are
    syntactically the same set ([sh_normset (sc_to_sh f) =
    sc_normset (sc_fun f)]), so the sups are equal. *)
Lemma sc_to_sh_cone_norm_le1 (f : scones_hom Gc A) :
  (cone_norm (sc_to_sh f) <= 1)%R.
Proof.
rewrite -[cone_norm _]/(sh_norm (sc_to_sh f)).
apply: sh_norm_lub => x Hx.
exact: sc_image_ball.
Qed.

Variable e : scones_hom Gc B.
Variable M N : scones_hom Gc A.

(** Step 2: the [bool_case]-by-stablehom-branches [linhom_car]. *)
Definition cbn_if_linhom : linhom_car Ar B Sh :=
  bool_case_linhom (sc_to_sh M) (sc_to_sh N)
                   (sc_to_sh_cone_norm_le1 M)
                   (sc_to_sh_cone_norm_le1 N).

(** Step 3a: norm bound. *)
Lemma cbn_if_linhom_norm_le1 : (cone_norm cbn_if_linhom <= 1)%R.
Proof.
exact: bool_case_linhom_norm_le1.
Qed.

(** Step 3b: bridge to [scones_hom B Sh] via [linhom_icones] then [ders]. *)
Definition cbn_if_scones_B_Sh : scones_hom B Sh :=
  ders (linhom_icones cbn_if_linhom cbn_if_linhom_norm_le1).

(** Step 4: pre-compose with [e] to get a [scones_hom Gc Sh]. *)
Definition cbn_if_scones_Gc_Sh : scones_hom Gc Sh :=
  scones_comp cbn_if_scones_B_Sh e.

(** Step 5: diagonal-evaluate via [Ev]-after-[spair]. *)
Definition cbn_if_clause_def : scones_hom Gc A :=
  scones_comp (Ev Gc A) (spair cbn_if_scones_Gc_Sh (scones_id Gc)).

(** *** Reduction on the unit ball

    On [g : Gc] with [cone_norm g <= 1], the result computes to
    [bool_case (sc_fun e g) (sc_fun M g) (sc_fun N g)].  The
    intermediate computations follow the construction steps:
    [Ev] reduces by [Ev_pair], [spair] reduces to [sprod_pair] by
    [scpair_ball], [scones_comp] reduces by [scomp_ball], [ders] reduces
    by [sc_clamp_ball], [linhom_icones] reduces to [linhom_fun], and
    [bool_case_linhom] computes to [bool_case]. *)

Lemma cbn_if_clause_def_E (g : Gc) :
  (cone_norm g <= 1)%R ->
  sc_fun cbn_if_clause_def g =
  bool_case (sc_fun e g) (sc_fun M g) (sc_fun N g).
Proof.
move=> Hg.
have Heg : (cone_norm (sc_fun e g) <= 1)%R by exact: sc_image_ball.
have HSh_ball : (cone_norm (linhom_fun cbn_if_linhom (sc_fun e g)) <= 1)%R.
  have step := linhom_norm_apply_le cbn_if_linhom_norm_le1 (sc_fun e g).
  rewrite mul1r in step.
  exact: (le_trans step Heg).
have Hpair_ball : (cone_norm (sprod_pair
    (linhom_fun cbn_if_linhom (sc_fun e g)) g) <= 1)%R
  by exact: sprod_pair_norm_le1.
rewrite /cbn_if_clause_def (scomp_ball _ _ Hg).
have Hpair : sc_fun (spair cbn_if_scones_Gc_Sh (scones_id Gc)) g
           = sprod_pair (sc_fun cbn_if_scones_Gc_Sh g)
                         (sc_fun (scones_id Gc) g)
  by exact: scpair_ball.
rewrite Hpair.
have Hid : sc_fun (scones_id Gc) g = g
  by rewrite /scones_id /= (sc_clamp_ball Hg).
rewrite Hid.
have Hinner :
    sc_fun cbn_if_scones_Gc_Sh g =
    sc_fun cbn_if_scones_B_Sh (sc_fun e g)
  by rewrite /cbn_if_scones_Gc_Sh (scomp_ball _ _ Hg).
rewrite Hinner.
have HB : sc_fun cbn_if_scones_B_Sh (sc_fun e g)
        = linhom_fun cbn_if_linhom (sc_fun e g).
  rewrite /cbn_if_scones_B_Sh /ders /= (sc_clamp_ball Heg).
  by rewrite /linhom_icones /=.
rewrite HB (Ev_pair _ _ Hpair_ball).
by rewrite /cbn_if_linhom /= /bool_case /=.
Qed.

End CbnIfClause.

Arguments cbn_if_clause_def {R Ar G t} e M N.
Arguments cbn_if_clause_def_E {R Ar G t} e M N g.

(** ** The CBN denotation [eD_CBN_bool]

    Instantiate the trunk's [eD_CBN] with the four concrete clauses
    above (and let the M3 stubs remain abstract: they are still
    [Hypothesis]-bound, to be filled by [ppl_cbn_real.v]). *)

Section EDCBNBool.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).

Local Notation tR' := (tR R_obj).

(** M3 stubs — still abstract. *)
Variable cbn_sample_clause :
  forall (G : ppl_ctx Ar)
         (mu : fmeas R (ar_carrier Ar R_obj))
         (Hmu : (cone_norm mu <= 1)%R),
    scones_hom (ctxD_CBN G) (tyD_CBN tR').
Variable cbn_real_clause :
  forall (G : ppl_ctx Ar) (r : R),
    scones_hom (ctxD_CBN G) (tyD_CBN tR').
Variable cbn_score_clause :
  forall (G : ppl_ctx Ar)
         (f : R -> R)
         (Hf_meas : measurable_fun [set: R] f)
         (Hf_ge0 : forall r : R, (0 <= f r)%R)
         (Hf_le1 : forall r : R, (f r <= 1)%R)
         (e : scones_hom (ctxD_CBN G) (tyD_CBN tR')),
    scones_hom (ctxD_CBN G) (tyD_CBN (@tunit R Ar)).
Variable cbn_add_clause :
  forall (G : ppl_ctx Ar)
         (M N : scones_hom (ctxD_CBN G) (tyD_CBN tR')),
    scones_hom (ctxD_CBN G) (tyD_CBN tR').
Variable cbn_mul_clause :
  forall (G : ppl_ctx Ar)
         (M N : scones_hom (ctxD_CBN G) (tyD_CBN tR')),
    scones_hom (ctxD_CBN G) (tyD_CBN tR').

(** The CBN denotation with boolean clauses instantiated. *)
Definition eD_CBN_bool (G : named_ctx Ar) (t : ppl_type Ar)
    (M : @named_expr R Ar R_obj G t) :
    scones_hom (ctxD_CBN (drop_names G)) (tyD_CBN t) :=
  @eD_CBN R Ar R_obj
    cbn_sample_clause cbn_real_clause cbn_score_clause
    cbn_add_clause cbn_mul_clause
    (@cbn_true_clause_def R Ar)
    (@cbn_false_clause_def R Ar)
    (@cbn_bernoulli_clause_def R Ar)
    (@cbn_bernoulli_f_clause_def R Ar R_obj)
    (@cbn_if_clause_def R Ar) G t M.

(** *** Soundness reductions

    Headline structural-reduction lemmas for the four constructors. *)

(** [ne_true] denotes the constant [bool_dirac_true] clause. *)
Lemma eD_CBN_bool_true_E (G : named_ctx Ar) :
  eD_CBN_bool (@ne_true R Ar R_obj G) =
  cbn_true_clause_def (drop_names G).
Proof. by []. Qed.

(** [ne_false] denotes the constant [bool_dirac_false] clause. *)
Lemma eD_CBN_bool_false_E (G : named_ctx Ar) :
  eD_CBN_bool (@ne_false R Ar R_obj G) =
  cbn_false_clause_def (drop_names G).
Proof. by []. Qed.

(** [ne_bernoulli p Hp_ge0 Hp_le1] denotes the constant
    [bernoulli p]-clause. *)
Lemma eD_CBN_bool_bernoulli_E (G : named_ctx Ar) (p : R)
    (Hp_ge0 : (0 <= p)%R) (Hp_le1 : (p <= 1)%R) :
  eD_CBN_bool (@ne_bernoulli R Ar R_obj G p Hp_ge0 Hp_le1) =
  cbn_bernoulli_clause_def (drop_names G) p Hp_ge0 Hp_le1.
Proof. by []. Qed.

(** [ne_bernoulli_f f e] denotes the (γ)-degenerate constant-zero
    clause (see [cbn_bernoulli_f_clause_def]). *)
Lemma eD_CBN_bool_bernoulli_f_E (G : named_ctx Ar) (f : R -> R)
    (Hf_meas : measurable_fun [set: R] f)
    (Hf_ge0 : forall r : R, (0 <= f r)%R)
    (Hf_le1 : forall r : R, (f r <= 1)%R)
    (e : @named_expr R Ar R_obj G (tR R_obj)) :
  eD_CBN_bool (ne_bernoulli_f f Hf_meas Hf_ge0 Hf_le1 e) =
  cbn_bernoulli_f_clause_def (drop_names G) f Hf_meas Hf_ge0 Hf_le1
    (eD_CBN_bool e).
Proof. by []. Qed.

(** [ne_if e M N] denotes the if-clause applied to the three subterm
    denotations. *)
Lemma eD_CBN_bool_if_E (G : named_ctx Ar) (t : ppl_type Ar)
    (e : @named_expr R Ar R_obj G tbool)
    (M N : @named_expr R Ar R_obj G t) :
  eD_CBN_bool (@ne_if R Ar R_obj G t e M N) =
  cbn_if_clause_def (eD_CBN_bool e) (eD_CBN_bool M) (eD_CBN_bool N).
Proof. by []. Qed.

(** *** Pointwise computation rule for [eD_CBN_bool] at [ne_if]

    On the unit ball of [ctxD_CBN (drop_names G)], the [ne_if]
    denotation computes to [bool_case] of the three subterm
    denotations. *)
Lemma eD_CBN_bool_if_pointwise_E (G : named_ctx Ar) (t : ppl_type Ar)
    (e : @named_expr R Ar R_obj G tbool)
    (M N : @named_expr R Ar R_obj G t)
    (g : ctxD_CBN (drop_names G)) (Hg : (cone_norm g <= 1)%R) :
  sc_fun (eD_CBN_bool (@ne_if R Ar R_obj G t e M N)) g =
  bool_case (sc_fun (eD_CBN_bool e) g)
            (sc_fun (eD_CBN_bool M) g)
            (sc_fun (eD_CBN_bool N) g).
Proof.
rewrite eD_CBN_bool_if_E.
exact: cbn_if_clause_def_E.
Qed.

End EDCBNBool.

Arguments eD_CBN_bool {R Ar R_obj}
  cbn_sample_clause cbn_real_clause cbn_score_clause
  cbn_add_clause cbn_mul_clause
  {G t} M.

(** ** Notes for downstream waves

    - The four [cbn_{true,false,bernoulli,if}_clause_def] definitions
      are CLOSED — they introduce no axioms.  Axiom-free verification
      via [rocq_assumptions] on each of [eD_CBN_bool_{true,false,
      bernoulli,if}_E] returns the three [boolp] axioms inherited
      from [mathcomp-analysis].
    - The headline new combinator is [cbn_if_clause_def] (and the
      stand-alone [scones_const] / [bool_case_fixed_scones] of
      [bool_case_scones.v]); the variable-branch obstruction noted in
      [theories/programs/ppl.v]'s [case_em] comment block is avoided
      here by promoting [M, N] to POINTS of [stablehom (ctxD_CBN G)
      (tyD_CBN t)] (the SCones internal hom), where [bool_case_linhom]
      applies verbatim with the per-branch operator-norm bounds
      [sc_to_sh_cone_norm_le1 M] / [sc_to_sh_cone_norm_le1 N] —
      identifying [sh_norm (sc_to_sh g) = sc_norm (sc_fun g)] (the
      [sh_normset] / [sc_normset] sets are syntactically equal).
    - The pointwise reduction [cbn_if_clause_def_E] threads the on-ball
      computation rules [scomp_ball] / [scpair_ball] / [sc_clamp_ball]
      / [Ev_pair] / [bool_case_linhom]'s underlying-function unfold,
      ending in the [bool_case] reading of [sc_fun e g] / [sc_fun M g]
      / [sc_fun N g] at the [stablehom]-cone level.
    - M3 (the effectful / numeric / real clauses) remains parameterised
      in this file via the [cbn_*_clause] section variables. *)
