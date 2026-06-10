(**md**************************************************************************)
(** * CBN interpretation of the PPL — call-by-name semantics in [SCones]

    A parallel sibling to [theories/programs/ppl.v] providing a
    CBN interpretation of the same surface syntax [named_expr] of
    [theories/programs/ppl.v].  The CBN denotation lives NATIVELY in
    [SCones]: every expression denotes a [scones_hom (ctxD_CBN G)
    (tyD_CBN τ)] (no [Tobj] wrap on the codomain — this is the CBN
    win).  Recursion is FREE: [ne_fix]'s denotation packages
    [theories/stable/fixpoint.v]'s [Yfix] of the body's currying.

    ** Type interpretation (option B — pragmatic QBS reading) **
    [[
       ⟦tunit⟧         = Stop Ar
       ⟦tbase X⟧       = FMeas X                  (option B)
       ⟦tprod s t⟧     = sprod ⟦s⟧ ⟦t⟧
       ⟦tfun  A B⟧     = stablehom ⟦A⟧ ⟦B⟧        (SCones internal hom)
       ⟦tbool⟧         = bool_cone_car Ar
       ⟦tR'⟧           = FMeas R_obj
    ]]
    Contexts are interpreted right-associated with the head on the
    RIGHT:
    [[
       ⟦[]⟧      = Stop Ar
       ⟦t :: G⟧  = sprod ⟦G⟧ ⟦t⟧.
    ]]
    With this orientation, [hv_zero] reads the SECOND component (via
    [ssnd]) and [hv_succ] strips the head by reading the FIRST (via
    [sfst]) and recursing — exactly the [var_lookup] pattern of
    [ppl.v].

    ** Scope of this file (M1+M2+M5) **
    - M1: [tyD_CBN] / [ctxD_CBN] / computation Arguments directives.
    - M2: [var_lookup_CBN] + the core clauses of [eD_CBN] (ne_var,
      ne_tt, ne_pair, ne_fst, ne_snd, ne_lam, ne_app, ne_let).  CBN's
      [ne_let] is plain [scones_comp] after [spair (id, M)] — NO
      Kleisli monadic structure, since CBN is interpreted natively
      in [SCones].
    - M5: [ne_fix]'s clause via [Yfix] of [theories/stable/fixpoint.v]
      and a one-line soundness reduction lemma [eD_CBN_fix_E].

    ** Stubs (M3 + M4) **
    The effectful / numeric / boolean constructors ([ne_sample],
    [ne_score], [ne_real], [ne_add], [ne_mul], [ne_true], [ne_false],
    [ne_bernoulli], [ne_bernoulli_f], [ne_if]) are abstracted as
    [Hypothesis]-parametrised section variables [cbn_sample_clause],
    [cbn_score_clause], etc.  When [Section TermInterpCBN] closes,
    [eD_CBN] is parameterised by these hypotheses (no project axioms
    introduced).  Wave 2 (M3) and wave 3 (M4) will replace this
    section with concrete CBN denotations.

    ** Soundness — headline reductions **
    - [eD_CBN_fix_E]: the CBN fixpoint equation on the unit ball,
      using [Yfix_fix].
    - [ex_random_constant_CBN_denot_E]: structural reduction of the
      CBN denotation of [theories/programs/examples.v]'s
      [ex_random_constant] (modulo the [ne_sample] stub).

    All axiom-free modulo the three boolp axioms inherited from
    [mathcomp-analysis] (propositional extensionality, dependent
    function extensionality, constructive indefinite description). *)

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
Require Import Icones.homs.coalgebra.
Require Import Icones.homs.seely_defs.
Require Import Icones.programs.infra.bool_cone.
Require Import Icones.stable.totmono.
Require Import Icones.stable.stablehom.
Require Import Icones.stable.scones_cat.
Require Import Icones.stable.scones_ccc.
Require Import Icones.stable.fixpoint.
Require Import Icones.programs.ppl.
Require Import Icones.programs.examples.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** M1 — Type and context interpretation [tyD_CBN] / [ctxD_CBN]

    Every type denotes an iconeType of [Ar]; every context denotes the
    right-associated [sprod] cone of its components, with [Stop] at
    the empty end.  Option B at base types: [tbase X ↦ FMeas X] (the
    pragmatic QBS reading, NOT [Bang(FMeas X)]). *)

Section TypeInterpCBN.
Variables (R : realType) (Ar : MeasSubcat R).

Fixpoint tyD_CBN (t : ppl_type Ar) : ICone.type Ar :=
  match t with
  | tunit => Stop Ar
  | tbool => bool_cone_car Ar
  | tbase X => FMeas X
  | tprod s1 s2 => sprod (tyD_CBN s1) (tyD_CBN s2)
  | tfun A B => stablehom (tyD_CBN A) (tyD_CBN B)
  end.

Fixpoint ctxD_CBN (G : ppl_ctx Ar) : ICone.type Ar :=
  match G with
  | nil => Stop Ar
  | t :: G' => sprod (ctxD_CBN G') (tyD_CBN t)
  end.

End TypeInterpCBN.

Arguments tyD_CBN {R Ar} t.
Arguments ctxD_CBN {R Ar} G.

(** ** M2 — Variable lookup [var_lookup_CBN]

    Mirror of [var_lookup] of [ppl.v]: by structural recursion on the
    De Bruijn witness [v : has_var G t].
    - [hv_zero G' t']: the head; we project the SECOND component via
      [ssnd].
    - [hv_succ G' t' s v']: strip the head via [sfst] and recurse. *)

Section VarLookupCBN.
Variables (R : realType) (Ar : MeasSubcat R).

Fixpoint var_lookup_CBN (G : ppl_ctx Ar) (t : ppl_type Ar)
    (v : has_var G t) {struct v} :
    scones_hom (ctxD_CBN G) (tyD_CBN t) :=
  match v in has_var G0 t0 return scones_hom (ctxD_CBN G0) (tyD_CBN t0) with
  | hv_zero G' t' => ssnd (ctxD_CBN G') (tyD_CBN t')
  | hv_succ G' t' s v' =>
      scones_comp (var_lookup_CBN v') (sfst (ctxD_CBN G') (tyD_CBN s))
  end.

End VarLookupCBN.

Arguments var_lookup_CBN {R Ar G t} v.

(** ** Stubs for the effectful / numeric / boolean clauses

    Hypothesis-abstracted holes for the M3 (effects) and M4 (bool)
    waves.  Each stub has the SCones-native CBN signature [scones_hom
    (ctxD_CBN G) (tyD_CBN τ)] for the appropriate result type [τ].
    No project axioms are introduced: when [Section TermInterpCBN]
    closes, [eD_CBN] is parameterised by these hypotheses.  M3 and
    M4 will replace this section with concrete CBN clauses.

    Open question for M3/M4 (cf. final report):
    - [cbn_sample_clause]: should it integrate against the SCones
      [stablehom] CBN reading, or use the iconeType section
      [FMeas X] as a "constant" Dirac path?  The pragmatic choice
      below is a constant SCones morphism at the supplied [µ].
    - [cbn_score_clause]: the CBN reading of [ne_score] in option B
      is a hom into [Stop] (since [ne_score] returns [tunit]).
      Likely a unique map (any [Stop_mor]). *)

Section TermInterpCBN.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).

Local Notation tR' := (tR R_obj).
Local Notation T := (@ppl_type R Ar).

(** *** Stubs (M3 / M4) — Hypothesis abstraction *)

(** Sample primitive — CBN reading of [ne_sample mu Hmu] at type
    [tR'] in any context [G].  M3 wave will replace. *)
Hypothesis cbn_sample_clause :
  forall (G : ppl_ctx Ar)
         (mu : fmeas R (ar_carrier Ar R_obj))
         (Hmu : (cone_norm mu <= 1)%R),
    scones_hom (ctxD_CBN G) (tyD_CBN tR').

(** Real literal — CBN reading of [ne_real r] at type [tR'] in any
    context [G].  M3 will replace by a Dirac-at-[r] constant. *)
Hypothesis cbn_real_clause :
  forall (G : ppl_ctx Ar) (r : R),
    scones_hom (ctxD_CBN G) (tyD_CBN tR').

(** Score primitive — CBN reading of [ne_score f Hf_meas Hf_ge0
    Hf_le1 e] at type [tunit].  M3 will replace. *)
Hypothesis cbn_score_clause :
  forall (G : ppl_ctx Ar)
         (f : R -> R)
         (Hf_meas : measurable_fun [set: R] f)
         (Hf_ge0 : forall r : R, (0 <= f r)%R)
         (Hf_le1 : forall r : R, (f r <= 1)%R)
         (e : scones_hom (ctxD_CBN G) (tyD_CBN tR')),
    scones_hom (ctxD_CBN G) (tyD_CBN tunit).

(** Pointwise sum on two [tR']-valued CBN computations. *)
Hypothesis cbn_add_clause :
  forall (G : ppl_ctx Ar)
         (M N : scones_hom (ctxD_CBN G) (tyD_CBN tR')),
    scones_hom (ctxD_CBN G) (tyD_CBN tR').

(** Pointwise product on two [tR']-valued CBN computations. *)
Hypothesis cbn_mul_clause :
  forall (G : ppl_ctx Ar)
         (M N : scones_hom (ctxD_CBN G) (tyD_CBN tR')),
    scones_hom (ctxD_CBN G) (tyD_CBN tR').

(** Boolean constant [true] at [tbool] — M4 will replace. *)
Hypothesis cbn_true_clause :
  forall (G : ppl_ctx Ar), scones_hom (ctxD_CBN G) (tyD_CBN tbool).

(** Boolean constant [false] at [tbool] — M4 will replace. *)
Hypothesis cbn_false_clause :
  forall (G : ppl_ctx Ar), scones_hom (ctxD_CBN G) (tyD_CBN tbool).

(** Bernoulli sampling at [tbool] — M4 will replace. *)
Hypothesis cbn_bernoulli_clause :
  forall (G : ppl_ctx Ar) (p : R)
         (Hp_ge0 : (0 <= p)%R) (Hp_le1 : (p <= 1)%R),
    scones_hom (ctxD_CBN G) (tyD_CBN tbool).

(** Value-dependent Bernoulli at [tbool] — CBN reading of
    [ne_bernoulli_f f Hf_meas Hf_ge0 Hf_le1 e].  Same signature shape
    as [cbn_score_clause] (the witnesses plus the denotation of the
    [tR']-valued scrutinee), with codomain [tbool]. *)
Hypothesis cbn_bernoulli_f_clause :
  forall (G : ppl_ctx Ar)
         (f : R -> R)
         (Hf_meas : measurable_fun [set: R] f)
         (Hf_ge0 : forall r : R, (0 <= f r)%R)
         (Hf_le1 : forall r : R, (f r <= 1)%R)
         (e : scones_hom (ctxD_CBN G) (tyD_CBN tR')),
    scones_hom (ctxD_CBN G) (tyD_CBN tbool).

(** [if e then M else N] — boolean elimination at any type [t].
    M4 will replace. *)
Hypothesis cbn_if_clause :
  forall (G : ppl_ctx Ar) (t : T)
         (e : scones_hom (ctxD_CBN G) (tyD_CBN tbool))
         (M N : scones_hom (ctxD_CBN G) (tyD_CBN t)),
    scones_hom (ctxD_CBN G) (tyD_CBN t).

(** *** The CBN denotation [eD_CBN]

    By structural recursion on [named_expr]; the codomain is uniformly
    [scones_hom (ctxD_CBN (drop_names G)) (tyD_CBN t)] (NO [Tobj]
    wrap — CBN lives natively in [SCones]).

    Mirror conventions with [ppl.v]'s [eD]:
    - [ne_var v]: run [named_var_to_has_var v] then [var_lookup_CBN].
    - [ne_tt]: the unique [Stop]-valued morphism via [ders (Stop_mor _)].
    - [ne_pair / ne_fst / ne_snd]: [spair] / [sfst] / [ssnd] after
      [scones_comp].
    - [ne_lam]: [curry] of the body's denotation.  Concretely, the body
      [body : named_expr ((x, t1) :: G0) t2] denotes a [scones_hom
      (sprod (ctxD_CBN G0) (tyD_CBN t1)) (tyD_CBN t2)]; [curry] sends
      this to [scones_hom (ctxD_CBN G0) (stablehom (tyD_CBN t1)
      (tyD_CBN t2))] = [scones_hom (ctxD_CBN G0) (tyD_CBN (tfun t1
      t2))].  Clean.
    - [ne_app]: [Ev] after [spair].  Given [Vf : G ⇒ stablehom A B] and
      [Va : G ⇒ A], pair them via [spair] and post-compose with [Ev].
    - [ne_let]: plain [scones_comp] of the continuation after [spair
      (id, M)].  THE CBN WIN: NO Kleisli, no monadic structure — the
      continuation is interpreted in the extended product context and
      simply gets the captured value pair.
    - [ne_fix]: the Yfix wrap.  See [eD_CBN_fix_E] below. *)

Local Notation EX' G t :=
    (scones_hom (ctxD_CBN (drop_names G)) (tyD_CBN t)).

Fixpoint eD_CBN (G : named_ctx Ar) (t : T)
    (M : @named_expr R Ar R_obj G t) {struct M} : EX' G t :=
  match M in named_expr G0 t0 return EX' G0 t0 with
  | ne_var _ _ v => var_lookup_CBN (named_var_to_has_var v)
  | ne_tt G0 => ders (Stop_mor (ctxD_CBN (drop_names G0)))
  | ne_pair G0 t1 t2 M1 M2 => spair (eD_CBN M1) (eD_CBN M2)
  | ne_fst G0 t1 t2 M0 =>
      scones_comp (sfst (tyD_CBN t1) (tyD_CBN t2)) (eD_CBN M0)
  | ne_snd G0 t1 t2 M0 =>
      scones_comp (ssnd (tyD_CBN t1) (tyD_CBN t2)) (eD_CBN M0)
  | ne_lam G0 _ t1 t2 body => curry (eD_CBN body)
  (* [ne_fix]: package the body's denotation
     [eD_CBN body : scones_hom (sprod (ctxD_CBN G0) (tyD_CBN (tfun t1 t2)))
                               (tyD_CBN (tfun t1 t2))]
     via [curry] to [scones_hom (ctxD_CBN G0) (stablehom (tyD_CBN (tfun
     t1 t2)) (tyD_CBN (tfun t1 t2)))], then [scones_comp]-prefix with
     [Yfix] to land in [scones_hom (ctxD_CBN G0) (tyD_CBN (tfun t1
     t2))].  See [eD_CBN_fix_E] for the soundness lemma. *)
  | ne_fix G0 _ t1 t2 body =>
      scones_comp (Yfix (tyD_CBN (tfun t1 t2))) (curry (eD_CBN body))
  (* [ne_fix_mr s t Hfree body]: CBN recursion at any body type [t]
     satisfying [is_free_coalg_type t].  [Yfix] of [stable/fixpoint.v]
     works at ANY cone (its signature is
     [Yfix B : scones_hom (stablehom B B) B] for any [B : ICone.type Ar])
     so this clause is uniformly sound — no honest-scope limitation on
     the CBN side.

     IN PARTICULAR: at [t = tprod (tfun A1 B1) (tfun A2 B2)] this
     constructor yields a FULLY SOUND mutual-recursion fixpoint at the
     product-of-functions level, per the recipe.  The CBV side
     ([ppl.v]'s [Yfix_mr_pack]) has a documented honest-scope
     limitation at the product case, but CBN does not. *)
  | ne_fix_mr G0 _ t _ body =>
      scones_comp (Yfix (tyD_CBN t)) (curry (eD_CBN body))
  | ne_app G0 t1 t2 Vf Va =>
      scones_comp (Ev (tyD_CBN t1) (tyD_CBN t2))
                  (spair (eD_CBN Vf) (eD_CBN Va))
  (* [ne_let x M K]: K's denotation in context [(x, t1) :: G0] gets
     fed the captured [(env, M-value)] pair.  No monad. *)
  | ne_let G0 _ t1 t2 M0 K =>
      scones_comp (eD_CBN K)
        (spair (scones_id (ctxD_CBN (drop_names G0))) (eD_CBN M0))
  | ne_sample G0 mu0 Hmu0 =>
      @cbn_sample_clause (drop_names G0) mu0 Hmu0
  | ne_real G0 r => @cbn_real_clause (drop_names G0) r
  | ne_score G0 f Hf_meas Hf_ge0 Hf_le1 e =>
      @cbn_score_clause (drop_names G0) f Hf_meas Hf_ge0 Hf_le1 (eD_CBN e)
  | ne_add G0 M0 N0 =>
      @cbn_add_clause (drop_names G0) (eD_CBN M0) (eD_CBN N0)
  | ne_mul G0 M0 N0 =>
      @cbn_mul_clause (drop_names G0) (eD_CBN M0) (eD_CBN N0)
  | ne_true G0 => @cbn_true_clause (drop_names G0)
  | ne_false G0 => @cbn_false_clause (drop_names G0)
  | ne_bernoulli G0 p Hp_ge0 Hp_le1 =>
      @cbn_bernoulli_clause (drop_names G0) p Hp_ge0 Hp_le1
  | ne_bernoulli_f G0 f Hf_meas Hf_ge0 Hf_le1 e =>
      @cbn_bernoulli_f_clause (drop_names G0) f Hf_meas Hf_ge0 Hf_le1
        (eD_CBN e)
  | ne_if G0 t e M N =>
      @cbn_if_clause (drop_names G0) t (eD_CBN e) (eD_CBN M) (eD_CBN N)
  end.

End TermInterpCBN.

Arguments eD_CBN {R Ar R_obj}
  cbn_sample_clause cbn_real_clause cbn_score_clause
  cbn_add_clause cbn_mul_clause
  cbn_true_clause cbn_false_clause cbn_bernoulli_clause
  cbn_bernoulli_f_clause cbn_if_clause
  {G t} M.

(** ** M5 — Soundness of [ne_fix]: the fixpoint equation

    The CBN denotation of [ne_fix s body] satisfies, pointwise on the
    unit ball, the fixpoint equation
    [[
       (eD_CBN (ne_fix s body)) g
         = curry (eD_CBN body) g (eD_CBN (ne_fix s body) g)
    ]]
    — i.e. the recursive function applied at [g] is the body's curry
    image at [g], evaluated at the recursive function itself.  This
    is a direct unfolding of [eD_CBN] at [ne_fix] composed with
    [Yfix_fix].

    NOTE: the equation is stated POINTWISE on the unit ball because
    [Yfix_fix] is pointwise on the unit ball.  Both [sc_fun]
    applications and [sh_fun] applications reduce to plain function
    application of the underlying functions. *)

Section FixSoundness.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Variable cbn_sample_clause :
  forall (G : ppl_ctx Ar)
         (mu : fmeas R (ar_carrier Ar R_obj))
         (Hmu : (cone_norm mu <= 1)%R),
    scones_hom (ctxD_CBN G) (tyD_CBN (tR R_obj)).
Variable cbn_real_clause :
  forall (G : ppl_ctx Ar) (r : R),
    scones_hom (ctxD_CBN G) (tyD_CBN (tR R_obj)).
Variable cbn_score_clause :
  forall (G : ppl_ctx Ar)
         (f : R -> R)
         (Hf_meas : measurable_fun [set: R] f)
         (Hf_ge0 : forall r : R, (0 <= f r)%R)
         (Hf_le1 : forall r : R, (f r <= 1)%R)
         (e : scones_hom (ctxD_CBN G) (tyD_CBN (tR R_obj))),
    scones_hom (ctxD_CBN G) (tyD_CBN (@tunit R Ar)).
Variable cbn_add_clause :
  forall (G : ppl_ctx Ar)
         (M N : scones_hom (ctxD_CBN G) (tyD_CBN (tR R_obj))),
    scones_hom (ctxD_CBN G) (tyD_CBN (tR R_obj)).
Variable cbn_mul_clause :
  forall (G : ppl_ctx Ar)
         (M N : scones_hom (ctxD_CBN G) (tyD_CBN (tR R_obj))),
    scones_hom (ctxD_CBN G) (tyD_CBN (tR R_obj)).
Variable cbn_true_clause :
  forall (G : ppl_ctx Ar),
    scones_hom (ctxD_CBN G) (tyD_CBN (@tbool R Ar)).
Variable cbn_false_clause :
  forall (G : ppl_ctx Ar),
    scones_hom (ctxD_CBN G) (tyD_CBN (@tbool R Ar)).
Variable cbn_bernoulli_clause :
  forall (G : ppl_ctx Ar) (p : R)
         (Hp_ge0 : (0 <= p)%R) (Hp_le1 : (p <= 1)%R),
    scones_hom (ctxD_CBN G) (tyD_CBN (@tbool R Ar)).
Variable cbn_bernoulli_f_clause :
  forall (G : ppl_ctx Ar)
         (f : R -> R)
         (Hf_meas : measurable_fun [set: R] f)
         (Hf_ge0 : forall r : R, (0 <= f r)%R)
         (Hf_le1 : forall r : R, (f r <= 1)%R)
         (e : scones_hom (ctxD_CBN G) (tyD_CBN (tR R_obj))),
    scones_hom (ctxD_CBN G) (tyD_CBN (@tbool R Ar)).
Variable cbn_if_clause :
  forall (G : ppl_ctx Ar) (t : ppl_type Ar)
         (e : scones_hom (ctxD_CBN G) (tyD_CBN (@tbool R Ar)))
         (M N : scones_hom (ctxD_CBN G) (tyD_CBN t)),
    scones_hom (ctxD_CBN G) (tyD_CBN t).

Local Notation eD' :=
  (@eD_CBN R Ar R_obj
     cbn_sample_clause cbn_real_clause cbn_score_clause
     cbn_add_clause cbn_mul_clause
     cbn_true_clause cbn_false_clause cbn_bernoulli_clause
     cbn_bernoulli_f_clause cbn_if_clause).

(** Definitional unfolding of [eD_CBN] at [ne_fix]: the denotation
    is [scones_comp Yfix (curry (eD_CBN body))]. *)
Lemma eD_CBN_fix
    (G : named_ctx Ar) (s : string) (t1 t2 : ppl_type Ar)
    (body : @named_expr R Ar R_obj ((s, tfun t1 t2) :: G) (tfun t1 t2)) :
  eD' (ne_fix s body) =
  scones_comp (Yfix (tyD_CBN (tfun t1 t2))) (curry (eD' body)).
Proof. by []. Qed.

(** The headline soundness reduction: the [ne_fix] denotation is a
    fixed point of the body's curry, in the [Yfix_fix] sense
    (pointwise on the unit ball of the underlying context). *)
Lemma eD_CBN_fix_E
    (G : named_ctx Ar) (s : string) (t1 t2 : ppl_type Ar)
    (body : @named_expr R Ar R_obj ((s, tfun t1 t2) :: G) (tfun t1 t2))
    (g : ctxD_CBN (drop_names G))
    (Hg : (cone_norm g <= 1)%R) :
  sh_fun (sc_fun (curry (eD' body)) g)
         (sc_fun (eD' (ne_fix s body)) g) =
  sc_fun (eD' (ne_fix s body)) g.
Proof.
rewrite eD_CBN_fix scomp_ball//.
exact: Yfix_fix (sc_image_ball (curry (eD' body)) Hg).
Qed.

(** *** Mutual recursion — [ne_fix_mr] soundness reductions

    The CBN side has NO honest-scope limitation for [ne_fix_mr] (the
    product-of-functions case): [Yfix] of [stable/fixpoint.v]
    works at ANY cone, so the same reduction lemmas as [ne_fix] go
    through unchanged for any body type [t] (in particular [t =
    tprod (tfun A1 B1) (tfun A2 B2)], the mutual-recursion shape). *)

(** Definitional unfolding of [eD_CBN] at [ne_fix_mr]: the denotation
    is [scones_comp (Yfix (tyD_CBN t)) (curry (eD_CBN body))], for any
    body type [t]. *)
Lemma eD_CBN_fix_mr
    (G : named_ctx Ar) (s : string) (t : ppl_type Ar)
    (Hfree : is_free_coalg_type t)
    (body : @named_expr R Ar R_obj ((s, t) :: G) t) :
  eD' (ne_fix_mr s t Hfree body) =
  scones_comp (Yfix (tyD_CBN t)) (curry (eD' body)).
Proof. by []. Qed.

(** The headline soundness reduction for [ne_fix_mr]: the denotation is
    a fixed point of the body's curry, pointwise on the unit ball.
    Identical statement to [eD_CBN_fix_E] modulo replacing [tfun t1 t2]
    by an arbitrary [t]. *)
Lemma eD_CBN_fix_mr_E
    (G : named_ctx Ar) (s : string) (t : ppl_type Ar)
    (Hfree : is_free_coalg_type t)
    (body : @named_expr R Ar R_obj ((s, t) :: G) t)
    (g : ctxD_CBN (drop_names G))
    (Hg : (cone_norm g <= 1)%R) :
  sh_fun (sc_fun (curry (eD' body)) g)
         (sc_fun (eD' (ne_fix_mr s t Hfree body)) g) =
  sc_fun (eD' (ne_fix_mr s t Hfree body)) g.
Proof.
rewrite eD_CBN_fix_mr scomp_ball//.
exact: Yfix_fix (sc_image_ball (curry (eD' body)) Hg).
Qed.

End FixSoundness.

Arguments eD_CBN_fix {R Ar R_obj
  cbn_sample_clause cbn_real_clause cbn_score_clause
  cbn_add_clause cbn_mul_clause
  cbn_true_clause cbn_false_clause cbn_bernoulli_clause
  cbn_bernoulli_f_clause cbn_if_clause}
  G s t1 t2 body.
Arguments eD_CBN_fix_E {R Ar R_obj
  cbn_sample_clause cbn_real_clause cbn_score_clause
  cbn_add_clause cbn_mul_clause
  cbn_true_clause cbn_false_clause cbn_bernoulli_clause
  cbn_bernoulli_f_clause cbn_if_clause}
  G s t1 t2 body g Hg.
Arguments eD_CBN_fix_mr {R Ar R_obj
  cbn_sample_clause cbn_real_clause cbn_score_clause
  cbn_add_clause cbn_mul_clause
  cbn_true_clause cbn_false_clause cbn_bernoulli_clause
  cbn_bernoulli_f_clause cbn_if_clause}
  G s t Hfree body.
Arguments eD_CBN_fix_mr_E {R Ar R_obj
  cbn_sample_clause cbn_real_clause cbn_score_clause
  cbn_add_clause cbn_mul_clause
  cbn_true_clause cbn_false_clause cbn_bernoulli_clause
  cbn_bernoulli_f_clause cbn_if_clause}
  G s t Hfree body g Hg.

(** ** Smoke test — [ex_random_constant] CBN denotation

    The CBN denotation of [theories/programs/examples.v]'s
    [ex_random_constant mu Hmu = [ let "c" := sample mu in
    λx. #"c" ]] structurally reduces (definitionally, modulo the
    [ne_sample] stub) to a recognisable composite:
    [[
       eD_CBN (ex_random_constant mu Hmu)
         = scones_comp (curry (eD_CBN lam_body))
                       (spair (scones_id _) (cbn_sample_clause _ mu Hmu))
    ]]
    The reduction is just an [eD_CBN] unfold at [ne_let] then at
    [ne_lam], with the [ne_sample] denotation kept abstract as the
    stub [cbn_sample_clause].  M3 will refine the stub. *)

Section SmokeTest.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Variable cbn_sample_clause :
  forall (G : ppl_ctx Ar)
         (mu : fmeas R (ar_carrier Ar R_obj))
         (Hmu : (cone_norm mu <= 1)%R),
    scones_hom (ctxD_CBN G) (tyD_CBN (tR R_obj)).
Variable cbn_real_clause :
  forall (G : ppl_ctx Ar) (r : R),
    scones_hom (ctxD_CBN G) (tyD_CBN (tR R_obj)).
Variable cbn_score_clause :
  forall (G : ppl_ctx Ar)
         (f : R -> R)
         (Hf_meas : measurable_fun [set: R] f)
         (Hf_ge0 : forall r : R, (0 <= f r)%R)
         (Hf_le1 : forall r : R, (f r <= 1)%R)
         (e : scones_hom (ctxD_CBN G) (tyD_CBN (tR R_obj))),
    scones_hom (ctxD_CBN G) (tyD_CBN (@tunit R Ar)).
Variable cbn_add_clause :
  forall (G : ppl_ctx Ar)
         (M N : scones_hom (ctxD_CBN G) (tyD_CBN (tR R_obj))),
    scones_hom (ctxD_CBN G) (tyD_CBN (tR R_obj)).
Variable cbn_mul_clause :
  forall (G : ppl_ctx Ar)
         (M N : scones_hom (ctxD_CBN G) (tyD_CBN (tR R_obj))),
    scones_hom (ctxD_CBN G) (tyD_CBN (tR R_obj)).
Variable cbn_true_clause :
  forall (G : ppl_ctx Ar),
    scones_hom (ctxD_CBN G) (tyD_CBN (@tbool R Ar)).
Variable cbn_false_clause :
  forall (G : ppl_ctx Ar),
    scones_hom (ctxD_CBN G) (tyD_CBN (@tbool R Ar)).
Variable cbn_bernoulli_clause :
  forall (G : ppl_ctx Ar) (p : R)
         (Hp_ge0 : (0 <= p)%R) (Hp_le1 : (p <= 1)%R),
    scones_hom (ctxD_CBN G) (tyD_CBN (@tbool R Ar)).
Variable cbn_bernoulli_f_clause :
  forall (G : ppl_ctx Ar)
         (f : R -> R)
         (Hf_meas : measurable_fun [set: R] f)
         (Hf_ge0 : forall r : R, (0 <= f r)%R)
         (Hf_le1 : forall r : R, (f r <= 1)%R)
         (e : scones_hom (ctxD_CBN G) (tyD_CBN (tR R_obj))),
    scones_hom (ctxD_CBN G) (tyD_CBN (@tbool R Ar)).
Variable cbn_if_clause :
  forall (G : ppl_ctx Ar) (t : ppl_type Ar)
         (e : scones_hom (ctxD_CBN G) (tyD_CBN (@tbool R Ar)))
         (M N : scones_hom (ctxD_CBN G) (tyD_CBN t)),
    scones_hom (ctxD_CBN G) (tyD_CBN t).

Variable mu : fmeas R (ar_carrier Ar R_obj).
Hypothesis Hmu : (cone_norm mu <= 1)%R.

Local Notation tR' := (tR R_obj).
Local Notation eD' :=
  (@eD_CBN R Ar R_obj
     cbn_sample_clause cbn_real_clause cbn_score_clause
     cbn_add_clause cbn_mul_clause
     cbn_true_clause cbn_false_clause cbn_bernoulli_clause
     cbn_bernoulli_f_clause cbn_if_clause).

(** Structural reduction lemma — the CBN denotation of
    [ex_random_constant] unfolds to a [scones_comp] of the lambda
    body's curry and the [spair (id, sample-stub)] pairing. *)
Lemma ex_random_constant_CBN_denot_E :
  eD' (ex_random_constant mu Hmu) =
  scones_comp (eD' (ex_rc_lam (R_obj := R_obj)))
              (spair (scones_id (ctxD_CBN (drop_names (Ar:=Ar) nil)))
                     (@cbn_sample_clause nil mu Hmu)).
Proof. by []. Qed.

End SmokeTest.

(** ** Notes for downstream waves (M3, M4)

    - All stub hypotheses appear in [eD_CBN]'s signature after
      [Section TermInterpCBN] closes.  Wave 2 (M3) will:
      - replace [cbn_sample_clause] / [cbn_real_clause] with concrete
        constant SCones morphisms at the supplied measure / Dirac;
      - replace [cbn_score_clause] with a [Stop_mor]-or-equivalent
        unique map (the codomain [tyD_CBN tunit = Stop Ar] forces
        uniqueness up to [Stop_eq]);
      - replace [cbn_add_clause] / [cbn_mul_clause] with the CBN
        reading of pointwise arithmetic (likely via [fmeas_lax] of
        [theories/homs/fmeas_lax.v], analogous to the EM/CBV [add_lift]
        / [mul_lift] of [ppl.v]).
    - Wave 3 (M4) will replace the boolean stubs by the CBN reading
      of [bool_cone_car] morphisms; expect to re-use much of the
      [bool_case_hom.v] machinery, but lifted to SCones (no
      bang/!-comonad in CBN).
    - The headline lemma [eD_CBN_fix_E] is INDEPENDENT of M3/M4
      stubs (it only uses the fix clause); future waves should NOT
      rewrite it. *)
