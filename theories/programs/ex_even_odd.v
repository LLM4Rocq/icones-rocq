(**md**************************************************************************)
(** * [ex_even_odd] — mutual recursion at a product-of-functions type

    The construction relies on the fact that the CBV value-fixpoint at
    function types extends to body types whose interpretation is a free
    [!]-coalgebra; this class includes products of function types, which
    is exactly what enables MUTUAL RECURSION.

    The [ne_fix_mr] constructor of [theories/programs/ppl.v]
    lets one bind a recursive name [s] of any
    [is_free_coalg_type]-true type [t], notably
    [t = tprod (tfun A1 B1) (tfun A2 B2)] — a PAIR of functions.  Each
    component can then refer to the other via [fst #"s"] / [snd #"s"],
    realising mutual recursion.

    *** What this file delivers, AXIOM-FREE (modulo the 3 boolp axioms).

    [[
       ex_even_odd_pair :=
         fix_mr "p" ::: tprod (tfun tR tR) (tfun tR tR) { erefl } in
           ( λ n. snd #"p" @ #"n",       ("even"-like component)
             λ n. fst #"p" @ #"n" )       ("odd"-like component)
    ]]

    Two mutually recursive functions of type [tR → tR] bound under a
    single product-typed recursive name; each immediately delegates to
    the other.  Operationally this diverges everywhere (the
    [Yfix_fun_T]-via-collapse honest-scope caveat applies in CBV; CBN
    diverges via the standard Kleene argument).  Syntactically it is
    EXACTLY the mutual-recursion shape: a single fixed point at the
    product, with the two recursive calls cross-wired through the
    [fst]/[snd] projections.

    The deliverables:

    - [ex_even_odd_pair] : the surface program ([named_expr nil _]);
    - [ex_even] / [ex_odd] : the [fst] / [snd] projections;
    - [ex_even_odd_pair_denot_CBN] : the CBN denotation (sound mutual
      recursion via SCones' [Yfix] at the product cone, with full
      [eD_CBN_fix_mr_E] soundness reduction available);
    - [ex_even_odd_pair_denot] : the CBV denotation (typechecks, with
      the documented honest-scope limitation: [Yfix_mr_pack] returns a
      constant-zero placeholder at product types);
    - [ex_even_odd_pair_denot_E] : the structural CBV reduction lemma
      exposing the [Yfix_mr_pack]-at-tprod placeholder;
    - [ex_even_odd_pair_denot_CBN_E] : the structural CBN reduction
      lemma — the analogue of [eD_CBN_fix_E] for [ne_fix_mr], pointwise
      on the unit ball.

    HEADLINE: the surface program type-checks and both CBV and CBN
    denotations are well-defined.  CBN soundness for mutual recursion
    is FULLY SOUND.  CBV soundness for mutual recursion is HONEST-SCOPE
    deferred (same status as [Yfix_fun_T] for [ne_fix]).

    Author: Guillaume Baudart <guillaume.baudart@inria.fr>. *)

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

From Stdlib Require Import Strings.String.

Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_cat.
Require Import Icones.stable.scones_cat.
Require Import Icones.stable.scones_ccc.
Require Import Icones.stable.stablehom.
Require Import Icones.stable.fixpoint.
Require Import Icones.homs.linhom.
Require Import Icones.homs.bang.
Require Import Icones.homs.coalgebra.
Require Import Icones.homs.em_cat.
Require Import Icones.homs.em_cartesian.
Require Import Icones.programs.infra.em_fix.
Require Import Icones.programs.infra.cbv_adjunction.
Require Import Icones.programs.cbv.
Require Import Icones.programs.ppl.
Require Import Icones.programs.ppl_cbn.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** The mutually-recursive surface program *)

Section ExEvenOdd.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).

Local Notation tR' := (tR R_obj).
Local Notation pair_ty := (tprod (tfun tR' tR') (tfun tR' tR')).

(** Two pre-named lambdas, in the context extended with the rec name
    [p : pair_ty].  The "even"-like component delegates to [snd p];
    the "odd"-like component delegates to [fst p].

    These are pulled OUT of the surface [(M, N)] pair because the
    [ppl_named] pair notation [(M, N)] requires each component at
    custom level 60, and the lambda notation [\ x ::: A => ...] sits
    at level 70 > 60 — so an inline lambda cannot syntactically be a
    pair component.  Pulling the lambdas out via [Definition] (and
    splicing them back via the [{ ... }] escape-to-constr) is the
    surface-syntax workaround. *)
Definition ex_even_odd_lam_a :
    @named_expr R Ar R_obj (("p"%string, pair_ty) :: nil)
                            (tfun tR' tR') :=
  [ \ "n" ::: tR' => snd # "p" @ # "n" ].

Definition ex_even_odd_lam_b :
    @named_expr R Ar R_obj (("p"%string, pair_ty) :: nil)
                            (tfun tR' tR') :=
  [ \ "n" ::: tR' => fst # "p" @ # "n" ].

(** The mutually-recursive function PAIR.  Bound under a single
    recursive name [p] of type [tprod (tfun tR tR) (tfun tR tR)] (a
    free-coalgebra type, witnessed by [erefl : is_free_coalg_type _ =
    true]).  The two components delegate to each other via the [fst] /
    [snd] projections of the rec-bound product. *)
Definition ex_even_odd_pair :
    @named_expr R Ar R_obj nil pair_ty :=
  [ fix_mr "p" as pair_ty by erefl
       in ({ex_even_odd_lam_a}, {ex_even_odd_lam_b}) ].

(** The first component — the "even" half. *)
Definition ex_even :
    @named_expr R Ar R_obj nil (tfun tR' tR') :=
  [ fst {ex_even_odd_pair} ].

(** The second component — the "odd" half. *)
Definition ex_odd :
    @named_expr R Ar R_obj nil (tfun tR' tR') :=
  [ snd {ex_even_odd_pair} ].

(** The body of the [fix_mr] — useful for stating the [_denot_E]
    lemmas.  In the extended context [("p", pair_ty) :: nil], the body
    has the same type [pair_ty] as the rec-bound name. *)
Definition ex_even_odd_body :
    @named_expr R Ar R_obj
      (("p"%string, pair_ty) :: nil)
      pair_ty :=
  [ ({ex_even_odd_lam_a}, {ex_even_odd_lam_b}) ].

End ExEvenOdd.

Arguments ex_even_odd_pair {R Ar R_obj}.
Arguments ex_even {R Ar R_obj}.
Arguments ex_odd {R Ar R_obj}.
Arguments ex_even_odd_body {R Ar R_obj}.

(** ** CBV denotation — honest scope at product types

    The CBV denotation of [ex_even_odd_pair] is well-defined and
    typechecks, but per the [Yfix_mr_pack] honest-scope limitation at
    [tprod] (see [theories/programs/ppl.v]), it reduces to a
    constant-zero Kleisli arrow at the product cone — NOT a real
    fixpoint.  The structural reduction lemma below exposes exactly
    this. *)

Section ExEvenOddCBV.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Local Notation tR' := (tR R_obj).
Local Notation pair_ty := (tprod (tfun tR' tR') (tfun tR' tR')).

(** The CBV denotation of the pair as a Kleisli arrow [⟦[]⟧ ⇝ ⟦pair_ty⟧]. *)
Definition ex_even_odd_pair_denot :
    coalg_hom (ctxD (drop_names nil)) (Tobj (tyD pair_ty)) :=
  @eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas
      nil pair_ty (@ex_even_odd_pair R Ar R_obj).

(** Structural CBV reduction — the [_denot_E] HEADLINE for the
    mutually-recursive pair.

    The [eD]-clause for [ne_fix_mr] is [Yfix_mr_pack Hfree (eD body)];
    at the product-of-functions case (the [tprod] arm of
    [Yfix_mr_pack]) this reduces to the documented constant-zero
    placeholder [const_kleisli precone_zero ...].

    This lemma is the syntactic shape one would expect for a mutual
    recursion — the constant-zero is the honest-scope CBV stub.  The
    CBN version (below) has the full [Yfix]-based reduction. *)
Lemma ex_even_odd_pair_denot_E :
  ex_even_odd_pair_denot =
  @const_kleisli R Ar (ctxD (drop_names nil))
    (coalg_obj (EM_prod (tyD (tfun tR' tR')) (tyD (tfun tR' tR'))))
    precone_zero (precone_zero_norm_le1 _).
Proof.
rewrite /ex_even_odd_pair_denot /ex_even_odd_pair.
(* unfold [eD] at [ne_fix_mr] then [Yfix_mr_pack] at [tprod]. *)
by [].
Qed.

End ExEvenOddCBV.

Arguments ex_even_odd_pair_denot {R Ar R_obj}
  R_carrier_eq R_carrier_meas R_to_carrier_meas.
Arguments ex_even_odd_pair_denot_E {R Ar R_obj}
  R_carrier_eq R_carrier_meas R_to_carrier_meas.

(** ** CBN denotation — SOUND mutual recursion

    The CBN side of [ne_fix_mr] is FULLY SOUND for any
    [is_free_coalg_type]-true type [t], including [tprod (tfun A1 B1)
    (tfun A2 B2)].  This is because SCones' [Yfix] of
    [theories/stable/fixpoint.v] is the genuine least fixed point at
    ANY [ICone.type Ar], and the construction [scones_comp (Yfix _)
    (curry _)] supplies the body's environment-dependent recursive
    self.

    This makes [ex_even_odd_pair]'s CBN denotation the FULL,
    correctly-mutually-recursive product fixpoint — modulo the standard
    Yfix-pointwise-on-the-unit-ball reduction lemma. *)

Section ExEvenOddCBN.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).

(** Hypothesis-abstracted CBN clauses, as in [ppl_cbn.v]. *)
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
Variable cbn_if_clause :
  forall (G : ppl_ctx Ar) (t : ppl_type Ar)
         (e : scones_hom (ctxD_CBN G) (tyD_CBN (@tbool R Ar)))
         (M N : scones_hom (ctxD_CBN G) (tyD_CBN t)),
    scones_hom (ctxD_CBN G) (tyD_CBN t).

Local Notation tR' := (tR R_obj).
Local Notation pair_ty := (tprod (tfun tR' tR') (tfun tR' tR')).
Local Notation eD_CBN' :=
  (@eD_CBN R Ar R_obj
     cbn_sample_clause cbn_real_clause cbn_score_clause
     cbn_add_clause cbn_mul_clause
     cbn_true_clause cbn_false_clause cbn_bernoulli_clause
     cbn_if_clause).

(** The CBN denotation of the mutually-recursive pair. *)
Definition ex_even_odd_pair_denot_CBN :
    scones_hom (ctxD_CBN (drop_names nil)) (tyD_CBN pair_ty) :=
  eD_CBN' (@ex_even_odd_pair R Ar R_obj).

(** Structural CBN reduction — exposes the [Yfix]-at-product shape.

    Unfolds [eD_CBN] at the [ne_fix_mr] clause: the denotation is
    [scones_comp (Yfix (tyD_CBN pair_ty)) (curry (eD_CBN body))], with
    [tyD_CBN pair_ty = sprod (stablehom (tyD_CBN tR) (tyD_CBN tR))
                             (stablehom (tyD_CBN tR) (tyD_CBN tR))]. *)
Lemma ex_even_odd_pair_denot_CBN_E :
  ex_even_odd_pair_denot_CBN =
  scones_comp (Yfix (tyD_CBN pair_ty))
              (curry (eD_CBN' (@ex_even_odd_body R Ar R_obj))).
Proof. by []. Qed.

(** Soundness — the [ne_fix_mr] denotation is a fixed point of the
    body's curry, pointwise on the unit ball.

    The Yfix-soundness identity transports unchanged from
    [eD_CBN_fix_mr_E]: at [g] in the unit ball, applying the body's
    curry at [g] to the [ex_even_odd_pair] denotation at [g] returns
    the [ex_even_odd_pair] denotation at [g] itself.  This is GENUINE
    mutual recursion — the body's curry has both projection slots [fst
    #"p"] / [snd #"p"] simultaneously available through the rec-bound
    name [p]. *)
Lemma ex_even_odd_pair_denot_CBN_fix
    (g : ctxD_CBN (drop_names (Ar := Ar) nil))
    (Hg : (cone_norm g <= 1)%R) :
  sh_fun (sc_fun (curry (eD_CBN' (@ex_even_odd_body R Ar R_obj))) g)
         (sc_fun ex_even_odd_pair_denot_CBN g) =
  sc_fun ex_even_odd_pair_denot_CBN g.
Proof.
rewrite /ex_even_odd_pair_denot_CBN /ex_even_odd_pair.
exact: (@eD_CBN_fix_mr_E R Ar R_obj
          cbn_sample_clause cbn_real_clause cbn_score_clause
          cbn_add_clause cbn_mul_clause
          cbn_true_clause cbn_false_clause cbn_bernoulli_clause
          cbn_if_clause
          nil "p" pair_ty erefl
          (@ex_even_odd_body R Ar R_obj) g Hg).
Qed.

End ExEvenOddCBN.

Arguments ex_even_odd_pair_denot_CBN {R Ar R_obj}
  cbn_sample_clause cbn_real_clause cbn_score_clause
  cbn_add_clause cbn_mul_clause
  cbn_true_clause cbn_false_clause cbn_bernoulli_clause
  cbn_if_clause.
Arguments ex_even_odd_pair_denot_CBN_E {R Ar R_obj}
  cbn_sample_clause cbn_real_clause cbn_score_clause
  cbn_add_clause cbn_mul_clause
  cbn_true_clause cbn_false_clause cbn_bernoulli_clause
  cbn_if_clause.
Arguments ex_even_odd_pair_denot_CBN_fix {R Ar R_obj
  cbn_sample_clause cbn_real_clause cbn_score_clause
  cbn_add_clause cbn_mul_clause
  cbn_true_clause cbn_false_clause cbn_bernoulli_clause
  cbn_if_clause} g Hg.
