(**md**************************************************************************)
(** * A higher-order probabilistic PPL, interpreted in [ICones_CBV] — PPL

    This file extends the first-order CBV demo of [theories/homs/cbv.v]
    with HIGHER-ORDER function-type INTRODUCTION (lambda abstraction)
    and ports the canonical higher-order example from mathcomp-qbs's
    [ppl_qbs.v] / [showcase/ppl_examples.v]:

    [[
        random_constant ≜ do c <- sample (μ : X); return (λx. c)
    ]]

    a distribution over the function space [X → X], which is the
    paradigmatic *higher-order* example the QBS development emphasises
    (distributions on function spaces are impossible in classical
    measure-theoretic / kernel-based semantics; QBS resolves this via
    cartesian closure, our cones model via the LNL decomposition).

    Mathcomp-qbs design summary (in [theories/ppl_qbs.v]):
    - Types: [ppl_real | ppl_bool | ppl_unit | ppl_prod | ppl_sum |
      ppl_fun | ppl_prob] — function type is first-class;
    - Expressions are intrinsically typed with de Bruijn indices,
      including [e_lam], [e_app], [e_ret], [e_bind], [e_sample_*];
    - Denotational semantics uses the QBS exponential [expQ X Y] for
      [ppl_fun] and the probability monad [monadP] for [ppl_prob];
    - The killer example is [random_linear] (a distribution over
      [linear functions R → R]); the simplest higher-order PPL-syntax
      variant is [ex_random_constant_ppl] in
      [showcase/ppl_examples.v].

    ** Why this matters **

    Mathcomp-qbs explicitly says: "These programs have no denotation
    [in ordinary measure-theoretic semantics]: the function space
    [R → R] cannot be given a sigma-algebra that makes both
    evaluation and currying measurable.  QBS resolves this via the
    cartesian-closed category of quasi-Borel spaces." (showcase/
    ppl_examples.v header).

    Our cones model resolves it differently — via the linear/non-
    linear decomposition of Girard: function types are interpreted
    LINEARLY out of the duplicable copy of the argument.  This file
    demonstrates that the higher-order example port goes through,
    axiom-free, in the LNL discipline, while the existing first-order
    [cbv.v] continues to be the demo of the value-CCC-free fragment.

    ** The interpretation route — Girard/LNL [A → B = !A ⊸ B] **

    Our value category is the FULL Eilenberg–Moore category [EM(!)]
    ([em_cartesian.v]); it is cartesian (Cor 20, unconditional) but is
    NOT known to be cartesian-closed.  Higher-order CBV is recovered
    via the standard linear-non-linear decomposition: a CBV arrow
    [A → B] denotes a *linear* arrow [!A ⊸ B] (out of the duplicable
    copy of [A]).  This is interpretable axiom-free in our model:
    - the linear function space [!A ⊸ B] is [linhom_car Ar (Bang Ar A) B],
      an [iconeType Ar] of the underlying [ICones];
    - the function-type denotation is the cofree coalgebra
      [bang_cofree (linhom_car Ar (Bang Ar ⟦A⟧.obj) ⟦B⟧.obj)] of
      EM(!), so function VALUES live in the value category;
    - lambda abstraction uses the SMCC currying [tensor_curry]
      ([tensor_construct.v]) of the underlying [ICones], composed
      with [adj_psi] of the cofree adjunction to land back in EM(!).

    ** The fragment interpreted (stated honestly) **

    Compared to mathcomp-qbs:
    - [ppl_real], [ppl_prod], [ppl_unit] map to our [tbase'] / [tprod']
      / [tunit'] (as in [cbv.v]);
    - [ppl_fun] adds the higher-order arrow [tfun A B] = [!A ⊸ B] at
      the value type level — but we provide only the INTRODUCTION rule
      [v_lam], NOT the elimination [v_app]; see "Honest scope" below.
    - [ppl_bool] / [ppl_sum] are NOT supported (no boolean / coproduct
      objects in our setup); they are orthogonal to the higher-order
      content and not exercised by the example;
    - [ppl_prob] is identified with the CBV computation monad [T] of
      [cbv.v] (so [P τ] is the result type of a [c_ret'] / [c_let'] /
      [c_sample'] computation, not a separate value type — same shape
      as a Moggi-style CBV).  Probabilistic content lives in [sample]
      (the Theorem-9.7 coalgebra structure).

    The HIGHER-ORDER example we port is the simpler
    [ex_random_constant_ppl] of the showcase:
    [[
        ex_random_constant ≜
          c_let (c_sample v_var) (c_ret (v_lam (v_fst v_var)))
    ]]
    in context [tbase' X ⊢ — : T (tfun (tbase' X) (tbase' X))]: draw a
    sample [c], then return the constant function [λ x. c].  Its
    denotation is a coalgebra morphism
    [FMeas X → T (bang_cofree (!FMeas X ⊸ FMeas X))].

    ** Honest scope **

    We deliver:
    - syntax / type interpretation / term interpretation, all
      axiom-free and structurally total;
    - the [let]-of-[ret] law ([cpD'_letret]), the [sample]-as-[ret]
      identity ([cpD'_sample_ret]) at the PPL level — identical to
      the [cbv.v] proofs since the computation grammar is unchanged;
    - the higher-order [v_lam] unfolding via [adj_phi_lam_coalg] —
      applying [adj_phi] to a lambda value reads as [tensor_curry] of
      the body composed with [id ⊗ der_A] (the LNL underlying linear
      hom of the lambda);
    - the higher-order EXAMPLE [ex_random_constant_denot_E]: its
      denotation reduces, via [cpD'_sample_ret] + [cpD'_letret] +
      [vlD'_varE], to the value of the lambda — an axiom-free,
      compositional witness that the [v_lam] machinery is coherent
      with the existing computation laws.

    We do NOT include [v_app] in the syntax.  Reason: applying a
    function value gives an [icones_hom] [app_under := eval ∘ (φ ⊗ ψ)
    ∘ d_G] in the underlying [ICones]; promoting this to a coalgebra
    morphism in [EM(!)] would require proving that the SMCC evaluation
    [eval : (!A ⊸ B) ⊗ !A → B] is itself a coalgebra morphism between
    the appropriate EM-products and the target coalgebra structure on
    [B], which is true (it is the counit of the *monoidal* cofree
    adjunction, by Melliès §6.3 / Bénabou) but is *not* in our current
    file inventory.  Stating it would not increase axiom load — there
    are no project axioms in the staged tier — but it WOULD be a
    significant proof obligation (a new file of monoidal-adjunction
    coherence).  For the example we port, [v_app] is not needed: the
    lambda is the OUTPUT of the program, not consumed by a subsequent
    application.  We record the underlying [lam_under] combinator
    (the SMCC-currying of the body) so that a future [v_app] addition
    can reuse it.  See also [APP_NOTE] below for the precise statement
    of the coalgebra-morphism obligation that would close the gap. *)

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
Require Import Icones.homs.cbv.

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

(** ** The PPL syntax — types extended with [tfun]

    A higher-order extension of [cbv.v]'s grammar.  The only new type
    constructor is [tfun A B] (the LNL arrow [!A ⊸ B]); products
    [tprod'], unit [tunit'] and the base types [tbase' X] are exactly
    as in [cbv.v].  Values gain a lambda introduction [v_lam].  We do
    NOT add an application constructor — see "Honest scope" in the
    header.  This is the higher-order INTRODUCTION-only fragment, which
    is exactly what the ported QBS example needs. *)
Section Syntax.
Variable (R : realType) (Ar : MeasSubcat R).

Inductive ty' : Type :=
  | tunit'
  | tbase' (X : ar_obj Ar)
  | tprod' (s t : ty')
  | tfun (A B : ty').

(** Values [vl' Γ τ] : a value of type [τ] with one free variable of
    type [Γ].  Compared to [cbv.v]'s [vl], we add [v_lam] (which binds
    a fresh variable of type [A], turning the body's context into
    [tprod' Γ A]). *)
Inductive vl' (G : ty') : ty' -> Type :=
  | v_var' : vl' G G
  | v_unit' : vl' G tunit'
  | v_pair' (s t : ty') :
      vl' G s -> vl' G t -> vl' G (tprod' s t)
  | v_fst' (s t : ty') : vl' G (tprod' s t) -> vl' G s
  | v_snd' (s t : ty') : vl' G (tprod' s t) -> vl' G t
  | v_lam (A B : ty') :
      vl' (tprod' G A) B -> vl' G (tfun A B).

(** Computations [cp' Γ τ] : same shape as [cbv.v]'s [cp]. *)
Inductive cp' (G : ty') : ty' -> Type :=
  | c_ret' (t : ty') : vl' G t -> cp' G t
  | c_let' (H t : ty') : cp' G H -> cp' H t -> cp' G t
  | c_sample' (X : ar_obj Ar) :
      vl' G (tbase' X) -> cp' G (tbase' X).

End Syntax.

Arguments ty' {R} Ar.
Arguments tunit' {R Ar}.
Arguments tbase' {R Ar} X.
Arguments tprod' {R Ar} s t.
Arguments tfun {R Ar} A B.
Arguments vl' {R Ar} G t.
Arguments v_var' {R Ar G}.
Arguments v_unit' {R Ar G}.
Arguments v_pair' {R Ar G s t} V W.
Arguments v_fst' {R Ar G s t} V.
Arguments v_snd' {R Ar G s t} V.
Arguments v_lam {R Ar G A B} V.
Arguments cp' {R Ar} G t.
Arguments c_ret' {R Ar G t} V.
Arguments c_let' {R Ar G H t} M N.
Arguments c_sample' {R Ar G X} V.

(** ** Type interpretation [tyD']

    Every type denotes a coalgebra of [EM(!)].  The extra clause for
    [tfun A B]:
      [⟦tfun A B⟧ = bang_cofree (linhom_car Ar (Bang Ar ⟦A⟧.obj) ⟦B⟧.obj)]
    i.e. the cofree coalgebra of the *linear* function space
    [!⟦A⟧.obj ⊸ ⟦B⟧.obj].  Underlying [ICones] object: the linear
    function space; coalgebra structure: cofree (the comultiplication
    [dig]).  This is the Girard/LNL [A → B = !A ⊸ B] decomposition. *)
Section TypeInterp.
Variables (R : realType) (Ar : MeasSubcat R).

Fixpoint tyD' (t : ty' Ar) : Coalgebra Ar :=
  match t with
  | tunit' => EM_term
  | tbase' X => FMeas_coalgebra X
  | tprod' s1 s2 => EM_prod (tyD' s1) (tyD' s2)
  | tfun A B => bang_cofree (linhom_car Ar (Bang Ar (coalg_obj (tyD' A)))
                                        (coalg_obj (tyD' B)))
  end.

End TypeInterp.

Arguments tyD' {R Ar} t.

(** ** Closure assembly for [v_lam] — the Girard/LNL underlying map

    Helper combinator used by [vlD'] below: keep [vlD'] structurally
    recursive while making the LNL interpretation self-documenting. *)
Section Lam.
Variables (R : realType) (Ar : MeasSubcat R).

(** Underlying linear hom of a lambda — Girard/LNL.

    Given the body's coalg-hom interpretation
    [VB : coalg_hom (EM_prod G A) B], we construct an
    [icones_hom (coalg_obj G) (!A.obj ⊸ B.obj)]:
    - the underlying [ch_mor VB] is an icones_hom
      [coalg_obj G ⊗ coalg_obj A → coalg_obj B];
    - precompose with [id ⊗ der_A] to lift the [coalg_obj A] factor
      to [Bang Ar (coalg_obj A)];
    - then [tensor_curry] gives the curried form. *)
Definition lam_under (G A B : Coalgebra Ar)
    (VB : coalg_hom (EM_prod G A) B) :
    icones_hom Ar (coalg_obj G)
      (linhom_car Ar (Bang Ar (coalg_obj A)) (coalg_obj B)) :=
  tensor_curry
    (icones_comp (ch_mor VB)
       (tensor_mor (icones_id Ar (coalg_obj G)) (der (coalg_obj A)))).

(** Bundled as a coalgebra morphism into the cofree
    [!̃(!A.obj ⊸ B.obj)]: this is the value-category form of [lam_under]
    (lambda is a VALUE, hence a coalg-hom).  Uses [adj_psi] of the
    cofree adjunction [U ⊣ !̃]. *)
Definition lam_coalg (G A B : Coalgebra Ar)
    (VB : coalg_hom (EM_prod G A) B) :
    coalg_hom G (bang_cofree (linhom_car Ar (Bang Ar (coalg_obj A))
                                         (coalg_obj B))) :=
  adj_psi (lam_under VB).

End Lam.

Arguments lam_under {R Ar G A B} VB.
Arguments lam_coalg {R Ar G A B} VB.

(** ** Term interpretation [vlD'] / [cpD']

    Values denote coalgebra morphisms; computations denote Kleisli
    arrows of the CBV monad [T = !̃ ∘ U] of [cbv.v]. *)
Section TermInterp.
Variables (R : realType) (Ar : MeasSubcat R).

Fixpoint vlD' (G : ty' Ar) (t : ty' Ar) (V : vl' G t) {struct V} :
    coalg_hom (tyD' G) (tyD' t) :=
  match V in vl' _ t0 return coalg_hom (tyD' G) (tyD' t0) with
  | v_var' => coalg_id (tyD' G)
  | v_unit' => em_term_mor (tyD' G)
  | v_pair' s t W1 W2 => em_pair (vlD' W1) (vlD' W2)
  | v_fst' s t W => coalg_comp (em_proj1 (tyD' s) (tyD' t)) (vlD' W)
  | v_snd' s t W => coalg_comp (em_proj2 (tyD' s) (tyD' t)) (vlD' W)
  | v_lam A B body => lam_coalg (vlD' body)
  end.

(** Computation denotation [cpD'] — identical shape to [cbv.v]. *)
Fixpoint cpD' (G : ty' Ar) (t : ty' Ar) (M : cp' G t) {struct M} :
    coalg_hom (tyD' G) (Tobj (tyD' t)) :=
  match M in cp' _ t0 return coalg_hom (tyD' G) (Tobj (tyD' t0)) with
  | c_ret' t0 V => coalg_comp (tunit_eta (tyD' t0)) (vlD' V)
  | c_let' H t0 N1 N2 => kcomp (cpD' N2) (cpD' N1)
  | c_sample' X V => coalg_comp (tunit_eta (tyD' (tbase' X))) (vlD' V)
  end.

End TermInterp.

Arguments vlD' {R Ar G t} V.
Arguments cpD' {R Ar G t} M.

(** ** Soundness — the higher-order rule and the example *)
Section Soundness.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

(** Definitional unfoldings of [vlD'] / [cpD']. *)
Lemma vlD'_varE (G : ty' Ar) :
  vlD' (v_var' (G := G)) = coalg_id (tyD' G).
Proof. by []. Qed.

Lemma vlD'_lamE (G : ty' Ar) (A B : ty' Ar)
    (V : vl' (tprod' G A) B) :
  vlD' (v_lam V) = lam_coalg (vlD' V).
Proof. by []. Qed.

(** Underlying linear hom of [v_lam V] — reads via [adj_phiK] as the
    [tensor_curry] of the body with [der] inserted on the argument
    side, the standard LNL formula. *)
Lemma adj_phi_lam_coalg (G A B : Coalgebra Ar)
    (VB : coalg_hom (EM_prod G A) B) :
  adj_phi (lam_coalg VB) = lam_under VB.
Proof. exact: adj_phiK. Qed.

(** The [let]-of-[ret] law (substitution-as-composition): the proof
    is structurally identical to [cbv.cpD_letret]. *)
Lemma cpD'_letret (G H : ty' Ar) (t : ty' Ar)
    (V : vl' G H) (N : cp' H t) :
  cpD' (c_let' (c_ret' V) N) = coalg_comp (cpD' N) (vlD' V).
Proof.
change (cpD' (c_let' (c_ret' V) N))
  with (kcomp (cpD' N) (cpD' (c_ret' V))).
change (cpD' (c_ret' V)) with (coalg_comp (tunit_eta (tyD' H)) (vlD' V)).
rewrite /kcomp.
rewrite (coalg_compA (kbind (cpD' N)) (tunit_eta (tyD' H)) (vlD' V)).
by rewrite -/(kcomp (cpD' N) (tunit_eta (tyD' H))) kcomp_etaR.
Qed.

(** [c_sample' V] = [c_ret' V] (definitional, the !-monad identifies
    sampling with returning a measure — same fact as [cbv.cpD_sample_ret],
    a genuine feature of the cones model). *)
Lemma cpD'_sample_ret (G : ty' Ar) (Y : ar_obj Ar) (V : vl' G (tbase' Y)) :
  cpD' (c_sample' V) = cpD' (c_ret' V).
Proof. by []. Qed.

(** ** The higher-order example — [random_constant]

    [c_let (c_sample' v_var') (c_ret' (v_lam (v_fst' v_var')))] in
    context [Γ = tbase' X], denoting a Kleisli arrow
    [FMeas X ⇝ tfun (tbase' X) (tbase' X)].

    Reading: sample a value [c] from the input measure, then return
    the constant function [λ x. c].  The denotation is a coalgebra
    morphism [FMeas X → T (bang_cofree (!FMeas X ⊸ FMeas X))], i.e. a
    distribution over functions — the very feature mathcomp-qbs
    invokes QBS for, recovered here in the LNL discipline. *)
Section RandomConstant.
Variable X : ar_obj Ar.

(** The PPL program. *)
Definition ex_random_constant :
    cp' (tbase' X) (tfun (tbase' X) (tbase' X)) :=
  c_let' (c_sample' (v_var' (G := tbase' X)))
         (c_ret' (v_lam (v_fst' (v_var' (G := tprod' (tbase' X) (tbase' X)))))).

(** Its denotation is a Kleisli arrow [tbase' X ⇝ tfun (tbase' X)
    (tbase' X)], i.e. a coalgebra morphism
    [FMeas X → T (bang_cofree (!FMeas X ⊸ FMeas X))]. *)
Definition ex_random_constant_denot :
    coalg_hom (tyD' (tbase' X))
              (Tobj (tyD' (tfun (tbase' X) (tbase' X)))) :=
  cpD' ex_random_constant.

(** β-step of the higher-order example: since [c_sample _] = [c_ret _]
    on the [!]-monad ([cpD'_sample_ret]), and [let-of-ret] = compose
    ([cpD'_letret]) with the bound value [v_var' = id], the program
    reduces to the constant-lambda value. *)
Lemma ex_random_constant_denot_E :
  ex_random_constant_denot =
  cpD' (c_ret' (v_lam (v_fst' (v_var' (G := tprod' (tbase' X) (tbase' X)))))).
Proof.
rewrite /ex_random_constant_denot /ex_random_constant.
(* [c_sample' V] = [c_ret' V] definitionally on the !-monad. *)
have Esamp :
  @cpD' R Ar (tbase' X) (tbase' X) (c_sample' (v_var' (G := tbase' X))) =
  @cpD' R Ar (tbase' X) (tbase' X) (c_ret' (v_var' (G := tbase' X)))
  by [].
change (cpD' (c_let' (c_sample' (v_var' (G := tbase' X)))
                     (c_ret' (v_lam (v_fst' v_var')))))
  with (kcomp (cpD' (c_ret' (v_lam
                  (v_fst' (v_var' (G := tprod' (tbase' X) (tbase' X)))))))
              (cpD' (c_sample' (v_var' (G := tbase' X))))).
rewrite Esamp.
change (kcomp (cpD' (c_ret' (v_lam
                  (v_fst' (v_var' (G := tprod' (tbase' X) (tbase' X)))))))
              (cpD' (c_ret' (v_var' (G := tbase' X)))))
  with (cpD' (c_let' (c_ret' (v_var' (G := tbase' X)))
              (c_ret' (v_lam
                  (v_fst' (v_var' (G := tprod' (tbase' X) (tbase' X)))))))).
rewrite cpD'_letret vlD'_varE.
exact: coalg_compIr.
Qed.

(** And the value of the lambda, unfolded: [v_lam (v_fst' v_var')] is
    the constant-c function, packaged through [lam_coalg] over the
    body [v_fst' v_var' : vl' (tprod' (tbase' X) (tbase' X)) (tbase' X)]. *)
Lemma ex_random_constant_value_E :
  vlD' (v_lam (v_fst' (v_var' (G := tprod' (tbase' X) (tbase' X))))) =
  lam_coalg (vlD' (v_fst' (v_var' (G := tprod' (tbase' X) (tbase' X))))).
Proof. exact: vlD'_lamE. Qed.

(** The underlying [icones_hom] of the lambda VALUE — the linear map
    [!FMeas X ⊸ FMeas X] that is the LNL reading of the closure
    [λx. c].  We do not "unfold" past [lam_under]; the deep unfolding
    [adj_phi_lam_coalg] gives it explicitly. *)
Lemma ex_random_constant_under_E :
  adj_phi (vlD' (v_lam (v_fst' (v_var' (G := tprod' (tbase' X) (tbase' X)))))) =
  lam_under (vlD' (v_fst' (v_var' (G := tprod' (tbase' X) (tbase' X))))).
Proof.
rewrite vlD'_lamE; exact: adj_phi_lam_coalg.
Qed.

End RandomConstant.

End Soundness.

Arguments cpD'_letret {R Ar G H t} V N.
Arguments cpD'_sample_ret {R Ar G Y} V.
Arguments vlD'_varE {R Ar} G.
Arguments vlD'_lamE {R Ar G A B} V.
Arguments adj_phi_lam_coalg {R Ar G A B} VB.
Arguments ex_random_constant {R Ar} X.
Arguments ex_random_constant_denot {R Ar} X.
Arguments ex_random_constant_denot_E {R Ar} X.

(** ** [APP_NOTE] — the exact coalgebra-morphism obligation for [v_app]

    To close the gap and add [v_app], one would prove:

    Given [G A B : Coalgebra Ar] and [φ : icones_hom (coalg_obj G)
    (linhom_car Ar (Bang Ar (coalg_obj A)) (coalg_obj B))], [ψ :
    icones_hom (coalg_obj G) (Bang Ar (coalg_obj A))] satisfying the
    appropriate coalgebra-morphism conditions, the composite
    [eval_smcc ∘ (φ ⊗ ψ) ∘ coalg_d G] is a coalgebra morphism
    [G → B].

    This is a special case of "the SMCC closed structure on [ICones]
    lifts to the cartesian structure of [EM(!)]" (Melliès §6.3 /
    Bénabou): the cofree adjunction [U ⊣ !̃] is a monoidal adjunction
    ([cbv_adjunction.v]), and the SMCC evaluation is the counit of
    the *internal hom* of the cartesian closure that should follow.
    The proof would be a moderate-sized diagram chase (analogous to
    [em_proj1_is_mor] in [cbv.v]); it is NOT in [cbv_adjunction.v] /
    [em_cartesian.v] today.  Recording this here as the precise
    statement that would unlock the [v_app] elimination. *)
