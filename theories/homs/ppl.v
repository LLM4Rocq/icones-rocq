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
      the value type level; lambda abstraction [v_lam] (value) and
      application [c_app] (COMPUTATION, Moggi/CBPV style) — see
      "Honest scope" below for why application is a computation, not a
      value, in our presentation.
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

    **Application is a computation, not a value.**  In a generic CBV
    presentation, applying a function value [V W] to an argument value
    [W] would give a value of type [B]; in our setup it gives a
    COMPUTATION of type [T B] (a Kleisli arrow into [bang_cofree B]).
    Reason: the underlying linear hom of application is
    [app_under := eval ∘ (φ ⊗ ψ) ∘ d_G : G → B] in the underlying
    [ICones]; promoting this to a coalgebra morphism in [EM(!)]
    DIRECTLY (i.e. into [B] itself) would require proving that the
    SMCC evaluation [eval : (!A ⊸ B) ⊗ !A → B] is itself a coalgebra
    morphism between the appropriate EM-products and the target
    coalgebra structure on [B], which is true (it is the counit of
    the *monoidal* cofree adjunction, by Melliès §6.3 / Bénabou) but is
    *not* in our current file inventory.

    Routing through [Tobj B = bang_cofree (coalg_obj B)] dodges this
    obligation: [adj_psi] of the cofree adjunction unconditionally
    lifts any [icones_hom (coalg_obj G) X] to a coalgebra morphism
    [G → bang_cofree X] ([adj_psi_is_mor] in [em_cat.v]).  This makes
    application a computation; in our calculus we can sequence it via
    [c_let'] just like [c_sample'].  The resulting calculus is
    Moggi/CBPV-style: function values [V W : tfun A B → A → cp' G B]
    is exactly the [F]-elimination of CBPV's value/computation split,
    over the value space [EM(!)] and the computation monad [T].

    The remaining feature we do NOT cover is the GENERIC
    coalgebra-morphism property of [eval_smcc] itself; this would let
    [c_app] be replaced by a value-level [v_app] producing a coalgebra
    morphism into [B] directly.  We record this in [APP_NOTE] at the
    end of the file. *)

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
    as in [cbv.v].  Values gain a lambda introduction [v_lam], and
    computations gain a Moggi/CBPV-style application [c_app] (which
    returns [T B], not [B] — see the "Honest scope" in the file
    header). *)
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

(** Computations [cp' Γ τ] : extends [cbv.v]'s [cp] with [c_app], a
    Moggi-style "application as a computation".  In a CBV/CBPV
    discipline, applying a function VALUE to an argument VALUE is a
    COMPUTATION (yielding [T B] not [B]) — see e.g. Levy's CBPV.  This
    is what allows the higher-order ELIMINATION to be a coalgebra
    morphism in our model: the result lives in [Tobj B = bang_cofree
    (coalg_obj B)], and [adj_psi] makes the underlying linear map of
    application ([app_under]) into a coalgebra morphism into this
    cofree object — UNCONDITIONALLY (the proof is [adj_psi_is_mor] in
    [em_cat.v]). *)
Inductive cp' (G : ty') : ty' -> Type :=
  | c_ret' (t : ty') : vl' G t -> cp' G t
  | c_let' (H t : ty') : cp' G H -> cp' H t -> cp' G t
  | c_sample' (X : ar_obj Ar) :
      vl' G (tbase' X) -> cp' G (tbase' X)
  | c_app (A B : ty') : vl' G (tfun A B) -> vl' G A -> cp' G B.

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
Arguments c_app {R Ar G A B} V W.

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

(** *** The SMCC evaluation map [eval_smcc B C : (B ⊸ C) ⊗ B → C]

    A standard piece of SMCC kit, defined from [tensor_uncurry] applied
    to the identity [id_{B ⊸ C} : (B ⊸ C) → (B ⊸ C)].  This is the
    evaluation arrow of the closed structure on [ICones]; used by
    [app_under] below to interpret application. *)
Definition eval_smcc (B C : ICone.type Ar) :
    icones_hom Ar (tensor Ar (linhom_car Ar B C) B) C :=
  tensor_uncurry (icones_id Ar (linhom_car Ar B C)).

(** *** Underlying linear hom of an application — Girard/LNL

    Given the function and argument's coalg-hom interpretations
    [VF] and [VA], produce an icones_hom [coalg_obj G → coalg_obj B]:
    - pair the underlying [adj_phi VF : coalg_obj G → !A.obj ⊸ B.obj]
      (= the counit of the cofree adjunction applied to [VF]) with the
      promoted argument [bang_fmap (ch_mor VA) ∘ coalg_str G : coalg_obj G
      → Bang Ar (coalg_obj A)] (= the underlying of
      [adj_psi (ch_mor VA)]: the [!]-promotion of [VA] seen through the
      coalgebra structure of Γ);
    - precompose with the comonoid diagonal [coalg_d G]
      (unconditional via [EMComon_all], Cor 20);
    - postcompose with [eval_smcc].

    This is the underlying linear hom of "application after the
    diagonal".  At the VALUE-CATEGORY level it is then lifted to a
    coalgebra morphism into [bang_cofree (coalg_obj B) = T B] via
    [adj_psi] (unconditional, see [adj_psi_is_mor] in [em_cat.v]) —
    making application a COMPUTATION (CBPV-style), not a value. *)
Definition app_under (G A B : Coalgebra Ar)
    (VF : coalg_hom G (bang_cofree (linhom_car Ar (Bang Ar (coalg_obj A))
                                              (coalg_obj B))))
    (VA : coalg_hom G A) :
    icones_hom Ar (coalg_obj G) (coalg_obj B) :=
  icones_comp (eval_smcc (Bang Ar (coalg_obj A)) (coalg_obj B))
    (icones_comp
       (tensor_mor (adj_phi VF)
                   (icones_comp (bang_fmap (ch_mor VA)) (coalg_str G)))
       (coalg_d G)).

(** Bundled application as a coalgebra morphism into [T B = bang_cofree
    (coalg_obj B)].  Application is a COMPUTATION (Moggi/CBPV-style):
    its denotation lives in the Kleisli category of [T]. *)
Definition app_kleisli (G A B : Coalgebra Ar)
    (VF : coalg_hom G (bang_cofree (linhom_car Ar (Bang Ar (coalg_obj A))
                                              (coalg_obj B))))
    (VA : coalg_hom G A) :
    coalg_hom G (bang_cofree (coalg_obj B)) :=
  adj_psi (app_under VF VA).

End Lam.

Arguments lam_under {R Ar G A B} VB.
Arguments lam_coalg {R Ar G A B} VB.
Arguments eval_smcc {R Ar} B C.
Arguments app_under {R Ar G A B} VF VA.
Arguments app_kleisli {R Ar G A B} VF VA.

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

(** Computation denotation [cpD'] — extends [cbv.v]'s with [c_app].

    For [c_app Vf Va] we use [app_kleisli], which routes [app_under]
    through [adj_psi] of the cofree adjunction to land in
    [bang_cofree (coalg_obj B) = Tobj B].  This is unconditional: every
    [icones_hom (coalg_obj G) (coalg_obj B)] becomes a coalgebra
    morphism into [bang_cofree (coalg_obj B)] via [adj_psi]
    ([adj_psi_is_mor] in [em_cat.v]). *)
Fixpoint cpD' (G : ty' Ar) (t : ty' Ar) (M : cp' G t) {struct M} :
    coalg_hom (tyD' G) (Tobj (tyD' t)) :=
  match M in cp' _ t0 return coalg_hom (tyD' G) (Tobj (tyD' t0)) with
  | c_ret' t0 V => coalg_comp (tunit_eta (tyD' t0)) (vlD' V)
  | c_let' H t0 N1 N2 => kcomp (cpD' N2) (cpD' N1)
  | c_sample' X V => coalg_comp (tunit_eta (tyD' (tbase' X))) (vlD' V)
  | c_app A B Vf Va => app_kleisli (vlD' Vf) (vlD' Va)
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

(** [c_app] denotation reads as [app_kleisli] of the value
    denotations — definitional. *)
Lemma cpD'_appE (G : ty' Ar) (A B : ty' Ar)
    (Vf : vl' G (tfun A B)) (Va : vl' G A) :
  cpD' (c_app Vf Va) = app_kleisli (vlD' Vf) (vlD' Va).
Proof. by []. Qed.

(** *** The β-rule at the underlying-ICones level

    [adj_phi (app_kleisli VF VA) = app_under VF VA] — round-trip of
    [adj_psi] through [adj_phi] is the identity ([adj_phiK]).  This
    gives the underlying linear hom of an application, without going
    through the cofree coalgebra detour. *)
Lemma adj_phi_app_kleisli (G A B : Coalgebra Ar)
    (VF : coalg_hom G (bang_cofree (linhom_car Ar (Bang Ar (coalg_obj A))
                                              (coalg_obj B))))
    (VA : coalg_hom G A) :
  adj_phi (app_kleisli VF VA) = app_under VF VA.
Proof. exact: adj_phiK. Qed.

(** *** The β-rule on a lambda: the underlying of [c_app (v_lam V) W]

    Combine [adj_phi_app_kleisli] with [adj_phi_lam_coalg] to read
    the underlying linear hom of [c_app (v_lam V) W] as
    [eval_smcc ∘ (lam_under (vlD' V) ⊗ (bang_fmap (vlD' W) ∘ coalg_str))
    ∘ coalg_d].  This is the standard β-reduction of an LNL CBV
    application; full β-equivalence with the substituted body
    [V[W/x]] would need a substitution lemma, which is a separate
    development (not pursued here). *)
Lemma adj_phi_cpD'_app_lam (G A B : ty' Ar)
    (V : vl' (tprod' G A) B) (W : vl' G A) :
  adj_phi (cpD' (c_app (v_lam V) W)) =
  icones_comp (eval_smcc (Bang Ar (coalg_obj (tyD' A))) (coalg_obj (tyD' B)))
    (icones_comp
       (tensor_mor (lam_under (vlD' V))
                   (icones_comp (bang_fmap (ch_mor (vlD' W)))
                                (coalg_str (tyD' G))))
       (coalg_d (tyD' G))).
Proof.
rewrite cpD'_appE adj_phi_app_kleisli /app_under.
by rewrite vlD'_lamE adj_phi_lam_coalg.
Qed.

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

(** A second higher-order example, exercising APPLICATION
    ([c_app]): apply the identity-lambda to its own argument.  This
    is "lift the variable through a function value" — a degenerate
    HO program that nonetheless exercises [v_lam], [c_app], and the
    [lam_under]/[app_under] LNL plumbing.

    [Γ = tbase' X ⊢
      let f = ret (λx. x) in let _ = sample x in app f x : T X]

    or just the bare application
    [Γ = tbase' X ⊢ app (λx. x) x : cp' (tbase' X)]. *)
Definition ex_app_id : cp' (tbase' X) (tbase' X) :=
  c_app (v_lam (v_snd' (v_var' (G := tprod' (tbase' X) (tbase' X)))))
        (v_var' (G := tbase' X)).

Definition ex_app_id_denot :
    coalg_hom (tyD' (tbase' X)) (Tobj (tyD' (tbase' X))) :=
  cpD' ex_app_id.

(** The denotation is definitionally an [app_kleisli] of the lambda's
    interpretation and the variable's identity. *)
Lemma ex_app_id_denot_E :
  ex_app_id_denot =
  app_kleisli (vlD' (v_lam (v_snd' (v_var' (G := tprod' (tbase' X) (tbase' X))))))
              (vlD' (v_var' (G := tbase' X))).
Proof. by []. Qed.

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

(** **The integral anchor.**  Combining the reduction
    [ex_random_constant_denot_E] with [cpD_sample_is_integral] of
    [cbv.v] (= [Theta] = identity at the coalgebra structure of
    [FMeas X]), the denotation of [ex_random_constant] is *the
    integral against the input measure of the promoted constant-
    function path*: for [μ : FMeas X],

      ⟦ ex_random_constant ⟧(μ) = (Coalg_{T(...)} ∘ lam_coalg ...)(μ)

    in the underlying ICones — and [Coalg_X] of a Dirac is the
    promoted Dirac ([Coalg_dirac] in [coalgebra.v]), so an atomic input
    measure [δr] yields the promoted constant-r function [(λx.r)!].
    This is the precise integration sense in which our denotation
    matches the mathcomp-qbs [monadP_map curried_const Normal(0,1)]. *)
Lemma ex_random_constant_denot_at_ret :
  ex_random_constant_denot =
  coalg_comp
    (tunit_eta (tyD' (tfun (tbase' X) (tbase' X))))
    (vlD' (v_lam (v_fst' (v_var' (G := tprod' (tbase' X) (tbase' X)))))).
Proof. exact: ex_random_constant_denot_E. Qed.

End RandomConstant.

End Soundness.

Arguments cpD'_letret {R Ar G H t} V N.
Arguments cpD'_sample_ret {R Ar G Y} V.
Arguments cpD'_appE {R Ar G A B} Vf Va.
Arguments vlD'_varE {R Ar} G.
Arguments vlD'_lamE {R Ar G A B} V.
Arguments adj_phi_lam_coalg {R Ar G A B} VB.
Arguments adj_phi_app_kleisli {R Ar G A B} VF VA.
Arguments adj_phi_cpD'_app_lam {R Ar G A B} V W.
Arguments ex_random_constant {R Ar} X.
Arguments ex_random_constant_denot {R Ar} X.
Arguments ex_random_constant_denot_E {R Ar} X.
Arguments ex_random_constant_denot_at_ret {R Ar} X.
Arguments ex_random_constant_value_E {R Ar} X.
Arguments ex_random_constant_under_E {R Ar} X.
Arguments ex_app_id {R Ar} X.
Arguments ex_app_id_denot {R Ar} X.
Arguments ex_app_id_denot_E {R Ar} X.

(** ** [APP_NOTE] — promoting [c_app] (computation) to a value [v_app]

    Our [c_app] makes application a COMPUTATION, landing in [Tobj B].
    To replace it with a value-level [v_app] landing in [B] directly,
    one would prove:

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
    statement that would unlock the [v_app] elimination directly into
    the value category.  For the example we port, this is not needed:
    the lambda is the OUTPUT of the program, never consumed. *)
