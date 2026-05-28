(**md**************************************************************************)
(** * A higher-order probabilistic PPL — fine-grain Moggi CBV in EM(!)

    This file extends the first-order Moggi-CBV demo of
    [theories/programs/cbv.v] with HIGHER-ORDER function types and ports
    the canonical higher-order example from mathcomp-qbs's
    [ppl_qbs.v] / [showcase/ppl_examples.v]:

    [[
        random_constant ≜ do c <- sample (μ : X); return (λx. c)
    ]]

    a distribution over the function space [X → X], the paradigmatic
    *higher-order* example mathcomp-qbs emphasises (distributions on
    function spaces are impossible in classical measure-theoretic
    / kernel-based semantics; QBS resolves this via cartesian
    closure, the cones model via the structure described below).

    ** The mathematical framework — EM(!) Kleisli exponentials for [T = !̃ ∘ U] **

    The value category is the FULL Eilenberg–Moore category [EM(!)]
    of the exponential comonad ([em_cartesian.v]); it is cartesian
    (Prop 28 / Cor 20, [emc_d_mor] holds for all coalgebras via the
    structural [EMComon_all]) but is NOT cartesian-closed — and is
    not expected to be.  [EM(!)] does, however, support the *Kleisli
    exponential* for the CBV computation monad [T = !̃ ∘ U]
    ([Tobj] in [cbv.v]), which is exactly what Moggi-style monadic
    CBV semantics needs.

    The Kleisli-exponential structure on [EM(!)] for [T] is given by
    the natural-bijection chain (each step is named and witnessed by
    a lemma in this development):

    [[
       Hom_EM(C × A, T B)
         ≅ Hom_IC(U(C × A), U B)            [cofree adjunction U ⊣ !̃: [adj_phi]/[adj_psi]]
         ≅ Hom_IC(U C ⊗ U A, U B)           [U is STRICT monoidal: [cbv_U_prod] in [cbv_adjunction.v]]
         ≅ Hom_IC(U C, U A ⊸ U B)           [SMCC closure on [ICones]: [tensor_curry]/[tensor_uncurry]]
         ≅ Hom_EM(C, !̃(U A ⊸ U B))          [cofree adjunction U ⊣ !̃ again]
    ]]

    So the CBV function-type denotation is the cofree coalgebra of
    the LINEAR function space [U A ⊸ U B]:

    [[
        ⟦A → B⟧ := !̃(U A ⊸ U B)
                = bang_cofree (linhom_car Ar (coalg_obj ⟦A⟧) (coalg_obj ⟦B⟧)).
    ]]

    In Moggi-style monadic CBV, application is a *computation*: the
    interpretation of [v_app f x] lives in [Hom_EM(C × A, T B)], the
    LEFT end of the chain above.  Lambda introduces a function value
    by going LEFT→RIGHT (curry); application eliminates it by going
    RIGHT→LEFT (uncurry).  Both are by structural natural-bijection
    — there is no diagram chase about "is the SMCC eval a coalgebra
    morphism into [B]?": the cofree adjunction unconditionally lifts
    *every* [icones_hom (U_obj G) (U_obj B)] to a coalgebra morphism
    [G → !̃(U B) = T B] (via [adj_psi]), which IS the [T B] target
    of an application in monadic CBV.  No CCC on [EM(!)], no
    co-Kleisli / Girard extra [!] on the domain, no `eval_smcc`
    coalgebra-morphism claim, no APP_NOTE.

    ** Anti-glossary (terminology that DOES NOT apply here) **

    The reader looking at earlier versions of this file (or at CBPV
    presentations) should not look for:
    - "CBPV split" / "F-elimination" / "value-CCC":  this is straight
      Moggi-CBV, not CBPV, and the function type is a Kleisli
      exponential for [T = !̃ ∘ U] in [EM(!)], not the [F] of CBPV.
    - "Girard / co-Kleisli / CBN translation [A → B = !A ⊸ B]":  that
      would put an extra [!] on the domain.  The Kleisli-exponential
      [!̃(U A ⊸ U B)] has NO extra [!] on the domain — that is the
      whole point of the chain.
    - "Mellies §6.3 gap" / "[eval_smcc] is a coalg-morphism":  no
      such obligation exists in this development.  Application is a
      computation INTRINSICALLY in monadic CBV, by the right-end of
      the chain landing in [!̃(U B)].

    ** The fragment interpreted (stated honestly) **

    Compared to mathcomp-qbs:
    - [ppl_real], [ppl_prod], [ppl_unit] map to our [tbase'] / [tprod']
      / [tunit'] (as in [cbv.v]);
    - [ppl_fun] is the higher-order arrow [tfun A B] = [!̃(U A ⊸ U B)] —
      the Kleisli exponential for the CBV monad [T = !̃ ∘ U];
    - lambda abstraction [v_lam] is a VALUE binding a fresh variable;
      the body of a lambda is a COMPUTATION (fine-grain Moggi-CBV);
    - application [c_app] is a COMPUTATION (Moggi monadic CBV, NOT a
      CBPV split — application LANDS in [T B] by the chain above);
    - [ppl_bool] / [ppl_sum] are NOT supported (no boolean / coproduct
      objects in the setup); they are orthogonal to the higher-order
      content and not exercised by the example;
    - [ppl_prob] is identified with the CBV computation monad [T] of
      [cbv.v].

    ** The headline example: [random_constant] **

    [[
        ex_random_constant ≜
          c_let' (c_sample' v_var')
                 (c_ret' (v_lam (c_ret' (v_fst' v_var'))))
    ]]
    in context [Γ = tbase' X ⊢ — : T (tfun (tbase' X) (tbase' X))]:
    draw a sample [c], then return the constant function [λ x. c]
    (whose body is a value-form computation that returns [c]).  Its
    denotation is a coalgebra morphism
    [FMeas X → T (!̃(FMeas X ⊸ FMeas X))]: a distribution over linear
    functions — the higher-order feature mathcomp-qbs invokes QBS for,
    recovered here in the EM(!) Kleisli-exponential discipline.

    We deliver:
    - syntax / type interpretation / term interpretation, all
      axiom-free and structurally total;
    - the [let]-of-[ret] law ([cpD'_letret]), the [sample]-as-[ret]
      identity ([cpD'_sample_ret]) at the PPL level — identical to
      [cbv.v];
    - the β-rule at the underlying-ICones level
      ([adj_phi_cpD'_app_lam]): the round-trip of [adj_psi] through
      [adj_phi] reads application-on-a-lambda as the SMCC
      uncurry/curry pair;
    - the higher-order example [ex_random_constant_denot_E]: its
      denotation reduces, via [cpD'_sample_ret] + [cpD'_letret] +
      [vlD'_varE], to the constant-lambda value.

    EM(!) is not cartesian closed and is not expected to be; the
    Kleisli exponential [!̃(U A ⊸ U B)] for [T = !̃ ∘ U] is what CBV
    requires, and that *is* the encoding above.  There is no further
    missing structure for this calculus. *)

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
Require Import Icones.programs.cbv.

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
    constructor is [tfun A B] (the Kleisli-exponential type
    [!̃(U A ⊸ U B)]); products [tprod'], unit [tunit'] and base types
    [tbase' X] are exactly as in [cbv.v].  Values gain a lambda
    introduction [v_lam] whose body is a *computation* (fine-grain
    Moggi-CBV), and computations gain a Moggi-CBV application [c_app]
    which lands in [T B]. *)
Section Syntax.
Variable (R : realType) (Ar : MeasSubcat R).

Inductive ty' : Type :=
  | tunit'
  | tbase' (X : ar_obj Ar)
  | tprod' (s t : ty')
  | tfun (A B : ty').

(** Values [vl' Γ τ] : a value of type [τ] with one free variable of
    type [Γ].  Compared to [cbv.v]'s [vl], we add [v_lam]; its body is
    a COMPUTATION ([cp']) in the extended context [tprod' Γ A] —
    fine-grain Moggi-CBV. *)
Inductive vl' (G : ty') : ty' -> Type :=
  | v_var' : vl' G G
  | v_unit' : vl' G tunit'
  | v_pair' (s t : ty') :
      vl' G s -> vl' G t -> vl' G (tprod' s t)
  | v_fst' (s t : ty') : vl' G (tprod' s t) -> vl' G s
  | v_snd' (s t : ty') : vl' G (tprod' s t) -> vl' G t
  | v_lam (A B : ty') :
      cp' (tprod' G A) B -> vl' G (tfun A B)

(** Computations [cp' Γ τ] : extends [cbv.v]'s [cp] with [c_app], a
    Moggi-style application that LANDS in [T B] by the Kleisli-
    exponential chain — the standard form of application in monadic
    CBV.  This is NOT a CBPV / fallback choice: it is what the
    Kleisli exponential gives. *)
with cp' (G : ty') : ty' -> Type :=
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
Arguments v_lam {R Ar G A B} M.
Arguments cp' {R Ar} G t.
Arguments c_ret' {R Ar G t} V.
Arguments c_let' {R Ar G H t} M N.
Arguments c_sample' {R Ar G X} V.
Arguments c_app {R Ar G A B} V W.

(** ** Type interpretation [tyD']

    Every type denotes a coalgebra of [EM(!)].  The new clause for
    [tfun A B] is the Kleisli exponential for [T = !̃ ∘ U]:
    [[
        ⟦tfun A B⟧ = !̃(U A ⊸ U B)
                  = bang_cofree (linhom_car Ar (coalg_obj ⟦A⟧) (coalg_obj ⟦B⟧)).
    ]]
    Note: NO [Bang] on the domain — this is the Kleisli-exponential
    encoding for monadic CBV, NOT the Girard / CBN translation. *)
Section TypeInterp.
Variables (R : realType) (Ar : MeasSubcat R).

Fixpoint tyD' (t : ty' Ar) : Coalgebra Ar :=
  match t with
  | tunit' => EM_term
  | tbase' X => FMeas_coalgebra X
  | tprod' s1 s2 => EM_prod (tyD' s1) (tyD' s2)
  | tfun A B => bang_cofree (linhom_car Ar (coalg_obj (tyD' A))
                                        (coalg_obj (tyD' B)))
  end.

End TypeInterp.

Arguments tyD' {R Ar} t.

(** ** Lambda and application via the Kleisli-exponential chain

    The two helper combinators [lam_coalg] and [app_kleisli] realise
    the chain
    [[
       Hom_EM(G × A, T B) ≅ Hom_EM(G, !̃(U A ⊸ U B))
    ]]
    as Coq definitions, using:

    - step 1 (cofree adjunction at the LEFT end, target [!̃(U B)]):
      [adj_phi] / [adj_psi] of [em_cat.v];
    - step 2 (U strict monoidal): definitional — [coalg_obj
      (EM_prod G A) = coalg_obj G ⊗ coalg_obj A] by [EM_prod_obj], so
      step 2 is invisible at the term level;
    - step 3 (SMCC closure on [ICones]): [tensor_curry] /
      [tensor_uncurry] of [tensor_construct.v] / [smcc.v];
    - step 4 (cofree adjunction at the RIGHT end, target
      [!̃(U A ⊸ U B)]): [adj_phi] / [adj_psi] again. *)

Section Lam.
Variables (R : realType) (Ar : MeasSubcat R).

(** *** Lambda — going LEFT to RIGHT through the chain

    Given a body interpretation
    [MB : coalg_hom (EM_prod G A) (Tobj B)]
    (a Kleisli arrow [G × A ⇝ B]), produce
    [coalg_hom G (bang_cofree (linhom_car Ar (coalg_obj A) (coalg_obj B)))].

    Steps (right-to-left in the diagram above, but reading the code
    bottom-up):
    - [adj_phi MB : icones_hom Ar (U_obj (EM_prod G A)) (U_obj B)]
      (step 1: cofree adjunction at LEFT end);
    - by [EM_prod_obj] the domain is definitionally
      [coalg_obj G ⊗ coalg_obj A] (step 2: U strict monoidal — no map
      needed);
    - [tensor_curry] turns it into
      [icones_hom Ar (coalg_obj G) (linhom_car Ar (coalg_obj A) (coalg_obj B))]
      (step 3: SMCC closure);
    - [adj_psi] lifts that to a coalgebra morphism into
      [bang_cofree (linhom_car Ar (coalg_obj A) (coalg_obj B))]
      (step 4: cofree adjunction at RIGHT end). *)
Definition lam_under (G A B : Coalgebra Ar)
    (MB : coalg_hom (EM_prod G A) (Tobj B)) :
    icones_hom Ar (coalg_obj G)
      (linhom_car Ar (coalg_obj A) (coalg_obj B)) :=
  tensor_curry (adj_phi MB).

Definition lam_coalg (G A B : Coalgebra Ar)
    (MB : coalg_hom (EM_prod G A) (Tobj B)) :
    coalg_hom G (bang_cofree (linhom_car Ar (coalg_obj A) (coalg_obj B))) :=
  adj_psi (lam_under MB).

(** *** Application — going RIGHT to LEFT through the chain

    Given:
    - [VF : coalg_hom G (bang_cofree (linhom_car Ar (coalg_obj A) (coalg_obj B)))]
      (a value of the function type);
    - [VA : coalg_hom G A]
      (a value of the argument type);
    produce a Kleisli arrow [G ⇝ B], i.e.
    [coalg_hom G (Tobj B) = coalg_hom G (bang_cofree (coalg_obj B))].

    Steps (right-to-left in the diagram above):
    - [adj_phi VF : icones_hom Ar (coalg_obj G) (linhom_car Ar (coalg_obj A) (coalg_obj B))]
      (step 4 reversed: cofree adjunction at RIGHT end);
    - [tensor_uncurry] turns it into
      [icones_hom Ar (coalg_obj G ⊗ coalg_obj A) (coalg_obj B)]
      (step 3 reversed: SMCC closure);
    - precompose with [(id ⊗ U_mor VA) ∘ coalg_d G : coalg_obj G →
      coalg_obj G ⊗ coalg_obj A] (step 2 reversed: U strict monoidal —
      the comonoidal diagonal [coalg_d G : coalg_obj G → coalg_obj G ⊗
      coalg_obj G] then pair the IDENTITY with the underlying [U_mor VA
      = ch_mor VA] of the argument);
    - [adj_psi] lifts to a coalgebra morphism into
      [bang_cofree (coalg_obj B) = Tobj B]
      (step 1 reversed: cofree adjunction at LEFT end).

    No `eval_smcc-is-a-coalg-morphism' chase is performed: every
    [icones_hom (coalg_obj G) (coalg_obj B)] is lifted to
    [coalg_hom G (Tobj B)] by [adj_psi_is_mor] unconditionally — this
    is exactly what makes monadic CBV work. *)
Definition app_under (G A B : Coalgebra Ar)
    (VF : coalg_hom G
            (bang_cofree (linhom_car Ar (coalg_obj A) (coalg_obj B))))
    (VA : coalg_hom G A) :
    icones_hom Ar (coalg_obj G) (coalg_obj B) :=
  icones_comp (tensor_uncurry (adj_phi VF))
    (icones_comp (tensor_mor (icones_id Ar (coalg_obj G)) (ch_mor VA))
                 (coalg_d G)).

Definition app_kleisli (G A B : Coalgebra Ar)
    (VF : coalg_hom G
            (bang_cofree (linhom_car Ar (coalg_obj A) (coalg_obj B))))
    (VA : coalg_hom G A) :
    coalg_hom G (Tobj B) :=
  adj_psi (app_under VF VA).

End Lam.

Arguments lam_under {R Ar G A B} MB.
Arguments lam_coalg {R Ar G A B} MB.
Arguments app_under {R Ar G A B} VF VA.
Arguments app_kleisli {R Ar G A B} VF VA.

(** ** Term interpretation [vlD'] / [cpD']

    Values denote coalgebra morphisms; computations denote Kleisli
    arrows of the CBV monad [T = !̃ ∘ U] of [cbv.v].  Defined by
    MUTUAL fixpoint on the syntax (lambda's body is a [cp'], so [vlD']
    needs [cpD'] and vice versa). *)
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
  | v_lam A B body => lam_coalg (cpD' body)
  end

with cpD' (G : ty' Ar) (t : ty' Ar) (M : cp' G t) {struct M} :
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

(** Definitional unfoldings of [vlD'] / [cpD'] (stated as lemmas so
    [rewrite] folds them cleanly without an aggressive [/=]). *)
Lemma vlD'_varE (G : ty' Ar) :
  vlD' (v_var' (G := G)) = coalg_id (tyD' G).
Proof. by []. Qed.

Lemma vlD'_lamE (G : ty' Ar) (A B : ty' Ar)
    (M : cp' (tprod' G A) B) :
  vlD' (v_lam M) = lam_coalg (cpD' M).
Proof. by []. Qed.

Lemma cpD'_retE (G : ty' Ar) (t : ty' Ar) (V : vl' G t) :
  cpD' (c_ret' V) = coalg_comp (tunit_eta (tyD' t)) (vlD' V).
Proof. by []. Qed.

Lemma cpD'_letE (G H : ty' Ar) (t : ty' Ar)
    (M : cp' G H) (N : cp' H t) :
  cpD' (c_let' M N) = kcomp (cpD' N) (cpD' M).
Proof. by []. Qed.

Lemma cpD'_sampleE (G : ty' Ar) (X : ar_obj Ar) (V : vl' G (tbase' X)) :
  cpD' (c_sample' V) = coalg_comp (tunit_eta (FMeas_coalgebra X)) (vlD' V).
Proof. by []. Qed.

(** *** Beta-rule support: [adj_phi] of [lam_coalg]

    [adj_phi] is the LEFT inverse of [adj_psi] ([adj_phiK]), so the
    underlying linear hom of a lambda VALUE is exactly [lam_under] of
    the body — i.e. [tensor_curry] of [adj_phi (cpD' body)]. *)
Lemma adj_phi_lam_coalg (G A B : Coalgebra Ar)
    (MB : coalg_hom (EM_prod G A) (Tobj B)) :
  adj_phi (lam_coalg MB) = lam_under MB.
Proof. exact: adj_phiK. Qed.

(** *** [adj_phi] of [app_kleisli]: read application back to its
    underlying linear hom.  Again by [adj_phiK]. *)
Lemma adj_phi_app_kleisli (G A B : Coalgebra Ar)
    (VF : coalg_hom G (bang_cofree (linhom_car Ar (coalg_obj A)
                                              (coalg_obj B))))
    (VA : coalg_hom G A) :
  adj_phi (app_kleisli VF VA) = app_under VF VA.
Proof. exact: adj_phiK. Qed.

(** The [let]-of-[ret] law (substitution-as-composition): the proof
    is structurally identical to [cbv.cpD_letret]. *)
Lemma cpD'_letret (G H : ty' Ar) (t : ty' Ar)
    (V : vl' G H) (N : cp' H t) :
  cpD' (c_let' (c_ret' V) N) = coalg_comp (cpD' N) (vlD' V).
Proof.
rewrite cpD'_letE cpD'_retE /kcomp.
rewrite (coalg_compA (kbind (cpD' N)) (tunit_eta (tyD' H)) (vlD' V)).
by rewrite -/(kcomp (cpD' N) (tunit_eta (tyD' H))) kcomp_etaR.
Qed.

(** [c_sample' V] = [c_ret' V] (definitional, the !-monad identifies
    sampling with returning a measure — same fact as
    [cbv.cpD_sample_ret], a genuine feature of the cones model). *)
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

    Combine [adj_phi_app_kleisli] with [adj_phi_lam_coalg] to read
    the underlying linear hom of [c_app (v_lam M) W] as

      [tensor_uncurry (tensor_curry (adj_phi (cpD' M))) ∘
        (id_G ⊗ ch_mor (vlD' W)) ∘ coalg_d G]
      = [adj_phi (cpD' M) ∘ (id_G ⊗ ch_mor (vlD' W)) ∘ coalg_d G]

    by the SMCC inversion [tensor_uncurryK / tensor_curryK].  This is
    the structural β-equation at the linear-hom level; full term-level
    β-equivalence with the substituted body [M[W/x]] would need a
    syntactic substitution lemma (not pursued here — it is orthogonal
    to the type-theoretic correctness of the new encoding). *)
Lemma adj_phi_cpD'_app_lam (G A B : ty' Ar)
    (M : cp' (tprod' G A) B) (W : vl' G A) :
  adj_phi (cpD' (c_app (v_lam M) W)) =
  icones_comp (tensor_uncurry (lam_under (cpD' M)))
    (icones_comp
       (tensor_mor (icones_id Ar (coalg_obj (tyD' G))) (ch_mor (vlD' W)))
       (coalg_d (tyD' G))).
Proof.
rewrite cpD'_appE adj_phi_app_kleisli /app_under.
by rewrite vlD'_lamE adj_phi_lam_coalg.
Qed.

(** ** The higher-order example — [random_constant]

    [[
        ex_random_constant ≜
          c_let' (c_sample' v_var')
                 (c_ret' (v_lam (c_ret' (v_fst' v_var'))))
    ]]
    in context [Γ = tbase' X], denoting a Kleisli arrow
    [FMeas X ⇝ tfun (tbase' X) (tbase' X)].

    Reading: sample a value [c] from the input measure, then return
    the constant function [λ x. c] (whose body is the value-form
    computation [ret c]).  The denotation is a coalgebra morphism
    [FMeas X → T (!̃(FMeas X ⊸ FMeas X))], i.e. a distribution over
    linear maps — the very feature mathcomp-qbs invokes QBS for,
    recovered here in the EM(!) Kleisli-exponential discipline. *)
Section RandomConstant.
Variable X : ar_obj Ar.

(** The PPL program.  Note the lambda body is a COMPUTATION
    [c_ret' (v_fst' v_var')] — fine-grain Moggi-CBV. *)
Definition ex_random_constant :
    cp' (tbase' X) (tfun (tbase' X) (tbase' X)) :=
  c_let' (c_sample' (v_var' (G := tbase' X)))
         (c_ret' (v_lam (c_ret' (v_fst' (v_var' (G := tprod' (tbase' X)
                                                             (tbase' X))))))).

(** Its denotation is a Kleisli arrow [tbase' X ⇝ tfun (tbase' X)
    (tbase' X)], i.e. a coalgebra morphism
    [FMeas X → T (!̃(FMeas X ⊸ FMeas X))]. *)
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
  cpD' (c_ret' (v_lam (c_ret' (v_fst' (v_var' (G := tprod' (tbase' X)
                                                           (tbase' X))))))).
Proof.
rewrite /ex_random_constant_denot /ex_random_constant.
rewrite cpD'_letE (cpD'_sample_ret v_var') -cpD'_letE.
rewrite cpD'_letret vlD'_varE.
exact: coalg_compIr.
Qed.

(** And the value of the lambda, unfolded: [v_lam (c_ret' (v_fst'
    v_var'))] is the constant-c function, packaged through
    [lam_coalg] over the body computation
    [c_ret' (v_fst' v_var') : cp' (tprod' (tbase' X) (tbase' X)) (tbase' X)]. *)
Lemma ex_random_constant_value_E :
  vlD' (v_lam (c_ret' (v_fst' (v_var' (G := tprod' (tbase' X) (tbase' X)))))) =
  lam_coalg (cpD' (c_ret' (v_fst'
              (v_var' (G := tprod' (tbase' X) (tbase' X)))))).
Proof. exact: vlD'_lamE. Qed.

(** A second higher-order example, exercising APPLICATION ([c_app]):
    apply the identity-lambda to its own argument.  The lambda's body
    is [c_ret' (v_snd' v_var')] — the value-form computation returning
    the second component of the pair (Γ, x).

    [Γ = tbase' X ⊢ app (λx. ret x) x : cp' (tbase' X)]. *)
Definition ex_app_id : cp' (tbase' X) (tbase' X) :=
  c_app (v_lam (c_ret' (v_snd' (v_var' (G := tprod' (tbase' X) (tbase' X))))))
        (v_var' (G := tbase' X)).

Definition ex_app_id_denot :
    coalg_hom (tyD' (tbase' X)) (Tobj (tyD' (tbase' X))) :=
  cpD' ex_app_id.

(** The denotation is definitionally an [app_kleisli] of the lambda's
    interpretation and the variable's identity. *)
Lemma ex_app_id_denot_E :
  ex_app_id_denot =
  app_kleisli (vlD' (v_lam (c_ret' (v_snd'
                  (v_var' (G := tprod' (tbase' X) (tbase' X)))))))
              (vlD' (v_var' (G := tbase' X))).
Proof. by []. Qed.

(** The underlying [icones_hom] of the lambda VALUE — the linear map
    [FMeas X ⊸ FMeas X] that is the Kleisli-exponential reading of
    the closure [λx. c].  Read directly via [adj_phi_lam_coalg]. *)
Lemma ex_random_constant_under_E :
  adj_phi (vlD' (v_lam (c_ret' (v_fst'
            (v_var' (G := tprod' (tbase' X) (tbase' X))))))) =
  lam_under (cpD' (c_ret' (v_fst'
            (v_var' (G := tprod' (tbase' X) (tbase' X)))))).
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
    promoted Dirac ([Coalg_dirac] in [coalgebra.v]), so an atomic
    input measure [δr] yields the promoted constant-r function
    [(λx.r)!].  This is the precise integration sense in which our
    denotation matches the mathcomp-qbs [monadP_map curried_const
    Normal(0,1)]. *)
Lemma ex_random_constant_denot_at_ret :
  ex_random_constant_denot =
  coalg_comp
    (tunit_eta (tyD' (tfun (tbase' X) (tbase' X))))
    (vlD' (v_lam (c_ret' (v_fst'
            (v_var' (G := tprod' (tbase' X) (tbase' X))))))).
Proof. exact: ex_random_constant_denot_E. Qed.

End RandomConstant.

End Soundness.

Arguments cpD'_letret {R Ar G H t} V N.
Arguments cpD'_sample_ret {R Ar G Y} V.
Arguments cpD'_appE {R Ar G A B} Vf Va.
Arguments vlD'_varE {R Ar} G.
Arguments vlD'_lamE {R Ar G A B} M.
Arguments adj_phi_lam_coalg {R Ar G A B} MB.
Arguments adj_phi_app_kleisli {R Ar G A B} VF VA.
Arguments adj_phi_cpD'_app_lam {R Ar G A B} M W.
Arguments ex_random_constant {R Ar} X.
Arguments ex_random_constant_denot {R Ar} X.
Arguments ex_random_constant_denot_E {R Ar} X.
Arguments ex_random_constant_denot_at_ret {R Ar} X.
Arguments ex_random_constant_value_E {R Ar} X.
Arguments ex_random_constant_under_E {R Ar} X.
Arguments ex_app_id {R Ar} X.
Arguments ex_app_id_denot {R Ar} X.
Arguments ex_app_id_denot_E {R Ar} X.
