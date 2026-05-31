(**md**************************************************************************)
(** * A small first-order call-by-value calculus, interpreted in [ICones_CBV] — CBV §5

    Step 5 of the call-by-value roadmap
    ([/home/rocq/prime_gap/icones-cbv-plan.md], Part 7).  We define a small
    *probabilistic* call-by-value (CBV) calculus and interpret it in the CBV
    model [ICones_CBV] of [cbv_adjunction.v], demonstrating that the model
    actually interprets a probabilistic CBV language.

    **The fragment interpreted (stated honestly).**  This is the *first-order*
    fragment: a base type per measurable space, a unit type, binary products,
    [let]-sequencing, [return], and [sample].  Function/arrow types are NOT
    interpreted — the value category is cartesian but is NOT (yet) known to be
    closed (the [!A ⊸ B] route is not pursued), so no value-CCC and no closure
    claim are made.

    **The semantic domain (the value category).**  The value category is the
    FULL Eilenberg–Moore category [EM(!)] with its cartesian structure
    ([em_cartesian.v]).  Since [EMComon] holds for EVERY coalgebra
    ([EMComon_all], Melliès Cor 20 / Prop 28), [EM(!)] is cartesian with no
    subcategory restriction: types denote ARBITRARY coalgebras, products by
    [EM_prod], terminal by [EM_term], pairing by [em_pair], projections by
    [em_proj1_mor]/[em_proj2_mor], β-laws by [em_proj1_pair]/[em_proj2_pair],
    all UNCONDITIONAL.

    HONEST SCOPE: the only remaining deferral is HIGHER-ORDER / CLOSURE.  The
    value category is cartesian but not yet known to be closed in this model
    (Melliès' [!A ⊸ B] route is not pursued here); so the grammar has no
    function types.  Within the first-order fragment there is NO restriction
    on the type system anymore — products of products, products at any depth,
    arbitrary contexts are all admitted.

    **Computations and the monad.**  The CBV computation monad is the monad
    [T] induced by the adjunction [U ⊣ !̃] on the value category, [T P =
    !̃(U P) = bang_cofree (coalg_obj P)].  Its unit is [adj_unit] and Kleisli
    composition [kcomp] is built from the adjunction.  A computation
    [Γ ⊢ M : τ] denotes a Kleisli arrow [⟦Γ⟧ → T⟦τ⟧]; a value [Γ ⊢ V : τ]
    a coalgebra morphism [⟦Γ⟧ → ⟦τ⟧].  Contexts are single-variable;
    substitution is composition.

    **[sample] and probabilistic content.**  [sample] over a base space [X]
    denotes the Theorem-9.7 coalgebra structure map [Coalg X] (= the integral
    operator [µ ↦ ∫ (δ_X r)! dµ], [int_to_linhom (bang_dirac_path X)]); its
    action on a Dirac value [δ_X r] is [(δ_X r)!] ([Coalg_dirac]).  In this
    [!]-induced monad [sample] coincides with the monadic [return] on measure
    values (the unit on [FMeas X] IS the integration-of-Diracs map): a genuine
    feature of the cones model, recorded honestly ([cpD_sample_ret]).

    Contents:
    - the CBV monad [T] ([Tobj]/[tunit_eta]/[kcomp]) + its three monad laws
      ([kcomp_etaR]/[kcomp_etaL]/[kcomp_A], via [adj_phi_kcomp]);
    - the projections as coalgebra morphisms ([em_proj1]/[em_proj2]),
      UNCONDITIONAL (using [EMComon_all]);
    - the syntax: a single [ty], values [vl], computations [cp] (Rocq
      inductives, intrinsically typed);
    - the type interpretation [tyD];
    - the term interpretation [vlD]/[cpD] (TOTAL by construction);
    - the soundness core: the [let] laws ([cpD_let_retvar]/[cpD_letret]/
      [cpD_letassoc]), the product β-laws ([vlD_fst_pair]/[vlD_snd_pair]),
      and the [sample] semantics ([cpD_sample_mor]/[cpD_sample_var_dirac]/
      [cpD_sample_is_integral]). *)

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

(** ** The CBV computation monad [T] induced by [U ⊣ !̃]

    On the value category [EM(!)] the adjunction [U ⊣ !̃] of [em_cat.v]
    induces the monad [T = !̃ ∘ U] (Melliès p141: the linear-category route's
    CBV computation monad).  [T P = !̃(U P) = bang_cofree (coalg_obj P)]; the
    unit is the coalgebra structure map ([adj_unit]) and the multiplication
    is [!̃] of the counit ([der]).  This is the [!]-induced "make duplicable"
    monad; the *probabilistic* content of CBV is NOT in [T] but in [sample]
    (the Theorem-9.7 coalgebra structure), interpreted below.

    We expose Kleisli composition [kcomp] and prove the three monad laws,
    which give the [let] equations. *)
Section CBVMonad.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Bg := (@Bang R Ar).

(** [T P = !̃(U P)]. *)
Definition Tobj (P : Coalgebra Ar) : Coalgebra Ar := bang_cofree (U_obj P).

(** Functorial action [T h = !̃(U h)]. *)
Definition Tmap (P Q : Coalgebra Ar) (h : coalg_hom P Q) :
    coalg_hom (Tobj P) (Tobj Q) := bang_cofree_hom (U_mor h).

(** Unit [η_P = coalg_str P : P → T P] (= [adj_unit]). *)
Definition tunit_eta (P : Coalgebra Ar) : coalg_hom P (Tobj P) := adj_unit P.

(** Multiplication [µ_S = !̃(ε_{U S}) : T(T S) → T S]. *)
Definition tmul (S : Coalgebra Ar) : coalg_hom (Tobj (Tobj S)) (Tobj S) :=
  bang_cofree_hom (adj_counit (U_obj S)).

(** Kleisli extension [f† = µ ∘ T f : T P → T Q] for [f : P → T Q]. *)
Definition kbind (P Q : Coalgebra Ar) (f : coalg_hom P (Tobj Q)) :
    coalg_hom (Tobj P) (Tobj Q) := coalg_comp (tmul Q) (Tmap f).

(** Kleisli composition [g ⋄ f = f† ∘ g... ] — for [f : P → T Q],
    [g : Q → T S]: [kcomp g f = g† ∘ f : P → T S]. *)
Definition kcomp (P Q S : Coalgebra Ar)
    (g : coalg_hom Q (Tobj S)) (f : coalg_hom P (Tobj Q)) :
    coalg_hom P (Tobj S) := coalg_comp (kbind g) f.

(** *** The monad laws (= the CBV [let] laws)

    All three reduce, via the faithful [U] ([coalg_hom_eqP]), to the comonad
    laws of [bang.v] ([comonad_counitL]/[comonad_counitR]/[comonad_coassoc],
    [dig_nat]/[der_nat]) and the coalgebra laws of the arguments. *)

(** Right unit / left-identity Kleisli law: [kcomp f η = f].  Underlying:
    [!ε ∘ !(U f) ∘ a = !ε ∘ dig ∘ U f = U f] (coalgebra-morphism of [f] +
    [comonad_counitR]). *)
Lemma kcomp_etaR (P Q : Coalgebra Ar) (f : coalg_hom P (Tobj Q)) :
  kcomp f (tunit_eta P) = f.
Proof.
apply: coalg_hom_eqP.
rewrite /kcomp /kbind /Tmap /tmul /tunit_eta /Tobj !coalg_comp_mor /=.
have Hf := ch_is_mor f; rewrite /is_coalg_mor /= in Hf.
rewrite /adj_counit /U_mor.
rewrite -icones_compA -Hf.
rewrite icones_compA (comonad_counitR (U_obj Q)).
by rewrite icones_compIl.
Qed.

(** Left unit / right-identity Kleisli law: [kcomp η f = f].  Underlying:
    [!ε ∘ !(U η) ∘ U f = !(ε ∘ U η) ∘ U f = U f]
    (with [ε ∘ U η = adj_triangleL = id]). *)
Lemma kcomp_etaL (P Q : Coalgebra Ar) (f : coalg_hom P (Tobj Q)) :
  kcomp (tunit_eta Q) f = f.
Proof.
apply: coalg_hom_eqP.
rewrite /kcomp /kbind /Tmap /tmul /tunit_eta /Tobj !coalg_comp_mor /=.
rewrite /adj_counit /U_mor.
rewrite -(bang_fmap_comp (der (U_obj Q)) (coalg_str Q)).
have := adj_triangleL Q; rewrite /adj_phi /adj_counit /U_mor => ->.
by rewrite bang_fmap_id icones_compIl.
Qed.

(** The adjunction bijection [adj_phi] is a FUNCTOR from the Kleisli
    category of [T] to [IC]: [Φ(g ⋄ f) = Φ(g) ∘ Φ(f)] (with [Φ(η_P) = id],
    [adj_triangleL]).  Underlying: [ε ∘ !(ε∘U g) ∘ U f = (ε∘U g) ∘ (ε∘U f)]
    via [der_nat (ε∘U g)].  This is the slick engine for the monad laws:
    since [adj_phi] is a bijection ([adj_phiK]/[adj_psiK]), every Kleisli
    equation reduces to an [icones_comp] equation. *)
Lemma adj_phi_kcomp (P Q S : Coalgebra Ar)
    (g : coalg_hom Q (Tobj S)) (f : coalg_hom P (Tobj Q)) :
  adj_phi (kcomp g f) = icones_comp (adj_phi g) (adj_phi f).
Proof.
rewrite /kcomp /kbind /Tmap /tmul /adj_phi /adj_counit /U_mor !coalg_comp_mor /=.
rewrite -(bang_fmap_comp (der (U_obj S)) (ch_mor g)).
rewrite (icones_compA (der (U_obj S)) (bang_fmap (icones_comp (der (U_obj S)) (ch_mor g))) (ch_mor f)).
rewrite -(der_nat (icones_comp (der (U_obj S)) (ch_mor g))).
by rewrite -!icones_compA.
Qed.

(** [adj_phi] is injective (it is a bijection by [adj_psiK]). *)
Lemma adj_phi_inj (P : Coalgebra Ar) (B : ICone.type Ar)
    (a b : coalg_hom P (bang_cofree B)) : adj_phi a = adj_phi b -> a = b.
Proof. by move=> Hab; rewrite -(adj_psiK a) -(adj_psiK b) Hab. Qed.

(** Associativity of Kleisli composition: [kcomp (kcomp h g) f =
    kcomp h (kcomp g f)].  Immediate from [adj_phi_kcomp] + [icones_compA]
    + injectivity of [adj_phi]. *)
Lemma kcomp_A (P Q S T : Coalgebra Ar)
    (h : coalg_hom S (Tobj T)) (g : coalg_hom Q (Tobj S)) (f : coalg_hom P (Tobj Q)) :
  kcomp (kcomp h g) f = kcomp h (kcomp g f).
Proof. by apply: adj_phi_inj; rewrite !adj_phi_kcomp icones_compA. Qed.

End CBVMonad.

Arguments Tobj {R Ar} P.
Arguments Tmap {R Ar P Q} h.
Arguments tunit_eta {R Ar} P.
Arguments tmul {R Ar} S.
Arguments kbind {R Ar P Q} f.
Arguments kcomp {R Ar P Q S} g f.
Arguments adj_phi_kcomp {R Ar P Q S} g f.
Arguments adj_phi_inj {R Ar P B} a b.
Arguments kcomp_etaR {R Ar P Q} f.
Arguments kcomp_etaL {R Ar P Q} f.
Arguments kcomp_A {R Ar P Q S T} h g f.

(** ** The projections are coalgebra morphisms — UNCONDITIONAL

    Migrated to [cbv_adjunction.v] (see [em_proj1_is_mor]/[em_proj2_is_mor]
    and [em_proj1]/[em_proj2] over there).  Kept here as a historical
    cross-reference: the projections are unconditional composites of
    [m_runit_coalg_mor]/[m_lunit_coalg_mor] (the unitors as coalgebra
    morphisms) with the bifunctor action [EM_prod_mor] on [id] and
    [coalg_e] (which is unconditionally a coalgebra morphism by
    [emc_e_mor (EMComon_all _)]). *)

(** ** The CBV calculus — syntax

    A small first-order probabilistic call-by-value calculus, intrinsically
    typed by Rocq inductives.  The type system is now a SINGLE inductive
    (the rich-subcategory split is gone — every type denotes a coalgebra of
    the FULL cartesian [EM(!)]):
    - [tunit] : the unit type;
    - [tbase X] : a base type per measurable space [X];
    - [tprod s t] : binary products at any depth.

    Contexts are single-variable, of ANY type (no restriction); substitution
    is composition.  The grammar stays first-order: there are NO function /
    arrow types (the value category is not known to be closed, see the
    header). *)
Section Syntax.
Variable (R : realType) (Ar : MeasSubcat R).

Inductive ty : Type :=
  | tunit
  | tbase (X : ar_obj Ar)
  | tprod (s t : ty).

(** Values [vl Γ τ] : a value of type [τ] with one free variable of type
    [Γ]. *)
Inductive vl (G : ty) : ty -> Type :=
  | v_var : vl G G                              (* the variable [x] *)
  | v_unit : vl G tunit                         (* [()] *)
  | v_pair (s t : ty) :
      vl G s -> vl G t -> vl G (tprod s t)      (* [(V, W)] *)
  | v_fst (s t : ty) : vl G (tprod s t) -> vl G s  (* [fst V] *)
  | v_snd (s t : ty) : vl G (tprod s t) -> vl G t. (* [snd V] *)

(** Computations [cp Γ τ] : a computation of type [τ] with one free variable
    of type [Γ]. *)
Inductive cp (G : ty) : ty -> Type :=
  | c_ret (t : ty) : vl G t -> cp G t              (* [return V] *)
  | c_let (H t : ty) :                             (* [let x = M in N] *)
      cp G H -> cp H t -> cp G t
  | c_sample (X : ar_obj Ar) :                     (* [sample V] *)
      vl G (tbase X) -> cp G (tbase X).

End Syntax.

Arguments ty {R} Ar.
Arguments tunit {R Ar}.
Arguments tbase {R Ar} X.
Arguments tprod {R Ar} s t.
Arguments vl {R Ar} G t.
Arguments v_var {R Ar G}.
Arguments v_unit {R Ar G}.
Arguments v_pair {R Ar G s t} V W.
Arguments v_fst {R Ar G s t} V.
Arguments v_snd {R Ar G s t} V.
Arguments cp {R Ar} G t.
Arguments c_ret {R Ar G t} V.
Arguments c_let {R Ar G H t} M N.
Arguments c_sample {R Ar G X} V.

(** ** The interpretation of types

    Every type denotes a coalgebra of [EM(!)] by structural recursion:
    [tunit ↦ EM_term], [tbase X ↦ FMeas_coalgebra X] (the Theorem-9.7
    coalgebra), [tprod s t ↦ EM_prod (tyD s) (tyD t)].  No comonoid witness
    is threaded: every coalgebra is comonoidal by [EMComon_all]. *)
Section TypeInterp.
Variables (R : realType) (Ar : MeasSubcat R).

(** Type denotation as a coalgebra. *)
Fixpoint tyD (t : ty Ar) : Coalgebra Ar :=
  match t with
  | tunit => EM_term
  | tbase X => FMeas_coalgebra X
  | tprod s1 s2 => EM_prod (tyD s1) (tyD s2)
  end.

End TypeInterp.

Arguments tyD {R Ar} t.

(** ** The interpretation of terms

    Values denote coalgebra morphisms [⟦Γ⟧ → ⟦τ⟧] in the value category;
    computations denote Kleisli arrows [⟦Γ⟧ → T⟦τ⟧].  Both are TOTAL by
    construction (a structurally-recursive Rocq function on the intrinsically
    typed syntax), which IS the well-definedness / totality part of
    soundness. *)
Section TermInterp.
Variables (R : realType) (Ar : MeasSubcat R).

(** Value denotation [⟦Γ ⊢ V : τ⟧ : coalg_hom (tyD Γ) (tyD τ)].

    - [v_var]   ↦ identity coalgebra morphism;
    - [v_unit]  ↦ the terminal map ([em_term_mor], unconditional);
    - [v_pair]  ↦ the cartesian pairing [em_pair] (unconditional);
    - [v_fst]/[v_snd] ↦ postcompose with the projection [em_proj1]/[em_proj2]
      (unconditional coalgebra morphisms via [EMComon_all]). *)
Fixpoint vlD (G : ty Ar) (t : ty Ar) (V : vl G t) {struct V} :
    coalg_hom (tyD G) (tyD t) :=
  match V in vl _ t0 return coalg_hom (tyD G) (tyD t0) with
  | v_var => coalg_id (tyD G)
  | v_unit => em_term_mor (tyD G)
  | v_pair s t W1 W2 => em_pair (vlD W1) (vlD W2)
  | v_fst s t W => coalg_comp (em_proj1 (tyD s) (tyD t)) (vlD W)
  | v_snd s t W => coalg_comp (em_proj2 (tyD s) (tyD t)) (vlD W)
  end.

(** Computation denotation [⟦Γ ⊢ M : τ⟧ : coalg_hom (tyD Γ) (Tobj (tyD τ))]
    — a Kleisli arrow.

    - [c_ret V]   ↦ [η ∘ ⟦V⟧] (the monad unit after the value);
    - [c_let M N] ↦ Kleisli composition [kcomp ⟦N⟧ ⟦M⟧]: [⟦M⟧ : Γ ⇝ H],
      [⟦N⟧ : H ⇝ τ];
    - [c_sample V] ↦ [η_{FMeas X} ∘ ⟦V⟧], i.e. the Theorem-9.7 coalgebra
      structure [Coalg X] (= [coalg_str (FMeas_coalgebra X)] = [adj_unit])
      after the value — the integration-of-Diracs map (see [cpD_sample_dirac]
      / [cpD_sample_ret] below). *)
Fixpoint cpD (G : ty Ar) (t : ty Ar) (M : cp G t) {struct M} :
    coalg_hom (tyD G) (Tobj (tyD t)) :=
  match M in cp _ t0 return coalg_hom (tyD G) (Tobj (tyD t0)) with
  | c_ret t0 V => coalg_comp (tunit_eta (tyD t0)) (vlD V)
  | c_let H t0 N1 N2 => kcomp (cpD N2) (cpD N1)
  | c_sample X V => coalg_comp (tunit_eta (tyD (tbase X))) (vlD V)
  end.

End TermInterp.

Arguments vlD {R Ar G t} V.
Arguments cpD {R Ar G t} M.

(** ** Soundness of the interpretation

    Beyond totality (the interpretation is a total function on the
    intrinsically-typed syntax, above), we prove the compositional
    equations a CBV interpretation must satisfy:
    - the [let] laws (the monad laws, in term form);
    - the product β-laws;
    - the [sample] semantics ([= Coalg X], the integral / Dirac law). *)
Section Soundness.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

(** Definitional unfoldings of [cpD] (stated as lemmas so [rewrite] folds
    them cleanly without an aggressive [/=]). *)
Lemma cpD_retE (G : ty Ar) (t : ty Ar) (V : vl G t) :
  cpD (c_ret V) = coalg_comp (tunit_eta (tyD t)) (vlD V).
Proof. by []. Qed.

Lemma cpD_letE (G H : ty Ar) (t : ty Ar) (M : cp G H) (N : cp H t) :
  cpD (c_let M N) = kcomp (cpD N) (cpD M).
Proof. by []. Qed.

Lemma cpD_sampleE (G : ty Ar) (X : ar_obj Ar) (V : vl G (tbase X)) :
  cpD (c_sample V) = coalg_comp (tunit_eta (FMeas_coalgebra X)) (vlD V).
Proof. by []. Qed.

Lemma vlD_varE (G : ty Ar) : vlD (v_var (G := G)) = coalg_id (tyD G).
Proof. by []. Qed.

Lemma vlD_pairE (G s t : ty Ar) (V : vl G s) (W : vl G t) :
  vlD (v_pair V W) = em_pair (vlD V) (vlD W).
Proof. by []. Qed.

Lemma vlD_fstE (G s t : ty Ar) (V : vl G (tprod s t)) :
  vlD (v_fst V) = coalg_comp (em_proj1 (tyD s) (tyD t)) (vlD V).
Proof. by []. Qed.

Lemma vlD_sndE (G s t : ty Ar) (V : vl G (tprod s t)) :
  vlD (v_snd V) = coalg_comp (em_proj2 (tyD s) (tyD t)) (vlD V).
Proof. by []. Qed.

(** *** The [let] laws

    [let x = M in (return x) = M] (right unit), [let x = (return V) in N =
    N[V/x]] read as the composition [⟦N⟧ ∘ ⟦V⟧] (left unit), and
    associativity of [let] (Kleisli associativity). *)

(** Right unit: [⟦ let x = M in return x ⟧ = ⟦ M ⟧]. *)
Lemma cpD_let_retvar (G H : ty Ar) (M : cp G H) :
  cpD (c_let M (c_ret v_var)) = cpD M.
Proof.
rewrite cpD_letE cpD_retE vlD_varE coalg_compIr.
exact: kcomp_etaL.
Qed.

(** Left unit / [let]-of-[return] = substitution-as-composition:
    [⟦ let x = return V in N ⟧ = ⟦N⟧ ∘ ⟦V⟧]
    (the value [V] is substituted for [x] by precomposition). *)
Lemma cpD_letret (G H : ty Ar) (t : ty Ar)
    (V : vl G H) (N : cp H t) :
  cpD (c_let (c_ret V) N) = coalg_comp (cpD N) (vlD V).
Proof.
rewrite cpD_letE cpD_retE /kcomp.
rewrite (coalg_compA (kbind (cpD N)) (tunit_eta (tyD H)) (vlD V)).
by rewrite -/(kcomp (cpD N) (tunit_eta (tyD H))) kcomp_etaR.
Qed.

(** Associativity of [let]:
    [⟦ let y = (let x = L in M) in N ⟧ = ⟦ let x = L in (let y = M in N) ⟧]. *)
Lemma cpD_letassoc (G H K : ty Ar) (t : ty Ar)
    (L : cp G H) (M : cp H K) (N : cp K t) :
  cpD (c_let (c_let L M) N) = cpD (c_let L (c_let M N)).
Proof. by rewrite !cpD_letE kcomp_A. Qed.

(** *** The product β-laws

    [⟦ fst (V, W) ⟧ = ⟦V⟧] and [⟦ snd (V, W) ⟧ = ⟦W⟧].  Both reduce on the
    underlying maps to [em_proj1_pair]/[em_proj2_pair] of [em_cartesian.v],
    which are unconditional (only the OTHER factor's [is_coalg_mor] is
    needed; supplied by [ch_is_mor]). *)
Lemma vlD_fst_pair (G s t : ty Ar) (V : vl G s) (W : vl G t) :
  vlD (v_fst (v_pair V W)) = vlD V.
Proof.
apply: coalg_hom_eqP.
rewrite vlD_fstE vlD_pairE coalg_comp_mor.
rewrite -[ch_mor (em_proj1 (tyD s) (tyD t))]/(em_proj1_mor (tyD s) (tyD t)).
rewrite -[ch_mor (em_pair (vlD V) (vlD W))]
        /(em_pair_mor (ch_mor (vlD V)) (ch_mor (vlD W))).
exact: (em_proj1_pair (ch_is_mor (vlD W))).
Qed.

Lemma vlD_snd_pair (G s t : ty Ar) (V : vl G s) (W : vl G t) :
  vlD (v_snd (v_pair V W)) = vlD W.
Proof.
apply: coalg_hom_eqP.
rewrite vlD_sndE vlD_pairE coalg_comp_mor.
rewrite -[ch_mor (em_proj2 (tyD s) (tyD t))]/(em_proj2_mor (tyD s) (tyD t)).
rewrite -[ch_mor (em_pair (vlD V) (vlD W))]
        /(em_pair_mor (ch_mor (vlD V)) (ch_mor (vlD W))).
exact: (em_proj2_pair (ch_is_mor (vlD V))).
Qed.

(** *** The [sample] semantics

    [sample] over a base space [X] denotes the Theorem-9.7 coalgebra
    structure map [Coalg X] composed with the value:
    [⟦ sample V ⟧ = Coalg_X ∘ ⟦V⟧] (on the underlying [icones_hom]).  The
    structure map [Coalg X = coalg_str (FMeas_coalgebra X) = int_to_linhom
    (bang_dirac_path X)] IS the integral operator [µ ↦ ∫ (δ_X r)! dµ]. *)

(** The underlying map of [⟦sample V⟧] is [Coalg X ∘ ⟦V⟧]. *)
Lemma cpD_sample_mor (G : ty Ar) (X : ar_obj Ar) (V : vl G (tbase X)) :
  ch_mor (cpD (c_sample V)) = icones_comp (Coalg X) (ch_mor (vlD V)).
Proof. by rewrite cpD_sampleE coalg_comp_mor. Qed.

(** [sample] = the monad [return] on measure values: the CBV computation
    monad [T = !̃∘U] identifies "draw from a measure" with "return the
    measure as a duplicable value", because its unit on [FMeas X] IS the
    integration-of-Diracs map [Coalg X] (Theorem 9.7).  This is a genuine
    feature of the cones model, recorded honestly. *)
Lemma cpD_sample_ret (G : ty Ar) (X : ar_obj Ar) (V : vl G (tbase X)) :
  cpD (c_sample V) = cpD (c_ret V).
Proof. by []. Qed.

(** [sample] = integral, on the Dirac basis: drawing from the point mass
    [δ_X r] (the input, when [Γ = tbase X] and [V = x]) deterministically
    yields the promoted Dirac [(δ_X r)!] — Paper [Coalg_dirac].  This is the
    base case of the "draw [r ∼ µ] is an integral" identity, the precise
    sense in which [sample]'s denotation is the integration of the Dirac
    path against the measure. *)
Lemma cpD_sample_var_dirac (X : ar_obj Ar) (r : ar_carrier Ar X) :
  Lfun (ch_mor (cpD (c_sample (G := tbase X) (X := X) v_var))) (dirac_fmeas r)
    = prom (dirac_fmeas r).
Proof.
rewrite (cpD_sample_mor (G := tbase X) v_var) vlD_varE.
rewrite -[ch_mor (coalg_id (tyD (tbase X)))]/(icones_id Ar (FMeas X)).
rewrite -[Lfun (icones_comp (Coalg X) (icones_id Ar (FMeas X))) (dirac_fmeas r)]
        /(Lfun (Coalg X) (Lfun (icones_id Ar (FMeas X)) (dirac_fmeas r))).
exact: (Coalg_dirac X r).
Qed.

(** [Coalg X] is literally the integral operator [int_to_linhom
    (bang_dirac_path X)] of Theorem 6.1 — so [⟦sample⟧] integrates the
    promoted Dirac path [r ↦ (δ_X r)!] against the measure value. *)
Lemma cpD_sample_is_integral (X : ar_obj Ar) :
  ch_mor (tunit_eta (FMeas_coalgebra X)) = Coalg X.
Proof. by []. Qed.

End Soundness.

Arguments cpD_let_retvar {R Ar G H} M.
Arguments cpD_letret {R Ar G H t} V N.
Arguments cpD_letassoc {R Ar G H K t} L M N.
Arguments vlD_fst_pair {R Ar G s t} V W.
Arguments vlD_snd_pair {R Ar G s t} V W.
Arguments cpD_sample_mor {R Ar G X} V.
Arguments cpD_sample_ret {R Ar G X} V.
Arguments cpD_sample_var_dirac {R Ar X} r.
Arguments cpD_sample_is_integral {R Ar} X.

(** ** A worked example program

    The program [Γ = x : tbase X ⊢  let y = sample x in return (y, ()) :
    tprod (tbase X) tunit].  It samples the input measure [x] and pairs the
    result with the unit.  This exercises [sample], [let]-sequencing, pairing,
    and the unit value in one well-typed term, and its denotation is total
    (a coalgebra morphism), computed by [cpD]. *)
Section Example.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (X : ar_obj Ar).

Definition ex_prog : cp (tbase X) (tprod (tbase X) tunit) :=
  c_let (c_sample v_var) (c_ret (v_pair v_var v_unit)).

(** It denotes a (total) Kleisli arrow
    [FMeas X → T (EM_prod (FMeas X) EM_term)]. *)
Definition ex_denot :
    coalg_hom (tyD (tbase X)) (Tobj (tyD (tprod (tbase X) tunit))) :=
  cpD ex_prog.

(** Since [sample x] denotes [η ∘ ⟦x⟧] (the [!]-monad identifies it with
    [return x], [cpD_sample_ret]), the program reduces by the left-unit law
    to the continuation composed with the value [x] (= [id]): the denotation
    is the continuation pairing-with-unit, precomposed with the sample
    structure. *)
Lemma ex_denot_E :
  ex_denot =
  coalg_comp (cpD (c_ret (v_pair (v_var (G := tbase X)) v_unit)))
             (vlD (v_var (G := tbase X))).
Proof.
rewrite /ex_denot /ex_prog cpD_letE (cpD_sample_ret v_var) -cpD_letE.
exact: (cpD_letret v_var (c_ret (v_pair v_var v_unit))).
Qed.

End Example.

Arguments ex_prog {R Ar} X.
Arguments ex_denot {R Ar} X.
