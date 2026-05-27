(**md**************************************************************************)
(** * A small first-order call-by-value calculus, interpreted in [ICones_CBV] — CBV §5

    Step 5 of the call-by-value roadmap
    ([/home/rocq/prime_gap/icones-cbv-plan.md], Part 7).  We define a small
    *probabilistic* call-by-value (CBV) calculus and interpret it in the CBV
    model [ICones_CBV] of [cbv_adjunction.v], demonstrating that the model
    actually interprets a probabilistic CBV language.

    **The fragment interpreted (stated honestly).**  This is the *first-order*
    fragment (option (a) of the design guidance), the guaranteed core: a base
    type per measurable space, a unit type, binary products, [let]-sequencing,
    [return], and [sample].  Function/arrow types are NOT interpreted — the
    value category is cartesian but NOT closed (step 3 deferred closure, and
    [EMComon] is not closed under products), so a value-CCC is unavailable;
    we make no closure claim.

    **The semantic domain (the value category).**  Value types denote objects
    of the *cartesian rich subcategory* of [EM(!)]: a [Coalgebra Ar] bundled
    with its [EMComon] witness ([vtype] below).  The generators are the
    Theorem-9.7 coalgebras [FMeas X] ([EMComon_FMeas]); the unit type denotes
    the terminal coalgebra [EM_term] and products the [EM_prod] of carriers.
    For unit and products to live in the rich subcategory we prove the two
    missing comonoidality facts [EMComon_term] and [EMComon_prod] here (the
    [d_A]/[e_A]-are-coalgebra-morphism step that Melliès flags as Cor 20 — we
    discharge it on the rich generators via the comonoid-morphism lemmas
    [coalg_mor_d]/[coalg_mor_e] of [em_cartesian.v], which ARE general).

    **Computations and the monad.**  The CBV computation monad is the monad
    [T] induced by the adjunction [U ⊣ !̃] on the value category, [T P =
    !̃(U P) = bang_cofree (coalg_obj P)].  Its unit is [adj_unit] and Kleisli
    extension is built from the adjunction bijection [adj_phi]/[adj_psi].  A
    computation [Γ ⊢ M : τ] denotes a coalgebra morphism [⟦Γ⟧ → T⟦τ⟧];
    a value [Γ ⊢ V : τ] a coalgebra morphism [⟦Γ⟧ → ⟦τ⟧].  Contexts are
    single-variable (one free variable of a value type); substitution is
    composition.

    **[sample] and probabilistic content.**  [sample] over a base space [X]
    denotes the Theorem-9.7 coalgebra structure map [Coalg X] (= the integral
    operator [µ ↦ ∫ (δ_X r)! dµ], [int_to_linhom (bang_dirac_path X)]); its
    action on a Dirac value [δ_X r] is [(δ_X r)!] ([Coalg_dirac]), and the
    equational engine is [dirac_dense].

    Contents:
    - the syntax: types [vty], values [vl], computations [cp], typing as
      Rocq inductives;
    - the type interpretation [tyD] into the rich subcategory [vtype];
    - the term interpretation [vlD]/[cpD] as coalgebra morphisms;
    - the soundness core: totality (by construction), the monad/[let] laws,
      the product β-laws, and the [sample] = integral statement. *)

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

(** ** Comonoidality of the terminal coalgebra [EM_term] (a missing generator)

    [em_cartesian.v] proved [EMComon] for the cofree coalgebras [!̃B]
    ([EMComon_cofree]) and for the Theorem-9.7 coalgebras [FMeas X]
    ([EMComon_FMeas]), but NOT for the terminal [EM_term].  We supply it
    here so that the CBV unit type [tunit] lives in the cartesian rich
    subcategory.  Like the two existing witnesses, every field reduces on
    the SPANNING point [one1] of the unit cone via the [one_ext]
    extensionality engine ([em_seely_comonoid.v]); on [one1] the Eq-88
    comonoid maps compute to [coalg_d(one1) = one1⊗one1] and
    [coalg_e(one1) = one1]. *)
Section TerminalComonoidal.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation "B '⊗' C" := (tensor Ar B C)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '!'" := (prom x) (at level 2, format "x '!'").
Local Notation ET := (EM_term : Coalgebra Ar).

(** [coalg_d EM_term (one1) = one1 ⊗ one1]. *)
Lemma coalg_d_EMterm_one1 : Lfun (coalg_d ET) one1 = one1 ⊗p one1.
Proof.
have H1 : cone_norm (one1 : cone_one_car Ar) <= 1.
  by rewrite (_ : cone_norm one1 = 1) // /cone_norm /= /c1_norm.
rewrite /coalg_d.
rewrite (@Lfun_comp _ _ _ _ _ (tensor_mor (der (coalg_obj ET)) (der (coalg_obj ET)))
          (icones_comp (d_bang (coalg_obj ET)) (coalg_str ET)) one1).
rewrite (@Lfun_comp _ _ _ _ _ (d_bang (coalg_obj ET)) (coalg_str ET) one1).
rewrite -[coalg_str ET]/(unit_cofree_str) unit_cofree_str_one1.
rewrite (d_bang_prom (A := coalg_obj ET) one1 H1).
rewrite (tensor_morE (der (coalg_obj ET)) (der (coalg_obj ET)) one1! one1!).
by rewrite (der_prom (B := coalg_obj ET) one1 H1).
Qed.

(** [coalg_e EM_term (one1) = one1] (indeed [coalg_e EM_term = id]). *)
Lemma coalg_e_EMterm_one1 : Lfun (coalg_e ET) one1 = one1.
Proof. by rewrite (coalg_e_term (R := R) (Ar := Ar)). Qed.

Lemma EMComon_term : EMComon ET.
Proof.
have D := coalg_d_EMterm_one1.
have E := coalg_e_EMterm_one1.
have H1 : cone_norm (one1 : cone_one_car Ar) <= 1.
  by rewrite (_ : cone_norm one1 = 1) // /cone_norm /= /c1_norm.
have idd : Lfun (icones_id Ar (coalg_obj ET)) one1 = one1 by [].
apply: MkEMComon.
- (* coassociativity: both sides on [one1] give [one1 ⊗ (one1 ⊗ one1)]. *)
  apply: one_ext.
  rewrite (@Lfun_comp _ _ _ _ _ (iso_fwd (tensor_assoc (coalg_obj ET) (coalg_obj ET) (coalg_obj ET)))
            (icones_comp (tensor_mor (coalg_d ET) (icones_id Ar (coalg_obj ET))) (coalg_d ET)) one1).
  rewrite (@Lfun_comp _ _ _ _ _ (tensor_mor (coalg_d ET) (icones_id Ar (coalg_obj ET)))
            (coalg_d ET) one1).
  rewrite D (tensor_morE (coalg_d ET) (icones_id Ar (coalg_obj ET)) one1 one1).
  rewrite D idd tensor_assocEp.
  rewrite (@Lfun_comp _ _ _ _ _ (tensor_mor (icones_id Ar (coalg_obj ET)) (coalg_d ET))
            (coalg_d ET) one1).
  rewrite D (tensor_morE (icones_id Ar (coalg_obj ET)) (coalg_d ET) one1 one1).
  by rewrite idd D.
- (* left counit: [λ ((e⊗id)(one1⊗one1)) = λ(one1⊗one1) = one1]. *)
  apply: one_ext.
  rewrite (@Lfun_comp _ _ _ _ _ (iso_fwd (tensor_lunit (coalg_obj ET)))
            (icones_comp (tensor_mor (coalg_e ET) (icones_id Ar (coalg_obj ET))) (coalg_d ET)) one1).
  rewrite (@Lfun_comp _ _ _ _ _ (tensor_mor (coalg_e ET) (icones_id Ar (coalg_obj ET)))
            (coalg_d ET) one1).
  rewrite D (tensor_morE (coalg_e ET) (icones_id Ar (coalg_obj ET)) one1 one1).
  rewrite E idd tensor_lunitEp.
  by rewrite [c1_val one1]/= precone_scale_1.
- (* right counit: symmetric. *)
  apply: one_ext.
  rewrite (@Lfun_comp _ _ _ _ _ (iso_fwd (tensor_runit (coalg_obj ET)))
            (icones_comp (tensor_mor (icones_id Ar (coalg_obj ET)) (coalg_e ET)) (coalg_d ET)) one1).
  rewrite (@Lfun_comp _ _ _ _ _ (tensor_mor (icones_id Ar (coalg_obj ET)) (coalg_e ET))
            (coalg_d ET) one1).
  rewrite D (tensor_morE (icones_id Ar (coalg_obj ET)) (coalg_e ET) one1 one1).
  rewrite E idd tensor_runitEp.
  by rewrite [c1_val one1]/= precone_scale_1.
- (* cocommutativity: [σ(one1⊗one1) = one1⊗one1]. *)
  apply: one_ext.
  rewrite (@Lfun_comp _ _ _ _ _ (iso_fwd (tensor_braid (coalg_obj ET) (coalg_obj ET)))
            (coalg_d ET) one1).
  by rewrite D tensor_braidEp.
- (* [coalg_d] is a coalgebra morphism [EM_term → EM_prod EM_term EM_term].
     On [one1]: LHS [s(one1⊗one1) = m(one1!⊗one1!) = (one1⊗one1)!];
     RHS [!(coalg_d)(one1!) = (coalg_d one1)! = (one1⊗one1)!]. *)
  rewrite /is_coalg_mor EM_prod_str_E /EM_prod_str.
  apply: one_ext.
  rewrite (@Lfun_comp _ _ _ _ _ (icones_comp (m_bang (coalg_obj ET) (coalg_obj ET))
             (tensor_mor (coalg_str ET) (coalg_str ET))) (coalg_d ET) one1).
  rewrite D.
  rewrite (@Lfun_comp _ _ _ _ _ (m_bang (coalg_obj ET) (coalg_obj ET))
             (tensor_mor (coalg_str ET) (coalg_str ET)) (one1 ⊗p one1)).
  rewrite (tensor_morE (coalg_str ET) (coalg_str ET) one1 one1).
  rewrite -[coalg_str ET]/(unit_cofree_str) unit_cofree_str_one1.
  rewrite (m_bang_prom (A := coalg_obj ET) (B := coalg_obj ET) (x := one1) (y := one1) H1 H1).
  rewrite (@Lfun_comp _ _ _ _ _ (bang_fmap (coalg_d ET)) (coalg_str ET) one1).
  rewrite -[coalg_str ET]/(unit_cofree_str) unit_cofree_str_one1.
  rewrite (bang_fmap_prom (coalg_d ET) one1 H1).
  by rewrite D.
- (* [coalg_e] is a coalgebra morphism [EM_term → EM_term]; as [coalg_e EM_term
     = id], this is [coalg_mor_id]. *)
  rewrite (coalg_e_term (R := R) (Ar := Ar)).
  exact: (coalg_mor_id ET).
Qed.

End TerminalComonoidal.

Arguments coalg_d_EMterm_one1 {R Ar}.
Arguments coalg_e_EMterm_one1 {R Ar}.
Arguments EMComon_term {R Ar}.

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

(** ** The projections are coalgebra morphisms (when the discarded factor is
    comonoidal)

    [em_cartesian.v] exposes the projections [em_proj1_mor]/[em_proj2_mor] as
    plain [icones_hom] (the β-laws are stated at that level).  To use them in
    the value category we package them as coalgebra morphisms: when the
    discarded factor is comonoidal ([EMComon]), the projection
    [ρ ∘ (id ⊗ coalg_e)] is a composite of coalgebra morphisms — the unitor
    [m_runit_coalg_mor]/[m_lunit_coalg_mor] of [cbv_adjunction.v] and the
    bifunctor action [EM_prod_mor] on [id] and the comonoid counit
    [emc_e_mor]. *)
Section Projections.
Variables (R : realType) (Ar : MeasSubcat R).

Lemma em_proj1_is_mor (P Q : Coalgebra Ar) (hQ : EMComon Q) :
  is_coalg_mor (EM_prod P Q) P (em_proj1_mor P Q).
Proof.
rewrite /em_proj1_mor.
apply: (coalg_mor_comp (P := EM_prod P Q) (Q := EM_prod P EM_term) (S := P)).
- exact: (m_runit_coalg_mor P).
- apply: (EM_prod_mor (P':=P) (Q':=EM_term) (icones_id Ar (coalg_obj P)) (coalg_e Q)).
  + exact: (coalg_mor_id P).
  + exact: (emc_e_mor hQ).
Qed.

Lemma em_proj2_is_mor (P Q : Coalgebra Ar) (hP : EMComon P) :
  is_coalg_mor (EM_prod P Q) Q (em_proj2_mor P Q).
Proof.
rewrite /em_proj2_mor.
apply: (coalg_mor_comp (P := EM_prod P Q) (Q := EM_prod EM_term Q) (S := Q)).
- exact: (m_lunit_coalg_mor Q).
- apply: (EM_prod_mor (P':=EM_term) (Q':=Q) (coalg_e P) (icones_id Ar (coalg_obj Q))).
  + exact: (emc_e_mor hP).
  + exact: (coalg_mor_id Q).
Qed.

(** The bundled projection coalgebra morphisms. *)
Definition em_proj1 (P Q : Coalgebra Ar) (hQ : EMComon Q) :
    coalg_hom (EM_prod P Q) P := MkCoalgHom (em_proj1_is_mor P hQ).

Definition em_proj2 (P Q : Coalgebra Ar) (hP : EMComon P) :
    coalg_hom (EM_prod P Q) Q := MkCoalgHom (em_proj2_is_mor Q hP).

End Projections.

Arguments em_proj1_is_mor {R Ar} P {Q} hQ.
Arguments em_proj2_is_mor {R Ar P} Q hP.
Arguments em_proj1 {R Ar} P {Q} hQ.
Arguments em_proj2 {R Ar P} Q hP.

(** ** The CBV calculus — syntax

    A small first-order probabilistic call-by-value calculus, intrinsically
    typed by Rocq inductives.  We separate two grammars:
    - *comonoidal context types* [cty] — the types that carry [EMComon] and so
      may be the type of the (single) free variable / [let]-bound variable:
      the unit [cunit] and a base type [cbase X] per measurable space [X];
    - *value types* [vty] — a comonoidal type [vcty G], or a binary PRODUCT
      [vprod G H] of two comonoidal types.  (Products themselves are NOT
      comonoidal — [EMComon] is not closed under [EM_prod], step 3 open — so a
      product is a value type but never a context type; this is the honest
      first-order restriction.)

    Contexts are single-variable; substitution is composition.  The grammar
    deliberately stays first-order: there are NO function/arrow types (the
    value category is cartesian but NOT closed, see the file header). *)
Section Syntax.
Variable (R : realType) (Ar : MeasSubcat R).

Inductive cty : Type :=
  | cunit
  | cbase (X : ar_obj Ar).

Inductive vty : Type :=
  | vcty (G : cty)
  | vprod (G H : cty).

(** Values [vl Γ τ] : a value of type [τ] with one free variable of
    comonoidal type [Γ]. *)
Inductive vl (G : cty) : vty -> Type :=
  | v_var : vl G (vcty G)                              (* the variable [x] *)
  | v_unit : vl G (vcty cunit)                         (* [()] *)
  | v_pair (H K : cty) :
      vl G (vcty H) -> vl G (vcty K) -> vl G (vprod H K)  (* [(V, W)] *)
  | v_fst (H K : cty) : vl G (vprod H K) -> vl G (vcty H)  (* [fst V] *)
  | v_snd (H K : cty) : vl G (vprod H K) -> vl G (vcty K). (* [snd V] *)

(** Computations [cp Γ τ] : a computation of type [τ] with one free variable
    of comonoidal type [Γ]. *)
Inductive cp (G : cty) : vty -> Type :=
  | c_ret (t : vty) : vl G t -> cp G t                   (* [return V] *)
  | c_let (H : cty) (t : vty) :                          (* [let x = M in N] *)
      cp G (vcty H) -> cp H t -> cp G t
  | c_sample (X : ar_obj Ar) :                           (* [sample V] *)
      vl G (vcty (cbase X)) -> cp G (vcty (cbase X)).

End Syntax.

Arguments cty {R} Ar.
Arguments vty {R} Ar.
Arguments cunit {R Ar}.
Arguments cbase {R Ar} X.
Arguments vcty {R Ar} G.
Arguments vprod {R Ar} G H.
Arguments vl {R Ar} G t.
Arguments v_var {R Ar G}.
Arguments v_unit {R Ar G}.
Arguments v_pair {R Ar G H K} V W.
Arguments v_fst {R Ar G H K} V.
Arguments v_snd {R Ar G H K} V.
Arguments cp {R Ar} G t.
Arguments c_ret {R Ar G t} V.
Arguments c_let {R Ar G H t} M N.
Arguments c_sample {R Ar G X} V.

(** ** The interpretation of types

    Comonoidal context types denote the rich-subcategory generators
    ([EM_term], [FMeas_coalgebra X]); value types denote their carriers and
    [EM_prod]s.  [ctyComon] supplies the [EMComon] witness for every context
    type (using [EMComon_term] of this file and [EMComon_FMeas] of
    [em_cartesian.v]). *)
Section TypeInterp.
Variables (R : realType) (Ar : MeasSubcat R).

(** Context-type denotation, as a comonoidal coalgebra. *)
Definition ctyD (G : cty Ar) : Coalgebra Ar :=
  match G with
  | cunit => EM_term
  | cbase X => FMeas_coalgebra X
  end.

Definition ctyComon (G : cty Ar) : EMComon (ctyD G) :=
  match G with
  | cunit => EMComon_term
  | cbase X => EMComon_FMeas X
  end.

(** Value-type denotation. *)
Definition vtyD (t : vty Ar) : Coalgebra Ar :=
  match t with
  | vcty G => ctyD G
  | vprod G H => EM_prod (ctyD G) (ctyD H)
  end.

(** A [vcty]-type denotes the same coalgebra as its context type (so the
    variable rule [v_var : vl G (vcty G)] is [id] on [ctyD G]). *)
Lemma vtyD_vcty (G : cty Ar) : vtyD (vcty G) = ctyD G.
Proof. by []. Qed.

End TypeInterp.

Arguments ctyD {R Ar} G.
Arguments ctyComon {R Ar} G.
Arguments vtyD {R Ar} t.

(** ** The interpretation of terms

    Values denote coalgebra morphisms [⟦Γ⟧ → ⟦τ⟧] in the value category;
    computations denote Kleisli arrows [⟦Γ⟧ → T⟦τ⟧].  Both are TOTAL by
    construction (a structurally-recursive Rocq function on the intrinsically
    typed syntax), which IS the well-definedness / totality part of
    soundness. *)
Section TermInterp.
Variables (R : realType) (Ar : MeasSubcat R).

(** Value denotation [⟦Γ ⊢ V : τ⟧ : coalg_hom (ctyD Γ) (vtyD τ)].

    - [v_var]   ↦ identity coalgebra morphism;
    - [v_unit]  ↦ the terminal map ([em_term_mor]);
    - [v_pair]  ↦ the cartesian pairing [em_pair] (domain [ctyD G] comonoidal);
    - [v_fst]/[v_snd] ↦ postcompose with the projection [em_proj1]/[em_proj2]
      (a coalgebra morphism since the discarded factor [ctyD K]/[ctyD H] is
      comonoidal). *)
Fixpoint vlD (G : cty Ar) (t : vty Ar) (V : vl G t) {struct V} :
    coalg_hom (ctyD G) (vtyD t) :=
  match V in vl _ t0 return coalg_hom (ctyD G) (vtyD t0) with
  | v_var => coalg_id (ctyD G)
  | v_unit => em_term_mor (ctyComon G)
  | v_pair H K W1 W2 => em_pair (ctyComon G) (vlD W1) (vlD W2)
  | v_fst H K W => coalg_comp (em_proj1 (ctyD H) (ctyComon K)) (vlD W)
  | v_snd H K W => coalg_comp (em_proj2 (ctyD K) (ctyComon H)) (vlD W)
  end.

(** Computation denotation [⟦Γ ⊢ M : τ⟧ : coalg_hom (ctyD Γ) (Tobj (vtyD τ))]
    — a Kleisli arrow.

    - [c_ret V]   ↦ [η ∘ ⟦V⟧] (the monad unit after the value);
    - [c_let M N] ↦ Kleisli composition [kcomp ⟦N⟧ ⟦M⟧]: [⟦M⟧ : Γ ⇝ H],
      [⟦N⟧ : H ⇝ τ];
    - [c_sample V] ↦ [η_{FMeas X} ∘ ⟦V⟧], i.e. the Theorem-9.7 coalgebra
      structure [Coalg X] (= [coalg_str (FMeas_coalgebra X)] = [adj_unit])
      after the value — the integration-of-Diracs map (see [cpD_sample_dirac]
      / [cpD_sample_ret] below). *)
Fixpoint cpD (G : cty Ar) (t : vty Ar) (M : cp G t) {struct M} :
    coalg_hom (ctyD G) (Tobj (vtyD t)) :=
  match M in cp _ t0 return coalg_hom (ctyD G) (Tobj (vtyD t0)) with
  | c_ret t0 V => coalg_comp (tunit_eta (vtyD t0)) (vlD V)
  | c_let H t0 N1 N2 => kcomp (cpD N2) (cpD N1)
  | c_sample X V => coalg_comp (tunit_eta (vtyD (vcty (cbase X)))) (vlD V)
  end.

End TermInterp.

Arguments vlD {R Ar G t} V.
Arguments cpD {R Ar G t} M.
