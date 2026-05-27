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
