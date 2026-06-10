(**md**************************************************************************)
(** * The monoidal adjunction [U ⊣ !̃] and the CBV model — CBV §4

    *** CBV LNL adjunction + extensions

    This file provides:
    - The LNL adjunction [U ⊣ !̃ : EM(!) ⇄ ICones] (Mellies §7.4 recipe,
      beyond the paper proper).
    - The cartesian-η identity [em_pair_mor_proj_id] (Fox 1976 /
      Mellies Prop 28 at the icones level — a corollary of paper §9's
      Cor 20 / [EMComon_all], exposed at the unbundled icones API).
    - [em_proj1/2_is_mor] : projections are coalg morphisms (uses
      [m_runit/lunit_coalg_mor]).

    Used by [theories/programs/cbv.v] (Moggi-CBV) and
    [theories/programs/ppl.v] (direct-style CBV PPL).

    ---

    Step 4 of the call-by-value roadmap
    ([/home/rocq/prime_gap/icones-cbv-plan.md], Phase D1; Melliès §7.4
    Proposition 29, via Lack's lifting §6.10).  We package the
    (lax symmetric) monoidal adjunction
      [U ⊣ !̃] : [(EM(!), EM_prod, EM_term) ⇄ (ICones, ⊗, 1)]
    between the forgetful functor [U] and the cofree functor [!̃] of
    [em_cat.v], with the monoidal structures of [smcc.v] (on [ICones]) and
    [em_cartesian.v] (the lifted [⊗] on [EM(!)]).  Together with the
    cartesian structure on the FULL [EM(!)] ([em_cartesian.v]'s
    [ICones_EM_cartesian], cartesian for ALL coalgebras by [EMComon_all])
    this is the CBV/LNL data.

    This is mostly ASSEMBLY of pieces that already exist, with one genuine
    block of new content: the lax-monoidal coherence of [!̃] at the
    [m_bang]-level (the associativity / unit / symmetry hexagons of the
    comparison map [m_bang]), proved on promoted points by the
    [tens_excl_charact]/[tens_excl_charact3l] engine + [m_bang_prom] + the
    structural-iso [...Ep] laws, exactly as [seely.v]/[em_seely_comonoid.v]
    discharge their coherence diagrams.

    Scope:
    - The monoidal ADJUNCTION [U ⊣ !̃] is over the FULL [EM(!)] (it needs no
      cartesianness).  The cartesian "value category" is the FULL [EM(!)]
      itself — every [!]-coalgebra carries the transported commutative
      comonoid ([EMComon_all]), so [(EM(!), ⊗, 1)] is cartesian (Melliès
      Prop 28), NOT merely a rich subcategory.  In particular the cofree
      coalgebras [!̃B] and the Theorem-9.7 coalgebras [FMeas X] are objects
      of this cartesian category, but no subcategory restriction is needed.

    Contents:
    - the [m_bang] coherence lemmas (NEW): [m_bang_assoc] (associativity),
      [m_bang_lunit]/[m_bang_runit] (unitors), [m_bang_braid] (symmetry).
    - [U] is STRONG symmetric monoidal: the comparison maps are identities
      ([U_phi2]/[U_phi0] definitional), and the associator/unitor/braiding
      of [EM(!)] are carried by the [ICones] ones ([m_assoc_coalg_mor] etc.),
      so [U] preserves them strictly ([U_strong_assoc] etc.).
    - [!̃] is LAX symmetric monoidal: the comparison coalgebra morphism
      [bang_m : EM_prod (!̃A)(!̃B) → !̃(A⊗B)] (= [m_bang] packaged) and unit
      [bang_e0 : EM_term → !̃1] (= [unit_cofree_str] packaged), with the
      lax coherence [bang_lax_assoc]/[bang_lax_lunit]/[bang_lax_runit]/
      [bang_lax_braid].
    - the MONOIDAL ADJUNCTION: the counit [der] is monoidal
      ([adj_counit_monoidal2]/[adj_counit_monoidal0]) and the unit
      [coalg_str] is monoidal ([adj_unit_monoidal2]/[adj_unit_monoidal0]).
    - the bundle [CBV_Model] + the witness [ICones_CBV Ar]. *)

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

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

(** Seal the tensor/Seely/comonad data exactly as [em_cartesian.v] does, so
    a bare [/=] does not unfold the [tensor_construct]/[lin]/[scones]
    internals (which would break the [...Ep]/[_prom] rewrites and diverge).
    The [...E]/[_prom] equational lemmas still rewrite (opacity never blocks
    rewriting WITH an equation). *)
Opaque tensor_mor tensor_assoc tensor_lunit tensor_runit tensor_braid
       ptensor tau Seely2.
Opaque dig der prom bang_fmap d_bang e_bang unit_cofree_str Coalg
       tens_cofree_str m_bang.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section CBVAdjunction.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

Local Notation "B '⊗' C" := (tensor Ar B C)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '!'" := (prom x) (at level 2, format "x '!'").
Local Notation Bg := (@Bang R Ar).

(** ** The lax-monoidal coherence of [m_bang] — the genuine new content

    [m_bang] makes [(!, m_bang, e0)] a LAX SYMMETRIC MONOIDAL endofunctor of
    [(⊗,1)].  We discharge the three coherence hexagons on promoted points
    using the [tens_excl_charact*] engine + [m_bang_prom] + the structural
    iso [...Ep] laws. *)

(** Associativity of [m]:
      [!(α) ∘ m_{A⊗B,C} ∘ (m_{A,B} ⊗ id) = m_{A,B⊗C} ∘ (id ⊗ m_{B,C}) ∘ α].
    On [(x!⊗y!)⊗z!] both sides give [(x⊗(y⊗z))!]. *)
Lemma m_bang_assoc (A B C : ICone.type Ar) :
  icones_comp (bang_fmap (iso_fwd (tensor_assoc A B C)))
    (icones_comp (m_bang (A ⊗ B) C)
       (tensor_mor (m_bang A B) (icones_id Ar (Bg C)))) =
  icones_comp (m_bang A (B ⊗ C))
    (icones_comp (tensor_mor (icones_id Ar (Bg A)) (m_bang B C))
       (iso_fwd (tensor_assoc (Bg A) (Bg B) (Bg C)))).
Proof.
apply: tens_excl_charact3l => x y z Hx Hy Hz.
have Hxy : cone_norm (x ⊗p y) <= 1 by exact: ptensor_prom_ball.
have Hyz : cone_norm (y ⊗p z) <= 1 by exact: ptensor_prom_ball.
(* LHS *)
rewrite (@Lfun_comp _ _ _ _ _ (bang_fmap (iso_fwd (tensor_assoc A B C)))
          (icones_comp (m_bang (A ⊗ B) C)
             (tensor_mor (m_bang A B) (icones_id Ar (Bg C)))) ((x! ⊗p y!) ⊗p z!)).
rewrite (@Lfun_comp _ _ _ _ _ (m_bang (A ⊗ B) C)
          (tensor_mor (m_bang A B) (icones_id Ar (Bg C))) ((x! ⊗p y!) ⊗p z!)).
rewrite (tensor_morE (m_bang A B) (icones_id Ar (Bg C)) (x! ⊗p y!) z!).
rewrite (m_bang_prom Hx Hy).
have idC : Lfun (icones_id Ar (Bg C)) z! = z! by [].
rewrite idC (m_bang_prom Hxy Hz).
rewrite (bang_fmap_prom (iso_fwd (tensor_assoc A B C)) ((x ⊗p y) ⊗p z)
          (ptensor_prom_ball Hxy Hz)).
rewrite tensor_assocEp.
(* RHS *)
rewrite (@Lfun_comp _ _ _ _ _ (m_bang A (B ⊗ C))
          (icones_comp (tensor_mor (icones_id Ar (Bg A)) (m_bang B C))
             (iso_fwd (tensor_assoc (Bg A) (Bg B) (Bg C)))) ((x! ⊗p y!) ⊗p z!)).
rewrite (@Lfun_comp _ _ _ _ _ (tensor_mor (icones_id Ar (Bg A)) (m_bang B C))
          (iso_fwd (tensor_assoc (Bg A) (Bg B) (Bg C))) ((x! ⊗p y!) ⊗p z!)).
rewrite tensor_assocEp.
rewrite (tensor_morE (icones_id Ar (Bg A)) (m_bang B C) x! (y! ⊗p z!)).
have idA : Lfun (icones_id Ar (Bg A)) x! = x! by [].
rewrite idA (m_bang_prom Hy Hz).
by rewrite (m_bang_prom Hx Hyz).
Qed.

(** Left unit of [m]:
      [!(λ) ∘ m_{1,A} ∘ (e0 ⊗ id) = λ]   (with [e0 = unit_cofree_str]).
    On [u!⊗x!] (where [u : 1], [x : A]):
      LHS [!λ(m(e0(u!)⊗x!))]; since [e0(u!)] is not promoted directly we
    instead read the unit via [EM_term].  This is the [unit_cofree_str]
    half — its underlying point is delicate, so we phrase the unitors at the
    [EM_term] level below ([bang_lax_lunit]). *)

(** Symmetry of [m]: [!(σ) ∘ m_{A,B} = m_{B,A} ∘ σ].
    On [x!⊗y!]: LHS [!σ(m(x!⊗y!)) = !σ((x⊗y)!) = (σ(x⊗y))! = (y⊗x)!];
    RHS [m_{B,A}(σ(x!⊗y!)) = m_{B,A}(y!⊗x!) = (y⊗x)!]. *)
Lemma m_bang_braid (A B : ICone.type Ar) :
  icones_comp (bang_fmap (iso_fwd (tensor_braid A B))) (m_bang A B) =
  icones_comp (m_bang B A) (iso_fwd (tensor_braid (Bg A) (Bg B))).
Proof.
apply: tens_excl_charact => x y Hx Hy.
(* LHS *)
rewrite (@Lfun_comp _ _ _ _ _ (bang_fmap (iso_fwd (tensor_braid A B)))
          (m_bang A B) (x! ⊗p y!)).
rewrite (m_bang_prom Hx Hy).
rewrite (bang_fmap_prom (iso_fwd (tensor_braid A B)) (x ⊗p y)
          (ptensor_prom_ball Hx Hy)).
rewrite tensor_braidEp.
(* RHS *)
rewrite (@Lfun_comp _ _ _ _ _ (m_bang B A) (iso_fwd (tensor_braid (Bg A) (Bg B)))
          (x! ⊗p y!)).
rewrite tensor_braidEp.
by rewrite (m_bang_prom Hy Hx).
Qed.

End CBVAdjunction.

Arguments m_bang_assoc {R Ar} A B C.
Arguments m_bang_braid {R Ar} A B.

Section CBVAdjunctionUnit.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation "B '⊗' C" := (tensor Ar B C)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '!'" := (prom x) (at level 2, format "x '!'").
Local Notation Bg := (@Bang R Ar).

(** Left unit of [m] at the [unit_cofree_str] comparison:
      [!(λ^⊗_A) ∘ m_{1,A} ∘ (e0 ⊗ id) = λ^⊗_{!A}]   (as maps [1 ⊗ !A → !A]).
    On [1 ⊗ x!]: [(e0⊗id)(1⊗x!) = 1! ⊗ x!], [m(1!⊗x!) = (1⊗x)!],
    [!λ((1⊗x)!) = (λ(1⊗x))! = (1·x)! = x!]; RHS [λ(1⊗x!) = 1·x! = x!]. *)
Lemma m_bang_lunit (A : ICone.type Ar) :
  icones_comp (bang_fmap (iso_fwd (tensor_lunit A)))
    (icones_comp (m_bang (cone_one_car Ar) A)
       (tensor_mor unit_cofree_str (icones_id Ar (Bg A)))) =
  iso_fwd (tensor_lunit (Bg A)).
Proof.
apply: tens_excl_unitL => x Hx.
have H1 : cone_norm (one1 : cone_one_car Ar) <= 1.
  by rewrite (_ : cone_norm one1 = 1) // /cone_norm /= /c1_norm.
(* LHS *)
rewrite (@Lfun_comp _ _ _ _ _ (bang_fmap (iso_fwd (tensor_lunit A)))
          (icones_comp (m_bang (cone_one_car Ar) A)
             (tensor_mor unit_cofree_str (icones_id Ar (Bg A)))) (one1 ⊗p x!)).
rewrite (@Lfun_comp _ _ _ _ _ (m_bang (cone_one_car Ar) A)
          (tensor_mor unit_cofree_str (icones_id Ar (Bg A))) (one1 ⊗p x!)).
rewrite (tensor_morE unit_cofree_str (icones_id Ar (Bg A)) one1 x!).
rewrite unit_cofree_str_one1.
have idA : Lfun (icones_id Ar (Bg A)) x! = x! by [].
rewrite idA (m_bang_prom H1 Hx).
rewrite (bang_fmap_prom (iso_fwd (tensor_lunit A)) (one1 ⊗p x)
          (ptensor_prom_ball H1 Hx)).
rewrite tensor_lunitEp.
have e1 : c1_val (one1 : cone_one_car Ar) = 1%:nng by [].
rewrite e1 precone_scale_1.
(* RHS *)
rewrite tensor_lunitEp.
by rewrite e1 precone_scale_1.
Qed.

(** Right unit of [m]: [!(ρ^⊗_A) ∘ m_{A,1} ∘ (id ⊗ e0) = ρ^⊗_{!A}]
    (as maps [!A ⊗ 1 → !A]).  Symmetric to [m_bang_lunit]. *)
Lemma m_bang_runit (A : ICone.type Ar) :
  icones_comp (bang_fmap (iso_fwd (tensor_runit A)))
    (icones_comp (m_bang A (cone_one_car Ar))
       (tensor_mor (icones_id Ar (Bg A)) unit_cofree_str)) =
  iso_fwd (tensor_runit (Bg A)).
Proof.
apply: tens_excl_unitR => x Hx.
have H1 : cone_norm (one1 : cone_one_car Ar) <= 1.
  by rewrite (_ : cone_norm one1 = 1) // /cone_norm /= /c1_norm.
(* LHS *)
rewrite (@Lfun_comp _ _ _ _ _ (bang_fmap (iso_fwd (tensor_runit A)))
          (icones_comp (m_bang A (cone_one_car Ar))
             (tensor_mor (icones_id Ar (Bg A)) unit_cofree_str)) (x! ⊗p one1)).
rewrite (@Lfun_comp _ _ _ _ _ (m_bang A (cone_one_car Ar))
          (tensor_mor (icones_id Ar (Bg A)) unit_cofree_str) (x! ⊗p one1)).
rewrite (tensor_morE (icones_id Ar (Bg A)) unit_cofree_str x! one1).
rewrite unit_cofree_str_one1.
have idA : Lfun (icones_id Ar (Bg A)) x! = x! by [].
rewrite idA (m_bang_prom Hx H1).
rewrite (bang_fmap_prom (iso_fwd (tensor_runit A)) (x ⊗p one1)
          (ptensor_prom_ball Hx H1)).
rewrite tensor_runitEp.
have e1 : c1_val (one1 : cone_one_car Ar) = 1%:nng by [].
rewrite e1 precone_scale_1.
(* RHS *)
rewrite tensor_runitEp.
by rewrite e1 precone_scale_1.
Qed.

End CBVAdjunctionUnit.

Arguments m_bang_lunit {R Ar} A.
Arguments m_bang_runit {R Ar} A.

(** ** [U] is STRONG symmetric monoidal — the monoidal structure on [EM(!)]

    The forgetful [U : EM(!) → IC] is STRICT/STRONG symmetric monoidal:
    [U(EM_prod P Q) = U P ⊗ U Q] and [U(EM_term) = 1] definitionally
    ([EM_prod_obj]/[EM_term_obj]), so the comparison maps [φ2]/[φ0] are
    IDENTITIES.  The monoidal structure of [EM(!)] (the lifted [⊗]) is then
    carried by the [IC] structural isos [α]/[λ]/[ρ]/[σ]; the content is that
    each is a COALGEBRA MORPHISM between the corresponding product
    coalgebras (so [⊗] lifts to a symmetric monoidal structure on [EM(!)],
    and [U] strictly preserves it).  These are GENERAL (every coalgebra):
    chases through the [m_bang] coherence lemmas above. *)
Section UStrongMonoidal.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation "B '⊗' C" := (tensor Ar B C)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '!'" := (prom x) (at level 2, format "x '!'").
Local Notation Bg := (@Bang R Ar).

(** Associator naturality (a pure SMC helper, no [!] content):
    [α_{A',B',C'} ∘ ((f⊗g)⊗h) = (f⊗(g⊗h)) ∘ α_{A,B,C}].  By [tensor_ext3]. *)
Lemma tensor_assoc_nat (A A' B B' C C' : ICone.type Ar)
    (f : icones_hom Ar A A') (g : icones_hom Ar B B') (h : icones_hom Ar C C') :
  icones_comp (iso_fwd (tensor_assoc A' B' C'))
    (tensor_mor (tensor_mor f g) h) =
  icones_comp (tensor_mor f (tensor_mor g h))
    (iso_fwd (tensor_assoc A B C)).
Proof.
apply: tensor_ext3 => x y z.
rewrite (@Lfun_comp _ _ _ _ _ (iso_fwd (tensor_assoc A' B' C'))
          (tensor_mor (tensor_mor f g) h) ((x ⊗p y) ⊗p z)).
rewrite (tensor_morE (tensor_mor f g) h (x ⊗p y) z).
rewrite (tensor_morE f g x y) tensor_assocEp.
rewrite (@Lfun_comp _ _ _ _ _ (tensor_mor f (tensor_mor g h))
          (iso_fwd (tensor_assoc A B C)) ((x ⊗p y) ⊗p z)).
rewrite tensor_assocEp.
by rewrite (tensor_morE f (tensor_mor g h) x (y ⊗p z)) (tensor_morE g h y z).
Qed.

(** The associator [α] is a coalgebra morphism
    [EM_prod (EM_prod P Q) S → EM_prod P (EM_prod Q S)].  Requirement
    [s_R ∘ α = !α ∘ s_L].  Chase:
      [!α ∘ m_{P⊗Q,S} ∘ ((m_{P,Q}∘(a⊗b)) ⊗ c)
       = !α ∘ m_{P⊗Q,S} ∘ (m_{P,Q}⊗id) ∘ ((a⊗b)⊗c)
       = (m_{P,Q⊗S} ∘ (id⊗m_{Q,S}) ∘ α) ∘ ((a⊗b)⊗c)   (m_bang_assoc)
       = m_{P,Q⊗S} ∘ (id⊗m_{Q,S}) ∘ (a⊗(b⊗c)) ∘ α       (tensor_assoc_nat)
       = m_{P,Q⊗S} ∘ (a ⊗ (m_{Q,S}∘(b⊗c))) ∘ α = s_R ∘ α]. *)
Lemma m_assoc_coalg_mor (P Q S : Coalgebra Ar) :
  is_coalg_mor (EM_prod (EM_prod P Q) S) (EM_prod P (EM_prod Q S))
    (iso_fwd (tensor_assoc (coalg_obj P) (coalg_obj Q) (coalg_obj S))).
Proof.
rewrite /is_coalg_mor.
rewrite (EM_prod_str_E P (EM_prod Q S)) (EM_prod_str_E (EM_prod P Q) S).
rewrite {1}/EM_prod_str (EM_prod_str_E Q S).
rewrite {2}/EM_prod_str (EM_prod_str_E P Q).
rewrite /EM_prod_str.
set a := coalg_str P; set b := coalg_str Q; set c := coalg_str S.
(* RHS bifunctor split: [(m_{P,Q}∘(a⊗b)) ⊗ c = (m_{P,Q}⊗id) ∘ ((a⊗b)⊗c)]. *)
have HR : tensor_mor (icones_comp (m_bang (coalg_obj P) (coalg_obj Q)) (tensor_mor a b)) c =
  icones_comp (tensor_mor (m_bang (coalg_obj P) (coalg_obj Q)) (icones_id Ar (Bg (coalg_obj S))))
    (tensor_mor (tensor_mor a b) c).
  rewrite -(tensor_mor_comp (m_bang (coalg_obj P) (coalg_obj Q)) (tensor_mor a b)
             (icones_id Ar (Bg (coalg_obj S))) c).
  by rewrite icones_compIl.
rewrite HR.
(* LHS bifunctor split: [a ⊗ (m_{Q,S}∘(b⊗c)) = (id⊗m_{Q,S}) ∘ (a⊗(b⊗c))]. *)
have HL : tensor_mor a (icones_comp (m_bang (coalg_obj Q) (coalg_obj S)) (tensor_mor b c)) =
  icones_comp (tensor_mor (icones_id Ar (Bg (coalg_obj P))) (m_bang (coalg_obj Q) (coalg_obj S)))
    (tensor_mor a (tensor_mor b c)).
  rewrite -(tensor_mor_comp (icones_id Ar (Bg (coalg_obj P))) a
             (m_bang (coalg_obj Q) (coalg_obj S)) (tensor_mor b c)).
  by rewrite icones_compIl.
rewrite HL.
(* RHS: reassociate to expose [!α ∘ (m_{P⊗Q,S} ∘ (m_{P,Q}⊗id))] and pull
   [m_bang_assoc]. *)
rewrite (icones_compA (m_bang (coalg_obj (EM_prod P Q)) (coalg_obj S))
           (tensor_mor (m_bang (coalg_obj P) (coalg_obj Q)) (icones_id Ar (Bg (coalg_obj S))))
           (tensor_mor (tensor_mor a b) c)).
rewrite (icones_compA (bang_fmap (iso_fwd (tensor_assoc (coalg_obj P) (coalg_obj Q) (coalg_obj S))))
           (icones_comp (m_bang (coalg_obj (EM_prod P Q)) (coalg_obj S))
              (tensor_mor (m_bang (coalg_obj P) (coalg_obj Q)) (icones_id Ar (Bg (coalg_obj S)))))
           (tensor_mor (tensor_mor a b) c)).
rewrite (m_bang_assoc (coalg_obj P) (coalg_obj Q) (coalg_obj S)).
(* RHS now [m_{P,Q⊗S} ∘ (id⊗m_{Q,S}) ∘ α_! ∘ ((a⊗b)⊗c)]; right-associate and
   apply associator naturality [tensor_assoc_nat]. *)
rewrite -(icones_compA (m_bang (coalg_obj P) (coalg_obj Q ⊗ coalg_obj S))
           (icones_comp (tensor_mor (icones_id Ar (Bg (coalg_obj P))) (m_bang (coalg_obj Q) (coalg_obj S)))
              (iso_fwd (tensor_assoc (Bg (coalg_obj P)) (Bg (coalg_obj Q)) (Bg (coalg_obj S)))))
           (tensor_mor (tensor_mor a b) c)).
rewrite -(icones_compA (tensor_mor (icones_id Ar (Bg (coalg_obj P))) (m_bang (coalg_obj Q) (coalg_obj S)))
           (iso_fwd (tensor_assoc (Bg (coalg_obj P)) (Bg (coalg_obj Q)) (Bg (coalg_obj S))))
           (tensor_mor (tensor_mor a b) c)).
rewrite (tensor_assoc_nat a b c).
(* LHS: right-associate to the same shape [m_{P,Q⊗S} ∘ ((id⊗m_{Q,S}) ∘
   ((a⊗(b⊗c)) ∘ α))]. *)
rewrite -(icones_compA (m_bang (coalg_obj P) (coalg_obj (EM_prod Q S)))
           (icones_comp (tensor_mor (icones_id Ar (Bg (coalg_obj P))) (m_bang (coalg_obj Q) (coalg_obj S)))
              (tensor_mor a (tensor_mor b c)))
           (iso_fwd (tensor_assoc (coalg_obj P) (coalg_obj Q) (coalg_obj S)))).
rewrite -(icones_compA (tensor_mor (icones_id Ar (Bg (coalg_obj P))) (m_bang (coalg_obj Q) (coalg_obj S)))
           (tensor_mor a (tensor_mor b c))
           (iso_fwd (tensor_assoc (coalg_obj P) (coalg_obj Q) (coalg_obj S)))).
(* both sides agree (up to [coalg_obj (EM_prod Q S) = coalg_obj Q ⊗ coalg_obj S]). *)
by [].
Qed.

End UStrongMonoidal.

Arguments tensor_assoc_nat {R Ar A A' B B' C C'} f g h.
Arguments m_assoc_coalg_mor {R Ar} P Q S.

Section UStrongMonoidal2.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation "B '⊗' C" := (tensor Ar B C)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '!'" := (prom x) (at level 2, format "x '!'").
Local Notation Bg := (@Bang R Ar).

(** The braiding [σ] is a coalgebra morphism [EM_prod P Q → EM_prod Q P].
    Requirement [s_{Q,P} ∘ σ = !σ ∘ s_{P,Q}].  Chase:
      [!σ ∘ m_{P,Q} ∘ (a⊗b) = m_{Q,P} ∘ σ_{!P,!Q} ∘ (a⊗b)   (m_bang_braid)
       = m_{Q,P} ∘ (b⊗a) ∘ σ_{P,Q}                          (σ naturality)
       = s_{Q,P} ∘ σ]. *)
Lemma m_braid_coalg_mor (P Q : Coalgebra Ar) :
  is_coalg_mor (EM_prod P Q) (EM_prod Q P)
    (iso_fwd (tensor_braid (coalg_obj P) (coalg_obj Q))).
Proof.
rewrite /is_coalg_mor.
rewrite (EM_prod_str_E Q P) (EM_prod_str_E P Q) /EM_prod_str.
set a := coalg_str P; set b := coalg_str Q.
(* RHS: [!σ ∘ m_{P,Q} ∘ (a⊗b)]; pull [m_bang_braid]. *)
rewrite (icones_compA (bang_fmap (iso_fwd (tensor_braid (coalg_obj P) (coalg_obj Q))))).
rewrite (m_bang_braid (coalg_obj P) (coalg_obj Q)).
(* RHS now [m_{Q,P} ∘ σ_{!P,!Q} ∘ (a⊗b)]; use braiding naturality on the
   pure-tensor [σ ∘ (a⊗b) = (b⊗a) ∘ σ]. *)
rewrite -(icones_compA (m_bang (coalg_obj Q) (coalg_obj P))).
have Hsig : icones_comp (iso_fwd (tensor_braid (Bg (coalg_obj P)) (Bg (coalg_obj Q))))
              (tensor_mor a b) =
            icones_comp (tensor_mor b a)
              (iso_fwd (tensor_braid (coalg_obj P) (coalg_obj Q))).
  apply: tensor_ext => x y.
  rewrite (@Lfun_comp _ _ _ _ _ (iso_fwd (tensor_braid (Bg (coalg_obj P)) (Bg (coalg_obj Q))))
            (tensor_mor a b) (x ⊗p y)).
  rewrite (tensor_morE a b x y) tensor_braidEp.
  rewrite (@Lfun_comp _ _ _ _ _ (tensor_mor b a)
            (iso_fwd (tensor_braid (coalg_obj P) (coalg_obj Q))) (x ⊗p y)).
  by rewrite tensor_braidEp (tensor_morE b a y x).
rewrite Hsig.
by rewrite !icones_compA.
Qed.

(** The left unitor [λ] is a coalgebra morphism [EM_prod EM_term P → P].
    Requirement [a ∘ λ = !λ ∘ s_{1,P}].  Chase:
      [!λ ∘ m_{1,P} ∘ (e0⊗a) = !λ ∘ m_{1,P} ∘ (e0⊗id) ∘ (id⊗a)
       = λ_{!P} ∘ (id⊗a)        (m_bang_lunit)
       = a ∘ λ_P                (tensor_lunit_nat)]. *)
Lemma m_lunit_coalg_mor (P : Coalgebra Ar) :
  is_coalg_mor (EM_prod EM_term P) P
    (iso_fwd (tensor_lunit (coalg_obj P))).
Proof.
rewrite /is_coalg_mor (EM_prod_str_E EM_term P) /EM_prod_str.
rewrite -[coalg_str EM_term]/(unit_cofree_str).
set a := coalg_str P.
(* RHS: [!λ ∘ m_{1,P} ∘ (e0⊗a)]; split [e0⊗a = (e0⊗id_!P)∘(id_1⊗a)]. *)
have Hsplit : tensor_mor unit_cofree_str a =
  icones_comp (tensor_mor unit_cofree_str (icones_id Ar (Bg (coalg_obj P))))
    (tensor_mor (icones_id Ar (cone_one_car Ar)) a).
  rewrite -(tensor_mor_comp unit_cofree_str (icones_id Ar (cone_one_car Ar))
             (icones_id Ar (Bg (coalg_obj P))) a).
  by rewrite icones_compIr icones_compIl.
rewrite Hsplit.
(* RHS now [!λ ∘ m_{1,P} ∘ (e0⊗id_!P) ∘ (id_1⊗a)]; apply [m_bang_lunit]. *)
rewrite (icones_compA (m_bang (cone_one_car Ar) (coalg_obj P))).
rewrite (icones_compA (bang_fmap (iso_fwd (tensor_lunit (coalg_obj P))))).
rewrite (m_bang_lunit (coalg_obj P)).
(* RHS now [λ_{!P} ∘ (id_1⊗a)]; use left-unitor naturality. *)
by rewrite (tensor_lunit_nat a).
Qed.

(** The right unitor [ρ] is a coalgebra morphism [EM_prod P EM_term → P].
    Symmetric to [m_lunit_coalg_mor]. *)
Lemma m_runit_coalg_mor (P : Coalgebra Ar) :
  is_coalg_mor (EM_prod P EM_term) P
    (iso_fwd (tensor_runit (coalg_obj P))).
Proof.
rewrite /is_coalg_mor (EM_prod_str_E P EM_term) /EM_prod_str.
rewrite -[coalg_str EM_term]/(unit_cofree_str).
set a := coalg_str P.
(* RHS: [!ρ ∘ m_{P,1} ∘ (a⊗e0)]; split [a⊗e0 = (id_!P⊗e0)∘(a⊗id_1)]. *)
have Hsplit : tensor_mor a unit_cofree_str =
  icones_comp (tensor_mor (icones_id Ar (Bg (coalg_obj P))) unit_cofree_str)
    (tensor_mor a (icones_id Ar (cone_one_car Ar))).
  rewrite -(tensor_mor_comp (icones_id Ar (Bg (coalg_obj P))) a
             unit_cofree_str (icones_id Ar (cone_one_car Ar))).
  by rewrite icones_compIr icones_compIl.
rewrite Hsplit.
(* RHS now [!ρ ∘ m_{P,1} ∘ (id_!P⊗e0) ∘ (a⊗id_1)]; apply [m_bang_runit]. *)
rewrite (icones_compA (m_bang (coalg_obj P) (cone_one_car Ar))).
rewrite (icones_compA (bang_fmap (iso_fwd (tensor_runit (coalg_obj P))))).
rewrite (m_bang_runit (coalg_obj P)).
(* RHS now [ρ_{!P} ∘ (a⊗id_1)]; use right-unitor naturality. *)
by rewrite (tensor_runit_nat a).
Qed.

End UStrongMonoidal2.

Arguments m_braid_coalg_mor {R Ar} P Q.
Arguments m_lunit_coalg_mor {R Ar} P.
Arguments m_runit_coalg_mor {R Ar} P.

(** ** The cartesian projections are coalgebra morphisms — UNCONDITIONAL

    [em_cartesian.v] exposes the projections [em_proj1_mor]/[em_proj2_mor]
    as plain [icones_hom] (the β-laws are stated at that level).  Packaged
    as coalgebra morphisms they are unconditional composites of
    [m_runit_coalg_mor]/[m_lunit_coalg_mor] (above), the bifunctor action
    [EM_prod_mor] on [id] and [coalg_e], using [EMComon_all] to extract
    [emc_e_mor] of the discarded factor.

    These lemmas live here (NOT in [cbv.v]) so that [em_pair_mor_proj_id]
    below can be stated on coalgebra morphisms while still being part of
    the cartesian-η machinery that the [cbv.v] / [ppl.v] downstream needs. *)
Section EMProjections.
Variables (R : realType) (Ar : MeasSubcat R).

Lemma em_proj1_is_mor (P Q : Coalgebra Ar) :
  is_coalg_mor (EM_prod P Q) P (em_proj1_mor P Q).
Proof.
rewrite /em_proj1_mor.
apply: (coalg_mor_comp (P := EM_prod P Q) (Q := EM_prod P EM_term) (S := P)).
- exact: (m_runit_coalg_mor P).
- apply: (EM_prod_mor (P':=P) (Q':=EM_term) (icones_id Ar (coalg_obj P)) (coalg_e Q)).
  + exact: (coalg_mor_id P).
  + exact: (emc_e_mor (EMComon_all Q)).
Qed.

Lemma em_proj2_is_mor (P Q : Coalgebra Ar) :
  is_coalg_mor (EM_prod P Q) Q (em_proj2_mor P Q).
Proof.
rewrite /em_proj2_mor.
apply: (coalg_mor_comp (P := EM_prod P Q) (Q := EM_prod EM_term Q) (S := Q)).
- exact: (m_lunit_coalg_mor Q).
- apply: (EM_prod_mor (P':=EM_term) (Q':=Q) (coalg_e P) (icones_id Ar (coalg_obj Q))).
  + exact: (emc_e_mor (EMComon_all P)).
  + exact: (coalg_mor_id Q).
Qed.

(** The bundled projection coalgebra morphisms — unconditional. *)
Definition em_proj1 (P Q : Coalgebra Ar) :
    coalg_hom (EM_prod P Q) P := MkCoalgHom (em_proj1_is_mor P Q).

Definition em_proj2 (P Q : Coalgebra Ar) :
    coalg_hom (EM_prod P Q) Q := MkCoalgHom (em_proj2_is_mor P Q).

End EMProjections.

Arguments em_proj1_is_mor {R Ar} P Q.
Arguments em_proj2_is_mor {R Ar} P Q.
Arguments em_proj1 {R Ar} P Q.
Arguments em_proj2 {R Ar} P Q.

(** ** The cartesian η-rule [⟨π₁,π₂⟩ = id]  (Fox 1976 / Melliès Prop 28)

    The "pair-of-projections is the identity" identity of the cartesian
    structure on [EM(!)] — the η-law of the cartesian product
    [(EM_prod, π₁, π₂, ⟨·,·⟩)] in [EM(!)]; together with the β-laws
    [em_proj1_pair]/[em_proj2_pair] it completes the universal property
    of the binary product (Fox's theorem 1976 for the EM category of a
    linear exponential comonad; the icones-level statement is folklore).

    Proof strategy (retract-transport, the Melliès-Prop-27 pattern).
    Both [em_pair_mor (π₁) (π₂)] and [id_{cP⊗cQ}] are morphisms in
    [EM(!)] out of [EM_prod P Q].  Use the SPLIT MONO retraction
      [(coalg_str P ⊗ coalg_str Q) : EM_prod P Q → EM_prod (!̃cP) (!̃cQ)]
      [(der_cP ⊗ der_cQ) : EM_prod (!̃cP) (!̃cQ) → EM_prod P Q]
    (which satisfies [r∘u = id] by [coalg_counit P/Q]) to reduce
    icones-level equation on [P⊗Q] to one on [!cP⊗!cQ] (the cofree
    case).  In the cofree case the equation reduces, via [tens_excl_charact],
    to a check on the promoted pure tensor [x!⊗y!], where both sides
    give [x!⊗y!] by [d_bang_prom]/[der_prom]/[m_bang_prom] computations. *)

Section EmPairProjId.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation "B '⊗' C" := (tensor Ar B C)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '!'" := (prom x) (at level 2, format "x '!'").
Local Notation Bg := (@Bang R Ar).

(** *** Step 1 — the cofree case via promoted-point extensionality.

    On the cofree pair [(!̃A, !̃B)] the [coalg_d] computes on [x!⊗y!]
    via [d_bang_prom]/[m_bang_prom]/[der_prom] to [(x!⊗y!) ⊗ (x!⊗y!)],
    and both [em_proj1_mor] and [em_proj2_mor] reduce on [x!⊗y!] to [x!]
    / [y!] respectively (via the [(id⊗e_!B)] / [(e_!A⊗id)] tensor action
    + [e_bang_prom] + the unitor on promoted points).  So
    [em_pair_mor (π₁)(π₂)(x!⊗y!) = x!⊗y!] = the [icones_id] action.
    Discharge by [tens_excl_charact]. *)
Lemma em_pair_mor_proj_id_cofree (A B : ICone.type Ar) :
  @em_pair_mor R Ar (EM_prod (bang_cofree A) (bang_cofree B))
    (bang_cofree A) (bang_cofree B)
    (em_proj1_mor (bang_cofree A) (bang_cofree B))
    (em_proj2_mor (bang_cofree A) (bang_cofree B))
  = icones_id Ar (coalg_obj (EM_prod (bang_cofree A) (bang_cofree B))).
Proof.
apply: tens_excl_charact => x y Hx Hy.
rewrite /em_pair_mor.
rewrite -[Lfun (icones_comp _ _) _]
        /(Lfun (tensor_mor (em_proj1_mor (bang_cofree A) (bang_cofree B))
                           (em_proj2_mor (bang_cofree A) (bang_cofree B)))
          (Lfun (coalg_d (EM_prod (bang_cofree A) (bang_cofree B)))
                (x! ⊗p y!))).
rewrite /coalg_d.
rewrite -[Lfun (icones_comp _ _) (x! ⊗p y!)]
        /(Lfun (tensor_mor (der (Bg A ⊗ Bg B)) (der (Bg A ⊗ Bg B)))
          (Lfun (icones_comp (d_bang (Bg A ⊗ Bg B))
                  (coalg_str (EM_prod (bang_cofree A) (bang_cofree B))))
                (x! ⊗p y!))).
rewrite -[Lfun (icones_comp (d_bang _) _) _]
        /(Lfun (d_bang (Bg A ⊗ Bg B))
          (Lfun (coalg_str (EM_prod (bang_cofree A) (bang_cofree B)))
                (x! ⊗p y!))).
rewrite (EM_prod_str_E (bang_cofree A) (bang_cofree B)).
rewrite /EM_prod_str.
rewrite !bang_cofree_str.
have Hxp : cone_norm (x! : Bg A) <= 1 by exact: prom_ball.
have Hyp : cone_norm (y! : Bg B) <= 1 by exact: prom_ball.
rewrite -[Lfun (icones_comp _ _) (x! ⊗p y!)]
        /(Lfun (m_bang _ _) (Lfun (tensor_mor (dig A) (dig B)) (x! ⊗p y!))).
rewrite tensor_morE (dig_prom x Hx) (dig_prom y Hy).
rewrite (m_bang_prom Hxp Hyp).
have Hxyp : cone_norm (x! ⊗p y!) <= 1 by exact: ptensor_prom_ball.
rewrite (d_bang_prom (x! ⊗p y!) Hxyp).
rewrite tensor_morE.
rewrite (der_prom _ Hxyp).
rewrite tensor_morE.
rewrite /em_proj1_mor /em_proj2_mor.
rewrite -[Lfun (icones_comp (iso_fwd (tensor_runit _)) _) _]
        /(Lfun (iso_fwd (tensor_runit (Bg A)))
          (Lfun (tensor_mor (icones_id Ar (Bg A))
                            (coalg_e (bang_cofree B))) (x! ⊗p y!))).
rewrite -[Lfun (icones_comp (iso_fwd (tensor_lunit _)) _) _]
        /(Lfun (iso_fwd (tensor_lunit (Bg B)))
          (Lfun (tensor_mor (coalg_e (bang_cofree A))
                            (icones_id Ar (Bg B))) (x! ⊗p y!))).
rewrite (tensor_morE (icones_id Ar (Bg A)) (coalg_e (bang_cofree B)) x! y!).
have H2 : Lfun (tensor_mor (coalg_e (bang_cofree A)) (icones_id Ar (Bg B)))
                (x! ⊗p y!)
        = Lfun (coalg_e (bang_cofree A)) x! ⊗p Lfun (icones_id Ar (Bg B)) y!
  by rewrite (tensor_morE (coalg_e (bang_cofree A)) (icones_id Ar (Bg B)) x! y!).
rewrite H2.
rewrite (coalg_e_cofree A) (coalg_e_cofree B).
rewrite (e_bang_prom x Hx) (e_bang_prom y Hy).
rewrite -[Lfun (icones_id Ar (Bg A)) x!]/x!.
rewrite -[Lfun (icones_id Ar (Bg B)) y!]/y!.
rewrite tensor_runitEp tensor_lunitEp.
have e1 : c1_val (one1 : cone_one_car Ar) = 1%:nng by [].
rewrite e1 precone_scale_1.
by rewrite precone_scale_1.
Qed.

(** *** Step 2 — helper: naturality of [em_pair_mor] in its output factors
    (right form, no side condition).  Same statement as [em_pair_mor_natR]
    in [ppl.v]; inlined here because we need it BEFORE [ppl.v]. *)
Lemma em_pair_mor_natR_cbv (Z P Q P' Q' : Coalgebra Ar)
    (a : icones_hom Ar (coalg_obj Z) (coalg_obj P))
    (b : icones_hom Ar (coalg_obj Z) (coalg_obj Q))
    (f : icones_hom Ar (coalg_obj P) (coalg_obj P'))
    (g : icones_hom Ar (coalg_obj Q) (coalg_obj Q')) :
  icones_comp (tensor_mor f g) (em_pair_mor a b)
  = em_pair_mor (icones_comp f a) (icones_comp g b).
Proof.
rewrite /em_pair_mor icones_compA.
by rewrite (tensor_mor_comp f a g b).
Qed.

(** *** Step 2 — helper: left naturality of [em_pair_mor] (needs the input
    morphism to be a coalgebra morphism).  Same as [em_pair_mor_natL] in
    [ppl.v]; inlined here. *)
Lemma em_pair_mor_natL_cbv (Z Y P Q : Coalgebra Ar)
    (h : icones_hom Ar (coalg_obj Z) (coalg_obj Y))
    (p : icones_hom Ar (coalg_obj Y) (coalg_obj P))
    (q : icones_hom Ar (coalg_obj Y) (coalg_obj Q))
    (Hh : is_coalg_mor Z Y h) :
  icones_comp (em_pair_mor p q) h
  = em_pair_mor (icones_comp p h) (icones_comp q h).
Proof.
rewrite /em_pair_mor -icones_compA (coalg_mor_d _ Hh).
rewrite icones_compA (tensor_mor_comp p h q h).
by rewrite icones_compA.
Qed.

(** *** Step 3 — the projection-naturality identities at the [coalg_str]
    retract.  For [u := tensor_mor (coalg_str P) (coalg_str Q)] (the [EM(!)]
    unit at [EM_prod P Q]), we have
      [coalg_str P ∘ em_proj1_mor P Q  =  em_proj1_mor (!̃cP) (!̃cQ) ∘ u]
      [coalg_str Q ∘ em_proj2_mor P Q  =  em_proj2_mor (!̃cP) (!̃cQ) ∘ u]
    Both follow from [tensor_runit_nat]/[tensor_lunit_nat] (unitor
    naturality) + [tensor_mor_comp] + [coalg_e_cofree] (which writes
    [coalg_e (!̃cQ) = e_bang cQ], hence
    [coalg_e (!̃cQ) ∘ coalg_str Q = e_bang cQ ∘ coalg_str Q = coalg_e Q]
    by definition of [coalg_e]). *)
Lemma coalg_str_em_proj1 (P Q : Coalgebra Ar) :
  icones_comp (coalg_str P) (em_proj1_mor P Q) =
  icones_comp (em_proj1_mor (bang_cofree (coalg_obj P)) (bang_cofree (coalg_obj Q)))
              (tensor_mor (coalg_str P) (coalg_str Q)).
Proof.
rewrite /em_proj1_mor.
rewrite icones_compA.
rewrite -(tensor_runit_nat (coalg_str P)).
rewrite -icones_compA.
rewrite -(tensor_mor_comp (coalg_str P) (icones_id Ar (coalg_obj P))
                          (icones_id Ar (cone_one_car Ar)) (coalg_e Q)).
rewrite icones_compIr icones_compIl.
rewrite -icones_compA.
rewrite -(tensor_mor_comp (icones_id Ar (Bg (coalg_obj P))) (coalg_str P)
                          (coalg_e (bang_cofree (coalg_obj Q))) (coalg_str Q)).
rewrite icones_compIl.
rewrite (coalg_e_cofree (coalg_obj Q)).
rewrite -[icones_comp (e_bang (coalg_obj Q)) (coalg_str Q)]/(coalg_e Q).
by [].
Qed.

Lemma coalg_str_em_proj2 (P Q : Coalgebra Ar) :
  icones_comp (coalg_str Q) (em_proj2_mor P Q) =
  icones_comp (em_proj2_mor (bang_cofree (coalg_obj P)) (bang_cofree (coalg_obj Q)))
              (tensor_mor (coalg_str P) (coalg_str Q)).
Proof.
rewrite /em_proj2_mor.
rewrite icones_compA.
rewrite -(tensor_lunit_nat (coalg_str Q)).
rewrite -icones_compA.
rewrite -(tensor_mor_comp (icones_id Ar (cone_one_car Ar)) (coalg_e P)
                          (coalg_str Q) (icones_id Ar (coalg_obj Q))).
rewrite icones_compIr icones_compIl.
rewrite -icones_compA.
rewrite -(tensor_mor_comp (coalg_e (bang_cofree (coalg_obj P))) (coalg_str P)
                          (icones_id Ar (Bg (coalg_obj Q))) (coalg_str Q)).
rewrite icones_compIl.
rewrite (coalg_e_cofree (coalg_obj P)).
rewrite -[icones_comp (e_bang (coalg_obj P)) (coalg_str P)]/(coalg_e P).
by [].
Qed.

(** *** Step 4 — the headline.  Lift the cofree case along the retract
    [u = (coalg_str P ⊗ coalg_str Q)] (with retraction [(der_cP ⊗ der_cQ)],
    [coalg_counit P/Q]) via [lcancel_mono]: it suffices to check
    [u ∘ em_pair_mor (π₁)(π₂) = u].  Chain:
      LHS = em_pair_mor (coalg_str P ∘ π₁) (coalg_str Q ∘ π₂)   [natR]
          = em_pair_mor (π₁_cof ∘ u) (π₂_cof ∘ u)              [Step 3]
          = em_pair_mor π₁_cof π₂_cof ∘ u                      [natL backward; u is coalg mor]
          = id_{!cP⊗!cQ} ∘ u                                    [em_pair_mor_proj_id_cofree]
          = u. *)
Lemma em_pair_mor_proj_id (P Q : Coalgebra Ar) :
  @em_pair_mor R Ar (EM_prod P Q) P Q (em_proj1_mor P Q) (em_proj2_mor P Q)
  = icones_id Ar (coalg_obj (EM_prod P Q)).
Proof.
pose u := tensor_mor (coalg_str P) (coalg_str Q).
have Hri : icones_comp (tensor_mor (der (coalg_obj P)) (der (coalg_obj Q))) u
         = icones_id Ar (coalg_obj P ⊗ coalg_obj Q).
  rewrite /u -(tensor_mor_comp (der (coalg_obj P)) (coalg_str P)
                               (der (coalg_obj Q)) (coalg_str Q)).
  by rewrite (coalg_counit P) (coalg_counit Q) tensor_mor_id.
have Hu : is_coalg_mor (EM_prod P Q)
            (EM_prod (bang_cofree (coalg_obj P)) (bang_cofree (coalg_obj Q))) u.
  rewrite /u; apply: EM_prod_mor;
    [exact: (adj_unit_is_mor P) | exact: (adj_unit_is_mor Q)].
apply: (lcancel_mono u (tensor_mor (der (coalg_obj P)) (der (coalg_obj Q))) Hri).
rewrite icones_compIr.
rewrite -/u.
rewrite (em_pair_mor_natR_cbv (Z := EM_prod P Q) (P := P) (Q := Q)
                              (P' := bang_cofree (coalg_obj P))
                              (Q' := bang_cofree (coalg_obj Q))
           (em_proj1_mor P Q) (em_proj2_mor P Q) (coalg_str P) (coalg_str Q)).
rewrite (coalg_str_em_proj1 P Q).
rewrite (coalg_str_em_proj2 P Q).
rewrite -(em_pair_mor_natL_cbv (Z := EM_prod P Q)
            (Y := EM_prod (bang_cofree (coalg_obj P)) (bang_cofree (coalg_obj Q)))
            (P := bang_cofree (coalg_obj P)) (Q := bang_cofree (coalg_obj Q))
            (h := u)
            (em_proj1_mor (bang_cofree (coalg_obj P)) (bang_cofree (coalg_obj Q)))
            (em_proj2_mor (bang_cofree (coalg_obj P)) (bang_cofree (coalg_obj Q)))
            Hu).
rewrite (em_pair_mor_proj_id_cofree (coalg_obj P) (coalg_obj Q)).
by rewrite icones_compIl.
Qed.

End EmPairProjId.

(** ** [!̃] is LAX symmetric monoidal — the comparison coalgebra morphisms

    The cofree functor [!̃] carries a LAX symmetric monoidal structure
    [(!̃, bang_m, bang_e0)]:
    - the binary comparison [bang_m : EM_prod (!̃A)(!̃B) → !̃(A⊗B)] is
      [m_bang A B] packaged as a coalgebra morphism (its source product
      coalgebra has the SAME structure map [tens_cofree_str A B] as
      [tens_cofree A B], so [m_bang_is_coalg_mor] applies);
    - the unit comparison [bang_e0 : EM_term → !̃1] is [unit_cofree_str]
      packaged (a coalgebra morphism by [unit_cofree_coassoc]).
    The lax coherence (associativity / unitors / symmetry) is exactly the
    [m_bang_*] coherence lemmas above, read in [EM(!)] — since [U] is
    FAITHFUL ([ch_mor] injective on the side-condition, [coalg_hom_eqP]),
    a coalgebra-morphism equation holds iff its underlying [icones_hom]
    equation holds, and those are [m_bang_assoc]/[m_bang_lunit]/
    [m_bang_runit]/[m_bang_braid]. *)
Section BangLax.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation "B '⊗' C" := (tensor Ar B C)
  (at level 40, left associativity) : ring_scope.
Local Notation Bg := (@Bang R Ar).

(** [EM_prod (!̃A)(!̃B)] has the SAME structure map as [tens_cofree A B]
    ([m_bang ∘ (dig⊗dig) = tens_cofree_str], the general-[A B] version of
    [em_cartesian.v]'s [EM_prod_str_cofree]). *)
Lemma EM_prod_str_cofreeAB (A B : ICone.type Ar) :
  EM_prod_str (bang_cofree A) (bang_cofree B) = tens_cofree_str A B.
Proof.
by rewrite /EM_prod_str /= -(tens_cofree_str_m_bang A B).
Qed.

(** Hence [m_bang A B] is a coalgebra morphism
    [EM_prod (!̃A)(!̃B) → !̃(A⊗B)] (transport [m_bang_is_coalg_mor] along
    the structure-map equality). *)
Lemma bang_m_is_coalg_mor (A B : ICone.type Ar) :
  is_coalg_mor (EM_prod (bang_cofree A) (bang_cofree B))
    (bang_cofree (A ⊗ B)) (m_bang A B).
Proof.
have H := m_bang_is_coalg_mor A B.
rewrite /is_coalg_mor in H *.
rewrite (EM_prod_str_E (bang_cofree A) (bang_cofree B)) EM_prod_str_cofreeAB.
by rewrite -(tens_cofree_strE A B).
Qed.

(** The binary lax comparison, packaged. *)
Definition bang_m (A B : ICone.type Ar) :
    coalg_hom (EM_prod (bang_cofree A) (bang_cofree B)) (bang_cofree (A ⊗ B)) :=
  MkCoalgHom (bang_m_is_coalg_mor A B).

(** The unit lax comparison [bang_e0 : EM_term → !̃1] is [unit_cofree_str]
    (a coalgebra morphism [unit_cofree → bang_cofree 1] by
    [unit_cofree_coassoc]). *)
Lemma bang_e0_is_coalg_mor :
  is_coalg_mor (EM_term : Coalgebra Ar) (bang_cofree (cone_one_car Ar))
    unit_cofree_str.
Proof.
rewrite /is_coalg_mor (bang_cofree_str (cone_one_car Ar)).
rewrite -[coalg_str EM_term]/(unit_cofree_str).
exact: unit_cofree_coassoc.
Qed.

Definition bang_e0 : coalg_hom (EM_term : Coalgebra Ar) (bang_cofree (cone_one_car Ar)) :=
  MkCoalgHom bang_e0_is_coalg_mor.

(** *** The lax coherence, read on the underlying maps (U faithful)

    Each is the corresponding [m_bang_*] lemma; the [EM(!)]-associator /
    unitors / braiding are the coalgebra morphisms [m_assoc_coalg_mor] etc.
    whose UNDERLYING maps are [tensor_assoc] / [tensor_lunit] /
    [tensor_runit] / [tensor_braid], so the lax diagrams project (via the
    faithful [U]) to [m_bang_assoc] / [m_bang_lunit] / [m_bang_runit] /
    [m_bang_braid]. *)

Definition bang_lax_assoc (A B C : ICone.type Ar) :
  icones_comp (bang_fmap (iso_fwd (tensor_assoc A B C)))
    (icones_comp (m_bang (A ⊗ B) C)
       (tensor_mor (m_bang A B) (icones_id Ar (Bg C)))) =
  icones_comp (m_bang A (B ⊗ C))
    (icones_comp (tensor_mor (icones_id Ar (Bg A)) (m_bang B C))
       (iso_fwd (tensor_assoc (Bg A) (Bg B) (Bg C))))
  := m_bang_assoc A B C.

Definition bang_lax_lunit (A : ICone.type Ar) :
  icones_comp (bang_fmap (iso_fwd (tensor_lunit A)))
    (icones_comp (m_bang (cone_one_car Ar) A)
       (tensor_mor unit_cofree_str (icones_id Ar (Bg A)))) =
  iso_fwd (tensor_lunit (Bg A))
  := m_bang_lunit A.

Definition bang_lax_runit (A : ICone.type Ar) :
  icones_comp (bang_fmap (iso_fwd (tensor_runit A)))
    (icones_comp (m_bang A (cone_one_car Ar))
       (tensor_mor (icones_id Ar (Bg A)) unit_cofree_str)) =
  iso_fwd (tensor_runit (Bg A))
  := m_bang_runit A.

Definition bang_lax_braid (A B : ICone.type Ar) :
  icones_comp (bang_fmap (iso_fwd (tensor_braid A B))) (m_bang A B) =
  icones_comp (m_bang B A) (iso_fwd (tensor_braid (Bg A) (Bg B)))
  := m_bang_braid A B.

End BangLax.

Arguments EM_prod_str_cofreeAB {R Ar} A B.
Arguments bang_m_is_coalg_mor {R Ar} A B.
Arguments bang_m {R Ar} A B.
Arguments bang_e0_is_coalg_mor {R Ar}.
Arguments bang_e0 {R Ar}.
Arguments bang_lax_assoc {R Ar} A B C.
Arguments bang_lax_lunit {R Ar} A.
Arguments bang_lax_runit {R Ar} A.
Arguments bang_lax_braid {R Ar} A B.

(** ** The monoidal adjunction [U ⊣ !̃] — Melliès Prop 29

    The EM adjunction [U ⊣ !̃] of [em_cat.v] lifts to a (lax symmetric)
    monoidal adjunction: the counit [ε = der] is a monoidal natural
    transformation w.r.t. the STRONG structure of [U] and the LAX structure
    of [!̃], and the unit [η = coalg_str] is monoidal too.  This is the
    doctrinal-adjunction / Lack's-lifting fact (§6.10): for a symmetric
    monoidal comonad, the EM adjunction is automatically monoidal.  In our
    concrete model the two monoidality squares are exactly [der_m_bang] /
    [unit_cofree_counit] (counit) and [EM_prod_str_E] / definitional
    (unit). *)
Section MonoidalAdjunction.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation "B '⊗' C" := (tensor Ar B C)
  (at level 40, left associativity) : ring_scope.
Local Notation Bg := (@Bang R Ar).

(** *** Monoidality of the counit [ε = der]

    [der] is the counit [U(!̃B) → B] (= [adj_counit]).  Monoidality
    w.r.t. the lax structure of [!∘U]-style comparison [m_bang] and the
    identity comparison of [U]:
    - binary [der_{A⊗B} ∘ m_{A,B} = der_A ⊗ der_B]   ([der_m_bang]);
    - nullary [der_1 ∘ e0 = id_1]                     ([unit_cofree_counit]). *)
Lemma adj_counit_monoidal2 (A B : ICone.type Ar) :
  icones_comp (adj_counit (A ⊗ B)) (m_bang A B) =
  tensor_mor (adj_counit A) (adj_counit B).
Proof. rewrite /adj_counit; exact: (der_m_bang A B). Qed.

Lemma adj_counit_monoidal0 :
  icones_comp (adj_counit (cone_one_car Ar)) unit_cofree_str =
  icones_id Ar (cone_one_car Ar).
Proof. rewrite /adj_counit; exact: unit_cofree_counit. Qed.

(** *** Monoidality of the unit [η = coalg_str]

    [η_P = coalg_str P : P → !̃(U P)] (= [adj_unit]).  Monoidality w.r.t. the
    STRONG (identity-comparison) structure of [U] and the LAX comparison
    [m_bang] of [!̃∘U]:
    - binary: [m_{UP,UQ} ∘ (η_P ⊗ η_Q) = η_{EM_prod P Q}], i.e. the
      structure map of the product coalgebra IS this composite — by
      DEFINITION ([EM_prod_str_E]);
    - nullary: [η_{EM_term} = e0], i.e. [coalg_str EM_term = unit_cofree_str]
      — definitional. *)
Lemma adj_unit_monoidal2 (P Q : Coalgebra Ar) :
  icones_comp (m_bang (coalg_obj P) (coalg_obj Q))
    (tensor_mor (coalg_str P) (coalg_str Q)) =
  coalg_str (EM_prod P Q).
Proof. by rewrite (EM_prod_str_E P Q) /EM_prod_str. Qed.

Lemma adj_unit_monoidal0 :
  coalg_str (EM_term : Coalgebra Ar) = unit_cofree_str.
Proof. by []. Qed.

End MonoidalAdjunction.

Arguments adj_counit_monoidal2 {R Ar} A B.
Arguments adj_counit_monoidal0 {R Ar}.
Arguments adj_unit_monoidal2 {R Ar} P Q.
Arguments adj_unit_monoidal0 {R Ar}.

(** ** The CBV-model bundle — Melliès' linear–non-linear (LNL) data

    [CBV_Model R Ar] collects the data that constitutes the CBV/LNL
    structure on [ICones], mirroring the [SeelyCategory]/[ICones_Seely]
    record-with-witness convention:

    - [cbv_smcc] : the SMC [(ICones, ⊗, 1)] ([smcc.v]);
    - [cbv_em] : the EM category [EM(!)] ([em_cat.v]);
    - [cbv_cart] : the CARTESIAN structure on the FULL [EM(!)]
      ([em_cartesian.v]) — the VALUE category.  Every [!]-coalgebra carries
      the transported commutative comonoid ([EMComon_all]), so the product
      universal property holds for ALL coalgebras (Melliès Prop 28); the
      cofree coalgebras [!̃B] and the Theorem-9.7 coalgebras [FMeas X] are
      among its objects, but no subcategory restriction is needed;
    - the MONOIDAL ADJUNCTION [U ⊣ !̃] over the FULL [EM(!)] (needs no
      cartesianness): the functors [cbv_U_obj]/[cbv_U_mor] and
      [cbv_bang_obj]/[cbv_bang_mor], the (co)units
      [cbv_unit]/[cbv_counit] with the hom-bijection
      [cbv_phi]/[cbv_psi] + round-trips and the triangle identities;
    - the MONOIDALITY witnesses: [U] strict monoidal (the product carrier
      [cbv_U_prod] and terminal [cbv_U_term] are identities), [!̃] lax
      monoidal (the underlying comparison maps [cbv_m2]/[cbv_m0], the same
      packaged as coalgebra morphisms [cbv_bang_m]/[cbv_bang_e0], and the
      lax-functor coherence [cbv_lax_assoc]/[cbv_lax_braid]), and the
      monoidal COUNIT laws [cbv_counit_monoidal2]/[cbv_counit_monoidal0].

    (The monoidal UNIT laws are recorded OUTSIDE the record as the proved
    lemmas [adj_unit_monoidal2]/[adj_unit_monoidal0]: they are definitional
    — [m ∘ (η_P ⊗ η_Q)] IS the product structure map [coalg_str (EM_prod P Q)]
    — so they are kept as standalone facts to avoid the dependent-type
    plumbing through the abstract [cart_prod]/[coalg_str] carriers.) *)
Record CBV_Model (R : realType) (Ar : MeasSubcat R) : Type := MkCBVModel {
  (* the linear category [(ICones, ⊗, 1)] *)
  cbv_smcc : ICones_SMCC Ar;
  (* the Eilenberg–Moore category [EM(!)] of the exponential comonad *)
  cbv_em : EM_Cat Ar;
  (* the cartesian VALUE category: the FULL Eilenberg–Moore category
     [EM(!)] (every coalgebra is comonoidal, [EMComon_all]), with its
     [⊗]-product / [1]-terminal (NOT [&]/[⊤]) *)
  cbv_cart : EM_Cartesian Ar;

  (* the monoidal adjunction [U ⊣ !̃] over the FULL [EM(!)] *)
  cbv_U_obj : Coalgebra Ar -> ICone.type Ar;
  cbv_U_mor : forall P Q : Coalgebra Ar,
    coalg_hom P Q -> icones_hom Ar (cbv_U_obj P) (cbv_U_obj Q);
  cbv_bang_obj : ICone.type Ar -> Coalgebra Ar;
  cbv_bang_mor : forall B C : ICone.type Ar,
    icones_hom Ar B C -> coalg_hom (cbv_bang_obj B) (cbv_bang_obj C);
  cbv_unit : forall P : Coalgebra Ar, coalg_hom P (cbv_bang_obj (cbv_U_obj P));
  cbv_counit : forall B : ICone.type Ar,
    icones_hom Ar (cbv_U_obj (cbv_bang_obj B)) B;
  cbv_phi : forall (P : Coalgebra Ar) (B : ICone.type Ar),
    coalg_hom P (cbv_bang_obj B) -> icones_hom Ar (cbv_U_obj P) B;
  cbv_psi : forall (P : Coalgebra Ar) (B : ICone.type Ar),
    icones_hom Ar (cbv_U_obj P) B -> coalg_hom P (cbv_bang_obj B);
  cbv_phiK : forall (P : Coalgebra Ar) (B : ICone.type Ar)
    (g : icones_hom Ar (cbv_U_obj P) B), cbv_phi (cbv_psi g) = g;
  cbv_psiK : forall (P : Coalgebra Ar) (B : ICone.type Ar)
    (h : coalg_hom P (cbv_bang_obj B)), cbv_psi (cbv_phi h) = h;
  cbv_triangleL : forall P : Coalgebra Ar,
    cbv_phi (cbv_unit P) = icones_id Ar (cbv_U_obj P);
  cbv_triangleR : forall B : ICone.type Ar,
    cbv_psi (cbv_counit B) = coalg_id (cbv_bang_obj B);

  (* [U] STRICT/STRONG monoidal: the product / terminal carriers are
     definitionally the [⊗]-tensor / [1]-unit (so the comparison maps are
     identities) *)
  cbv_U_prod : forall P Q : Coalgebra Ar,
    cbv_U_obj (cart_prod cbv_cart P Q) =
    tensor Ar (cbv_U_obj P) (cbv_U_obj Q);
  cbv_U_term : cbv_U_obj (cart_term cbv_cart) = cone_one_car Ar;

  (* [!̃] LAX symmetric monoidal.  The comparison is recorded both as the
     UNDERLYING [ICones] map [cbv_m2]/[cbv_m0] (on which the lax-functor
     coherence and the (co)unit monoidality are cleanly stated) and as a
     COALGEBRA MORPHISM [cbv_bang_m]/[cbv_bang_e0] (so it is a morphism of
     [EM(!)]); [cbv_bang_mE]/[cbv_bang_e0E] tie the two together. *)
  cbv_m2 : forall A B : ICone.type Ar,
    icones_hom Ar (tensor Ar (cbv_U_obj (cbv_bang_obj A)) (cbv_U_obj (cbv_bang_obj B)))
      (cbv_U_obj (cbv_bang_obj (tensor Ar A B)));
  cbv_m0 : icones_hom Ar (cone_one_car Ar) (cbv_U_obj (cbv_bang_obj (cone_one_car Ar)));
  cbv_bang_m : forall A B : ICone.type Ar,
    coalg_hom (cart_prod cbv_cart (cbv_bang_obj A) (cbv_bang_obj B))
      (cbv_bang_obj (tensor Ar A B));
  cbv_bang_e0 : coalg_hom (cart_term cbv_cart) (cbv_bang_obj (cone_one_car Ar));
  (* the lax-functor coherence (associativity / symmetry), on the
     underlying comparison [cbv_m2] *)
  cbv_lax_assoc : forall A B C : ICone.type Ar,
    icones_comp (cbv_U_mor (cbv_bang_mor (iso_fwd (tensor_assoc A B C))))
      (icones_comp (cbv_m2 (tensor Ar A B) C)
         (tensor_mor (cbv_m2 A B) (icones_id Ar (cbv_U_obj (cbv_bang_obj C))))) =
    icones_comp (cbv_m2 A (tensor Ar B C))
      (icones_comp
         (tensor_mor (icones_id Ar (cbv_U_obj (cbv_bang_obj A))) (cbv_m2 B C))
         (iso_fwd (tensor_assoc (cbv_U_obj (cbv_bang_obj A))
            (cbv_U_obj (cbv_bang_obj B)) (cbv_U_obj (cbv_bang_obj C)))));
  cbv_lax_braid : forall A B : ICone.type Ar,
    icones_comp (cbv_U_mor (cbv_bang_mor (iso_fwd (tensor_braid A B))))
      (cbv_m2 A B) =
    icones_comp (cbv_m2 B A)
      (iso_fwd (tensor_braid (cbv_U_obj (cbv_bang_obj A))
         (cbv_U_obj (cbv_bang_obj B))));

  (* the (co)units are MONOIDAL natural transformations *)
  (* counit [ε = der] monoidal: binary [ε∘m = ε⊗ε], nullary [ε∘m0 = id] *)
  cbv_counit_monoidal2 : forall A B : ICone.type Ar,
    icones_comp (cbv_counit (tensor Ar A B)) (cbv_m2 A B) =
    tensor_mor (cbv_counit A) (cbv_counit B);
  cbv_counit_monoidal0 :
    icones_comp (cbv_counit (cone_one_car Ar)) cbv_m0 =
    icones_id Ar (cone_one_car Ar);
}.

Arguments CBV_Model {R} Ar.

(** *** The canonical CBV model on [ICones] — the headline witness

    Every field populated by a proved lemma of this file (and of
    [em_cat.v]/[em_cartesian.v]/[smcc.v]).  [ICones_CBV] is AXIOM-FREE
    modulo the three classical [boolp] axioms, as for [ICones_Seely]. *)
Definition ICones_CBV (R : realType) (Ar : MeasSubcat R) : CBV_Model Ar :=
  {| cbv_smcc := ICones_smcc Ar;
     cbv_em := ICones_EM Ar;
     cbv_cart := ICones_EM_cartesian Ar;
     cbv_U_obj := @U_obj R Ar;
     cbv_U_mor := @U_mor R Ar;
     cbv_bang_obj := @bang_cofree R Ar;
     cbv_bang_mor := @bang_cofree_hom R Ar;
     cbv_unit := @adj_unit R Ar;
     cbv_counit := @adj_counit R Ar;
     cbv_phi := @adj_phi R Ar;
     cbv_psi := @adj_psi R Ar;
     cbv_phiK := @adj_phiK R Ar;
     cbv_psiK := @adj_psiK R Ar;
     cbv_triangleL := @adj_triangleL R Ar;
     cbv_triangleR := @adj_triangleR R Ar;
     cbv_U_prod := @EM_prod_obj R Ar;
     cbv_U_term := @EM_term_obj R Ar;
     cbv_m2 := @m_bang R Ar;
     cbv_m0 := @unit_cofree_str R Ar;
     cbv_bang_m := @bang_m R Ar;
     cbv_bang_e0 := @bang_e0 R Ar;
     cbv_lax_assoc := @bang_lax_assoc R Ar;
     cbv_lax_braid := @bang_lax_braid R Ar;
     cbv_counit_monoidal2 := @adj_counit_monoidal2 R Ar;
     cbv_counit_monoidal0 := @adj_counit_monoidal0 R Ar |}.

Arguments ICones_CBV {R} Ar.
