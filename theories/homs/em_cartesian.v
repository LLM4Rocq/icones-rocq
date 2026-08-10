(**md**************************************************************************)
(** * The cartesian structure of [EM(!)] — CBV §3 (Melliès Prop 26–28)

    Step 3 of the call-by-value roadmap
    ([/home/rocq/prime_gap/icones-cbv-plan.md], Phase C).  We equip the
    Eilenberg–Moore category [EM(!)] of the exponential comonad [!] with
    the cartesian structure whose product is carried by the *linear* tensor
    [⊗] (NOT the cartesian [&]) and whose terminal object is the tensor
    unit [1].  This is the content of Melliès' Proposition 28 (the only
    genuinely non-formal step of the linear-category axiomatisation).

    **Which path is delivered.**  The FULL [EM(!)] — every [!]-coalgebra,
    not a subcategory.  Melliès flags Prop 28 / Cor 20 — "the diagonal
    [d_A] is a coalgebra morphism" — as "not so immediate", and the right
    proof is STRUCTURAL (a retraction/lifting argument), NOT a point
    computation: the transported maps [d_A = (ε⊗ε)∘d_{!A}∘a],
    [e_A = e_{!A}∘a] (Eq 88) are built from [d_bang]/[e_bang], which only
    *compute* on promoted points [x!] — and for a general coalgebra [a x]
    is not promoted — so a point argument cannot work.  Instead we follow
    Melliès verbatim:
    - **Prop 26** ([diagram81]): the structure map [a] is a comonoid
      morphism [P → !̃A], i.e. [(a⊗a)∘d_A = d_{!A}∘a].  In our model this
      is the already-GENERAL [coalg_mor_d] at the unit [a] + [coalg_d_cofree].
    - **Prop 27** ([transp_*]): a retract of a commutative comonoid is one.
      A generic SMC transport by split-mono cancellation ([lcancel_mono]) +
      the associator/braiding/unitor naturality + Diagram (85) = [diagram81].
    - **Cor 20** ([coalg_mor_lift], Melliès §6.11 Prop 20): the lifting
      property — if [i] is a coalgebra morphism with a retraction
      [r∘i = id] and [i∘f] is a coalgebra morphism, then [f] is.  Applied
      at the retraction [(a⊗a) / (ε⊗ε)] this shows [d_A] is a coalgebra
      morphism ([coalg_d_is_mor_gen]); [e_A] is the easy composite
      ([coalg_e_is_mor_gen]).
    - **Cor 17**: the resulting commutative comonoid on every object makes
      [(EM(!), ⊗, 1)] cartesian.

    The bundling of all this is [EMComon_all : forall P, EMComon P] —
    UNCONDITIONAL — and hence the cartesian universal property holds for
    ALL coalgebras (no per-object [EMComon] hypothesis threaded anymore).

    Contents:
    - [m_bang A B : !A⊗!B ⊸ !(A⊗B)] — the lax symmetric-monoidal structure
      map of [!], with [m_bang_prom]: [m(x!⊗y!) = (x⊗y)!]; the
      compatibility lemmas [der_m_bang], [tens_cofree_str_m_bang],
      [m_bang_is_coalg_mor].
    - [EM_prod_str]/[EM_prod] — the product coalgebra [(A⊗B, m∘(a⊗b))];
      [EM_term] — the terminal coalgebra [(1, ·)] ([= unit_cofree]).
    - [coalg_d]/[coalg_e] — the Eq-88 transported comonoid on every
      coalgebra; [EMComon P] — the comonoidal predicate (comonoid laws +
      [coalg_d]/[coalg_e] coalgebra morphisms).
    - [diagram81]/[transp_*]/[coalg_mor_lift]/[coalg_d_is_mor_gen]/
      [coalg_e_is_mor_gen] — Melliès Prop 26/27 + Cor 20; [EMComon_all] —
      the headline unconditional comonoid.
    - the projections [em_proj1]/[em_proj2], pairing [em_pair], diagonal,
      and the cartesian universal property [em_proj1_pair]/[em_proj2_pair];
      terminal [em_term_mor]/[em_term_unique] — all for EVERY coalgebra.
    - the headline bundle [ICones_EM_cartesian] (the FULL [EM(!)] cartesian). *)

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

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

(** Seal the tensor/Seely data, as in [seely.v]/[em_seely_comonoid.v], so a
    bare [/=] does not unfold the [tensor_construct] internals (which would
    break the [tensor_morE]/[...Ep] rewrites).

    We ALSO seal the comonad/Seely-comonoid maps [dig]/[der]/[bang_fmap]/
    [prom]/[d_bang]/[e_bang]/[tens_cofree_str]/[unit_cofree_str]/[Coalg].
    These are TRANSPARENT [lin]/[scones] constructions whose internals are
    enormous; without sealing, [rewrite Lfun_comp] (and [/=]) traverse and
    unfold them, blowing up / diverging.  Sealed, the [_prom]/[_dirac]/
    [...E] equational lemmas still rewrite (opacity never blocks rewriting
    WITH an equation), but tactic SCANS stay syntactic and fast. *)
Opaque tensor_mor tensor_assoc tensor_lunit tensor_runit tensor_braid
       ptensor tau Seely2.
Opaque dig der prom bang_fmap d_bang e_bang unit_cofree_str Coalg.
(* [tens_cofree_str] and [m_bang] are sealed LATER (after the lemmas that
   need to unfold them: [m_bang_prom]/[tens_cofree_str_m_bang]). *)

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section EMCartesian.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

Local Notation "B '⊗' C" := (tensor Ar B C)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '!'" := (prom x) (at level 2, format "x '!'").
Local Notation Bg := (@Bang R Ar).

(** ** The lax symmetric-monoidal structure map [m_{A,B}]

    [m_{A,B} : !A ⊗ !B ⊸ !(A⊗B)] makes [!] a lax symmetric monoidal
    endofunctor of [(⊗,1)] and so lifts [⊗] to [EM(!)].  We build it from
    step 2's [tens_cofree_str] (the transport of [dig] across [Seely2]) and
    the counit [der]:
      [m_{A,B} = !(ε_A ⊗ ε_B) ∘ tens_cofree_str_{A,B}].
    This sidesteps the absent canonical comparison [A&B → A⊗B]: we go
    [!A⊗!B → !(!A⊗!B) → !(A⊗B)] using [der⊗der], never [&→⊗]. *)
Definition m_bang (A B : ICone.type Ar) :
    icones_hom Ar (Bg A ⊗ Bg B) (Bg (A ⊗ B)) :=
  icones_comp (bang_fmap (tensor_mor (der A) (der B))) (tens_cofree_str A B).

(** A pure-tensor product of two unit-ball points is in the unit ball. *)
Lemma ptensor_prom_ball (A B : ICone.type Ar) (x : A) (y : B) :
  cone_norm x <= 1 -> cone_norm y <= 1 -> cone_norm (x ⊗p y) <= 1.
Proof.
move=> Hx Hy.
apply: le_trans (tensor_norm_le _ _) _; rewrite -[1]mulr1.
by apply: ler_pM => //; [exact: cone_norm_ge0 | exact: cone_norm_ge0].
Qed.
Arguments ptensor_prom_ball {A B x y}.

(** The step-2 transported structure sends a promoted pure tensor to its
    promotion, [tens_cofree_str_{A,B}(x! ⊗ y!) = (x! ⊗ y!)!], is
    [em_seely_comonoid.v]'s [tens_cofree_str_prom] — factored there, where
    it already discharges [tens_cofree_coassoc] and [d_bang_is_coalg_mor];
    it arrives here with all arguments implicit, so [m_bang_prom] and
    [tens_cofree_str_m_bang] below apply it as [tens_cofree_str_prom Hx Hy]. *)

(** [m_{A,B}(x! ⊗ y!) = (x ⊗ y)!] for unit-ball points: [tens_cofree_str]
    sends [x!⊗y!] to [(x!⊗y!)!], then [!(ε⊗ε)] sends it to
    [((ε⊗ε)(x!⊗y!))! = (x⊗y)!]. *)
Lemma m_bang_prom (A B : ICone.type Ar) (x : A) (y : B) :
  cone_norm x <= 1 -> cone_norm y <= 1 ->
  Lfun (m_bang A B) (x! ⊗p y!) = (x ⊗p y)!.
Proof.
move=> Hx Hy.
have Hpt : cone_norm (x! ⊗p y!) <= 1 by exact: ptensor_prom_ball (prom_ball Hx) (prom_ball Hy).
rewrite /m_bang.
rewrite -[Lfun (icones_comp (bang_fmap (tensor_mor (der A) (der B))) (tens_cofree_str A B)) _]
        /(Lfun (bang_fmap (tensor_mor (der A) (der B))) (Lfun (tens_cofree_str A B) (x! ⊗p y!))).
rewrite (tens_cofree_str_prom Hx Hy).
rewrite (bang_fmap_prom (tensor_mor (der A) (der B)) (x! ⊗p y!) Hpt).
by rewrite tensor_morE (der_prom x Hx) (der_prom y Hy).
Qed.
Arguments m_bang_prom {A B x y}.

(** Seal [m_bang] now that its pointwise law [m_bang_prom] is proved (cf.
    the comonad-map sealing above): downstream proofs only use the [_prom]
    equation, never the [icones_comp]/[bang_fmap] internals. *)
Opaque m_bang.

(** [der_{A⊗B} ∘ m_{A,B} = ε_A ⊗ ε_B] (the monoidal-comonad counit
    compatibility), as maps out of [!A⊗!B].  Both send [x!⊗y!] to [x⊗y].
    Used for the product-coalgebra counit law. *)
Lemma der_m_bang (A B : ICone.type Ar) :
  icones_comp (der (A ⊗ B)) (m_bang A B) =
  tensor_mor (der A) (der B).
Proof.
apply: tens_excl_charact => x y Hx Hy.
rewrite -[Lfun (icones_comp (der (A ⊗ B)) (m_bang A B)) _]
        /(Lfun (der (A ⊗ B)) (Lfun (m_bang A B) (x! ⊗p y!))).
rewrite (m_bang_prom Hx Hy) (der_prom (x ⊗p y) (ptensor_prom_ball Hx Hy)).
by rewrite tensor_morE (der_prom x Hx) (der_prom y Hy).
Qed.

(** [tens_cofree_str_{A,B} = m_{!A,!B} ∘ (dig_A ⊗ dig_B)], as maps out of
    [!A⊗!B].  Both send [x!⊗y!] to [(x!⊗y!)!].  This rewrites the step-2
    transported structure into [m]-shape for the coassoc chase. *)
Lemma tens_cofree_str_m_bang (A B : ICone.type Ar) :
  tens_cofree_str A B =
  icones_comp (m_bang (Bg A) (Bg B)) (tensor_mor (dig A) (dig B)).
Proof.
apply: tens_excl_charact => x y Hx Hy.
(* LHS: [tens_cofree_str (x!⊗y!) = (x!⊗y!)!]. *)
rewrite (tens_cofree_str_prom Hx Hy).
(* RHS: [m_{!A,!B}((dig⊗dig)(x!⊗y!)) = m_{!A,!B}((x!)!⊗(y!)!) = (x!⊗y!)!]. *)
rewrite -[Lfun (icones_comp (m_bang (Bg A) (Bg B)) (tensor_mor (dig A) (dig B))) _]
        /(Lfun (m_bang (Bg A) (Bg B)) (Lfun (tensor_mor (dig A) (dig B)) (x! ⊗p y!))).
rewrite tensor_morE (dig_prom x Hx) (dig_prom y Hy).
by rewrite (m_bang_prom (prom_ball Hx) (prom_ball Hy)).
Qed.

(** Seal [tens_cofree_str] now that the two lemmas needing to unfold it
    ([m_bang_prom], [tens_cofree_str_m_bang]) are proved. *)
Opaque tens_cofree_str.

(** The structure map of [tens_cofree A B] is [tens_cofree_str A B]
    (definitional projection; stated as a lemma so [rewrite] can fold it
    WITHOUT the heavyweight [/=] that would expand [m_bang]/[tens_cofree_str]
    into their [lin]/[scones] internals and diverge). *)
Lemma tens_cofree_strE (A B : ICone.type Ar) :
  coalg_str (tens_cofree A B) = tens_cofree_str A B.
Proof. by []. Qed.

(** [m_{A,B}] is a coalgebra morphism [tens_cofree A B → !̃(A⊗B)]:
    [dig_{A⊗B} ∘ m_{A,B} = !(m_{A,B}) ∘ tens_cofree_str_{A,B}].  Both send
    [x!⊗y!] to [((x⊗y)!)!]. *)
Lemma m_bang_is_coalg_mor (A B : ICone.type Ar) :
  is_coalg_mor (tens_cofree A B) (bang_cofree (A ⊗ B)) (m_bang A B).
Proof.
rewrite /is_coalg_mor (bang_cofree_str (A ⊗ B)) (tens_cofree_strE A B).
apply: tens_excl_charact => x y Hx Hy.
have Hpt : cone_norm (x! ⊗p y!) <= 1
  by exact: ptensor_prom_ball (prom_ball Hx) (prom_ball Hy).
(* The RHS carries the heavy [tens_cofree_str]/[m_bang] terms, so EVERY
   rewrite below is scoped to [in LHS]/[in RHS] to avoid whole-goal
   conversion scans (which diverge on those [lin]/[scones] internals). *)
(* LHS: [dig (m (x!⊗y!)) = dig ((x⊗y)!) = ((x⊗y)!)!]. *)
rewrite [in LHS]Lfun_comp [in LHS](m_bang_prom Hx Hy).
rewrite [in LHS](dig_prom (x ⊗p y) (ptensor_prom_ball Hx Hy)).
(* RHS: [!m (tens_cofree_str (x!⊗y!)) = !m ((x!⊗y!)!) = (m(x!⊗y!))!
        = ((x⊗y)!)!]. *)
rewrite [in RHS]Lfun_comp [in RHS](tens_cofree_str_prom Hx Hy).
rewrite [in RHS](bang_fmap_prom (m_bang A B) (x! ⊗p y!) Hpt).
by rewrite [in RHS](m_bang_prom Hx Hy).
Qed.

(** Monoidal-comonad coassociativity of [m] (direct equation form):
    [dig_{A⊗B} ∘ m_{A,B} = !(m_{A,B}) ∘ m_{!A,!B} ∘ (dig_A ⊗ dig_B)].
    Combines [m_bang_is_coalg_mor] (with [coalg_str] projected to [dig]/
    [tens_cofree_str]) and [tens_cofree_str_m_bang]. *)
Lemma m_bang_coassoc (A B : ICone.type Ar) :
  icones_comp (dig (A ⊗ B)) (m_bang A B) =
  icones_comp (bang_fmap (m_bang A B))
    (icones_comp (m_bang (Bg A) (Bg B)) (tensor_mor (dig A) (dig B))).
Proof.
have H := m_bang_is_coalg_mor A B.
rewrite /is_coalg_mor (bang_cofree_str (A ⊗ B)) (tens_cofree_strE A B) in H.
by rewrite H (tens_cofree_str_m_bang A B).
Qed.

(** ** Bifunctoriality of [⊗] on morphisms (a small local helper)

    [(g1 ∘ f1) ⊗ (g2 ∘ f2) = (g1 ⊗ g2) ∘ (f1 ⊗ f2)].  Agreement on pure
    tensors by [tensor_morE]. *)
Lemma tensor_mor_comp (B1 B2 B3 C1 C2 C3 : ICone.type Ar)
    (g1 : icones_hom Ar B2 B3) (f1 : icones_hom Ar B1 B2)
    (g2 : icones_hom Ar C2 C3) (f2 : icones_hom Ar C1 C2) :
  tensor_mor (icones_comp g1 f1) (icones_comp g2 f2) =
  icones_comp (tensor_mor g1 g2) (tensor_mor f1 f2).
Proof.
apply: tensor_ext => x y.
rewrite tensor_morE.
rewrite -[Lfun (icones_comp (tensor_mor g1 g2) (tensor_mor f1 f2)) _]
        /(Lfun (tensor_mor g1 g2) (Lfun (tensor_mor f1 f2) (x ⊗p y))).
by rewrite !tensor_morE.
Qed.

(** Naturality of [m]: [m_{A',B'} ∘ (!f ⊗ !g) = !(f⊗g) ∘ m_{A,B}].
    On [x!⊗y!] both sides give [(f x ⊗ g y)!]. *)
Lemma m_bang_nat (A A' B B' : ICone.type Ar)
    (f : icones_hom Ar A A') (g : icones_hom Ar B B') :
  icones_comp (m_bang A' B') (tensor_mor (bang_fmap f) (bang_fmap g)) =
  icones_comp (bang_fmap (tensor_mor f g)) (m_bang A B).
Proof.
apply: tens_excl_charact => x y Hx Hy.
(* LHS *)
rewrite -[Lfun (icones_comp (m_bang A' B') (tensor_mor (bang_fmap f) (bang_fmap g))) _]
        /(Lfun (m_bang A' B') (Lfun (tensor_mor (bang_fmap f) (bang_fmap g)) (x! ⊗p y!))).
rewrite tensor_morE (bang_fmap_prom f x Hx) (bang_fmap_prom g y Hy).
have Hf : cone_norm (Lfun f x) <= 1 by exact: (ders_lin_ball f Hx).
have Hg : cone_norm (Lfun g y) <= 1 by exact: (ders_lin_ball g Hy).
rewrite (m_bang_prom Hf Hg).
(* RHS *)
rewrite -[Lfun (icones_comp (bang_fmap (tensor_mor f g)) (m_bang A B)) _]
        /(Lfun (bang_fmap (tensor_mor f g)) (Lfun (m_bang A B) (x! ⊗p y!))).
rewrite (m_bang_prom Hx Hy).
rewrite (bang_fmap_prom (tensor_mor f g) (x ⊗p y) (ptensor_prom_ball Hx Hy)).
by rewrite tensor_morE.
Qed.

(** ** The product coalgebra [EM_prod] — Paper §7.4, the lifted [⊗]

    For coalgebras [(A,a)] and [(B,b)], the product carrier is the LINEAR
    tensor [A⊗B] with structure map [s = m_{A,B} ∘ (a⊗b) : A⊗B ⊸ !(A⊗B)].
    Both coalgebra laws are GENERAL (every coalgebra), proved through the
    [m_bang] compatibility lemmas above (whose domain [!A⊗!B] is reducible
    by [tens_excl_charact]) — no Cor 20 needed. *)

Definition EM_prod_str (P Q : Coalgebra Ar) :
    icones_hom Ar (coalg_obj P ⊗ coalg_obj Q) (Bg (coalg_obj P ⊗ coalg_obj Q)) :=
  icones_comp (m_bang (coalg_obj P) (coalg_obj Q))
    (tensor_mor (coalg_str P) (coalg_str Q)).

(** Counit law: [der ∘ s = id].
    [der ∘ m ∘ (a⊗b) = (der⊗der) ∘ (a⊗b) = (der∘a)⊗(der∘b) = id⊗id = id]. *)
Lemma EM_prod_counit (P Q : Coalgebra Ar) :
  icones_comp (der (coalg_obj P ⊗ coalg_obj Q)) (EM_prod_str P Q) =
  icones_id Ar (coalg_obj P ⊗ coalg_obj Q).
Proof.
rewrite /EM_prod_str icones_compA (der_m_bang (coalg_obj P) (coalg_obj Q)).
rewrite -(tensor_mor_comp (der (coalg_obj P)) (coalg_str P)
                          (der (coalg_obj Q)) (coalg_str Q)).
by rewrite (coalg_counit P) (coalg_counit Q) tensor_mor_id.
Qed.

(** Coassociativity: [dig ∘ s = !s ∘ s]. *)
Lemma EM_prod_coassoc (P Q : Coalgebra Ar) :
  icones_comp (dig (coalg_obj P ⊗ coalg_obj Q)) (EM_prod_str P Q) =
  icones_comp (bang_fmap (EM_prod_str P Q)) (EM_prod_str P Q).
Proof.
rewrite /EM_prod_str.
(* Reassociate the LHS [dig ∘ (m ∘ (a⊗b)) → (dig ∘ m) ∘ (a⊗b)] (scoped so
   the [!s∘s] RHS, whose [m∘(a⊗b)] is hidden under the opaque [bang_fmap],
   is never disturbed), then pull [dig∘m] out by [m_bang_coassoc]. *)
rewrite [in LHS]icones_compA [in LHS](m_bang_coassoc (coalg_obj P) (coalg_obj Q)).
(* fully right-associate the LHS *)
rewrite -[in LHS]icones_compA -[in LHS]icones_compA.
(* combine [(dig⊗dig) ∘ (a⊗b)] = [(dig∘a)⊗(dig∘b)] *)
rewrite -[in LHS](tensor_mor_comp (dig (coalg_obj P)) (coalg_str P)
                          (dig (coalg_obj Q)) (coalg_str Q)).
rewrite [in LHS](coalg_coassoc P) [in LHS](coalg_coassoc Q).
(* split [(!a∘a)⊗(!b∘b)] = [(!a⊗!b) ∘ (a⊗b)] *)
rewrite [in LHS](tensor_mor_comp (bang_fmap (coalg_str P)) (coalg_str P)
                         (bang_fmap (coalg_str Q)) (coalg_str Q)).
(* LHS now [!m ∘ (m!! ∘ ((!a⊗!b) ∘ (a⊗b)))]; pull [!(a⊗b)] across [m!!] *)
rewrite [in LHS](icones_compA (m_bang (Bg (coalg_obj P)) (Bg (coalg_obj Q)))).
rewrite [in LHS](m_bang_nat (coalg_str P) (coalg_str Q)).
(* LHS now [!m ∘ ((!(a⊗b) ∘ m) ∘ (a⊗b))]; reassociate to expose [!m ∘ !(a⊗b)] *)
rewrite [in LHS](icones_compA (bang_fmap (m_bang (coalg_obj P) (coalg_obj Q)))).
rewrite [in LHS](icones_compA (bang_fmap (m_bang (coalg_obj P) (coalg_obj Q)))).
rewrite -[in LHS](bang_fmap_comp (m_bang (coalg_obj P) (coalg_obj Q))
                         (tensor_mor (coalg_str P) (coalg_str Q))).
(* LHS is now [((!(m∘(a⊗b)) ∘ m) ∘ (a⊗b))] = [!(m∘(a⊗b)) ∘ (m∘(a⊗b))] = RHS *)
by rewrite -[in LHS]icones_compA.
Qed.

Definition EM_prod (P Q : Coalgebra Ar) : Coalgebra Ar :=
  MkCoalgebra (EM_prod_counit P Q) (EM_prod_coassoc P Q).

Lemma EM_prod_obj (P Q : Coalgebra Ar) :
  coalg_obj (EM_prod P Q) = (coalg_obj P ⊗ coalg_obj Q).
Proof. by []. Qed.

Lemma EM_prod_str_E (P Q : Coalgebra Ar) :
  coalg_str (EM_prod P Q) = EM_prod_str P Q.
Proof. by []. Qed.

(** ** The terminal coalgebra [EM_term]

    The tensor unit [1] with the step-2 transported structure
    [unit_cofree_str] is the terminal object of [EM(!)]: every coalgebra
    has a unique morphism into it. *)
Definition EM_term : Coalgebra Ar := unit_cofree.

Lemma EM_term_obj : coalg_obj EM_term = cone_one_car Ar.
Proof. by []. Qed.

(** ** The transported comonoid on every coalgebra — Eq 88

    For a coalgebra [(A,a)] the comonoid maps are transported from the
    Seely comonoid on the cofree object [!A] along the retraction
    [A —a→ !A —ε→ A] ([ε∘a = id], [coalg_counit]):
      [coalg_d = (ε⊗ε) ∘ d_{!A} ∘ a : A ⊸ A⊗A]   (Eq 88, diagonal)
      [coalg_e = e_{!A} ∘ a : A ⊸ 1]              (Eq 88, counit).
    These are the comonoid maps of [EMComon]; the comonoid laws and the
    coalgebra-morphism squares (Cor 20) hold for EVERY coalgebra
    ([EMComon_all]). *)
Definition coalg_d (P : Coalgebra Ar) :
    icones_hom Ar (coalg_obj P) (coalg_obj P ⊗ coalg_obj P) :=
  icones_comp (tensor_mor (der (coalg_obj P)) (der (coalg_obj P)))
    (icones_comp (d_bang (coalg_obj P)) (coalg_str P)).

Definition coalg_e (P : Coalgebra Ar) :
    icones_hom Ar (coalg_obj P) (cone_one_car Ar) :=
  icones_comp (e_bang (coalg_obj P)) (coalg_str P).

(** ** The comonoidal structure — Prop 26/27 + Cor 20

    [EMComon P] bundles the facts that Melliès' Prop 28 establishes for a
    coalgebra [P]:
    - the four commutative-comonoid laws for [(coalg_obj P, coalg_d, coalg_e)]
      (coassociativity, both counits, cocommutativity) — Prop 27;
    - [coalg_d P] is a coalgebra morphism [P → EM_prod P P] — Cor 20;
    - [coalg_e P] is a coalgebra morphism [P → EM_term] — Prop 26 (easy).

    [EMComon P] holds for EVERY coalgebra ([EMComon_all], proved further
    down via the structural Cor-20 lifting — NOT a point computation).  From
    it the cartesian universal property (Cor 17) is derived for ALL
    coalgebras below — [(EM(!), ⊗, 1)] is cartesian (Prop 28). *)
Record EMComon (P : Coalgebra Ar) : Type := MkEMComon {
  emc_coassoc :
    icones_comp (iso_fwd (tensor_assoc (coalg_obj P) (coalg_obj P) (coalg_obj P)))
      (icones_comp (tensor_mor (coalg_d P) (icones_id Ar (coalg_obj P))) (coalg_d P)) =
    icones_comp (tensor_mor (icones_id Ar (coalg_obj P)) (coalg_d P)) (coalg_d P);
  emc_counitL :
    icones_comp (iso_fwd (tensor_lunit (coalg_obj P)))
      (icones_comp (tensor_mor (coalg_e P) (icones_id Ar (coalg_obj P))) (coalg_d P)) =
    icones_id Ar (coalg_obj P);
  emc_counitR :
    icones_comp (iso_fwd (tensor_runit (coalg_obj P)))
      (icones_comp (tensor_mor (icones_id Ar (coalg_obj P)) (coalg_e P)) (coalg_d P)) =
    icones_id Ar (coalg_obj P);
  emc_cocomm :
    icones_comp (iso_fwd (tensor_braid (coalg_obj P) (coalg_obj P))) (coalg_d P) =
    coalg_d P;
  emc_d_mor : is_coalg_mor P (EM_prod P P) (coalg_d P);
  emc_e_mor : is_coalg_mor P EM_term (coalg_e P);
}.

End EMCartesian.

Arguments m_bang {R Ar} A B.
Arguments ptensor_prom_ball {R Ar A B x y}.
Arguments m_bang_prom {R Ar A B x y}.
Arguments der_m_bang {R Ar} A B.
Arguments tens_cofree_str_m_bang {R Ar} A B.
Arguments m_bang_is_coalg_mor {R Ar} A B.
Arguments tensor_mor_comp {R Ar B1 B2 B3 C1 C2 C3} g1 f1 g2 f2.
Arguments m_bang_nat {R Ar A A' B B'} f g.
Arguments EM_prod_str {R Ar} P Q.
Arguments EM_prod {R Ar} P Q.
Arguments EM_term {R Ar}.
Arguments coalg_d {R Ar} P.
Arguments coalg_e {R Ar} P.
Arguments EMComon {R Ar} P.
Arguments emc_coassoc {R Ar P}.
Arguments emc_counitL {R Ar P}.
Arguments emc_counitR {R Ar P}.
Arguments emc_cocomm {R Ar P}.
Arguments emc_d_mor {R Ar P}.
Arguments emc_e_mor {R Ar P}.

(** ** Witness 1 — the cofree coalgebras [!̃B] are comonoidal

    On [bang_cofree B] the Eq-88 comonoid recovers EXACTLY the step-2 Seely
    comonoid [d_bang]/[e_bang], so every [EMComon] field is a step-2 lemma
    ([comonoid_*], [d_bang_is_coalg_mor], [e_bang_is_coalg_mor]). *)
Section CofreeComonoidal.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation "B '⊗' C" := (tensor Ar B C)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '!'" := (prom x) (at level 2, format "x '!'").
Local Notation Bg := (@Bang R Ar).

(** [coalg_d (!̃B) = d_bang B].  On [x!]:
    [coalg_d (x!) = (ε⊗ε)(d_{!B}(dig_B(x!))) = (ε⊗ε)(d_{!B}((x!)!))
    = (ε⊗ε)((x!)! ⊗ (x!)!) = x! ⊗ x! = d_bang B (x!)]. *)
Lemma coalg_d_cofree (B : ICone.type Ar) :
  coalg_d (bang_cofree B) = d_bang B.
Proof.
rewrite /coalg_d; apply: bang_ext => x Hx.
rewrite -[Lfun (icones_comp (tensor_mor (der (Bg B)) (der (Bg B)))
                  (icones_comp (d_bang (Bg B)) (coalg_str (bang_cofree B)))) x!]
        /(Lfun (tensor_mor (der (Bg B)) (der (Bg B)))
          (Lfun (icones_comp (d_bang (Bg B)) (coalg_str (bang_cofree B))) x!)).
rewrite -[Lfun (icones_comp (d_bang (Bg B)) (coalg_str (bang_cofree B))) x!]
        /(Lfun (d_bang (Bg B)) (Lfun (coalg_str (bang_cofree B)) x!)).
rewrite bang_cofree_str (dig_prom x Hx) (d_bang_prom x! (prom_ball Hx)).
rewrite (tensor_morE (der (Bg B)) (der (Bg B)) (x!)! (x!)!).
rewrite (der_prom x! (prom_ball Hx)).
by rewrite (d_bang_prom x Hx).
Qed.

(** [coalg_e (!̃B) = e_bang B].  On [x!]:
    [coalg_e (x!) = e_{!B}(dig_B(x!)) = e_{!B}((x!)!) = 1 = e_bang B (x!)]. *)
Lemma coalg_e_cofree (B : ICone.type Ar) :
  coalg_e (bang_cofree B) = e_bang B.
Proof.
rewrite /coalg_e; apply: bang_ext => x Hx.
rewrite -[Lfun (icones_comp (e_bang (Bg B)) (coalg_str (bang_cofree B))) x!]
        /(Lfun (e_bang (Bg B)) (Lfun (coalg_str (bang_cofree B)) x!)).
rewrite bang_cofree_str (dig_prom x Hx).
by rewrite (e_bang_prom x! (prom_ball Hx)) (e_bang_prom x Hx).
Qed.

(** The product coalgebra of two cofree objects has the same structure map
    as the step-2 transported coalgebra [tens_cofree B B]
    ([EM_prod_str = m ∘ (dig ⊗ dig) = tens_cofree_str], by
    [tens_cofree_str_m_bang]). *)
Lemma EM_prod_str_cofree (B : ICone.type Ar) :
  EM_prod_str (bang_cofree B) (bang_cofree B) = tens_cofree_str B B.
Proof.
by rewrite /EM_prod_str /= -(tens_cofree_str_m_bang B B).
Qed.

(** ([coalg_d_cofree]/[coalg_e_cofree]/[EM_prod_str_cofree] are the
    load-bearing facts: they feed [diagram81]/[diagram89e]/
    [coalg_d_is_mor_gen], i.e. the GENERAL Cor-20 argument.  The comonoidal
    structure on the cofree coalgebras themselves is now just the
    unconditional [EMComon_all] specialised — see [EMComon_cofree]
    below.) *)

End CofreeComonoidal.

Arguments coalg_d_cofree {R Ar} B.
Arguments coalg_e_cofree {R Ar} B.
Arguments EM_prod_str_cofree {R Ar} B.

(** ** The cartesian universal property — Melliès Corollary 17

    From a pair of comonoidal objects we build the binary-product universal
    property of [(EM_prod, EM_term)] in [EM(!)].  The pieces:
    - [EM_prod_mor] — [⊗] is a bifunctor ON [EM(!)] (tensor of coalgebra
      morphisms is a coalgebra morphism), GENERAL;
    - [coalg_mor_is_comonoid] — every coalgebra morphism is a comonoid
      morphism (Melliès' "nearly immediate" naturality), GENERAL;
    - the projections, pairing and diagonal, and the [β]/[η] laws of the
      product, plus the terminal universal property. *)
Section CartesianUP.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation "B '⊗' C" := (tensor Ar B C)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '!'" := (prom x) (at level 2, format "x '!'").
Local Notation Bg := (@Bang R Ar).

(** *** [⊗] is a bifunctor on [EM(!)] (GENERAL)

    If [f : P → P'] and [g : Q → Q'] are coalgebra morphisms then
    [f ⊗ g : EM_prod P Q → EM_prod P' Q'] is a coalgebra morphism. *)
Lemma EM_prod_mor (P P' Q Q' : Coalgebra Ar)
    (f : icones_hom Ar (coalg_obj P) (coalg_obj P'))
    (g : icones_hom Ar (coalg_obj Q) (coalg_obj Q')) :
  is_coalg_mor P P' f -> is_coalg_mor Q Q' g ->
  is_coalg_mor (EM_prod P Q) (EM_prod P' Q') (tensor_mor f g).
Proof.
move=> Hf Hg.
rewrite /is_coalg_mor.
rewrite (EM_prod_str_E P' Q') (EM_prod_str_E P Q) /EM_prod_str.
(* LHS: [m' ∘ (a'⊗b') ∘ (f⊗g) = m' ∘ ((a'∘f)⊗(b'∘g))
        = m' ∘ ((!f∘a)⊗(!g∘b)) = m' ∘ (!f⊗!g) ∘ (a⊗b)
        = !(f⊗g) ∘ m ∘ (a⊗b)]. *)
rewrite -icones_compA -(tensor_mor_comp (coalg_str P') f (coalg_str Q') g).
rewrite /is_coalg_mor in Hf Hg; rewrite Hf Hg.
rewrite (tensor_mor_comp (bang_fmap f) (coalg_str P) (bang_fmap g) (coalg_str Q)).
rewrite (icones_compA (m_bang (coalg_obj P') (coalg_obj Q'))) (m_bang_nat f g).
by rewrite -!icones_compA.
Qed.

(** *** Naturality of the unitors and braiding w.r.t. plain maps

    Small SMC helpers (no [!] content), by [tensor_ext]. *)
Lemma tensor_runit_nat (A A' : ICone.type Ar) (f : icones_hom Ar A A') :
  icones_comp (iso_fwd (tensor_runit A')) (tensor_mor f (icones_id Ar (cone_one_car Ar))) =
  icones_comp f (iso_fwd (tensor_runit A)).
Proof.
apply: tensor_ext => x u.
rewrite -[Lfun (icones_comp (iso_fwd (tensor_runit A')) (tensor_mor f (icones_id Ar (cone_one_car Ar)))) _]
        /(Lfun (iso_fwd (tensor_runit A')) (Lfun (tensor_mor f (icones_id Ar (cone_one_car Ar))) (x ⊗p u))).
rewrite tensor_morE.
have idu : Lfun (icones_id Ar (cone_one_car Ar)) u = u by [].
rewrite idu tensor_runitEp.
rewrite -[Lfun (icones_comp f (iso_fwd (tensor_runit A))) _]
        /(Lfun f (Lfun (iso_fwd (tensor_runit A)) (x ⊗p u))).
rewrite tensor_runitEp.
by have [_ _ ->] := cones_hom_linear (mcones_hom_cones (icones_hom_mcones f)).
Qed.

Lemma tensor_lunit_nat (A A' : ICone.type Ar) (f : icones_hom Ar A A') :
  icones_comp (iso_fwd (tensor_lunit A')) (tensor_mor (icones_id Ar (cone_one_car Ar)) f) =
  icones_comp f (iso_fwd (tensor_lunit A)).
Proof.
apply: tensor_ext => u x.
rewrite -[Lfun (icones_comp (iso_fwd (tensor_lunit A')) (tensor_mor (icones_id Ar (cone_one_car Ar)) f)) _]
        /(Lfun (iso_fwd (tensor_lunit A')) (Lfun (tensor_mor (icones_id Ar (cone_one_car Ar)) f) (u ⊗p x))).
rewrite tensor_morE.
have idu : Lfun (icones_id Ar (cone_one_car Ar)) u = u by [].
rewrite idu tensor_lunitEp.
rewrite -[Lfun (icones_comp f (iso_fwd (tensor_lunit A))) _]
        /(Lfun f (Lfun (iso_fwd (tensor_lunit A)) (u ⊗p x))).
rewrite tensor_lunitEp.
by have [_ _ ->] := cones_hom_linear (mcones_hom_cones (icones_hom_mcones f)).
Qed.


(** ** Naturality of the associator and braiding (SMC helpers, no [!])

    Companions to [tensor_runit_nat]/[tensor_lunit_nat], proved by
    pure-tensor extensionality. *)
Lemma tensor_braid_nat (A A' C C' : ICone.type Ar)
    (f : icones_hom Ar A A') (g : icones_hom Ar C C') :
  icones_comp (iso_fwd (tensor_braid A' C')) (tensor_mor f g) =
  icones_comp (tensor_mor g f) (iso_fwd (tensor_braid A C)).
Proof.
apply: tensor_ext => x y.
rewrite -[Lfun (icones_comp (iso_fwd (tensor_braid A' C')) (tensor_mor f g)) _]
        /(Lfun (iso_fwd (tensor_braid A' C')) (Lfun (tensor_mor f g) (x ⊗p y))).
rewrite tensor_morE tensor_braidEp.
rewrite -[Lfun (icones_comp (tensor_mor g f) (iso_fwd (tensor_braid A C))) _]
        /(Lfun (tensor_mor g f) (Lfun (iso_fwd (tensor_braid A C)) (x ⊗p y))).
by rewrite tensor_braidEp tensor_morE.
Qed.

Lemma tensor_assoc_nat (A A' B B' C C' : ICone.type Ar)
    (f : icones_hom Ar A A') (g : icones_hom Ar B B') (h : icones_hom Ar C C') :
  icones_comp (iso_fwd (tensor_assoc A' B' C'))
    (tensor_mor (tensor_mor f g) h) =
  icones_comp (tensor_mor f (tensor_mor g h)) (iso_fwd (tensor_assoc A B C)).
Proof.
apply: tensor_ext3 => x y z.
rewrite -[Lfun (icones_comp (iso_fwd (tensor_assoc A' B' C'))
                  (tensor_mor (tensor_mor f g) h)) _]
        /(Lfun (iso_fwd (tensor_assoc A' B' C'))
          (Lfun (tensor_mor (tensor_mor f g) h) ((x ⊗p y) ⊗p z))).
rewrite tensor_morE tensor_morE tensor_assocEp.
rewrite -[Lfun (icones_comp (tensor_mor f (tensor_mor g h)) (iso_fwd (tensor_assoc A B C))) _]
        /(Lfun (tensor_mor f (tensor_mor g h)) (Lfun (iso_fwd (tensor_assoc A B C)) ((x ⊗p y) ⊗p z))).
by rewrite tensor_assocEp tensor_morE tensor_morE.
Qed.


Lemma lcancel_mono (W A0 B0 : ICone.type Ar)
    (i : icones_hom Ar A0 B0) (r : icones_hom Ar B0 A0)
    (f g : icones_hom Ar W A0) :
  icones_comp r i = icones_id Ar A0 ->
  icones_comp i f = icones_comp i g -> f = g.
Proof.
move=> Hri Heq.
have H := congr1 (fun k => icones_comp r k) Heq.
rewrite !icones_compA in H.
rewrite Hri in H.
rewrite !icones_compIl in H.
exact: H.
Qed.

(** ** Proposition 27 — a retract of a commutative comonoid is one

    Generic SMC transport (no [!] content): given a commutative comonoid
    [(B, dB, eB)] and a retraction [A —i→ B —r→ A] ([r∘i = id]) with the
    transported maps [dA := (r⊗r)∘dB∘i], [eA := eB∘i] satisfying Diagram (85)
    [(i⊗i)∘dA = dB∘i], the triple [(A, dA, eA)] is a commutative comonoid.
    Each law is proved by left-cancelling the split mono [i] (resp. [i⊗i],
    [i⊗(i⊗i)]) and reducing to the corresponding [B]-law via (85) and the
    naturality of the structural isos.  This is Melliès' Prop 27 diagram
    chase, organised as explicit [have]-factorisations to keep the
    associativity bookkeeping robust. *)
Section ComonoidTransport.
Variables (A B : ICone.type Ar).
Variables (dB : icones_hom Ar B (B ⊗ B)) (eB : icones_hom Ar B (cone_one_car Ar)).
Variables (i : icones_hom Ar A B) (r : icones_hom Ar B A).
Hypothesis Hri : icones_comp r i = icones_id Ar A.
Hypothesis HBcoassoc :
  icones_comp (iso_fwd (tensor_assoc B B B))
    (icones_comp (tensor_mor dB (icones_id Ar B)) dB) =
  icones_comp (tensor_mor (icones_id Ar B) dB) dB.
Hypothesis HBcounitL :
  icones_comp (iso_fwd (tensor_lunit B))
    (icones_comp (tensor_mor eB (icones_id Ar B)) dB) = icones_id Ar B.
Hypothesis HBcounitR :
  icones_comp (iso_fwd (tensor_runit B))
    (icones_comp (tensor_mor (icones_id Ar B) eB) dB) = icones_id Ar B.
Hypothesis HBcocomm :
  icones_comp (iso_fwd (tensor_braid B B)) dB = dB.
Local Notation dA := (icones_comp (tensor_mor r r) (icones_comp dB i)).
Local Notation eA := (icones_comp eB i).
Hypothesis H85 : icones_comp (tensor_mor i i) dA = icones_comp dB i.

(* (i⊗i) is split mono with left inverse (r⊗r) *)
Let Hri2 : icones_comp (tensor_mor r r) (tensor_mor i i) = icones_id Ar (A ⊗ A).
Proof. by rewrite -(tensor_mor_comp r i r i) Hri tensor_mor_id. Qed.

Lemma transp_counitL :
  icones_comp (iso_fwd (tensor_lunit A))
    (icones_comp (tensor_mor eA (icones_id Ar A)) dA) = icones_id Ar A.
Proof.
apply: (lcancel_mono (i := i) (r := r) Hri); rewrite icones_compIr.
(* eA ⊗ i = (eB ⊗ id_B) ∘ (i ⊗ i) *)
have F : tensor_mor eA i = icones_comp (tensor_mor eB (icones_id Ar B)) (tensor_mor i i).
  by rewrite -(tensor_mor_comp eB i (icones_id Ar B) i) icones_compIl.
(* i ∘ λ_A = λ_B ∘ (id_1 ⊗ i) ; combine with (eA ⊗ id_A) into eA ⊗ i *)
rewrite (icones_compA i (iso_fwd (tensor_lunit A))) -(tensor_lunit_nat i).
rewrite -(icones_compA (iso_fwd (tensor_lunit B))).
rewrite (icones_compA (tensor_mor (icones_id Ar (cone_one_car Ar)) i)).
rewrite -(tensor_mor_comp (icones_id Ar (cone_one_car Ar)) eA i (icones_id Ar A)).
rewrite icones_compIl icones_compIr.
(* now λ_B ∘ ((eA⊗i) ∘ dA) ; rewrite eA⊗i, apply (85), then B-counitL *)
rewrite F.
rewrite -(icones_compA (tensor_mor eB (icones_id Ar B)) (tensor_mor i i) dA) H85.
rewrite (icones_compA (tensor_mor eB (icones_id Ar B)) dB i).
rewrite (icones_compA (iso_fwd (tensor_lunit B)) (icones_comp (tensor_mor eB (icones_id Ar B)) dB) i).
by rewrite HBcounitL icones_compIl.
Qed.

Lemma transp_counitR :
  icones_comp (iso_fwd (tensor_runit A))
    (icones_comp (tensor_mor (icones_id Ar A) eA) dA) = icones_id Ar A.
Proof.
apply: (lcancel_mono (i := i) (r := r) Hri); rewrite icones_compIr.
have F : tensor_mor i eA = icones_comp (tensor_mor (icones_id Ar B) eB) (tensor_mor i i).
  by rewrite -(tensor_mor_comp (icones_id Ar B) i eB i) icones_compIl.
rewrite (icones_compA i (iso_fwd (tensor_runit A))) -(tensor_runit_nat i).
rewrite -(icones_compA (iso_fwd (tensor_runit B))).
rewrite (icones_compA (tensor_mor i (icones_id Ar (cone_one_car Ar)))).
rewrite -(tensor_mor_comp i (icones_id Ar A) (icones_id Ar (cone_one_car Ar)) eA).
rewrite icones_compIl icones_compIr.
rewrite F.
rewrite -(icones_compA (tensor_mor (icones_id Ar B) eB) (tensor_mor i i) dA) H85.
rewrite (icones_compA (tensor_mor (icones_id Ar B) eB) dB i).
rewrite (icones_compA (iso_fwd (tensor_runit B)) (icones_comp (tensor_mor (icones_id Ar B) eB) dB) i).
by rewrite HBcounitR icones_compIl.
Qed.

Lemma transp_cocomm :
  icones_comp (iso_fwd (tensor_braid A A)) dA = dA.
Proof.
apply: (lcancel_mono (i := tensor_mor i i) (r := tensor_mor r r) Hri2).
(* (i⊗i) ∘ σ_A = σ_B ∘ (i⊗i) *)
rewrite (icones_compA (tensor_mor i i) (iso_fwd (tensor_braid A A))).
rewrite -(tensor_braid_nat i i).
rewrite -(icones_compA (iso_fwd (tensor_braid B B)) (tensor_mor i i) dA) H85.
by rewrite (icones_compA (iso_fwd (tensor_braid B B)) dB i) HBcocomm.
Qed.

Lemma transp_coassoc :
  icones_comp (iso_fwd (tensor_assoc A A A))
    (icones_comp (tensor_mor dA (icones_id Ar A)) dA) =
  icones_comp (tensor_mor (icones_id Ar A) dA) dA.
Proof.
apply: (lcancel_mono (i := tensor_mor i (tensor_mor i i))
                     (r := tensor_mor r (tensor_mor r r))).
  rewrite -(tensor_mor_comp r i (tensor_mor r r) (tensor_mor i i)) Hri.
  by rewrite Hri2 tensor_mor_id.
(* factorisations *)
have FL : tensor_mor (icones_comp dB i) i
        = icones_comp (tensor_mor dB (icones_id Ar B)) (tensor_mor i i).
  by rewrite -(tensor_mor_comp dB i (icones_id Ar B) i) icones_compIl.
have FR : tensor_mor i (icones_comp dB i)
        = icones_comp (tensor_mor (icones_id Ar B) dB) (tensor_mor i i).
  by rewrite -(tensor_mor_comp (icones_id Ar B) i dB i) icones_compIl.
(* LHS: reduce to ((id_B⊗dB)∘dB)∘i via assoc-naturality, (85), B-coassoc *)
rewrite (icones_compA (tensor_mor i (tensor_mor i i)) (iso_fwd (tensor_assoc A A A))).
rewrite -(tensor_assoc_nat i i i).
rewrite -(icones_compA (iso_fwd (tensor_assoc B B B))).
rewrite (icones_compA (tensor_mor (tensor_mor i i) i) (tensor_mor dA (icones_id Ar A)) dA).
rewrite -(tensor_mor_comp (tensor_mor i i) dA i (icones_id Ar A)).
rewrite H85 icones_compIr FL.
rewrite -(icones_compA (tensor_mor dB (icones_id Ar B)) (tensor_mor i i) dA) H85.
rewrite (icones_compA (tensor_mor dB (icones_id Ar B)) dB i).
rewrite (icones_compA (iso_fwd (tensor_assoc B B B))
  (icones_comp (tensor_mor dB (icones_id Ar B)) dB) i).
rewrite HBcoassoc.
(* RHS: reduce to the same ((id_B⊗dB)∘dB)∘i *)
rewrite (icones_compA (tensor_mor i (tensor_mor i i)) (tensor_mor (icones_id Ar A) dA) dA).
rewrite -(tensor_mor_comp i (icones_id Ar A) (tensor_mor i i) dA).
rewrite icones_compIr H85 FR.
rewrite -(icones_compA (tensor_mor (icones_id Ar B) dB) (tensor_mor i i) dA) H85.
by rewrite (icones_compA (tensor_mor (icones_id Ar B) dB) dB i).
Qed.

End ComonoidTransport.

(** *** Every coalgebra morphism is a comonoid morphism (GENERAL)

    For a coalgebra morphism [g : (Z,z) → (B,b)]:
    [coalg_e B ∘ g = coalg_e Z]  and  [coalg_d B ∘ g = (g⊗g) ∘ coalg_d Z].
    Uses the naturality of the Seely comonoid [d_bang]/[e_bang] (proved by
    [bang_ext]) + counit naturality [der_nat]. *)

(** Naturality of [e_bang]: [e_{B} ∘ !g = e_{Z}].  On [x!] both give [1]. *)
Lemma e_bang_nat (Z B : ICone.type Ar) (g : icones_hom Ar Z B) :
  icones_comp (e_bang B) (bang_fmap g) = e_bang Z.
Proof.
apply: bang_ext => x Hx.
rewrite -[Lfun (icones_comp (e_bang B) (bang_fmap g)) x!]
        /(Lfun (e_bang B) (Lfun (bang_fmap g) x!)).
by rewrite (bang_fmap_prom g x Hx) (e_bang_prom (Lfun g x) (ders_lin_ball g Hx))
           (e_bang_prom x Hx).
Qed.

(** Naturality of [d_bang]: [d_{B} ∘ !g = (!g ⊗ !g) ∘ d_{Z}].
    On [x!]: LHS [d_B((g x)!) = (g x)! ⊗ (g x)!];
    RHS [(!g⊗!g)(x!⊗x!) = (g x)! ⊗ (g x)!]. *)
Lemma d_bang_nat (Z B : ICone.type Ar) (g : icones_hom Ar Z B) :
  icones_comp (d_bang B) (bang_fmap g) =
  icones_comp (tensor_mor (bang_fmap g) (bang_fmap g)) (d_bang Z).
Proof.
apply: bang_ext => x Hx.
rewrite -[Lfun (icones_comp (d_bang B) (bang_fmap g)) x!]
        /(Lfun (d_bang B) (Lfun (bang_fmap g) x!)).
rewrite (bang_fmap_prom g x Hx) (d_bang_prom (Lfun g x) (ders_lin_ball g Hx)).
rewrite -[Lfun (icones_comp (tensor_mor (bang_fmap g) (bang_fmap g)) (d_bang Z)) x!]
        /(Lfun (tensor_mor (bang_fmap g) (bang_fmap g)) (Lfun (d_bang Z) x!)).
by rewrite (d_bang_prom x Hx) tensor_morE (bang_fmap_prom g x Hx).
Qed.

(** Comonoid-morphism, counit half: [coalg_e B ∘ g = coalg_e Z]. *)
Lemma coalg_mor_e (Z B : Coalgebra Ar)
    (g : icones_hom Ar (coalg_obj Z) (coalg_obj B)) :
  is_coalg_mor Z B g -> icones_comp (coalg_e B) g = coalg_e Z.
Proof.
rewrite /is_coalg_mor /coalg_e => Hg.
by rewrite -icones_compA Hg icones_compA (e_bang_nat g).
Qed.

(** Comonoid-morphism, comultiplication half:
    [coalg_d B ∘ g = (g⊗g) ∘ coalg_d Z]. *)
Lemma coalg_mor_d (Z B : Coalgebra Ar)
    (g : icones_hom Ar (coalg_obj Z) (coalg_obj B)) :
  is_coalg_mor Z B g ->
  icones_comp (coalg_d B) g =
  icones_comp (tensor_mor g g) (coalg_d Z).
Proof.
rewrite /is_coalg_mor /coalg_d => Hg.
(* [coalg_d B ∘ g = (εB⊗εB) ∘ d_B ∘ b ∘ g
                  = (εB⊗εB) ∘ d_B ∘ !g ∘ z    (g coalg mor)
                  = (εB⊗εB) ∘ (!g⊗!g) ∘ d_Z ∘ z   (d_bang nat)
                  = ((εB∘!g)⊗(εB∘!g)) ∘ d_Z ∘ z
                  = ((g∘εZ)⊗(g∘εZ)) ∘ d_Z ∘ z   (der_nat)
                  = (g⊗g) ∘ (εZ⊗εZ) ∘ d_Z ∘ z]. *)
(* Peel with TARGETED [icones_compA] only (a blanket [-!icones_compA]
   would cascade into the opaque [tensor_mor]/[d_bang] internals). *)
rewrite -(icones_compA (tensor_mor (der (coalg_obj B)) (der (coalg_obj B)))).
rewrite -(icones_compA (d_bang (coalg_obj B))) Hg.
rewrite (icones_compA (d_bang (coalg_obj B))) (d_bang_nat g).
rewrite (icones_compA (tensor_mor (der (coalg_obj B)) (der (coalg_obj B)))).
rewrite (icones_compA (tensor_mor (der (coalg_obj B)) (der (coalg_obj B))))
        -(tensor_mor_comp (der (coalg_obj B)) (bang_fmap g)
                          (der (coalg_obj B)) (bang_fmap g))
        -(der_nat g) (tensor_mor_comp g (der (coalg_obj Z)) g (der (coalg_obj Z))).
by rewrite -(icones_compA (icones_comp (tensor_mor g g)
              (tensor_mor (der (coalg_obj Z)) (der (coalg_obj Z)))))
           -(icones_compA (tensor_mor g g)).
Qed.


End CartesianUP.

Arguments EM_prod_mor {R Ar P P' Q Q'} f g.
Arguments tensor_runit_nat {R Ar A A'} f.
Arguments tensor_lunit_nat {R Ar A A'} f.
Arguments e_bang_nat {R Ar Z B} g.
Arguments d_bang_nat {R Ar Z B} g.
Arguments coalg_mor_e {R Ar Z B} g.
Arguments coalg_mor_d {R Ar Z B} g.
Arguments tensor_braid_nat {R Ar A A' C C'} f g.
Arguments tensor_assoc_nat {R Ar A A' B B' C C'} f g h.
Arguments lcancel_mono {R Ar W A0 B0} i r {f g}.

(** ** The unconditional comonoid — Melliès Prop 26/27/28 + Cor 20

    [EMComon P] holds for EVERY [!]-coalgebra [P] (NOT just the cofree /
    [FMeas] generators): the transported comonoid [coalg_d]/[coalg_e]
    (Eq 88) satisfies the four commutative-comonoid laws (transported from
    the Seely comonoid on [!A] by Prop 27 = [transp_*]) AND the two
    coalgebra-morphism squares — the [coalg_d]-half being exactly Melliès'
    "not so immediate" step, discharged here by the structural lifting
    [coalg_mor_lift] (Cor 20) off the retraction [(coalg_str ⊗ coalg_str)]
    / [(der ⊗ der)], NOT by any point computation.  This makes the whole
    Eilenberg–Moore category [EM(!)] cartesian (Prop 28). *)
Section EMComonAll.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation "B '⊗' C" := (tensor Ar B C)
  (at level 40, left associativity) : ring_scope.
Local Notation Bg := (@Bang R Ar).

Lemma diagram81 (P : Coalgebra Ar) :
  icones_comp (tensor_mor (coalg_str P) (coalg_str P)) (coalg_d P) =
  icones_comp (d_bang (coalg_obj P)) (coalg_str P).
Proof.
have H := coalg_mor_d (Z := P) (B := bang_cofree (coalg_obj P))
  (coalg_str P) (adj_unit_is_mor P).
rewrite (coalg_d_cofree (coalg_obj P)) in H.
by rewrite H.
Qed.

Lemma diagram89e (P : Coalgebra Ar) :
  icones_comp (e_bang (coalg_obj P)) (coalg_str P) = coalg_e P.
Proof.
have H := coalg_mor_e (Z := P) (B := bang_cofree (coalg_obj P))
  (coalg_str P) (adj_unit_is_mor P).
by rewrite (coalg_e_cofree (coalg_obj P)) in H.
Qed.

Lemma coalg_mor_lift (X PA QB : Coalgebra Ar)
    (i : icones_hom Ar (coalg_obj PA) (coalg_obj QB))
    (r : icones_hom Ar (coalg_obj QB) (coalg_obj PA))
    (f : icones_hom Ar (coalg_obj X) (coalg_obj PA)) :
  is_coalg_mor PA QB i ->
  icones_comp r i = icones_id Ar (coalg_obj PA) ->
  is_coalg_mor X QB (icones_comp i f) ->
  is_coalg_mor X PA f.
Proof.
rewrite /is_coalg_mor => Hi Hri Hif.
have D67 : icones_comp (bang_fmap r) (icones_comp (coalg_str QB) i) = coalg_str PA.
  rewrite Hi icones_compA -(bang_fmap_comp r i) Hri.
  by rewrite bang_fmap_id icones_compIl.
have D66 : icones_comp (bang_fmap r) (icones_comp (coalg_str QB) (icones_comp i f))
           = icones_comp (bang_fmap f) (coalg_str X).
  rewrite Hif icones_compA -(bang_fmap_comp r (icones_comp i f)).
  rewrite (icones_compA r i f) Hri icones_compIl.
  by [].
rewrite -D67.
rewrite -(icones_compA (bang_fmap r) (icones_comp (coalg_str QB) i) f).
rewrite -(icones_compA (coalg_str QB) i f).
exact: D66.
Qed.

(* coalg_e is a coalg mor P -> EM_term, general *)
Lemma coalg_e_is_mor_gen (P : Coalgebra Ar) :
  is_coalg_mor P EM_term (coalg_e P).
Proof.
rewrite -(diagram89e P).
apply: (coalg_mor_comp (P := P) (Q := bang_cofree (coalg_obj P)) (S := EM_term)).
- exact: (e_bang_is_coalg_mor (coalg_obj P)).
- exact: (adj_unit_is_mor P).
Qed.

(* coalg_d is a coalg mor P -> EM_prod P P, general (Cor 20) *)
Lemma coalg_d_is_mor_gen (P : Coalgebra Ar) :
  is_coalg_mor P (EM_prod P P) (coalg_d P).
Proof.
pose A := coalg_obj P.
have Hi : is_coalg_mor (EM_prod P P)
    (EM_prod (bang_cofree A) (bang_cofree A))
    (tensor_mor (coalg_str P) (coalg_str P)).
  by apply: EM_prod_mor; exact: (adj_unit_is_mor P).
have Hri : icones_comp (tensor_mor (der A) (der A))
    (tensor_mor (coalg_str P) (coalg_str P)) = icones_id Ar (A ⊗ A).
  rewrite -(tensor_mor_comp (der A) (coalg_str P) (der A) (coalg_str P)).
  by rewrite (coalg_counit P) tensor_mor_id.
have Hdm : is_coalg_mor (bang_cofree A) (EM_prod (bang_cofree A) (bang_cofree A))
    (d_bang A).
  rewrite /is_coalg_mor EM_prod_str_E EM_prod_str_cofree.
  exact: (d_bang_is_coalg_mor A).
have Hif : is_coalg_mor P (EM_prod (bang_cofree A) (bang_cofree A))
    (icones_comp (tensor_mor (coalg_str P) (coalg_str P)) (coalg_d P)).
  rewrite (diagram81 P).
  apply: (coalg_mor_comp (P := P) (Q := bang_cofree A)
            (S := EM_prod (bang_cofree A) (bang_cofree A))).
  - exact: Hdm.
  - exact: (adj_unit_is_mor P).
apply: (coalg_mor_lift (X := P) (PA := EM_prod P P)
          (QB := EM_prod (bang_cofree A) (bang_cofree A))
          (i := tensor_mor (coalg_str P) (coalg_str P))
          (r := tensor_mor (der A) (der A))).
- exact: Hi.
- exact: Hri.
- exact: Hif.
Qed.

Lemma EMComon_all (P : Coalgebra Ar) : EMComon P.
Proof.
pose A := coalg_obj P.
have Hri : icones_comp (der A) (coalg_str P) = icones_id Ar A
  by exact: (coalg_counit P).
have HcoalgdE : coalg_d P =
  icones_comp (tensor_mor (der A) (der A)) (icones_comp (d_bang A) (coalg_str P))
  by rewrite /coalg_d.
have HcoalgeE : coalg_e P = icones_comp (e_bang A) (coalg_str P)
  by rewrite /coalg_e.
(* Diagram (85) for this retraction = Diagram (81). *)
have H85 : icones_comp (tensor_mor (coalg_str P) (coalg_str P))
    (icones_comp (tensor_mor (der A) (der A)) (icones_comp (d_bang A) (coalg_str P)))
  = icones_comp (d_bang A) (coalg_str P).
  by rewrite -HcoalgdE; exact: (diagram81 P).
apply: MkEMComon.
- rewrite HcoalgdE.
  apply: transp_coassoc;
    [exact: Hri | exact: (comonoid_coassoc A) | exact: H85].
- rewrite HcoalgdE HcoalgeE.
  apply: transp_counitL; [exact: Hri | exact: (comonoid_counitL A) | exact: H85].
- rewrite HcoalgdE HcoalgeE.
  apply: transp_counitR; [exact: Hri | exact: (comonoid_counitR A) | exact: H85].
- rewrite HcoalgdE.
  apply: transp_cocomm; [exact: Hri | exact: (comonoid_cocomm A) | exact: H85].
- exact: (coalg_d_is_mor_gen P).
- exact: (coalg_e_is_mor_gen P).
Qed.

End EMComonAll.

Arguments diagram81 {R Ar} P.
Arguments diagram89e {R Ar} P.
Arguments coalg_mor_lift {R Ar X PA QB} i r f.
Arguments coalg_e_is_mor_gen {R Ar} P.
Arguments coalg_d_is_mor_gen {R Ar} P.
Arguments EMComon_all {R Ar} P.

(** *** The two distinguished families are comonoidal (trivial corollaries)

    Now that [EMComon] holds unconditionally, the cofree coalgebras [!̃B]
    and the Theorem-9.7 coalgebras [FMeas X] are comonoidal as immediate
    specialisations of [EMComon_all] — no longer the special witnesses they
    once were.  Kept as named facts for documentation / downstream
    convenience. *)
Definition EMComon_cofree (R : realType) (Ar : MeasSubcat R)
    (B : ICone.type Ar) : EMComon (bang_cofree B) := EMComon_all (bang_cofree B).

Definition EMComon_FMeas (R : realType) (Ar : MeasSubcat R)
    (X : ar_obj Ar) : EMComon (FMeas_coalgebra X) := EMComon_all (FMeas_coalgebra X).

Arguments EMComon_cofree {R Ar} B.
Arguments EMComon_FMeas {R Ar} X.

(** ** Products, projections, pairing, diagonal and their laws

    With the comonoid data on the objects, the [⊗]-product becomes the
    CATEGORICAL product in [EM(!)] (Cor 17).  We package the cartesian data
    over BUNDLED coalgebra morphisms ([coalg_hom] of [em_cat.v]).  Pairing
    and diagonal use the comonoid diagonal of the DOMAIN; projections use
    the comonoid counit of the discarded factor. *)
Section CartesianData.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation "B '⊗' C" := (tensor Ar B C)
  (at level 40, left associativity) : ring_scope.
Local Notation Bg := (@Bang R Ar).

(** *** The pairing [⟨f,g⟩ = (f⊗g) ∘ d_Z]

    For coalgebra morphisms [f : Z → P], [g : Z → Q], the pairing into the
    product is a coalgebra morphism [Z → EM_prod P Q]: it is the composite
    of the diagonal [coalg_d Z : Z → EM_prod Z Z] ([emc_d_mor]) and the
    bifunctor action [f ⊗ g : EM_prod Z Z → EM_prod P Q] ([EM_prod_mor]). *)
Definition em_pair_mor (Z P Q : Coalgebra Ar)
    (f : icones_hom Ar (coalg_obj Z) (coalg_obj P))
    (g : icones_hom Ar (coalg_obj Z) (coalg_obj Q)) :
    icones_hom Ar (coalg_obj Z) (coalg_obj P ⊗ coalg_obj Q) :=
  icones_comp (tensor_mor f g) (coalg_d Z).

Lemma em_pair_is_mor (Z P Q : Coalgebra Ar)
    (f : icones_hom Ar (coalg_obj Z) (coalg_obj P))
    (g : icones_hom Ar (coalg_obj Z) (coalg_obj Q)) :
  is_coalg_mor Z P f -> is_coalg_mor Z Q g ->
  is_coalg_mor Z (EM_prod P Q) (em_pair_mor f g).
Proof.
move=> Hf Hg; rewrite /em_pair_mor.
apply: (coalg_mor_comp (P := Z) (Q := EM_prod Z Z) (S := EM_prod P Q)).
- exact: (EM_prod_mor f g Hf Hg).
- exact: (emc_d_mor (EMComon_all Z)).
Qed.

(** Bundled pairing of [coalg_hom]s. *)
Definition em_pair (Z P Q : Coalgebra Ar)
    (f : coalg_hom Z P) (g : coalg_hom Z Q) : coalg_hom Z (EM_prod P Q) :=
  MkCoalgHom (em_pair_is_mor (ch_is_mor f) (ch_is_mor g)).

(** *** The projections

    [em_proj1 = ρ_P ∘ (id_P ⊗ coalg_e Q) : P⊗Q → P],
    [em_proj2 = λ_Q ∘ (coalg_e P ⊗ id_Q) : P⊗Q → Q]. *)
Definition em_proj1_mor (P Q : Coalgebra Ar) :
    icones_hom Ar (coalg_obj P ⊗ coalg_obj Q) (coalg_obj P) :=
  icones_comp (iso_fwd (tensor_runit (coalg_obj P)))
    (tensor_mor (icones_id Ar (coalg_obj P)) (coalg_e Q)).

Definition em_proj2_mor (P Q : Coalgebra Ar) :
    icones_hom Ar (coalg_obj P ⊗ coalg_obj Q) (coalg_obj Q) :=
  icones_comp (iso_fwd (tensor_lunit (coalg_obj Q)))
    (tensor_mor (coalg_e P) (icones_id Ar (coalg_obj Q))).

(** *** The product [β]-laws (Cor 17): [π1 ∘ ⟨f,g⟩ = f], [π2 ∘ ⟨f,g⟩ = g]

    Pure [icones_hom] equations (no coalgebra side): the discarded factor is
    erased by the comonoid counit law [emc_counitR]/[emc_counitL] of the
    domain [Z], after [tensor_mor_comp] and the comonoid-morphism counit
    identity [coalg_mor_e]. *)
Lemma em_proj1_pair (Z P Q : Coalgebra Ar)
    (f : icones_hom Ar (coalg_obj Z) (coalg_obj P))
    (g : icones_hom Ar (coalg_obj Z) (coalg_obj Q)) :
  is_coalg_mor Z Q g ->
  icones_comp (em_proj1_mor P Q) (em_pair_mor f g) = f.
Proof.
move=> Hg; rewrite /em_proj1_mor /em_pair_mor.
(* [ρ ∘ (id⊗eQ) ∘ (f⊗g) ∘ d_Z]; peel with TARGETED [icones_compA] (a blanket
   [-!icones_compA] would cascade into the opaque [tensor_mor]/[coalg_d]
   internals). *)
rewrite -(icones_compA (iso_fwd (tensor_runit (coalg_obj P)))).
rewrite (icones_compA (tensor_mor (icones_id Ar (coalg_obj P)) (coalg_e Q))).
rewrite -(tensor_mor_comp (icones_id Ar (coalg_obj P)) f (coalg_e Q) g).
rewrite icones_compIl (coalg_mor_e g Hg).
(* [(f ⊗ coalg_e Z) = (f∘id_Z) ⊗ (id_1∘coalg_e Z) = (f⊗id_1) ∘ (id_Z⊗coalg_e Z)]. *)
rewrite -{1}(icones_compIr f) -(icones_compIl (coalg_e Z)).
rewrite (tensor_mor_comp f (icones_id Ar (coalg_obj Z))
                         (icones_id Ar (cone_one_car Ar)) (coalg_e Z)).
(* [ρ_P ∘ (f ⊗ id_1) = f ∘ ρ_Z]. *)
rewrite (icones_compA (iso_fwd (tensor_runit (coalg_obj P)))).
rewrite (icones_compA (iso_fwd (tensor_runit (coalg_obj P)))).
rewrite (tensor_runit_nat f).
(* [f ∘ (ρ_Z ∘ (id_Z⊗coalg_e Z) ∘ d_Z) = f ∘ id = f]. *)
rewrite -(icones_compA (icones_comp f (iso_fwd (tensor_runit (coalg_obj Z))))).
rewrite -(icones_compA f).
by rewrite (emc_counitR (EMComon_all Z)) icones_compIr.
Qed.

Lemma em_proj2_pair (Z P Q : Coalgebra Ar)
    (f : icones_hom Ar (coalg_obj Z) (coalg_obj P))
    (g : icones_hom Ar (coalg_obj Z) (coalg_obj Q)) :
  is_coalg_mor Z P f ->
  icones_comp (em_proj2_mor P Q) (em_pair_mor f g) = g.
Proof.
move=> Hf; rewrite /em_proj2_mor /em_pair_mor.
rewrite -(icones_compA (iso_fwd (tensor_lunit (coalg_obj Q)))).
rewrite (icones_compA (tensor_mor (coalg_e P) (icones_id Ar (coalg_obj Q)))).
rewrite -(tensor_mor_comp (coalg_e P) f (icones_id Ar (coalg_obj Q)) g).
rewrite icones_compIl (coalg_mor_e f Hf).
(* [(coalg_e Z ⊗ g) = (id_1⊗g) ∘ (coalg_e Z⊗id_Z)]. *)
rewrite -{1}(icones_compIl (coalg_e Z)) -(icones_compIr g).
rewrite (tensor_mor_comp (icones_id Ar (cone_one_car Ar)) (coalg_e Z)
                         g (icones_id Ar (coalg_obj Z))).
(* [λ_Q ∘ (id_1 ⊗ g) = g ∘ λ_Z]. *)
rewrite (icones_compA (iso_fwd (tensor_lunit (coalg_obj Q)))).
rewrite (icones_compA (iso_fwd (tensor_lunit (coalg_obj Q)))).
rewrite (tensor_lunit_nat g).
rewrite -(icones_compA (icones_comp g (iso_fwd (tensor_lunit (coalg_obj Z))))).
rewrite -(icones_compA g).
by rewrite (emc_counitL (EMComon_all Z)) icones_compIr.
Qed.

(** *** The diagonal [Δ_P = ⟨id,id⟩ = coalg_d P]

    The diagonal is the comonoid comultiplication itself (a coalgebra
    morphism [P → EM_prod P P] by [emc_d_mor]); equivalently the pairing of
    [id] with [id]. *)
Lemma em_diag_pair (P : Coalgebra Ar) :
  em_pair_mor (icones_id Ar (coalg_obj P)) (icones_id Ar (coalg_obj P)) = coalg_d P.
Proof.
by rewrite /em_pair_mor tensor_mor_id icones_compIl.
Qed.

End CartesianData.

Arguments em_pair_mor {R Ar Z P Q} f g.
Arguments em_pair_is_mor {R Ar Z P Q} {f g}.
Arguments em_pair {R Ar Z P Q} f g.
Arguments em_proj1_mor {R Ar} P Q.
Arguments em_proj2_mor {R Ar} P Q.
Arguments em_proj1_pair {R Ar Z P Q} {f g}.
Arguments em_proj2_pair {R Ar Z P Q} {f g}.
Arguments em_diag_pair {R Ar} P.

(** ** The terminal object [EM_term = (1, ·)] — Cor 17 (nullary case)

    [EM_term] is terminal in [EM(!)]: the unique morphism from every
    coalgebra [P] is [coalg_e P], and any coalgebra morphism into [EM_term]
    equals it (because every coalgebra morphism is a comonoid morphism, and
    the comonoid counit of [EM_term] is the identity). *)
Section Terminal.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation Bg := (@Bang R Ar).

(** The counit of the terminal coalgebra is the identity:
    [coalg_e EM_term = id_1]. *)
Lemma coalg_e_term : coalg_e (EM_term : Coalgebra Ar) = icones_id Ar (cone_one_car Ar).
Proof.
apply: one_ext.
rewrite -[coalg_e EM_term]/(icones_comp (e_bang (cone_one_car Ar)) unit_cofree_str).
rewrite -[Lfun (icones_comp (e_bang (cone_one_car Ar)) unit_cofree_str) one1]
        /(Lfun (e_bang (cone_one_car Ar)) (Lfun unit_cofree_str one1)).
rewrite unit_cofree_str_one1.
have H1 : cone_norm (one1 : cone_one_car Ar) <= 1.
  by rewrite (_ : cone_norm one1 = 1) // /cone_norm /= /c1_norm.
by rewrite (e_bang_prom one1 H1).
Qed.

(** [coalg_e P] is the canonical morphism [P → EM_term] (a coalgebra
    morphism for EVERY [P] by [emc_e_mor (EMComon_all P)]). *)
Definition em_term_mor (P : Coalgebra Ar) :
    coalg_hom P EM_term :=
  MkCoalgHom (emc_e_mor (EMComon_all P)).

(** Uniqueness: any coalgebra morphism [h : P → EM_term] equals [coalg_e P].
    [coalg_mor_e h] gives [coalg_e EM_term ∘ h = coalg_e P], and
    [coalg_e EM_term = id], so [h = coalg_e P]. *)
Lemma em_term_unique (P : Coalgebra Ar)
    (h : icones_hom Ar (coalg_obj P) (coalg_obj (EM_term : Coalgebra Ar))) :
  is_coalg_mor P EM_term h -> h = coalg_e P.
Proof.
move=> Hh.
have := coalg_mor_e h Hh.
by rewrite coalg_e_term icones_compIl.
Qed.

End Terminal.

Arguments coalg_e_term {R Ar}.
Arguments em_term_mor {R Ar} P.
Arguments em_term_unique {R Ar P} h.

(** ** The headline bundle — Melliès Corollary 17 / Proposition 28

    [(EM(!), ⊗, 1)] is CARTESIAN — for the FULL Eilenberg–Moore category,
    NOT just a rich subcategory: since [EMComon] holds unconditionally
    ([EMComon_all]), EVERY pair of coalgebras has a [⊗]-product with
    projections, pairing and the [β]-laws, and the tensor unit is terminal
    for EVERY coalgebra.  The record packages the cartesian data + laws over
    the [EM(!)] category of [em_cat.v]; the field types reference the LINEAR
    tensor [⊗] (NOT the cartesian [&]) — see [cart_prod_obj].  No per-object
    [EMComon] hypothesis is threaded anymore. *)
Record EM_Cartesian (R : realType) (Ar : MeasSubcat R) : Type := MkEMCartesian {
  (* binary product carried by the linear ⊗, and terminal = tensor unit *)
  cart_prod : Coalgebra Ar -> Coalgebra Ar -> Coalgebra Ar;
  cart_term : Coalgebra Ar;
  (* the product carrier is the LINEAR tensor of the carriers (NOT [&]) *)
  cart_prod_obj : forall P Q : Coalgebra Ar,
    coalg_obj (cart_prod P Q) = tensor Ar (coalg_obj P) (coalg_obj Q);
  (* projections (underlying maps) and the pairing of coalgebra morphisms
     out of ANY coalgebra *)
  cart_proj1 : forall P Q : Coalgebra Ar,
    icones_hom Ar (coalg_obj (cart_prod P Q)) (coalg_obj P);
  cart_proj2 : forall P Q : Coalgebra Ar,
    icones_hom Ar (coalg_obj (cart_prod P Q)) (coalg_obj Q);
  cart_pair : forall (Z P Q : Coalgebra Ar),
    coalg_hom Z P -> coalg_hom Z Q -> coalg_hom Z (cart_prod P Q);
  (* the β-laws of the product (Cor 17) *)
  cart_beta1 : forall (Z P Q : Coalgebra Ar)
    (f : coalg_hom Z P) (g : coalg_hom Z Q),
    icones_comp (cart_proj1 P Q) (ch_mor (cart_pair f g)) = ch_mor f;
  cart_beta2 : forall (Z P Q : Coalgebra Ar)
    (f : coalg_hom Z P) (g : coalg_hom Z Q),
    icones_comp (cart_proj2 P Q) (ch_mor (cart_pair f g)) = ch_mor g;
  (* terminal universal property: canonical map + uniqueness, for EVERY P *)
  cart_term_mor : forall (P : Coalgebra Ar), coalg_hom P cart_term;
  cart_term_unique : forall (P : Coalgebra Ar)
    (h : icones_hom Ar (coalg_obj P) (coalg_obj cart_term)),
    is_coalg_mor P cart_term h -> h = ch_mor (cart_term_mor P);
}.

Arguments EM_Cartesian {R} Ar.

(** *** The canonical cartesian structure of [EM(!)]

    Products [= EM_prod], terminal [= EM_term], projections [= em_proj1/2],
    pairing [= em_pair], β-laws [= em_proj1/2_pair], terminal UP
    [= em_term_mor]/[em_term_unique].  Headline result: the FULL [EM(!)] is
    cartesian. *)
Definition ICones_EM_cartesian (R : realType) (Ar : MeasSubcat R) :
    EM_Cartesian Ar :=
  {| cart_prod := @EM_prod R Ar;
     cart_term := @EM_term R Ar;
     cart_prod_obj := @EM_prod_obj R Ar;
     cart_proj1 := @em_proj1_mor R Ar;
     cart_proj2 := @em_proj2_mor R Ar;
     cart_pair := fun Z P Q f g => @em_pair R Ar Z P Q f g;
     cart_beta1 := fun Z P Q f g =>
       @em_proj1_pair R Ar Z P Q (ch_mor f) (ch_mor g) (ch_is_mor g);
     cart_beta2 := fun Z P Q f g =>
       @em_proj2_pair R Ar Z P Q (ch_mor f) (ch_mor g) (ch_is_mor f);
     cart_term_mor := fun P => @em_term_mor R Ar P;
     cart_term_unique := fun P h Hh => @em_term_unique R Ar P h Hh |}.

