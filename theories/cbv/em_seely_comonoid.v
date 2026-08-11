(**md**************************************************************************)
(** * The Seely comonoid on [!A] and LC2–LC4 — CBV §2

    Step 2 of the call-by-value roadmap
    ([/home/rocq/prime_gap/icones-cbv-plan.md], Phase B1).  We build, on
    every cofree object [!A], the commutative-comonoid structure of a
    Melliès *linear category* (conditions LC2–LC4, §7.4 p150), transported
    from the cartesian diagonal/terminal of [(&, ⊤)] through the Seely isos
    [Seely2]/[Seely0] of [seely.v].

    These are diagram chases on promoted points, NOT new analysis: each law
    reduces on [x!] (resp. [x1! ⊗ x2!]) via the [bang_ext]/[tens_excl_charact]
    extensionality of [bang.v]/[seely.v], then computes by [Seely2E]/
    [Seely0E]/[bang_fmap_prom]/[tensor_morE] + the structural-iso E-laws —
    exactly the engine that discharges [seely_comult] and friends.

    Contents:
    - [diag A] / [term A] — the cartesian diagonal [A → A & A]
      ([spair id id]) and the terminal map [A → ⊤] ([Stop_mor]).
    - [d_bang A : !A ⊸ !A ⊗ !A] — the COMULTIPLICATION
      [Seely2⁻¹ ∘ !(diag_A)], with [d_bang_prom]: [d_A(x!) = x! ⊗ x!].
    - [e_bang A : !A ⊸ 1] — the COUNIT [Seely0⁻¹ ∘ !(term_A)], with
      [e_bang_prom]: [e_A(x!) = 1].
    - **LC2** — [(!A, d_A, e_A)] is a commutative comonoid:
      [comonoid_coassoc] (coassociativity), [comonoid_counitL]/
      [comonoid_counitR] (left/right counit), [comonoid_cocomm]
      (cocommutativity).
    - the transport-of-cofree coalgebras [tens_cofree A B] (the structure
      [!A ⊗ !B] inherits across [Seely2]) and [unit_cofree] (the structure
      [1] inherits across [Seely0]) — the symmetric-monoidal (LC1-level)
      structure of [EM(!)], NOT the cartesian product (step 3); their
      workhorse computation [tens_cofree_str_prom]
      ([str(x! ⊗ y!) = (x! ⊗ y!)!]) is also what [em_cartesian.v] uses.
    - **LC3** — [d_A] and [e_A] are coalgebra morphisms:
      [d_bang_is_coalg_mor] ([!̃A → tens_cofree A A]) and
      [e_bang_is_coalg_mor] ([!̃A → unit_cofree]).
    - **LC4** — [dig_A] is a comonoid morphism: [dig_comonoid_mult]
      (compatible with [d]) and [dig_comonoid_counit] (compatible with [e]).

    Step 3 (the cartesian structure on the FULL [EM(!)], Melliès Prop 28 /
    Cor 20) is in [em_cartesian.v]. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference.

Require Import Icones.cones.precone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.cone.
Require Import Icones.cones.cone_cat.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.icone.
Require Import Icones.icones.examples_icone.
Require Import Icones.icones.icone_cat.
Require Import Icones.stable.scones_cat.
Require Import Icones.stable.scones_ccc.
Require Import Icones.homs.icones_iso.
Require Import Icones.homs.tensor.
Require Import Icones.homs.smcc.
Require Import Icones.homs.exp_adjunction.
Require Import Icones.homs.bang.
Require Import Icones.homs.seely_defs.
Require Import Icones.homs.seely.
Require Import Icones.homs.coalgebra.
Require Import Icones.homs.em_cat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

(** Re-seal the tensor data as in [seely.v] so a bare [/=] does not unfold
    the [tensor_construct] internals (which would break the
    [tensor_morE]/[...Ep] rewrites). *)
Opaque tensor_mor tensor_assoc tensor_lunit tensor_runit tensor_braid
       ptensor tau Seely2.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section SeelyComonoid.
Variables (R : realType) (Ar : MeasSubcat R).

(** The underlying linear function of an [icones_hom]. *)
Local Notation Lfun h := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

Local Notation "B '⊗' C" := (tensor Ar B C)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '!'" := (prom x) (at level 2, format "x '!'").
Local Notation Bg := (@Bang R Ar).

(** ** The cartesian diagonal and terminal maps *)

(** The diagonal [A → A & A], [diag_A = ⟨id, id⟩]. *)
Definition diag (A : ICone.type Ar) : icones_hom Ar A (sprod A A) :=
  spair (icones_id Ar A) (icones_id Ar A).

Lemma diagE (A : ICone.type Ar) (x : A) :
  Lfun (diag A) x = sprod_pair x x.
Proof. by rewrite /diag spairE. Qed.

(** The terminal map [A → ⊤]. *)
Definition term (A : ICone.type Ar) : icones_hom Ar A (Stop Ar) := Stop_mor A.

(** ** The comultiplication [d_A : !A ⊸ !A ⊗ !A] — Paper §7.4 (LC2)

    [d_A = Seely2_{A,A}⁻¹ ∘ !(diag_A)]. *)
Definition d_bang (A : ICone.type Ar) :
    icones_hom Ar (Bg A) (Bg A ⊗ Bg A) :=
  icones_comp (iso_bwd (Seely2 A A)) (bang_fmap (diag A)).

(** [d_A(x!) = x! ⊗ x!] for [‖x‖ ≤ 1].  [!(diag_A)(x!) = (diag_A x)! =
    ⟨x,x⟩!]; then [Seely2⁻¹(⟨x,x⟩!) = x! ⊗ x!] (the inverse of [Seely2E]). *)
Lemma d_bang_prom (A : ICone.type Ar) (x : A) :
  cone_norm x <= 1 -> Lfun (d_bang A) x! = x! ⊗p x!.
Proof.
move=> Hx.
rewrite /d_bang -[Lfun (icones_comp _ _) _]/(Lfun (iso_bwd (Seely2 A A))
  (Lfun (bang_fmap (diag A)) x!)).
rewrite (bang_fmap_prom (diag A) x Hx) diagE.
apply: (iso_fwd_inj (Seely2 A A)).
rewrite -[Lfun (iso_fwd (Seely2 A A)) (Lfun (iso_bwd (Seely2 A A)) _)]
        /(Lfun (icones_comp (iso_fwd (Seely2 A A)) (iso_bwd (Seely2 A A)))
          (sprod_pair x x)!).
rewrite iso_bwdK -[Lfun (icones_id _ _) _]/((sprod_pair x x)!).
by rewrite (Seely2E x x Hx Hx).
Qed.

(** ** The counit [e_A : !A ⊸ 1] — Paper §7.4 (LC2)

    [e_A = Seely0⁻¹ ∘ !(term_A)]. *)
Definition e_bang (A : ICone.type Ar) :
    icones_hom Ar (Bg A) (cone_one_car Ar) :=
  icones_comp (iso_bwd Seely0) (bang_fmap (term A)).

(** [e_A(x!) = 1] (the unit point [one1]) for [‖x‖ ≤ 1].
    [!(term_A)(x!) = (term_A x)! = 0!]; then [Seely0⁻¹(0!) = 1] (the
    inverse of [Seely0E] at [one1], since [Seely0(1) = 1·0! = 0!]). *)
Lemma e_bang_prom (A : ICone.type Ar) (x : A) :
  cone_norm x <= 1 -> Lfun (e_bang A) x! = one1.
Proof.
move=> Hx.
rewrite /e_bang -[Lfun (icones_comp _ _) _]/(Lfun (iso_bwd Seely0)
  (Lfun (bang_fmap (term A)) x!)).
rewrite (bang_fmap_prom (term A) x Hx).
have -> : Lfun (term A) x = (precone_zero : Stop Ar) by exact: Stop_eq.
apply: (iso_fwd_inj Seely0).
rewrite -[Lfun (iso_fwd Seely0) (Lfun (iso_bwd Seely0) _)]
        /(Lfun (icones_comp (iso_fwd Seely0) (iso_bwd Seely0)) (precone_zero : Stop Ar)!).
rewrite iso_bwdK -[Lfun (icones_id _ _) _]/((precone_zero : Stop Ar)!).
rewrite (Seely0E one1).
have e1 : c1_val one1 = 1%:nng by [].
by rewrite e1 precone_scale_1.
Qed.

(** ** LC2 — [(!A, d_A, e_A)] is a commutative comonoid

    All four laws reduce on [x!] via [bang_ext] (then compute by
    [d_bang_prom]/[e_bang_prom] + the structural-iso E-laws). *)

(** Coassociativity:
    [α ∘ (d_A ⊗ id) ∘ d_A = (id ⊗ d_A) ∘ d_A] as maps [!A → !A ⊗ (!A ⊗ !A)].
    On [x!] both sides give [x! ⊗ (x! ⊗ x!)]. *)
Lemma comonoid_coassoc (A : ICone.type Ar) :
  icones_comp (iso_fwd (tensor_assoc (Bg A) (Bg A) (Bg A)))
    (icones_comp (tensor_mor (d_bang A) (icones_id Ar (Bg A))) (d_bang A)) =
  icones_comp (tensor_mor (icones_id Ar (Bg A)) (d_bang A)) (d_bang A).
Proof.
apply: bang_ext => x Hx.
have Hp : cone_norm x! <= 1 by exact: prom_ball.
(* LHS *)
rewrite -[Lfun (icones_comp (iso_fwd (tensor_assoc _ _ _)) _) _]
        /(Lfun (iso_fwd (tensor_assoc (Bg A) (Bg A) (Bg A)))
          (Lfun (icones_comp (tensor_mor (d_bang A) (icones_id Ar (Bg A))) (d_bang A)) x!)).
rewrite -[Lfun (icones_comp (tensor_mor _ _) (d_bang A)) x!]
        /(Lfun (tensor_mor (d_bang A) (icones_id Ar (Bg A))) (Lfun (d_bang A) x!)).
rewrite (d_bang_prom Hx) tensor_morE.
have idA : Lfun (icones_id Ar (Bg A)) x! = x! by [].
rewrite idA (d_bang_prom Hx) tensor_assocEp.
(* RHS *)
rewrite -[RHS]/(Lfun (tensor_mor (icones_id Ar (Bg A)) (d_bang A)) (Lfun (d_bang A) x!)).
by rewrite (d_bang_prom Hx) tensor_morE idA (d_bang_prom Hx).
Qed.

(** Left counit: [λ ∘ (e_A ⊗ id) ∘ d_A = id_{!A}].
    On [x!]: [(e_A ⊗ id)(x! ⊗ x!) = 1 ⊗ x!], [λ(1 ⊗ x!) = 1·x! = x!]. *)
Lemma comonoid_counitL (A : ICone.type Ar) :
  icones_comp (iso_fwd (tensor_lunit (Bg A)))
    (icones_comp (tensor_mor (e_bang A) (icones_id Ar (Bg A))) (d_bang A)) =
  icones_id Ar (Bg A).
Proof.
apply: bang_ext => x Hx.
rewrite -[Lfun (icones_comp (iso_fwd (tensor_lunit _)) _) _]
        /(Lfun (iso_fwd (tensor_lunit (Bg A)))
          (Lfun (icones_comp (tensor_mor (e_bang A) (icones_id Ar (Bg A))) (d_bang A)) x!)).
rewrite -[Lfun (icones_comp (tensor_mor _ _) (d_bang A)) x!]
        /(Lfun (tensor_mor (e_bang A) (icones_id Ar (Bg A))) (Lfun (d_bang A) x!)).
rewrite (d_bang_prom Hx) tensor_morE (e_bang_prom Hx).
have idA : Lfun (icones_id Ar (Bg A)) x! = x! by [].
rewrite idA tensor_lunitEp.
have e1 : c1_val one1 = 1%:nng by [].
by rewrite e1 precone_scale_1.
Qed.

(** Right counit: [ρ ∘ (id ⊗ e_A) ∘ d_A = id_{!A}].  Symmetric. *)
Lemma comonoid_counitR (A : ICone.type Ar) :
  icones_comp (iso_fwd (tensor_runit (Bg A)))
    (icones_comp (tensor_mor (icones_id Ar (Bg A)) (e_bang A)) (d_bang A)) =
  icones_id Ar (Bg A).
Proof.
apply: bang_ext => x Hx.
rewrite -[Lfun (icones_comp (iso_fwd (tensor_runit _)) _) _]
        /(Lfun (iso_fwd (tensor_runit (Bg A)))
          (Lfun (icones_comp (tensor_mor (icones_id Ar (Bg A)) (e_bang A)) (d_bang A)) x!)).
rewrite -[Lfun (icones_comp (tensor_mor _ _) (d_bang A)) x!]
        /(Lfun (tensor_mor (icones_id Ar (Bg A)) (e_bang A)) (Lfun (d_bang A) x!)).
rewrite (d_bang_prom Hx) tensor_morE (e_bang_prom Hx).
have idA : Lfun (icones_id Ar (Bg A)) x! = x! by [].
rewrite idA tensor_runitEp.
have e1 : c1_val one1 = 1%:nng by [].
by rewrite e1 precone_scale_1.
Qed.

(** Cocommutativity: [σ ∘ d_A = d_A].
    On [x!]: [σ(x! ⊗ x!) = x! ⊗ x! = d_A(x!)]. *)
Lemma comonoid_cocomm (A : ICone.type Ar) :
  icones_comp (iso_fwd (tensor_braid (Bg A) (Bg A))) (d_bang A) = d_bang A.
Proof.
apply: bang_ext => x Hx.
rewrite -[Lfun (icones_comp (iso_fwd (tensor_braid _ _)) (d_bang A)) x!]
        /(Lfun (iso_fwd (tensor_braid (Bg A) (Bg A))) (Lfun (d_bang A) x!)).
by rewrite (d_bang_prom Hx) tensor_braidEp.
Qed.

(** ** The transported cofree coalgebras (the monoidal structure of [EM(!)])

    The tensor [!A ⊗ !B] inherits a coalgebra structure by TRANSPORTING the
    cofree structure of [!(A & B)] across the Seely iso [Seely2]; likewise
    [1] across [Seely0].  This is the symmetric-monoidal (LC1-level)
    structure of [EM(!)] given by Lack's lifting — NOT the cartesian product
    of step 3. *)

(** Transport of the cofree structure [dig_{A&B}] along [Seely2_{A,B}]:
    [str = !(Seely2⁻¹) ∘ dig_{A&B} ∘ Seely2]. *)
Definition tens_cofree_str (A B : ICone.type Ar) :
    icones_hom Ar (Bg A ⊗ Bg B) (Bg (Bg A ⊗ Bg B)) :=
  icones_comp (bang_fmap (iso_bwd (Seely2 A B)))
    (icones_comp (dig (sprod A B)) (iso_fwd (Seely2 A B))).

(** The transported structure sends a promoted pure tensor to its own
    promotion: [tens_cofree_str_{A,B}(x! ⊗ y!) = (x! ⊗ y!)!].  Chase
    [Seely2E], [dig_prom] and [bang_fmap_prom] through the transport, then
    cancel the [Seely2] round-trip with [iso_bwdK].

    This single computation is the workhorse of the whole [EM(!)]
    monoidal layer: it discharges [tens_cofree_coassoc] and
    [d_bang_is_coalg_mor] below, and [em_cartesian.v]'s [m_bang_prom] and
    [tens_cofree_str_m_bang]. *)
Lemma tens_cofree_str_prom (A B : ICone.type Ar) (x : A) (y : B) :
  cone_norm x <= 1 -> cone_norm y <= 1 ->
  Lfun (tens_cofree_str A B) (x! ⊗p y!) = (x! ⊗p y!)!.
Proof.
move=> Hx Hy.
have Hp : cone_norm (sprod_pair x y) <= 1 by exact: sprod_pair_norm_le1.
have Hpp : cone_norm (sprod_pair x y)! <= 1 by exact: prom_ball.
rewrite /tens_cofree_str.
rewrite -[Lfun (icones_comp (bang_fmap (iso_bwd (Seely2 A B))) _) _]
        /(Lfun (bang_fmap (iso_bwd (Seely2 A B)))
          (Lfun (icones_comp (dig (sprod A B)) (iso_fwd (Seely2 A B))) (x! ⊗p y!))).
rewrite -[Lfun (icones_comp (dig (sprod A B)) (iso_fwd (Seely2 A B))) _]
        /(Lfun (dig (sprod A B)) (Lfun (iso_fwd (Seely2 A B)) (x! ⊗p y!))).
rewrite (Seely2E x y Hx Hy) (dig_prom (sprod_pair x y) Hp).
rewrite (bang_fmap_prom (iso_bwd (Seely2 A B)) (sprod_pair x y)! Hpp).
congr (prom _).
apply: (iso_fwd_inj (Seely2 A B)).
rewrite -[Lfun (iso_fwd (Seely2 A B)) (Lfun (iso_bwd (Seely2 A B)) _)]
        /(Lfun (icones_comp (iso_fwd (Seely2 A B)) (iso_bwd (Seely2 A B))) (sprod_pair x y)!).
rewrite iso_bwdK -[Lfun (icones_id _ _) _]/((sprod_pair x y)!).
by rewrite (Seely2E x y Hx Hy).
Qed.
Arguments tens_cofree_str_prom {A B x y}.

(** The counit law for the transported structure:
    [der ∘ str = id].  We chase through [Seely2] and [comonad_counitL]. *)
Lemma tens_cofree_counit (A B : ICone.type Ar) :
  icones_comp (der (Bg A ⊗ Bg B)) (tens_cofree_str A B) =
  icones_id Ar (Bg A ⊗ Bg B).
Proof.
rewrite /tens_cofree_str.
rewrite icones_compA -(der_nat (iso_bwd (Seely2 A B))).
rewrite -icones_compA (icones_compA (der (Bg (sprod A B)))).
rewrite (comonad_counitL (sprod A B)) icones_compIl.
by rewrite (iso_fwdK (Seely2 A B)).
Qed.

(** The coassociativity law for the transported structure:
    [dig ∘ str = !str ∘ str].  Both sides are the transport of
    [comonad_coassoc] across [Seely2]; we discharge on promoted pure
    tensors via [tens_excl_charact]. *)
Lemma tens_cofree_coassoc (A B : ICone.type Ar) :
  icones_comp (dig (Bg A ⊗ Bg B)) (tens_cofree_str A B) =
  icones_comp (bang_fmap (tens_cofree_str A B)) (tens_cofree_str A B).
Proof.
apply: tens_excl_charact => x1 x2 Hx1 Hx2.
(* the structure map on [x1! ⊗ x2!] is [(x1! ⊗ x2!)!]. *)
have Hstr := tens_cofree_str_prom Hx1 Hx2.
(* LHS: [dig (str (x1!⊗x2!)) = dig ((x1!⊗x2!)!) = ((x1!⊗x2!)!)!]. *)
rewrite -[Lfun (icones_comp (dig (Bg A ⊗ Bg B)) (tens_cofree_str A B)) _]
        /(Lfun (dig (Bg A ⊗ Bg B)) (Lfun (tens_cofree_str A B) (x1! ⊗p x2!))).
rewrite Hstr.
have Hpt : cone_norm (x1! ⊗p x2!) <= 1.
  apply: le_trans (tensor_norm_le _ _) _; rewrite -[1]mulr1.
  by apply: ler_pM => //;
    [exact: cone_norm_ge0 | exact: cone_norm_ge0
     | exact: prom_ball Hx1 | exact: prom_ball Hx2].
rewrite (dig_prom (x1! ⊗p x2!) Hpt).
(* RHS: [!str (str (x1!⊗x2!)) = !str ((x1!⊗x2!)!) = (str(x1!⊗x2!))! =
   ((x1!⊗x2!)!)!]. *)
rewrite -[Lfun (icones_comp (bang_fmap (tens_cofree_str A B)) (tens_cofree_str A B)) _]
        /(Lfun (bang_fmap (tens_cofree_str A B)) (Lfun (tens_cofree_str A B) (x1! ⊗p x2!))).
rewrite Hstr (bang_fmap_prom (tens_cofree_str A B) (x1! ⊗p x2!) Hpt).
by rewrite Hstr.
Qed.

Definition tens_cofree (A B : ICone.type Ar) : Coalgebra Ar :=
  MkCoalgebra (tens_cofree_counit A B) (tens_cofree_coassoc A B).

(** Transport of the cofree structure [dig_⊤] along [Seely0 : 1 ≅ !⊤]. *)
Definition unit_cofree_str :
    icones_hom Ar (cone_one_car Ar) (Bg (cone_one_car Ar)) :=
  icones_comp (bang_fmap (iso_bwd Seely0))
    (icones_comp (dig (Stop Ar)) (iso_fwd Seely0)).

(** [str_1] on the unit point [one1] is [one1!]. *)
Lemma unit_cofree_str_one1 :
  Lfun unit_cofree_str one1 = one1!.
Proof.
rewrite /unit_cofree_str.
rewrite -[Lfun (icones_comp (bang_fmap (iso_bwd Seely0)) _) _]
        /(Lfun (bang_fmap (iso_bwd Seely0))
          (Lfun (icones_comp (dig (Stop Ar)) (iso_fwd Seely0)) one1)).
rewrite -[Lfun (icones_comp (dig (Stop Ar)) (iso_fwd Seely0)) _]
        /(Lfun (dig (Stop Ar)) (Lfun (iso_fwd Seely0) one1)).
have H0 : cone_norm (precone_zero : Stop Ar) <= 1 by rewrite cone_norm0.
rewrite (Seely0E one1).
have e1 : c1_val one1 = 1%:nng by [].
rewrite e1 precone_scale_1.
rewrite (dig_prom (precone_zero : Stop Ar) H0).
rewrite (bang_fmap_prom (iso_bwd Seely0) (precone_zero : Stop Ar)! (prom_ball H0)).
congr (prom _).
apply: (iso_fwd_inj Seely0).
rewrite -[Lfun (iso_fwd Seely0) (Lfun (iso_bwd Seely0) _)]
        /(Lfun (icones_comp (iso_fwd Seely0) (iso_bwd Seely0)) (precone_zero : Stop Ar)!).
rewrite iso_bwdK -[Lfun (icones_id _ _) _]/((precone_zero : Stop Ar)!).
by rewrite (Seely0E one1) e1 precone_scale_1.
Qed.

(** A morphism out of [1] is determined by its value at [one1] (the
    representability of [ICones(1, -)]).  We use that a [cone_one_car]
    point is [c1_val · one1], so linearity pins the map down. *)
Lemma one_ext (C : ICone.type Ar) (f g : icones_hom Ar (cone_one_car Ar) C) :
  Lfun f one1 = Lfun g one1 -> f = g.
Proof.
move=> H1; apply: icones_hom_eq => s.
have -> : s = precone_scale (c1_val s) one1.
  by apply: cone_one_eq; apply: val_inj => /=; rewrite mulr1.
rewrite (basic_lemmas.linearZ (cones_hom_linear _) (c1_val s) one1).
rewrite (basic_lemmas.linearZ (cones_hom_linear _) (c1_val s) one1).
by rewrite -[cones_hom_fun _ one1]/(Lfun f one1) H1.
Qed.

Lemma unit_cofree_counit :
  icones_comp (der (cone_one_car Ar)) unit_cofree_str =
  icones_id Ar (cone_one_car Ar).
Proof.
apply: one_ext.
rewrite -[Lfun (icones_comp (der (cone_one_car Ar)) unit_cofree_str) one1]
        /(Lfun (der (cone_one_car Ar)) (Lfun unit_cofree_str one1)).
rewrite unit_cofree_str_one1.
have H1 : cone_norm (one1 : cone_one_car Ar) <= 1.
  by rewrite (_ : cone_norm one1 = 1) // /cone_norm /= /c1_norm.
by rewrite (der_prom one1 H1).
Qed.

Lemma unit_cofree_coassoc :
  icones_comp (dig (cone_one_car Ar)) unit_cofree_str =
  icones_comp (bang_fmap unit_cofree_str) unit_cofree_str.
Proof.
apply: one_ext.
have H1 : cone_norm (one1 : cone_one_car Ar) <= 1.
  by rewrite (_ : cone_norm one1 = 1) // /cone_norm /= /c1_norm.
(* LHS: [dig (str one1) = dig (one1!) = (one1!)!]. *)
rewrite -[Lfun (icones_comp (dig (cone_one_car Ar)) unit_cofree_str) one1]
        /(Lfun (dig (cone_one_car Ar)) (Lfun unit_cofree_str one1)).
rewrite unit_cofree_str_one1 (dig_prom one1 H1).
(* RHS: [!str (str one1) = !str (one1!) = (str one1)! = (one1!)!]. *)
rewrite -[Lfun (icones_comp (bang_fmap unit_cofree_str) unit_cofree_str) one1]
        /(Lfun (bang_fmap unit_cofree_str) (Lfun unit_cofree_str one1)).
rewrite unit_cofree_str_one1 (bang_fmap_prom unit_cofree_str one1 H1).
by rewrite unit_cofree_str_one1.
Qed.

Definition unit_cofree : Coalgebra Ar :=
  MkCoalgebra unit_cofree_counit unit_cofree_coassoc.

(** ** LC3 — [d_A] and [e_A] are coalgebra morphisms

    [d_A : !̃A → tens_cofree A A] and [e_A : !̃A → unit_cofree]. *)

(** [d_A] is a coalgebra morphism [!̃A → (!A ⊗ !A, tens_cofree_str A A)]:
    [tens_cofree_str ∘ d_A = !(d_A) ∘ dig_A].  On [x!]:
    LHS [str (d_A(x!)) = str(x! ⊗ x!) = (x! ⊗ x!)!];
    RHS [!d_A (dig_A(x!)) = !d_A((x!)!) = (d_A(x!))! = (x! ⊗ x!)!]. *)
Lemma d_bang_is_coalg_mor (A : ICone.type Ar) :
  is_coalg_mor (bang_cofree A) (tens_cofree A A) (d_bang A).
Proof.
rewrite /is_coalg_mor /=.
apply: bang_ext => x Hx.
have Hpt : cone_norm (x! ⊗p x!) <= 1.
  apply: le_trans (tensor_norm_le _ _) _; rewrite -[1]mulr1.
  by apply: ler_pM => //;
    [exact: cone_norm_ge0 | exact: cone_norm_ge0
     | exact: prom_ball Hx | exact: prom_ball Hx].
(* LHS *)
rewrite -[Lfun (icones_comp (tens_cofree_str A A) (d_bang A)) x!]
        /(Lfun (tens_cofree_str A A) (Lfun (d_bang A) x!)).
rewrite (d_bang_prom Hx).
have Hstr := tens_cofree_str_prom Hx Hx.
rewrite Hstr.
(* RHS *)
rewrite -[Lfun (icones_comp (bang_fmap (d_bang A)) (coalg_str (bang_cofree A))) x!]
        /(Lfun (bang_fmap (d_bang A)) (Lfun (coalg_str (bang_cofree A)) x!)).
rewrite bang_cofree_str (dig_prom x Hx).
rewrite (bang_fmap_prom (d_bang A) x! (prom_ball Hx)).
by rewrite (d_bang_prom Hx).
Qed.

Definition d_bang_hom (A : ICone.type Ar) :
    coalg_hom (bang_cofree A) (tens_cofree A A) :=
  MkCoalgHom (d_bang_is_coalg_mor A).

(** [e_A] is a coalgebra morphism [!̃A → (1, unit_cofree_str)]:
    [unit_cofree_str ∘ e_A = !(e_A) ∘ dig_A].  On [x!]:
    LHS [str_1 (e_A(x!)) = str_1(1) = 1!];
    RHS [!e_A (dig_A(x!)) = !e_A((x!)!) = (e_A(x!))! = 1!]. *)
Lemma e_bang_is_coalg_mor (A : ICone.type Ar) :
  is_coalg_mor (bang_cofree A) unit_cofree (e_bang A).
Proof.
rewrite /is_coalg_mor /=.
apply: bang_ext => x Hx.
(* LHS *)
rewrite -[Lfun (icones_comp unit_cofree_str (e_bang A)) x!]
        /(Lfun unit_cofree_str (Lfun (e_bang A) x!)).
rewrite (e_bang_prom Hx) unit_cofree_str_one1.
(* RHS *)
rewrite -[Lfun (icones_comp (bang_fmap (e_bang A)) (coalg_str (bang_cofree A))) x!]
        /(Lfun (bang_fmap (e_bang A)) (Lfun (coalg_str (bang_cofree A)) x!)).
rewrite bang_cofree_str (dig_prom x Hx).
rewrite (bang_fmap_prom (e_bang A) x! (prom_ball Hx)).
by rewrite (e_bang_prom Hx).
Qed.

Definition e_bang_hom (A : ICone.type Ar) :
    coalg_hom (bang_cofree A) unit_cofree :=
  MkCoalgHom (e_bang_is_coalg_mor A).

(** ** LC4 — [dig_A] is a comonoid morphism

    [dig_A : (!A, d_A, e_A) → (!!A, d_{!A}, e_{!A})] is a morphism of
    commutative comonoids: it commutes with the comultiplications and the
    counits. *)

(** Compatibility with comultiplication:
    [d_{!A} ∘ dig_A = (dig_A ⊗ dig_A) ∘ d_A].  On [x!]:
    LHS [d_{!A}((x!)!) = (x!)! ⊗ (x!)!];
    RHS [(dig ⊗ dig)(x! ⊗ x!) = dig(x!) ⊗ dig(x!) = (x!)! ⊗ (x!)!]. *)
Lemma dig_comonoid_mult (A : ICone.type Ar) :
  icones_comp (d_bang (Bg A)) (dig A) =
  icones_comp (tensor_mor (dig A) (dig A)) (d_bang A).
Proof.
apply: bang_ext => x Hx.
(* LHS *)
rewrite -[Lfun (icones_comp (d_bang (Bg A)) (dig A)) x!]
        /(Lfun (d_bang (Bg A)) (Lfun (dig A) x!)).
rewrite (dig_prom x Hx) (d_bang_prom (prom_ball Hx)).
(* RHS *)
rewrite -[Lfun (icones_comp (tensor_mor (dig A) (dig A)) (d_bang A)) x!]
        /(Lfun (tensor_mor (dig A) (dig A)) (Lfun (d_bang A) x!)).
rewrite (d_bang_prom Hx) tensor_morE.
by rewrite !(dig_prom x Hx).
Qed.

(** Compatibility with counit: [e_{!A} ∘ dig_A = e_A].  On [x!]:
    LHS [e_{!A}((x!)!) = 1]; RHS [e_A(x!) = 1]. *)
Lemma dig_comonoid_counit (A : ICone.type Ar) :
  icones_comp (e_bang (Bg A)) (dig A) = e_bang A.
Proof.
apply: bang_ext => x Hx.
rewrite -[Lfun (icones_comp (e_bang (Bg A)) (dig A)) x!]
        /(Lfun (e_bang (Bg A)) (Lfun (dig A) x!)).
by rewrite (dig_prom x Hx) (e_bang_prom (prom_ball Hx)) (e_bang_prom Hx).
Qed.

End SeelyComonoid.

Arguments diag {R Ar} A.
Arguments diagE {R Ar} A x.
Arguments term {R Ar} A.
Arguments d_bang {R Ar} A.
Arguments d_bang_prom {R Ar A} x.
Arguments e_bang {R Ar} A.
Arguments e_bang_prom {R Ar A} x.
Arguments comonoid_coassoc {R Ar} A.
Arguments comonoid_counitL {R Ar} A.
Arguments comonoid_counitR {R Ar} A.
Arguments comonoid_cocomm {R Ar} A.
Arguments tens_cofree_str {R Ar} A B.
Arguments tens_cofree_str_prom {R Ar A B x y}.
Arguments tens_cofree {R Ar} A B.
Arguments unit_cofree_str {R Ar}.
Arguments unit_cofree {R Ar}.
Arguments one_ext {R Ar C} f g.
Arguments d_bang_is_coalg_mor {R Ar} A.
Arguments d_bang_hom {R Ar} A.
Arguments e_bang_is_coalg_mor {R Ar} A.
Arguments e_bang_hom {R Ar} A.
Arguments dig_comonoid_mult {R Ar} A.
Arguments dig_comonoid_counit {R Ar} A.
