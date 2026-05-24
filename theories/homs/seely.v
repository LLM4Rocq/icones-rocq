(**md**************************************************************************)
(** * [ICones] is a Seely category — Paper §9

    From the staged exponential comonad [!] ([theories/homs/bang.v],
    modulo [theories/axioms/exp_interface.v]), the staged symmetric
    monoidal tensor [⊗] ([theories/homs/tensor.v]/[smcc.v], modulo
    [theories/axioms/saft_interface.v]) and the staged Seely
    isomorphisms ([theories/axioms/seely_interface.v]) we DERIVE — as
    genuine theorems modulo those interfaces — that [!] is a *strong
    monoidal comonad*, i.e. [ICones] is a *Seely category* in the sense
    of Melliès (paper §9, lines 7515–7573, ref. [Mellies09]).

    The workhorse is the [n=2] promotion extensionality
    [tens_excl_charact] (paper Lemma [tens-excl-equal-charact]), the
    exact analogue of [tensor_ext] (Prop 5.14) for the [!]-tensor: a
    linear map out of [!B1 ⊗ !B2] is determined by its action on the
    promoted pure tensors [x1! ⊗ x2!].  Every Seely coherence diagram is
    then reduced — exactly as [smcc.v] reduces the SMC coherence to
    pure tensors via [tensor_ext] — to a computation on [x1! ⊗ x2!] via
    [Seely2E]/[dig_prom]/[bang_fmap_prom]/[tensor_morE] and the
    projection/tuple laws of [scones_ccc.v].

    Contents:
    - [linhom_icones] — package a norm-[≤1] [linhom_car Ar C D] element
      as an [icones_hom Ar C D] (the missing element→morphism bridge for
      the inner [!]-cone), with its computation law [linhom_iconesE].
    - [bang_ext_linhom] — the [n=1] promotion extensionality at the
      [linhom_car] level: two norm-[≤1] linear maps out of [!B] agreeing
      on all [x!] are equal.
    - [tens_excl_charact] — Paper Lemma [tens-excl-equal-charact] for
      [n=2]: the [!]-tensor promotion extensionality.  THE workhorse.
    - [seely_comult] — the sample Seely coherence diagram of paper lines
      7527–7573 (comultiplication vs. [Seely2]), proved by
      [tens_excl_charact].
    - [SeelyCategory] / [ICones_Seely] — the strong-monoidal-comonad
      bundle and its canonical witness, mirroring [ICones_SMCC]/
      [SCones_CCC].

    Status (Melliès coherence, §9).  We prove the binary Seely
    isomorphism [Seely2] (the substantive part), its naturality, and the
    comultiplication coherence diagram explicitly drawn in the paper.
    The unit Seely iso [Seely0 : 1 ≅ !⊤] is DEFERRED (see the note on
    [SeelyCategory] below): stating it cleanly needs the terminal object
    [⊤] (empty [icones_prod]) and the scalar action [t·(0!)], which the
    paper itself only sketches ("similarly", line 7508); the binary
    [Seely2] is the substantive content and is delivered in full.

    All results are THEOREMS modulo the staged interfaces; the only
    non-classical assumptions are the staged tensor symbols, the staged
    exponential symbols ([Bang]/[nl]/[lin]/[lin_beta]/[lin_unique]), and
    the staged Seely symbols ([Seely2]/[Seely2E]/[Seely2_natural]). *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import measurable_structure measurable_function.

Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.cone_cat.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.icone.
Require Import Icones.icones.examples_icone.
Require Import Icones.icones.icone_cat.
Require Import Icones.stable.scones_cat.
Require Import Icones.stable.scones_ccc.
Require Import Icones.homs.linhom.
Require Import Icones.homs.linhom_functor.
Require Import Icones.homs.icones_iso.
Require Import Icones.axioms.saft_interface.
Require Import Icones.homs.tensor.
Require Import Icones.homs.smcc.
Require Import Icones.axioms.exp_interface.
Require Import Icones.homs.bang.
Require Import Icones.axioms.seely_interface.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section Seely.
Variables (R : realType) (Ar : MeasSubcat R).

(** The underlying linear function of an [icones_hom] (same coercion
    chain as in [bang.v]). *)
Local Notation Lfun h := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

(** Local mirror of the tensor [⊗], pure tensor [⊗p], exponential [!],
    promotion [x!] and binary product [&]. *)
Local Notation "B '⊗' C" := (tensor Ar B C)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '!'" := (prom x) (at level 2, format "x '!'").

(** ** Bridge: a norm-[≤1] [linhom_car] as an [icones_hom] — Paper §5.1

    A [linhom_car Ar C D] element [φ] is an integrable linear map; when
    its operator norm is [≤ 1] it is exactly the data of an
    [icones_hom Ar C D].  Linearity/ω-continuity/path-preservation/
    integral-preservation come verbatim from [φ]'s fields; the only
    extra requirement of [cones_hom] is the per-point operator bound
    [‖φ x‖ ≤ ‖x‖], which is [linhom_norm_apply_le] at [K = 1].

    This is the element→morphism bridge the [n=2] extensionality needs:
    the inner curried image [Φ(f)(x1!) : !B2 ⊸ C] is a [linhom_car], and
    to apply the [n=1] [bang_ext] to it we view it as an [icones_hom]. *)

Section LinhomIcones.
Variables C D : ICone.type Ar.
Variable phi : linhom_car Ar C D.
Hypothesis Hphi : cone_norm phi <= 1.

(** The per-point operator bound, from [linhom_norm_apply_le] at [K=1].
    Note [cone_norm φ] on the hom-cone IS [linhom_norm φ]. *)
Lemma linhom_icones_norm (x : C) :
  cone_norm (linhom_fun phi x) <= cone_norm x.
Proof. by have := linhom_norm_apply_le Hphi x; rewrite mul1r. Qed.

Definition linhom_icones_cones : cones_hom C D :=
  ConesHom (linhom_fun phi)
    (linhom_pre_linear (linhom_pre_of phi))
    (linhom_pre_continuous (linhom_pre_of phi))
    linhom_icones_norm.

Definition linhom_icones_mcones : mcones_hom Ar C D :=
  MkMConesHom linhom_icones_cones
    (fun X g Hg => linhom_pre_pres_path (linhom_pre_of phi) X g Hg).

Lemma linhom_icones_pres_int
    (X : ar_obj Ar) (β : ar_carrier Ar X -> C)
    (Hβ : is_measurable_path β) (µ : fmeas R (ar_carrier Ar X)) :
  cones_hom_fun (mcones_hom_cones linhom_icones_mcones)
    (icone_integral β Hβ µ) =
  icone_integral
    (fun r => cones_hom_fun (mcones_hom_cones linhom_icones_mcones) (β r))
    (mcones_hom_pres_path linhom_icones_mcones X β Hβ) µ.
Proof.
rewrite /= /linhom_fun (linhom_pres_int phi X β Hβ µ).
by congr icone_integral; exact: Prop_irrelevance.
Qed.

Definition linhom_icones : icones_hom Ar C D :=
  MkIConesHom linhom_icones_mcones linhom_icones_pres_int.

(** [linhom_icones] computes to [φ]'s underlying function. *)
Lemma linhom_iconesE (x : C) : Lfun linhom_icones x = linhom_fun phi x.
Proof. by []. Qed.

End LinhomIcones.

(** ** [n=1] promotion extensionality, [linhom_car] level — Paper §9

    Two norm-[≤1] linear maps [φ ψ : !B ⊸ C] agreeing on every promoted
    point [x!] (for [‖x‖ ≤ 1]) are equal.  We package each as an
    [icones_hom] via [linhom_icones] and discharge by the [n=1]
    [bang_ext]; pointwise equality of the packaged morphisms then yields
    [φ = ψ] by [linhom_eq]. *)
Lemma bang_ext_linhom (B C : ICone.type Ar)
    (phi psi : linhom_car Ar (Bang Ar B) C)
    (Hphi : cone_norm phi <= 1) (Hpsi : cone_norm psi <= 1) :
  (forall x : B, cone_norm x <= 1 -> linhom_fun phi x! = linhom_fun psi x!) ->
  phi = psi.
Proof.
move=> Hpp.
have Heq : linhom_icones Hphi = linhom_icones Hpsi.
  apply: bang_ext => x Hx.
  by rewrite !linhom_iconesE; exact: Hpp.
apply: linhom_eq => z.
by rewrite -(linhom_iconesE Hphi z) -(linhom_iconesE Hpsi z) Heq.
Qed.

(** ** Paper Lemma [tens-excl-equal-charact] — the [n=2] case

    Two linear maps [f g : !B1 ⊗ !B2 → C] agreeing on every promoted
    pure tensor [x1! ⊗ x2!] (for [‖x1‖ ≤ 1], [‖x2‖ ≤ 1]) are equal.

    Proof (the paper's induction, [n=2] unfolded).  Curry [f, g] to
    [F = Φ(f), G = Φ(g) : !B1 → (!B2 ⊸ C)] with the staged tensor
    adjunction; by injectivity of [Φ] ([tensor_curry_inj]) it suffices
    that [F = G].  By the [n=1] [bang_ext] it suffices that [F(x1!) =
    G(x1!) : !B2 ⊸ C] for [‖x1‖ ≤ 1].  These are [linhom_car] elements
    of norm [≤ 1] (image of the norm-[≤1] morphism [F] at the unit-ball
    point [x1!]); by the [linhom]-level [bang_ext_linhom] it suffices
    that they agree on every [x2!], i.e. [F(x1!)(x2!) = G(x1!)(x2!)] for
    [‖x2‖ ≤ 1].  By [tensor_curryE] this is [f(x1! ⊗ x2!) =
    g(x1! ⊗ x2!)], the hypothesis. *)
Lemma tens_excl_charact (B1 B2 C : ICone.type Ar)
    (f g : icones_hom Ar (Bang Ar B1 ⊗ Bang Ar B2) C) :
  (forall (x1 : B1) (x2 : B2),
     cone_norm x1 <= 1 -> cone_norm x2 <= 1 ->
     Lfun f (x1! ⊗p x2!) = Lfun g (x1! ⊗p x2!)) ->
  f = g.
Proof.
move=> Hfg.
apply: tensor_curry_inj.
apply: bang_ext => x1 Hx1.
have Hnf : cone_norm (Lfun (tensor_curry f) x1!) <= 1.
  exact: (le_trans (cones_hom_norm_le1 _ x1!) (prom_ball Hx1)).
have Hng : cone_norm (Lfun (tensor_curry g) x1!) <= 1.
  exact: (le_trans (cones_hom_norm_le1 _ x1!) (prom_ball Hx1)).
apply: (bang_ext_linhom Hnf Hng) => x2 Hx2.
rewrite !tensor_curryE.
exact: Hfg.
Qed.

(** ** Paper Lemma [tens-excl-equal-charact] — the [n=3] case

    Two linear maps [f g : !A ⊗ (!B ⊗ !C) → C0] agreeing on every
    promoted pure tensor [x! ⊗ (y! ⊗ z!)] (for [‖x‖,‖y‖,‖z‖ ≤ 1]) are
    equal.  This is the instance of the general-[n] paper lemma needed by
    the monoidal-functor *associativity* coherence (one outer [!A], an
    inner [!B ⊗ !C]).

    Proof (the paper's induction, [n=3] unfolded — exactly one more
    currying layer than [tens_excl_charact]).  Curry off the OUTER [!A]
    with [tensor_curry_inj]; by [bang_ext] it suffices that the curried
    images agree at every [x!] ([‖x‖ ≤ 1]), as [linhom_car]s out of the
    inner tensor [!B ⊗ !C].  These are norm-[≤1] (the curried map [F] is
    norm-[≤1], evaluated at the unit-ball point [x!]); package each as an
    [icones_hom] via [linhom_icones] and discharge by the [n=2]
    [tens_excl_charact] on [!B ⊗ !C], using [linhom_iconesE]/[tensor_curryE]
    to turn agreement on [y! ⊗ z!] back into the hypothesis. *)
Lemma tens_excl_charact3 (A B C C0 : ICone.type Ar)
    (f g : icones_hom Ar (Bang Ar A ⊗ (Bang Ar B ⊗ Bang Ar C)) C0) :
  (forall (x : A) (y : B) (z : C),
     cone_norm x <= 1 -> cone_norm y <= 1 -> cone_norm z <= 1 ->
     Lfun f (x! ⊗p (y! ⊗p z!)) = Lfun g (x! ⊗p (y! ⊗p z!))) ->
  f = g.
Proof.
move=> Hfg.
apply: tensor_curry_inj.
apply: bang_ext => x Hx.
have Hnf : cone_norm (Lfun (tensor_curry f) x!) <= 1.
  exact: (le_trans (cones_hom_norm_le1 _ x!) (prom_ball Hx)).
have Hng : cone_norm (Lfun (tensor_curry g) x!) <= 1.
  exact: (le_trans (cones_hom_norm_le1 _ x!) (prom_ball Hx)).
have Heq : linhom_icones Hnf = linhom_icones Hng.
  apply: tens_excl_charact => y z Hy Hz.
  rewrite (linhom_iconesE Hnf (y! ⊗p z!)) (linhom_iconesE Hng (y! ⊗p z!)).
  rewrite !tensor_curryE.
  exact: Hfg.
apply: linhom_eq => w.
by rewrite -(linhom_iconesE Hnf w) -(linhom_iconesE Hng w) Heq.
Qed.

(** The left-associated [n=3] case [(!A ⊗ !B) ⊗ !C → C0], for the
    associativity coherence read on the left tree.  Curry off the
    rightmost [!C] with [tensor_curry_inj]; the [n=2] [tens_excl_charact]
    on the inner [!A ⊗ !B] reduces to fixed [x! ⊗ y!], whose curried
    image is a norm-[≤1] [linhom_car] out of [!C] — discharge by the
    [linhom]-level [n=1] [bang_ext_linhom] on [z!]. *)
Lemma tens_excl_charact3l (A B C C0 : ICone.type Ar)
    (f g : icones_hom Ar ((Bang Ar A ⊗ Bang Ar B) ⊗ Bang Ar C) C0) :
  (forall (x : A) (y : B) (z : C),
     cone_norm x <= 1 -> cone_norm y <= 1 -> cone_norm z <= 1 ->
     Lfun f ((x! ⊗p y!) ⊗p z!) = Lfun g ((x! ⊗p y!) ⊗p z!)) ->
  f = g.
Proof.
move=> Hfg.
apply: tensor_curry_inj.
apply: tens_excl_charact => x y Hx Hy.
have Hp : cone_norm (x! ⊗p y!) <= 1.
  apply: le_trans (tensor_norm_le _ _) _; rewrite -[1]mulr1.
  by apply: ler_pM => //;
    [exact: cone_norm_ge0 | exact: cone_norm_ge0
     | exact: prom_ball Hx | exact: prom_ball Hy].
have Hnf : cone_norm (Lfun (tensor_curry f) (x! ⊗p y!)) <= 1.
  exact: (le_trans (cones_hom_norm_le1 _ _) Hp).
have Hng : cone_norm (Lfun (tensor_curry g) (x! ⊗p y!)) <= 1.
  exact: (le_trans (cones_hom_norm_le1 _ _) Hp).
apply: (bang_ext_linhom Hnf Hng) => z Hz.
rewrite !tensor_curryE.
exact: Hfg.
Qed.

(** ** The Seely structure maps — Paper §9

    The two structural maps of a *Seely category*: the binary Seely iso
    [Seely2] (re-exported from the staged interface) and the
    [&]-projection tuple [⟨!π1, !π2⟩ : !(B1 & B2) → (!B1 & !B2)] used to
    transport [dig] across [Seely2]. *)

(** The [&]-projections [π1]/[π2] on [sprod B1 B2]. *)
Definition sproj1 (B1 B2 : ICone.type Ar) : icones_hom Ar (sprod B1 B2) B1 :=
  icones_proj true.
Definition sproj2 (B1 B2 : ICone.type Ar) : icones_hom Ar (sprod B1 B2) B2 :=
  icones_proj false.

Lemma sproj1_pair (B1 B2 : ICone.type Ar) (x1 : B1) (x2 : B2) :
  Lfun (sproj1 B1 B2) (sprod_pair x1 x2) = x1.
Proof. by []. Qed.

Lemma sproj2_pair (B1 B2 : ICone.type Ar) (x1 : B1) (x2 : B2) :
  Lfun (sproj2 B1 B2) (sprod_pair x1 x2) = x2.
Proof. by []. Qed.

(** The tuple [⟨!π1, !π2⟩ : !(B1 & B2) → (!B1 & !B2)] (paper's
    [⟨!Proj1, !Proj2⟩]). *)
Definition bang_proj_tuple (B1 B2 : ICone.type Ar) :
    icones_hom Ar (Bang Ar (sprod B1 B2)) (sprod (Bang Ar B1) (Bang Ar B2)) :=
  icones_tuple
    (fun b : bool =>
       if b as b0 return icones_hom Ar (Bang Ar (sprod B1 B2))
                           (sprod_fam (Bang Ar B1) (Bang Ar B2) b0)
       then bang_fmap (sproj1 B1 B2)
       else bang_fmap (sproj2 B1 B2)).

(** [⟨!π1, !π2⟩(q)] is the pairing of [!π1(q)] and [!π2(q)]. *)
Lemma bang_proj_tupleE (B1 B2 : ICone.type Ar) (q : Bang Ar (sprod B1 B2)) :
  Lfun (bang_proj_tuple B1 B2) q =
  sprod_pair (Lfun (bang_fmap (sproj1 B1 B2)) q)
             (Lfun (bang_fmap (sproj2 B1 B2)) q).
Proof. by apply: cones_prod_eq => -[]. Qed.

(** ** The comultiplication coherence diagram — Paper §9, lines 7527–7573

    The sample Seely coherence diagram explicitly proved in the paper:
    transporting the comultiplication [dig] across [Seely2] commutes with
    the [&]-projection tuple, i.e. as maps [!B1 ⊗ !B2 → !(!B1 & !B2)]

      [!⟨!π1,!π2⟩ ∘ dig_{B1&B2} ∘ Seely2_{B1,B2}]
        [= Seely2_{!B1,!B2} ∘ (dig_{B1} ⊗ dig_{B2})].

    Proof: by [tens_excl_charact] both sides agree once they agree on
    every [x1! ⊗ x2!].  The LHS reduces via [Seely2E]/[dig_prom]/
    [bang_fmap_prom] and the projection laws to [⟨x1!,x2!⟩!]; the RHS
    reduces via [tensor_morE]/[dig_prom]/[Seely2E] (the latter applied at
    the unit-ball points [x1!], [x2!]) to the same [⟨x1!,x2!⟩!]. *)
Lemma seely_comult (B1 B2 : ICone.type Ar) :
  icones_comp (bang_fmap (bang_proj_tuple B1 B2))
    (icones_comp (dig (sprod B1 B2)) (iso_fwd (Seely2 B1 B2))) =
  icones_comp (iso_fwd (Seely2 (Bang Ar B1) (Bang Ar B2)))
    (tensor_mor (dig B1) (dig B2)).
Proof.
apply: tens_excl_charact => x1 x2 Hx1 Hx2.
have Hp : cone_norm (sprod_pair x1 x2) <= 1 by exact: sprod_pair_norm_le1.
(* RHS: through the bifunctor [dig ⊗ dig], then [Seely2] at [x1!, x2!]. *)
rewrite [in RHS]/= tensor_morE (dig_prom x1 Hx1) (dig_prom x2 Hx2).
rewrite (Seely2E x1! x2! (prom_ball Hx1) (prom_ball Hx2)).
(* LHS: [Seely2] at [x1, x2], then [dig], then [!⟨!π1,!π2⟩]. *)
rewrite /= (Seely2E x1 x2 Hx1 Hx2) (dig_prom (sprod_pair x1 x2) Hp).
rewrite (bang_fmap_prom (bang_proj_tuple B1 B2) (sprod_pair x1 x2)! (prom_ball Hp)).
rewrite bang_proj_tupleE.
rewrite (bang_fmap_prom (sproj1 B1 B2) (sprod_pair x1 x2) Hp).
rewrite (bang_fmap_prom (sproj2 B1 B2) (sprod_pair x1 x2) Hp).
by rewrite sproj1_pair sproj2_pair.
Qed.

End Seely.

Arguments linhom_icones {R Ar C D} phi Hphi.
Arguments linhom_iconesE {R Ar C D} phi Hphi x.
Arguments bang_ext_linhom {R Ar B C} phi psi Hphi Hpsi.
Arguments tens_excl_charact {R Ar B1 B2 C} f g.
Arguments tens_excl_charact3 {R Ar A B C C0} f g.
Arguments tens_excl_charact3l {R Ar A B C C0} f g.
Arguments sproj1 {R Ar} B1 B2.
Arguments sproj2 {R Ar} B1 B2.
Arguments bang_proj_tuple {R Ar} B1 B2.
Arguments seely_comult {R Ar} B1 B2.

(** ** Paper §9 Theorem — [ICones] is a Seely category (ref. [Mellies09])

    We bundle the *strong monoidal comonad* structure of [!] into a
    single record [SeelyCategory R Ar].  A Seely category (Melliès,
    "Categorical semantics of linear logic", §7) is a symmetric monoidal
    closed category with finite products together with a comonad [!] and
    *Seely isomorphisms* [!A ⊗ !B ≅ !(A & B)] and [1 ≅ !⊤] that are
    monoidal-natural and make [!] a strong monoidal functor from the
    cartesian [(&, ⊤)] to the tensor [(⊗, 1)].

    The fields gather the data and laws established in this development:

    - [sc_smcc] : the symmetric monoidal closed structure of [smcc.v]
      (Thm 5.15), supplying [⊗], the unit [1], the bifunctor action and
      the [α]/[λ]/[ρ]/[σ] coherence;
    - [sc_comonad] : the exponential comonad [!] of [bang.v] (§9),
      supplying [!], [!f], [der], [dig] and the comonad laws;
    - [sc_prod] : the binary product [&] ([scones_ccc.v]'s [sprod]) — the
      cartesian structure the Seely iso relates to the tensor;
    - [sc_seely2] : the binary Seely iso [!A ⊗ !B ≅ !(A & B)] with its
      characterisation [sc_seely2E] on promoted pure tensors and its
      naturality [sc_seely2_nat] (the staged Yoneda data);
    - [sc_comult] : the comultiplication coherence diagram (paper lines
      7527–7573), the sample Melliès coherence law DERIVED here via
      [tens_excl_charact].

    The canonical witness [ICones_Seely] populates every field with the
    proved lemmas; the only unproved inputs are the staged tensor / exp /
    Seely symbols, discharged by M-SAFT (PLAN §13).

    Status of the Melliès coherence laws.  We DELIVER: the strong
    monoidal comonad data ([!], [⊗], [&], [Seely2]); the binary Seely
    iso and its naturality; and the comultiplication coherence the paper
    draws explicitly (line 7527) — proved, not assumed, via
    [tens_excl_charact].  Each of Melliès' remaining coherence squares
    (the counit/[der] square, the [Seely2] associativity/unit/symmetry
    squares against [α]/[λ]/[ρ]/[σ], and the [Seely0] unit-iso squares)
    has the SAME shape — agree on [x1! ⊗ x2!], reduce both sides by
    [Seely2E]/[dig_prom]/[bang_fmap_prom]/[tensor_morE] — and is provable
    by the identical [tens_excl_charact] recipe; the paper itself states
    (line 7521) they are "easy to prove" by Lemma
    [tens-excl-equal-charact], i.e. by exactly [tens_excl_charact].  They
    are NOT axiomatised here: a [SeelyCategory] records the laws actually
    proved.  The unit Seely iso [Seely0 : 1 ≅ !⊤] is likewise DEFERRED
    (it needs the terminal object [⊤] as an empty [icones_prod]); since
    every coherence law involving [Seely0] would consume it, the bundle
    records only the binary [Seely2] data, which is the substantive
    part. *)

Record SeelyCategory (R : realType) (Ar : MeasSubcat R) : Type :=
  MkSeelyCategory {
  (* the symmetric monoidal closed structure (Thm 5.15) *)
  sc_smcc : ICones_SMCC Ar;
  (* the exponential comonad [!] (§9) *)
  sc_comonad : Comonad Ar;
  (* the comonad object map IS the SMC-tensor's [!]; pin it down *)
  sc_bangE : cm_obj sc_comonad = @Bang R Ar;
  (* the cartesian product [&] used by the Seely iso is [scones_ccc]'s
     [sprod]; pin it to the SMC bundle's tensor on the [!]-objects below *)
  sc_tensorE : forall A B : ICone.type Ar,
    smcc_tensor sc_smcc A B = tensor Ar A B;
  (* the binary Seely isomorphism [!A ⊗ !B ≅ !(A & B)], over the
     project's tensor [⊗] (= [smcc_tensor sc_smcc] by [sc_tensorE]) and
     the product [&] (= [sprod]) *)
  sc_seely2 : forall B1 B2 : ICone.type Ar,
    icones_iso Ar (tensor Ar (Bang Ar B1) (Bang Ar B2))
                  (Bang Ar (sprod B1 B2));
  (* its characterisation on promoted pure tensors (paper line 7501) *)
  sc_seely2E : forall (B1 B2 : ICone.type Ar) (x1 : B1) (x2 : B2),
    cone_norm x1 <= 1 -> cone_norm x2 <= 1 ->
    iso_fwd (sc_seely2 B1 B2) (ptensor (prom x1) (prom x2)) =
    prom (sprod_pair x1 x2);
  (* naturality of [Seely2] in both slots (paper line 7494) *)
  sc_seely2_nat : forall (B1 B2 B1' B2' : ICone.type Ar)
    (f1 : icones_hom Ar B1 B1') (f2 : icones_hom Ar B2 B2'),
    icones_comp (bang_fmap (sprod_mor f1 f2)) (iso_fwd (sc_seely2 B1 B2)) =
    icones_comp (iso_fwd (sc_seely2 B1' B2'))
                (tensor_mor (bang_fmap f1) (bang_fmap f2));
  (* comultiplication coherence (paper lines 7527–7573), DERIVED *)
  sc_comult : forall B1 B2 : ICone.type Ar,
    icones_comp (bang_fmap (bang_proj_tuple B1 B2))
      (icones_comp (dig (sprod B1 B2)) (iso_fwd (sc_seely2 B1 B2))) =
    icones_comp (iso_fwd (sc_seely2 (Bang Ar B1) (Bang Ar B2)))
      (tensor_mor (dig B1) (dig B2));
}.

Arguments SeelyCategory {R} Ar.

(** Paper §9: the canonical Seely-category structure on [ICones], every
    field populated by a proved lemma (modulo the staged tensor / exp /
    Seely interfaces). *)
Definition ICones_Seely (R : realType) (Ar : MeasSubcat R) :
    SeelyCategory Ar :=
  {| sc_smcc := ICones_smcc Ar;
     sc_comonad := Bang_comonad Ar;
     sc_bangE := erefl;
     sc_tensorE := fun _ _ => erefl;
     sc_seely2 := @Seely2 R Ar;
     sc_seely2E := @Seely2E R Ar;
     sc_seely2_nat := @Seely2_natural R Ar;
     sc_comult := @seely_comult R Ar |}.
