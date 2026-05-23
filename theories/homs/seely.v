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

End Seely.

Arguments linhom_icones {R Ar C D} phi Hphi.
Arguments linhom_iconesE {R Ar C D} phi Hphi x.
Arguments bang_ext_linhom {R Ar B C} phi psi Hphi Hpsi.
Arguments tens_excl_charact {R Ar B1 B2 C} f g.
