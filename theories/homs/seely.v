(**md**************************************************************************)
(** * [ICones] is a Seely category — Paper §9

    From the staged exponential comonad [!] ([theories/homs/bang.v],
    modulo [theories/axioms/exp_interface.v]), the now-AXIOM-FREE
    symmetric monoidal tensor [⊗] ([theories/homs/tensor.v]/[smcc.v]; the
    SAFT contract [saft_interface.v] is discharged and deleted) and the
    staged Seely isomorphisms ([theories/axioms/seely_interface.v]) we
    DERIVE — as genuine theorems modulo the remaining (exp/Seely)
    interfaces — that [!] is a *strong monoidal comonad*, i.e. [ICones]
    is a *Seely category* in the sense of Melliès (paper §9, lines
    7515–7573, ref. [Mellies09]).

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
    - [tens_excl_charact3]/[tens_excl_charact3l] — the [n=3] cases (right-
      and left-associated), for the monoidal-functor associativity.
    - [spair]/[sprod_assoc]/[sprod_braid]/[sprod_lunit]/[sprod_runit] —
      the cartesian structural isos of the binary product [&] and the
      terminal [⊤], built from [icones_proj]/[icones_tuple], with their
      pure-pairing computation laws.
    - [seely_assoc]/[seely_braid]/[seely_lunit]/[seely_runit] — the FULL
      symmetric-monoidal-functor coherence of [(!, Seely2, Seely0)]:
      associativity, symmetry, left/right unit.
    - [seely_comult] — the comultiplication coherence of paper lines
      7527–7573 ([dig] vs. [Seely2]).
    - [seely_der_unit]/[seely_der1]/[seely_der2] — the counit ([der])
      compatibility laws.
    - [SeelyCategory] / [ICones_Seely] — the strong-monoidal-comonad
      bundle and its canonical witness, mirroring [ICones_SMCC]/
      [SCones_CCC].

    Status (Melliès coherence, §9).  [ICones] is now a FULL Seely category
    in the sense of Melliès (ref. [Mellies09]): we deliver the
    strong-monoidal-comonad data ([!], [⊗], [&], [⊤], [Seely2], [Seely0]),
    the binary AND unit Seely isos with their characterisations and the
    [Seely2] naturality, the FULL symmetric-monoidal-functor coherence of
    [(!, Seely2, Seely0)] (associativity, symmetry, both unitors), the
    comultiplication ([dig]) coherence the paper draws explicitly, and the
    counit ([der]) compatibility.  Every coherence is PROVED — not assumed
    — by the paper's recipe (reduce on promoted pure tensors via
    [tens_excl_charact]/[tens_excl_charact3l] or the mixed unit
    extensionality, then compute by [Seely2E]/[Seely0E]/[bang_fmap_prom]/
    [tensor_morE] + the structural-iso E-laws), exactly the "easy by Lemma
    [tens-excl-equal-charact]" of paper line 7521.  The only un-stated
    square is a SINGLE un-projected morphism equation for the binary
    counit [der_{A&B} ∘ Seely2_{A,B} : !A ⊗ !B → A & B]: [&] and [⊗]
    differ with no canonical comparison [A & B ↔ A ⊗ B] to phrase it
    through, so it is recorded in projected form ([seely_der1]/[der2]),
    which carries the same content.

    All results are THEOREMS modulo the remaining staged interfaces; the
    tensor symbols are now AXIOM-FREE (SAFT discharged), so the only
    non-classical assumptions left are the staged exponential symbols
    ([Bang]/[nl]/[lin]/[lin_beta]/[lin_unique]) and the staged Seely
    symbols ([Seely2]/[Seely2E]/[Seely2_natural] and [Seely0]/[Seely0E]). *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import measurable_structure measurable_function.

Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.omega_general.
Require Import Icones.cones.cone_cat.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.icone.
Require Import Icones.icones.examples_icone.
Require Import Icones.icones.icone_cat.
Require Import Icones.stable.totmono.
Require Import Icones.stable.scones_cat.
Require Import Icones.stable.scones_ccc.
Require Import Icones.homs.linhom.
Require Import Icones.homs.linhom_functor.
Require Import Icones.homs.icones_iso.
Require Import Icones.homs.tensor.
Require Import Icones.homs.smcc.
Require Import Icones.axioms.exp_interface.
Require Import Icones.homs.bang.
Require Import Icones.axioms.seely_interface.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

(** P6 — the tensor SAFT contract is DISCHARGED.  [tensor.v] (Required
    above) [Export]s the proved tensor symbols, replacing the former
    [saft_interface].  Re-seal the now-TRANSPARENT structural-iso /
    bifunctor data so a bare [/=]/[simpl] in the Seely coherence proofs
    below does not unfold the [tensor_construct] internals (which would
    break the [tensor_assocEp]/[tensor_braidEp]/[tensor_morE]/[...Ep]
    rewrites); [conversion] still computes their [...E] values, so the
    promotion-coherence proofs go through verbatim. *)
Opaque tensor_mor tensor_assoc tensor_lunit tensor_runit tensor_braid
       tensor_curry tensor_uncurry ptensor tau.

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
    [F = Φ(f), G = Φ(g) : !B1 → (!B2 ⊸ C)] with the tensor
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

(** ** Exponential naturality of [lin] — Paper §9 ([E ⊣ Der] naturality)

    [lin] is natural on the [ICones]-side: post-composing the linear
    factoriser by a morphism [g] is the factoriser of the stable map
    [ders g ∘ f].  Proof by the uniqueness half [lin_unique]: compute
    [Θ(g ∘ lin f) = ders g ∘ (ders (lin f) ∘ nl) = ders g ∘ Θ(lin f) =
    ders g ∘ f] via [ders_comp]/[scones_compA]/[ThetaK]. *)
Lemma lin_natural (B C D : ICone.type Ar)
    (g : icones_hom Ar C D) (f : scones_hom B C) :
  lin (scones_comp (ders g) f) = icones_comp g (lin f).
Proof.
apply/esym/lin_unique.
rewrite /Theta ders_comp -scones_compA.
by rewrite -/(Theta (lin f)) ThetaK.
Qed.

(** Dual exponential naturality of [Θ]: [Θ (g ∘ h) = ders g ∘ Θ h].  The
    [SCones]-side reading of [lin_natural]; immediate from [ders_comp] and
    associativity of [scones_comp]. *)
Lemma Theta_comp (B C D : ICone.type Ar)
    (g : icones_hom Ar C D) (h : icones_hom Ar (Bang Ar B) C) :
  Theta (icones_comp g h) = scones_comp (ders g) (Theta h).
Proof. by rewrite /Theta ders_comp -scones_compA. Qed.

(** ** Paper §9 — the unit Seely isomorphism [\Seelyz] (DISCHARGED)

    The unit Seely iso [Seely0 : 1 ≅ !⊤], built by the contravariant
    Yoneda lemma [co_yoneda_iso] from the natural hom-bijection
    [ICones(1, C) ≃ ICones(!⊤, C)].  Both hom-sets are the unit ball of
    [C]: a morphism [1 → C] is its value at the unit [1] ([eval1]); a
    morphism [!⊤ → C] is [lin] of a stable map [⊤ → C], which (since [⊤]
    is the one-point cone) is the *constant* map at its value on [0].  The
    forward map of the assembled iso is [psiV id_{!⊤}], the linear-point
    map [t ↦ t·(0!)], giving [Seely0E] by [lin_ptE]. *)

Section Seely0Build.

(** The constant stable map [⊤ → C] at value [c] (for [‖c‖ ≤ 1]).
    [⊤ = Stop] is the one-point cone, so the off-ball [0]-extension is
    vacuous; total monotonicity is the constant-sum order
    [big_Pneg_le_Ppos]; ω-continuity-on-the-unit-ball is the sup of a
    constant chain; measurability of paths is [const_path_measurable]. *)
Section ConstScones.
Variable C : ICone.type Ar.
Variable c : C.
Hypothesis Hc : cone_norm c <= 1.

Definition cs_fun : Stop Ar -> C := fun _ => c.

Lemma cs_totmono : is_totmono cs_fun.
Proof. by move=> n x u _; rewrite /cs_fun; exact: big_Pneg_le_Ppos. Qed.

Lemma cs_stable : is_stable cs_fun.
Proof.
split.
- exact: cs_totmono.
- by exists (cone_norm c) => x _; rewrite /cs_fun.
- move=> Mf u uch ub1 fuch fubMf Mfpos; rewrite /cs_fun.
  (* RHS is [cone_sup_at] of the constant-[c] image chain, which is [c]
     by antisymmetry. *)
  apply: precone_le_anti.
  + exact: (cone_sup_at_ub fuch fubMf Mfpos 0%N).
  + by apply: cone_sup_at_lub => n /=; exact: precone_le_refl.
Qed.

Lemma cs_meas_stable : is_meas_stable cs_fun.
Proof.
split; first exact: cs_stable.
by move=> X γ _ _; rewrite /cs_fun; exact: const_path_measurable.
Qed.

Lemma cs_norm_le1 : sc_norm cs_fun <= 1.
Proof. by apply: sc_norm_lub => x _; rewrite /cs_fun. Qed.

(** Every point of [⊤] has norm [0 ≤ 1], so off-ball is vacuous. *)
Lemma cs_offball (x : Stop Ar) : ~~ (cone_norm x <= 1) -> cs_fun x = precone_zero.
Proof. by rewrite (Stop_is0 x) cone_norm0 ler01. Qed.

Definition cs : scones_hom (Stop Ar) C :=
  MkSconesHom cs_fun cs_meas_stable cs_norm_le1 cs_offball.

(** [cs] evaluated anywhere is the constant [c]. *)
Lemma csE (x : Stop Ar) : sc_fun cs x = c.
Proof. by []. Qed.

End ConstScones.

Variable C : ICone.type Ar.

(** A morphism [1 → C] is norm-[≤1] at the unit point. *)
Lemma one_eval_ball (f : icones_hom Ar (cone_one_car Ar) C) :
  cone_norm (Lfun f (c1_one Ar)) <= 1.
Proof.
apply: le_trans (cones_hom_norm_le1 _ (c1_one Ar)) _.
by rewrite (_ : cone_norm (c1_one Ar) = 1) // /cone_norm /= /c1_norm.
Qed.

(** A promoted [⊤]-point [x!] (for [‖x‖ ≤ 1]) of a [!⊤ → C] morphism is
    norm-[≤1]; in particular at [0!]. *)
Lemma bangstop_eval_ball (g : icones_hom Ar (Bang Ar (Stop Ar)) C) :
  cone_norm (Lfun g (prom (precone_zero : Stop Ar))) <= 1.
Proof.
apply: le_trans (cones_hom_norm_le1 _ _) _.
by apply: prom_ball; rewrite cone_norm0.
Qed.

(** Forward leg [ICones(1, C) → ICones(!⊤, C)]: send [f] to [lin] of the
    constant stable map at [f(1)]. *)
Definition psi0 (f : icones_hom Ar (cone_one_car Ar) C) :
    icones_hom Ar (Bang Ar (Stop Ar)) C :=
  lin (cs (one_eval_ball f)).

(** Backward leg [ICones(!⊤, C) → ICones(1, C)]: send [g] to the
    linear-point map at [g(0!)]. *)
Definition psiV0 (g : icones_hom Ar (Bang Ar (Stop Ar)) C) :
    icones_hom Ar (cone_one_car Ar) C :=
  linhom_icones (phi := lin_pt (Lfun g (prom (precone_zero : Stop Ar))))
    (le_trans (lo_lift_norm_le1 _) (bangstop_eval_ball g)).

(** [psi0 f] applied to a promoted point [x!] is the constant [f(1)]. *)
Lemma psi0_prom (f : icones_hom Ar (cone_one_car Ar) C) (x : Stop Ar) :
  cone_norm x <= 1 -> Lfun (psi0 f) x! = Lfun f (c1_one Ar).
Proof.
move=> Hx; rewrite /psi0.
rewrite -(Theta_prom (lin (cs (one_eval_ball f))) x Hx) ThetaK.
by rewrite csE.
Qed.

(** [psiV0 g] applied to [s : 1] is [c1_val s · g(0!)]. *)
Lemma psiV0E (g : icones_hom Ar (Bang Ar (Stop Ar)) C) (s : cone_one_car Ar) :
  Lfun (psiV0 g) s = precone_scale (c1_val s) (Lfun g (prom (precone_zero : Stop Ar))).
Proof. by rewrite /psiV0 linhom_iconesE lin_ptE. Qed.

End Seely0Build.

(** *** The four [co_yoneda_iso] hypotheses for [Seely0]. *)

(** Round-trip [psiV0 (psi0 f) = f].  [psi0 f] at [0!] is [f(1)]
    ([psi0_prom]), so [psiV0 (psi0 f)] is the linear-point map at [f(1)];
    evaluated at [s] it is [c1_val s · f(1) = f(c1_val s · 1) = f s] by
    homogeneity of [f]. *)
Lemma psi0K (C : ICone.type Ar) (f : icones_hom Ar (cone_one_car Ar) C) :
  psiV0 (psi0 f) = f.
Proof.
apply: icones_hom_eq => s.
rewrite psiV0E.
have H0 : cone_norm (precone_zero : Stop Ar) <= 1 by rewrite cone_norm0.
rewrite (psi0_prom f H0).
rewrite -[Lfun f (c1_one Ar)]/(cones_hom_fun _ (c1_one Ar)).
rewrite -(basic_lemmas.linearZ (cones_hom_linear _) (c1_val s) (c1_one Ar)).
congr (cones_hom_fun _ _).
by apply: cone_one_eq; apply: val_inj => /=; rewrite mulr1.
Qed.

(** Round-trip [psi0 (psiV0 g) = g].  [psiV0 g] at [1] is [g(0!)], so
    [psi0 (psiV0 g)] is the constant-[g(0!)] [lin]; on every [x!] it is
    [g(0!) = g(x!)] since all points of [⊤] equal [0] ([Stop_is0]).
    Discharge by [bang_ext]. *)
Lemma psiV0K (C : ICone.type Ar) (g : icones_hom Ar (Bang Ar (Stop Ar)) C) :
  psi0 (psiV0 g) = g.
Proof.
apply: bang_ext => x Hx.
rewrite (psi0_prom (psiV0 g) Hx) psiV0E.
have e1 : c1_val (c1_one Ar) = 1%:nng by [].
rewrite e1 precone_scale_1.
by rewrite (Stop_is0 x).
Qed.

(** Postcomposition naturality of [psi0]: [psi0 (g ∘ f) = g ∘ psi0 f].
    [Lfun (g∘f) 1 = g(f 1)], and [lin] is natural ([lin_natural]):
    [psi0 (g∘f) = lin (cs (g(f 1))) = lin (ders g ∘ cs (f 1)) =
    g ∘ lin (cs (f 1))], the last step since [ders g ∘ (const f1)] is
    the constant [g(f 1)] (on the ball; off-ball both clamp to [0]). *)
Lemma psi0_nat (C C' : ICone.type Ar)
    (f : icones_hom Ar (cone_one_car Ar) C) (g : icones_hom Ar C C') :
  psi0 (icones_comp g f) = icones_comp g (psi0 f).
Proof.
rewrite /psi0 -lin_natural; congr lin.
apply: scones_hom_eq => x.
(* every point of [⊤] has norm [0 ≤ 1] *)
have Hx : cone_norm x <= 1 by rewrite (Stop_is0 x) cone_norm0.
rewrite csE.
(* RHS [scones_comp (ders g) (cs (f 1))] on the ball: clamp, then [ders g]
   of the constant [f 1] (also in the ball, [one_eval_ball f]). *)
rewrite /= (sc_clamp_ball Hx).
rewrite -[cs_fun (Lfun f (c1_one Ar)) x]/(Lfun f (c1_one Ar)).
by rewrite (sc_clamp_ball (one_eval_ball f)).
Qed.

(** Postcomposition naturality of [psiV0]: [psiV0 (g ∘ f) = g ∘ psiV0 f].
    [Lfun (g∘f) 0! = g(f(0!))], so both sides at [s] are
    [c1_val s · g(f(0!))] (by homogeneity of [g] on the RHS). *)
Lemma psiV0_nat (C C' : ICone.type Ar)
    (f : icones_hom Ar (Bang Ar (Stop Ar)) C) (g : icones_hom Ar C C') :
  psiV0 (icones_comp g f) = icones_comp g (psiV0 f).
Proof.
apply: icones_hom_eq => s.
rewrite psiV0E /=.
by rewrite lin_ptE (basic_lemmas.linearZ (cones_hom_linear _)).
Qed.

(** The unit Seely iso [Seely0 : 1 ≅ !⊤], assembled by [co_yoneda_iso].
    Its forward is [psiV0 id_{!⊤}], the linear-point map [t ↦ t·(0!)]. *)
Definition Seely0 : icones_iso Ar (cone_one_car Ar) (Bang Ar (Stop Ar)) :=
  co_yoneda_iso psi0 psiV0 psi0K psiV0K psi0_nat psiV0_nat.

(** Paper line 7508: [Seely0(t) = t·(0!)]. *)
Lemma Seely0E (t : cone_one_car Ar) :
  iso_fwd Seely0 t =
  precone_scale (c1_val t) (prom (precone_zero : Stop Ar)).
Proof.
rewrite /Seely0 /co_yoneda_iso /=.
by rewrite lin_ptE.
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

(** ** The cartesian-product structural isos for [&] — Paper §7.4

    The symmetric-monoidal-functor coherence of [!] relates [Seely2] /
    [Seely0] to the *cartesian* structure [(&, ⊤)] of [ICones] (the
    [sprod] product, the terminal [Stop]) on one side and the [⊗]
    structure [(⊗, 1)] on the other.  We need the cartesian associator,
    symmetry and unitors for [&], built from [icones_proj]/[icones_tuple]
    (their pure-point computation is definitional). *)

(** Pairing of two morphisms into a [&]-product. *)
Definition spair (Q X Y : ICone.type Ar)
    (f : icones_hom Ar Q X) (g : icones_hom Ar Q Y) :
    icones_hom Ar Q (sprod X Y) :=
  icones_tuple
    (fun b : bool =>
       if b as b0 return icones_hom Ar Q (sprod_fam X Y b0) then f else g).

Lemma spairE (Q X Y : ICone.type Ar)
    (f : icones_hom Ar Q X) (g : icones_hom Ar Q Y) (q : Q) :
  Lfun (spair f g) q = sprod_pair (Lfun f q) (Lfun g q).
Proof. by apply: cones_prod_eq => -[]. Qed.

(** *** The cartesian associator [α^& : (A & B) & C ≅ A & (B & C)]. *)
Definition sprod_assoc_fwd (A B C : ICone.type Ar) :
    icones_hom Ar (sprod (sprod A B) C) (sprod A (sprod B C)) :=
  spair (icones_comp (sproj1 A B) (sproj1 (sprod A B) C))
        (spair (icones_comp (sproj2 A B) (sproj1 (sprod A B) C))
               (sproj2 (sprod A B) C)).

Definition sprod_assoc_bwd (A B C : ICone.type Ar) :
    icones_hom Ar (sprod A (sprod B C)) (sprod (sprod A B) C) :=
  spair (spair (sproj1 A (sprod B C))
               (icones_comp (sproj1 B C) (sproj2 A (sprod B C))))
        (icones_comp (sproj2 B C) (sproj2 A (sprod B C))).

Lemma sprod_assoc_fwdK (A B C : ICone.type Ar) (p : sprod (sprod A B) C) :
  Lfun (sprod_assoc_bwd A B C) (Lfun (sprod_assoc_fwd A B C) p) = p.
Proof.
by apply: cones_prod_eq => -[] //=; apply: cones_prod_eq => -[].
Qed.

Lemma sprod_assoc_bwdK (A B C : ICone.type Ar) (p : sprod A (sprod B C)) :
  Lfun (sprod_assoc_fwd A B C) (Lfun (sprod_assoc_bwd A B C) p) = p.
Proof.
by apply: cones_prod_eq => -[] //=; apply: cones_prod_eq => -[].
Qed.

Definition sprod_assoc (A B C : ICone.type Ar) :
    icones_iso Ar (sprod (sprod A B) C) (sprod A (sprod B C)) :=
  icones_iso_of_cancel (sprod_assoc_fwd A B C) (sprod_assoc_bwd A B C)
    (@sprod_assoc_fwdK A B C) (@sprod_assoc_bwdK A B C).

(** [α^&(⟨⟨a,b⟩,c⟩) = ⟨a,⟨b,c⟩⟩]. *)
Lemma sprod_assocE (A B C : ICone.type Ar) (a : A) (b : B) (c : C) :
  Lfun (iso_fwd (sprod_assoc A B C)) (sprod_pair (sprod_pair a b) c) =
  sprod_pair a (sprod_pair b c).
Proof.
by apply: cones_prod_eq => -[] //=; apply: cones_prod_eq => -[].
Qed.

(** *** The cartesian symmetry [σ^& : A & B ≅ B & A]. *)
Definition sprod_braid_fwd (A B : ICone.type Ar) :
    icones_hom Ar (sprod A B) (sprod B A) :=
  spair (sproj2 A B) (sproj1 A B).

Lemma sprod_braid_fwdK (A B : ICone.type Ar) (p : sprod A B) :
  Lfun (sprod_braid_fwd B A) (Lfun (sprod_braid_fwd A B) p) = p.
Proof. by apply: cones_prod_eq => -[]. Qed.

Definition sprod_braid (A B : ICone.type Ar) :
    icones_iso Ar (sprod A B) (sprod B A) :=
  icones_iso_of_cancel (sprod_braid_fwd A B) (sprod_braid_fwd B A)
    (@sprod_braid_fwdK A B) (@sprod_braid_fwdK B A).

(** [σ^&(⟨a,b⟩) = ⟨b,a⟩]. *)
Lemma sprod_braidE (A B : ICone.type Ar) (a : A) (b : B) :
  Lfun (iso_fwd (sprod_braid A B)) (sprod_pair a b) = sprod_pair b a.
Proof. by apply: cones_prod_eq => -[]. Qed.

(** *** The cartesian left unitor [λ^& : ⊤ & A ≅ A]. *)
Definition sprod_lunit_fwd (A : ICone.type Ar) :
    icones_hom Ar (sprod (Stop Ar) A) A := sproj2 (Stop Ar) A.

Definition sprod_lunit_bwd (A : ICone.type Ar) :
    icones_hom Ar A (sprod (Stop Ar) A) :=
  spair (Stop_mor A) (icones_id Ar A).

Lemma sprod_lunit_fwdK (A : ICone.type Ar) (p : sprod (Stop Ar) A) :
  Lfun (sprod_lunit_bwd A) (Lfun (sprod_lunit_fwd A) p) = p.
Proof. by apply: cones_prod_eq => -[] //=; exact: Stop_eq. Qed.

Lemma sprod_lunit_bwdK (A : ICone.type Ar) (a : A) :
  Lfun (sprod_lunit_fwd A) (Lfun (sprod_lunit_bwd A) a) = a.
Proof. by []. Qed.

Definition sprod_lunit (A : ICone.type Ar) :
    icones_iso Ar (sprod (Stop Ar) A) A :=
  icones_iso_of_cancel (sprod_lunit_fwd A) (sprod_lunit_bwd A)
    (@sprod_lunit_fwdK A) (@sprod_lunit_bwdK A).

(** [λ^&(⟨_,a⟩) = a]. *)
Lemma sprod_lunitE (A : ICone.type Ar) (s : Stop Ar) (a : A) :
  Lfun (iso_fwd (sprod_lunit A)) (sprod_pair s a) = a.
Proof. by []. Qed.

(** *** The cartesian right unitor [ρ^& : A & ⊤ ≅ A]. *)
Definition sprod_runit_fwd (A : ICone.type Ar) :
    icones_hom Ar (sprod A (Stop Ar)) A := sproj1 A (Stop Ar).

Definition sprod_runit_bwd (A : ICone.type Ar) :
    icones_hom Ar A (sprod A (Stop Ar)) :=
  spair (icones_id Ar A) (Stop_mor A).

Lemma sprod_runit_fwdK (A : ICone.type Ar) (p : sprod A (Stop Ar)) :
  Lfun (sprod_runit_bwd A) (Lfun (sprod_runit_fwd A) p) = p.
Proof. by apply: cones_prod_eq => -[] //=; exact: Stop_eq. Qed.

Lemma sprod_runit_bwdK (A : ICone.type Ar) (a : A) :
  Lfun (sprod_runit_fwd A) (Lfun (sprod_runit_bwd A) a) = a.
Proof. by []. Qed.

Definition sprod_runit (A : ICone.type Ar) :
    icones_iso Ar (sprod A (Stop Ar)) A :=
  icones_iso_of_cancel (sprod_runit_fwd A) (sprod_runit_bwd A)
    (@sprod_runit_fwdK A) (@sprod_runit_bwdK A).

(** [ρ^&(⟨a,_⟩) = a]. *)
Lemma sprod_runitE (A : ICone.type Ar) (a : A) (s : Stop Ar) :
  Lfun (iso_fwd (sprod_runit A)) (sprod_pair a s) = a.
Proof. by []. Qed.

(** ** The monoidal-functor coherence of [!] — Paper §9 (Melliès)

    These are the laws making [(!, Seely2, Seely0)] a SYMMETRIC MONOIDAL
    FUNCTOR from the cartesian [(ICones, &, ⊤)] to the tensor
    [(ICones, ⊗, 1)] (ref. [Mellies09], Bierman).  Each is proved by the
    paper's recipe: reduce on promoted pure tensors via
    [tens_excl_charact]/[tens_excl_charact3l] (or the mixed unit
    extensionality [tens_excl_unitL]/[tens_excl_unitR]) and compute by
    [Seely2E]/[Seely0E]/[bang_fmap_prom]/[tensor_morE] + the structural-iso
    E-laws.  The paper itself (line 7521) says they are "easy to prove" by
    Lemma [tens-excl-equal-charact]. *)

(** *** Associativity coherence — Seely2 vs the associators [α^⊗]/[α^&].

    As maps [(!A ⊗ !B) ⊗ !C → !(A & (B & C))]:
      [!(α^&) ∘ Seely2_{A&B,C} ∘ (Seely2_{A,B} ⊗ id)]
        [= Seely2_{A,B&C} ∘ (id ⊗ Seely2_{B,C}) ∘ α^⊗].
    Both sides send [(x! ⊗ y!) ⊗ z!] to [⟨x,⟨y,z⟩⟩!]. *)
Lemma seely_assoc (A B C : ICone.type Ar) :
  icones_comp (bang_fmap (iso_fwd (sprod_assoc A B C)))
    (icones_comp (iso_fwd (Seely2 (sprod A B) C))
       (tensor_mor (iso_fwd (Seely2 A B)) (icones_id Ar (Bang Ar C)))) =
  icones_comp (iso_fwd (Seely2 A (sprod B C)))
    (icones_comp (tensor_mor (icones_id Ar (Bang Ar A)) (iso_fwd (Seely2 B C)))
       (iso_fwd (tensor_assoc (Bang Ar A) (Bang Ar B) (Bang Ar C)))).
Proof.
apply: tens_excl_charact3l => x y z Hx Hy Hz.
have Hxy : cone_norm (sprod_pair x y) <= 1 by exact: sprod_pair_norm_le1.
have Hyz : cone_norm (sprod_pair y z) <= 1 by exact: sprod_pair_norm_le1.
rewrite [in LHS]/= tensor_morE (Seely2E x y Hx Hy).
have idC : Lfun (icones_id Ar (Bang Ar C)) z! = z! by [].
rewrite idC (Seely2E (sprod_pair x y) z Hxy Hz).
have Hxyz : cone_norm (sprod_pair (sprod_pair x y) z) <= 1.
  exact: sprod_pair_norm_le1.
rewrite (bang_fmap_prom (sprod_assoc_fwd A B C)
           (sprod_pair (sprod_pair x y) z) Hxyz) sprod_assocE.
rewrite [in RHS]/= tensor_assocEp tensor_morE.
have idA : Lfun (icones_id Ar (Bang Ar A)) x! = x! by [].
by rewrite idA (Seely2E y z Hy Hz) (Seely2E x (sprod_pair y z) Hx Hyz).
Qed.

(** *** Symmetry coherence — Seely2 vs the braidings [σ^⊗]/[σ^&].

    As maps [!A ⊗ !B → !(B & A)]:
      [!(σ^&) ∘ Seely2_{A,B} = Seely2_{B,A} ∘ σ^⊗].
    Both sides send [x! ⊗ y!] to [⟨y,x⟩!]. *)
Lemma seely_braid (A B : ICone.type Ar) :
  icones_comp (bang_fmap (iso_fwd (sprod_braid A B))) (iso_fwd (Seely2 A B)) =
  icones_comp (iso_fwd (Seely2 B A))
    (iso_fwd (tensor_braid (Bang Ar A) (Bang Ar B))).
Proof.
apply: tens_excl_charact => x y Hx Hy.
rewrite [in LHS]/= (Seely2E x y Hx Hy).
have Hxy : cone_norm (sprod_pair x y) <= 1 by exact: sprod_pair_norm_le1.
rewrite (bang_fmap_prom (sprod_braid_fwd A B) (sprod_pair x y) Hxy) sprod_braidE.
by rewrite [in RHS]/= tensor_braidEp (Seely2E y x Hy Hx).
Qed.

(** *** The unit point [1 ∈ 1] and the [tensor_lunit]/[tensor_runit]
    inverse on promotions, used by the unit-coherence extensionality. *)
Definition one1 : cone_one_car Ar := MkConeOne Ar 1%:nng.

Lemma lunit_bwd_prom (B : ICone.type Ar) (x : B) :
  iso_bwd (tensor_lunit (Bang Ar B)) x! = ptensor one1 x!.
Proof.
(* P6 — with [tensor_lunit] sealed [Opaque], the staged change-fold no
   longer applies; but [iso_fwd ∘ iso_bwd] cancels by [iso_can'] and the
   forward unitor on the unit-scalar pure tensor [one1 ⊗ x!] computes to
   [x!], so the residual goal closes by conversion. *)
apply: (iso_fwd_inj (tensor_lunit (Bang Ar B))).
by rewrite iso_can'.
Qed.

Lemma runit_bwd_prom (B : ICone.type Ar) (x : B) :
  iso_bwd (tensor_runit (Bang Ar B)) x! = ptensor x! one1.
Proof.
apply: (iso_fwd_inj (tensor_runit (Bang Ar B))).
by rewrite iso_can'.
Qed.

(** Mixed unit extensionality.  A linear map [1 ⊗ !B → C] is determined
    by its values on [1 ⊗ x!] (the unit scalar [1] tensored with a
    promotion): post-compose with the iso [(λ^⊗)⁻¹] (which sends [x!] to
    [1 ⊗ x!], [lunit_bwd_prom]) and discharge by the [n=1] [bang_ext]. *)
Lemma tens_excl_unitL (A C0 : ICone.type Ar)
    (f g : icones_hom Ar (tensor Ar (cone_one_car Ar) (Bang Ar A)) C0) :
  (forall x : A, cone_norm x <= 1 ->
     Lfun f (ptensor one1 x!) = Lfun g (ptensor one1 x!)) ->
  f = g.
Proof.
move=> Hfg.
have Hbwd : icones_comp f (iso_bwd (tensor_lunit (Bang Ar A))) =
            icones_comp g (iso_bwd (tensor_lunit (Bang Ar A))).
  apply: bang_ext => x Hx.
  rewrite /= -/(Lfun (iso_bwd (tensor_lunit (Bang Ar A))) x!) lunit_bwd_prom.
  exact: Hfg.
rewrite -(icones_compIr f) -(icones_compIr g).
rewrite -(iso_fwdK (tensor_lunit (Bang Ar A))).
by rewrite !icones_compA Hbwd.
Qed.

Lemma tens_excl_unitR (A C0 : ICone.type Ar)
    (f g : icones_hom Ar (tensor Ar (Bang Ar A) (cone_one_car Ar)) C0) :
  (forall x : A, cone_norm x <= 1 ->
     Lfun f (ptensor x! one1) = Lfun g (ptensor x! one1)) ->
  f = g.
Proof.
move=> Hfg.
have Hbwd : icones_comp f (iso_bwd (tensor_runit (Bang Ar A))) =
            icones_comp g (iso_bwd (tensor_runit (Bang Ar A))).
  apply: bang_ext => x Hx.
  rewrite /= -/(Lfun (iso_bwd (tensor_runit (Bang Ar A))) x!) runit_bwd_prom.
  exact: Hfg.
rewrite -(icones_compIr f) -(icones_compIr g).
rewrite -(iso_fwdK (tensor_runit (Bang Ar A))).
(* P6 — [tensor_runit_bwd] is itself an [icones_comp]; a blanket
   [!icones_compA] would reassociate INTO it (defeating the [Opaque]
   seal) and break the [Hbwd] match.  Reassociate only the two outer
   composites by giving [icones_compA] explicit arguments. *)
rewrite (icones_compA f (iso_bwd (tensor_runit (Bang Ar A)))
                       (iso_fwd (tensor_runit (Bang Ar A)))).
rewrite (icones_compA g (iso_bwd (tensor_runit (Bang Ar A)))
                       (iso_fwd (tensor_runit (Bang Ar A)))).
by rewrite Hbwd.
Qed.

(** *** Left-unit coherence — Seely0 vs the left unitors [λ^⊗]/[λ^&].

    As maps [1 ⊗ !A → !A]:
      [!(λ^&_A) ∘ Seely2_{⊤,A} ∘ (Seely0 ⊗ id) = λ^⊗_{!A}].
    Both sides send [1 ⊗ x!] to [x!] (the LHS through [Seely0(1) = 0!],
    [Seely2(0! ⊗ x!) = ⟨0,x⟩!] and [λ^&⟨0,x⟩ = x]). *)
Lemma seely_lunit (A : ICone.type Ar) :
  icones_comp (bang_fmap (iso_fwd (sprod_lunit A)))
    (icones_comp (iso_fwd (Seely2 (Stop Ar) A))
       (tensor_mor (iso_fwd Seely0) (icones_id Ar (Bang Ar A)))) =
  iso_fwd (tensor_lunit (Bang Ar A)).
Proof.
apply: tens_excl_unitL => x Hx.
have H0 : cone_norm (precone_zero : Stop Ar) <= 1 by rewrite cone_norm0.
rewrite [in LHS]/= tensor_morE (Seely0E one1).
have e1 : c1_val one1 = 1%:nng by [].
rewrite e1 precone_scale_1.
have idA : Lfun (icones_id Ar (Bang Ar A)) x! = x! by [].
rewrite idA (Seely2E (precone_zero : Stop Ar) x H0 Hx).
have Hp : cone_norm (sprod_pair (precone_zero : Stop Ar) x) <= 1.
  exact: sprod_pair_norm_le1.
rewrite (bang_fmap_prom (sprod_lunit_fwd A)
           (sprod_pair (precone_zero : Stop Ar) x) Hp) sprod_lunitE.
by rewrite tensor_lunitEp e1 precone_scale_1.
Qed.

(** *** Right-unit coherence — Seely0 vs the right unitors [ρ^⊗]/[ρ^&].

    As maps [!A ⊗ 1 → !A]:
      [!(ρ^&_A) ∘ Seely2_{A,⊤} ∘ (id ⊗ Seely0) = ρ^⊗_{!A}].
    Both sides send [x! ⊗ 1] to [x!]. *)
Lemma seely_runit (A : ICone.type Ar) :
  icones_comp (bang_fmap (iso_fwd (sprod_runit A)))
    (icones_comp (iso_fwd (Seely2 A (Stop Ar)))
       (tensor_mor (icones_id Ar (Bang Ar A)) (iso_fwd Seely0))) =
  iso_fwd (tensor_runit (Bang Ar A)).
Proof.
apply: tens_excl_unitR => x Hx.
have H0 : cone_norm (precone_zero : Stop Ar) <= 1 by rewrite cone_norm0.
rewrite [in LHS]/= tensor_morE (Seely0E one1).
have e1 : c1_val one1 = 1%:nng by [].
rewrite e1 precone_scale_1.
have idA : Lfun (icones_id Ar (Bang Ar A)) x! = x! by [].
rewrite idA (Seely2E x (precone_zero : Stop Ar) Hx H0).
have Hp : cone_norm (sprod_pair x (precone_zero : Stop Ar)) <= 1.
  exact: sprod_pair_norm_le1.
rewrite (bang_fmap_prom (sprod_runit_fwd A)
           (sprod_pair x (precone_zero : Stop Ar)) Hp) sprod_runitE.
by rewrite tensor_runitEp e1 precone_scale_1.
Qed.

(** ** Comonad-vs-monoidal compatibility — the counit [der] (Paper §9)

    Complementing [seely_comult] (the comultiplication [dig] vs [Seely2]),
    these record the counit [der]'s compatibility with the Seely isos.

    *** Counit/unit coherence: [der_⊤ ∘ Seely0 = !] (the unique [1 → ⊤]).
    Immediate from terminality of [⊤] ([Stop_mor_unique]). *)
Lemma seely_der_unit :
  icones_comp (der (Stop Ar)) (iso_fwd Seely0) = Stop_mor (cone_one_car Ar).
Proof. exact: Stop_mor_unique. Qed.

(** *** Counit/Seely2 binary coherence, in projected form.  The product
    [A & B] is determined by its two projections, so the counit-square
    [der_{A&B} ∘ Seely2_{A,B} : !A ⊗ !B → A & B] is pinned down by its two
    [&]-projections, each of which is the naturality of [der] ([der_nat])
    transported across [Seely2]: [πᵢ ∘ der_{A&B} ∘ Seely2 = derᵢ ∘ !πᵢ ∘
    Seely2].  (Both send [x! ⊗ y!] to [x] resp. [y].) *)
Lemma seely_der1 (A B : ICone.type Ar) :
  icones_comp (sproj1 A B)
    (icones_comp (der (sprod A B)) (iso_fwd (Seely2 A B))) =
  icones_comp (der A)
    (icones_comp (bang_fmap (sproj1 A B)) (iso_fwd (Seely2 A B))).
Proof. by rewrite icones_compA (der_nat (sproj1 A B)) -icones_compA. Qed.

Lemma seely_der2 (A B : ICone.type Ar) :
  icones_comp (sproj2 A B)
    (icones_comp (der (sprod A B)) (iso_fwd (Seely2 A B))) =
  icones_comp (der B)
    (icones_comp (bang_fmap (sproj2 A B)) (iso_fwd (Seely2 A B))).
Proof. by rewrite icones_compA (der_nat (sproj2 A B)) -icones_compA. Qed.

End Seely.

Arguments linhom_icones {R Ar C D} phi Hphi.
Arguments linhom_iconesE {R Ar C D} phi Hphi x.
Arguments lin_natural {R Ar B C D} g f.
Arguments Theta_comp {R Ar B C D} g h.
Arguments cs {R Ar C} c Hc.
Arguments csE {R Ar C} c Hc x.
Arguments psi0 {R Ar C} f.
Arguments psiV0 {R Ar C} g.
Arguments Seely0 {R Ar}.
Arguments Seely0E {R Ar}.
Arguments bang_ext_linhom {R Ar B C} phi psi Hphi Hpsi.
Arguments tens_excl_charact {R Ar B1 B2 C} f g.
Arguments tens_excl_charact3 {R Ar A B C C0} f g.
Arguments tens_excl_charact3l {R Ar A B C C0} f g.
Arguments sproj1 {R Ar} B1 B2.
Arguments sproj2 {R Ar} B1 B2.
Arguments bang_proj_tuple {R Ar} B1 B2.
Arguments seely_comult {R Ar} B1 B2.
Arguments spair {R Ar Q X Y}.
Arguments spairE {R Ar Q X Y}.
Arguments sprod_assoc {R Ar} A B C.
Arguments sprod_assocE {R Ar A B C}.
Arguments sprod_braid {R Ar} A B.
Arguments sprod_braidE {R Ar A B}.
Arguments sprod_lunit {R Ar} A.
Arguments sprod_lunitE {R Ar A}.
Arguments sprod_runit {R Ar} A.
Arguments sprod_runitE {R Ar A}.
Arguments one1 {R Ar}.
Arguments tens_excl_unitL {R Ar A C0} f g.
Arguments tens_excl_unitR {R Ar A C0} f g.
Arguments seely_assoc {R Ar} A B C.
Arguments seely_braid {R Ar} A B.
Arguments seely_lunit {R Ar} A.
Arguments seely_runit {R Ar} A.
Arguments seely_der_unit {R Ar}.
Arguments seely_der1 {R Ar} A B.
Arguments seely_der2 {R Ar} A B.

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
    - [sc_seely2]/[sc_seely2E]/[sc_seely2_nat] : the binary Seely iso
      [!A ⊗ !B ≅ !(A & B)], its characterisation on promoted pure tensors
      and its naturality (the staged Yoneda data);
    - [sc_seely0]/[sc_seely0E] : the unit Seely iso [1 ≅ !⊤] (with [⊤] the
      terminal cone [Stop]) and its characterisation [Seely0(t) = t·0!];
    - [sc_assoc]/[sc_braid]/[sc_lunit]/[sc_runit] : the four
      symmetric-monoidal-functor coherence squares of [(!, Seely2, Seely0)]
      against the cartesian [(&, ⊤)] and the tensor [(⊗, 1)] structural
      isos (associator/symmetry/unitors), DERIVED via
      [tens_excl_charact3l]/[tens_excl_charact]/[tens_excl_unitL/R];
    - [sc_comult] : the comultiplication coherence (paper lines 7527–7573),
      the [dig] vs [Seely2] Melliès law, DERIVED via [tens_excl_charact];
    - [sc_der_unit]/[sc_der1]/[sc_der2] : the counit [der] compatibility —
      the counit/unit law [der_⊤ ∘ Seely0 = !] and the projected
      counit/[Seely2] binary laws.

    The canonical witness [ICones_Seely] populates every field with the
    proved lemmas; the tensor symbols are now AXIOM-FREE (SAFT
    discharged), so the only unproved inputs left are the staged exp /
    Seely symbols (PLAN §13).

    Status of the Melliès coherence laws.  We DELIVER, as THEOREMS modulo
    the staged interfaces (not axioms): the strong-monoidal-comonad data
    ([!], [⊗], [&], [⊤], [Seely2], [Seely0]); the binary Seely iso, its
    naturality and characterisation; the unit Seely iso and its
    characterisation; the FULL symmetric-monoidal-functor coherence of
    [(!, Seely2, Seely0)] — associativity, symmetry, left/right unit; the
    comultiplication ([dig]) coherence the paper draws explicitly (line
    7527); and the counit ([der]) compatibility laws.  Every coherence is
    proved by the paper's recipe — reduce on promoted pure tensors via
    [tens_excl_charact]/[tens_excl_charact3l] (or the mixed unit
    extensionality), compute by [Seely2E]/[Seely0E]/[bang_fmap_prom]/
    [tensor_morE] + the structural-iso E-laws — exactly the "easy by Lemma
    [tens-excl-equal-charact]" of paper line 7521.

    The binary counit/[Seely2] square [der_{A&B} ∘ Seely2_{A,B}] is
    recorded only in its PROJECTED form ([sc_der1]/[sc_der2]): the product
    [A & B] is determined by its projections, and each projection of that
    square is the dereliction naturality [der_nat] transported across
    [Seely2].  A single un-projected morphism equation between [!A ⊗ !B]
    and [A & B] is not stated, since [&] and [⊗] differ and there is no
    canonical comparison [A & B ↔ A ⊗ B] to phrase it through; the two
    projections jointly carry the same content. *)

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
  (* the unit Seely iso [1 ≅ !⊤], with [⊤ = Stop Ar] the terminal cone *)
  sc_seely0 : icones_iso Ar (cone_one_car Ar) (Bang Ar (Stop Ar));
  (* its characterisation [Seely0(t) = t·(0!)] (paper line 7508) *)
  sc_seely0E : forall t : cone_one_car Ar,
    iso_fwd sc_seely0 t =
    precone_scale (c1_val t) (prom (precone_zero : Stop Ar));
  (* SYMMETRIC MONOIDAL FUNCTOR coherence of [(!, Seely2, Seely0)]
     (Melliès; ref. [Mellies09]) — associativity, symmetry, unitors *)
  sc_assoc : forall A B C : ICone.type Ar,
    icones_comp (bang_fmap (iso_fwd (sprod_assoc A B C)))
      (icones_comp (iso_fwd (sc_seely2 (sprod A B) C))
         (tensor_mor (iso_fwd (sc_seely2 A B)) (icones_id Ar (Bang Ar C)))) =
    icones_comp (iso_fwd (sc_seely2 A (sprod B C)))
      (icones_comp
         (tensor_mor (icones_id Ar (Bang Ar A)) (iso_fwd (sc_seely2 B C)))
         (iso_fwd (tensor_assoc (Bang Ar A) (Bang Ar B) (Bang Ar C))));
  sc_braid : forall A B : ICone.type Ar,
    icones_comp (bang_fmap (iso_fwd (sprod_braid A B)))
                (iso_fwd (sc_seely2 A B)) =
    icones_comp (iso_fwd (sc_seely2 B A))
                (iso_fwd (tensor_braid (Bang Ar A) (Bang Ar B)));
  sc_lunit : forall A : ICone.type Ar,
    icones_comp (bang_fmap (iso_fwd (sprod_lunit A)))
      (icones_comp (iso_fwd (sc_seely2 (Stop Ar) A))
         (tensor_mor (iso_fwd sc_seely0) (icones_id Ar (Bang Ar A)))) =
    iso_fwd (tensor_lunit (Bang Ar A));
  sc_runit : forall A : ICone.type Ar,
    icones_comp (bang_fmap (iso_fwd (sprod_runit A)))
      (icones_comp (iso_fwd (sc_seely2 A (Stop Ar)))
         (tensor_mor (icones_id Ar (Bang Ar A)) (iso_fwd sc_seely0))) =
    iso_fwd (tensor_runit (Bang Ar A));
  (* comultiplication coherence (paper lines 7527–7573), DERIVED *)
  sc_comult : forall B1 B2 : ICone.type Ar,
    icones_comp (bang_fmap (bang_proj_tuple B1 B2))
      (icones_comp (dig (sprod B1 B2)) (iso_fwd (sc_seely2 B1 B2))) =
    icones_comp (iso_fwd (sc_seely2 (Bang Ar B1) (Bang Ar B2)))
      (tensor_mor (dig B1) (dig B2));
  (* counit [der] compatibility (complements [sc_comult]) *)
  sc_der_unit :
    icones_comp (der (Stop Ar)) (iso_fwd sc_seely0) =
    Stop_mor (cone_one_car Ar);
  sc_der1 : forall A B : ICone.type Ar,
    icones_comp (sproj1 A B)
      (icones_comp (der (sprod A B)) (iso_fwd (sc_seely2 A B))) =
    icones_comp (der A)
      (icones_comp (bang_fmap (sproj1 A B)) (iso_fwd (sc_seely2 A B)));
  sc_der2 : forall A B : ICone.type Ar,
    icones_comp (sproj2 A B)
      (icones_comp (der (sprod A B)) (iso_fwd (sc_seely2 A B))) =
    icones_comp (der B)
      (icones_comp (bang_fmap (sproj2 A B)) (iso_fwd (sc_seely2 A B)));
}.

Arguments SeelyCategory {R} Ar.

(** Paper §9: the canonical Seely-category structure on [ICones], every
    field populated by a proved lemma (the tensor is now axiom-free;
    modulo the remaining staged exp / Seely interfaces). *)
Definition ICones_Seely (R : realType) (Ar : MeasSubcat R) :
    SeelyCategory Ar :=
  {| sc_smcc := ICones_smcc Ar;
     sc_comonad := Bang_comonad Ar;
     sc_bangE := erefl;
     sc_tensorE := fun _ _ => erefl;
     sc_seely2 := @Seely2 R Ar;
     sc_seely2E := @Seely2E R Ar;
     sc_seely2_nat := @Seely2_natural R Ar;
     sc_seely0 := @Seely0 R Ar;
     sc_seely0E := @Seely0E R Ar;
     sc_assoc := @seely_assoc R Ar;
     sc_braid := @seely_braid R Ar;
     sc_lunit := @seely_lunit R Ar;
     sc_runit := @seely_runit R Ar;
     sc_comult := @seely_comult R Ar;
     sc_der_unit := @seely_der_unit R Ar;
     sc_der1 := @seely_der1 R Ar;
     sc_der2 := @seely_der2 R Ar |}.
