(**md**************************************************************)
(** * Total monotonicity and the precone of stable maps — Paper §7.2

    This file opens the §7 "stable functions" track (file S7b).  The
    *local cone* of §7.1 is delivered in [stable/local_cone.v]; here we
    formalise the §7.2 predicates that single out the morphisms of the
    sought cartesian-closed category — *totally monotonic*, *stable*,
    and *measurable stable* functions — together with the closure
    lemmas that make up Lemma 7.11.

    Paper reference: §7.2 (pages 1:56–1:58), Definitions 7.5, 7.7,
    7.10 and Lemma 7.11.

    Coverage in this file.
    - The sign-split power sets [Pneg n] / [Ppos n] over ['I_n]
      (paper, txt ~3211), with [Ppos_setT] ([{1..n} ∈ P⁺(n)]) and the
      complementarity fact [in_Pneg_Ppos].
    - The short alias [\sumP_(...)] for the cone sums
      [\big[precone_add/precone_zero]_(...)] used in (7.1).  (The
      [Monoid.com_law] instance for [precone_add] / [precone_zero] that
      makes those [bigop]s usable is declared in the cones layer,
      [cones/omega_general.v].)
    - [is_totmono] (Def 7.5, eq 7.1), with the sanity reformulations
      [totmono_increasing] (n = 1 ⇔ increasing) and [totmono2] /
      [totmono2E] (n = 2).
    - [is_stable] (Def 7.7): totally monotonic, bounded, ω-continuous,
      where ω-continuity is now Scott-continuity on the domain [B_P]
      ([is_scott_continuous_unit]: unit-ball INPUT chain, general image
      radius [Mf]) — the [M = 1] instance of [is_scott_continuous]
      ([cones/omega_general.v]).  This image-radius generality is what
      unblocks the nonlinear scaling closure [stable_scale].
    - [is_meas_stable] (Def 7.10): stable and measurable-path
      preserving on the unit ball.
    - Lemma 7.11 closure lemmas: the zero map, the pointwise sum
      [f + g] and the nonneg scaling [r *: f] preserve each of total
      monotonicity, stability and measurability.  [stable_scale] is
      proved via [r *: f = (r *: ·) ∘ f], [scaler_scott_continuous]
      and the radius-aware suprema of [omega_general.v].  (We deliver
      these as free-standing lemmas; the precone *record* and its HB
      tower are the job of the next file [stable/stablehom.v].)

    Design notes.
    - The cone sums of (7.1) range over the *finite* index sets
      [Pneg n] / [Ppos n] (subsets of ['I_n]) and the inner sums over
      [I : {set 'I_n}].  We use the standard mathcomp [bigop] machinery
      over [precone_add]; [big_split] / [eq_bigr] / [big1] /
      [big_morph] then discharge the closure lemmas pointwise.
    - The stability fields mirror [homs/linhom.v]: boundedness is
      [exists M, ∀ x ∈ B, ‖f x‖ ≤ M], ω-continuity is
      [is_scott_continuous_unit] (Def 2.2 on the domain [B_P]; the
      [linhom] linear maps use the unit-ball-image [is_omega_continuous],
      but nonlinear stable maps need the general image radius), and path
      preservation is [is_measurable_path]-on-[is_measurable_path],
      guarded by the pointwise unit-ball condition since [f] is only
      defined on [B_C].
    - On the input radius: a stable [f : B_P → Q] is monotone only on
      [B_P] (total monotonicity, [totmono_increasing]); the full-radius
      [is_scott_continuous f] (input chains of any radius) is therefore
      *too strong* for nonlinear closure — for an input chain leaving
      [B_P], [f ∘ u] need not be increasing and the commutation can
      fail.  We keep the input in [B_P], matching the ω-closed domain of
      Def 2.2, and let only the image radius range freely.
    - Lemma 7.12 (the induced order) is *not* delivered here: it needs
      the precone record (the addition operation of [P]) which lives in
      the next file; we note this in the closing comment. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import measurable_structure measurable_function.

Require Import Icones.prelude.nonneg_extra.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.omega_general.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.path.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(** ** Cone sums — the [\sumP_] alias

    The total-monotonicity inequality (7.1) sums values of [f] over the
    finite sets [Pneg n] / [Ppos n], and forms inner sums [∑_{i∈I} u i]
    over [I : {set 'I_n}].  The [Monoid.com_law] instance for
    [precone_add] / [precone_zero] — which makes the standard [bigop]
    lemmas ([big_split], [eq_bigr], [big1], [big_morph], [bigID],
    [big_setU1]) apply — is declared once and for all in the cones
    layer ([cones/omega_general.v], Section [PreconeComLaw]); it used
    to be declared here, and re-declaring it would only add a redundant
    canonical projection.  We keep here just the short alias
    [\sumP_(...)] for readability. *)

Notation "\sumP_ ( i <- r | C ) F" :=
  (\big[precone_add/precone_zero]_(i <- r | C) F)
  (at level 41, F at level 41, i, r at level 50,
   format "'[' \sumP_ ( i  <-  r  |  C ) '/  '  F ']'") : ring_scope.
Notation "\sumP_ ( i 'in' A ) F" :=
  (\big[precone_add/precone_zero]_(i in A) F)
  (at level 41, F at level 41, i, A at level 50,
   format "'[' \sumP_ ( i  in  A ) '/  '  F ']'") : ring_scope.

(** ** Sign-split power sets — Paper §7.2 (txt ~3211)

    For [n : nat], [Pneg n] (resp. [Ppos n]) collects the subsets
    [I ⊆ {1,…,n}] (here [I : {set 'I_n}]) such that [n − #I] is odd
    (resp. even).  In particular [{1,…,n} ∈ P⁺(n)]. *)

Section SignSplit.

Definition Pneg (n : nat) : {set {set 'I_n}} :=
  [set I in powerset [set: 'I_n] | odd (n - #|I|)].

Definition Ppos (n : nat) : {set {set 'I_n}} :=
  [set I in powerset [set: 'I_n] | ~~ odd (n - #|I|)].

(** Membership unfolds to the parity condition: every [I : {set 'I_n}]
    is a subset of [{1,…,n}], so the [powerset] guard is vacuous. *)
Lemma in_Pneg (n : nat) (I : {set 'I_n}) :
  (I \in Pneg n) = odd (n - #|I|).
Proof. by rewrite inE powersetT inE. Qed.

Lemma in_Ppos (n : nat) (I : {set 'I_n}) :
  (I \in Ppos n) = ~~ odd (n - #|I|).
Proof. by rewrite inE powersetT inE. Qed.

(** Paper §7.2: [{1,…,n} ∈ P⁺(n)] (here the full set [[set: 'I_n]]). *)
Lemma Ppos_setT (n : nat) : [set: 'I_n] \in Ppos n.
Proof. by rewrite in_Ppos cardsT card_ord subnn. Qed.

(** The two sign-split sets partition the full power set: [Ppos] is the
    complement of [Pneg] inside [powerset {1,…,n}].  We use this to
    split a [bigop] over [powerset] into its [Pneg] and [Ppos] parts. *)
Lemma in_Pneg_Ppos (n : nat) (I : {set 'I_n}) :
  (I \in Ppos n) = ~~ (I \in Pneg n).
Proof. by rewrite in_Pneg in_Ppos. Qed.

End SignSplit.

Arguments Pneg : clear implicits.
Arguments Ppos : clear implicits.

(** ** Inner cone sums and their algebra

    Helper lemmas about [∑_{i∈I} u i] and the (7.1) sums that the
    closure lemmas reuse.  All of these are pointwise consequences of
    the [bigop] morphism lemmas for the [precone_add] monoid. *)

Section ConeSumLemmas.
Variable R : realType.
Variable P : preconeType R.
Local Open Scope precone_scope.
Implicit Types (u : 'I_0 -> P).

(** A [precone]-sum of [f x + g x] splits into the sum of [f] and the
    sum of [g] — the [precone_add] instance of [big_split]. *)
Lemma sumP_add (T : finType) (A : {set T}) (f g : T -> P) :
  \big[precone_add/precone_zero]_(i in A) (f i + g i) =
  (\big[precone_add/precone_zero]_(i in A) f i)
  + (\big[precone_add/precone_zero]_(i in A) g i).
Proof. exact: big_split. Qed.

(** A scalar [r] pulls out of a [precone]-sum — [big_morph] for the
    semimodule action [r *: -]. *)
Lemma sumP_scale (T : finType) (A : {set T}) (r : {nonneg R})
  (f : T -> P) :
  r *: (\big[precone_add/precone_zero]_(i in A) f i) =
  \big[precone_add/precone_zero]_(i in A) (r *: f i).
Proof.
apply: big_morph; last exact: precone_scale_0r.
by move=> x y; exact: precone_scale_DAr.
Qed.

End ConeSumLemmas.

(** ** Def 7.5 — totally monotonic functions

    Let [P, Q] be cones.  A function [f : B_P → Q] (defined on the unit
    ball) is *totally monotonic* if for each [n], each [x : P] and each
    family [u : 'I_n → P] with [x + ∑_i u i ∈ B_P], one has

      ∑_{I ∈ P⁻(n)} f (x + ∑_{i∈I} u i)  ≤  ∑_{I ∈ P⁺(n)} f (x + ∑_{i∈I} u i)

    where [≤] is the cone order [precone_le] of [Q] and the sums use
    the cone addition [precone_add]. *)

Section TotMono.
Variable R : realType.
Variables P Q : coneType R.
Local Open Scope precone_scope.

(** The (7.1) argument for index set [I]: [x + ∑_{i∈I} u i]. *)
Definition tm_arg (n : nat) (x : P) (u : 'I_n -> P) (I : {set 'I_n}) : P :=
  x + \big[precone_add/precone_zero]_(i in I) u i.

(** Paper Def 7.5, Condition (7.1). *)
Definition is_totmono (f : P -> Q) : Prop :=
  forall (n : nat) (x : P) (u : 'I_n -> P),
    cone_norm (x + \big[precone_add/precone_zero]_(i : 'I_n) u i) <= 1 ->
    precone_le
      (\big[precone_add/precone_zero]_(I in Pneg n) f (tm_arg x u I))
      (\big[precone_add/precone_zero]_(I in Ppos n) f (tm_arg x u I)).

End TotMono.

Arguments tm_arg {R P n} x u I.
Arguments is_totmono {R P Q}.

(** ** Sanity check: [n = 1] ⇔ increasing — Paper §7.2

    For [n = 1] we have [P⁻(1) = {∅}] and [P⁺(1) = {{1}}], so (7.1)
    reads [f x ≤ f (x + u 0)], i.e. [f] is increasing on the unit
    ball. *)

Section SanityN1.
Variable R : realType.
Variables P Q : coneType R.
Local Open Scope precone_scope.

(** Every [I : {set 'I_1}] is either empty or full. *)
Lemma I1_cases (I : {set 'I_1}) : (I = finset.set0) \/ (I = [set: 'I_1]).
Proof.
have := finset.subsetT I; rewrite subEproper => /predU1P[->|]; first by right.
rewrite properEcard cardsT card_ord => /andP[_].
by rewrite ltnS leqn0 cards_eq0 => /eqP ->; left.
Qed.

(** [P⁻(1) = {∅}]: the only [I : {set 'I_1}] with [1 − #I] odd is [∅]. *)
Lemma Pneg1 : Pneg 1 = [set (finset.set0 : {set 'I_1})].
Proof.
apply/setP => I; rewrite in_Pneg !inE.
have [->|->] := I1_cases I.
  by rewrite cards0 subn0/= eqxx.
rewrite cardsT card_ord subnn/=.
by apply/esym/negbTE/eqP => /setP/(_ ord0); rewrite !inE.
Qed.

(** [P⁺(1) = {{1}}] = the full set [[set: 'I_1]]. *)
Lemma Ppos1 : Ppos 1 = [set [set: 'I_1]].
Proof.
apply/setP => I; rewrite in_Ppos !inE.
have [->|->] := I1_cases I.
  rewrite cards0 subn0/=; apply/esym/negbTE/eqP => /setP/(_ ord0).
  by rewrite !inE.
by rewrite cardsT card_ord subnn/= eqxx.
Qed.

(** Paper §7.2: for [n = 1], total monotonicity is increasingness. *)
Lemma totmono_increasing (f : P -> Q) :
  is_totmono f ->
  forall (x v : P), cone_norm (x + v) <= 1 -> precone_le (f x) (f (x + v)).
Proof.
move=> Hf x v Hxv.
have := Hf 1%N x (fun _ => v).
rewrite big_ord1 => /(_ Hxv).
rewrite Pneg1 Ppos1 !big_set1 /tm_arg.
rewrite big_set0 precone_addr0.
rewrite (eq_bigl predT) ?big_ord1//.
by move=> i; exact: finset.in_setT.
Qed.

End SanityN1.

(** ** Sanity check: [n = 2] — Paper §7.2

    For [n = 2], [P⁻(2) = {{1},{2}}] and [P⁺(2) = {{1,2}, ∅}], so (7.1)
    reads [f(x+u₀) + f(x+u₁) ≤ f(x+u₀+u₁) + f x]. *)

Section SanityN2.
Variable R : realType.
Variables P Q : coneType R.
Local Open Scope precone_scope.

(** The instance of [is_totmono] at [n = 2]: the raw (7.1) inequality
    between the two [precone]-sums over [Pneg 2] / [Ppos 2]. *)
Lemma totmono2 (f : P -> Q) :
  is_totmono f ->
  forall (x : P) (u : 'I_2 -> P),
    cone_norm (x + \big[precone_add/precone_zero]_(i : 'I_2) u i) <= 1 ->
    precone_le
      (\big[precone_add/precone_zero]_(I in Pneg 2) f (tm_arg x u I))
      (\big[precone_add/precone_zero]_(I in Ppos 2) f (tm_arg x u I)).
Proof. by move=> Hf x u; exact: Hf. Qed.

End SanityN2.

(** ** Def 7.7 — stable functions

    A function [f : B_P → Q] is *stable* if it is totally monotonic,
    bounded, and ω-continuous.  Following Def 7.7 / Def 2.2 faithfully,
    ω-continuity is *Scott*-continuity on the *domain* [B_P]: the input
    chain ranges over [B_P] (the function's domain, [‖uₙ‖ ≤ 1]) while
    its image is allowed to escape the unit ball — the supremum on the
    output side is the radius-aware [cone_sup_at] at any image radius
    [Mf], rather than the unit-ball [cone_sup_ball].  We call this
    [is_scott_continuous_unit]; it is exactly [is_scott_continuous]
    ([cones/omega_general.v]) instantiated at input radius [M = 1] (via
    [cone_sup_at_ball], which identifies [cone_sup_at] at radius [1]
    with [cone_sup_ball]).

    The *image*-side radius is general ([Mf] arbitrary), so nonneg
    scaling [r *: f] — whose image chain has norm up to [1/r > 1] for
    [r < 1] — is Scott-continuous (see [stable_scale]).  The
    unrestricted-input form [is_scott_continuous f] (all input radii)
    is too strong for *nonlinear* stable maps: a stable [f : B_P → Q]
    is only monotone on [B_P] (total monotonicity,
    [totmono_increasing]), so for an input chain leaving [B_P] the
    image chain [f ∘ u] need not be increasing and the commutation can
    fail.  Def 2.2 sidesteps this by keeping the input chain in the
    ω-closed domain [A = B_P]. *)

Section Stable.
Variable R : realType.
Variables P Q : coneType R.

(** Def 2.2 ω-continuity for a [B_P → Q] map: input chain in [B_P],
    output supremum at the (general) image radius [Mf].  Equal to
    [is_scott_continuous f] specialised to input radius [1]. *)
Definition is_scott_continuous_unit (f : P -> Q) : Prop :=
  forall (Mf : {nonneg R}) (u : nat -> P)
         (uch : forall n, precone_le (u n) (u n.+1))
         (ub1 : forall n, cone_norm (u n) <= 1)
         (fuch : forall n, precone_le (f (u n)) (f (u n.+1)))
         (fubMf : forall n, cone_norm (f (u n)) <= Mf%:num)
         (Mfpos : 0 < Mf%:num),
    f (cone_sup_ball u uch ub1) = cone_sup_at (u := f \o u) fuch fubMf Mfpos.

(** Paper Def 7.7. *)
Definition is_stable (f : P -> Q) : Prop :=
  [/\ is_totmono f,
      exists M : R, forall x : P, cone_norm x <= 1 -> cone_norm (f x) <= M
   &  is_scott_continuous_unit f].

End Stable.

Arguments is_scott_continuous_unit {R P Q}.

Arguments is_stable {R P Q}.

(** ** Def 7.10 — measurable stable functions

    Let [C, D] be measurable cones.  A stable function [f : B_C → D] is
    *measurable* if for each [X ∈ Ar] and each measurable path
    [γ : ar_carrier X → C] that stays in the unit ball [B_C]
    pointwise — i.e. [γ ∈ B Path(X, C)] — the composite [f ∘ γ] is a
    measurable path [∈ Path(X, D)].  This mirrors the path-preservation
    field of [linhom_pre]. *)

Section MeasStable.
Variable R : realType.
Variable Ar : MeasSubcat R.
Variables C D : MCone.type Ar.

(** Paper Def 7.10. *)
Definition is_meas_stable (f : C -> D) : Prop :=
  is_stable f /\
  forall (X : ar_obj Ar) (γ : ar_carrier Ar X -> C),
    (forall r, cone_norm (γ r) <= 1) ->
    is_measurable_path (Ar:=Ar) (C:=C) γ ->
    is_measurable_path (Ar:=Ar) (C:=D) (fun r => f (γ r)).

End MeasStable.

Arguments is_meas_stable {R Ar C D}.

(** ** Lemma 7.11 — closure under the pointwise operations

    The stable-and-measurable functions [C → D], with the pointwise
    algebraic operations, form a precone.  We deliver the *content* of
    Lemma 7.11: the zero map is stable and measurable, and total
    monotonicity / stability / measurability are preserved by the
    pointwise [+] and by nonneg scaling [r *: -].  (The precone record
    and its HB tower are built in [stable/stablehom.v].) *)

(** *** The zero map *)

Section ClosureZero.
Variable R : realType.
Variables P Q : coneType R.
Local Open Scope precone_scope.

Definition stm_zero : P -> Q := fun _ => precone_zero.

(** Both sums of (7.1) are [0], so the order holds reflexively. *)
Lemma totmono_zero : is_totmono stm_zero.
Proof.
move=> n x u _; rewrite /stm_zero.
rewrite big1; last by [].
rewrite [X in precone_le _ X]big1; last by [].
exact: precone_le_refl.
Qed.

Lemma stable_zero : is_stable stm_zero.
Proof.
split.
- exact: totmono_zero.
- by exists 0%R => x _; rewrite /stm_zero cone_norm0.
- move=> Mf u uch ub1 fuch fubMf Mfpos; rewrite /stm_zero.
  (* Both sides are [0]: LHS by [stm_zero]; RHS as the [cone_sup_at] of
     the constant-[0] image chain, which is [0] by antisymmetry. *)
  apply: precone_le_anti.
  + by exists (cone_sup_at fuch fubMf Mfpos); rewrite precone_add0.
  + by apply: cone_sup_at_lub => n /=; exact: precone_le_refl.
Qed.

End ClosureZero.

Arguments stm_zero {R} P Q.

Section ClosureZeroMeas.
Variable R : realType.
Variable Ar : MeasSubcat R.
Variables C D : MCone.type Ar.

Lemma meas_stable_zero : is_meas_stable (stm_zero C D).
Proof.
split; first exact: stable_zero.
by move=> X γ _ _; exact: const_path_measurable.
Qed.

End ClosureZeroMeas.

(** *** Pointwise addition *)

Section ClosureAdd.
Variable R : realType.
Variables P Q : coneType R.
Local Open Scope precone_scope.

Definition stm_add (f g : P -> Q) : P -> Q := fun x => f x + g x.

(** Total monotonicity is preserved by pointwise [+]: each of the two
    (7.1) sums for [f + g] splits ([sumP_add]) into the [f]-sum and the
    [g]-sum, and the cone order is additive ([precone_add_le_r] /
    [precone_add_le_l]). *)
Lemma totmono_add (f g : P -> Q) :
  is_totmono f -> is_totmono g -> is_totmono (stm_add f g).
Proof.
move=> Hf Hg n x u Hxu; rewrite /stm_add.
rewrite (eq_bigr (fun I => f (tm_arg x u I) + g (tm_arg x u I)))//.
rewrite [X in precone_le _ X]
  (eq_bigr (fun I => f (tm_arg x u I) + g (tm_arg x u I)))//.
rewrite !sumP_add.
apply: (@precone_le_trans _ _
  ((\big[precone_add/precone_zero]_(I in Ppos n) f (tm_arg x u I))
   + (\big[precone_add/precone_zero]_(I in Pneg n) g (tm_arg x u I)))).
- by apply: precone_add_le_r; exact: Hf.
- by apply: precone_add_le_l; exact: Hg.
Qed.

(** Boundedness is preserved by pointwise [+], with bound [M + N]. *)
Lemma bounded_add (f g : P -> Q) :
  (exists M : R, forall x, cone_norm x <= 1 -> cone_norm (f x) <= M) ->
  (exists N : R, forall x, cone_norm x <= 1 -> cone_norm (g x) <= N) ->
  exists L : R, forall x, cone_norm x <= 1 ->
    cone_norm (stm_add f g x) <= L.
Proof.
move=> [M HM] [N HN]; exists (M + N)%R => x Hx; rewrite /stm_add.
apply: le_trans; first exact: cone_normt.
by rewrite lerD//; [exact: HM | exact: HN].
Qed.

End ClosureAdd.

Arguments stm_add {R P Q}.

(** *** Diagonal-sup identity — now in [cones/omega_general.v]

    ω-continuity of the pointwise sum needs the *diagonal-sup identity*
    [sup_n (a_n + b_n) = sup_n a_n + sup_n b_n] for chains [a], [b]
    whose diagonal sum stays within the common radius.  Both the
    unit-ball and the radius-aware forms used to be re-proved here (an
    acknowledged port of the [homs/linhom.v] argument); they are now
    stated once, over a bare [coneType] and at a general radius, in
    [cones/omega_general.v] as [cone_sup_ball_addD] and
    [cone_sup_at_addD].  The radius-aware form keeps its local name
    [sup_at_addD] (it is the one the paper text cites) as a one-line
    derivation of the general statement; the unit-ball form is gone —
    use [cone_sup_ball_addD]. *)

Section DiagonalSup.
Variable R : realType.
Variable P : coneType R.
Local Open Scope precone_scope.
Implicit Types a b : nat -> P.

(** Radius-aware diagonal-sup identity: for increasing chains [a], [b]
    *and* their diagonal sum all bounded by a common radius [M > 0],
    the sup of the diagonal sum is the sum of the sups.  This is the
    radius-aware engine behind ω-continuity of the pointwise sum
    [f + g]; it is [omega_general.cone_sup_at_addD] under its local
    name. *)
Lemma sup_at_addD (M : {nonneg R}) a b
  (ach : forall n, a n <=p a n.+1)
  (aubM : forall n, cone_norm (a n) <= M%:num)
  (bch : forall n, b n <=p b n.+1)
  (bubM : forall n, cone_norm (b n) <= M%:num)
  (sch : forall n, a n + b n <=p a n.+1 + b n.+1)
  (subM : forall n, cone_norm (a n + b n) <= M%:num)
  (Mpos : (0 < M%:num)%R) :
  cone_sup_at sch subM Mpos =
  (cone_sup_at ach aubM Mpos) + (cone_sup_at bch bubM Mpos).
Proof. exact: cone_sup_at_addD. Qed.

End DiagonalSup.

(** *** Stability of [f + g]

    ω-continuity of the pointwise sum needs that each summand is an
    increasing chain on the unit ball.  For *stable* functions this is
    exactly [totmono_increasing] (the [n = 1] sanity lemma), so we
    package ω-continuity and stability of [f + g] together. *)

Section ClosureAddStable.
Variable R : realType.
Variables P Q : coneType R.
Local Open Scope precone_scope.

(** From total monotonicity we recover increasingness on the unit ball
    along an increasing unit-ball chain. *)
Let tm_chain (f : P -> Q) (Hf : is_totmono f)
    (u : nat -> P) (uch : forall n, u n <=p u n.+1)
    (ub1 : forall n, cone_norm (u n) <= 1) n :
  f (u n) <=p f (u n.+1).
Proof.
have [v Hv] := uch n.
rewrite Hv; apply: (totmono_increasing Hf).
by rewrite -Hv; exact: ub1.
Qed.

(** Stability is preserved by pointwise [+].  Total monotonicity is
    [totmono_add], boundedness is [bounded_add]; Scott-continuity
    (unit-ball input, image radius [Mf]) follows from [sup_at_addD]:
    each summand chain [f ∘ u], [g ∘ u] is increasing on [B_P] via
    [tm_chain] (the [n = 1] sanity lemma [totmono_increasing]) and
    bounded by [Mf] via (Normp).  We apply the [is_scott_continuous_unit]
    field of [f] and [g] to commute each through the unit-ball
    supremum, then [sup_at_addD] at the (possibly large) image radius
    [Mf] recombines the two image suprema. *)
Lemma stable_add (f g : P -> Q) :
  is_stable f -> is_stable g -> is_stable (stm_add f g).
Proof.
move=> [Hfm Hfb Hfc] [Hgm Hgb Hgc].
split; first exact: totmono_add.
  exact: bounded_add.
move=> Mf u uch ub1 fuch fubMf Mfpos; rewrite /stm_add.
(* Pointwise image bounds for each summand (by Normp, ≤ Mf). *)
have fubM n : cone_norm (f (u n)) <= Mf%:num.
  by apply: le_trans (fubMf n); apply: cone_normp; exists (g (u n)).
have gubM n : cone_norm (g (u n)) <= Mf%:num.
  apply: le_trans (fubMf n); apply: cone_normp.
  by exists (f (u n)); rewrite precone_addC.
(* Pointwise chains for each summand (by total monotonicity). *)
have fch n : f (u n) <=p f (u n.+1) by exact: (tm_chain Hfm uch ub1).
have gch n : g (u n) <=p g (u n.+1) by exact: (tm_chain Hgm uch ub1).
(* Scott-continuity of each summand, then the diagonal-sup identity. *)
rewrite (Hfc Mf u uch ub1 fch fubM Mfpos).
rewrite (Hgc Mf u uch ub1 gch gubM Mfpos).
symmetry.
exact: (@sup_at_addD R Q Mf (f \o u) (g \o u)
          fch fubM gch gubM fuch fubMf Mfpos).
Qed.

End ClosureAddStable.

Section ClosureAddMeas.
Variable R : realType.
Variable Ar : MeasSubcat R.
Variables C D : MCone.type Ar.
Local Open Scope precone_scope.

(** Measurability is preserved by pointwise [+]: the sum of two
    measurable paths is a measurable path ([path_add]'s underlying
    fact), so [(f+g)∘γ = f∘γ + g∘γ] is a measurable path whenever
    [f∘γ] and [g∘γ] are. *)
Lemma meas_stable_add (f g : C -> D) :
  is_meas_stable f -> is_meas_stable g -> is_meas_stable (stm_add f g).
Proof.
move=> [Hfs Hfp] [Hgs Hgp]; split; first exact: stable_add.
move=> X γ Hγ1 Hγ; rewrite /stm_add.
have Hf := Hfp X γ Hγ1 Hγ.
have Hg := Hgp X γ Hγ1 Hγ.
exact: (path_add_is_path (MkPath Hf) (MkPath Hg)).
Qed.

End ClosureAddMeas.

(** *** Nonneg scaling *)

Section ClosureScale.
Variable R : realType.
Variables P Q : coneType R.
Local Open Scope precone_scope.

Definition stm_scale (r : {nonneg R}) (f : P -> Q) : P -> Q :=
  fun x => r *: f x.

(** Total monotonicity is preserved by nonneg scaling: each (7.1) sum
    for [r *: f] factors [r] out ([sumP_scale]) and the cone order is
    preserved by scaling ([precone_scale_le]). *)
Lemma totmono_scale (r : {nonneg R}) (f : P -> Q) :
  is_totmono f -> is_totmono (stm_scale r f).
Proof.
move=> Hf n x u Hxu; rewrite /stm_scale.
rewrite (eq_bigr (fun I => r *: f (tm_arg x u I)))//.
rewrite [X in precone_le _ X](eq_bigr (fun I => r *: f (tm_arg x u I)))//.
rewrite -!sumP_scale.
by apply: precone_scale_le; exact: Hf.
Qed.

(** Boundedness is preserved by nonneg scaling, with bound [r * M]. *)
Lemma bounded_scale (r : {nonneg R}) (f : P -> Q) :
  (exists M : R, forall x, cone_norm x <= 1 -> cone_norm (f x) <= M) ->
  exists L : R, forall x, cone_norm x <= 1 ->
    cone_norm (stm_scale r f x) <= L.
Proof.
move=> [M HM]; exists (r%:num * M) => x Hx.
rewrite /stm_scale cone_normh.
have rge0 : (0%R <= r%:num) by exact: nngnum_ge0.
have [-> | rpos] := eqVneq r%:num 0%R; first by rewrite !mul0r.
by rewrite ler_pM2l ?lt_def ?rpos ?rge0//; exact: HM.
Qed.

(** *** Stability of [r *: f]

    With Scott-continuity ([is_scott_continuous_unit]) the image side
    carries a *general* radius [Mf], so although the image chain
    [r *: f∘u] in [B_Q] would force [‖f(uₙ)‖ ≤ 1/r] (escaping [B_Q]
    for [r < 1]) under a unit-ball-restricted ω-continuity, the
    Scott form lets the chain escape harmlessly.  We write
    [r *: f = (r *: ·) ∘ f] and chain: [f] commutes with the unit-ball
    sup at image radius [Mf'] (its [is_scott_continuous_unit] field,
    with [f ∘ u] increasing by total monotonicity and bounded by the
    [is_stable] witness), and then the *linear* [r *: ·] commutes with
    [cone_sup_at] at any radius ([scaler_scott_continuous],
    [omega_general.v]). *)
Lemma stable_scale (r : {nonneg R}) (f : P -> Q) :
  is_stable f -> is_stable (stm_scale r f).
Proof.
move=> [Hfm Hfb Hfc]; split; first exact: totmono_scale.
  exact: bounded_scale.
have [M0 HM0] := Hfb.
(* A strictly-positive image radius bounding [f] on [B_P]. *)
have Mf'ge0 : (0 <= Num.max M0 1)%R by rewrite le_max ler01 orbT.
pose Mf' : {nonneg R} := NngNum Mf'ge0.
have Mf'pos : (0 < Mf'%:num)%R by rewrite /= lt_max ltr01 orbT.
move=> Mf u uch ub1 fuch fubMf Mfpos; rewrite /stm_scale.
(* [f ∘ u] is increasing on [B_P] (total monotonicity) … *)
have fch n : f (u n) <=p f (u n.+1).
  have [v Hv] := uch n; rewrite Hv.
  by apply: (totmono_increasing Hfm); rewrite -Hv; exact: ub1.
(* … and bounded by [Mf'] (the [is_stable] witness, on [B_P]). *)
have fubM n : cone_norm (f (u n)) <= Mf'%:num.
  by apply: le_trans (HM0 _ (ub1 n)) _; rewrite /= le_max lexx.
(* [f] commutes with the unit-ball sup at image radius [Mf']. *)
rewrite (Hfc Mf' u uch ub1 fch fubM Mf'pos).
(* The linear [r *: ·] commutes with [cone_sup_at] (any radius). *)
have rfch n : r *: (f \o u) n <=p r *: (f \o u) n.+1.
  by apply: precone_scale_le; exact: fch.
rewrite (scaler_scott_continuous r Mf' Mf (f \o u) fch fubM Mf'pos rfch
           fubMf Mfpos).
by congr cone_sup_at; exact: Prop_irrelevance.
Qed.

End ClosureScale.

Arguments stm_scale {R P Q}.

Section ClosureScaleMeas.
Variable R : realType.
Variable Ar : MeasSubcat R.
Variables C D : MCone.type Ar.
Local Open Scope precone_scope.

(** Measurability is preserved by nonneg scaling: [(r *: f)∘γ =
    r *: (f∘γ)] is a measurable path whenever [f∘γ] is
    ([path_scale_is_path]). *)
Lemma meas_stable_scale (r : {nonneg R}) (f : C -> D) :
  (forall (X : ar_obj Ar) (γ : ar_carrier Ar X -> C),
     (forall s, cone_norm (γ s) <= 1) ->
     is_measurable_path (Ar:=Ar) (C:=C) γ ->
     is_measurable_path (Ar:=Ar) (C:=D) (fun s => f (γ s))) ->
  forall (X : ar_obj Ar) (γ : ar_carrier Ar X -> C),
    (forall s, cone_norm (γ s) <= 1) ->
    is_measurable_path (Ar:=Ar) (C:=C) γ ->
    is_measurable_path (Ar:=Ar) (C:=D) (fun s => stm_scale r f (γ s)).
Proof.
move=> Hfp X γ Hγ1 Hγ; rewrite /stm_scale.
have Hf := Hfp X γ Hγ1 Hγ.
exact: (path_scale_is_path r (MkPath Hf)).
Qed.

End ClosureScaleMeas.
