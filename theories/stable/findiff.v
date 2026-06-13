(**md**************************************************************)
(** * Finite differences on totally monotonic functions — Paper §7.3

    This file opens the §7.3 "finite differences" track.  Following the
    paper, we introduce the difference operators [Δ⁺ f u⃗], [Δ⁻ f u⃗] and
    [Δ f u⃗] on a function [f : B_B → C], the inductive predicate
    [is_n_increasing] (Definition 7.15), and the basic recurrences
    (Lemmas 7.4, 7.16, 7.17) that drive the inductive characterisation
    of total monotonicity.

    Paper reference: §7.3 (pages 1:59–1:62), Lemma 7.4, Definition 7.15,
    Lemmas 7.16 and 7.17.

    Foundations reused.
    - [stable/local_cone.v]: the local cone [B_x := local_cone x] of [B]
      at an interior point [x] (a full [coneType] via [lc_coneType Hx]
      when [‖x‖ < 1]), with inclusion [lc_val : local_cone x → B], the
      homomorphism rewrites [lc_val0]/[lc_valD]/[lc_valZ], the order
      coincidence [lc_leE], the cancellation [lc_addxle] and the
      unit-ball bridge [lc_step1].
    - [stable/totmono.v]: the sign-split power sets [Pneg n] / [Ppos n]
      over ['I_n] (parity of [n − #I]), the cone-sum big-op [\sumP], the
      [is_totmono] predicate with the [n = 1] sanity lemma
      [totmono_increasing], and the lemmas [Pneg1] / [Ppos1].
    - [cones/precone.v], [cones/cone.v]: [precone_add]/[precone_le]/
      [precone_cancel], the order lemmas and [cone_norm].

    Design notes — the changing source cone.
    - The difference operators map *into* a nested local cone:
      [Δε f u⃗ : B_u⃗ → C] where [B_u⃗ := local_cone (\sumP_i u i)].  We
      keep the underlying cone [B] a *section parameter* and represent a
      point of [B_u⃗] by its [B]-value through [lc_val]; the paper's
      [f (x + Σ_{i∈I} uᵢ)] is then [f (lc_val x + \sumP_(i∈I) u i)],
      a value of [f] at a point of [B].  Because the operators are
      defined purely in terms of [lc_val] and the [B]-sum, their *type*
      [local_cone (\sumP_i u i) → C] makes sense for any family
      [u : 'I_n → B] (the bare [local_cone] type needs no [‖·‖ < 1]
      hypothesis; only its [coneType] instance does).
    - [is_n_increasing] (Definition 7.15) is a [Fixpoint] on [n] with the
      source cone [B] kept as a parameter, so that the recursive call on
      [Δ f u : local_cone u → C] typechecks with source [local_cone u].
      The "increasing" base predicate is monotonicity for [precone_le]
      on the unit ball [B_B]. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference archimedean.

Require Import Icones.prelude.classical_extra.
Require Import Icones.prelude.nonneg_extra.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.omega_general.
Require Import Icones.stable.local_cone.
Require Import Icones.stable.totmono.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Import archimedean.Num.Theory.

Local Open Scope ring_scope.

(** ** Lemma 7.4 — the [injj] reindexing — Paper §7.3 (txt ~3214)

    Fix [j ∈ {1,…,n+1}].  The paper's [injj] maps a subset
    [I ⊆ {1,…,n}] to [{i ∈ I | i < j} ∪ {j} ∪ {i+1 | i ∈ I, i ≥ j}],
    a subset of [{1,…,n+1}] containing [j], and establishes a bijection
    between [Pε(n)] and [{J ∈ Pε(n+1) | j ∈ J}].

    We only ever use the case [j = 1] (the head of the list [u :: u⃗] in
    the recurrence of Lemma 7.17), and in our ['I_n] encoding [j] is the
    first index [ord0].  We deliver the two reindexing facts we need in
    that case, packaged as [finset] equalities so that [big_imset]
    discharges the corresponding [\sumP] reindexings:

    - the "[ord0 ∈ I]" half: [I ↦ ord0 |: (lift ord0 @: J)] is the
      [j = 1] instance of [injj] and bijects [Pε(n)] with
      [{I ∈ Pε(n+1) | ord0 ∈ I}] — *same* sign [ε];
    - the "[ord0 ∉ I]" half: [I ↦ lift ord0 @: J] bijects [Pε(n)] with
      [{I ∈ P^{-ε}(n+1) | ord0 ∉ I}] — *opposite* sign (this is the
      part of the [Pε(n+1)] sum that does not see the head). *)

Section InjReindex.
Variable n : nat.

(** The "[ord0 ∉ I]" embedding ['I_n ↪ 'I_{n+1}] lifted to subsets. *)
Definition injI (J : {set 'I_n}) : {set 'I_n.+1} :=
  [set lift ord0 i | i in J].

(** The "[ord0 ∈ I]" embedding: add the head index [ord0]. *)
Definition injI0 (J : {set 'I_n}) : {set 'I_n.+1} := ord0 |: injI J.

(** [ord0] never lies in the image of [lift ord0]. *)
Lemma ord0_notin_injI (J : {set 'I_n}) : ord0 \notin injI J.
Proof.
apply/negP => /imsetP[i _ /eqP].
by move=> /eqP H; move: (neq_lift ord0 i); rewrite -H eqxx.
Qed.

Lemma card_injI (J : {set 'I_n}) : #|injI J| = #|J|.
Proof. by rewrite card_imset//; exact: lift_inj. Qed.

Lemma card_injI0 (J : {set 'I_n}) : #|injI0 J| = (#|J|).+1.
Proof. by rewrite /injI0 cardsU1 ord0_notin_injI card_injI. Qed.

(** [#|J| ≤ n] for every [J : {set 'I_n}] — the parity bookkeeping. *)
Lemma card_leq (J : {set 'I_n}) : (#|J| <= n)%N.
Proof. by apply: leq_trans (max_card _) _; rewrite card_ord. Qed.

(** Parity of [injI0]: same sign as [J] (the [ord0 ∈ I] half). *)
Lemma injI0_Pneg (J : {set 'I_n}) :
  (injI0 J \in Pneg n.+1) = (J \in Pneg n).
Proof. by rewrite !in_Pneg card_injI0 subSS. Qed.

Lemma injI0_Ppos (J : {set 'I_n}) :
  (injI0 J \in Ppos n.+1) = (J \in Ppos n).
Proof. by rewrite !in_Ppos card_injI0 subSS. Qed.

(** Parity of [injI]: opposite sign to [J] (the [ord0 ∉ I] half). *)
Lemma injI_Pneg (J : {set 'I_n}) :
  (injI J \in Pneg n.+1) = (J \in Ppos n).
Proof. by rewrite in_Pneg in_Ppos card_injI subSn ?card_leq. Qed.

Lemma injI_Ppos (J : {set 'I_n}) :
  (injI J \in Ppos n.+1) = (J \in Pneg n).
Proof.
rewrite in_Ppos in_Pneg card_injI subSn ?card_leq//.
by rewrite oddS negbK.
Qed.

(** The "section" map [{set 'I_{n+1}} → {set 'I_n}]: keep the indices
    that are [lift ord0]-images.  It inverts [injI] / [injI0] on their
    respective domains. *)
Definition projI (I : {set 'I_n.+1}) : {set 'I_n} :=
  [set j : 'I_n | lift ord0 j \in I].

Lemma projI_injI (J : {set 'I_n}) : projI (injI J) = J.
Proof.
apply/setP => j; rewrite inE.
by rewrite (mem_imset _ _ lift_inj).
Qed.

Lemma projI_injI0 (J : {set 'I_n}) : projI (injI0 J) = J.
Proof.
apply/setP => j; rewrite inE /injI0 inE (mem_imset _ _ lift_inj).
by rewrite inE eq_sym (negbTE (neq_lift _ _)).
Qed.

(** Surjectivity onto the two halves.  When [ord0 ∉ I], reconstruct [I]
    from its [lift ord0]-section. *)
Lemma injI_projI (I : {set 'I_n.+1}) :
  ord0 \notin I -> injI (projI I) = I.
Proof.
move=> I0; apply/setP => i; apply/imsetP/idP => [[j]|iI].
  by rewrite inE => jI ->.
have ino : ord0 != i by apply: contraNneq I0 => ->.
case: (unlift_some ino) => j ji _.
by exists j; rewrite ?inE -?ji.
Qed.

(** When [ord0 ∈ I], reconstruct [I] as [injI0] of its section. *)
Lemma injI0_projI (I : {set 'I_n.+1}) :
  ord0 \in I -> injI0 (projI I) = I.
Proof.
move=> I0; apply/setP => i; rewrite /injI0 inE.
apply/orP/idP => [[|]|iI].
- by rewrite inE => /eqP ->.
- by move=> /imsetP[j]; rewrite inE => jI ->.
- have [->|ino] := eqVneq i ord0; first by left; rewrite inE.
  right; apply/imsetP; have ino' : ord0 != i by rewrite eq_sym.
  case: (unlift_some ino') => j ji _.
  by exists j; rewrite ?inE -?ji.
Qed.

(** Lemma 7.4 (the two [j = 1] reindexings as [finset] equalities). *)
Lemma Ppos_split_in :
  [set I in Ppos n.+1 | ord0 \in I] = [set injI0 J | J in Ppos n].
Proof.
apply/setP => I; rewrite inE.
apply/andP/imsetP => [[IP I0]|[J JP ->]].
  by exists (projI I); rewrite ?injI0_projI// -injI0_Ppos injI0_projI.
by rewrite injI0_Ppos JP /injI0 !inE eqxx.
Qed.

Lemma Pneg_split_in :
  [set I in Pneg n.+1 | ord0 \in I] = [set injI0 J | J in Pneg n].
Proof.
apply/setP => I; rewrite inE.
apply/andP/imsetP => [[IP I0]|[J JP ->]].
  by exists (projI I); rewrite ?injI0_projI// -injI0_Pneg injI0_projI.
by rewrite injI0_Pneg JP /injI0 !inE eqxx.
Qed.

Lemma Ppos_split_out :
  [set I in Ppos n.+1 | ord0 \notin I] = [set injI J | J in Pneg n].
Proof.
apply/setP => I; rewrite inE.
apply/andP/imsetP => [[IP I0]|[J JP ->]].
  by exists (projI I); rewrite ?injI_projI// -injI_Ppos injI_projI.
by rewrite injI_Ppos JP ord0_notin_injI.
Qed.

Lemma Pneg_split_out :
  [set I in Pneg n.+1 | ord0 \notin I] = [set injI J | J in Ppos n].
Proof.
apply/setP => I; rewrite inE.
apply/andP/imsetP => [[IP I0]|[J JP ->]].
  by exists (projI I); rewrite ?injI_projI// -injI_Pneg injI_projI.
by rewrite injI_Pneg JP ord0_notin_injI.
Qed.

End InjReindex.

Arguments injI {n} J.
Arguments injI0 {n} J.

(** ** The difference operators [Δ⁺], [Δ⁻], [Δ] — Paper §7.3 (txt ~3434)

    Fix cones [B], [C] and a function [f : B → C].  Given [n] and a
    family [u : 'I_n → B], the operators map a point [x] of the local
    cone [B_u⃗ = local_cone (\sumP_i u i)] to a value of [C]:

      [Δε f u⃗ : B_u⃗ → C],  [x ↦ \sumP_(I ∈ Pε(n)) f (lc_val x + \sumP_(i∈I) u i)]

    and [Δ f u⃗ := Δ⁺f u⃗ ⊖ Δ⁻f u⃗], the pointwise cone difference, which is
    well defined where [Δ⁻ ≤ Δ⁺] (in particular on [B_u⃗] when [f] is
    totally monotonic, see [Delta_neg_le_pos]).

    The raw sums [Δ⁺], [Δ⁻] are total functions of [x] — no hypothesis on
    [‖\sumP_i u i‖] is needed for the *type* [B_u⃗ → C], since the bare
    [local_cone] carrier is a [Type] for any centre.  The difference
    [Δ f u⃗] is made total by a [pselect] guard ([Delta]); off the region
    where [Δ⁻ ≤ Δ⁺] it collapses to [0] (the canonical 0-extension used
    throughout the development, e.g. [shd_fun] in [stable/stablehom.v]).
    Its defining equation [Delta_E] is available wherever the order
    [Δ⁻ ≤ Δ⁺] holds. *)

Section Delta.
Variable R : realType.
Variables B C : coneType R.
Variable f : B -> C.
Local Open Scope precone_scope.

(** The argument [lc_val x + \sumP_(i∈I) u i] of [f] for the index set
    [I] — the paper's [x + Σ_{i∈I} uᵢ] read on a point of [B_u⃗]. *)
Definition Delta_arg (n : nat) (u : 'I_n -> B)
    (x : local_cone (\big[precone_add/precone_zero]_(i : 'I_n) u i))
    (I : {set 'I_n}) : B :=
  lc_val x + \big[precone_add/precone_zero]_(i in I) u i.

(** [Δ⁺ f u⃗] — sum over [Ppos n]. *)
Definition Delta_pos (n : nat) (u : 'I_n -> B)
    (x : local_cone (\big[precone_add/precone_zero]_(i : 'I_n) u i)) : C :=
  \big[precone_add/precone_zero]_(I in Ppos n) f (@Delta_arg n u x I).

(** [Δ⁻ f u⃗] — sum over [Pneg n]. *)
Definition Delta_neg (n : nat) (u : 'I_n -> B)
    (x : local_cone (\big[precone_add/precone_zero]_(i : 'I_n) u i)) : C :=
  \big[precone_add/precone_zero]_(I in Pneg n) f (@Delta_arg n u x I).

(** [Δ f u⃗] — the pointwise cone difference [Δ⁺ ⊖ Δ⁻], 0-extended off
    the region where the order [Δ⁻ ≤ Δ⁺] holds. *)
Definition Delta (n : nat) (u : 'I_n -> B)
    (x : local_cone (\big[precone_add/precone_zero]_(i : 'I_n) u i)) : C :=
  match pselect (precone_le (@Delta_neg n u x) (@Delta_pos n u x)) with
  | left p => projT1 (cid p)
  | right _ => precone_zero
  end.

(** Defining equation: where [Δ⁻ ≤ Δ⁺], [Δ⁺ = Δ⁻ + Δ]. *)
Lemma Delta_E (n : nat) (u : 'I_n -> B)
    (x : local_cone (\big[precone_add/precone_zero]_(i : 'I_n) u i)) :
  precone_le (@Delta_neg n u x) (@Delta_pos n u x) ->
  @Delta_pos n u x = @Delta_neg n u x + @Delta n u x.
Proof.
move=> p; rewrite /Delta; case: pselect => [p'|]; last by [].
exact: (projT2 (cid p')).
Qed.

End Delta.

Arguments Delta_arg {R B n} u x I.
Arguments Delta_pos {R B C} f {n} u x.
Arguments Delta_neg {R B C} f {n} u x.
Arguments Delta {R B C} f {n} u x.

(** ** The base case [n = 0] — Paper §7.3 (txt ~3446)

    For [n = 0] the only family is the empty one and [\sumP_i u i = 0],
    so [B_() = local_cone 0].  We have [P⁻(0) = ∅] and [P⁺(0) = {∅}], so
    [Δ⁻f(()) = 0], [Δ⁺f(())(x) = f (lc_val x)] and hence [Δf(())(x) =
    f (lc_val x)] — the paper's [Δf(()) = f]. *)

Lemma Pneg0 : Pneg 0 = finset.set0.
Proof.
apply/setP => I; rewrite finset.in_set0 in_Pneg.
by have -> : #|I| = 0%N by apply/eqP; rewrite cards_eq0; apply/eqP/setP; case.
Qed.

Lemma Ppos0 : Ppos 0 = [set finset.set0 : {set 'I_0}].
Proof.
apply/setP => I; rewrite in_Ppos inE.
have -> : #|I| = 0%N by apply/eqP; rewrite cards_eq0; apply/eqP/setP; case=> -[].
by rewrite subn0/=; apply/esym/eqP/setP => i; case: i.
Qed.

Section DeltaZero.
Variable R : realType.
Variables B C : coneType R.
Variable f : B -> C.
Local Open Scope precone_scope.

Lemma Delta_neg0 (u : 'I_0 -> B)
    (x : local_cone (\big[precone_add/precone_zero]_(i : 'I_0) u i)) :
  Delta_neg f u x = 0.
Proof. by rewrite /Delta_neg Pneg0 big_set0. Qed.

Lemma Delta_pos0 (u : 'I_0 -> B)
    (x : local_cone (\big[precone_add/precone_zero]_(i : 'I_0) u i)) :
  Delta_pos f u x = f (lc_val x).
Proof.
by rewrite /Delta_pos Ppos0 big_set1 /Delta_arg big_set0 precone_addr0.
Qed.

End DeltaZero.

(** ** Well-definedness of [Δ]: [Δ⁻ ≤ Δ⁺] on the ball — Paper §7.3

    For a totally monotonic [f], the [n] instance of total monotonicity
    (Condition (7.1)) at centre [lc_val x] and family [u] is exactly the
    inequality [Δ⁻f(u⃗)(x) ≤ Δ⁺f(u⃗)(x)].  Its norm side-condition
    [‖lc_val x + Σᵢ uᵢ‖ ≤ 1] holds on the unit ball of [B_u⃗] by
    [lc_step1] (provided [‖Σᵢ uᵢ‖ < 1], so that [B_u⃗] is a cone).  This
    is what makes the pointwise difference [Δf(u⃗)] well defined on the
    ball, via [Delta_E]. *)

Section DeltaWellDef.
Variable R : realType.
Variables B C : coneType R.
Variable f : B -> C.
Hypothesis Hf : is_totmono f.
Local Open Scope precone_scope.

Lemma Delta_neg_le_pos (n : nat) (u : 'I_n -> B)
    (Hs : cone_norm (\big[precone_add/precone_zero]_(i : 'I_n) u i) < 1)
    (x : local_cone (\big[precone_add/precone_zero]_(i : 'I_n) u i)) :
  lc_norm x <= 1 ->
  precone_le (Delta_neg f u x) (Delta_pos f u x).
Proof.
move=> Hx.
have cond : cone_norm (lc_val x +
    \big[precone_add/precone_zero]_(i : 'I_n) u i) <= 1.
  rewrite precone_addC.
  exact: (@lc_step1 R B (\big[precone_add/precone_zero]_(i : 'I_n) u i)
            Hs x Hx).
have := Hf cond.
by rewrite /Delta_neg /Delta_pos /Delta_arg /tm_arg.
Qed.

End DeltaWellDef.

(** ** Definition 7.15 — [n]-increasing functions — Paper §7.3 (txt ~3448)

    [f : B → C] is *increasing* when it is monotone for [precone_le] on
    the unit ball [B_B] (this matches the conclusion of
    [totmono_increasing], the [n = 1] sanity lemma of [totmono.v]). *)

Definition is_increasing (R : realType) (B C : coneType R) (f : B -> C)
    : Prop :=
  forall x v : B, cone_norm (precone_add x v) <= 1 ->
    precone_le (f x) (f (precone_add x v)).

Arguments is_increasing {R B C} f.

(** Definition 7.15.  [is_n_increasing n f] is a [Fixpoint] on [n]:

    - [n = 0]: [f] is increasing;
    - [n.+1]: [f] is increasing *and*, for every direction [u ∈ B_B],
      the single-step difference [Δf(u)] is [n]-increasing *from the
      local cone of [u]*.

    The recursive call changes the source cone from [B] to the local
    cone of [u].  We keep [B] (here [lc_coneType Hu]) a parameter of the
    fixpoint so the call typechecks, and — crucially — we present the
    direction [u] as the *one-element family* [fun _ : 'I_1 => u] so that
    [Δf(u) = Delta f (fun _ => u)] has the literal source
    [local_cone (\sumP_(i:'I_1) u) = lc_coneType Hu] *without any cast*.
    The hypothesis [Hu] is the [‖·‖ < 1] witness needed for that local
    cone to be a [coneType]; up to the propositional identity
    [\sumP_(i:'I_1) u = u] it is the paper's [u ∈ B_B] (strict interior,
    as in [local_cone.v]). *)
Fixpoint is_n_increasing (n : nat) (R : realType) (B C : coneType R)
    (f : B -> C) {struct n} : Prop :=
  match n with
  | 0 => is_increasing f
  | n'.+1 => is_increasing f /\
      forall (u : B) (Hu : cone_norm
        (\big[precone_add/precone_zero]_(i : 'I_1) (fun=> u) i) < 1),
        @is_n_increasing n' R (lc_coneType Hu) C (Delta f (fun=> u))
  end.

Arguments is_n_increasing n {R B C} f.

(** ** Lemma 7.16 — Paper §7.3 (txt ~3453)

    If [f] is [n]-increasing for all [n], then for each [u ∈ B_B] the
    single-step difference [Δf(u) : B_u → C] is [n]-increasing for all
    [n].  This is the second conjunct of [is_n_increasing] at [n.+1],
    read off directly. *)
Lemma is_n_increasing_Delta (R : realType) (B C : coneType R) (f : B -> C) :
  (forall n, is_n_increasing n f) ->
  forall (u : B) (Hu : cone_norm
     (\big[precone_add/precone_zero]_(i : 'I_1) (fun=> u) i) < 1) (n : nat),
    @is_n_increasing n R (lc_coneType Hu) C (Delta f (fun=> u)).
Proof. by move=> H u Hu n; have /= [_ /(_ u Hu)] := H n.+1. Qed.

(** ** Lemma 7.17 — the cons recurrence — Paper §7.3 (txt ~3456)

    Let [v⃗ = (u, u⃗)] be the family [u :: u⃗] of length [n+1].  Splitting
    the [Pε(n+1)] sum into the parts with [ord0 ∈ I] and [ord0 ∉ I]
    (mathcomp [bigID]) and reindexing each via Lemma 7.4 ([Ppos_split_in]
    / [Ppos_split_out], discharged by [big_imset]) yields the paper's

      [Δε f (u :: u⃗)(x) = Δε f u⃗ (x + u) + Δ^{-ε} f u⃗ (x)].

    We isolate the combinatorial core as a pure cone-sum identity on [B]
    ([Spos]/[Sneg], the [Δ⁺]/[Δ⁻] formulas read at a centre [xb : B]),
    independent of the local-cone packaging; the operator form then
    follows by [Delta_pos = Spos ∘ lc_val] ([Delta_pos_Spos]). *)

Section Recurrence.
Variable R : realType.
Variables B C : coneType R.
Variable f : B -> C.
Local Open Scope precone_scope.

(** [u :: u⃗]: the family of length [n+1] with head [u] at [ord0] and
    tail [u⃗] on the [lift ord0]-image. *)
Definition vcons (n : nat) (u : B) (w : 'I_n -> B) : 'I_n.+1 -> B :=
  fun j => match unlift ord0 j with Some i => w i | None => u end.

Lemma vcons0 (n : nat) (u : B) (w : 'I_n -> B) : vcons u w ord0 = u.
Proof. by rewrite /vcons unlift_none. Qed.

Lemma vconsS (n : nat) (u : B) (w : 'I_n -> B) (i : 'I_n) :
  vcons u w (lift ord0 i) = w i.
Proof. by rewrite /vcons liftK. Qed.

(** Inner-sum reindexings (Lemma 7.4, applied to a single sum). *)
Lemma sumP_injI (n : nat) (g : 'I_n.+1 -> B) (J : {set 'I_n}) :
  \big[precone_add/precone_zero]_(i in injI J) g i =
  \big[precone_add/precone_zero]_(i in J) g (lift ord0 i).
Proof. by rewrite /injI big_imset//; exact: in2W lift_inj. Qed.

Lemma sumP_injI0 (n : nat) (g : 'I_n.+1 -> B) (J : {set 'I_n}) :
  \big[precone_add/precone_zero]_(i in injI0 J) g i =
  g ord0 + \big[precone_add/precone_zero]_(i in J) g (lift ord0 i).
Proof. by rewrite /injI0 big_setU1 ?ord0_notin_injI// sumP_injI. Qed.

(** The combinatorial core, on [B]: the [Δ⁺]/[Δ⁻] sums read at a [B]
    centre [xb]. *)
Definition Spos (n : nat) (u : 'I_n -> B) (xb : B) : C :=
  \big[precone_add/precone_zero]_(I in Ppos n)
    f (xb + \big[precone_add/precone_zero]_(i in I) u i).

Definition Sneg (n : nat) (u : 'I_n -> B) (xb : B) : C :=
  \big[precone_add/precone_zero]_(I in Pneg n)
    f (xb + \big[precone_add/precone_zero]_(i in I) u i).

(** Lemma 7.17, core ([ε = +]): split [bigID] on [ord0 ∈ I], reindex by
    [injI0] / [injI] (Lemma 7.4), and read off the head [u] and tail. *)
Lemma Spos_recur (n : nat) (u : B) (w : 'I_n -> B) (xb : B) :
  @Spos n.+1 (vcons u w) xb = @Spos n w (xb + u) + @Sneg n w xb.
Proof.
rewrite /Spos /Sneg (bigID (fun I : {set 'I_n.+1} => ord0 \in I))/=.
congr precone_add.
- rewrite (eq_bigl (fun I => I \in [set I in Ppos n.+1 | ord0 \in I]));
    last by move=> I; rewrite inE.
  rewrite Ppos_split_in big_imset/=;
    last exact: in2W (can_inj (@projI_injI0 n)).
  apply: eq_bigr => J _; rewrite sumP_injI0 vcons0.
  rewrite precone_addA; congr (f (_ + _)); apply: eq_bigr => i _.
  by rewrite vconsS.
- rewrite (eq_bigl (fun I => I \in [set I in Ppos n.+1 | ord0 \notin I]));
    last by move=> I; rewrite !inE.
  rewrite Ppos_split_out big_imset/=;
    last exact: in2W (can_inj (@projI_injI n)).
  apply: eq_bigr => J _; rewrite sumP_injI.
  by congr (f (_ + _)); apply: eq_bigr => i _; rewrite vconsS.
Qed.

(** Lemma 7.17, core ([ε = −]): same split, with the sign on the
    [ord0 ∉ I] part flipped ([Pneg_split_out] lands in [Ppos n]). *)
Lemma Sneg_recur (n : nat) (u : B) (w : 'I_n -> B) (xb : B) :
  @Sneg n.+1 (vcons u w) xb = @Sneg n w (xb + u) + @Spos n w xb.
Proof.
rewrite /Spos /Sneg (bigID (fun I : {set 'I_n.+1} => ord0 \in I))/=.
congr precone_add.
- rewrite (eq_bigl (fun I => I \in [set I in Pneg n.+1 | ord0 \in I]));
    last by move=> I; rewrite inE.
  rewrite Pneg_split_in big_imset/=;
    last exact: in2W (can_inj (@projI_injI0 n)).
  apply: eq_bigr => J _; rewrite sumP_injI0 vcons0.
  rewrite precone_addA; congr (f (_ + _)); apply: eq_bigr => i _.
  by rewrite vconsS.
- rewrite (eq_bigl (fun I => I \in [set I in Pneg n.+1 | ord0 \notin I]));
    last by move=> I; rewrite !inE.
  rewrite Pneg_split_out big_imset/=;
    last exact: in2W (can_inj (@projI_injI n)).
  apply: eq_bigr => J _; rewrite sumP_injI.
  by congr (f (_ + _)); apply: eq_bigr => i _; rewrite vconsS.
Qed.

(** [Δ⁺]/[Δ⁻] read on a local-cone point equal the [B]-core at its
    [lc_val] (definitionally: [Delta_arg u x I = lc_val x + Σ_{i∈I} uᵢ]). *)
Lemma Delta_pos_Spos (n : nat) (u : 'I_n -> B)
    (x : local_cone (\big[precone_add/precone_zero]_(i : 'I_n) u i)) :
  Delta_pos f u x = @Spos n u (lc_val x).
Proof. by rewrite /Delta_pos /Spos /Delta_arg. Qed.

Lemma Delta_neg_Sneg (n : nat) (u : 'I_n -> B)
    (x : local_cone (\big[precone_add/precone_zero]_(i : 'I_n) u i)) :
  Delta_neg f u x = @Sneg n u (lc_val x).
Proof. by rewrite /Delta_neg /Sneg /Delta_arg. Qed.

(** Lemma 7.17 (operator form): the [Δ⁺] / [Δ⁻] cons recurrences.
    Here [x] is a point of [B_{u::u⃗}] and [lc_val x + u] is the centre
    of the [B_u⃗]-sum (the paper's [x + u]); [lc_val x] the centre of the
    [B_u⃗]-sum (the paper's [x]). *)
Lemma Delta_pos_recur (n : nat) (u : B) (w : 'I_n -> B)
    (x : local_cone
       (\big[precone_add/precone_zero]_(i : 'I_n.+1) vcons u w i)) :
  Delta_pos f (vcons u w) x = @Spos n w (lc_val x + u) + @Sneg n w (lc_val x).
Proof. by rewrite Delta_pos_Spos Spos_recur. Qed.

Lemma Delta_neg_recur (n : nat) (u : B) (w : 'I_n -> B)
    (x : local_cone
       (\big[precone_add/precone_zero]_(i : 'I_n.+1) vcons u w i)) :
  Delta_neg f (vcons u w) x = @Sneg n w (lc_val x + u) + @Spos n w (lc_val x).
Proof. by rewrite Delta_neg_Sneg Sneg_recur. Qed.

(** The [n]-instance of total monotonicity, read on the [B]-core: where
    the norm condition holds, [Δ⁻f(u⃗) ≤ Δ⁺f(u⃗)]. *)
Lemma Sneg_le_Spos (Hf : is_totmono f) (n : nat) (u : 'I_n -> B) (xb : B) :
  cone_norm (precone_add xb
     (\big[precone_add/precone_zero]_(i : 'I_n) u i)) <= 1 ->
  precone_le (@Sneg n u xb) (@Spos n u xb).
Proof. by move=> Hc; have := Hf _ xb u Hc; rewrite /Sneg /Spos /tm_arg. Qed.

(** Lemma 7.17 (monotonicity of the difference): in additive,
    subtraction-free form, [Δf(u⃗)(x) ≤ Δf(u⃗)(x+u)] reads
    [Δ⁻f(u⃗)(x+u) + Δ⁺f(u⃗)(x) ≤ Δ⁺f(u⃗)(x+u) + Δ⁻f(u⃗)(x)].  It is the
    [n+1]-instance of total monotonicity at [u :: u⃗], rewritten by the
    two cons recurrences. *)
Lemma Sdiff_mono (Hf : is_totmono f) (n : nat) (u : B) (w : 'I_n -> B)
    (xb : B) :
  cone_norm (precone_add xb
     (\big[precone_add/precone_zero]_(i : 'I_n.+1) vcons u w i)) <= 1 ->
  precone_le (@Sneg n w (xb + u) + @Spos n w xb)
             (@Spos n w (xb + u) + @Sneg n w xb).
Proof.
move=> Hc; have := @Sneg_le_Spos Hf n.+1 (vcons u w) xb Hc.
by rewrite Spos_recur Sneg_recur.
Qed.

End Recurrence.

Arguments vcons {R B n} u w.
Arguments Spos {R B C} f n u xb.
Arguments Sneg {R B C} f n u xb.

(** ** Generic cone helpers used by §7.3 below

    Two facts about the local cone and cone-sums that drive the
    nested-cone argument of Lemma 7.18: a left-cancellation for the cone
    order, the [lc_val]-homomorphism over a [bigop], and the subset
    monotonicity of a [\sumP]. *)

Section ConeHelpers.
Variable R : realType.
Local Open Scope precone_scope.

(** Left-cancellation for the cone order: [c + a ≤p c + b ⇒ a ≤p b].
    The dual of [precone_add_le_l]; derived from [precone_cancel]. *)
Lemma precone_le_addlI (B : coneType R) (c a b : B) :
  c + a <=p c + b -> a <=p b.
Proof.
move=> [z Hz]; exists z.
by apply: (@precone_cancel _ _ c); rewrite Hz precone_addA.
Qed.

(** [lc_val] commutes with an arbitrary [bigop] (it is a precone
    homomorphism), in the general [\big[_/_]_(i <- r | Q i)] shape. *)
Lemma lc_val_big (B : coneType R) (x : B) (Hx : cone_norm x < 1)
    (T : Type) (r : seq T) (Q : pred T) (g : T -> lc_coneType Hx) :
  lc_val (\big[precone_add/precone_zero]_(i <- r | Q i) g i) =
  \big[precone_add/precone_zero]_(i <- r | Q i) lc_val (g i).
Proof. by elim/big_rec2: _ => // i s s' _ <-; rewrite lc_valD. Qed.

(** A partial [\sumP] is below the full one: [Σ_{i∈I} g ≤p Σ_i g]. *)
Lemma sumP_sub_le (B : coneType R) (T : finType) (I : {set T})
    (g : T -> B) :
  \big[precone_add/precone_zero]_(i in I) g i <=p
  \big[precone_add/precone_zero]_(i : T) g i.
Proof.
rewrite [X in (_ <=p X)](bigID (fun i => i \in I))/=.
by exists (\big[precone_add/precone_zero]_(i | i \notin I) g i).
Qed.

(** Head/tail split of the [\sumP] of a [vcons] family: the [u :: u⃗] sum
    is [u + Σⱼ u⃗ⱼ]. *)
Lemma sum_vcons (B : coneType R) (n : nat) (u : B) (w : 'I_n -> B) :
  \big[precone_add/precone_zero]_(i : 'I_n.+1) vcons u w i =
  u + \big[precone_add/precone_zero]_(i : 'I_n) w i.
Proof.
rewrite big_ord_recl vcons0; congr (u + _).
by apply: eq_bigr => i _; rewrite vconsS.
Qed.

End ConeHelpers.

Arguments precone_le_addlI {R B} c a b.

(** ** ω-continuity of the inclusion [lc_val : B_x → B] — Paper §7.1
       (the missing "translate" lemma for §7.3)

    The inclusion [lc_val : B_x → B] is ω-continuous on the unit ball: for
    an increasing unit-ball chain [u : nat → B_x], the [B]-value of the
    [B_x]-supremum is the [B]-supremum of the [B]-values,

      [lc_val (cone_sup_ball u) = cone_sup_ball (lc_val ∘ u)] .

    This is derived purely from existing exports: the (Normc) translate of
    the local cone [lc_sup_ball_translate]
    ([x + lc_val(B_x-sup u) = B-sup of (x + lc_val uₙ)]), the shift-commutes
    fact [sup_ball_addr] (the [B]-sup commutes with [· + x]) and the
    cancellation [precone_cancel] (cancel the centre [x]).  The B-side chain
    proofs are derived from the [B_x]-chain ones by [lc_leE] (order
    coincidence) and [lc_val_norm_le] (the [B]-norm is below the gauge
    norm). *)

Section LcValScott.
Variable R : realType.
Variable B : coneType R.
Variable x : B.
Hypothesis Hx : cone_norm x < 1.
Local Notation LC := (lc_coneType Hx).
Variable u : nat -> LC.
Local Open Scope precone_scope.

(** The [B]-value chain inherits monotonicity from the [B_x]-chain. *)
Lemma lc_val_chain_mono (uch : forall n, u n <=p u n.+1) n :
  lc_val (u n) <=p lc_val (u n.+1).
Proof. exact: (lc_leE Hx (u n) (u n.+1)).1 (uch n). Qed.

(** The [B]-value chain stays in the unit ball ([B]-norm ≤ gauge norm). *)
Lemma lc_val_chain_ub1 (ub1 : forall n, cone_norm (u n) <= 1) n :
  cone_norm (lc_val (u n)) <= 1.
Proof. by apply: le_trans (ub1 n); exact: (lc_val_norm_le Hx (u n)). Qed.

(** **ω-continuity of [lc_val].**  The B-side chain proofs [vch]/[vb1] are
    passed explicitly (they are the [lc_val_chain_mono]/[lc_val_chain_ub1]
    of the [B_x]-chain proofs [uch]/[ub1]); [cone_sup_ball] is determined by
    the chain up to its (irrelevant) proof arguments. *)
Lemma lc_val_scott
    (uch : forall n, u n <=p u n.+1)
    (ub1 : forall n, cone_norm (u n) <= 1)
    (vch : forall n, lc_val (u n) <=p lc_val (u n.+1))
    (vb1 : forall n, cone_norm (lc_val (u n)) <= 1) :
  lc_val (cone_sup_ball u uch ub1) =
  cone_sup_ball (fun n => lc_val (u n)) vch vb1.
Proof.
have transl := lc_sup_ball_translate uch ub1.
set SL := lc_val (cone_sup_ball u uch ub1) in transl *.
set SB := cone_sup_ball (fun n => lc_val (u n)) vch vb1.
(* The shifted chain [n ↦ lc_val uₙ + x] is increasing and unit-ball. *)
have addch n : lc_val (u n) + x <=p lc_val (u n.+1) + x.
  by apply: precone_add_le_r; exact: vch.
have addub n : cone_norm (lc_val (u n) + x) <= 1.
  by rewrite precone_addC; exact: (lc_step1 Hx (ub1 n)).
(* Cancel the centre [x]: show [x + SL = x + SB]. *)
apply: (@precone_cancel _ _ x).
rewrite transl.
(* [transl]'s sup is over [n ↦ x + lc_val uₙ]; flip to [lc_val uₙ + x]. *)
set CH := cone_sup_ball (fun n => x + lc_val (u n))
  (local_cone.c_mono_subproof0 uch) (local_cone.c_ub1_subproof0 ub1).
have ->: CH = cone_sup_ball (fun n => lc_val (u n) + x) addch addub.
  apply: precone_le_anti.
  - apply: cone_sup_ball_lub => n; rewrite precone_addC.
    exact: (cone_sup_ball_ub (fun n => lc_val (u n) + x) addch addub n).
  - apply: cone_sup_ball_lub => n; rewrite [lc_val (u n) + x]precone_addC.
    exact: (cone_sup_ball_ub (fun n => x + lc_val (u n))
      (local_cone.c_mono_subproof0 uch) (local_cone.c_ub1_subproof0 ub1) n).
have key := @sup_ball_addr R B (fun n => lc_val (u n)) vch vb1 x addch addub.
by rewrite key precone_addC.
Qed.

End LcValScott.

Arguments lc_val_chain_mono {R B x} Hx {u} uch n.
Arguments lc_val_chain_ub1 {R B x} Hx {u} ub1 n.
Arguments lc_val_scott {R B x} Hx {u} uch ub1 vch vb1.

(** ** Lemma 7.18 — [Δf(u)] is totally monotonic — Paper §7.3 (txt 3523)

    For [f] totally monotonic and [u ∈ B_B], the single-step difference
    [Δf(u) : B_u → C] is totally monotonic.

    The paper's proof opens "notice that [(B_u)_u⃗ = B_{u,u⃗}]".  In this
    formalization [B_u = local_cone u] carries the *gauge* norm, so the
    identity is not definitional.  We resolve the obstacle *without* a
    cone-iso/transport: every point of the nested cone [(B_u)_u⃗] used in
    the total-monotonicity instance of [Δf(u)] is some [tm_arg xL wL I],
    an actual point of [B_u]; we expand the value [Δf(u)(tm_arg xL wL I)]
    through the [n = 1] defining equation [Delta1_E] *at that very point*,
    pushing the whole computation through [lc_val] onto the [B]-side.
    There the cons-recurrences [Spos_recur] / [Sneg_recur] (head [u]) and
    the difference-monotonicity inequality [Sdiff_mono] (the
    [(u :: u⃗)]-instance of total monotonicity of [f]) close the goal. *)

Section Lemma718.
Variable R : realType.
Variables B C : coneType R.
Variable f : B -> C.
Variable u : B.
Local Open Scope precone_scope.

(** The one-element family [fun _ : 'I_1 => u] and its [\sumP] (which is
    [u] up to [big_ord1]). *)
Notation oneu := (fun _ : 'I_1 => u).
Notation su := (\big[precone_add/precone_zero]_(i : 'I_1) oneu i).

(** [Δ⁺f(u)(x) = f(lc_val x + u)] (the [Ppos 1 = {{1}}] term). *)
Lemma Delta1_pos (x : local_cone su) :
  Delta_pos f oneu x = f (lc_val x + u).
Proof.
rewrite Delta_pos_Spos /Spos Ppos1 big_set1; congr (f (_ + _)).
rewrite (eq_bigl predT); last by move=> i; rewrite finset.in_setT.
by rewrite big_ord1.
Qed.

(** [Δ⁻f(u)(x) = f(lc_val x)] (the [Pneg 1 = {∅}] term). *)
Lemma Delta1_neg (x : local_cone su) :
  Delta_neg f oneu x = f (lc_val x).
Proof.
by rewrite Delta_neg_Sneg /Sneg Pneg1 big_set1 big_set0 precone_addr0.
Qed.

(** The [n = 1] defining equation read on a single point: where [f] is
    increasing at [lc_val x], [f(lc_val x + u) = f(lc_val x) + Δf(u)(x)].
    This is the paper's [Δf(u)(x) = f(x + u) ⊖ f(x)]. *)
Lemma Delta1_E (x : local_cone su) :
  f (lc_val x) <=p f (lc_val x + u) ->
  f (lc_val x + u) = f (lc_val x) + Delta f oneu x.
Proof.
move=> Hle.
have HE : Delta_neg f oneu x <=p Delta_pos f oneu x.
  by rewrite Delta1_pos Delta1_neg.
by have := Delta_E HE; rewrite Delta1_pos Delta1_neg.
Qed.

Hypothesis Hsu : cone_norm su < 1.
Notation Bu := (lc_coneType Hsu).

(** The increasing instance at each index set [I], derived from
    increasingness of [f] and the unit-ball bound on [B_u].  The point
    [lc_val (tm_arg xL wL I) + u] lies in [B_B] because
    [tm_arg xL wL I ≤ xL + Σⱼ wL j] in [B_u] and [lc_step1] transports the
    [B_u]-ball bound to [B].  Parametrised on [is_increasing f] so the
    same lemma serves both directions of Theorem 7.19. *)
Lemma Delta1_inc (Hi : is_increasing f) (m : nat) (xL : Bu)
    (wL : 'I_m -> Bu)
    (Hnorm : cone_norm
       (xL + \big[precone_add/precone_zero]_(i : 'I_m) wL i) <= 1)
    (I : {set 'I_m}) :
  f (lc_val (tm_arg xL wL I)) <=p f (lc_val (tm_arg xL wL I) + u).
Proof.
have step1 := lc_step1 Hsu Hnorm.
apply: Hi; apply: le_trans step1; apply: cone_normp.
rewrite /tm_arg lc_valD lc_val_big.
rewrite [in X in (_ <=p X)]lc_valD lc_val_big.
rewrite [X in (_ <=p X + _)]big_ord1.
rewrite [X in (_ <=p X)]precone_addC -precone_addA precone_addA.
by apply: precone_add_le_r; apply: precone_add_le_l; exact: sumP_sub_le.
Qed.

(** Summed [n = 1] equation (positive part): the paper's
    [Δ⁺f(u⃗)(x + u) = Δ⁺f(u⃗)(x) + Δ⁺(Δf(u))(u⃗)(x)], read with [Δ⁺f(u⃗)]
    on the [B]-side as [Spos] at the centre [lc_val xL]. *)
Lemma SDpos_E (m : nat) (xL : Bu) (wL : 'I_m -> Bu)
    (Hinc : forall I : {set 'I_m},
       f (lc_val (tm_arg xL wL I)) <=p f (lc_val (tm_arg xL wL I) + u)) :
  Spos f m (fun i => lc_val (wL i)) (lc_val xL + u) =
  Spos f m (fun i => lc_val (wL i)) (lc_val xL) +
  \big[precone_add/precone_zero]_(I in Ppos m) Delta f oneu (tm_arg xL wL I).
Proof.
rewrite /Spos -big_split/=; apply: eq_bigr => I _.
have harg : lc_val (tm_arg xL wL I) =
    lc_val xL + \big[precone_add/precone_zero]_(i in I) lc_val (wL i).
  by rewrite /tm_arg lc_valD lc_val_big.
rewrite -precone_addA (precone_addC u) precone_addA -harg.
by move/Delta1_E : (Hinc I) => ->.
Qed.

(** Summed [n = 1] equation (negative part), identical with [Pneg]. *)
Lemma SDneg_E (m : nat) (xL : Bu) (wL : 'I_m -> Bu)
    (Hinc : forall I : {set 'I_m},
       f (lc_val (tm_arg xL wL I)) <=p f (lc_val (tm_arg xL wL I) + u)) :
  Sneg f m (fun i => lc_val (wL i)) (lc_val xL + u) =
  Sneg f m (fun i => lc_val (wL i)) (lc_val xL) +
  \big[precone_add/precone_zero]_(I in Pneg m) Delta f oneu (tm_arg xL wL I).
Proof.
rewrite /Sneg -big_split/=; apply: eq_bigr => I _.
have harg : lc_val (tm_arg xL wL I) =
    lc_val xL + \big[precone_add/precone_zero]_(i in I) lc_val (wL i).
  by rewrite /tm_arg lc_valD lc_val_big.
rewrite -precone_addA (precone_addC u) precone_addA -harg.
by move/Delta1_E : (Hinc I) => ->.
Qed.

(** Lemma 7.18.  Total monotonicity of [Δf(u) : B_u → C]: for every [m],
    [xL] and [wL] with the [B_u]-ball bound, [Δ⁻(Δf(u))(u⃗) ≤ Δ⁺(Δf(u))(u⃗)].
    Expand both [\sumP]s of [Δf(u)]-values by [SDneg_E] / [SDpos_E], use
    the [(u :: u⃗)]-difference inequality [Sdiff_mono] of [f], and cancel
    the common summand [Σ⁻ + Σ⁺] (at centre [lc_val xL]) on the left. *)
Lemma totmono_Delta1 (Hf : is_totmono f) : @is_totmono R Bu C (Delta f oneu).
Proof.
move=> m xL wL Hnorm.
have Hinc := Delta1_inc (totmono_increasing Hf) Hnorm.
have key : Sneg f m (fun i => lc_val (wL i)) (lc_val xL + u)
             + Spos f m (fun i => lc_val (wL i)) (lc_val xL) <=p
           Spos f m (fun i => lc_val (wL i)) (lc_val xL + u)
             + Sneg f m (fun i => lc_val (wL i)) (lc_val xL).
  apply: (@Sdiff_mono R B C f Hf m u (fun i => lc_val (wL i)) (lc_val xL)).
  have suE : su = u by rewrite big_ord1.
  rewrite sum_vcons -[in X in cnorm (_ + (X + _)) <= _]suE.
  rewrite precone_addA (precone_addC (lc_val xL)) -precone_addA.
  rewrite -lc_val_big -lc_valD.
  exact: (lc_step1 Hsu Hnorm).
move: key; rewrite SDpos_E// SDneg_E//.
set Sn := Sneg f m _ _; set Sp := Spos f m _ _.
set DN := \big[_/_]_(I in Pneg m) _; set DP := \big[_/_]_(I in Ppos m) _.
rewrite -[Sn + DN + Sp]precone_addA [DN + Sp]precone_addC precone_addA.
rewrite -[Sp + DP + Sn]precone_addA [DP + Sn]precone_addC precone_addA.
rewrite [Sp + Sn]precone_addC.
exact: (precone_le_addlI (Sn + Sp)).
Qed.

End Lemma718.

Arguments totmono_Delta1 {R B C} f u Hsu Hf.

(** ** Lemma 7.17, last monotonicity clause — Paper §7.3 (txt 3516)

    Operator-level difference monotonicity: [Δf(u⃗)(x) ≤ Δf(u⃗)(x + u)].
    Here [x] and [x'] are two points of [B_u⃗ = local_cone (Σⱼ u⃗ⱼ)] with
    [x'] reached from [x] by a step [u] of [B] ([lc_val x' = lc_val x + u]);
    [Δf(u⃗)] is well defined at both by [Delta_neg_le_pos].  Expanding both
    [Δ] through their defining equations [Delta_E] turns the goal into the
    [B]-additive inequality [Sdiff_mono] (the [(u :: u⃗)]-difference
    instance of total monotonicity), after which the common summand
    [Σ⁻(x+u) + Σ⁻(x)] cancels on the left ([precone_le_addlI]).  This
    is the operator-level half of the Lemma 7.17 clause; [Sdiff_mono]
    earlier in this file is its subtraction-free [B]-form. *)

Section DeltaMono.
Variable R : realType.
Variables B C : coneType R.
Variable f : B -> C.
Hypothesis Hf : is_totmono f.
Local Open Scope precone_scope.

Lemma Delta_mono (n : nat) (w : 'I_n -> B)
    (Hs : cone_norm (\big[precone_add/precone_zero]_(i : 'I_n) w i) < 1)
    (x x' : local_cone (\big[precone_add/precone_zero]_(i : 'I_n) w i))
    (u : B) (Hxx' : lc_val x' = lc_val x + u)
    (Hxle : lc_norm x <= 1) (Hx'le : lc_norm x' <= 1)
    (Hdiff : cone_norm (lc_val x +
        \big[precone_add/precone_zero]_(i : 'I_n.+1) vcons u w i) <= 1) :
  Delta f w x <=p Delta f w x'.
Proof.
have Ex := Delta_E (Delta_neg_le_pos Hf Hs Hxle).
have Ex' := Delta_E (Delta_neg_le_pos Hf Hs Hx'le).
move: Ex Ex'; rewrite !Delta_pos_Spos !Delta_neg_Sneg Hxx' => Ex Ex'.
have key := @Sdiff_mono R B C f Hf n u w (lc_val x) Hdiff.
rewrite Ex Ex' in key; move: key.
set Su := Sneg f n w (lc_val x + u); set Sx := Sneg f n w (lc_val x).
rewrite precone_addA -[Su + Delta f w x' + Sx]precone_addA.
rewrite [Delta f w x' + Sx]precone_addC precone_addA.
exact: (precone_le_addlI (Su + Sx)).
Qed.

End DeltaMono.

Arguments Delta_mono {R B C} f Hf n w Hs x x' u.

(** ** Theorem 7.19 — Paper §7.3 (txt 3533)

    A function [f : B_B → C] is totally monotonic *iff* it is
    [n]-increasing for every [n].  We deliver the *forward* implication
    here ([totmono_is_n_increasing]) and the *closed-ball converse*
    [is_n_increasing_totmono] below (for [f] also
    [is_scott_continuous_unit]). *)

(** Forward implication (paper: induction on [k]).  For every [n], total
    monotonicity gives [n]-increasingness.  Generalising over [R B C f]
    so the inductive hypothesis applies to [Δf(u) : B_u → C]:
    - [n = 0] is increasingness, i.e. [totmono_increasing];
    - [n.+1] also needs, for each direction [u], that [Δf(u)] be
      [n]-increasing; [Δf(u)] is totally monotonic by Lemma 7.18
      ([totmono_Delta1]), so the inductive hypothesis applies. *)
Lemma totmono_is_n_increasing (n : nat) (R : realType) (B C : coneType R)
    (f : B -> C) : is_totmono f -> is_n_increasing n f.
Proof.
elim: n R B C f => [|n IHn] R B C f Hf.
  exact: (totmono_increasing Hf).
split; first exact: (totmono_increasing Hf).
move=> u Hu.
exact: (IHn _ _ _ _ (totmono_Delta1 f u Hu Hf)).
Qed.

(** ** Theorem 7.19 converse — Paper §7.3 (txt 3545)

    The paper's induction on the arity [n].  The [(u₀ :: u⃗)] instance of
    the (7.1) inequality for [f] reduces, by the two cons recurrences and
    the summed [n = 1] equations [SDpos_E] / [SDneg_E], to the (7.1)
    inequality for the single-step difference [Δf(u₀) : B_{u₀} → C] at
    arity [n].  By Lemma 7.16 ([is_n_increasing_Delta]) the difference
    [Δf(u₀)] is [k]-increasing for all [k], so the inductive hypothesis
    (generalised over the source cone) applies to it — provided [B_{u₀}]
    is a [coneType], i.e. [‖u₀‖ < 1] *strictly*.

    We first deliver the *strict-interior* converse ([conv_strict_aux]):
    the (7.1) inequality for every configuration whose total sum lies in
    the *open* unit ball ([‖x + Σᵢ uᵢ‖ < 1]).  Inside the open ball the
    head [u₀] is itself strictly interior ([‖u₀‖ ≤ ‖x + Σᵢ uᵢ‖ < 1]) so
    [B_{u₀}] is a cone, and the nested family [u⃗ ∈ B^{n}] lifts to
    [B_{u₀}] *with step [1]*: each direction [w i] and the centre [x] are
    admissible at [u₀] because they are [≤p (x + Σⱼ wⱼ)] and
    [‖u₀ + (x + Σⱼ wⱼ)‖ = ‖x + Σ vcons‖ ≤ 1].  The lifted [B_{u₀}]-norm
    side-condition is exactly [lc_step1_norm] applied to that same bound.
    The closed-ball converse would follow by an ω-continuity limit at the
    boundary; see the closing status note for the precise remaining wall. *)

(** A direction [z] with [‖u₀ + z‖ ≤ 1] is admissible at the interior
    centre [u₀]: step [1] keeps [u₀ + z] in the unit ball.  This is the
    [‖u₀ + v‖ ≤ 1 ⇒ localP u₀ v] lifting datum. *)
Lemma lift_localP (R : realType) (B : coneType R) (u0 : B) (z : B) :
  cone_norm (precone_add u0 z) <= 1 -> localP u0 z.
Proof.
move=> Hz; exists 1%:nng; split; first by rewrite /= ltr01.
by rewrite precone_scale_1.
Qed.

Arguments lift_localP {R B u0 z}.

(** Strict reach lemma: if [x + lc_val u] is in the *open* unit ball,
    then the gauge norm of [u] is [< 1].  A step [1 + δ] is still
    admissible for [δ] small enough — [x + (1+δ)·u = (x + u) + δ·u] has
    norm [≤ ‖x + u‖ + δ‖u‖ < 1] — so [gauge_sup u ≥ 1 + δ > 1] and
    [lc_norm u = (gauge_sup u)⁻¹ < 1].  This is the strict analogue of
    [lc_step1_norm], needed to keep configurations strictly interior
    through the converse induction. *)
Lemma lc_step1_norm_lt (R : realType) (B : coneType R) (x : B)
    (Hx : cone_norm x < 1) (u : local_cone x) :
  cone_norm (precone_add x (lc_val u)) < 1 -> lc_norm u < 1.
Proof.
move=> Hu.
have [u0|un0] := pselect (lc_val u = precone_zero).
  by rewrite lc_norm0// ltr01.
have nu_pos : 0 < cone_norm (lc_val u).
  rewrite lt_neqAle cone_norm_ge0 andbT eq_sym.
  by apply/eqP => /cone_normz.
(* Choose [δ > 0] with [‖x + u‖ + δ‖u‖ < 1]. *)
pose d : R := (1 - cone_norm (precone_add x (lc_val u)))
              / (2 * cone_norm (lc_val u)).
have d_gt0 : 0 < d by rewrite divr_gt0 ?subr_gt0 ?mulr_gt0 ?ltr0n.
have d_ge0 : 0 <= d := ltW d_gt0.
have onepd_ge0 : 0 <= 1 + d by rewrite addr_ge0// ler01.
(* The step [1 + δ] is admissible. *)
have step_adm : cone_norm
    (precone_add x (precone_scale (NngNum onepd_ge0) (lc_val u))) <= 1.
  have split1 : precone_scale (NngNum onepd_ge0) (lc_val u) =
      precone_add (lc_val u) (precone_scale (NngNum d_ge0) (lc_val u)).
    rewrite -{2}(precone_scale_1 (lc_val u)) -precone_scale_DAl.
    by congr (precone_scale _ (lc_val u)); apply: val_inj.
  rewrite split1 precone_addA.
  apply: le_trans (cone_normt _ _) _.
  rewrite cone_normh /=.
  rewrite -lerBrDl.
  apply: le_trans (_ : d * cone_norm (lc_val u) <= _).
    by rewrite mulrC.
  rewrite /d -mulrA.
  rewrite invfM -mulrA mulVf ?gt_eqF// mulr1.
  rewrite ler_pdivrMr ?ltr0n//.
  rewrite ler_peMr ?subr_ge0 ?ltW//.
  by rewrite -{1}(addr0 1) -[2]/(1 + 1) ltrD2l ltr01.
have ge1d : 1 + d <= gauge_sup u.
  rewrite /gauge_sup; apply: sup_upper_bound; last first.
    by exists (NngNum onepd_ge0).
  by split; [exact: gauge_set_neq0 | exact: gauge_set_ub].
rewrite /lc_norm -invr1 ltf_pV2 ?posrE ?ltr01 ?gauge_sup_gt0//.
by apply: lt_le_trans ge1d; rewrite ltrDl.
Qed.

Arguments lc_step1_norm_lt {R B x} Hx u.

Section ConvStrict.
Variable R : realType.
Local Open Scope precone_scope.

(** Functional [η]-expansion of a family of arity [n+1] as a [vcons] of
    its head [v ord0] and tail [v ∘ lift ord0]. *)
Lemma vcons_eta (B : coneType R) (n : nat) (v : 'I_n.+1 -> B) :
  v = vcons (v ord0) (fun i => v (lift ord0 i)).
Proof.
apply/funext => j; rewrite /vcons.
by case: (unliftP ord0 j) => [i ->|->]; rewrite ?liftK ?unlift_none.
Qed.

(** The strict-interior converse, in [B]-core form.  Generalised over the
    source/target cones and the map so that the inductive hypothesis can
    be applied to [Δf(u₀) : B_{u₀} → C]. *)
Lemma conv_strict_aux (n : nat) (B C : coneType R) (f : B -> C) :
  (forall k, is_n_increasing k f) ->
  forall (x : B) (u : 'I_n -> B),
    cone_norm (x + \big[precone_add/precone_zero]_(i : 'I_n) u i) < 1 ->
    precone_le (Sneg f n u x) (Spos f n u x).
Proof.
elim: n B C f => [|n IHn] B C f Hinc x u Hnorm.
  by rewrite /Sneg Pneg0 big_set0; exact: precone_le0.
(* Split [u] as [u₀ :: w] and unfold the goal through the recurrences. *)
rewrite [u]vcons_eta in Hnorm *.
set u0 := u ord0; set w := (fun i => u (lift ord0 i)).
rewrite -/u0 -/w in Hnorm *.
rewrite Spos_recur Sneg_recur.
(* The total sum is in the open ball, so the head [u₀] is interior. *)
have Hsum : cone_norm
    (\big[precone_add/precone_zero]_(i : 'I_1) (fun=> u0) i) < 1.
  rewrite big_ord1; apply: le_lt_trans Hnorm; apply: cone_normp.
  rewrite sum_vcons -/u0 -/w precone_addA (precone_addC x u0) -precone_addA.
  by exists (x + \big[precone_add/precone_zero]_(i : 'I_n) w i).
set su := \big[precone_add/precone_zero]_(i : 'I_1) (fun=> u0) i.
set sw := \big[precone_add/precone_zero]_(i : 'I_n) w i.
(* Each [z ≤p x + Σⱼ wⱼ] is admissible at the centre [su]: step [1] keeps
   [su + z] in the unit ball, because [su + (x + Σⱼ wⱼ) = x + Σ vcons]. *)
have suxw : su + (x + sw) = x +
    \big[precone_add/precone_zero]_(i : 'I_n.+1)
      vcons u0 w i.
  rewrite /su big_ord1 -/u0 sum_vcons -/u0 -/w.
  by rewrite precone_addA (precone_addC u0 x) -precone_addA.
have Hadm (z : B) : z <=p x + sw -> cone_norm (su + z) <= 1.
  move=> Hz; apply: le_trans (ltW Hnorm); apply: cone_normp.
  rewrite -suxw; apply: precone_add_le_l; exact: Hz.
(* The lifted centre [xL] and family [wL] in [B_{u₀}]. *)
have HxleB : x <=p x + sw by exists sw.
have wi_le_sw i : w i <=p sw.
  have := sumP_sub_le [set i] w; rewrite big_set1 -/sw; exact.
have HwleB i : w i <=p x + sw.
  apply: (@precone_le_trans _ _ sw); first exact: wi_le_sw.
  by exists x; rewrite precone_addC.
pose xL : lc_coneType Hsum := exist (localP su) x (lift_localP (Hadm x HxleB)).
pose wL (i : 'I_n) : lc_coneType Hsum :=
  exist (localP su) (w i) (lift_localP (Hadm (w i) (HwleB i))).
have lc_xL : lc_val xL = x by [].
have lc_wL i : lc_val (wL i) = w i by [].
(* [Δf(u₀)] is [k]-increasing for all [k] (Lemma 7.16). *)
have HD := @is_n_increasing_Delta R B C f Hinc u0 Hsum.
(* The lifted total sum stays strictly interior in [B_{u₀}]. *)
have HnormBu : cone_norm
    (xL + \big[precone_add/precone_zero]_(i : 'I_n) wL i) < 1.
  rewrite -[cone_norm _]/(lc_norm _).
  apply: (lc_step1_norm_lt Hsum); rewrite lc_valD lc_val_big lc_xL.
  rewrite (eq_bigr (fun i => w i)); last by move=> i _; rewrite lc_wL.
  by rewrite -/sw suxw.
(* Increasingness of [f] at the lifted [tm_arg]s, for [SDpos_E]/[SDneg_E]. *)
have Hi : is_increasing f by have := Hinc 0%N.
have Hinc_arg := @Delta1_inc R B C f u0 Hsum Hi n xL wL (ltW HnormBu).
(* The inductive hypothesis on [Δf(u₀)]: its (7.1) inequality at arity
   [n], centre [xL] and family [wL].  Definitionally [Sneg]/[Spos] of
   [Δf(u₀)] are the [\sumP] of [Δf(u₀)] over [Pneg n] / [Ppos n]. *)
have IH : precone_le
    (\big[precone_add/precone_zero]_(I in Pneg n)
       Delta f (fun=> u0) (tm_arg xL wL I))
    (\big[precone_add/precone_zero]_(I in Ppos n)
       Delta f (fun=> u0) (tm_arg xL wL I)).
  exact: IHn (lc_coneType Hsum) C (Delta f (fun=> u0)) HD xL wL HnormBu.
(* The two summed [n = 1] equations, read with [lc_val xL = x] and
   [lc_val ∘ wL = w], turn the goal's [Sε f n w (x + u₀)] terms into the
   centre-[x] term plus the [Δf(u₀)] sum. *)
have wLval : (fun i => lc_val (wL i)) = w.
  by apply/funext => i; rewrite lc_wL.
have EP := @SDpos_E R B C f u0 Hsum n xL wL Hinc_arg.
have EN := @SDneg_E R B C f u0 Hsum n xL wL Hinc_arg.
rewrite lc_xL wLval in EP; rewrite lc_xL wLval in EN.
rewrite EP EN.
set Sw := Spos f n w x; set Snw := Sneg f n w x.
set DP := \big[precone_add/precone_zero]_(I in Ppos n) _.
set DN := \big[precone_add/precone_zero]_(I in Pneg n) _.
(* Goal: (Snw + DN) + Sw ≤p (Sw + DP) + Snw; cancel the common [Snw + Sw]. *)
rewrite -precone_addA [DN + Sw]precone_addC precone_addA.
rewrite -[Sw + DP + Snw]precone_addA [DP + Snw]precone_addC precone_addA.
rewrite [Sw + Snw]precone_addC.
by apply: precone_add_le_l.
Qed.
End ConvStrict.

Arguments conv_strict_aux {R} n {B C} f.

(** ** Theorem 7.19 converse — strict-interior consequences

    The strict-interior converse in the [tm_arg] form of [is_totmono]
    (Condition 7.1): for every strictly-interior configuration the
    [Pneg]/[Ppos] sums of [f] are ordered.  This is exactly the
    [is_totmono] inequality restricted to the open unit ball, derived
    here from [n]-increasingness alone. *)
Lemma conv_strict (R : realType) (B C : coneType R) (f : B -> C) :
  (forall k, is_n_increasing k f) ->
  forall (n : nat) (x : B) (u : 'I_n -> B),
    cone_norm (precone_add x
      (\big[precone_add/precone_zero]_(i : 'I_n) u i)) < 1 ->
    precone_le
      (\big[precone_add/precone_zero]_(I in Pneg n) f (tm_arg x u I))
      (\big[precone_add/precone_zero]_(I in Ppos n) f (tm_arg x u I)).
Proof.
move=> Hinc n x u Hnorm.
have := conv_strict_aux n f Hinc x u Hnorm.
by rewrite /Sneg /Spos /tm_arg.
Qed.

Arguments conv_strict {R B C} f.

(** The pointwise difference [Δf(u⃗)] is well defined on the strict
    interior for an [n]-increasing (for all [n]) map [f].  This is the
    converse-side analogue of [Delta_neg_le_pos] (which assumed
    [is_totmono]): the order [Δ⁻f(u⃗) ≤ Δ⁺f(u⃗)] needed by [Delta_E] now
    follows from [n]-increasingness through the strict-interior converse
    [conv_strict].  The well-definedness region is the open ball of
    configurations, [‖lc_val x + Σᵢ uᵢ‖ < 1]. *)
Section DeltaWellDefConv.
Variable R : realType.
Variables B C : coneType R.
Variable f : B -> C.
Hypothesis Hinc : forall k, is_n_increasing k f.
Local Open Scope precone_scope.

Lemma Delta_neg_le_pos_conv (n : nat) (u : 'I_n -> B)
    (x : local_cone (\big[precone_add/precone_zero]_(i : 'I_n) u i)) :
  cone_norm (lc_val x + \big[precone_add/precone_zero]_(i : 'I_n) u i) < 1 ->
  precone_le (Delta_neg f u x) (Delta_pos f u x).
Proof.
move=> cond.
have := conv_strict f Hinc n (lc_val x) u cond.
by rewrite Delta_pos_Spos Delta_neg_Sneg /Spos /Sneg /tm_arg.
Qed.

End DeltaWellDefConv.

Arguments Delta_neg_le_pos_conv {R B C} f Hinc {n} u x.

(** ** The scaling-chain supremum — the boundary bridge engine

    For a unit-ball point [z] ([‖z‖ ≤ 1]) and the Archimedean ratios
    [λₘ = (m+1)/(m+2) ↑ 1] in [[0,1)], the chain [m ↦ λₘ ·: z] is
    increasing, stays in [B_B], and its [cone_sup_ball] is exactly [z].
    This is the only analytic ingredient the closed-ball converse adds:
    it lets us realise a boundary configuration as the supremum of an
    increasing chain of strictly-interior ones.  The proof of the
    least-upper-bound half is the Archimedean "the gap vanishes" argument
    of [gauge_sup_reach] (in [local_cone.v]), specialised to the simple
    scaling chain. *)

Section ScaleChain.
Variable R : realType.
Variable P : coneType R.

(** The ratio [λₘ = (m+1)/(m+2)] and its complement [1 − λₘ = 1/(m+2)],
    both as nonneg reals. *)
Lemma scl_ge0 (m : nat) : 0 <= (m.+1)%:R / (m.+2)%:R :> R.
Proof. by rewrite divr_ge0// ler0n. Qed.

Lemma scc_ge0 (m : nat) : 0 <= (m.+2)%:R^-1 :> R.
Proof. by rewrite invr_ge0 ler0n. Qed.

Definition scl (m : nat) : {nonneg R} := NngNum (scl_ge0 m).
Definition scc (m : nat) : {nonneg R} := NngNum (scc_ge0 m).

(** [λₘ + (1 − λₘ) = 1] as reals. *)
Lemma scl_scc_num (m : nat) : (scl m)%:num + (scc m)%:num = 1.
Proof.
by rewrite /= -[X in _ + X]mul1r -mulrDl natr1 mulfV.
Qed.

Lemma scl_le1 (m : nat) : (scl m)%:num <= 1.
Proof.
rewrite -(scl_scc_num m) lerDl; exact: nngnum_ge0.
Qed.

Lemma scl_num (m : nat) : (scl m)%:num = 1 - (scc m)%:num.
Proof. by rewrite -(scl_scc_num m) addrK. Qed.

(** Monotonicity of the ratios: [λₘ ≤ λₘ₊₁] (equivalently [comp] ↓). *)
Lemma scl_mono (m : nat) : (scl m)%:num <= (scl m.+1)%:num.
Proof.
by rewrite !scl_num lerB// lef_pV2 ?posrE ?ltr0n// ler_nat ltnS leqnSn.
Qed.

Local Open Scope precone_scope.

(** The chain [m ↦ λₘ ·: z]. *)
Lemma scchain_mono (z : P) (m : nat) : scl m *: z <=p scl m.+1 *: z.
Proof.
have d_ge0 : (0 <= (scl m.+1)%:num - (scl m)%:num)%R.
  by rewrite subr_ge0; exact: scl_mono.
exists (NngNum d_ge0 *: z).
rewrite -precone_scale_DAl; congr (_ *: z); apply: val_inj => /=.
by rewrite addrC subrK.
Qed.

Lemma scchain_ub1 (z : P) :
  cone_norm z <= 1 -> forall m, cone_norm (scl m *: z) <= 1.
Proof.
move=> Hz m; rewrite cone_normh -[1]mulr1.
by apply: ler_pM;
  [exact: nngnum_ge0|exact: cone_norm_ge0|exact: scl_le1|exact: Hz].
Qed.

(** [z] is an upper bound of the chain: [λₘ ·: z ≤p z]. *)
Lemma scchain_le (z : P) (m : nat) : scl m *: z <=p z.
Proof.
exists (scc m *: z).
rewrite -precone_scale_DAl -[z in LHS]precone_scale_1.
by congr (_ *: z); apply: val_inj => /=; rewrite scl_scc_num.
Qed.

(** **The scaling-chain supremum.** [cone_sup_ball (m ↦ λₘ ·: z) = z]. *)
Lemma scale_chain_sup (z : P) (Hz : cone_norm z <= 1) :
  cone_sup_ball (fun m => scl m *: z) (scchain_mono z) (scchain_ub1 Hz) = z.
Proof.
set s := cone_sup_ball _ _ _.
have s_le_z : s <=p z by apply: cone_sup_ball_lub => m; exact: scchain_le.
apply/esym/precone_le_anti => //.
(* Remains: [z ≤p s].  Write [z = s + t] and show [‖t‖ = 0]. *)
have [t Ht] := s_le_z.
have t_bound : forall m, cone_norm t <= m.+2%:R^-1 * cone_norm z.
  move=> m.
  have [w Hw] : scl m *: z <=p s by exact: cone_sup_ball_ub.
  (* [z = λₘ z + (1−λₘ) z] and [z = (λₘ z + w) + t], so by cancel
     [(1−λₘ) z = w + t], hence [t ≤p (1−λₘ) z]. *)
  have E1 : z = scl m *: z + scc m *: z.
    rewrite -precone_scale_DAl -[z in LHS]precone_scale_1.
    by congr (_ *: z); apply: val_inj => /=; rewrite scl_scc_num.
  have E2 : z = scl m *: z + (w + t).
    by rewrite [z in LHS]Ht Hw -precone_addA.
  have Heq : scc m *: z = w + t.
    by apply: (@precone_cancel _ _ (scl m *: z)); rewrite -E1 -E2.
  have t_le : t <=p scc m *: z by rewrite Heq precone_addC; exists w.
  by have := cone_normp _ _ t_le; rewrite cone_normh.
(* Sharpen using [‖z‖ ≤ 1]: [‖t‖ ≤ 1/(m+2)], which → 0. *)
have tb : forall m, cone_norm t <= m.+2%:R^-1.
  move=> m; apply: le_trans (t_bound m) _; rewrite -[X in _ <= X]mulr1.
  by rewrite ler_wpM2l// invr_ge0 ler0n.
have t_norm0 : (cone_norm t <= 0)%R.
  apply/unstable.ler_gtP => e e_pos.
  have e_pos' : (0 < e^-1)%R by rewrite invr_gt0.
  have HN := archi_boundP (ltW e_pos').
  set N := Num.bound e^-1 in HN.
  apply: le_trans (tb N) _.
  rewrite -[e]invrK lef_pV2 ?posrE ?invr_gt0 ?ltr0n//.
  apply: le_trans (ltW HN) _; rewrite ler_nat.
  by rewrite (leq_trans (leqnSn N)) ?leqnSn.
have t0 : t = 0.
  by apply: cone_normz; apply/le_anti; rewrite t_norm0 cone_norm_ge0.
by rewrite Ht t0 precone_addr0; exact: precone_le_refl.
Qed.

End ScaleChain.

Arguments scl {R} m.
Arguments scc {R} m.
Arguments scl_le1 {R} m.
Arguments scl_num {R} m.
Arguments scale_chain_sup {R P} z Hz.

(** ** Radius-aware finite-sum / supremum commutation (lub direction)

    The boundary bridge needs to pass the open-ball inequality to the
    limit through *finite* [\sumP] sums of chains whose images escape the
    unit ball (the values [f (λₘ ·: z_I)] have norm up to [‖f z_I‖ > 1]).
    The unit-ball [SumSup] of [stablehom.v] does not apply; we re-derive
    here the only half we need, the *least-upper-bound* direction, at a
    common image radius [M] using the radius-aware binary diagonal-sup
    identity [sup_at_addD] (totmono.v).  This mirrors [sum_cone_sup_lub]
    of [stablehom.v] line for line, with [cone_sup_ball] replaced by
    [cone_sup_at] and a generic radius. *)

Section SumSupAt.
Variable R : realType.
Variable P : coneType R.
Variable T : finType.
Variable c : T -> nat -> P.
Variable M : {nonneg R}.
Hypothesis cch : forall i n, precone_le (c i n) (c i n.+1).
Hypothesis cubM : forall i n, cone_norm (c i n) <= M%:num.
Hypothesis Mpos : (0 < M%:num)%R.
Local Open Scope precone_scope.

(** Per-index supremum [d i := cone_sup_at (c i)]. *)
Definition dsup (i : T) : P := cone_sup_at (cch i) (cubM i) Mpos.

(** The diagonal sum chain over [A]. *)
Definition dchain (A : {set T}) (n : nat) : P :=
  \big[precone_add/precone_zero]_(i in A) c i n.

Lemma dchain_ch (A : {set T}) n : dchain A n <=p dchain A n.+1.
Proof.
rewrite /dchain; elim/big_rec2: _; first exact: precone_le_refl.
move=> i y1 y2 _ Hy; apply: precone_le_trans (precone_add_le_r _ (cch i n)).
exact: precone_add_le_l.
Qed.

(** Norm of the diagonal sum: [≤ #|A| · M]. *)
Lemma dchain_norm (A : {set T}) n :
  cone_norm (dchain A n) <= #|A|%:R * M%:num.
Proof.
rewrite /dchain.
have -> : #|A|%:R * M%:num = \sum_(i in A) M%:num.
  by rewrite sumr_const mulr_natl.
elim/big_rec2: _ => [|i y1 y2 _ Hy]; first by rewrite cone_norm0.
by apply: le_trans (cone_normt _ _) _; rewrite lerD// cubM.
Qed.

(** A strictly-positive radius dominating [#|A| · M]: use [(#|A|+1)·M]. *)
Lemma dradius_ge0 (A : {set T}) : (0 <= #|A|.+1%:R * M%:num :> R)%R.
Proof. by rewrite mulr_ge0 ?ler0n// ltW. Qed.

Definition dradius (A : {set T}) : {nonneg R} := NngNum (dradius_ge0 A).

Lemma dradius_pos (A : {set T}) : (0 < (dradius A)%:num)%R.
Proof. by rewrite /dradius/= mulr_gt0 ?ltr0n. Qed.

Lemma dchain_radius (A : {set T}) n :
  cone_norm (dchain A n) <= (dradius A)%:num.
Proof.
apply: le_trans (dchain_norm A n) _.
by rewrite /dradius/= ler_wpM2r ?ltW// ltr_nat.
Qed.

(** The diagonal element is below the finite sum of per-index suprema. *)
Lemma dsum_ub (A : {set T}) n :
  dchain A n <=p \big[precone_add/precone_zero]_(i in A) dsup i.
Proof.
rewrite /dchain; elim/big_rec2: _; first exact: precone_le_refl.
move=> i y1 y2 _ Hy.
apply: (precone_le_trans (y := dsup i + y2)).
  by apply: precone_add_le_r; exact: cone_sup_at_ub.
by apply: precone_add_le_l.
Qed.

(** **Lub direction.** [Σ_A d i] is the least upper bound of [dchain A]. *)
Lemma dsum_lub (A : {set T}) (y : P) :
  (forall n, dchain A n <=p y) ->
  \big[precone_add/precone_zero]_(i in A) dsup i <=p y.
Proof.
move: y; have [N] := ubnP #|A|; elim: N A => // N IH A.
rewrite ltnS => HA y Hy.
case: (set_0Vmem A) => [-> | [a aA]].
  by rewrite big_set0; exact: precone_le0.
have aA' : a \notin (A :\ a) by rewrite !inE eqxx.
have AE : A = a |: (A :\ a) by rewrite finset.setD1K.
have cardA' : (#|A :\ a| < N)%N.
  by apply: leq_trans HA; rewrite (cardsD1 a A) aA add1n.
set A' := A :\ a in aA' cardA' *.
have splitE n : dchain A n = c a n + dchain A' n.
  by rewrite /dchain {1}AE (big_setU1 _ aA').
set Mb : {nonneg R} := dradius A.
have Mbpos := dradius_pos A.
have ca_ubMb n : cone_norm (c a n) <= Mb%:num.
  apply: le_trans (cubM a n) _; rewrite /Mb/= ler_peMl ?ltW//.
  by rewrite ltr1n ltnS card_gt0; apply/set0Pn; exists a.
have sumA'_ubMb n : cone_norm (dchain A' n) <= Mb%:num.
  apply: le_trans (dchain_norm A' n) _; rewrite /Mb/= ler_wpM2r ?ltW//.
  by rewrite ltr_nat ltnS; apply: subset_leq_card; exact: subsetDl.
have dch n : c a n + dchain A' n <=p c a n.+1 + dchain A' n.+1.
  apply: precone_le_trans (precone_add_le_r _ (cch a n)).
  exact: precone_add_le_l (dchain_ch A' n).
have dubMb n : cone_norm (c a n + dchain A' n) <= Mb%:num.
  by rewrite -splitE; exact: dchain_radius.
(* [dsup a = cone_sup_at (c a)] at radius [Mb] (radius-independence). *)
have caE : dsup a = cone_sup_at (cch a) ca_ubMb Mbpos.
  by rewrite /dsup; apply: cone_sup_at_indep.
(* The [A']-sum is the [cone_sup_at] of its diagonal chain (via IH). *)
have sumA'E : \big[precone_add/precone_zero]_(i in A') dsup i =
              cone_sup_at (dchain_ch A') sumA'_ubMb Mbpos.
  apply: precone_le_anti.
  - by apply: IH => // n; exact: cone_sup_at_ub.
  - by apply: cone_sup_at_lub => n; exact: dsum_ub.
rewrite AE (big_setU1 _ aA') caE sumA'E.
have key : cone_sup_at (cch a) ca_ubMb Mbpos
           + cone_sup_at (dchain_ch A') sumA'_ubMb Mbpos
         = cone_sup_at dch dubMb Mbpos.
  by rewrite (sup_at_addD (cch a) ca_ubMb (dchain_ch A') sumA'_ubMb dch dubMb).
change (precone_add (cone_sup_at (cch a) ca_ubMb Mbpos)
          (cone_sup_at (dchain_ch A') sumA'_ubMb Mbpos) <=p y).
rewrite key; apply: cone_sup_at_lub => n.
by apply: precone_le_trans (Hy n); rewrite splitE; exact: precone_le_refl.
Qed.

End SumSupAt.

Arguments dsup {R P T} c {M} cch cubM Mpos i.
Arguments dchain {R P T} c A n.
Arguments dsum_lub {R P T c M} cch cubM Mpos A y.

(** ** Theorem 7.19 converse — the closed-ball bridge

    Combining the scaling-chain supremum [scale_chain_sup], the
    radius-aware finite-sum lub [dsum_lub] and ω-continuity, we lift the
    open-ball converse [conv_strict] to the *closed* ball, obtaining the
    full [is_totmono] for a stable [f] that is [k]-increasing for all
    [k].  This is the boundary half of Theorem 7.19. *)

Section ConvClosed.
Variable R : realType.
Variables B C : coneType R.
Variable f : B -> C.
Local Open Scope precone_scope.

(** Scaling commutes with the (7.1) argument. *)
Lemma tm_arg_scale (n : nat) (r : {nonneg R}) (x : B) (u : 'I_n -> B)
    (I : {set 'I_n}) :
  tm_arg (r *: x) (fun i => r *: u i) I = r *: tm_arg x u I.
Proof. by rewrite /tm_arg precone_scale_DAr sumP_scale. Qed.

(** **Closed-ball converse / Theorem 7.19.** A stable [f] that is
    [k]-increasing for all [k] is totally monotonic. *)
Lemma is_n_increasing_totmono :
  (forall k, is_n_increasing k f) -> is_scott_continuous_unit f ->
  is_totmono f.
Proof.
move=> Hinc Hscott n x u Hz.
set z := x + \big[precone_add/precone_zero]_(i : 'I_n) u i.
(* Each [z_I = tm_arg x u I] is in the unit ball. *)
have HzI (I : {set 'I_n}) : cone_norm (tm_arg x u I) <= 1.
  apply: le_trans Hz; apply: cone_normp; rewrite /tm_arg /z.
  by apply: precone_add_le_l; exact: sumP_sub_le.
(* The scaled chain [c I m := f (λₘ ·: z_I)]. *)
pose c (I : {set 'I_n}) (m : nat) := f (scl m *: tm_arg x u I).
(* Common image radius [M := Σ_I ‖f z_I‖ + 1 > 0]. *)
have M_ge0 : (0 <= \sum_(I : {set 'I_n}) cone_norm (f (tm_arg x u I)) + 1)%R.
  by rewrite addr_ge0 ?ler01// sumr_ge0// => I _; exact: cone_norm_ge0.
pose M : {nonneg R} := NngNum M_ge0.
have Mpos : (0 < M%:num)%R.
  rewrite /M/=; apply: lt_le_trans ltr01 _.
  by rewrite lerDr sumr_ge0// => I _; exact: cone_norm_ge0.
have Hi : is_increasing f by have := Hinc 0%N.
(* [c I] is an increasing chain. *)
have cch I m : c I m <=p c I m.+1.
  rewrite /c; have [w Hw] := scchain_mono (tm_arg x u I) m.
  rewrite Hw; apply: Hi; rewrite -Hw.
  by apply: le_trans (scchain_ub1 (HzI I) m.+1); rewrite Hw; exact: lexx.
(* [c I m] has norm ≤ ‖f z_I‖ ≤ M (via [f] increasing, [λₘ z_I ≤p z_I]). *)
have c_le_fz I m : c I m <=p f (tm_arg x u I).
  rewrite /c; have [w Hw] := scchain_le (tm_arg x u I) m.
  by rewrite [X in _ <=p f X]Hw; apply: Hi; rewrite -Hw; exact: HzI.
have cubM I m : cone_norm (c I m) <= M%:num.
  apply: le_trans (cone_normp _ _ (c_le_fz I m)) _; rewrite /M/=.
  apply: le_trans (_ : \sum_(J : {set 'I_n})
      cone_norm (f (tm_arg x u J)) <= _)%R; last by rewrite lerDl ler01.
  by rewrite (bigD1 I)//= lerDl sumr_ge0// => J _; exact: cone_norm_ge0.
(* Per-index supremum is [f z_I], by ω-continuity + [scale_chain_sup]. *)
have dsup_eq I : dsup c cch cubM Mpos I = f (tm_arg x u I).
  have key := Hscott M (fun m => scl m *: tm_arg x u I)
    (scchain_mono _) (scchain_ub1 (HzI I)) (cch I) (cubM I) Mpos.
  by rewrite /dsup -key scale_chain_sup.
(* For each [m], the open-ball converse on the scaled config. *)
have step m : dchain c (Pneg n) m <=p dchain c (Ppos n) m.
  have sumE : \big[precone_add/precone_zero]_(i : 'I_n) (scl m *: u i)
            = scl m *: \big[precone_add/precone_zero]_(i : 'I_n) u i.
    by rewrite (big_morph _ (precone_scale_DAr (scl m)) (precone_scale_0r _)).
  have Hlt : cone_norm (scl m *: x +
      \big[precone_add/precone_zero]_(i : 'I_n) (scl m *: u i)) < 1.
    rewrite sumE -precone_scale_DAr cone_normh.
    apply: le_lt_trans (_ : (scl m)%:num * 1 < 1)%R.
      by rewrite ler_wpM2l ?nngnum_ge0//.
    by rewrite mulr1 scl_num ltrBlDl ltrDr invr_gt0 ltr0n.
  have H := conv_strict f Hinc n (scl m *: x) (fun i => scl m *: u i) Hlt.
  rewrite /dchain /c.
  under eq_bigr => I _ do rewrite -tm_arg_scale.
  under [X in _ <=p X]eq_bigr => I _ do rewrite -tm_arg_scale.
  exact: H.
(* Assemble: rewrite goal through [dsup_eq] and apply [dsum_lub]. *)
under eq_bigr => I _ do rewrite -(dsup_eq I).
under [X in _ <=p X]eq_bigr => I _ do rewrite -(dsup_eq I).
apply: (dsum_lub cch cubM Mpos) => m.
apply: precone_le_trans (step m) _.
exact: dsum_ub.
Qed.

End ConvClosed.

Arguments is_n_increasing_totmono {R B C} f.

(** ** [totmono_shift] — shift preserves total monotonicity — Paper §7.3
       (txt 3561, the "easy observation" of Lemma 7.20)

    If [g : B_B → C] is totally monotonic and [u ∈ B_B] (strict interior,
    [‖u‖ < 1]), then the shift [gᵤ : B_u → C], [gᵤ(x) := g(lc_val x + u)],
    is totally monotonic.  The (7.1) instance of [gᵤ] at a [B_u]-config
    [(xL, w⃗L)] is, through [lc_val], the (7.1) instance of [g] at the
    [B]-config [(lc_val xL + u, lc_val ∘ w⃗L)]; its norm side-condition is
    the local-cone step-[1] bound [lc_step1] (the [B_u]-ball bound
    transported to [B]), exactly as in [totmono_Delta1]/[Delta1_inc]. *)

Section TotmonoShift.
Variable R : realType.
Variables B C : coneType R.
Local Open Scope precone_scope.

Lemma totmono_shift (g : B -> C) (u : B) (Hu : cone_norm u < 1) :
  is_totmono g ->
  @is_totmono R (lc_coneType Hu) C (fun x => g (lc_val x + u)).
Proof.
move=> Hg n xL wL Hnorm.
(* Read each [gᵤ]-argument as a [g]-argument on the shifted [B]-config. *)
have argE (I : {set 'I_n}) :
    g (lc_val (tm_arg xL wL I) + u) =
    g (tm_arg (lc_val xL + u) (fun i => lc_val (wL i)) I).
  congr g; rewrite /tm_arg lc_valD lc_val_big.
  by rewrite -precone_addA (precone_addC _ u) precone_addA.
(* The shifted [B]-config is in the unit ball, by [lc_step1]. *)
have Hc : cone_norm ((lc_val xL + u) +
    \big[precone_add/precone_zero]_(i : 'I_n) lc_val (wL i)) <= 1.
  have key := lc_step1 Hu (w := xL +
    \big[precone_add/precone_zero]_(i : 'I_n) wL i) Hnorm.
  rewrite lc_valD lc_val_big in key.
  by rewrite (precone_addC (lc_val xL) u) -precone_addA.
have := Hg n (lc_val xL + u) (fun i => lc_val (wL i)) Hc.
under eq_bigr => I _ do rewrite -argE.
by under [X in _ <=p X]eq_bigr => I _ do rewrite -argE.
Qed.

(** The dominated-shift variant used by Lemma 7.20.  The shift direction
    [s] is *below* the local-cone centre [S = Σᵢ uᵢ] ([s ≤p S]); then the
    shift [gₛ : B_S → C], [gₛ(x) := g(lc_val x + s)], is totally monotonic
    on the *same* cone [B_S].  This is what lets [Δεf(u⃗)] — a sum of the
    shifts [g_{s_I}] by the partial sums [s_I = Σ_{i∈I} uᵢ ≤p S] — be read
    as a sum of totally monotonic maps on [B_S] (no cone restriction). *)
Lemma totmono_shift_le (g : B -> C) (S s : B) (Hs : cone_norm S < 1)
    (Hsle : s <=p S) :
  is_totmono g ->
  @is_totmono R (lc_coneType Hs) C (fun x => g (lc_val x + s)).
Proof.
move=> Hg n xL wL Hnorm.
have argE (I : {set 'I_n}) :
    g (lc_val (tm_arg xL wL I) + s) =
    g (tm_arg (lc_val xL + s) (fun i => lc_val (wL i)) I).
  congr g; rewrite /tm_arg lc_valD lc_val_big.
  by rewrite -precone_addA (precone_addC _ s) precone_addA.
(* The shifted [B]-config is in the unit ball: dominate [s] by [S] and
   reuse the [lc_step1] bound at the centre [S]. *)
have Hc : cone_norm ((lc_val xL + s) +
    \big[precone_add/precone_zero]_(i : 'I_n) lc_val (wL i)) <= 1.
  have key := lc_step1 Hs (w := xL +
    \big[precone_add/precone_zero]_(i : 'I_n) wL i) Hnorm.
  rewrite lc_valD lc_val_big in key.
  apply: le_trans key; apply: cone_normp.
  rewrite (precone_addC (lc_val xL) s) -precone_addA.
  set T := (lc_val xL + _).
  by apply: precone_add_le_r.
have := Hg n (lc_val xL + s) (fun i => lc_val (wL i)) Hc.
under eq_bigr => I _ do rewrite -argE.
by under [X in _ <=p X]eq_bigr => I _ do rewrite -argE.
Qed.

End TotmonoShift.

Arguments totmono_shift {R B C} g u Hu.
Arguments totmono_shift_le {R B C} g S s Hs Hsle.

(** ** Lemma 7.20 — [Δ⁺f(u⃗)], [Δ⁻f(u⃗)], [Δf(u⃗)] totally monotonic
       — Paper §7.3 (txt 3558)

    For [f] totally monotonic and a family [u⃗ ∈ Bⁿ] with [Σᵢ uᵢ ∈ B_B]
    (strict interior), the three difference operators are totally
    monotonic on [B_u⃗ = local_cone (Σᵢ uᵢ)]:

    - [Δεf(u⃗)] is the [\sumP] over [Pε(n)] of the shifts
      [g_{s_I}(x) = f(lc_val x + s_I)] by the partial sums
      [s_I = Σ_{i∈I} uᵢ ≤p Σᵢ uᵢ].  Each shift is totally monotonic on
      [B_u⃗] by [totmono_shift_le], and a finite [\sumP] of totally
      monotonic maps is totally monotonic ([totmono_bigP]).
    - [Δf(u⃗)] needs, in addition to total monotonicity, ω-continuity.  We
      record the [Δε] clauses (which need only [is_totmono f]) and the
      pointwise-difference reading; the [Δf(u⃗)] clause is delivered in
      [stable/compose.v] ([totmono_Delta], via the [SD_concat] identity,
      and [scott_Delta] for the ω-continuity half). *)

Section Lemma720.
Variable R : realType.
Variables B C : coneType R.
Variable f : B -> C.
Hypothesis Hf : is_totmono f.
Local Open Scope precone_scope.

(** A finite [\sumP] of totally monotonic maps [P → Q] is totally
    monotonic.  Pointwise [(\sumP_I g_I) x = \sumP_I (g_I x)] (the
    eval-at-[x] precone homomorphism), so total monotonicity transfers
    summand by summand through [totmono_add] / [totmono_zero]. *)
Lemma totmono_bigP (P Q : coneType R) (T : finType) (A : {set T})
    (g : T -> P -> Q) :
  (forall i, i \in A -> is_totmono (g i)) ->
  is_totmono (\big[stm_add/stm_zero P Q]_(i in A) g i).
Proof.
move=> Hg; elim/big_ind: _ => [|f1 f2 H1 H2|i iA].
- exact: totmono_zero.
- exact: totmono_add H1 H2.
- exact: Hg.
Qed.

(** [Δ⁺f(u⃗)] is totally monotonic on [B_u⃗]. *)
Lemma totmono_Delta_pos (n : nat) (u : 'I_n -> B)
    (Hs : cone_norm (\big[precone_add/precone_zero]_(i : 'I_n) u i) < 1) :
  @is_totmono R (lc_coneType Hs) C (Delta_pos f u).
Proof.
have shle (I : {set 'I_n}) :
    is_totmono (fun x : lc_coneType Hs =>
      f (lc_val x + \big[precone_add/precone_zero]_(i in I) u i)).
  by apply: totmono_shift_le => //; exact: sumP_sub_le.
have := @totmono_bigP (lc_coneType Hs) C _ (Ppos n)
  (fun I (x : lc_coneType Hs) =>
     f (lc_val x + \big[precone_add/precone_zero]_(i in I) u i))
  (fun I _ => shle I).
congr is_totmono; apply/funext => x.
by rewrite /Delta_pos /Delta_arg; elim/big_rec2: _ => // I s s' _ <-.
Qed.

(** [Δ⁻f(u⃗)] is totally monotonic on [B_u⃗]. *)
Lemma totmono_Delta_neg (n : nat) (u : 'I_n -> B)
    (Hs : cone_norm (\big[precone_add/precone_zero]_(i : 'I_n) u i) < 1) :
  @is_totmono R (lc_coneType Hs) C (Delta_neg f u).
Proof.
have shle (I : {set 'I_n}) :
    is_totmono (fun x : lc_coneType Hs =>
      f (lc_val x + \big[precone_add/precone_zero]_(i in I) u i)).
  by apply: totmono_shift_le => //; exact: sumP_sub_le.
have := @totmono_bigP (lc_coneType Hs) C _ (Pneg n)
  (fun I (x : lc_coneType Hs) =>
     f (lc_val x + \big[precone_add/precone_zero]_(i in I) u i))
  (fun I _ => shle I).
congr is_totmono; apply/funext => x.
by rewrite /Delta_neg /Delta_arg; elim/big_rec2: _ => // I s s' _ <-.
Qed.

End Lemma720.

Arguments totmono_bigP {R P Q T} A g.
Arguments totmono_Delta_pos {R B C} f Hf {n} u Hs.
Arguments totmono_Delta_neg {R B C} f Hf {n} u Hs.

(** ** B-core difference [SD] and the cons recurrence — engine for 7.21/7.22

    [Delta f u x] is defined purely from [Spos f n u (lc_val x)] and
    [Sneg f n u (lc_val x)] (the pointwise difference where [Sneg ≤ Spos]),
    so it depends on [x] only through [lc_val x].  We make this explicit
    by a *B-side* difference [SD f n u xb] — the cone difference
    [Spos ⊖ Sneg] at a bare centre [xb : B] — and show [Delta f u x =
    SD f n u (lc_val x)] ([SD_Delta]).  This decouples the difference
    recurrences from the local-cone carrier, so Lemmas 7.21 and 7.22 are
    proved as pure [B]-side identities ([SD_cons]), with no cone cast. *)

Section SDelta.
Variable R : realType.
Variables B C : coneType R.
Variable f : B -> C.
Local Open Scope precone_scope.

(** The B-side cone difference [Spos ⊖ Sneg] at a centre [xb], [0] off the
    region where the order [Sneg ≤ Spos] holds. *)
Definition SD (n : nat) (u : 'I_n -> B) (xb : B) : C :=
  match pselect (Sneg f n u xb <=p Spos f n u xb) with
  | left p => projT1 (cid p)
  | right _ => precone_zero
  end.

(** Defining equation: where [Sneg ≤ Spos], [Spos = Sneg + SD]. *)
Lemma SD_E (n : nat) (u : 'I_n -> B) (xb : B) :
  Sneg f n u xb <=p Spos f n u xb ->
  Spos f n u xb = Sneg f n u xb + SD u xb.
Proof.
move=> p; rewrite /SD; case: pselect => [p'|]; last by [].
exact: (projT2 (cid p')).
Qed.

(** [Delta f u x] is the B-side difference at the centre [lc_val x]. *)
Lemma SD_Delta (n : nat) (u : 'I_n -> B)
    (x : local_cone (\big[precone_add/precone_zero]_(i : 'I_n) u i)) :
  Delta f u x = SD u (lc_val x).
Proof.
by rewrite /Delta /SD Delta_pos_Spos Delta_neg_Sneg.
Qed.

(** The three [Sneg ≤ Spos] (well-definedness) facts for the [(u :: w)]
    config and its two sub-configs at centres [xb] and [xb + u], from
    total monotonicity and the unit-ball bound on the full sum. *)
Lemma Sle_xb (Hf : is_totmono f) (n : nat) (u : B) (w : 'I_n -> B) (xb : B) :
  cone_norm (xb +
     \big[precone_add/precone_zero]_(i : 'I_n.+1) vcons u w i) <= 1 ->
  Sneg f n w xb <=p Spos f n w xb.
Proof.
move=> Hc; apply: (Sneg_le_Spos Hf); apply: le_trans Hc.
apply: cone_normp; rewrite sum_vcons.
by apply: precone_add_le_l; exists u; rewrite precone_addC.
Qed.

Lemma Sle_xbu (Hf : is_totmono f) (n : nat) (u : B) (w : 'I_n -> B) (xb : B) :
  cone_norm (xb +
     \big[precone_add/precone_zero]_(i : 'I_n.+1) vcons u w i) <= 1 ->
  Sneg f n w (xb + u) <=p Spos f n w (xb + u).
Proof.
move=> Hc; apply: (Sneg_le_Spos Hf); apply: le_trans Hc.
apply: cone_normp; rewrite sum_vcons precone_addA.
exact: precone_le_refl.
Qed.

(** **The B-side cons recurrence (Lemma 7.22, first identity).**
    [SD f w (xb + u) = SD f w xb + SD f (u :: w) xb].  Cancel the common
    summand [Sn(xb+u) + Sn(xb)] in the three defining equations. *)
Lemma SD_cons (Hf : is_totmono f) (n : nat) (u : B) (w : 'I_n -> B) (xb : B)
    (Hc : cone_norm (xb +
       \big[precone_add/precone_zero]_(i : 'I_n.+1) vcons u w i) <= 1) :
  SD w (xb + u) = SD w xb + SD (vcons u w) xb.
Proof.
have D1 := SD_E (Sle_xbu Hf Hc).
have D0 := SD_E (Sle_xb Hf Hc).
have Dc := SD_E (Sneg_le_Spos Hf Hc).
rewrite Spos_recur Sneg_recur in Dc.
(* D1: Sp1 = Sn1 + d1; D0: Sp0 = Sn0 + d0;
   Dc: Sp1 + Sn0 = (Sn1 + Sp0) + dc.  Substitute D1, D0 and cancel. *)
rewrite D1 D0 in Dc.
set Sn1 := Sneg f n w (xb + u) in Dc.
set Sn0 := Sneg f n w xb in Dc.
set d1 := SD w (xb + u) in Dc *.
set d0 := SD w xb in Dc *.
set dc := SD (vcons u w) xb in Dc *.
apply: (@precone_cancel _ _ (Sn1 + Sn0)).
rewrite -[Sn1 + Sn0 + d1]precone_addA [Sn0 + d1]precone_addC precone_addA.
rewrite -[Sn1 + Sn0 + (d0 + dc)]precone_addA (precone_addA Sn0 d0 dc).
rewrite precone_addA; exact: Dc.
Qed.

(** [SD] at arity [0] is just [f] at the centre. *)
Lemma SD0 (u : 'I_0 -> B) (xb : B) : SD u xb = f xb.
Proof.
have HSp : Spos f 0 u xb = f xb.
  by rewrite /Spos Ppos0 big_set1 big_set0 precone_addr0.
have HSn : Sneg f 0 u xb = 0 by rewrite /Sneg Pneg0 big_set0.
have le : Sneg f 0 u xb <=p Spos f 0 u xb.
  by rewrite HSn; exact: precone_le0.
by have := SD_E le; rewrite HSp HSn precone_add0 => <-.
Qed.

(** **Lemma 7.21 (B-side form).** [SD u⃗ xb ≤p f(xb + Σᵢ uᵢ)], for [f]
    totally monotonic.  Induction on the arity: at [0], [SD = f xb]; at
    [n+1], [SD (u₀ :: w) xb ≤p SD w (xb + u₀)] (the [SD_cons] witness) and
    the IH at the shifted centre [xb + u₀] bounds the latter by
    [f((xb + u₀) + Σ wᵢ) = f(xb + Σ (u₀ :: w))]. *)
Lemma SD_le (Hf : is_totmono f) (n : nat) (u : 'I_n -> B) (xb : B) :
  cone_norm (xb + \big[precone_add/precone_zero]_(i : 'I_n) u i) <= 1 ->
  SD u xb <=p f (xb + \big[precone_add/precone_zero]_(i : 'I_n) u i).
Proof.
elim: n u xb => [|n IHn] u xb Hc.
  rewrite SD0 big_ord0 precone_addr0; exact: precone_le_refl.
rewrite [u]vcons_eta; set u0 := u ord0; set w := (fun i => u (lift ord0 i)).
have Hc' : cone_norm (xb +
    \big[precone_add/precone_zero]_(i : 'I_n.+1) vcons u0 w i) <= 1.
  by move: Hc; rewrite [u]vcons_eta -/u0 -/w.
have step := SD_cons Hf Hc'.
have IH : SD w (xb + u0) <=p
    f ((xb + u0) + \big[precone_add/precone_zero]_(i : 'I_n) w i).
  apply: IHn; apply: le_trans Hc'; apply: cone_normp.
  by rewrite sum_vcons precone_addA; exact: precone_le_refl.
apply: (precone_le_trans (y := SD w (xb + u0))).
  by rewrite step precone_addC; exists (SD w xb).
by rewrite sum_vcons precone_addA; exact: IH.
Qed.

(** **Lemma 7.22 (second identity, B-side form).**
    [SD (u+v :: w) xb = SD (u :: w) xb + SD (v :: w) (xb + u)].  Both sides
    telescope through [SD_cons]: adding the two cons identities at heads
    [u] (centre [xb]) and [v] (centre [xb+u]) gives
    [SD w (xb+u+v) = SD w xb + SD (u :: w) xb + SD (v :: w) (xb+u)], while
    the cons identity at head [u+v] gives
    [SD w (xb+(u+v)) = SD w xb + SD (u+v :: w) xb]; cancel [SD w xb]. *)
Lemma SD_add (Hf : is_totmono f) (n : nat) (u v : B) (w : 'I_n -> B) (xb : B)
    (Hc : cone_norm (xb +
       \big[precone_add/precone_zero]_(i : 'I_n.+1) vcons (u + v) w i) <= 1) :
  SD (vcons (u + v) w) xb =
  SD (vcons u w) xb + SD (vcons v w) (xb + u).
Proof.
(* Unit-ball bounds for the three cons applications. *)
have HcS : cone_norm (xb + (u + (v +
    \big[precone_add/precone_zero]_(i : 'I_n) w i))) <= 1.
  by move: Hc; rewrite sum_vcons -precone_addA.
have Huv : cone_norm (xb +
    \big[precone_add/precone_zero]_(i : 'I_n.+1) vcons (u + v) w i) <= 1
  by [].
have Hu : cone_norm (xb +
    \big[precone_add/precone_zero]_(i : 'I_n.+1) vcons u w i) <= 1.
  apply: le_trans HcS; apply: cone_normp; rewrite sum_vcons.
  apply: precone_add_le_l; apply: precone_add_le_l.
  by exists v; rewrite precone_addC.
have Hv : cone_norm ((xb + u) +
    \big[precone_add/precone_zero]_(i : 'I_n.+1) vcons v w i) <= 1.
  apply: le_trans HcS; apply: cone_normp; rewrite sum_vcons.
  by rewrite -precone_addA; exact: precone_le_refl.
(* The three cons identities. *)
have Euv := SD_cons Hf Huv.
have Eu := SD_cons Hf Hu.
have Ev := SD_cons Hf Hv.
(* [Euv]: SD w (xb+(u+v)) = SD w xb + SD (u+v::w) xb;  reassociate the
   centre to [xb+u+v] so the [Ev] telescope lines up. *)
rewrite precone_addA in Euv.
apply: (@precone_cancel _ _ (SD w xb)).
by rewrite -Euv [RHS]precone_addA -Eu -Ev.
Qed.

End SDelta.

Arguments SD {R B C} f {n} u xb.
Arguments SD_E {R B C} f {n} u xb.
Arguments SD_Delta {R B C} f {n} u x.
Arguments SD0 {R B C} f u xb.
Arguments SD_cons {R B C} f Hf {n} u w xb Hc.
Arguments SD_le {R B C} f Hf {n} u xb.
Arguments SD_add {R B C} f Hf {n} u v w xb Hc.

(** ** Lemma 7.21 (operator form) — Paper §7.3 (txt 3565)

    [Δf(u⃗)(x) ≤p f(lc_val x + Σᵢ uᵢ)] on the unit ball of [B_u⃗] (strict
    interior centre [Σᵢ uᵢ]).  Read off from the B-side bound [SD_le] via
    [SD_Delta], with the [B]-side norm bound [‖lc_val x + Σᵢ uᵢ‖ ≤ 1]
    supplied by [lc_step1]. *)
Section Lemma721.
Variable R : realType.
Variables B C : coneType R.
Variable f : B -> C.
Hypothesis Hf : is_totmono f.
Local Open Scope precone_scope.

Lemma Delta_le (n : nat) (u : 'I_n -> B)
    (Hs : cone_norm (\big[precone_add/precone_zero]_(i : 'I_n) u i) < 1)
    (x : local_cone (\big[precone_add/precone_zero]_(i : 'I_n) u i))
    (Hx : lc_norm x <= 1) :
  Delta f u x <=p
  f (lc_val x + \big[precone_add/precone_zero]_(i : 'I_n) u i).
Proof.
rewrite SD_Delta; apply: SD_le => //.
rewrite precone_addC; exact: (lc_step1 Hs Hx).
Qed.

End Lemma721.

Arguments Delta_le {R B C} f Hf {n} u Hs x.

(** ** Lemma 7.23 (base instance) — the telescoping identity — Paper §7.3
       (txt 3687)

    The paper's [Δf(u⃗+v⃗)(x+u)] identity, derived "by simple computations
    using Lemma 7.22".  On the [B]-side it decomposes into

      [SD (u⃗+v⃗)(xb+u) = SD (u⃗+v⃗)(xb) + SD (u, u⃗+v⃗)(xb)]   (Lemma 7.22 / [SD_cons])

    where the second summand is the paper's [Δf(u, u⃗+v⃗)(x)], and a
    *diagonal split* of the first summand

      [SD (u⃗+v⃗)(xb) = SD u⃗ (xb) + Σ_{j} SD (hybⱼ)(xb + uⱼ)] ,

    [hybⱼ] being the hybrid family [(u₁,…,u_{j-1}, vⱼ, u_{j+1}+v_{j+1},…)]
    of the paper's terms [3..n+1].  We deliver the *base instance* [n = 1]
    in [B]-side form, the smallest faithful case (and the one used by the
    induction base of Lemma 7.26): the diagonal split there is a single
    application of the second [SD_add] identity of Lemma 7.22 (split the
    sole head of [u⃗+v⃗]), and the head term is [SD_cons].  The general
    [n] case is delivered in [stable/compose.v] as [SD_diag] / [SD_723]
    via the diagonal sweep [SD_diag_sweep] over a fixed ['I_n] carrier
    (no prefix-concatenation needed). *)

Section Lemma723.
Variable R : realType.
Variables B C : coneType R.
Variable f : B -> C.
Hypothesis Hf : is_totmono f.
Local Open Scope precone_scope.

(** Lemma 7.23 at arity [n = 1], [B]-side.  Families [u v : 'I_1 → B],
    head [u0 : B], centre [xb : B].  The four paper terms collapse (for
    [n = 1]) to three: [Δf(u⃗)(x)] ([SD u xb]), [Δf(u, u⃗+v⃗)(x)]
    ([SD (vcons u0 (u+v)) xb]) and the single [j = 1] hybrid term
    [Δf(v₁)(x+u₁)] ([SD v (xb + u ord0)]). *)
Lemma SD_723_1 (u v : 'I_1 -> B) (u0 xb : B)
    (Hc : cone_norm (xb + (u0 +
       \big[precone_add/precone_zero]_(i : 'I_1) (u i + v i))) <= 1) :
  SD f (fun i => u i + v i) (xb + u0) =
  SD f u xb + SD f (vcons u0 (fun i => u i + v i)) xb
    + SD f v (xb + u ord0).
Proof.
have sum1 (g : 'I_1 -> B) :
    \big[precone_add/precone_zero]_(i : 'I_1) g i = g ord0.
  by rewrite big_ord_recl big_ord0 precone_addr0.
(* Head term, via the first [SD_cons] identity of Lemma 7.22. *)
have HcA : cone_norm (xb + \big[precone_add/precone_zero]_(i : 'I_1.+1)
    vcons u0 (fun i => u i + v i) i) <= 1.
  by rewrite sum_vcons sum1; move: Hc; rewrite sum1.
have stepA := SD_cons f Hf u0 (fun i => u i + v i) xb HcA.
(* Diagonal split of the sole head, via the second [SD_add] identity. *)
pose w0 := fun i : 'I_0 => u (lift ord0 i).
have euv : (fun i => u i + v i) = vcons (u ord0 + v ord0) w0.
  by apply/funext => i; rewrite [i]ord1 vcons0.
have HcB : cone_norm (xb + \big[precone_add/precone_zero]_(i : 'I_0.+1)
    vcons (u ord0 + v ord0) w0 i) <= 1.
  rewrite -euv; move: Hc; rewrite sum1 => H.
  apply: le_trans H; apply: cone_normp; apply: precone_add_le_l.
  by exists u0; rewrite precone_addC.
have stepB := SD_add f Hf (u ord0) (v ord0) w0 xb HcB.
rewrite -euv in stepB.
rewrite stepA stepB.
have eu : vcons (u ord0) w0 = u by apply/funext => i; rewrite [i]ord1 vcons0.
have ev : vcons (v ord0) w0 = v by apply/funext => i; rewrite [i]ord1 vcons0.
rewrite eu ev -!precone_addA.
by congr precone_add; exact: precone_addC.
Qed.

End Lemma723.

Arguments SD_723_1 {R B C} f Hf u v u0 xb.

(** ** The cone [SnB] — Paper §7.3 (txt 3695)

    [SnB B n := B^{n+1}], here the family type ['I_(n+1) → B], with
    *pointwise* cone operations and the non-product norm
    [‖g‖ := ‖Σ_{i} g i‖_B] (the [B]-norm of the total sum).  This is the
    cone at the origin of coherent differentiation (Remark 7.24): not the
    coproduct, nor the product, but [1 & ⋯ & 1 ⊸ B].

    We deliver the full [coneType]: the [isPrecone] mixin (pointwise, by
    the [funext] componentwise reductions) and the [isCone] mixin.  The
    five norm axioms reduce, through the total-sum homomorphism
    [snb_sum (g) = Σ_i g i] (which commutes with [+], [·:], and is
    monotone), to the [B]-norm axioms; (Normc) bundles the componentwise
    [cone_sup_ball]s, the norm bound coming from the radius-1 diagonal-sum
    lub [dsum_lub] (the total-sum chain stays in the unit ball). *)

Section SnBcone.
Variable R : realType.
Variable B : coneType R.
Variable n : nat.
Local Open Scope precone_scope.

(** Carrier: families of length [n+1]. *)
Definition snb_car : Type := 'I_n.+1 -> B.

Implicit Types g h : snb_car.

(** Pointwise operations. *)
Definition snb_zero : snb_car := fun=> precone_zero.
Definition snb_add g h : snb_car := fun i => g i + h i.
Definition snb_scale (r : {nonneg R}) g : snb_car := fun i => r *: g i.

(** The total sum [Σ_i g i] — a precone homomorphism into [B]. *)
Definition snb_sum g : B := \big[precone_add/precone_zero]_(i : 'I_n.+1) g i.

Lemma snb_sum0 : snb_sum snb_zero = 0.
Proof. by rewrite /snb_sum big1. Qed.

Lemma snb_sumD g h : snb_sum (snb_add g h) = snb_sum g + snb_sum h.
Proof. by rewrite /snb_sum -big_split. Qed.

Lemma snb_sumZ (r : {nonneg R}) g : snb_sum (snb_scale r g) = r *: snb_sum g.
Proof.
by rewrite /snb_sum (big_morph _ (precone_scale_DAr r) (precone_scale_0r r)).
Qed.

(** Precone axioms — pointwise. *)
Lemma snb_addA : associative snb_add.
Proof. by move=> g h k; apply/funext => i; rewrite /snb_add precone_addA. Qed.

Lemma snb_addC : commutative snb_add.
Proof. by move=> g h; apply/funext => i; rewrite /snb_add precone_addC. Qed.

Lemma snb_add0 : left_id snb_zero snb_add.
Proof. by move=> g; apply/funext => i; rewrite /snb_add precone_add0. Qed.

Lemma snb_scale_DAr (r : {nonneg R}) g h :
  snb_scale r (snb_add g h) = snb_add (snb_scale r g) (snb_scale r h).
Proof.
by apply/funext => i; rewrite /snb_scale /snb_add precone_scale_DAr.
Qed.

Lemma snb_scale_DAl (r s : {nonneg R}) g :
  snb_scale (r%:num + s%:num)%R%:nng g =
  snb_add (snb_scale r g) (snb_scale s g).
Proof.
by apply/funext => i; rewrite /snb_scale /snb_add precone_scale_DAl.
Qed.

Lemma snb_scale_A (r s : {nonneg R}) g :
  snb_scale (r%:num * s%:num)%R%:nng g = snb_scale r (snb_scale s g).
Proof. by apply/funext => i; rewrite /snb_scale precone_scale_A. Qed.

Lemma snb_scale_1 g : snb_scale (1%R)%:nng g = g.
Proof. by apply/funext => i; rewrite /snb_scale precone_scale_1. Qed.

Lemma snb_scale_0r (r : {nonneg R}) : snb_scale r snb_zero = snb_zero.
Proof. by apply/funext => i; rewrite /snb_scale precone_scale_0r. Qed.

Lemma snb_scale_0l g : snb_scale (0%R)%:nng g = snb_zero.
Proof. by apply/funext => i; rewrite /snb_scale precone_scale_0l. Qed.

Lemma snb_cancel g h k : snb_add g h = snb_add g k -> h = k.
Proof.
move=> H; apply/funext => i; apply: (@precone_cancel _ _ (g i)).
by have /(congr1 (fun w => w i)) := H.
Qed.

Lemma snb_pos g h : snb_add g h = snb_zero -> g = snb_zero /\ h = snb_zero.
Proof.
move=> H; split; apply/funext => i;
  have /(congr1 (fun w => w i)) := H => /= H'.
- by case: (precone_pos _ _ H').
- by case: (precone_pos _ _ H').
Qed.

HB.instance Definition _ := @isPrecone.Build R snb_car
  snb_zero snb_add snb_scale
  snb_addA snb_addC snb_add0
  snb_scale_DAr snb_scale_DAl snb_scale_A snb_scale_1
  snb_scale_0r snb_scale_0l snb_cancel snb_pos.

(** [snb_sum] is a precone homomorphism (re-export through the registered
    [+]/[·:]/[0] of [snb_car]) and monotone for the (pointwise) order. *)
Lemma snb_sum_add (g h : snb_car) : snb_sum (g + h) = snb_sum g + snb_sum h.
Proof. exact: snb_sumD. Qed.

(** Componentwise reading of the [snb_car] order. *)
Lemma snb_le_comp (g h : snb_car) :
  g <=p h -> forall i, g i <=p h i.
Proof.
by case=> z Hz i; exists (z i); have /(congr1 (fun w => w i)) := Hz.
Qed.

(** [snb_sum] is monotone: [g ≤p h ⇒ Σg ≤p Σh]. *)
Lemma snb_sum_le (g h : snb_car) : g <=p h -> snb_sum g <=p snb_sum h.
Proof. by case=> z ->; rewrite snb_sumD; exists (snb_sum z). Qed.

(** The norm: [B]-norm of the total sum. *)
Definition snb_norm (g : snb_car) : R := cone_norm (snb_sum g).

(** (Normh). *)
Lemma snb_normh (r : {nonneg R}) (g : snb_car) :
  snb_norm (r *: g) = r%:num * snb_norm g.
Proof. by rewrite /snb_norm snb_sumZ cone_normh. Qed.

(** (Normz). *)
Lemma snb_normz (g : snb_car) : snb_norm g = 0%R -> g = 0.
Proof.
move=> /cone_normz; rewrite /snb_sum => H.
apply/funext => i; move: H; rewrite (bigD1 i)//= => /precone_posl ->.
by rewrite /GRing.zero/=.
Qed.

(** (Normt). *)
Lemma snb_normt (g h : snb_car) :
  snb_norm (g + h) <= (snb_norm g + snb_norm h)%R.
Proof. by rewrite /snb_norm snb_sum_add; exact: cone_normt. Qed.

(** (Normp). *)
Lemma snb_normp (g h : snb_car) : g <=p h -> snb_norm g <= snb_norm h.
Proof. by move=> /snb_sum_le H; rewrite /snb_norm; exact: cone_normp. Qed.

End SnBcone.

Arguments snb_car {R} B n.
Arguments snb_sum {R B n} g.
Arguments snb_norm {R B n} g.
Arguments snb_le_comp {R B n g h}.
Arguments snb_sum_le {R B n g h}.

(** *** (Normc) — ω-completeness of the unit ball of [SnB]

    For a [≤p]-increasing unit-ball chain [u : nat → SnB], each component
    chain [c i k = u k i] is increasing and unit-ball (a component is
    [≤p] the total sum, whose norm is [≤ 1]).  The supremum is taken
    componentwise as a radius-1 [cone_sup_at]; it is the [SnB]-sup, with
    the norm bound coming from the radius-1 finite-diagonal-sum lub
    [dsum_lub]: the total-sum chain [Σ_i c i k = snb_sum (u k)] is
    unit-ball, so [Σ_i snb_sup i] is below its [cone_sup_ball] (norm ≤ 1). *)

Section SnBconeNorm.
Variable R : realType.
Variable B : coneType R.
Variable n : nat.
Local Open Scope precone_scope.

Notation Sn := (snb_car B n).

Section Sup.
Variable u : nat -> Sn.
Hypothesis uch : forall k, u k <=p u k.+1.
Hypothesis ub1 : forall k, snb_norm (u k) <= 1.

(** Per-component chain [c i k = u k i]. *)
Let c (i : 'I_n.+1) (k : nat) : B := u k i.

Let cch (i : 'I_n.+1) (k : nat) : c i k <=p c i k.+1.
Proof. exact: (snb_le_comp (uch k)). Qed.

(** A component is below the total sum [snb_sum (u k)]. *)
Let comp_le_sum (i : 'I_n.+1) (k : nat) : c i k <=p snb_sum (u k).
Proof.
rewrite /c /snb_sum (bigD1 i)//=.
by exists (\big[precone_add/precone_zero]_(j | j != i) u k j).
Qed.

Let M1 : {nonneg R} := 1%:nng.

Let cub1 (i : 'I_n.+1) (k : nat) : cone_norm (c i k) <= M1%:num.
Proof.
apply: le_trans (ub1 k); rewrite /snb_norm.
by apply: cone_normp; exact: comp_le_sum.
Qed.

Let M1pos : (0 < M1%:num)%R. Proof. by rewrite /M1/= ltr01. Qed.

(** The componentwise supremum, as a radius-1 [cone_sup_at]. *)
Definition snb_supf : Sn := fun i => dsup c cch cub1 M1pos i.

Lemma snb_supf_ub (k : nat) : u k <=p snb_supf.
Proof.
have wsex i : exists z, snb_supf i = u k i + z.
  by have := cone_sup_at_ub (cch i) (cub1 i) M1pos k.
pose Z i := projT1 (cid (wsex i)).
exists Z; apply/funext => i; rewrite /snb_add.
exact: (projT2 (cid (wsex i))).
Qed.

Lemma snb_supf_lub (y : Sn) : (forall k, u k <=p y) -> snb_supf <=p y.
Proof.
move=> uy.
have wsex i : exists z, y i = snb_supf i + z.
  apply: (cone_sup_at_lub (cch i) (cub1 i) M1pos) => k.
  exact: (snb_le_comp (uy k) i).
pose Z i := projT1 (cid (wsex i)).
exists Z; apply/funext => i; rewrite /snb_add.
exact: (projT2 (cid (wsex i))).
Qed.

Lemma snb_supf_norm : snb_norm snb_supf <= 1.
Proof.
have Tch (k : nat) : snb_sum (u k) <=p snb_sum (u k.+1).
  by apply: snb_sum_le; exact: uch.
have Tub1 (k : nat) : cone_norm (snb_sum (u k)) <= 1 by exact: ub1.
set T := cone_sup_ball (fun k => snb_sum (u k)) Tch Tub1.
have key : snb_sum snb_supf <=p T.
  rewrite /snb_sum /snb_supf.
  rewrite (_ : \big[precone_add/precone_zero]_(i : 'I_n.+1)
      dsup c cch cub1 M1pos i =
    \big[precone_add/precone_zero]_(i in [set: 'I_n.+1])
      dsup c cch cub1 M1pos i); last first.
    by apply: eq_bigl => i; rewrite finset.in_setT.
  apply: (dsum_lub cch cub1 M1pos) => k.
  apply: (precone_le_trans (y := snb_sum (u k))); last first.
    exact: (cone_sup_ball_ub (fun k => snb_sum (u k)) Tch Tub1 k).
  rewrite /dchain /snb_sum.
  rewrite (_ : \big[precone_add/precone_zero]_(i in [set: 'I_n.+1]) c i k =
    \big[precone_add/precone_zero]_(i : 'I_n.+1) u k i); last first.
    by apply: eq_bigl => i; rewrite finset.in_setT.
  exact: precone_le_refl.
rewrite /snb_norm; apply: le_trans (cone_normp _ _ key) _.
exact: (cone_sup_ball_norm (fun k => snb_sum (u k)) Tch Tub1).
Qed.

End Sup.

HB.instance Definition _ := @isCone.Build R Sn
  (@snb_norm R B n) (@snb_normh R B n) (@snb_normz R B n)
  (@snb_normt R B n) (@snb_normp R B n)
  snb_supf snb_supf_ub snb_supf_lub snb_supf_norm.

End SnBconeNorm.

(** [SnB B n] as a [coneType]: the family ['I_(n+1) → B] with pointwise
    operations and the total-sum norm. *)
Definition SnB (R : realType) (B : coneType R) (n : nat) : coneType R :=
  snb_car B n.

(**md**************************************************************)
(** ** Status: what is proved, and the remaining wall

    Delivered above with NO holes (no [Admitted]/[admit]/[Axiom]).
    - The *forward* half of Theorem 7.19 ([totmono_is_n_increasing]).
    - The strict reach lemma [lc_step1_norm_lt]: a configuration in the
      *open* unit ball has [B_x]-gauge-norm [< 1] (the strict analogue of
      [lc_step1_norm], proved by an admissible step [1 + δ]).
    - The lifting datum [lift_localP]: [‖u₀ + z‖ ≤ 1 ⇒ localP u₀ z].
    - **Theorem 7.19 converse, strict-interior form** ([conv_strict_aux]
      in [B]-core shape, [conv_strict] in the [is_totmono] [tm_arg] form):
      for an [f] that is [k]-increasing for all [k], the (7.1) inequality
      [Δ⁻f(u⃗)(x) ≤ Δ⁺f(u⃗)(x)] holds for every configuration in the *open*
      unit ball ([‖x + Σᵢ uᵢ‖ < 1]).  The induction on the arity follows
      the paper exactly: the [(u₀ :: u⃗)] step lifts the tail family [u⃗]
      from [B] to the local cone [B_{u₀}] (step-[1] admissibility, the
      lifted norm bound from [lc_step1_norm]/[lc_step1_norm_lt]), applies
      the inductive hypothesis to [Δf(u₀)] — which is [k]-increasing for
      all [k] by Lemma 7.16 — and recombines via [SDpos_E] / [SDneg_E] and
      the cons recurrences [Spos_recur] / [Sneg_recur].
    - The corollary [Delta_neg_le_pos_conv]: on the open ball, the
      pointwise difference [Δf(u⃗)] is well defined (the order consumed by
      [Delta_E]) from [n]-increasingness alone — the converse-side
      analogue of [Delta_neg_le_pos].
    - **Theorem 7.19 converse, full closed-ball form**
      ([is_n_increasing_totmono]): a *stable* [f] (i.e. [k]-increasing for
      all [k] *and* ω-continuous, [is_scott_continuous_unit f]) is totally
      monotonic.  This is the boundary bridge.  Its three reusable
      engines, all delivered above with NO holes:
      · [scale_chain_sup]: for [‖z‖ ≤ 1] and [λₘ = (m+1)/(m+2) ↑ 1] the
        chain [m ↦ λₘ ·: z] is increasing, unit-ball, and
        [cone_sup_ball (λₘ ·: z) = z] — the Archimedean "gap vanishes"
        argument in the style of [gauge_sup_reach] of [local_cone.v],
        here with [‖t‖ ≤ 1/(m+2) ‖z‖ → 0].
      · [dsum_lub] (section [SumSupAt]): the radius-aware finite-sum /
        supremum *least-upper-bound* commutation — the analogue of
        [sum_cone_sup_lub] of [stablehom.v] but with [cone_sup_at] at a
        common image radius [M], so the summand images may escape the unit
        ball.  Built on the radius-aware binary diagonal-sup identity
        [sup_at_addD] (totmono.v).
      · the boundary limit itself: for a closed-ball config [(x, u⃗)] and
        each summand [z_I = tm_arg x u I], the chain [c I m = f (λₘ ·: z_I)]
        is increasing (f increasing), norm-bounded by a common
        [M = Σ_I ‖f z_I‖ + 1] (f increasing, [λₘ z_I ≤p z_I]), and
        ω-continuity ([is_scott_continuous_unit]) + [scale_chain_sup] give
        its supremum [= f z_I] ([dsup_eq]).  [conv_strict] applied to the
        strictly-interior scaled config [(λₘ ·: x, λₘ ·: u⃗)] (norm
        [λₘ ‖z‖ ≤ λₘ < 1]) gives the open-ball inequality for each [m]
        ([step]); the [Ppos] side dominates its supremum ([dsum_ub]) and
        the [Pneg] side passes to it as a least upper bound ([dsum_lub]).

    §7.3 composition lead-up, delivered here with NO holes.
    - [totmono_shift] / [totmono_shift_le]: the "easy observation" of
      Lemma 7.20 — the shift [gₛ(x) = g(lc_val x + s)] preserves total
      monotonicity on the local cone [B_S] (single direction [s = S], and
      the dominated form [s ≤p S] used to read [Δε] as a sum of shifts by
      the partial sums).  Phrased and proved through [lc_val]/[lc_step1],
      the same local-cone transport as in [totmono_Delta1]/[Lemma718].
    - **Lemma 7.20, [Δε] clauses** ([totmono_Delta_pos] / [totmono_Delta_neg]):
      [Δ⁺f(u⃗)] and [Δ⁻f(u⃗)] are totally monotonic on [B_u⃗], as finite
      [\sumP]s of the dominated shifts [g_{s_I}] ([totmono_shift_le]) — a
      sum of totally monotonic maps is totally monotonic ([totmono_bigP]).
    - The **B-side difference [SD]** ([SD], [SD_E], [SD_Delta]): [Delta f u x]
      depends on [x] only through [lc_val x], so the difference recurrences
      live on bare [B]-centres, free of cone casts.
    - **Lemma 7.21** ([SD_le] in B-side form, [Delta_le] in operator form):
      [Δf(u⃗)(x) ≤p f(lc_val x + Σᵢ uᵢ)], by induction on the arity via
      [SD_cons] (the cons recurrence) and [SD0] (base case).
    - **Lemma 7.22** (both identities, B-side form): [SD_cons]
      ([SD w (x+u) = SD w x + SD (u :: w) x]) and [SD_add]
      ([SD (u+v :: w) x = SD (u :: w) x + SD (v :: w) (x+u)]) — pure
      [B]-side cancellations of the three [SD_E] defining equations.
    - **Lemma 7.23, base instance [n = 1]** ([SD_723_1], B-side): the
      telescoping identity [SD (u⃗+v⃗)(xb+u) = SD u⃗ (xb) +
      SD (u, u⃗+v⃗)(xb) + SD (v₁)(xb+u₁)].  The head term is [SD_cons],
      the single hybrid term is one [SD_add] (split the sole head of
      [u⃗+v⃗]).  The general-[n] case ([SD_723]) lives in
      [stable/compose.v].
    - **The cone [SnB]** ([SnB], full [coneType]): the family ['I_(n+1) → B]
      with pointwise operations and the total-sum norm [‖g‖ = ‖Σ_i g i‖_B]
      (Remark 7.24's [1 & ⋯ & 1 ⊸ B]).  All five norm axioms; (Normc)
      bundles the componentwise [cone_sup_at]s, the norm bound coming from
      the radius-1 diagonal-sum lub [dsum_lub].
    - **[lc_val_scott]**: the inclusion [lc_val : B_x → B] is ω-continuous
      on the unit ball — [lc_val (cone_sup_ball u) = cone_sup_ball
      (lc_val ∘ u)].  Derived from the (Normc) translate
      [lc_sup_ball_translate] (the [B]-sup of [n ↦ x + lc_val uₙ]), the
      shift-commutes fact [sup_ball_addr], and cancellation of the centre
      [precone_cancel]; the B-side chain proofs come from [lc_val_chain_mono]
      ([lc_leE]) and [lc_val_chain_ub1] ([lc_val_norm_le]).  This is the
      "translate" half of the [Δf(u⃗)] ω-continuity argument; the rest
      ([scott_Delta]) lives in [stable/compose.v], which can import
      [stable/stablehom.v]'s [diff_scott_at] (not importable here).

    Delivered in [stable/compose.v] (which imports [stable/stablehom.v]).
    - **[scott_Delta]** / Lemma 7.20 [Δf(u⃗)] clause: ω-continuity, then
      total monotonicity, of the difference operator [Δf(u⃗)] itself.
      Uses [lc_val_scott] above + the dominated shift [totmono_shift_le]
      and the difference-of-ω-continuous engine [diff_scott_at] of
      [stablehom.v].
    - Lemma 7.23, *general* arity (the full [Δf(u⃗+v⃗)(x+u)] telescope):
      [SD_diag] / [SD_723] via the diagonal sweep [SD_diag_sweep] over a
      fixed ['I_n] carrier (no prefix-concatenation needed).
    - Lemma 7.25 ([(x,u⃗) ↦ Δf(u⃗)(x)] increasing [B_SnB → C]):
      [SnB_increasing], built on the joint [SD_mono_full] monotonicity
      engine (centre [SD_mono_centre] + all directions [SD_mono_dirs] via
      the symmetry [SD_perm]) — purely from total monotonicity, with NO
      recourse to ω-continuity.  The [SnB] cone it lives on is complete
      (delivered above). *)
