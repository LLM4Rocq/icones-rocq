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
From mathcomp.algebra Require Import interval_inference.

Require Import Icones.prelude.classical_extra.
Require Import Icones.prelude.nonneg_extra.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.stable.local_cone.
Require Import Icones.stable.totmono.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

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

(** [Δf(())(x) = f (lc_val x)]: the difference [Δ⁺ ⊖ Δ⁻] at [n = 0]
    collapses to [Δ⁺ = f ∘ lc_val] since [Δ⁻ = 0]. *)
Lemma Delta0 (u : 'I_0 -> B)
    (x : local_cone (\big[precone_add/precone_zero]_(i : 'I_0) u i)) :
  Delta f u x = f (lc_val x).
Proof.
have le : precone_le (Delta_neg f u x) (Delta_pos f u x).
  by rewrite Delta_neg0; exact: precone_le0.
have := Delta_E le.
by rewrite Delta_neg0 Delta_pos0 precone_add0 => ->.
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
    discharges the operator-level half of the Lemma 7.17 clause that was
    previously delivered only in subtraction-free [B]-form ([Sdiff_mono]). *)

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
    here ([totmono_is_n_increasing]); the converse is deferred — see the
    note at the end of the file. *)

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

(** ** Deferred — Theorem 7.19 converse, Lemmas 7.20 / 7.21

    What is delivered above with no holes:
    - the nested-local-cone identity of Lemma 7.18, resolved *without* a
      cone-iso: every point of [(B_u)_u⃗] used in the total-monotonicity
      instance of [Δf(u)] is an actual [tm_arg] point of [B_u], expanded
      on the spot through [Delta1_E] and pushed onto the [B]-side, where
      the cons-recurrences and [Sdiff_mono] close it ([totmono_Delta1]);
    - the operator-level Lemma 7.17 monotonicity clause
      [Δf(u⃗)(x) ≤ Δf(u⃗)(x + u)] ([Delta_mono]);
    - the *forward* half of Theorem 7.19 ([totmono_is_n_increasing]).

    What remains, and the precise wall.
    - Theorem 7.19 *converse* ([(∀n, n-increasing) ⇒ totally monotonic]).
      The paper's induction on the arity [m] reduces the [(u₀ :: u⃗)]
      instance to the total monotonicity of [Δf(u₀) : B_{u₀} → C], obtained
      from Lemma 7.16 ([is_n_increasing_Delta]) plus the inductive
      hypothesis applied to [Δf(u₀)].  This requires [B_{u₀}] to be a
      [coneType], i.e. [‖u₀‖ < 1] *strictly* ([lc_coneType]).  But the
      directions [u₀] quantified by [is_totmono] range over the *closed*
      ball ([‖x + Σᵢ uᵢ‖ ≤ 1] only), so the head [u₀] may have
      [‖u₀‖ = 1] and [B_{u₀}] is then not available as a [coneType].
      Bridging the closed-ball case needs a strict-interior / Scott-limit
      argument (approximate [u₀] from inside the open ball and pass to the
      limit using ω-continuity), which is exactly the strict-interior
      transport deferred elsewhere in the development.  Note the lifting
      data themselves are available — the [mklift]-style admissibility
      [‖u₀ + v‖ ≤ 1 ⇒ localP u₀ v] and the summed equations [SDpos_E] /
      [SDneg_E] are in place — so only the [‖u₀‖ = 1] coneType gap blocks
      a clean converse.
    - Lemma 7.20 (total monotonicity of [Δ⁺f(u⃗)], [Δ⁻f(u⃗)], [Δf(u⃗)]) and
      Lemma 7.21 ([Δf(u⃗)(x) ≤ f(x + Σᵢ uᵢ)]).  The [Δf(u⃗)] parts both
      route through Theorem 7.19 (and, for 7.21, the nested clause
      [Δf(u :: u⃗) = Δ(Δf(u⃗))(u)] which again needs the closed-ball
      [B_{u⃗}] coneType), so they are blocked by the same wall.

    No axiom or [admit] is introduced: the deferred statements are simply
    not stated. *)
