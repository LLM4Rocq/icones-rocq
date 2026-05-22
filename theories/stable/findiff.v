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

(** ** Deferred — the remaining clause of Lemma 7.17

    The last clause of Lemma 7.17, [Δf(u :: u⃗) = Δ(Δf(u⃗))(u)], and the
    *operator-level* difference monotonicity [Δf(u⃗)(x) ≤ Δf(u⃗)(x+u)],
    are left for a follow-up.  Their content is fully delivered here in
    [B]-additive, subtraction-free form ([Sdiff_mono], together with the
    two cons recurrences [Delta_pos_recur] / [Delta_neg_recur] and the
    defining equation [Delta_E]); what remains is purely the
    *dependent-cone repackaging*:

    - the difference [Δ] is the [pselect]/[cid] cone-cancellation witness
      ([Delta]); turning [Sdiff_mono] into [precone_le (Δf u⃗ x)
      (Δf u⃗ x')] requires re-expressing both sides through [Delta_E] and
      threading the two [precone_le] witnesses, plus the cancellation
      [precone_le_addlI];
    - the nested form [Δ(Δf(u⃗))(u)] needs [u] re-presented as a
      *direction of [B_u⃗]* (a point of [local_cone (\sumP_i u⃗ i)]) and
      [Δf(u⃗) : B_u⃗ → C] fed to [Delta] again, i.e. a transport across
      [(B_u⃗)_{u} = B_{u :: u⃗}] (the paper's remark in Lemma 7.18).  This
      is the same kind of local-cone cast deferred elsewhere in the
      development and is the natural next increment.  No axiom or [admit]
      is used: the clause is simply not stated. *)
