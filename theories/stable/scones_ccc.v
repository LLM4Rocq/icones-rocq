(**md**************************************************************)
(** * The cartesian-closed structure of [SCones] — Paper §7.4

    The category [SCones] of integrable cones and stable-and-measurable
    functions is cartesian closed (Theorem 7.32).  The *products* part
    (projections, tupling, universal property) lives in
    [stable/scones_cat.v].  This file adds the *exponentials* part:

    - the binary product [sprod X Y] (the bool-indexed [icones_prod]),
      its pairing [sprod_pair] and projections [sprod_fst]/[sprod_snd];
    - the evaluation map [ev_fun] and **Lemma 7.27** ([ev_totmono]):
      evaluation is totally monotonic, hence the evaluation morphism
      [Ev : SCones(sprod (B ⇒ₛ C) B, C)];
    - currying [curry_app]/[curry] sending [SCones(sprod A B, C)] to
      [SCones(A, B ⇒ₛ C)];
    - the β/η laws and **Theorem 7.32** packaging [SCones] as a CCC
      ([SCones_CCC]).

    The internal hom [B ⇒ₛ C] is the iconeType [stablehom B C] of
    [stable/stablehom.v]; its cone operations are pointwise
    ([sh_addE]/[sh_scaleE]/[sh_zeroE]), which is what reduces the
    closed-structure proofs to pointwise statements in the codomain.

    Paper reference: §7.4 (page 1:65), Lemma 7.27, Theorem 7.32. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp Require Import perm.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import measurable_structure measurable_function.

Require Import Icones.prelude.classical_extra.
Require Import Icones.prelude.nonneg_extra.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.omega_general.
Require Import Icones.cones.cone_cat.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.path.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_cat.
Require Import Icones.stable.totmono.
Require Import Icones.stable.findiff.
Require Import Icones.stable.compose.
Require Import Icones.stable.stablehom.
Require Import Icones.stable.scones_cat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(** Proof-irrelevance of the unit-ball supremum: it is characterised by
    the upper-bound / least-upper-bound properties, so two
    [cone_sup_ball]s of the same chain (with different proof witnesses)
    are equal. *)
Lemma cone_sup_ball_irr (R : realType) (P : coneType R) (w : nat -> P)
    (c1 c2 : forall n, precone_le (w n) (w n.+1))
    (b1 b2 : forall n, cone_norm (w n) <= 1) :
  cone_sup_ball w c1 b1 = cone_sup_ball w c2 b2.
Proof.
apply: precone_le_anti; apply: cone_sup_ball_lub => n; exact: cone_sup_ball_ub.
Qed.

(** ** Generalized total monotonicity over a finite index family

    [is_totmono f] (Def 7.5) quantifies the (7.1) inequality over
    [u : 'I_n -> P].  For the evaluation map we need the same inequality
    with the increments indexed by an arbitrary [finType T] and the
    sign-split running over [{set T}] with parity [#|T| - #|J|].  We
    obtain it by transporting [is_totmono] along the canonical bijection
    [enum_val : 'I_#|T| -> T]. *)

Section GenTotmono.
Variable R : realType.
Variables P Q : coneType R.
Local Open Scope precone_scope.

(** The sign-split families over [{set T}], parity of [#|T| - #|J|]. *)
Definition gPneg (T : finType) : {set {set T}} :=
  [set J : {set T} | odd (#|T| - #|J|)].
Definition gPpos (T : finType) : {set {set T}} :=
  [set J : {set T} | ~~ odd (#|T| - #|J|)].

Lemma in_gPneg (T : finType) (J : {set T}) :
  (J \in gPneg T) = odd (#|T| - #|J|).
Proof. by rewrite inE. Qed.

Lemma in_gPpos (T : finType) (J : {set T}) :
  (J \in gPpos T) = ~~ odd (#|T| - #|J|).
Proof. by rewrite inE. Qed.

(** The (7.1) argument over a finite family [w : T -> P]. *)
Definition gtm_arg (T : finType) (a : P) (w : T -> P) (J : {set T}) : P :=
  a + \big[precone_add/precone_zero]_(j in J) w j.

(** Reindex an [Pε(#|T|)] sum (the [is_totmono] shape, with increments
    [w ∘ enum_val]) into a [{set T}]-indexed sum via the bijection
    [enum_rank : T -> 'I_#|T|]. *)
Lemma reindex_gPe (f : P -> Q) (T : finType)
    (D : pred {set 'I_#|T|}) (gD : pred {set T})
    (a : P) (w : T -> P) :
  (forall J : {set T}, D [set enum_rank j | j in J] = gD J) ->
  \big[precone_add/precone_zero]_(I in D)
      f (a + \big[precone_add/precone_zero]_(i in I) (w \o enum_val) i)
  = \big[precone_add/precone_zero]_(J in gD) f (gtm_arg a w J).
Proof.
move=> HD.
rewrite (reindex (fun J : {set T} => [set enum_rank j | j in J]))/=;
  last first.
  exists (fun I : {set 'I_#|T|} => [set enum_val i | i in I]) => X _.
  - rewrite -imset_comp; under eq_imset => i do rewrite /comp enum_rankK.
    by rewrite imset_id.
  - rewrite -imset_comp; under eq_imset => i do rewrite /comp enum_valK.
    by rewrite imset_id.
apply: eq_big => [J|J HJ].
  by rewrite unfold_in HD.
congr (f (a + _)).
rewrite big_imset/=; last exact: in2W enum_rank_inj.
by apply: eq_bigr => j _; rewrite /comp enum_rankK.
Qed.

(** Parity of the [enum_rank]-image: same as [#|T| - #|J|]. *)
Lemma enum_rank_imset_card (T : finType) (J : {set T}) :
  #|[set enum_rank j | j in J]| = #|J|.
Proof. by rewrite card_imset//; exact: enum_rank_inj. Qed.

(** **Generalized total monotonicity** over a [finType] family. *)
Lemma gen_totmono (f : P -> Q) (Hf : is_totmono f) (T : finType)
    (a : P) (w : T -> P) :
  cone_norm (a + \big[precone_add/precone_zero]_(j in [set: T]) w j) <= 1 ->
  \big[precone_add/precone_zero]_(J in gPneg T) f (gtm_arg a w J) <=p
  \big[precone_add/precone_zero]_(J in gPpos T) f (gtm_arg a w J).
Proof.
move=> Hc.
have parU (J : {set T}) :
    (#|T| - #|[set enum_rank j | j in J]|)%N = (#|T| - #|J|)%N.
  by rewrite enum_rank_imset_card.
rewrite -(reindex_gPe f (D := [in Pneg #|T|]) (gD := [in gPneg T])
            a w); last first.
  by move=> J; rewrite in_Pneg in_gPneg parU.
rewrite -(reindex_gPe f (D := [in Ppos #|T|]) (gD := [in gPpos T])
            a w); last first.
  by move=> J; rewrite in_Ppos in_gPpos parU.
have KEY : \big[precone_add/precone_zero]_(j in [set: T]) w j
         = \big[precone_add/precone_zero]_(i : 'I_#|T|) (w \o enum_val) i.
  transitivity (\big[precone_add/precone_zero]_(j : T) w j).
    by apply: eq_bigl => j; rewrite finset.in_setT.
  by rewrite -(big_enum_val (A := predT) w); apply: eq_bigl => j; rewrite !inE.
have Hc' : cone_norm (a +
    \big[precone_add/precone_zero]_(i : 'I_#|T|) (w \o enum_val) i) <= 1.
  by rewrite -KEY.
have := Hf #|T| a (w \o enum_val) Hc'.
by rewrite /tm_arg.
Qed.

End GenTotmono.

Arguments gen_totmono {R P Q f} Hf T a w.

(** ** The binary product [sprod X Y]

    The binary product in [SCones] (and in [ICones]) is the bool-indexed
    [icones_prod] [if b then X else Y].  Its projections are the [SCones]
    [scones_proj true]/[scones_proj false] of [scones_cat.v]; we add the
    pairing [sprod_pair] together with the computation lemmas
    [sprod_fstE]/[sprod_sndE]/[sprod_eta]. *)

Section SProd.
Variable R : realType.
Variable Ar : MeasSubcat R.
Local Open Scope precone_scope.

Definition sprod_fam (X Y : ICone.type Ar) : bool -> ICone.type Ar :=
  fun b => if b then X else Y.

(** The binary product cone. *)
Definition sprod (X Y : ICone.type Ar) : ICone.type Ar :=
  icones_prod (sprod_fam X Y).

(** First / second components of a product point. *)
Definition sprod_fst (X Y : ICone.type Ar) (p : sprod X Y) : X :=
  cones_prod_val p true.
Definition sprod_snd (X Y : ICone.type Ar) (p : sprod X Y) : Y :=
  cones_prod_val p false.

(** The pairing point [⟨x, y⟩], uniformly bounded by [‖x‖ + ‖y‖]. *)
Lemma sprod_pair_bd (X Y : ICone.type Ar) (x : X) (y : Y) :
  exists M : R, forall b : bool,
    cone_norm ((if b return sprod_fam X Y b then x else y)) <= M.
Proof.
exists (cone_norm x + cone_norm y)%R => -[].
- by rewrite lerDl; exact: cone_norm_ge0.
- by rewrite lerDr; exact: cone_norm_ge0.
Qed.

Definition sprod_pair (X Y : ICone.type Ar) (x : X) (y : Y) : sprod X Y :=
  {| cones_prod_val := fun b => if b return sprod_fam X Y b then x else y;
     cones_prod_bd := sprod_pair_bd x y |}.

Lemma sprod_fstE (X Y : ICone.type Ar) (x : X) (y : Y) :
  sprod_fst (sprod_pair x y) = x.
Proof. by []. Qed.

Lemma sprod_sndE (X Y : ICone.type Ar) (x : X) (y : Y) :
  sprod_snd (sprod_pair x y) = y.
Proof. by []. Qed.

(** A product point is determined by its two components. *)
Lemma sprod_eta (X Y : ICone.type Ar) (p : sprod X Y) :
  p = sprod_pair (sprod_fst p) (sprod_snd p).
Proof. by apply: cones_prod_eq => -[]. Qed.

(** The pairing of an addition is the addition of pairings (the product
    sum is componentwise). *)
Lemma sprod_pairD (X Y : ICone.type Ar) (x1 x2 : X) (y1 y2 : Y) :
  sprod_pair (x1 + x2) (y1 + y2) = sprod_pair x1 y1 + sprod_pair x2 y2.
Proof. by apply: cones_prod_eq => -[]. Qed.

(** Components of a product cone-sum are the componentwise sums. *)
Lemma sprod_fst_big (X Y : ICone.type Ar) (T : finType) (A : {set T})
    (h : T -> sprod X Y) :
  sprod_fst (\big[precone_add/precone_zero]_(j in A) h j) =
  \big[precone_add/precone_zero]_(j in A) sprod_fst (h j).
Proof. exact: cones_prod_val_big. Qed.

Lemma sprod_snd_big (X Y : ICone.type Ar) (T : finType) (A : {set T})
    (h : T -> sprod X Y) :
  sprod_snd (\big[precone_add/precone_zero]_(j in A) h j) =
  \big[precone_add/precone_zero]_(j in A) sprod_snd (h j).
Proof. exact: cones_prod_val_big. Qed.

End SProd.

Arguments sprod {R Ar}.
Arguments sprod_fst {R Ar X Y}.
Arguments sprod_snd {R Ar X Y}.
Arguments sprod_pair {R Ar X Y}.

(** Paper Cuball(X & Y) = Cuball X × Cuball Y.  The product norm is the
    sup of the two component norms, so a pairing of two unit-ball points
    is in the unit ball. *)
Section SProdNorm.
Variable R : realType.
Variable Ar : MeasSubcat R.
Variables X Y : ICone.type Ar.
Local Open Scope precone_scope.

(** [‖⟨x, y⟩‖ ≤ 1] when [‖x‖ ≤ 1] and [‖y‖ ≤ 1]. *)
Lemma sprod_pair_norm_le1 (x : X) (y : Y) :
  cone_norm x <= 1 -> cone_norm y <= 1 ->
  cone_norm (sprod_pair x y) <= 1.
Proof.
move=> Hx Hy; rewrite /cone_norm/= /cones_prod_norm.
apply: ge_sup.
  by exists (cone_norm (cones_prod_val (sprod_pair x y) true)), true.
by move=> r [[] ->].
Qed.

(** Conversely, both components of a unit-ball pairing are in the unit
    ball (each component norm is [≤] the product norm). *)
Lemma sprod_fst_ball (p : sprod X Y) :
  cone_norm p <= 1 -> cone_norm (sprod_fst p) <= 1.
Proof. by move=> Hp; apply: le_trans Hp; exact: (cones_prod_norm_ge_comp _ true). Qed.

Lemma sprod_snd_ball (p : sprod X Y) :
  cone_norm p <= 1 -> cone_norm (sprod_snd p) <= 1.
Proof. by move=> Hp; apply: le_trans Hp; exact: (cones_prod_norm_ge_comp _ false). Qed.

End SProdNorm.

Arguments sprod_pair_norm_le1 {R Ar X Y} x y.
Arguments sprod_fst_ball {R Ar X Y p}.
Arguments sprod_snd_ball {R Ar X Y p}.

(** ** The per-index totmono reduction (Term B of Lemma 7.27)

    For a totally-monotonic [h : B -> C] and a fixed index [i : 'I_n],
    the (7.1)-style sums *restricted to the index sets containing [i]*
    are again [≤p]-ordered.  We reduce this to [gen_totmono] over the
    sub-[finType] [{j : 'I_n | j != i}] via the bijection
    [J ↦ i |: (val @: J)] between [{set {j | j != i}}] and the index
    sets [I ⊆ 'I_n] with [i ∈ I]. *)

Section TotmonoInI.
Variable R : realType.
Variables B C : coneType R.
Variable h : B -> C.
Hypothesis Hh : is_totmono h.
Local Open Scope precone_scope.

Variable n : nat.
Variable i : 'I_n.
Local Notation Ti := {j : 'I_n | j != i}.

(** The [Ti]-image of [J] together with [i]. *)
Definition liftI (J : {set Ti}) : {set 'I_n} := i |: [set val j | j in J].

Lemma i_notin_imset (J : {set Ti}) : i \notin [set val j | j in J].
Proof.
apply/negP => /imsetP[j _ Hij].
by move: (valP j); rewrite -Hij eqxx.
Qed.

Lemma i_in_liftI (J : {set Ti}) : i \in liftI J.
Proof. by rewrite /liftI !inE eqxx. Qed.

Lemma card_liftI (J : {set Ti}) : #|liftI J| = (#|J|).+1.
Proof. by rewrite /liftI cardsU1 i_notin_imset/= card_imset//; exact: val_inj. Qed.

Lemma card_Ti : #|{: Ti}| = (n.-1)%N.
Proof.
rewrite card_sig (eq_card (B := predC1 i)); last by move=> j; rewrite !inE.
by rewrite cardC1 card_ord.
Qed.

(** Parity: [liftI J ∈ Pε(n) ⟺ J ∈ gPε(Ti)]. *)
Lemma liftI_Pneg (J : {set Ti}) :
  (liftI J \in Pneg n) = (J \in gPneg {: Ti}).
Proof.
rewrite in_Pneg in_gPneg card_liftI card_Ti; congr (odd _).
by rewrite -subn1 -subnDA add1n.
Qed.

Lemma liftI_Ppos (J : {set Ti}) :
  (liftI J \in Ppos n) = (J \in gPpos {: Ti}).
Proof.
rewrite in_Ppos in_gPpos card_liftI card_Ti; congr (~~ odd _).
by rewrite -subn1 -subnDA add1n.
Qed.

(** The argument identity: [x₀ + Σ_{j∈liftI J} v_j
    = (x₀ + v_i) + Σ_{j∈J} (v∘val) j]. *)
Lemma liftI_arg (x0 : B) (v : 'I_n -> B) (J : {set Ti}) :
  x0 + \big[precone_add/precone_zero]_(j in liftI J) v j =
  (x0 + v i) + \big[precone_add/precone_zero]_(j in J) (v \o val) j.
Proof.
rewrite /liftI big_setU1 ?i_notin_imset//=.
rewrite big_imset/=; last exact: in2W val_inj.
by rewrite precone_addA.
Qed.

(** **The Term-B per-index inequality.**  Restricting the (7.1) sums to
    index sets containing [i], reindexing by [liftI], and applying
    [gen_totmono] over [Ti] at centre [x₀ + v i]. *)
Lemma totmono_in_i (x0 : B) (v : 'I_n -> B) :
  cone_norm (x0 + \big[precone_add/precone_zero]_(j : 'I_n) v j) <= 1 ->
  \big[precone_add/precone_zero]_(I in Pneg n | i \in I)
      h (x0 + \big[precone_add/precone_zero]_(j in I) v j) <=p
  \big[precone_add/precone_zero]_(I in Ppos n | i \in I)
      h (x0 + \big[precone_add/precone_zero]_(j in I) v j).
Proof.
move=> Hc.
have reix (D : pred {set 'I_n}) (gD : pred {set Ti}) :
    (forall J : {set Ti}, D (liftI J) = gD J) ->
    \big[precone_add/precone_zero]_(I in D | i \in I)
        h (x0 + \big[precone_add/precone_zero]_(j in I) v j)
    = \big[precone_add/precone_zero]_(J in gD)
        h (gtm_arg (x0 + v i) (v \o val) J).
  move=> HD.
  rewrite (reindex liftI)/=; last first.
    exists (fun I : {set 'I_n} => [set j | val j \in I]) => X HX.
    - apply/setP => j; rewrite inE /liftI !inE.
      apply/idP/idP.
        case/orP => [/eqP Hvj|].
          by move: (valP j); rewrite Hvj eqxx.
        by case/imsetP => k Hk /val_inj ->.
      by move=> Hj; apply/orP; right; apply/imsetP; exists j.
    - move: HX => /andP[HD0 Hi0]; apply/setP => k; rewrite /liftI !inE.
      apply/idP/idP.
        by case/orP => [/eqP ->//|/imsetP[j]]; rewrite inE => Hj /= ->.
      move=> Hk; case: (eqVneq k i) => [|Hki]; first by [].
      by rewrite orFb; apply/imsetP; exists (Sub k Hki); rewrite ?inE.
  apply: eq_big => [J|J _].
    by rewrite unfold_in HD i_in_liftI andbT -topredE.
  by rewrite /gtm_arg liftI_arg.
rewrite (reix [in Pneg n] [in gPneg {: Ti}]); last first.
  by move=> J; rewrite liftI_Pneg.
rewrite (reix [in Ppos n] [in gPpos {: Ti}]); last first.
  by move=> J; rewrite liftI_Ppos.
apply: (gen_totmono Hh {: Ti} (x0 + v i) (v \o val)).
have -> : (x0 + v i) +
    \big[precone_add/precone_zero]_(j in [set: Ti]) (v \o val) j
  = x0 + \big[precone_add/precone_zero]_(j : 'I_n) v j; last exact: Hc.
rewrite -precone_addA; congr (x0 + _).
rewrite (bigID (fun j : 'I_n => j == i))/= big_pred1_eq.
congr (_ + _).
rewrite -(big_imset (h := val))/=; last exact: in2W val_inj.
apply: eq_bigl => k.
apply/imsetP/idP => [[j _ ->]|Hk].
  exact: (valP j).
by exists (Sub k Hk); rewrite ?inE.
Qed.

End TotmonoInI.

Arguments totmono_in_i {R B C h} Hh {n} i x0 v.

(** ** The evaluation morphism [Ev] — Paper Lemma 7.27 + §7.4

    [ev_fun φ = (φ.1) (φ.2)] applies the [stablehom] component of a
    product point to its point component.  Lemma 7.27 is its total
    monotonicity ([ev_totmono]). *)

Section Eval.
Variable R : realType.
Variable Ar : MeasSubcat R.
Variables B C : ICone.type Ar.
Local Open Scope precone_scope.

Local Notation H := (stablehom B C : ICone.type Ar).
Local Notation SP := (sprod H B).

(** Pointwise lift of [sh_addE] over a cone-sum of stable maps. *)
Lemma sh_bigE (T : finType) (A : {set T}) (g : T -> H) (x : B) :
  sh_fun (\big[precone_add/precone_zero]_(j in A) g j) x =
  \big[precone_add/precone_zero]_(j in A) sh_fun (g j) x.
Proof.
apply: (big_morph (fun f : H => sh_fun f x)).
  by move=> f1 f2; rewrite sh_addE.
by rewrite sh_zeroE.
Qed.

(** The evaluation function. *)
Definition ev_fun (φ : SP) : C := sh_fun (sprod_fst φ) (sprod_snd φ).

(** The key decomposition: at a (7.1) argument [tm_arg φ₀ Φ I], the
    evaluation splits into the fixed-hom part [f₀] applied at the point
    argument [x_I] plus the increments' homs applied at [x_I]. *)
Lemma ev_fun_tm_arg (n : nat) (φ0 : SP) (Φ : 'I_n -> SP) (I : {set 'I_n}) :
  ev_fun (tm_arg φ0 Φ I) =
  sh_fun (sprod_fst φ0)
    (sprod_snd φ0 + \big[precone_add/precone_zero]_(j in I) sprod_snd (Φ j))
  + \big[precone_add/precone_zero]_(j in I)
      sh_fun (sprod_fst (Φ j))
        (sprod_snd φ0 + \big[precone_add/precone_zero]_(j in I) sprod_snd (Φ j)).
Proof.
rewrite /ev_fun /tm_arg /sprod_fst /sprod_snd.
have valD (x y : SP) (b : bool) :
    cones_prod_val (x + y) b = cones_prod_val x b + cones_prod_val y b by [].
rewrite !valD !cones_prod_val_big.
by rewrite sh_addE sh_bigE.
Qed.

(** Projection of the product (7.1) guard to the point component. *)
Lemma ev_guard_snd (n : nat) (φ0 : SP) (Φ : 'I_n -> SP) :
  cone_norm (φ0 + \big[precone_add/precone_zero]_(i : 'I_n) Φ i) <= 1 ->
  cone_norm (sprod_snd φ0 +
    \big[precone_add/precone_zero]_(j : 'I_n) sprod_snd (Φ j)) <= 1.
Proof.
move=> Hz; apply: le_trans Hz.
rewrite (_ : sprod_snd φ0 + _ = sprod_snd (φ0 +
    \big[precone_add/precone_zero]_(i : 'I_n) Φ i)); last first.
  rewrite /sprod_snd.
  have valD (x y : SP) (b : bool) :
      cones_prod_val (x + y) b = cones_prod_val x b + cones_prod_val y b by [].
  rewrite [RHS](valD φ0); congr (_ + _).
  by apply: esym; apply: (big_morph (fun x : SP => cones_prod_val x false)).
exact: (cones_prod_norm_ge_comp _ false).
Qed.

(** **Lemma 7.27** — evaluation is totally monotonic. *)
Lemma ev_totmono : is_totmono ev_fun.
Proof.
move=> n φ0 Φ Hz.
set x0 := sprod_snd φ0.
set v := fun j : 'I_n => sprod_snd (Φ j).
have Hxg : cone_norm (x0 + \big[precone_add/precone_zero]_(j : 'I_n) v j) <= 1.
  exact: ev_guard_snd.
(* rewrite both sides with the decomposition, then split A + B *)
under eq_bigr => I _ do rewrite ev_fun_tm_arg.
under [X in _ <=p X]eq_bigr => I _ do rewrite ev_fun_tm_arg.
rewrite !sumP_add.
(* a pointwise [+]-monotone combinator *)
have pairle (a a' b b' : C) : a <=p a' -> b <=p b' -> a + b <=p a' + b'.
  move=> Ha Hb; apply: (precone_le_trans (y := a' + b)).
    exact: precone_add_le_r.
  exact: precone_add_le_l.
apply: pairle.
  (* Term A: total monotonicity of the fixed hom [sprod_fst φ0]. *)
  have [[HtmA _ _] _] := sh_meas_stable (sprod_fst φ0).
  by have := HtmA n x0 v Hxg; rewrite /tm_arg.
(* Term B: swap the two sums, then sum the per-index [totmono_in_i]. *)
rewrite [X in X <=p _](exchange_big_dep predT)//=.
rewrite [X in _ <=p X](exchange_big_dep predT)//=.
apply: (big_ind2 (fun a b => a <=p b)).
- exact: precone_le_refl.
- by move=> a a' b b' Ha Hb; apply: (precone_le_trans (y := a' + b));
    [exact: precone_add_le_r | exact: precone_add_le_l].
- move=> i _.
  have [[HtmB _ _] _] := sh_meas_stable (sprod_fst (Φ i)).
  exact: (totmono_in_i HtmB i x0 v Hxg).
Qed.

(** Pointwise bound: [‖φ.1 (φ.2)‖ ≤ ‖φ.1‖ ≤ 1] on the unit ball. *)
Lemma ev_image_ball (φ : SP) :
  cone_norm φ <= 1 -> cone_norm (ev_fun φ) <= 1.
Proof.
move=> Hφ; rewrite /ev_fun.
have Hfst : cone_norm (sprod_fst φ) <= 1.
  by apply: le_trans Hφ; exact: (cones_prod_norm_ge_comp _ true).
have Hsnd : cone_norm (sprod_snd φ) <= 1.
  by apply: le_trans Hφ; exact: (cones_prod_norm_ge_comp _ false).
apply: le_trans Hfst.
exact: (sh_norm_ub (sprod_fst φ) (sprod_snd φ) Hsnd).
Qed.

(** Boundedness clause of [is_stable]. *)
Lemma ev_bounded :
  exists M : R, forall φ : SP, cone_norm φ <= 1 -> cone_norm (ev_fun φ) <= M.
Proof. by exists 1 => φ Hφ; exact: ev_image_ball. Qed.

(** The unit-ball supremum of a chain of product points projects
    componentwise (definitionally, the [cones_prod_sup_ball]). *)
Lemma sprod_fst_sup (u : nat -> SP)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, cone_norm (u n) <= 1) :
  sprod_fst (cone_sup_ball u uch ub1) =
  cone_sup_ball (fun n => sprod_fst (u n))
    (cones_prod_sup_ball_chain_comp uch true)
    (cones_prod_sup_ball_ub1_comp ub1 true).
Proof. by []. Qed.

Lemma sprod_snd_sup (u : nat -> SP)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, cone_norm (u n) <= 1) :
  sprod_snd (cone_sup_ball u uch ub1) =
  cone_sup_ball (fun n => sprod_snd (u n))
    (cones_prod_sup_ball_chain_comp uch false)
    (cones_prod_sup_ball_ub1_comp ub1 false).
Proof. by []. Qed.

(** Evaluation is increasing on the unit ball (from total monotonicity). *)
Lemma ev_incr (φ ψ : SP) :
  φ <=p ψ -> cone_norm ψ <= 1 -> ev_fun φ <=p ev_fun ψ.
Proof. by move=> Hle Hψ; exact: (tm_incr_le ev_totmono Hle Hψ). Qed.

(** **ω-continuity of evaluation on the unit ball.**  The unit-ball
    supremum of a chain [u] of product points has [fst] the [stablehom]
    supremum [sh_sup] of the hom-chain and [snd] the point supremum.
    Evaluating gives a *triple* supremum which collapses to the diagonal
    [supₖ (fₖ xₖ)] by the standard "increase both indices to their max"
    argument. *)
Lemma ev_scott : is_scott_continuous_unit ev_fun.
Proof.
move=> Mf u uch ub1 fuch fubMf Mfpos.
set Φ := cone_sup_ball u uch ub1.
have HΦ1 : cone_norm Φ <= 1 by exact: cone_sup_ball_norm.
(* component chains *)
pose f := fun n => sprod_fst (u n).
pose x := fun n => sprod_snd (u n).
have fch n : f n <=p f n.+1 by exact: (cones_prod_le_comp (uch n) true).
have xch n : x n <=p x n.+1 by exact: (cones_prod_le_comp (uch n) false).
have fb1 n : sh_norm (f n) <= 1.
  by apply: le_trans (ub1 n); exact: (cones_prod_norm_ge_comp (u n) true).
have xb1 n : cone_norm (x n) <= 1.
  by apply: le_trans (ub1 n); exact: (cones_prod_norm_ge_comp (u n) false).
(* [snd Φ] is the point supremum [Y]; [fst Φ] is [sh_sup f]. *)
set Y := sprod_snd Φ.
have HY1 : cone_norm Y <= 1.
  by apply: le_trans HΦ1; exact: (cones_prod_norm_ge_comp Φ false).
have YE : Y = cone_sup_ball x xch xb1.
  by rewrite /Y sprod_snd_sup; exact: cone_sup_ball_irr.
have evΦE : ev_fun Φ = sh_sup_fun fch fb1 Y.
  rewrite /ev_fun /Y sprod_fst_sup.
  have -> : cone_sup_ball (fun n : nat => sprod_fst (u n))
      (cones_prod_sup_ball_chain_comp uch true)
      (cones_prod_sup_ball_ub1_comp ub1 true) = sh_sup fch fb1.
    exact: cone_sup_ball_irr.
  by [].
(* the two chains are monotone in [≤] (not just successor steps) *)
have xmono m k : (m <= k)%N -> x m <=p x k.
  elim: k => [|k IHk]; first by rewrite leqn0 => /eqP ->; exact: precone_le_refl.
  rewrite leq_eqVlt => /orP[/eqP ->|]; first exact: precone_le_refl.
  by rewrite ltnS => /IHk Hmk; apply: (precone_le_trans Hmk); exact: xch.
have fmono m k : (m <= k)%N -> f m <=p f k.
  elim: k => [|k IHk]; first by rewrite leqn0 => /eqP ->; exact: precone_le_refl.
  rewrite leq_eqVlt => /orP[/eqP ->|]; first exact: precone_le_refl.
  by rewrite ltnS => /IHk Hmk; apply: (precone_le_trans Hmk); exact: fch.
(* the diagonal: [fₘ xₖ ≤p ev (u (max m k))]. *)
have diag m k : sh_fun (f m) (x k) <=p ev_fun (u (maxn m k)).
  apply: (precone_le_trans (y := sh_fun (f m) (x (maxn m k)))).
    apply: (tm_incr_le (f := sh_fun (f m))).
    - by have [[Htm _ _] _] := sh_meas_stable (f m).
    - exact: xmono (leq_maxr m k).
    - exact: xb1.
  have ->: ev_fun (u (maxn m k)) = sh_fun (f (maxn m k)) (x (maxn m k)) by [].
  by apply: sh_le_pointwise; exact: fmono (leq_maxl m k).
apply: precone_le_anti.
- (* [ev Φ ≤p cone_sup_at (ev∘u)] via the lub of homs applied at [Y]. *)
  rewrite evΦE.
  apply: (sh_sup_fun_lubP fch fb1 HY1) => m.
  rewrite YE.
  have [[_ _ Hcont] _] := sh_meas_stable (f m).
  (* [fₘ Y = supₖ fₘ xₖ]; bound each by the diagonal. *)
  pose g := fun k => sh_fun (f m) (x k).
  have gch k : g k <=p g k.+1.
    rewrite /g; have [[Htm _ _] _] := sh_meas_stable (f m).
    by apply: (tm_incr_le Htm (xch k)); exact: xb1.
  have gb1 k : cone_norm (g k) <= 1.
    by rewrite /g; apply: le_trans (fb1 m); exact: sh_norm_ub _ _ (xb1 k).
  rewrite (Hcont 1%:nng x xch xb1 gch gb1 ltr01).
  rewrite (@cone_sup_at_ball _ _ g gch gb1 (fun k => gb1 k) ltr01).
  apply: cone_sup_ball_lub => k.
  apply: (precone_le_trans (diag m k)).
  exact: cone_sup_at_ub.
- (* [cone_sup_at (ev∘u) ≤p ev Φ]: each [ev (u k) ≤p ev Φ]. *)
  apply: cone_sup_at_lub => k.
  apply: ev_incr => //; exact: cone_sup_ball_ub.
Qed.

(** **Path-preservation of evaluation.**  Along a unit-ball product path
    [δ], the hom-component [δ.1] and the point-component [δ.2] are both
    unit-ball measurable paths; joint test-measurability of the internal
    hom ([sh_int_joint_meas]) applied along the *diagonal* [r ↦ (r, r)]
    gives measurability of [r ↦ ev_fun (δ r)]. *)
Lemma ev_pres_path (X : ar_obj Ar) (δ : ar_carrier Ar X -> SP) :
  (forall r, cone_norm (δ r) <= 1) ->
  is_measurable_path (Ar:=Ar) (C:=SP) δ ->
  is_measurable_path (Ar:=Ar) (C:=C) (fun r => ev_fun (δ r)).
Proof.
move=> Hδb Hδ; split; first by exists 1 => r; exact: ev_image_ball.
move=> Z m mM.
(* the two component paths and their unit-ball bounds *)
pose η := fun r => sprod_fst (δ r).
pose γ := fun r => sprod_snd (δ r).
have Hη : is_measurable_path (Ar:=Ar) (C:=stablehom B C : ICone.type Ar) η.
  exact: (icones_prod_path_comp Hδ true).
have Hγ : is_measurable_path (Ar:=Ar) (C:=B) γ.
  exact: (icones_prod_path_comp Hδ false).
have Hγb r : cone_norm (γ r) <= 1.
  by apply: le_trans (Hδb r); exact: (cones_prod_norm_ge_comp (δ r) false).
have JM := sh_int_joint_meas (Y':=X) Hη (X':=X) Hγb Hγ mM.
(* precompose with the diagonal [(z, r) ↦ (z, (r, r))] *)
have diag_meas : measurable_fun
    [set: (ar_carrier Ar Z * ar_carrier Ar X)%type]
    (fun p => (p.1, (p.2, p.2))).
  apply: measurable_fun_pair; first exact: measurable_fst.
  by apply: measurable_fun_pair; exact: measurable_snd.
have step :
    (fun p : ar_carrier Ar Z * ar_carrier Ar X =>
       test_fun m p.1 (ev_fun (δ p.2))) =
    (fun p => m p.1 (sh_fun (η p.2.2) (γ p.2.1))) \o
    (fun p => (p.1, (p.2, p.2))).
  by apply: funext.
(* [measurable_comp] (the [sigmaRingType] version) instead of
   [measurableT_comp]: it uses ordinary unification, sidestepping the
   keyed-matching failure on the product canonical structure of the
   doubled factor [X × X] in [JM]'s domain. *)
rewrite step.
apply: (measurable_comp
  (F := [set: (ar_carrier Ar Z *
               (ar_carrier Ar X * ar_carrier Ar X))%type]) measurableT).
- exact: subsetT.
- exact: JM.
- exact: diag_meas.
Qed.

(** Evaluation is a stable-and-measurable map (Lemma 7.27 + §7.4). *)
Lemma ev_meas_stable : is_meas_stable ev_fun.
Proof.
split; first split.
- exact: ev_totmono.
- exact: ev_bounded.
- exact: ev_scott.
- exact: ev_pres_path.
Qed.

End Eval.

Arguments ev_fun {R Ar B C}.
Arguments ev_totmono {R Ar B C}.

(** ** The evaluation morphism [Ev] — Paper §7.4

    [Ev : SCones(sprod (B ⇒ₛ C) B, C)] is the [scones_hom] carrying
    [ev_fun], 0-extended off the unit ball via the clamp [sc_clamp].
    Its measurable-stability is [ev_meas_stable] (through the clamp
    congruence [sc_clamp_meas_stable]); its operator norm is [≤ 1] since
    on the ball [‖ev_fun φ‖ ≤ 1] ([ev_image_ball]). *)

Section EvMorphism.
Variable R : realType.
Variable Ar : MeasSubcat R.
Variables B C : ICone.type Ar.
Local Open Scope precone_scope.

Local Notation H := (stablehom B C : ICone.type Ar).
Local Notation SP := (sprod H B).

Lemma Ev_meas_stable : is_meas_stable (sc_clamp (@ev_fun R Ar B C)).
Proof. exact: sc_clamp_meas_stable (ev_meas_stable B C). Qed.

Lemma Ev_norm_le1 : sc_norm (sc_clamp (@ev_fun R Ar B C)) <= 1.
Proof.
apply: sc_norm_lub => φ Hφ; rewrite (sc_clamp_ball Hφ).
exact: ev_image_ball.
Qed.

(** Paper §7.4: the evaluation morphism of [SCones]. *)
Definition Ev : scones_hom SP C :=
  MkSconesHom (sc_clamp (@ev_fun R Ar B C)) Ev_meas_stable Ev_norm_le1
    (sc_clamp_offball_field _).

(** On the unit ball [Ev] computes to [ev_fun]. *)
Lemma Ev_ball (φ : SP) : cone_norm φ <= 1 -> sc_fun Ev φ = ev_fun φ.
Proof. by move=> Hφ; rewrite /Ev /= (sc_clamp_ball Hφ). Qed.

(** On a pairing [⟨f, x⟩] in the ball, [Ev] is [f x]. *)
Lemma Ev_pair (f : H) (x : B) :
  cone_norm (sprod_pair f x) <= 1 ->
  sc_fun Ev (sprod_pair f x) = sh_fun f x.
Proof. by move=> Hfx; rewrite Ev_ball// /ev_fun sprod_fstE sprod_sndE. Qed.

End EvMorphism.

Arguments Ev {R Ar} B C.
Arguments Ev_ball {R Ar B C} φ.
Arguments Ev_pair {R Ar B C} f x.

(** ** Currying — Paper §7.4 (lines 5972–6074)

    Given [h : SCones(sprod D B, C)] and [z : D] with [‖z‖ ≤ 1], the
    section [x ↦ h(z, x)] is a stable-and-measurable map [B → C] of
    norm [≤ 1] (the paper's [g(z)]); we 0-extend it to [curry_app h z :
    stablehom B C].  The currying morphism [curry h : SCones(D, B ⇒ₛ C)]
    sends [z ↦ curry_app h z] (0-extended).

    The pairing-with-fixed-[z] section [B → sprod D B], [x ↦ ⟨z, x⟩], is
    used pervasively; on [B_B] (with [‖z‖ ≤ 1]) it lands in the product
    unit ball ([sprod_pair_norm_le1]), and the (7.1) data on the
    [B]-side transports to product (7.1) data with [D]-increments [0]. *)

Section CurryApp.
Variable R : realType.
Variable Ar : MeasSubcat R.
Variables D B C : ICone.type Ar.
Local Open Scope precone_scope.

Local Notation SDB := (sprod D B).

Variable h : scones_hom SDB C.

(** The bare section [x ↦ h(z, x)] (before 0-extension). *)
Definition cap_fun (z : D) : B -> C := fun x => sc_fun h (sprod_pair z x).

(** A product (7.1)-argument with [D]-increment [0]: pairing the centre
    [z] with the [B]-side (7.1)-argument is the product (7.1)-argument of
    [(z, x)] with increments [(0, w i)]. *)
Lemma cap_tm_arg (z : D) (n : nat) (x : B) (w : 'I_n -> B) (I : {set 'I_n}) :
  sprod_pair z (tm_arg x w I) =
  tm_arg (sprod_pair z x) (fun i => sprod_pair (0 : D) (w i)) I.
Proof.
rewrite /tm_arg.
apply: cones_prod_eq => -[]; rewrite /=.
- rewrite cones_prod_val_big.
  rewrite (eq_bigr (fun=> (0 : D))); last by move=> i _.
  by rewrite big1// precone_addr0.
- rewrite cones_prod_val_big.
  by congr (_ + _); apply: eq_bigr.
Qed.

(** The full product-increment sum with [D]-component [0]: pairs [z]
    with [x + Σ w] (the [n]-fold version of [cap_tm_arg] at [I = setT]). *)
Lemma cap_full (z : D) (n : nat) (x : B) (w : 'I_n -> B) :
  cone_norm z <= 1 ->
  cone_norm (x + \big[precone_add/precone_zero]_(i : 'I_n) w i) <= 1 ->
  cone_norm (sprod_pair z x +
     \big[precone_add/precone_zero]_(i : 'I_n)
        sprod_pair (0 : D) (w i)) <= 1.
Proof.
move=> Hz Hxw.
have -> : sprod_pair z x +
    \big[precone_add/precone_zero]_(i : 'I_n) sprod_pair (0 : D) (w i) =
    sprod_pair z (x + \big[precone_add/precone_zero]_(i : 'I_n) w i).
  apply: cones_prod_eq => -[]; rewrite /=.
  - rewrite (big_morph (cones_prod_val^~ true) (fun a b => erefl) (erefl))/=.
    rewrite (eq_bigr (fun=> (0 : D))); last by move=> i _.
    by rewrite big1// precone_addr0.
  - rewrite (big_morph (cones_prod_val^~ false) (fun a b => erefl) (erefl))/=.
    by congr (_ + _); apply: eq_bigr.
exact: sprod_pair_norm_le1.
Qed.

(** Total monotonicity of the section [x ↦ h(z, x)] on [B_B], for
    [‖z‖ ≤ 1]: it is [is_totmono h] at centre [(z, x)] with the
    [D]-increment-[0] family [(0, w i)]. *)
Lemma cap_totmono (z : D) : cone_norm z <= 1 -> is_totmono (cap_fun z).
Proof.
move=> Hz n x w Hxw; rewrite /cap_fun.
under eq_bigr => I _ do rewrite cap_tm_arg.
under [X in _ <=p X]eq_bigr => I _ do rewrite cap_tm_arg.
have [[Htm _ _] _] := sc_meas_stable h.
by apply: Htm; exact: cap_full.
Qed.

(** Boundedness of the section on [B_B] (for [‖z‖ ≤ 1]): each value
    [h(z, x)] has norm [≤ ‖h‖ ≤ 1] since [⟨z, x⟩ ∈ B_{sprod}]. *)
Lemma cap_bounded (z : D) :
  cone_norm z <= 1 ->
  exists M : R, forall x : B, cone_norm x <= 1 -> cone_norm (cap_fun z x) <= M.
Proof.
move=> Hz; exists 1 => x Hx; rewrite /cap_fun.
exact: (sc_image_ball h (sprod_pair_norm_le1 z x Hz Hx)).
Qed.

(** The section commutes with the unit-ball supremum: pairing [z] with
    a [B]-chain supremum is the [sprod]-supremum of the paired chain
    (the [sprod]-sup is componentwise — [z] constant, [u] varying). *)
Lemma sprod_pair_sup (z : D) (u : nat -> B)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, cone_norm (u n) <= 1) (Hz : cone_norm z <= 1)
    (pch : forall n, precone_le (sprod_pair z (u n)) (sprod_pair z (u n.+1)))
    (pb1 : forall n, cone_norm (sprod_pair z (u n)) <= 1) :
  sprod_pair z (cone_sup_ball u uch ub1) =
  cone_sup_ball (fun n => sprod_pair z (u n)) pch pb1.
Proof.
set S := cone_sup_ball (fun n => sprod_pair z (u n)) pch pb1.
(* The [true]-component of the paired-chain sup is [z] (constant chain). *)
have Etrue : cones_prod_val S true = z.
  apply: precone_le_anti.
  - apply: cone_sup_ball_lub => n.
    by have ->: cones_prod_val (sprod_pair z (u n)) true = z by [];
       exact: precone_le_refl.
  - have KEY := cones_prod_le_comp (cone_sup_ball_ub _ pch pb1 0%N) true.
    by move: KEY; have ->: cones_prod_val (sprod_pair z (u 0%N)) true = z by [].
(* The [false]-component is [cone_sup_ball u] (the [B]-chain sup). *)
have Efalse : cones_prod_val S false = cone_sup_ball u uch ub1.
  apply: precone_le_anti.
  - apply: cone_sup_ball_lub => n.
    have ->: cones_prod_val (sprod_pair z (u n)) false = u n by [].
    exact: cone_sup_ball_ub.
  - apply: cone_sup_ball_lub => n.
    have := cones_prod_le_comp (cone_sup_ball_ub _ pch pb1 n) false.
    by have ->: cones_prod_val (sprod_pair z (u n)) false = u n by [].
apply: cones_prod_eq => -[].
- by rewrite Etrue.
- by rewrite Efalse.
Qed.

(** ω-continuity of the section on [B_B] (for [‖z‖ ≤ 1]): commute the
    [B]-sup through the section ([sprod_pair_sup]) and through [h]'s own
    Scott-continuity. *)
Lemma cap_scott (z : D) :
  cone_norm z <= 1 -> is_scott_continuous_unit (cap_fun z).
Proof.
move=> Hz Mf u uch ub1 fuch fubMf Mfpos; rewrite /cap_fun.
have pch n : precone_le (sprod_pair z (u n)) (sprod_pair z (u n.+1)).
  by apply: cones_prod_le_compI => -[];
    rewrite ?sprod_fstE ?sprod_sndE; [exact: precone_le_refl | exact: uch].
have pb1 n : cone_norm (sprod_pair z (u n)) <= 1.
  exact: sprod_pair_norm_le1.
rewrite (sprod_pair_sup (z:=z) (u:=u) uch ub1 Hz pch pb1).
have [[_ _ Hsc] _] := sc_meas_stable h.
rewrite (Hsc Mf (fun n => sprod_pair z (u n)) pch pb1 fuch fubMf Mfpos).
by apply: precone_le_anti; apply: cone_sup_at_lub => n;
  exact: cone_sup_at_ub.
Qed.

(** Path-preservation of the section on [B_B] (for [‖z‖ ≤ 1]): a
    unit-ball [B]-path [γ] gives the unit-ball [sprod]-path
    [r ↦ ⟨z, γ r⟩] (constant [D]-component, [γ] in [B]-component), which
    [h] preserves. *)
Lemma cap_pres_path (z : D) :
  cone_norm z <= 1 ->
  forall (X : ar_obj Ar) (γ : ar_carrier Ar X -> B),
    (forall r, cone_norm (γ r) <= 1) ->
    is_measurable_path (Ar:=Ar) (C:=B) γ ->
    is_measurable_path (Ar:=Ar) (C:=C) (fun r => cap_fun z (γ r)).
Proof.
move=> Hz X γ Hγb Hγ; rewrite /cap_fun.
(* the paired path [r ↦ ⟨z, γ r⟩] is a unit-ball [sprod]-path *)
have Hpb r : cone_norm (sprod_pair z (γ r)) <= 1.
  exact: sprod_pair_norm_le1.
have Hpair : is_measurable_path (Ar:=Ar) (C:=SDB)
    (fun r => sprod_pair z (γ r)).
  split; first by exists 1 => r.
  move=> Y m mM.
  have [i [n [nM ->]]] := mM.
  (* A product test [iniTest i n] reads the [i]-component pointwise. *)
  rewrite (_ : (fun p : (ar_carrier Ar Y * ar_carrier Ar X)%type =>
       iniTest i n p.1 (sprod_pair z (γ p.2)))
     = (fun p => test_fun n p.1
          (cones_prod_val (sprod_pair z (γ p.2)) i))); last first.
    by apply: funext => p; rewrite /iniTest /= /iniTest_fun.
  case: i n nM => n nM /=.
  - (* [D]-component: constant [z], a constant section *)
    have Hc : is_measurable_path (Ar:=Ar) (C:=D) (fun _ : ar_carrier Ar X => z).
      exact: const_path_measurable.
    by have [_ Hcj] := Hc; have := Hcj Y n nM; apply: eq_measurable_fun.
  - (* [B]-component: the [γ]-path *)
    by have [_ Hγj] := Hγ; have := Hγj Y n nM; apply: eq_measurable_fun.
have [_ Hhp] := sc_meas_stable h.
exact: (Hhp X (fun r => sprod_pair z (γ r)) Hpb Hpair).
Qed.

(** The section [x ↦ h(z, x)] is measurable-stable on [B_B], for
    [‖z‖ ≤ 1] (paper: [g(z) ∈ Cuball(B ⇒ₛ C)]). *)
Lemma cap_meas_stable (z : D) :
  cone_norm z <= 1 -> is_meas_stable (cap_fun z).
Proof.
move=> Hz; split; first split.
- exact: cap_totmono.
- exact: cap_bounded.
- exact: cap_scott.
- exact: cap_pres_path.
Qed.

(** *** [curry_app h z : stablehom B C] — the 0-extended section

    For [‖z‖ ≤ 1] we package the 0-extension [sc_clamp (cap_fun z)] (the
    section [x ↦ h(z, x)], extended by [0] off [B_B]) as a [stablehom];
    off [B_D] (when [‖z‖ > 1]) it is the zero map [sh_zero].  This makes
    [curry_app h] a total [D → stablehom B C] (it will itself be
    0-extended at the [D]-level by [curry] below). *)

(** The [D]-guarded section: [h(z, x)] when [‖z‖ ≤ 1], else [0].  This
    side-steps a proof-carrying [match]: the guard makes the function
    [is_meas_stable] *uniformly* (on [B_B] it agrees with [cap_fun z],
    stable for [‖z‖ ≤ 1], or with the zero map otherwise). *)
Definition capg_fun (z : D) : B -> C :=
  fun x => if cone_norm z <= 1 then sc_fun h (sprod_pair z x) else precone_zero.

Lemma capg_meas_stable (z : D) : is_meas_stable (capg_fun z).
Proof.
rewrite /capg_fun; have [Hz | Hz] := boolP (cone_norm z <= 1).
- exact: (cap_meas_stable Hz).
- exact: (meas_stable_zero B C).
Qed.

Lemma capg_clamp_meas_stable (z : D) :
  is_meas_stable (sc_clamp (capg_fun z)).
Proof. exact: sc_clamp_meas_stable (capg_meas_stable z). Qed.

(** [curry_app h z : stablehom B C] — the section, 0-extended off [B_B]. *)
Definition curry_app (z : D) : stablehom B C :=
  MkStablehom (sc_clamp (capg_fun z)) (capg_clamp_meas_stable z)
    (sc_clamp_offball_field _).

(** On [B_D] (for [‖z‖ ≤ 1]) and on [B_B] (for [‖x‖ ≤ 1]),
    [curry_app h z] computes to [h(z, x)]. *)
Lemma curry_app_ball (z : D) (x : B) :
  cone_norm z <= 1 -> cone_norm x <= 1 ->
  sh_fun (curry_app z) x = sc_fun h (sprod_pair z x).
Proof.
by move=> Hz Hx; rewrite /curry_app /= (sc_clamp_ball Hx) /capg_fun Hz.
Qed.

(** Off [B_D] (for [‖z‖ > 1]) [curry_app h z] is the zero stable map. *)
Lemma curry_app_off (z : D) :
  ~~ (cone_norm z <= 1) -> curry_app z = sh_zero B C.
Proof.
move=> Hz; apply: stablehom_eq => x; rewrite /curry_app /= /stm_zero.
have [Hx | Hx] := boolP (cone_norm x <= 1).
  by rewrite (sc_clamp_ball Hx) /capg_fun (negbTE Hz).
by rewrite (sc_clamp_offball Hx).
Qed.

(** The operator norm of [curry_app h z] is [≤ 1]. *)
Lemma curry_app_norm (z : D) : sh_norm (curry_app z) <= 1.
Proof.
apply: sh_norm_lub => x Hx; rewrite /curry_app /= (sc_clamp_ball Hx) /capg_fun.
have [Hz | _] := boolP (cone_norm z <= 1); last by rewrite cone_norm0 ler01.
exact: (sc_image_ball h (sprod_pair_norm_le1 z x Hz Hx)).
Qed.

End CurryApp.

Arguments cap_fun {R Ar D B C} h z.
Arguments curry_app {R Ar D B C} h z.
Arguments curry_app_ball {R Ar D B C} h z x.
Arguments curry_app_off {R Ar D B C} h z.
Arguments curry_app_norm {R Ar D B C} h z.

(** ** Total monotonicity of [curry h] — Paper §7.4 (lines 5978–6053)

    The total-monotonicity inequality of [curry h] lives in the cone
    [stablehom B C].  We reduce it through the cone-order
    characterisation [sh_le_of_alt] (Lemma 7.12 backward) to a pointwise
    comparison [Hpw] (over [B_B]) and the alternating condition
    [sh_alt].  Both reduce to total monotonicity of [h] over [sprod D B]
    with the *interleaved* increment family [(w_i, 0)] / [(0, u_j)],
    classified by the parity-multiplicative [catf]/[catset] split of
    [compose.v] ([Spos_cat]/[Sneg_cat]). *)

Section CurryTotmono.
Variable R : realType.
Variable Ar : MeasSubcat R.
Variables D B C : ICone.type Ar.
Local Open Scope precone_scope.

Local Notation SDB := (sprod D B).
Variable h : scones_hom SDB C.

(** [h] paired against the interleaved increments reads as the
    [sprod D B]-shift: [h(z + Σ_I w, x + Σ_J u)] is [h] at
    [(z, x) + Σ_{catset(I,J)} ipair]. *)
Definition ipair (n k : nat) (w : 'I_n -> D) (u : 'I_k -> B)
    : 'I_(n + k) -> SDB :=
  catf (fun i => sprod_pair (w i) (0 : B)) (fun j => sprod_pair (0 : D) (u j)).

(** A cone-sum of [ipair]-increments over [catset (I, J)] is the
    pairing of the [D]-sum [Σ_I w] with the [B]-sum [Σ_J u]. *)
Lemma sumP_ipair (n k : nat) (w : 'I_n -> D) (u : 'I_k -> B)
    (I : {set 'I_n}) (J : {set 'I_k}) :
  \big[precone_add/precone_zero]_(l in catset (I, J)) ipair w u l =
  sprod_pair (\big[precone_add/precone_zero]_(i in I) w i)
             (\big[precone_add/precone_zero]_(j in J) u j).
Proof.
rewrite /ipair sumP_catf setL_catset setR_catset.
apply: cones_prod_eq => -[].
- have valDt (a b : SDB) :
    cones_prod_val (a + b) true = cones_prod_val a true + cones_prod_val b true
    by [].
  rewrite valDt.
  rewrite (big_morph (cones_prod_val^~ true) (fun a b => erefl) (erefl))/=.
  rewrite (big_morph (cones_prod_val^~ true) (fun a b => erefl) (erefl))/=.
  have HZ : \big[precone_add/precone_zero]_(j in J) (0 : D) = precone_zero
    by apply: big1.
  by rewrite HZ precone_addr0.
- have valDf (a b : SDB) :
    cones_prod_val (a + b) false =
    cones_prod_val a false + cones_prod_val b false
    by [].
  rewrite valDf.
  rewrite (big_morph (cones_prod_val^~ false) (fun a b => erefl) (erefl))/=.
  rewrite (big_morph (cones_prod_val^~ false) (fun a b => erefl) (erefl))/=.
  have HZ : \big[precone_add/precone_zero]_(i in I) (0 : B) = precone_zero
    by apply: big1.
  by rewrite HZ precone_add0.
Qed.

(** [h] at the [ipair]-shift equals [h] at the paired shifts. *)
Lemma h_ipair (n k : nat) (z : D) (x : B) (w : 'I_n -> D) (u : 'I_k -> B)
    (I : {set 'I_n}) (J : {set 'I_k}) :
  sc_fun h (tm_arg (sprod_pair z x) (ipair w u) (catset (I, J))) =
  sc_fun h (sprod_pair (z + \big[precone_add/precone_zero]_(i in I) w i)
                       (x + \big[precone_add/precone_zero]_(j in J) u j)).
Proof.
congr (sc_fun h _); rewrite /tm_arg sumP_ipair.
by rewrite -sprod_pairD.
Qed.

(** The cone-sum of [curry_app]s evaluated at a ball point [y] is the
    cone-sum of the [h]-values, provided every [z + Σ_I w] is in
    [B_D]. *)
Lemma sh_sum_curry (n : nat) (z : D) (w : 'I_n -> D) (A : {set {set 'I_n}})
    (y : B) (Hy : cone_norm y <= 1)
    (HzI : forall I : {set 'I_n},
       cone_norm (z + \big[precone_add/precone_zero]_(i in I) w i) <= 1) :
  sh_fun (\big[precone_add/precone_zero]_(I in A)
            curry_app h (z + \big[precone_add/precone_zero]_(i in I) w i)) y =
  \big[precone_add/precone_zero]_(I in A)
     sc_fun h (sprod_pair (z + \big[precone_add/precone_zero]_(i in I) w i) y).
Proof.
rewrite sh_bigE; apply: eq_bigr => I _.
by rewrite (curry_app_ball _ _ _ (HzI I) Hy).
Qed.

(** The cone-sum of the [D]-increments [(w_i, 0)] over [I] is the
    pairing [(Σ_I w, 0)]. *)
Lemma sumP_pair_w (n : nat) (w : 'I_n -> D) (I : {set 'I_n}) :
  \big[precone_add/precone_zero]_(i in I) sprod_pair (w i) (0 : B) =
  sprod_pair (\big[precone_add/precone_zero]_(i in I) w i) (0 : B).
Proof.
apply: cones_prod_eq => -[].
- rewrite (big_morph (cones_prod_val^~ true) (fun a b => erefl) (erefl))/=.
  by apply: eq_bigr.
- rewrite (big_morph (cones_prod_val^~ false) (fun a b => erefl) (erefl))/=.
  by rewrite (_ : \big[_/_]_(i in I) (0 : B) = precone_zero) ?big1.
Qed.

(** The combinatorial bridge.  [Spos]/[Sneg] of [h] over the
    [D]-increment family [(w_i, 0)], at the [J]-shifted centre
    [(z, x + Σ_J u)], are the [Ppos]/[Pneg]-block sums of [h]-values —
    equivalently, [sh_fun] of the [Ppos n]/[Pneg n] cone-sum of
    [curry_app]s at [x + Σ_J u]. *)
Lemma Spos_h_curry (n : nat) (z : D)
    (w : 'I_n -> D) (y : B)
    (Hx : cone_norm y <= 1)
    (HzI : forall I : {set 'I_n},
       cone_norm (z + \big[precone_add/precone_zero]_(i in I) w i) <= 1) :
  Spos (sc_fun h) n (fun i => sprod_pair (w i) (0 : B)) (sprod_pair z y) =
  sh_fun (\big[precone_add/precone_zero]_(I in Ppos n)
            curry_app h (z + \big[precone_add/precone_zero]_(i in I) w i)) y.
Proof.
rewrite (sh_sum_curry (Ppos n) Hx HzI) /Spos.
apply: eq_bigr => I _; congr (sc_fun h _).
by rewrite sumP_pair_w -sprod_pairD precone_addr0.
Qed.

Lemma Sneg_h_curry (n : nat) (z : D)
    (w : 'I_n -> D) (y : B)
    (Hx : cone_norm y <= 1)
    (HzI : forall I : {set 'I_n},
       cone_norm (z + \big[precone_add/precone_zero]_(i in I) w i) <= 1) :
  Sneg (sc_fun h) n (fun i => sprod_pair (w i) (0 : B)) (sprod_pair z y) =
  sh_fun (\big[precone_add/precone_zero]_(I in Pneg n)
            curry_app h (z + \big[precone_add/precone_zero]_(i in I) w i)) y.
Proof.
rewrite (sh_sum_curry (Pneg n) Hx HzI) /Sneg.
apply: eq_bigr => I _; congr (sc_fun h _).
by rewrite sumP_pair_w -sprod_pairD precone_addr0.
Qed.

(** The [B]-increment family [(0, u_j)] sums to [(0, Σ_Bs u)], so the
    [Bincr]-shift of the centre [(z, x)] is [(z, x + Σ_Bs u)]. *)
Lemma sprod_Bincr_shift (k : nat) (z : D) (x : B) (u : 'I_k -> B)
    (Bs : {set 'I_k}) :
  sprod_pair z x +
    \big[precone_add/precone_zero]_(j in Bs) sprod_pair (0 : D) (u j) =
  sprod_pair z (x + \big[precone_add/precone_zero]_(j in Bs) u j).
Proof.
have HZ : \big[precone_add/precone_zero]_(j in Bs) sprod_pair (0 : D) (u j) =
    sprod_pair (0 : D) (\big[precone_add/precone_zero]_(j in Bs) u j).
  apply: cones_prod_eq => -[].
  - rewrite (big_morph (cones_prod_val^~ true) (fun a b => erefl) (erefl))/=.
    by rewrite (_ : \big[_/_]_(j in Bs) (0 : D) = precone_zero) ?big1.
  - rewrite (big_morph (cones_prod_val^~ false) (fun a b => erefl) (erefl))/=.
    by apply: eq_bigr.
by rewrite HZ -sprod_pairD precone_addr0.
Qed.

(** **Lemma 7.27/§7.4 — total monotonicity of [curry h], the cone step.**
    The (7.1) inequality of [curry h] *in the cone* [stablehom B C].
    Through [sh_le_of_alt] (the stable-order characterisation, Lemma
    7.12 backward) it reduces to the pointwise comparison [Hpw] and the
    alternating condition [sh_alt]; both are total monotonicity of [h]
    over [sprod D B] with the [D]-increments [(w_i, 0)] (and, for
    [sh_alt], the interleaved [(0, u_j)]), classified by the
    [Spos_cat]/[Sneg_cat] parity-multiplicative split. *)
Lemma curry_totmono_step (n : nat) (z : D) (w : 'I_n -> D)
    (Hzw : cone_norm (z + \big[precone_add/precone_zero]_(i : 'I_n) w i) <= 1) :
  precone_le
    (\big[precone_add/precone_zero]_(I in Pneg n)
       curry_app h (z + \big[precone_add/precone_zero]_(i in I) w i))
    (\big[precone_add/precone_zero]_(I in Ppos n)
       curry_app h (z + \big[precone_add/precone_zero]_(i in I) w i)).
Proof.
have [[Hhm _ _] _] := sc_meas_stable h.
(* Every sub-sum [z + Σ_I w] is in [B_D]. *)
have HzI (I : {set 'I_n}) :
    cone_norm (z + \big[precone_add/precone_zero]_(i in I) w i) <= 1.
  apply: le_trans Hzw; apply: cone_normp; apply: precone_add_le_l.
  exact: sumP_sub_le.
apply: sh_le_of_alt.
- (* [Hpw]: pointwise on [B_B] — [is_totmono h] at [(z,x)] over the
     [D]-increments [(w_i, 0)]. *)
  move=> x Hx.
  rewrite -(Spos_h_curry (z:=z) (w:=w) (y:=x) Hx HzI)
          -(Sneg_h_curry (z:=z) (w:=w) (y:=x) Hx HzI).
  apply: (Sneg_le_Spos Hhm).
  rewrite (_ : \big[precone_add/precone_zero]_(i : 'I_n) sprod_pair (w i) (0 : B) =
               sprod_pair (\big[precone_add/precone_zero]_(i : 'I_n) w i) (0 : B));
    last first.
    apply: cones_prod_eq => -[].
    + rewrite (big_morph (cones_prod_val^~ true) (fun a b => erefl) (erefl))/=.
      by apply: eq_bigr.
    + rewrite (big_morph (cones_prod_val^~ false) (fun a b => erefl) (erefl))/=.
      by rewrite (_ : \big[_/_]_(i : 'I_n) (0 : B) = precone_zero) ?big1.
  rewrite -sprod_pairD precone_addr0.
  exact: sprod_pair_norm_le1.
(* [sh_alt]: the alternating four-block sum reorganises (via the bridge
   lemmas + [Spos_cat]/[Sneg_cat]) into [Sneg ≤p Spos] of [h] over the
   interleaved [catf]-family at centre [(z, x)] — its own total
   monotonicity. *)
move=> k x u Hxu.
have HxJ (J : {set 'I_k}) :
    cone_norm (x + \big[precone_add/precone_zero]_(j in J) u j) <= 1.
  apply: le_trans Hxu; apply: cone_normp; apply: precone_add_le_l.
  exact: sumP_sub_le.
rewrite /tm_arg.
(* Rewrite the four blocks via [Spos_h_curry]/[Sneg_h_curry]. *)
under eq_bigr => J _ do rewrite -(Spos_h_curry (z:=z) (w:=w)
  (y:=x + \big[precone_add/precone_zero]_(j in J) u j) (HxJ J) HzI).
under [X in (_ + X)%PC]eq_bigr => J _ do rewrite -(Sneg_h_curry (z:=z) (w:=w)
  (y:=x + \big[precone_add/precone_zero]_(j in J) u j) (HxJ J) HzI).
under [X in precone_le _ (X + _)]eq_bigr => J _ do rewrite -(Spos_h_curry
  (z:=z) (w:=w) (y:=x + \big[precone_add/precone_zero]_(j in J) u j) (HxJ J) HzI).
under [X in precone_le _ (_ + X)]eq_bigr => J _ do rewrite -(Sneg_h_curry
  (z:=z) (w:=w) (y:=x + \big[precone_add/precone_zero]_(j in J) u j) (HxJ J) HzI).
(* Fold the centre into the [Bincr]-shift, then [Spos_cat]/[Sneg_cat]. *)
under eq_bigr => J _ do rewrite -sprod_Bincr_shift.
under [X in (_ + X)%PC]eq_bigr => J _ do rewrite -sprod_Bincr_shift.
under [X in precone_le _ (X + _)]eq_bigr => J _ do rewrite -sprod_Bincr_shift.
under [X in precone_le _ (_ + X)]eq_bigr => J _ do rewrite -sprod_Bincr_shift.
rewrite -(Spos_cat (sc_fun h) (fun i : 'I_n => sprod_pair (w i) (0 : B))
            (fun j : 'I_k => sprod_pair (0 : D) (u j)) (sprod_pair z x)).
rewrite [X in precone_le X _]precone_addC.
rewrite -(Sneg_cat (sc_fun h) (fun i : 'I_n => sprod_pair (w i) (0 : B))
            (fun j : 'I_k => sprod_pair (0 : D) (u j)) (sprod_pair z x)).
apply: (Sneg_le_Spos Hhm).
rewrite sumP_catf_T.
have -> : \big[precone_add/precone_zero]_(i : 'I_n) sprod_pair (w i) (0 : B) =
    sprod_pair (\big[precone_add/precone_zero]_(i : 'I_n) w i) (0 : B).
  apply: cones_prod_eq => -[].
  + rewrite (big_morph (cones_prod_val^~ true) (fun a b => erefl) (erefl))/=.
    by apply: eq_bigr.
  + rewrite (big_morph (cones_prod_val^~ false) (fun a b => erefl) (erefl))/=.
    by rewrite (_ : \big[_/_]_(i : 'I_n) (0 : B) = precone_zero) ?big1.
have -> : \big[precone_add/precone_zero]_(j : 'I_k) sprod_pair (0 : D) (u j) =
    sprod_pair (0 : D) (\big[precone_add/precone_zero]_(j : 'I_k) u j).
  apply: cones_prod_eq => -[].
  + rewrite (big_morph (cones_prod_val^~ true) (fun a b => erefl) (erefl))/=.
    by rewrite (_ : \big[_/_]_(j : 'I_k) (0 : D) = precone_zero) ?big1.
  + rewrite (big_morph (cones_prod_val^~ false) (fun a b => erefl) (erefl))/=.
    by apply: eq_bigr.
rewrite -!sprod_pairD !precone_addr0 !precone_add0.
exact: sprod_pair_norm_le1.
Qed.

End CurryTotmono.

Arguments ipair {R Ar D B} {n k} w u.
Arguments sumP_ipair {R Ar D B n k} w u I J.
Arguments h_ipair {R Ar D B C} h {n k} z x w u I J.
Arguments curry_totmono_step {R Ar D B C} h n z w Hzw.

(** ** The currying morphism [curry h] — Paper §7.4

    [curry h : SCones(D, B ⇒ₛ C)] sends [z ↦ curry_app h z], 0-extended
    off [B_D].  Its total monotonicity is [curry_totmono_step]; its
    ω-continuity is the [sup]-of-stable-functions machinery
    ([sh_sup_ball_ub] / [sh_sup_ball_lub]); its path-preservation is the
    test-pullback argument (lines 6058–6074). *)

Section Curry.
Variable R : realType.
Variable Ar : MeasSubcat R.
Variables D B C : ICone.type Ar.
Local Open Scope precone_scope.

Local Notation SDB := (sprod D B).
Local Notation H := (stablehom B C : ICone.type Ar).
Variable h : scones_hom SDB C.

(** [curry_app h] is increasing on [B_D] (from total monotonicity). *)
Lemma curry_app_incr (z z' : D) :
  z <=p z' -> cone_norm z' <= 1 -> curry_app h z <=p curry_app h z'.
Proof. exact: (tm_incr_le (R:=R) (Q:=H) (curry_totmono_step h)). Qed.

(** Total monotonicity of [curry_app h] (Def 7.5 form). *)
Lemma curry_app_totmono : is_totmono (curry_app h).
Proof. by move=> n z w Hzw; exact: (curry_totmono_step h). Qed.

End Curry.