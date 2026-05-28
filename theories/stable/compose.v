(**md**************************************************************)
(** * Composition of stable functions — Paper §7.3 (Lemmas 7.23, 7.25,
      7.26, 7.27 and the closure of stable maps under composition)

    This file completes the §7.3 "finite differences" track opened in
    [stable/findiff.v], delivering the combinatorial heart that the paper
    needs to prove that totally monotonic — hence stable — functions are
    closed under composition (the §7.3 analogue of the Faà di Bruno
    formula).

    The track sits entirely on the *B-side* difference engine [SD] of
    [findiff.v] ([SD], [SD_E], [SD0], [SD_cons], [SD_add], [SD_le],
    [SD_Delta]) so that all the recurrences are pure cone-sum identities on
    bare [B]-centres, free of local-cone casts.  We add:

    - the *joint monotonicity* engine for [SD] (Section [SDmono]):
      monotonicity in the centre [SD_mono_centre] (Lemma 7.17, via
      [Sdiff_mono]), monotonicity in a single (head) direction
      [SD_mono_head] (via [SD_add]), the symmetry of [SD] under
      reindexing the direction family by a permutation
      ([Spos_perm]/[Sneg_perm]/[SD_perm]) and the resulting monotonicity
      in *all* directions [SD_mono_dirs] and jointly [SD_mono_full];
    - **Lemma 7.25** ([SnB_increasing]): the map [(x,u⃗) ↦ Δf(u⃗)(x)] is
      increasing [B_{SnB} → C], read off [SD_mono_full] (no ω-continuity
      needed: it is the joint centre/direction monotonicity of the
      difference, which the paper derives "from Theorem 7.19");
    - the **B-side reformulation** of Def 7.15 / Lemmas 7.16–7.18: the
      bare-[B] difference [dB], the [p]-increasing predicate [Sinc] whose
      recursion never leaves [B → C], the multi-direction bootstrap
      [Sinc_dB] (Lemma 7.16, immediate B-side), and the B-side Lemma 7.18
      engine [totmono_dB] ([dB f u] is totally monotonic on the
      shifted ball).  This sidesteps the nested-local-cone cast that blocks
      the local-cone [is_n_increasing] recursion of [findiff.v].

    Paper reference: §7.3 (pages 1:62–1:65), Lemmas 7.23, 7.25, 7.26, 7.27
    and Theorem 7.30. *)
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
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.path.
Require Import Icones.stable.local_cone.
Require Import Icones.stable.totmono.
Require Import Icones.stable.stablehom.
Require Import Icones.stable.findiff.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(** ** Joint monotonicity of the B-side difference [SD] — Paper §7.3

    The difference [SD f n u⃗ xb] is increasing in its centre [xb] and in
    each of its directions [u⃗], jointly.  This is the content the paper
    derives "from Theorem 7.19" for Lemmas 7.25 and the base case [p = 0]
    of Lemma 7.26; we obtain it directly from total monotonicity of [f]
    (no ω-continuity), through the §7.3 recurrences. *)

Section SDmono.
Variable R : realType.
Variables B C : coneType R.
Variable f : B -> C.
Hypothesis Hf : is_totmono f.
Local Open Scope precone_scope.

(** [SD] is well defined ([Sneg ≤ Spos]) under the unit-ball bound. *)
Lemma SDwd (n : nat) (u : 'I_n -> B) (xb : B) :
  cone_norm (xb + \big[precone_add/precone_zero]_(i : 'I_n) u i) <= 1 ->
  Sneg f n u xb <=p Spos f n u xb.
Proof. by move=> Hc; exact: (Sneg_le_Spos Hf). Qed.

(** Monotone in the centre: [SD u⃗ xb ≤p SD u⃗ (xb + d)] (Lemma 7.17). *)
Lemma SD_mono_centre (n : nat) (u : 'I_n -> B) (xb d : B) :
  cone_norm ((xb + d) +
     \big[precone_add/precone_zero]_(i : 'I_n) u i) <= 1 ->
  SD f u xb <=p SD f u (xb + d).
Proof.
move=> Hc.
have Hxb : cone_norm (xb +
    \big[precone_add/precone_zero]_(i : 'I_n) u i) <= 1.
  apply: le_trans Hc; apply: cone_normp.
  by apply: precone_add_le_r; exists d.
have ED := SD_E f u (xb + d) (SDwd Hc).
have E0 := SD_E f u xb (SDwd Hxb).
have Hcons : cone_norm (xb +
    \big[precone_add/precone_zero]_(i : 'I_n.+1) vcons d u i) <= 1.
  by rewrite sum_vcons precone_addA.
have HM := Sdiff_mono Hf (n:=n) (u:=d) (w:=u) (xb:=xb) Hcons.
rewrite E0 ED in HM.
set Sn1 := Sneg f n u (xb + d) in HM.
set Sn0 := Sneg f n u xb in HM.
apply: (precone_le_addlI (Sn1 + Sn0)).
apply: (@precone_le_trans _ _ (Sn1 + (Sn0 + SD f u xb))).
  rewrite precone_addA; exact: precone_le_refl.
apply: precone_le_trans HM _.
rewrite -precone_addA [SD f u (xb + d) + Sn0]precone_addC precone_addA.
exact: precone_le_refl.
Qed.

(** Monotone in the head direction: [SD (a::w) xb ≤p SD ((a+e)::w) xb]. *)
Lemma SD_mono_head (n : nat) (a e : B) (w : 'I_n -> B) (xb : B) :
  cone_norm (xb +
     \big[precone_add/precone_zero]_(i : 'I_n.+1) vcons (a + e) w i) <= 1 ->
  SD f (vcons a w) xb <=p SD f (vcons (a + e) w) xb.
Proof.
move=> Hc.
rewrite (SD_add f Hf a e w xb Hc).
by exists (SD f (vcons e w) (xb + a)); rewrite precone_addC.
Qed.

End SDmono.

Arguments SDwd {R B C} f Hf {n} u xb.
Arguments SD_mono_centre {R B C} f Hf {n} u xb d.
Arguments SD_mono_head {R B C} f Hf {n} a e w xb.

(** *** Symmetry of [SD] under reindexing the directions

    [Spos]/[Sneg] are invariant under reindexing the family [u⃗] by a
    permutation [s] of ['I_n]: the image map [I ↦ s @: I] bijects [Pε(n)]
    with itself (it preserves cardinality, [s] injective) and the inner
    cone-sum reindexes by [s].  Hence so is the difference [SD]. *)

Section SDsym.
Variable R : realType.
Variables B C : coneType R.
Variable f : B -> C.
Local Open Scope precone_scope.

Lemma Spos_perm (n : nat) (s : 'S_n) (u : 'I_n -> B) (xb : B) :
  Spos f n (u \o s) xb = Spos f n u xb.
Proof.
rewrite /Spos.
rewrite [RHS](reindex_inj (h := fun I : {set 'I_n} => s @: I)); last first.
  by apply: imset_inj; exact: perm_inj.
apply: eq_big => I.
  by rewrite !in_Ppos card_imset//; exact: perm_inj.
move=> _; congr (f (xb + _)).
rewrite [RHS]big_imset/=; last by move=> i j _ _; exact: perm_inj.
by apply: eq_bigr.
Qed.

Lemma Sneg_perm (n : nat) (s : 'S_n) (u : 'I_n -> B) (xb : B) :
  Sneg f n (u \o s) xb = Sneg f n u xb.
Proof.
rewrite /Sneg.
rewrite [RHS](reindex_inj (h := fun I : {set 'I_n} => s @: I)); last first.
  by apply: imset_inj; exact: perm_inj.
apply: eq_big => I.
  by rewrite !in_Pneg card_imset//; exact: perm_inj.
move=> _; congr (f (xb + _)).
rewrite [RHS]big_imset/=; last by move=> i j _ _; exact: perm_inj.
by apply: eq_bigr.
Qed.

(** [SD] inherits the symmetry of its two halves. *)
Lemma SD_perm (n : nat) (s : 'S_n) (u : 'I_n -> B) (xb : B) :
  SD f (u \o s) xb = SD f u xb.
Proof. by rewrite /SD Spos_perm Sneg_perm. Qed.

End SDsym.

Arguments Spos_perm {R B C} f {n} s u xb.
Arguments Sneg_perm {R B C} f {n} s u xb.
Arguments SD_perm {R B C} f {n} s u xb.

(** *** Monotonicity in all directions, via symmetry

    A single direction can be increased by transposing it to the head
    ([tperm ord0 k]), applying [SD_mono_head], and transposing back
    ([SD_perm]).  Increasing the *whole* direction family then follows by
    a [{set}]-induction adding one bumped index at a time. *)

Section SDmonoDirs.
Variable R : realType.
Variables B C : coneType R.
Variable f : B -> C.
Hypothesis Hf : is_totmono f.
Local Open Scope precone_scope.

(** Bump the single direction at index [k] by [e]. *)
Lemma SD_mono_idx (n : nat) (v : 'I_n.+1 -> B) (k : 'I_n.+1) (e : B)
    (xb : B) :
  cone_norm (xb + \big[precone_add/precone_zero]_(i : 'I_n.+1)
     (if i == k then v i + e else v i)) <= 1 ->
  SD f v xb <=p SD f (fun i => if i == k then v i + e else v i) xb.
Proof.
move=> Hc.
pose s : 'S_n.+1 := tperm ord0 k.
have sord0 : s ord0 = k by rewrite /s tpermL.
have Ev : v \o s = vcons (v k) (fun i => (v \o s) (lift ord0 i)).
  by rewrite [LHS]vcons_eta /= /comp sord0.
have Ev' : (fun i => if i == k then v i + e else v i) \o s
    = vcons (v k + e) (fun i => (v \o s) (lift ord0 i)).
  apply/funext => j; rewrite /comp /vcons.
  case: (unliftP ord0 j) => [i ->|->].
    case: ifP => // /eqP Hik.
    have : s (lift ord0 i) = s ord0 by rewrite sord0 Hik.
    by move/perm_inj => H; move: (neq_lift ord0 i); rewrite eq_sym H eqxx.
  by rewrite sord0 eqxx.
have <- : SD f (v \o s) xb = SD f v xb by rewrite SD_perm.
have <- : SD f ((fun i => if i == k then v i + e else v i) \o s) xb
    = SD f (fun i => if i == k then v i + e else v i) xb by rewrite SD_perm.
rewrite Ev Ev'; apply: (SD_mono_head f Hf).
rewrite -Ev'.
move: Hc; congr (cone_norm (xb + _) <= 1).
by rewrite (reindex_inj (h := s)) //; exact: perm_inj.
Qed.

End SDmonoDirs.

(** *** Monotone in the full direction family, then jointly

    Increase the whole direction family [u → u'] (pointwise [≤p]) by a
    [{set}]-induction that flips one index at a time to its [u']-value
    (each flip is monotone by [SD_mono_idx]); then combine with
    [SD_mono_centre] for the joint statement [SD_mono_full]. *)

Section SDmonoFull.
Variable R : realType.
Variables B C : coneType R.
Variable f : B -> C.
Hypothesis Hf : is_totmono f.
Local Open Scope precone_scope.

(** The hybrid family agreeing with [u'] on [J] and with [u] off [J]. *)
Definition bumpJ (n : nat) (u u' : 'I_n -> B) (J : {set 'I_n})
    : 'I_n -> B := fun i => if i \in J then u' i else u i.

Lemma bumpJ0 (n : nat) (u u' : 'I_n -> B) :
  bumpJ u u' finset.set0 = u.
Proof. by apply/funext => i; rewrite /bumpJ finset.in_set0. Qed.

Lemma bumpJT (n : nat) (u u' : 'I_n -> B) :
  bumpJ u u' [set: 'I_n] = u'.
Proof. by apply/funext => i; rewrite /bumpJ finset.in_setT. Qed.

(** A bumped family is pointwise below [u'] (used for the norm bounds). *)
Lemma bumpJ_le (n : nat) (u u' : 'I_n -> B) (J : {set 'I_n}) (i : 'I_n) :
  (forall j, u j <=p u' j) -> bumpJ u u' J i <=p u' i.
Proof.
move=> Hle; rewrite /bumpJ; case: ifP => _; [exact: precone_le_refl|exact: Hle].
Qed.

(** Sum monotonicity of a bumped family: [Σ (bumpJ J) ≤p Σ u']. *)
Lemma bumpJ_sum_le (n : nat) (u u' : 'I_n -> B) (J : {set 'I_n}) :
  (forall j, u j <=p u' j) ->
  \big[precone_add/precone_zero]_(i : 'I_n) bumpJ u u' J i <=p
  \big[precone_add/precone_zero]_(i : 'I_n) u' i.
Proof.
move=> Hle; elim/big_rec2: _ => [|i s s' _ Hs]; first exact: precone_le_refl.
apply: precone_le_trans (precone_add_le_l _ Hs).
by apply: precone_add_le_r; exact: bumpJ_le.
Qed.

(** Flipping the bumped set [J → J] grows the difference [SD] monotonically,
    one index at a time ([SD_mono_idx]).  Strong induction on [#|J|]. *)
Lemma SD_dirs_J (n : nat) (u u' : 'I_n.+1 -> B) (xb : B)
    (Hle : forall j, u j <=p u' j)
    (Hbd : cone_norm (xb +
       \big[precone_add/precone_zero]_(i : 'I_n.+1) u' i) <= 1)
    (J : {set 'I_n.+1}) :
  SD f u xb <=p SD f (bumpJ u u' J) xb.
Proof.
have [m] := ubnP #|J|; elim: m J => [|m IHm] J; first by rewrite ltn0.
move=> Hcard.
have [->|/set0Pn[k kJ]] := eqVneq J finset.set0.
  by rewrite bumpJ0; exact: precone_le_refl.
pose J' := J :\ k.
have HJ' : (#|J'| < m)%N.
  by rewrite (cardsD1 k J) kJ /= add1n ltnS in Hcard.
(* [u' k = (bumpJ J') k + e] for the [SD_mono_idx] flip. *)
have [e He] := Hle k.
have bk : bumpJ u u' J' k = u k.
  by rewrite /bumpJ /J' !inE eqxx.
have flipE : bumpJ u u' J =
    (fun i => if i == k then bumpJ u u' J' i + e else bumpJ u u' J' i).
  apply/funext => i; rewrite /bumpJ /J' !inE.
  by case: (eqVneq i k) => [->|ik] /=; first by rewrite kJ -He.
apply: (@precone_le_trans _ _ (SD f (bumpJ u u' J') xb)).
  by apply: IHm.
rewrite flipE; apply: (SD_mono_idx Hf).
apply: le_trans Hbd; apply: cone_normp; apply: precone_add_le_l.
elim/big_rec2: _ => [|i s s' _ Hs]; first exact: precone_le_refl.
apply: precone_le_trans (precone_add_le_l _ Hs).
apply: precone_add_le_r.
case: (eqVneq i k) => [->|ik].
  by rewrite bk -He; exact: precone_le_refl.
exact: bumpJ_le.
Qed.

(** Monotone in the whole direction family. *)
Lemma SD_mono_dirs (n : nat) (u u' : 'I_n.+1 -> B) (xb : B) :
  (forall j, u j <=p u' j) ->
  cone_norm (xb +
     \big[precone_add/precone_zero]_(i : 'I_n.+1) u' i) <= 1 ->
  SD f u xb <=p SD f u' xb.
Proof.
move=> Hle Hbd; have := SD_dirs_J Hle Hbd [set: 'I_n.+1].
by rewrite bumpJT.
Qed.

(** Jointly monotone in centre and all directions (arity [n+1]). *)
Lemma SD_mono_full (n : nat) (u u' : 'I_n.+1 -> B) (xb xb' : B) :
  xb <=p xb' -> (forall j, u j <=p u' j) ->
  cone_norm (xb' +
     \big[precone_add/precone_zero]_(i : 'I_n.+1) u' i) <= 1 ->
  SD f u xb <=p SD f u' xb'.
Proof.
move=> [d ->] Hle Hbd.
apply: (@precone_le_trans _ _ (SD f u (xb + d))).
  apply: (SD_mono_centre f Hf); apply: le_trans Hbd; apply: cone_normp.
  apply: precone_add_le_l.
  elim/big_rec2: _ => [|i s s' _ Hs]; first exact: precone_le_refl.
  apply: precone_le_trans (precone_add_le_l _ Hs).
  by apply: precone_add_le_r; exact: Hle.
exact: (SD_mono_dirs Hle Hbd).
Qed.

End SDmonoFull.

Arguments bumpJ {R B n} u u' J.
Arguments SD_mono_dirs {R B C} f Hf {n} u u' xb.
Arguments SD_mono_full {R B C} f Hf {n} u u' xb xb'.

(** ** Lemma 7.25 — [(x,u⃗) ↦ Δf(u⃗)(x)] increasing [B_{SnB} → C]
       — Paper §7.3 (txt 3705)

    On the cone [SnB B n] (a section [g : 'I_{n+1} → B], centre [g ord0],
    directions [g ∘ lift ord0]) the B-side difference [SnB_diff g :=
    SD f n (g ∘ lift ord0) (g ord0)] — which is [Δf(u⃗)(x)] read on bare
    [B]-data via [SD_Delta] — is increasing for the [SnB] (total-sum) norm.
    "Follows easily from Theorem 7.19": here it is the joint
    centre/direction monotonicity [SD_mono_full] of the difference, with
    no recourse to ω-continuity. *)

Section Lemma725.
Variable R : realType.
Variables B C : coneType R.
Variable f : B -> C.
Hypothesis Hf : is_totmono f.
Variable n : nat.
Local Open Scope precone_scope.

(** The §7.3 difference as a map [SnB B n → C]. *)
Definition SnB_diff (g : SnB B n) : C :=
  SD f (fun i => g (lift ord0 i)) (g ord0).

(** The [SnB]-sum splits into centre [g ord0] and the directions' sum. *)
Lemma snb_sum_recl (g : SnB B n) :
  snb_sum g = g ord0 +
    \big[precone_add/precone_zero]_(i : 'I_n) g (lift ord0 i).
Proof. by rewrite /snb_sum big_ord_recl. Qed.

Lemma SnB_increasing : is_increasing SnB_diff.
Proof.
move=> g v Hnorm; rewrite /SnB_diff.
(* Norm bound on the increased config, read on the B-side. *)
have Hbd : cone_norm ((g + v) ord0 +
    \big[precone_add/precone_zero]_(i : 'I_n) (g + v) (lift ord0 i)) <= 1.
  have En : cone_norm (g + v) = cone_norm (snb_sum (g + v)) by [].
  by move: Hnorm; rewrite En snb_sum_recl.
(* Componentwise [≤p] from [g ≤p g + v] in the [SnB] cone. *)
have Hc0 : g ord0 <=p (g + v) ord0 by exists (v ord0).
have Hdir i : g (lift ord0 i) <=p (g + v) (lift ord0 i)
  by exists (v (lift ord0 i)).
case: n g v Hnorm Hbd Hc0 Hdir => [|m] g v _ Hbd Hc0 Hdir.
  (* No directions: [SD] is just [f] at the centre; [f] increasing. *)
  rewrite !SD0; move: Hc0 => [d Hd].
  rewrite Hd; apply: (totmono_increasing Hf).
  move: Hbd; rewrite big_ord0 precone_addr0 => Hbd; rewrite -Hd; exact: Hbd.
exact: (@SD_mono_full R B C f Hf m _ _ _ _ Hc0 Hdir Hbd).
Qed.

End Lemma725.

(** ** ω-continuity and stability of the dominated shift — Paper §7.3
       (the [Δε] summand engine for [scott_Delta] / Lemma 7.20 [Δf])

    Each [Δε] summand is a *dominated shift* [x ↦ f(lc_val x + s)] of [f]
    by a partial sum [s = Σ_{i∈I} uᵢ ≤p S := Σᵢ uᵢ], read on the local
    cone [B_S = local_cone S].  We show this shift is ω-continuous
    ([scott_shift_le]) and — adding the easy bound — stable
    ([stable_shift_le]).  ω-continuity composes [lc_val_scott]
    (ω-continuity of the inclusion [lc_val : B_S → B], [findiff.v]) with
    [f]'s own [is_scott_continuous_unit]: the input chain [lc_val xₙ + s]
    stays in the unit ball (it is [≤p lc_val xₙ + S ∈ B_B] via [lc_step1],
    the unit ball being [≤p]-downward closed by (Normp)), and the shift
    [+ s] commutes with the [B]-supremum by [sup_ball_addr]. *)

Section StableShift.
Variable R : realType.
Variables B C : coneType R.
Variable f : B -> C.
Local Open Scope precone_scope.

(** **ω-continuity of the dominated shift** [x ↦ f(lc_val x + s)] on
    [B_S], for [s ≤p S] and [f] totally monotonic and ω-continuous. *)
Lemma scott_shift_le (S s : B) (Hs : cone_norm S < 1) (Hsle : s <=p S) :
  is_totmono f -> is_scott_continuous_unit f ->
  @is_scott_continuous_unit R (lc_coneType Hs) C (fun x => f (lc_val x + s)).
Proof.
move=> Hf Hfc Mf u uch ub1 fuch fubMf Mfpos.
set x := cone_sup_ball u uch ub1.
have lvch n : lc_val (u n) <=p lc_val (u n.+1).
  exact: (lc_leE Hs (u n) (u n.+1)).1 (uch n).
have lvb1 n : cone_norm (lc_val (u n)) <= 1.
  by apply: le_trans (ub1 n); exact: (lc_val_norm_le Hs (u n)).
have vch n : lc_val (u n) + s <=p lc_val (u n.+1) + s.
  by apply: precone_add_le_r; exact: lvch.
have vb1 n : cone_norm (lc_val (u n) + s) <= 1.
  have key := lc_step1 Hs (w := u n) (ub1 n).
  apply: le_trans key; apply: cone_normp.
  rewrite precone_addC; apply: precone_add_le_r.
  by case: Hsle => d Hd; exists d.
rewrite /x (lc_val_scott Hs uch ub1 lvch lvb1).
rewrite -(sup_ball_addr lvch lvb1 (y := s) vch vb1).
exact: (Hfc Mf (fun n => lc_val (u n) + s) vch vb1 fuch fubMf Mfpos).
Qed.

(** **Stability of the dominated shift.**  Total monotonicity is
    [totmono_shift_le] (findiff.v), boundedness uses [f]'s bound at the
    shifted config (in [B_B] by [lc_step1]), ω-continuity is
    [scott_shift_le]. *)
Lemma stable_shift_le (S s : B) (Hs : cone_norm S < 1) (Hsle : s <=p S) :
  is_stable f ->
  @is_stable R (lc_coneType Hs) C (fun x => f (lc_val x + s)).
Proof.
move=> [Hf [M HM] Hfc]; split.
- exact: (totmono_shift_le f S s Hs Hsle Hf).
- exists M => xL Hx; apply: HM.
  have key := lc_step1 Hs (w := xL) Hx.
  apply: le_trans key; apply: cone_normp.
  rewrite precone_addC; apply: precone_add_le_r.
  by case: Hsle => d Hd; exists d.
- exact: (scott_shift_le Hsle Hf Hfc).
Qed.

End StableShift.

Arguments scott_shift_le {R B C} f {S s} Hs Hsle.
Arguments stable_shift_le {R B C} f {S s} Hs Hsle.

(** A finite [\sumP] (over a [{set}]) of stable maps is stable.  By
    [big_ind] over [stm_add]/[stm_zero], reducing to [stable_zero] and
    [stable_add] (totmono.v).  The stable analogue of [totmono_bigP]. *)
Lemma stable_bigP (R : realType) (P Q : coneType R) (T : finType)
    (A : {set T}) (g : T -> P -> Q) :
  (forall i, i \in A -> is_stable (g i)) ->
  is_stable (\big[stm_add/stm_zero P Q]_(i in A) g i).
Proof.
move=> Hg; elim/big_ind: _ => [|f1 f2 H1 H2|i iA].
- exact: stable_zero.
- exact: stable_add H1 H2.
- exact: Hg.
Qed.

Arguments stable_bigP {R P Q T} A g.

(** ** Unit-ball difference-of-ω-continuous engine — Paper Lemma 2.10
       (radius-aware, unit-ball [Hsplit])

    A unit-ball restriction of [stablehom.v]'s [diff_scott_at]: the
    codomain difference [w₀ = g₀ ⊖ f₀] (with [g₀ x = f₀ x + w₀ x] on the
    *chain* and at its supremum only) is ω-continuous on the unit ball at
    any image radius [Mf], provided [f₀] is increasing along the chain and
    [g₀] is ω-continuous.  We need this variant — rather than [diff_scott_at]
    itself — because the [Δε] operators [Δ⁺f(u⃗)]/[Δ⁻f(u⃗)] satisfy the
    split [Δ⁺ = Δ⁻ + Δf(u⃗)] only on the unit ball of [B_u⃗] (where total
    monotonicity gives [Δ⁻ ≤p Δ⁺]); off the ball [Δf(u⃗)] is [0]-extended
    and the split fails.  The proof mirrors [diff_scott_at] line for line,
    using the supplied chain split [Hsplit] (at the [u n]) and [HsplitS]
    (at the supremum) in place of the global [Hsplit]. *)

Section DiffScottUnit.
Variable R : realType.
Variables P Q : coneType R.
Local Open Scope precone_scope.

Lemma diff_scott_unit
  (f0 g0 w0 : P -> Q)
  (Hg_cont : is_scott_continuous_unit g0)
  (Mf Mg : {nonneg R}) (u : nat -> P)
  (uch : forall n, u n <=p u n.+1)
  (ub1 : forall n, cone_norm (u n) <= 1)
  (Hsplit : forall n, g0 (u n) = f0 (u n) + w0 (u n))
  (HsplitS : g0 (cone_sup_ball u uch ub1)
             = f0 (cone_sup_ball u uch ub1) + w0 (cone_sup_ball u uch ub1))
  (fxle : forall n, f0 (u n) <=p f0 (cone_sup_ball u uch ub1))
  (wuch : forall n, w0 (u n) <=p w0 (u n.+1))
  (wxch : forall n, w0 (u n) <=p w0 (cone_sup_ball u uch ub1))
  (wubMf : forall n, cone_norm (w0 (u n)) <= Mf%:num)
  (Mfpos : (0 < Mf%:num)%R)
  (guch : forall n, g0 (u n) <=p g0 (u n.+1))
  (gubMg : forall n, cone_norm (g0 (u n)) <= Mg%:num)
  (Mgpos : (0 < Mg%:num)%R) :
  w0 (cone_sup_ball u uch ub1) = cone_sup_at wuch wubMf Mfpos.
Proof.
set x := cone_sup_ball u uch ub1.
set y := cone_sup_at wuch wubMf Mfpos.
apply: precone_le_anti; last first.
  by apply: cone_sup_at_lub => n; exact: wxch.
have gx_eq : g0 x = cone_sup_at guch gubMg Mgpos.
  by rewrite /x (Hg_cont Mg u uch ub1 guch gubMg Mgpos).
have step1 n : g0 (u n) <=p f0 x + w0 (u n).
  by rewrite (Hsplit n); apply: precone_add_le_r; exact: fxle.
have Kge0 : (0 <= cone_norm (f0 x) + Mf%:num)%R.
  by rewrite addr_ge0 // ?cone_norm_ge0 // ltW.
pose K : {nonneg R} := NngNum Kge0.
have Kpos : (0 < K%:num)%R.
  by rewrite /= -[X in (X < _)%R]addr0 ler_ltD // ?cone_norm_ge0.
have fwch n : f0 x + w0 (u n) <=p f0 x + w0 (u n.+1).
  by apply: precone_add_le_l; exact: wuch.
have fwub n : cone_norm (f0 x + w0 (u n)) <= K%:num.
  by apply: le_trans (cone_normt _ _) _; rewrite /= lerD2l; exact: wubMf.
have step2 n : g0 (u n) <=p cone_sup_at fwch fwub Kpos.
  by apply: precone_le_trans (step1 n) _; exact: cone_sup_at_ub.
have step3 : cone_sup_at guch gubMg Mgpos <=p cone_sup_at fwch fwub Kpos.
  by apply: cone_sup_at_lub => n; exact: step2.
have sumeq : cone_sup_at fwch fwub Kpos = f0 x + y.
  rewrite /y.
  by rewrite -(addl_scott_continuous (f0 x) Mf K (w0 \o u) wuch wubMf Mfpos
                fwch fwub Kpos).
have gx_le : g0 x <=p f0 x + y by rewrite gx_eq -sumeq; exact: step3.
move: gx_le; rewrite HsplitS => -[z Hz].
exists z.
have Hz' : f0 x + y = f0 x + (w0 x + z) by rewrite Hz -precone_addA.
exact: precone_cancel Hz'.
Qed.

End DiffScottUnit.

Arguments diff_scott_unit {R P Q f0 g0 w0} Hg_cont {Mf Mg u} uch ub1.

(** ** [scott_Delta] — ω-continuity of [Δf(u⃗)] — Paper §7.3 (Lemma 7.20)

    For a *stable* [f] (totally monotonic + ω-continuous) and a family
    [u⃗ ∈ Bⁿ] with [S := Σᵢ uᵢ ∈ B_B] (strict interior), the difference
    operator [Δf(u⃗) : B_S → C] is [is_scott_continuous_unit].  The two
    halves [Δ⁺f(u⃗)], [Δ⁻f(u⃗)] are *stable* (each is a finite [\sumP] of
    the dominated shifts [g_{s_I}(x) = f(lc_val x + s_I)], stable by
    [stable_shift_le], so stable by [stable_bigP]); their difference
    [Δf(u⃗) = Δ⁺ ⊖ Δ⁻] is ω-continuous by the unit-ball difference engine
    [diff_scott_unit], the split [Δ⁺ = Δ⁻ + Δf(u⃗)] holding on the unit
    ball by total monotonicity ([Sneg_le_Spos], read through [Delta_E]),
    centre-monotonicity of [Δf(u⃗)] supplied by [Delta_mono]. *)

Section ScottDelta.
Variable R : realType.
Variables B C : coneType R.
Variable f : B -> C.
Hypothesis Hf : is_stable f.
Local Open Scope precone_scope.

(** [Δ⁺f(u⃗)] is stable on [B_u⃗]. *)
Lemma stable_Delta_pos (n : nat) (u : 'I_n -> B)
    (Hs : cone_norm (\big[precone_add/precone_zero]_(i : 'I_n) u i) < 1) :
  @is_stable R (lc_coneType Hs) C (Delta_pos f u).
Proof.
have shle (I : {set 'I_n}) :
    is_stable (fun x : lc_coneType Hs =>
      f (lc_val x + \big[precone_add/precone_zero]_(i in I) u i)).
  apply: (stable_shift_le f Hs _ Hf); exact: sumP_sub_le.
have := @stable_bigP R (lc_coneType Hs) C _ (Ppos n)
  (fun I (x : lc_coneType Hs) =>
     f (lc_val x + \big[precone_add/precone_zero]_(i in I) u i))
  (fun I _ => shle I).
congr is_stable; apply/funext => x.
by rewrite /Delta_pos /Delta_arg; elim/big_rec2: _ => // I s s' _ <-.
Qed.

(** [Δ⁻f(u⃗)] is stable on [B_u⃗]. *)
Lemma stable_Delta_neg (n : nat) (u : 'I_n -> B)
    (Hs : cone_norm (\big[precone_add/precone_zero]_(i : 'I_n) u i) < 1) :
  @is_stable R (lc_coneType Hs) C (Delta_neg f u).
Proof.
have shle (I : {set 'I_n}) :
    is_stable (fun x : lc_coneType Hs =>
      f (lc_val x + \big[precone_add/precone_zero]_(i in I) u i)).
  apply: (stable_shift_le f Hs _ Hf); exact: sumP_sub_le.
have := @stable_bigP R (lc_coneType Hs) C _ (Pneg n)
  (fun I (x : lc_coneType Hs) =>
     f (lc_val x + \big[precone_add/precone_zero]_(i in I) u i))
  (fun I _ => shle I).
congr is_stable; apply/funext => x.
by rewrite /Delta_neg /Delta_arg; elim/big_rec2: _ => // I s s' _ <-.
Qed.

Lemma scott_Delta (n : nat) (u : 'I_n -> B)
    (Hs : cone_norm (\big[precone_add/precone_zero]_(i : 'I_n) u i) < 1) :
  @is_scott_continuous_unit R (lc_coneType Hs) C (Delta f u).
Proof.
have Hfm : is_totmono f by case: Hf.
have [Dpm _ Dpc] := @stable_Delta_pos n u Hs.
have [Dnm _ Dnc] := @stable_Delta_neg n u Hs.
have [_ [Mp HMp] _] := @stable_Delta_pos n u Hs.
move=> Mf w wch wb1 fuch fubMf Mfpos.
set x := cone_sup_ball w wch wb1.
(* The pointwise order [Δ⁻ ≤p Δ⁺] at a unit-ball point of [B_u⃗]. *)
have ord (z : lc_coneType Hs) : cone_norm z <= 1 ->
    Delta_neg f u z <=p Delta_pos f u z.
  move=> Hz; rewrite Delta_pos_Spos Delta_neg_Sneg.
  apply: (Sneg_le_Spos Hfm).
  have key := lc_step1 Hs (w := z) Hz.
  by rewrite precone_addC; apply: le_trans key; rewrite precone_addC.
(* The split [Δ⁺ = Δ⁻ + Δf(u⃗)] at unit-ball points. *)
have splitz (z : lc_coneType Hs) : cone_norm z <= 1 ->
    Delta_pos f u z = Delta_neg f u z + Delta f u z.
  by move=> Hz; apply: Delta_E; exact: ord.
have Hsx : cone_norm x <= 1 by rewrite /x; exact: cone_sup_ball_norm.
have wlex k : w k <=p x by rewrite /x; exact: cone_sup_ball_ub.
(* [Δ⁻] increasing along the chain and up to the supremum. *)
have fxle k : Delta_neg f u (w k) <=p Delta_neg f u x.
  have [v Hv] := wlex k; rewrite Hv.
  by apply: (totmono_increasing Dnm); rewrite -Hv.
(* [Δ⁺] increasing along the chain. *)
have guch k : Delta_pos f u (w k) <=p Delta_pos f u (w k.+1).
  have [v Hv] := wch k; rewrite Hv.
  apply: (totmono_increasing Dpm); rewrite -Hv.
  by apply: le_trans (wb1 k.+1); rewrite Hv; exact: lexx.
(* [Δf(u⃗)] increasing up to the supremum, by centre-monotonicity. *)
have wxch k : Delta f u (w k) <=p Delta f u x.
  have lle : lc_val (w k) <=p lc_val x.
    by apply: (lc_leE Hs (w k) x).1; exact: wlex.
  have [d Hd] := lle.
  apply: (Delta_mono f Hfm n u Hs (w k) x d Hd).
  - exact: wb1.
  - exact: Hsx.
  - rewrite sum_vcons precone_addA -Hd.
    have key := lc_step1 Hs (w := x) Hsx.
    by rewrite precone_addC in key; apply: le_trans key; rewrite precone_addC.
(* Image radius [Mg] for the [Δ⁺] chain. *)
have Mp_ge0 : (0 <= Mp + 1)%R.
  have h0 : (0 <= Mp)%R.
    by apply: le_trans (HMp (w 0%N) (wb1 0%N)); exact: cone_norm_ge0.
  by rewrite addr_ge0// ler01.
pose Mg : {nonneg R} := NngNum Mp_ge0.
have Mgpos : (0 < Mg%:num)%R.
  rewrite /Mg/= -[X in (X < _)%R]addr0 ler_ltD// ?ltr01//.
  by apply: le_trans (HMp (w 0%N) (wb1 0%N)); exact: cone_norm_ge0.
have gubMg k : cone_norm (Delta_pos f u (w k)) <= Mg%:num.
  by rewrite /Mg/=; apply: le_trans (HMp (w k) (wb1 k)) _; rewrite lerDl ler01.
have HsplitS := splitz x Hsx.
have Hsplitk k := splitz (w k) (wb1 k).
exact: (@diff_scott_unit R (lc_coneType Hs) C (Delta_neg f u)
          (Delta_pos f u) (Delta f u) Dpc Mf Mg w wch wb1 Hsplitk HsplitS
          fxle fuch wxch fubMf Mfpos guch gubMg Mgpos).
Qed.

End ScottDelta.

Arguments stable_Delta_pos {R B C} f Hf {n} u Hs.
Arguments stable_Delta_neg {R B C} f Hf {n} u Hs.
Arguments scott_Delta {R B C} f Hf {n} u Hs.

(** ** B-side single-step difference [dB] and the bare-[B] Lemma 7.18
       — Paper §7.3 (Def 7.15, Lemmas 7.16–7.18, Theorem 7.19)

    The local-cone predicate [is_n_increasing] (findiff.v) recurses on the
    *nested* local cone [(B_{u₀})_{u⃗}]: its [n.+1] clause asks that
    [Δf(u₀) : B_{u₀} → C] be [n]-increasing *from the local cone of [u₀]*.
    Iterating that recursion needs the nested-cone transport
    [(B_{u₀})_{u⃗} = B_{u₀,u⃗}], which is the unproved cast that blocks the
    multi-direction bootstrap (Lemma 7.20-[Δf]) and the composition.

    We sidestep the cast entirely by working on *bare [B]-centres*.  The
    B-side single-step difference of [φ : B → C] in direction [u] is

      [dB φ u xb := SD φ 1 (fun _ ↦ u) xb] ,

    which is the cone difference [φ(xb + u) ⊖ φ(xb)] (well defined on the
    ball, [0]-extended off it by [SD]'s [pselect]).  Crucially [dB φ u : B →
    C] *stays on [B]*, so the recursion of the B-side [p]-increasing
    predicate [Sinc] (below) never changes the carrier — the nested-cone
    cast simply disappears, and the multi-direction bootstrap [Sinc_dB] is a
    one-line projection. *)

Section BsideDiff.
Variable R : realType.
Variables B C : coneType R.
Variable f : B -> C.
Local Open Scope precone_scope.

(** The B-side single-step difference [dB f u xb = SD f (fun ↦ u) xb]. *)
Definition dB (u : B) : B -> C := fun xb => SD f (fun _ : 'I_1 => u) xb.

(** [Spos]/[Sneg] of the one-element family collapse to [f] at the two
    endpoints: [Spos f 1 (fun↦u) xb = f(xb+u)], [Sneg = f xb]. *)
Lemma Spos_oneu (u xb : B) : Spos f 1 (fun _ : 'I_1 => u) xb = f (xb + u).
Proof.
rewrite /Spos Ppos1 big_set1; congr (f (_ + _)).
by rewrite (eq_bigl predT) ?big_ord1// => i; rewrite finset.in_setT.
Qed.

Lemma Sneg_oneu (u xb : B) : Sneg f 1 (fun _ : 'I_1 => u) xb = f xb.
Proof. by rewrite /Sneg Pneg1 big_set1 big_set0 precone_addr0. Qed.

(** Defining equation of [dB]: where [f] is increasing at [xb] (the order
    [f xb ≤p f(xb+u)] holds), [f(xb+u) = f xb + dB f u xb].  The bare-[B]
    twin of [Delta1_E]. *)
Lemma dB_E (u xb : B) :
  f xb <=p f (xb + u) -> f (xb + u) = f xb + dB u xb.
Proof.
move=> Hle.
have HE : Sneg f 1 (fun _ : 'I_1 => u) xb <=p Spos f 1 (fun _ : 'I_1 => u) xb.
  by rewrite Spos_oneu Sneg_oneu.
by have := SD_E f (fun _ : 'I_1 => u) xb HE; rewrite Spos_oneu Sneg_oneu.
Qed.

End BsideDiff.

Arguments dB {R B C} f u xb.
Arguments Spos_oneu {R B C} f u xb.
Arguments Sneg_oneu {R B C} f u xb.
Arguments dB_E {R B C} f u xb.

(** ** B-side [p]-increasing predicate [Sinc] — Paper Def 7.15 (B-side)

    The bare-[B] reformulation of [is_n_increasing].  [Sinc p f] is a
    [Fixpoint] on [p] whose recursive call stays on the *same* carrier
    [B → C] (because [dB f u : B → C]):

    - [Sinc 0 f]: [f] is increasing on [B_B];
    - [Sinc p.+1 f]: [f] is increasing *and*, for every direction [u ∈ B_B]
      (strict interior, [‖u‖ < 1]), the B-side difference [dB f u : B → C]
      is [Sinc p].

    Contrast with [is_n_increasing], whose recursive call lands on the
    *nested local cone* [lc_coneType Hu] — the carrier that forces the
    blocked nested-cone cast.  Here the carrier is invariant, so the
    multi-direction bootstrap [Sinc_dB] is immediate. *)

Fixpoint Sinc (p : nat) (R : realType) (B C : coneType R) (f : B -> C)
    {struct p} : Prop :=
  match p with
  | 0 => is_increasing f
  | p'.+1 => is_increasing f /\
      forall u : B, cone_norm u < 1 -> @Sinc p' R B C (dB f u)
  end.

Arguments Sinc p {R B C} f.

(** ** [Sinc_dB] — the multi-direction bootstrap (Lemma 7.16, B-side)

    If [f] is [Sinc p] for all [p], then for every interior direction [u]
    the difference [dB f u : B → C] is [Sinc p] for all [p].  This is the
    second conjunct of [Sinc] at [p.+1], read off directly — the
    multi-direction step that the local-cone [is_n_increasing] could not
    take without the nested-cone transport.  It goes through B-side in one
    line precisely because [dB f u] lives on the bare carrier [B → C]. *)
Lemma Sinc_dB (R : realType) (B C : coneType R) (f : B -> C) :
  (forall p, Sinc p f) ->
  forall (u : B), cone_norm u < 1 -> forall p, Sinc p (dB f u).
Proof. by move=> H u Hu p; have /= [_ /(_ u Hu)] := H p.+1. Qed.

Arguments Sinc_dB {R B C} f.

(** ** B-side Lemma 7.18 — [dB f u] is totally monotonic (shifted ball)
       — Paper §7.3 (txt 3523)

    The bare-[B] twin of [totmono_Delta1]: for [f] totally monotonic and
    [u] interior, the single-step difference [dB f u : B → C] satisfies the
    (7.1) inequality at every configuration *whose [+u]-shift stays in the
    unit ball* ([‖xb + u + Σᵢ wᵢ‖ ≤ 1]).  This shifted bound is the bare-[B]
    image of the [B_u]-ball bound used by [totmono_Delta1] (there supplied
    automatically by [lc_step1] on the local cone [B_u]); on bare centres it
    must be carried explicitly, which is the only place the nested-cone
    transport would have removed it.

    Proof: the two summed [n = 1] equations [SDpos_dB] / [SDneg_dB] split
    [Sε f (xb+u)] as [Sε f xb + Sε (dB f u) xb] (each [f(yb+u) = f yb + dB f
    u yb] by [dB_E], valid since the shifted config keeps every [yb+u] in
    the ball); the [(u :: w)]-difference inequality [Sdiff_mono] of [f] then
    gives the order after cancelling the common summand [Sneg f + Spos f]. *)

Section TotmonoDB.
Variable R : realType.
Variables B C : coneType R.
Variable f : B -> C.
Hypothesis Hf : is_totmono f.
Variable u : B.
Local Open Scope precone_scope.

(** Each shifted partial centre [xb + Σ_{i∈I} wᵢ + u] stays in the ball,
    so [f] is increasing there: [f(yb) ≤p f(yb + u)]. *)
Lemma dB_inc (m : nat) (w : 'I_m -> B) (xb : B)
    (Hsh : cone_norm (xb + u +
       \big[precone_add/precone_zero]_(i : 'I_m) w i) <= 1)
    (I : {set 'I_m}) :
  f (xb + \big[precone_add/precone_zero]_(i in I) w i) <=p
  f (xb + \big[precone_add/precone_zero]_(i in I) w i + u).
Proof.
apply: (totmono_increasing Hf); apply: le_trans Hsh; apply: cone_normp.
rewrite -precone_addA [_ + u]precone_addC precone_addA.
by apply: precone_add_le_l; exact: sumP_sub_le.
Qed.

(** Summed [n = 1] equation (positive part), bare-[B]:
    [Spos f w (xb + u) = Spos f w xb + Spos (dB f u) w xb]. *)
Lemma SDpos_dB (m : nat) (w : 'I_m -> B) (xb : B)
    (Hsh : cone_norm (xb + u +
       \big[precone_add/precone_zero]_(i : 'I_m) w i) <= 1) :
  Spos f m w (xb + u) = Spos f m w xb + Spos (dB f u) m w xb.
Proof.
rewrite /Spos -big_split/=; apply: eq_bigr => I _.
rewrite -precone_addA [u + _]precone_addC precone_addA.
by rewrite (dB_E f u _ (dB_inc Hsh I)).
Qed.

(** Summed [n = 1] equation (negative part), bare-[B]. *)
Lemma SDneg_dB (m : nat) (w : 'I_m -> B) (xb : B)
    (Hsh : cone_norm (xb + u +
       \big[precone_add/precone_zero]_(i : 'I_m) w i) <= 1) :
  Sneg f m w (xb + u) = Sneg f m w xb + Sneg (dB f u) m w xb.
Proof.
rewrite /Sneg -big_split/=; apply: eq_bigr => I _.
rewrite -precone_addA [u + _]precone_addC precone_addA.
by rewrite (dB_E f u _ (dB_inc Hsh I)).
Qed.

(** **B-side Lemma 7.18.** [dB f u] satisfies (7.1) at every shifted-ball
    configuration: [Sneg (dB f u) w xb ≤p Spos (dB f u) w xb]. *)
Lemma totmono_dB (m : nat) (w : 'I_m -> B) (xb : B)
    (Hsh : cone_norm (xb + u +
       \big[precone_add/precone_zero]_(i : 'I_m) w i) <= 1) :
  Sneg (dB f u) m w xb <=p Spos (dB f u) m w xb.
Proof.
have key : Sneg f m w (xb + u) + Spos f m w xb <=p
           Spos f m w (xb + u) + Sneg f m w xb.
  apply: (Sdiff_mono Hf (n := m) (u := u) (w := w) (xb := xb)).
  by rewrite sum_vcons precone_addA.
move: key; rewrite SDpos_dB// SDneg_dB//.
set Sn := Sneg f m w xb; set Sp := Spos f m w xb.
set DN := Sneg (dB f u) m w xb; set DP := Spos (dB f u) m w xb.
rewrite -[Sn + DN + Sp]precone_addA [DN + Sp]precone_addC precone_addA.
rewrite -[Sp + DP + Sn]precone_addA [DP + Sn]precone_addC precone_addA.
rewrite [Sp + Sn]precone_addC.
exact: (precone_le_addlI (Sn + Sp)).
Qed.

End TotmonoDB.

Arguments dB_inc {R B C} f Hf u {m} w xb Hsh I.
Arguments SDpos_dB {R B C} f Hf u {m} w xb Hsh.
Arguments SDneg_dB {R B C} f Hf u {m} w xb Hsh.
Arguments totmono_dB {R B C} f Hf u {m} w xb Hsh.

(** ** B-side nested recurrence [SD_consdB] — Paper §7.3 (Lemma 7.17/7.22)

    The bare-[B] analogue of the nested-difference identity
    [Δf(u₀ :: u⃗) = Δ(Δf(u₀))(u⃗)], with *no* local cone: prepending the
    head [u₀] to the direction family of [SD] is the same as taking the
    [SD] of the single-step difference [dB f u₀],

      [SD f (u₀ :: u⃗) xb = SD (dB f u₀) u⃗ xb] .

    This is precisely the [SD]-linearity-in-[f] content of the task: the
    [SD]-cons recurrence [SD_cons] writes the head difference as
    [SD f u⃗ (xb+u₀) ⊖ SD f u⃗ xb], while the summed [n=1] equations
    [SDpos_dB] / [SDneg_dB] (Lemma 7.4, [dB_E] term-by-term) split
    [Sε f u⃗ (xb+u₀) = Sε f u⃗ xb + Sε (dB f u₀) u⃗ xb], so [dB f u₀]'s own
    difference [SD (dB f u₀) u⃗ xb] *is* the head difference.  Cancel the
    common summands in the four defining equations to identify them. *)

Section SDconsdB.
Variable R : realType.
Variables B C : coneType R.
Variable f : B -> C.
Hypothesis Hf : is_totmono f.
Local Open Scope precone_scope.

Lemma SD_consdB (u0 : B) (n : nat) (w : 'I_n -> B) (xb : B)
    (Hc : cone_norm (xb +
       \big[precone_add/precone_zero]_(i : 'I_n.+1) vcons u0 w i) <= 1) :
  SD f (vcons u0 w) xb = SD (dB f u0) w xb.
Proof.
have Hsh : cone_norm (xb + u0 +
    \big[precone_add/precone_zero]_(i : 'I_n) w i) <= 1.
  by move: Hc; rewrite sum_vcons precone_addA.
have D1 := SD_E f w (xb + u0) (Sle_xbu Hf Hc).
have D0 := SD_E f w xb (Sle_xb Hf Hc).
have step := SD_cons f Hf u0 w xb Hc.
have SP := SDpos_dB f Hf u0 w xb Hsh.
have SN := SDneg_dB f Hf u0 w xb Hsh.
have HleB := totmono_dB f Hf u0 w xb Hsh.
have DB := SD_E (dB f u0) w xb HleB.
rewrite SP SN in D1.
set Sp0 := Spos f n w xb in D1 D0 *.
set Sn0 := Sneg f n w xb in D1 D0 *.
set DP := Spos (dB f u0) n w xb in D1 DB *.
set DN := Sneg (dB f u0) n w xb in D1 DB *.
set d1 := SD f w (xb + u0) in D1 step.
set d0 := SD f w xb in step D0 *.
set dc := SD f (vcons u0 w) xb in step *.
set db := SD (dB f u0) w xb in DB *.
apply: (@precone_cancel _ _ (Sn0 + DN + d0)).
rewrite step D0 DB in D1.
rewrite -[Sn0 + DN + d0 + dc]precone_addA -D1.
rewrite -precone_addA [d0 + (DN + db)]precone_addA [d0 + DN]precone_addC.
by rewrite !precone_addA.
Qed.

End SDconsdB.

Arguments SD_consdB {R B C} f Hf u0 {n} w xb Hc.

(** ** B-side Theorem 7.19 converse on the *closed* ball — [Sinc_totmono]

    The B-side counterpart of [findiff.v]'s [is_n_increasing_totmono],
    delivered *without ever leaving the bare carrier* [B → C] — the
    [Sinc] recursion (Def 7.15, B-side) recurses through [dB f u : B → C],
    so the nested-local-cone transport that blocks the [is_n_increasing]
    route never appears.

    Two ingredients, both bare-[B]:

    - the **open-ball** converse [Sinc_conv_strict]: from [∀p, Sinc p g]
      the (7.1) inequality [Sneg g n u x ≤p Spos g n u x] holds at every
      *strictly interior* configuration ([‖x + Σ uᵢ‖ < 1]).  Induction on
      the arity [n]: peel the head [u₀] by the cons recurrences
      [Spos_recur]/[Sneg_recur]; inside the open ball [u₀] is itself
      strictly interior so [Sinc_dB] gives [∀p, Sinc p (dB g u₀)] and the
      increasing-only splits [SDpos_dB_i]/[SDneg_dB_i] reduce the goal,
      after cancelling the common centre summand, to the (7.1) inequality
      for [dB g u₀] at arity [n] — supplied by the inductive hypothesis
      *at the weaker plain bound* [‖x + Σ wᵢ‖ < 1] (the head shift is
      absorbed into [dB], so the engine [SDpos_dB_i] feeds on the *given*
      shifted bound while the IH only needs the implied plain one — this
      is how the shifted-vs-plain mismatch is reconciled);
    - the **closed-ball bridge**: realise a boundary configuration
      [z = x + Σ uᵢ] ([‖z‖ ≤ 1]) as the supremum of the strictly-interior
      scaling chain [λₘ ·: z], where [Sinc_conv_strict] applies, and pass
      to the limit by [g]'s ω-continuity ([is_scott_continuous_unit]),
      using [scale_chain_sup] / [dsum_lub] (the very machinery of
      [is_n_increasing_totmono]).  This is the only place ω-continuity
      (hence stability) enters, exactly as in Theorem 7.19. *)

Section SincConvSplits.
Variable R : realType.
Variables B C : coneType R.
Local Open Scope precone_scope.

(** Each shifted partial centre stays in the ball, so [g] is increasing
    there — the increasing-only twin of [dB_inc] (no [is_totmono]). *)
Lemma dB_inc_i (g : B -> C)
    (Hi : is_increasing g) (u : B) (m : nat) (w : 'I_m -> B) (xb : B)
    (Hsh : cone_norm (xb + u +
       \big[precone_add/precone_zero]_(i : 'I_m) w i) <= 1)
    (I : {set 'I_m}) :
  g (xb + \big[precone_add/precone_zero]_(i in I) w i) <=p
  g (xb + \big[precone_add/precone_zero]_(i in I) w i + u).
Proof.
apply: Hi; apply: le_trans Hsh; apply: cone_normp.
rewrite -precone_addA [_ + u]precone_addC precone_addA.
by apply: precone_add_le_l; exact: sumP_sub_le.
Qed.

(** Increasing-only summed [n=1] equations: [Sε g w (xb+u) =
    Sε g w xb + Sε (dB g u) w xb], from [dB_E] term-by-term (only
    increasingness of [g] is used, not [is_totmono]). *)
Lemma SDpos_dB_i (g : B -> C)
    (Hi : is_increasing g) (u : B) (m : nat) (w : 'I_m -> B) (xb : B)
    (Hsh : cone_norm (xb + u +
       \big[precone_add/precone_zero]_(i : 'I_m) w i) <= 1) :
  Spos g m w (xb + u) = Spos g m w xb + Spos (dB g u) m w xb.
Proof.
rewrite /Spos -big_split/=; apply: eq_bigr => I _.
rewrite -precone_addA [u + _]precone_addC precone_addA.
by rewrite (dB_E g u _ (dB_inc_i Hi Hsh I)).
Qed.

Lemma SDneg_dB_i (g : B -> C)
    (Hi : is_increasing g) (u : B) (m : nat) (w : 'I_m -> B) (xb : B)
    (Hsh : cone_norm (xb + u +
       \big[precone_add/precone_zero]_(i : 'I_m) w i) <= 1) :
  Sneg g m w (xb + u) = Sneg g m w xb + Sneg (dB g u) m w xb.
Proof.
rewrite /Sneg -big_split/=; apply: eq_bigr => I _.
rewrite -precone_addA [u + _]precone_addC precone_addA.
by rewrite (dB_E g u _ (dB_inc_i Hi Hsh I)).
Qed.

End SincConvSplits.

Arguments dB_inc_i {R B C} g Hi u {m} w xb Hsh I.
Arguments SDpos_dB_i {R B C} g Hi u {m} w xb Hsh.
Arguments SDneg_dB_i {R B C} g Hi u {m} w xb Hsh.

Section SincConv.
Variable R : realType.
Variables B C : coneType R.
Local Open Scope precone_scope.

(** **Open-ball B-side converse.** For [∀p, Sinc p g] the (7.1)
    inequality holds at every strictly-interior configuration.  Bare-[B]
    induction on the arity; the head difference [dB g u₀] is again
    [∀p, Sinc p] ([Sinc_dB], the head being strictly interior) and the
    inductive hypothesis applies to it at the implied plain bound. *)
Lemma Sinc_conv_strict (n : nat) (g : B -> C) (Hg : forall p, Sinc p g)
    (x : B) (u : 'I_n -> B) :
  cone_norm (x + \big[precone_add/precone_zero]_(i : 'I_n) u i) < 1 ->
  Sneg g n u x <=p Spos g n u x.
Proof.
elim: n g Hg x u => [|n IHn] g Hg x u Hnorm.
  by rewrite /Sneg Pneg0 big_set0; exact: precone_le0.
rewrite [u]vcons_eta in Hnorm *.
set u0 := u ord0; set w := (fun i => u (lift ord0 i)).
rewrite -/u0 -/w in Hnorm *.
have Hi : is_increasing g by have := Hg 0%N.
have Hsh : cone_norm (x + u0 +
    \big[precone_add/precone_zero]_(i : 'I_n) w i) <= 1.
  by apply: ltW; move: Hnorm; rewrite sum_vcons precone_addA.
have Hu0 : cone_norm u0 < 1.
  apply: le_lt_trans Hnorm; apply: cone_normp.
  rewrite sum_vcons precone_addC -precone_addA.
  by exists (\big[precone_add/precone_zero]_(i : 'I_n) w i + x).
have HdB : forall p, Sinc p (dB g u0) by exact: (Sinc_dB g Hg u0 Hu0).
have IH : Sneg (dB g u0) n w x <=p Spos (dB g u0) n w x.
  apply: (IHn (dB g u0) HdB x w).
  apply: le_lt_trans Hnorm; apply: cone_normp.
  rewrite sum_vcons; apply: precone_add_le_l.
  by exists u0; rewrite precone_addC.
rewrite Spos_recur Sneg_recur.
have EP := SDpos_dB_i g Hi u0 w x Hsh.
have EN := SDneg_dB_i g Hi u0 w x Hsh.
rewrite EP EN.
set Sw := Spos g n w x; set Snw := Sneg g n w x.
set DP := Spos (dB g u0) n w x; set DN := Sneg (dB g u0) n w x.
rewrite -precone_addA [DN + Sw]precone_addC precone_addA.
rewrite -[Sw + DP + Snw]precone_addA [DP + Snw]precone_addC precone_addA.
rewrite [Sw + Snw]precone_addC.
by apply: precone_add_le_l; exact: IH.
Qed.

End SincConv.

Arguments Sinc_conv_strict {R B C n} g Hg x u.

Section SincTotmonoMain.
Variable R : realType.
Variables B C : coneType R.
Variable f : B -> C.
Local Open Scope precone_scope.

(** **B-side Theorem 7.19 (closed-ball converse).** A map [f] that is
    [Sinc p] for all [p] and ω-continuous on the unit ball is totally
    monotonic.  The boundary is reached by the scaling-chain limit of the
    open-ball converse [Sinc_conv_strict], exactly as in [findiff.v]'s
    [is_n_increasing_totmono] — but bare-[B], with no local-cone cast. *)
Lemma Sinc_totmono (Hg : forall p, Sinc p f)
    (Hscott : is_scott_continuous_unit f) : is_totmono f.
Proof.
move=> n x u Hz.
set z := x + \big[precone_add/precone_zero]_(i : 'I_n) u i.
have HzI (I : {set 'I_n}) : cone_norm (tm_arg x u I) <= 1.
  apply: le_trans Hz; apply: cone_normp; rewrite /tm_arg /z.
  by apply: precone_add_le_l; exact: sumP_sub_le.
pose c (I : {set 'I_n}) (m : nat) := f (scl m *: tm_arg x u I).
have M_ge0 : (0 <= \sum_(I : {set 'I_n}) cone_norm (f (tm_arg x u I)) + 1)%R.
  by rewrite addr_ge0 ?ler01// sumr_ge0// => I _; exact: cone_norm_ge0.
pose M : {nonneg R} := NngNum M_ge0.
have Mpos : (0 < M%:num)%R.
  rewrite /M/=; apply: lt_le_trans ltr01 _.
  by rewrite lerDr sumr_ge0// => I _; exact: cone_norm_ge0.
have Hi : is_increasing f by have := Hg 0%N.
have cch I m : c I m <=p c I m.+1.
  rewrite /c; have [v Hv] := scchain_mono (tm_arg x u I) m.
  rewrite Hv; apply: Hi; rewrite -Hv.
  by apply: le_trans (scchain_ub1 (HzI I) m.+1); rewrite Hv; exact: lexx.
have c_le_fz I m : c I m <=p f (tm_arg x u I).
  rewrite /c; have [v Hv] := scchain_le (tm_arg x u I) m.
  by rewrite [X in _ <=p f X]Hv; apply: Hi; rewrite -Hv; exact: HzI.
have cubM I m : cone_norm (c I m) <= M%:num.
  apply: le_trans (cone_normp _ _ (c_le_fz I m)) _; rewrite /M/=.
  apply: le_trans (_ : \sum_(J : {set 'I_n})
      cone_norm (f (tm_arg x u J)) <= _)%R; last by rewrite lerDl ler01.
  by rewrite (bigD1 I)//= lerDl sumr_ge0// => J _; exact: cone_norm_ge0.
have dsup_eq I : dsup c cch cubM Mpos I = f (tm_arg x u I).
  have key := Hscott M (fun m => scl m *: tm_arg x u I)
    (scchain_mono _) (scchain_ub1 (HzI I)) (cch I) (cubM I) Mpos.
  by rewrite /dsup -key scale_chain_sup.
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
  have H := Sinc_conv_strict f Hg (scl m *: x) (fun i => scl m *: u i) Hlt.
  rewrite /dchain /c.
  under eq_bigr => I _ do rewrite -tm_arg_scale.
  under [X in _ <=p X]eq_bigr => I _ do rewrite -tm_arg_scale.
  exact: H.
under eq_bigr => I _ do rewrite -(dsup_eq I).
under [X in _ <=p X]eq_bigr => I _ do rewrite -(dsup_eq I).
apply: (dsum_lub cch cubM Mpos) => m.
apply: precone_le_trans (step m) _.
exact: dsum_ub.
Qed.

End SincTotmonoMain.

Arguments Sinc_totmono {R B C} f Hg Hscott.

(** ** Interior-position split of [SD] — Paper §7.3 (Lemma 7.22, [SD_add]
       at an arbitrary position)

    [SD_add] (findiff.v) splits the *head* direction [u₀ = a + b] of an
    [SD]-difference into two; the §7.3 telescope (Lemma 7.23 general) needs
    the same split at an *arbitrary* interior position [k].  We obtain it by
    transposing [k] to the head ([tperm ord0 k]), applying the head split
    [SD_add], and transposing back — the [SD]-symmetry [SD_perm] making
    every reindexing free.  This is the missing "interior-position [SD_add]
    engine" of the §7.3 status note. *)

Section SDsplitIdx.
Variable R : realType.
Variables B C : coneType R.
Variable f : B -> C.
Hypothesis Hf : is_totmono f.
Local Open Scope precone_scope.

(** Replace the value of a family [v] at index [k] by [c]. *)
Definition setidx (n : nat) (v : 'I_n -> B) (k : 'I_n) (c : B) : 'I_n -> B :=
  fun i => if i == k then c else v i.

Lemma setidx_eq (n : nat) (v : 'I_n -> B) (k : 'I_n) (c : B) :
  setidx v k c k = c.
Proof. by rewrite /setidx eqxx. Qed.

Lemma setidx_neq (n : nat) (v : 'I_n -> B) (k i : 'I_n) (c : B) :
  i != k -> setidx v k c i = v i.
Proof. by rewrite /setidx => /negbTE ->. Qed.

(** Moving index [k] to the head: [v ∘ tperm ord0 k] is [vcons (v k) _].
    [SD f v xb = SD f (vcons (v k) (tail)) xb] by [SD_perm]. *)
Lemma SD_head_at (n : nat) (v : 'I_n.+1 -> B) (k : 'I_n.+1) (xb : B) :
  SD f v xb =
  SD f (vcons (v k) (fun i => v (tperm ord0 k (lift ord0 i)))) xb.
Proof.
pose s : 'S_n.+1 := tperm ord0 k.
have sord0 : s ord0 = k by rewrite /s tpermL.
have Ev : v \o s = vcons (v k) (fun i => v (tperm ord0 k (lift ord0 i))).
  by rewrite [LHS]vcons_eta /= /comp sord0.
by rewrite -Ev SD_perm.
Qed.

(** **Interior-position split.**  If [v k = a + b] then
    [SD f v xb = SD f (v[k:=a]) xb + SD f (v[k:=b]) (xb + a)].  Stated over
    an arbitrary arity ['I_n] with the index [k] witnessing [n > 0]. *)
Lemma SD_split_idx (n : nat) (v : 'I_n -> B) (k : 'I_n)
    (a b : B) (xb : B) (Hk : v k = a + b)
    (Hc : cone_norm (xb +
       \big[precone_add/precone_zero]_(i : 'I_n) v i) <= 1) :
  SD f v xb =
  SD f (setidx v k a) xb + SD f (setidx v k b) (xb + a).
Proof.
case: n => [|n] in v k a b Hk Hc *; first by case: k Hk Hc.
pose tl := fun i : 'I_n => v (tperm ord0 k (lift ord0 i)).
have tlE i : tperm ord0 k (lift ord0 i) != k.
  apply: contraNneq (neq_lift ord0 i) => Hki.
  by have := tpermK ord0 k (lift ord0 i); rewrite Hki tpermR.
have Ev : vcons (v k) tl = v \o tperm ord0 k.
  apply/funext => i; rewrite /comp /vcons /tl.
  by case: (unliftP ord0 i) => [j ->|->]//; rewrite tpermL.
(* Head split of the transposed family. *)
have Hsum : \big[precone_add/precone_zero]_(i : 'I_n.+1)
    vcons (v k) tl i = \big[precone_add/precone_zero]_(i : 'I_n.+1) v i.
  rewrite (reindex_inj (h := tperm ord0 k)); last exact: perm_inj.
  by apply: eq_bigr => i _; rewrite Ev /comp tpermK.
have HcH : cone_norm (xb +
    \big[precone_add/precone_zero]_(i : 'I_n.+1) vcons (a + b) tl i) <= 1.
  by rewrite -Hk Hsum.
have step := SD_add f Hf a b tl xb HcH.
rewrite (SD_head_at v k xb) -/tl Hk step.
(* Identify [vcons a tl] and [vcons b tl] with [setidx]-families transposed. *)
have EvA : vcons a tl = (setidx v k a) \o tperm ord0 k.
  apply/funext => i; rewrite /comp /vcons /tl.
  case: (unliftP ord0 i) => [j ->|->]; last by rewrite tpermL setidx_eq.
  by rewrite setidx_neq// tlE.
have EvB : vcons b tl = (setidx v k b) \o tperm ord0 k.
  apply/funext => i; rewrite /comp /vcons /tl.
  case: (unliftP ord0 i) => [j ->|->]; last by rewrite tpermL setidx_eq.
  by rewrite setidx_neq// tlE.
by rewrite EvA EvB !SD_perm.
Qed.

End SDsplitIdx.

Arguments setidx {R B n} v k c.
Arguments SD_split_idx {R B C} f Hf {n} v k a b xb Hk Hc.

(** ** Lemma 7.23, general arity — the diagonal split of [SD] — Paper §7.3
       (txt 3687)

    The §7.3 telescope: differencing [f] in the *sum* family [u⃗ + v⃗]
    decomposes diagonally as the pure-[u⃗] difference plus a sum of
    single-direction-shifted hybrid differences,

      [SD f (u⃗+v⃗) xb = SD f u⃗ xb + Σ_{j} SD f (hybⱼ)(xb + uⱼ)] ,

    where [hybⱼ] is the *hybrid family* [(u₁,…,u_{j-1}, vⱼ, u_{j+1}+v_{j+1},
    …)] — [u] before position [j], [v] at [j], [u+v] after.  This is the
    general arity of [findiff.v]'s base [SD_723_1] (n = 1).

    Proof by a telescoping "diagonal sweep": let [mixt j] be the family
    [u] on positions [< j] and [u+v] on positions [≥ j] (so [mixt 0 =
    u⃗+v⃗] and [mixt n = u⃗]).  At each [j] the position-[j] value of
    [mixt j] is [uⱼ + vⱼ]; splitting it by the interior-position engine
    [SD_split_idx] yields [mixt j.+1] (position [j] now [uⱼ], the
    [u]-prefix grown) plus the hybrid term [SD f (hybⱼ)(xb + uⱼ)] — the
    [v]-branch is exactly [hybⱼ].  Telescoping from [j = 0] to [j = n]
    collects the [Σⱼ] hybrid sum and leaves [SD f u⃗ xb].  No
    prefix-concatenation / ordinal cast is needed: the interior split
    keeps the carrier ['I_n] fixed throughout. *)

Section SDdiag.
Variable R : realType.
Variables B C : coneType R.
Variable f : B -> C.
Hypothesis Hf : is_totmono f.
Local Open Scope precone_scope.

Variable n : nat.
Variables u v : 'I_n -> B.

(** [mixt j]: [u] on positions [< j], [u+v] on positions [≥ j]. *)
Definition mixt (j : nat) : 'I_n -> B :=
  fun i => if (i < j)%N then u i else u i + v i.

(** [hyb k]: [u] before [k], [v] at [k], [u+v] after [k]. *)
Definition hyb (k : 'I_n) : 'I_n -> B :=
  fun i => if (i < k)%N then u i else if i == k then v i else u i + v i.

Lemma mixt0 : mixt 0 = (fun i => u i + v i).
Proof. by apply/funext => i; rewrite /mixt ltn0. Qed.

Lemma mixtn : mixt n = u.
Proof. by apply/funext => i; rewrite /mixt ltn_ord. Qed.

(** At [k] (value [j = k]), [mixt j] has value [u k + v k]; setting it to
    [u k] gives [mixt j.+1]; setting it to [v k] gives [hyb k]. *)
Lemma mixt_at (k : 'I_n) : mixt k k = u k + v k.
Proof. by rewrite /mixt ltnn. Qed.

Lemma set_mixt_u (k : 'I_n) : setidx (mixt k) k (u k) = mixt k.+1.
Proof.
apply/funext => i; rewrite /setidx /mixt.
case: (ltngtP i k) => [Hik|Hik|Hik].
- have ik : (i == k) = false by rewrite -val_eqE; apply: ltn_eqF.
  by rewrite ik (ltn_trans Hik (ltnSn k)).
- have ik : (i == k) = false by rewrite -val_eqE gtn_eqF.
  by rewrite ik ltnNge Hik.
- have ik : i = k by apply: val_inj.
  by rewrite ik eqxx ltnSn.
Qed.

Lemma set_mixt_v (k : 'I_n) : setidx (mixt k) k (v k) = hyb k.
Proof.
apply/funext => i; rewrite /setidx /mixt /hyb.
case: (ltngtP i k) => [Hik|Hik|Hik].
- have ik : (i == k) = false by rewrite -val_eqE; apply: ltn_eqF.
  by rewrite ik.
- have ik : (i == k) = false by rewrite -val_eqE gtn_eqF.
  by rewrite ik.
- have ik : i = k by apply: val_inj.
  by rewrite ik eqxx.
Qed.

(** Sum of [mixt j] is below the full [u+v] sum (each term is [≤p]). *)
Lemma mixt_sum_le (j : nat) :
  \big[precone_add/precone_zero]_(i : 'I_n) mixt j i <=p
  \big[precone_add/precone_zero]_(i : 'I_n) (u i + v i).
Proof.
elim/big_rec2: _ => [|i s s' _ Hs]; first exact: precone_le_refl.
apply: precone_le_trans (precone_add_le_l _ Hs).
apply: precone_add_le_r; rewrite /mixt; case: ifP => _.
  by exists (v i).
exact: precone_le_refl.
Qed.

(** **Single diagonal step.**  [SD f (mixt j) xb = SD f (mixt j.+1) xb +
    SD f (hyb k) (xb + u k)] for [k : 'I_n] of value [j]. *)
Lemma SD_diag_step (k : 'I_n) (xb : B)
    (Hc : cone_norm (xb +
       \big[precone_add/precone_zero]_(i : 'I_n) (u i + v i)) <= 1) :
  SD f (mixt k) xb =
  SD f (mixt k.+1) xb + SD f (hyb k) (xb + u k).
Proof.
have Hck : cone_norm (xb +
    \big[precone_add/precone_zero]_(i : 'I_n) mixt k i) <= 1.
  apply: le_trans Hc; apply: cone_normp; apply: precone_add_le_l.
  exact: mixt_sum_le.
have := SD_split_idx f Hf (mixt k) k (u k) (v k) xb (mixt_at k) Hck.
by rewrite set_mixt_u set_mixt_v.
Qed.

(** **Diagonal sweep (telescope).**  Collecting the steps [j = 0 .. m-1]
    leaves [SD f (mixt m) xb] plus the partial hybrid sum. *)
Lemma SD_diag_sweep (m : nat) (Hmn : (m <= n)%N) (xb : B)
    (Hc : cone_norm (xb +
       \big[precone_add/precone_zero]_(i : 'I_n) (u i + v i)) <= 1) :
  SD f (mixt 0) xb =
  SD f (mixt m) xb +
    \big[precone_add/precone_zero]_(k : 'I_n | (k < m)%N)
      SD f (hyb k) (xb + u k).
Proof.
elim: m Hmn => [|m IHm] Hmn.
  rewrite big_pred0; last by move=> k; rewrite ltn0.
  by rewrite precone_addr0.
have Hmn' : (m <= n)%N by exact: ltnW.
rewrite (IHm Hmn').
pose km : 'I_n := Ordinal Hmn.
have step := SD_diag_step km.
rewrite (step xb Hc).
(* Reassemble: the new step's hybrid term joins the partial sum. *)
rewrite -precone_addA; congr precone_add.
rewrite [in RHS](bigD1 km)/=; last by rewrite ltnSn.
rewrite [in RHS](eq_bigl (fun k : 'I_n => (k < m)%N)); last first.
  by move=> k; rewrite ltnS andbC -val_eqE/= -ltn_neqAle.
by [].
Qed.

(** **Lemma 7.23, general arity ([B]-side diagonal split).** *)
Lemma SD_diag (xb : B)
    (Hc : cone_norm (xb +
       \big[precone_add/precone_zero]_(i : 'I_n) (u i + v i)) <= 1) :
  SD f (fun i => u i + v i) xb =
  SD f u xb +
    \big[precone_add/precone_zero]_(k : 'I_n) SD f (hyb k) (xb + u k).
Proof.
have sweep := SD_diag_sweep (m := n) (leqnn n).
rewrite -mixt0 (sweep xb Hc) mixtn; congr precone_add.
by apply: eq_bigl => k; rewrite ltn_ord.
Qed.

(** **Lemma 7.23, general arity (full telescope, [B]-side).**  The paper's
    [Δf(u⃗+v⃗)(x+u₀)] identity: peel the head shift [u₀] by [SD_cons]
    (yielding the head term [Δf(u₀, u⃗+v⃗)(x)]), then split the residual
    [Δf(u⃗+v⃗)(x)] diagonally by [SD_diag].  This is the general arity of
    [findiff.v]'s [SD_723_1] (n = 1). *)
Lemma SD_723 (u0 xb : B)
    (Hc : cone_norm (xb + (u0 +
       \big[precone_add/precone_zero]_(i : 'I_n) (u i + v i))) <= 1) :
  SD f (fun i => u i + v i) (xb + u0) =
  SD f u xb + SD f (vcons u0 (fun i => u i + v i)) xb +
    \big[precone_add/precone_zero]_(k : 'I_n) SD f (hyb k) (xb + u k).
Proof.
have HcA : cone_norm (xb + \big[precone_add/precone_zero]_(i : 'I_n.+1)
    vcons u0 (fun i => u i + v i) i) <= 1 by rewrite sum_vcons.
have stepA := SD_cons f Hf u0 (fun i => u i + v i) xb HcA.
have HcD : cone_norm (xb +
    \big[precone_add/precone_zero]_(i : 'I_n) (u i + v i)) <= 1.
  apply: le_trans Hc; apply: cone_normp; apply: precone_add_le_l.
  by exists u0; rewrite precone_addC.
rewrite stepA (SD_diag HcD).
by rewrite -!precone_addA; congr precone_add; exact: precone_addC.
Qed.

End SDdiag.

Arguments mixt {R B n} u v j.
Arguments hyb {R B n} u v k.
Arguments SD_diag {R B C} f Hf {n} u v xb Hc.
Arguments SD_723 {R B C} f Hf {n} u v u0 xb Hc.

(** ** SD_concat — the difference operator composes — Paper §7.3 *)

Section SDcatComb.
Variables n m : nat.

(** Concatenation of an [n]-family and an [m]-family into an
    ['I_(n+m)]-family, via the [split] of the ordinal. *)
Definition catf (B : Type) (u : 'I_n -> B) (w : 'I_m -> B)
    : 'I_(n + m) -> B :=
  fun k => match split k with inl i => u i | inr j => w j end.

(** The two halves of a [{set 'I_(n+m)}], read on the [lshift]/[rshift]
    images. *)
Definition setL (K : {set 'I_(n + m)}) : {set 'I_n} :=
  [set i : 'I_n | lshift m i \in K].
Definition setR (K : {set 'I_(n + m)}) : {set 'I_m} :=
  [set j : 'I_m | rshift n j \in K].

(** The pairing [{set 'I_n} * {set 'I_m} → {set 'I_(n+m)}]. *)
Definition catset (AB : {set 'I_n} * {set 'I_m}) : {set 'I_(n + m)} :=
  [set lshift m i | i in AB.1] :|: [set rshift n j | j in AB.2].

Lemma lshift_in_catset (A : {set 'I_n}) (Bs : {set 'I_m}) (i : 'I_n) :
  (lshift m i \in catset (A, Bs)) = (i \in A).
Proof.
rewrite /catset !inE; apply/orP/idP => [[]|iA].
- by move=> /imsetP[i' i'A] /lshift_inj ->.
- by move=> /imsetP[j' _] /eqP; rewrite eq_lrshift.
- by left; apply/imsetP; exists i.
Qed.

Lemma rshift_in_catset (A : {set 'I_n}) (Bs : {set 'I_m}) (j : 'I_m) :
  (rshift n j \in catset (A, Bs)) = (j \in Bs).
Proof.
rewrite /catset !inE; apply/orP/idP => [[]|jB].
- by move=> /imsetP[i' _] /eqP; rewrite eq_rlshift.
- by move=> /imsetP[j' j'B] /rshift_inj ->.
- by right; apply/imsetP; exists j.
Qed.

Lemma setL_catset (A : {set 'I_n}) (Bs : {set 'I_m}) :
  setL (catset (A, Bs)) = A.
Proof. by apply/setP => i; rewrite inE lshift_in_catset. Qed.

Lemma setR_catset (A : {set 'I_n}) (Bs : {set 'I_m}) :
  setR (catset (A, Bs)) = Bs.
Proof. by apply/setP => j; rewrite inE rshift_in_catset. Qed.

Lemma catset_LR (K : {set 'I_(n + m)}) : catset (setL K, setR K) = K.
Proof.
apply/setP => k; rewrite -[k](splitK); case: (split k) => [i|j] /=.
- by rewrite lshift_in_catset inE.
- by rewrite rshift_in_catset inE.
Qed.

Lemma catset_bij : bijective catset.
Proof.
exists (fun K => (setL K, setR K)) => [[A Bs]|K].
  by rewrite setL_catset setR_catset.
exact: catset_LR.
Qed.

(** The two images are disjoint, so cardinality splits. *)
Lemma catset_card (A : {set 'I_n}) (Bs : {set 'I_m}) :
  #|catset (A, Bs)| = (#|A| + #|Bs|)%N.
Proof.
rewrite /catset cardsU !card_imset.
- have -> : [set lshift m i | i in A] :&: [set rshift n j | j in Bs]
      = finset.set0.
    apply/setP => k; rewrite !inE; apply/negbTE/negP => /andP[].
    by move=> /imsetP[i _ ->] /imsetP[j _] /eqP; rewrite eq_lrshift.
  by rewrite cards0 subn0.
- exact: rshift_inj.
- exact: lshift_inj.
Qed.

(** [#|setL K| ≤ n], [#|setR K| ≤ m] (cardinality bounds for parity). *)
Lemma setL_card_leq (K : {set 'I_(n + m)}) : (#|setL K| <= n)%N.
Proof. by apply: leq_trans (max_card _) _; rewrite card_ord. Qed.
Lemma setR_card_leq (K : {set 'I_(n + m)}) : (#|setR K| <= m)%N.
Proof. by apply: leq_trans (max_card _) _; rewrite card_ord. Qed.

End SDcatComb.

Arguments catf {n m B} u w.
Arguments setL {n m} K.
Arguments setR {n m} K.
Arguments catset {n m} AB.

(** Parity multiplicativity: the [Ppos]/[Pneg] sign of [catset (A,Bs)]
    in ['I_(n+m)] is the product of the signs of [A] in ['I_n] and [Bs]
    in ['I_m] (using the cardinality bounds [#A ≤ n], [#B ≤ m]). *)
Section CatParity.
Variables n m : nat.

Lemma catset_odd (A : {set 'I_n}) (Bs : {set 'I_m}) :
  odd (n + m - #|catset (A, Bs)|) =
  odd (n - #|A|) (+) odd (m - #|Bs|).
Proof.
rewrite catset_card.
have HA := setL_card_leq (catset (A, Bs)); rewrite setL_catset in HA.
have HB := setR_card_leq (catset (A, Bs)); rewrite setR_catset in HB.
have -> : (n + m - (#|A| + #|Bs|) = (n - #|A|) + (m - #|Bs|))%N
  by rewrite addnBA// addnBAC// subnDA.
by rewrite oddD.
Qed.

Lemma catset_Ppos (A : {set 'I_n}) (Bs : {set 'I_m}) :
  (catset (A, Bs) \in Ppos (n + m)) =
  ((A \in Ppos n) == (Bs \in Ppos m)).
Proof.
rewrite !in_Ppos catset_odd negb_add.
by case: (odd _); case: (odd _).
Qed.

Lemma catset_Pneg (A : {set 'I_n}) (Bs : {set 'I_m}) :
  (catset (A, Bs) \in Pneg (n + m)) =
  ((A \in Ppos n) != (Bs \in Ppos m)).
Proof.
rewrite in_Pneg catset_odd.
by rewrite !in_Ppos; case: (odd _); case: (odd _).
Qed.

End CatParity.

Arguments catset_card {n m} A Bs.
Arguments catset_Ppos {n m} A Bs.
Arguments catset_Pneg {n m} A Bs.

(** ** The cone-side composition: [Spos]/[Sneg] of the concatenated
       config split as parity-classified blocks of the inner difference. *)

Section SDcatSum.
Variable R : realType.
Variables B C : coneType R.
Variable f : B -> C.
Local Open Scope precone_scope.

(** The inner-sum split: the [catf]-sum over [K] is the [setL]-sum of [u]
    plus the [setR]-sum of [w]. *)
Lemma sumP_catf (n m : nat) (u : 'I_n -> B) (w : 'I_m -> B)
    (K : {set 'I_(n + m)}) :
  \big[precone_add/precone_zero]_(k in K) catf u w k =
  \big[precone_add/precone_zero]_(i in setL K) u i +
  \big[precone_add/precone_zero]_(j in setR K) w j.
Proof.
rewrite big_split_ord/=; congr precone_add.
- apply: eq_big => [i|i _]; first by rewrite inE.
  rewrite /catf; case: splitP => j /= Hj.
    by congr u; exact: ord_inj.
  by move: (ltn_ord i); rewrite Hj ltnNge leq_addr.
- apply: eq_big => [j|j _]; first by rewrite inE.
  rewrite /catf; case: splitP => i /= Hi.
    by move: (ltn_ord i); rewrite -Hi ltnNge leq_addr.
  by congr w; apply: ord_inj; move: Hi => /eqP; rewrite eqn_add2l => /eqP.
Qed.

(** [Spos] of the concatenated config, reindexed over [catset] and split
    along [Bs ∈ Ppos m] into the two same-parity blocks (parity
    multiplicativity [catset_Ppos]): the [Ppos m] block contributes
    [Spos f n u], the [Pneg m] block [Sneg f n u]. *)
Lemma Spos_cat (n m : nat) (u : 'I_n -> B) (w : 'I_m -> B) (XB : B) :
  Spos f (n + m) (catf u w) XB =
  \big[precone_add/precone_zero]_(Bs in Ppos m)
     Spos f n u (XB + \big[precone_add/precone_zero]_(j in Bs) w j) +
  \big[precone_add/precone_zero]_(Bs in Pneg m)
     Sneg f n u (XB + \big[precone_add/precone_zero]_(j in Bs) w j).
Proof.
rewrite /Spos (reindex catset)/=; last by apply: onW_bij; exact: catset_bij.
under eq_bigl => AB do rewrite catset_Ppos.
under eq_bigr => AB ? do
  rewrite sumP_catf setL_catset setR_catset precone_addA.
rewrite (bigID (fun AB : {set 'I_n} * {set 'I_m} => AB.2 \in Ppos m))/=.
congr precone_add.
  rewrite (eq_bigl (fun AB : {set 'I_n} * {set 'I_m} =>
     (AB.1 \in Ppos n) && (AB.2 \in Ppos m))); last first.
    by move=> AB /=; case: (AB.2 \in Ppos m); case: (AB.1 \in Ppos n).
  under [RHS]eq_bigr => Bs _ do under eq_bigr => I _ do
    rewrite -precone_addA [\big[_/_]_(j in Bs) w j + _]precone_addC
      precone_addA.
  by rewrite [RHS]exchange_big/= [RHS]pair_big/=.
rewrite (eq_bigl (fun AB : {set 'I_n} * {set 'I_m} =>
   (AB.1 \in Pneg n) && (AB.2 \in Pneg m))); last first.
  move=> AB /=; rewrite !in_Pneg_Ppos.
  by case: (AB.2 \in Pneg m); case: (AB.1 \in Pneg n).
rewrite /Sneg.
under [RHS]eq_bigr => Bs _ do under eq_bigr => I _ do
  rewrite -precone_addA [\big[_/_]_(j in Bs) w j + _]precone_addC precone_addA.
by rewrite [RHS]exchange_big/= [RHS]pair_big/=.
Qed.

(** [Sneg] of the concatenated config: the *opposite*-parity blocks
    ([catset_Pneg]).  The [Ppos m] block contributes [Sneg f n u], the
    [Pneg m] block [Spos f n u]. *)
Lemma Sneg_cat (n m : nat) (u : 'I_n -> B) (w : 'I_m -> B) (XB : B) :
  Sneg f (n + m) (catf u w) XB =
  \big[precone_add/precone_zero]_(Bs in Ppos m)
     Sneg f n u (XB + \big[precone_add/precone_zero]_(j in Bs) w j) +
  \big[precone_add/precone_zero]_(Bs in Pneg m)
     Spos f n u (XB + \big[precone_add/precone_zero]_(j in Bs) w j).
Proof.
rewrite /Sneg (reindex catset)/=; last by apply: onW_bij; exact: catset_bij.
under eq_bigl => AB do rewrite catset_Pneg.
under eq_bigr => AB ? do
  rewrite sumP_catf setL_catset setR_catset precone_addA.
rewrite (bigID (fun AB : {set 'I_n} * {set 'I_m} => AB.2 \in Ppos m))/=.
congr precone_add.
  rewrite (eq_bigl (fun AB : {set 'I_n} * {set 'I_m} =>
     (AB.1 \in Pneg n) && (AB.2 \in Ppos m))); last first.
    move=> AB /=; rewrite -[AB.1 \in Pneg n]negbK -in_Pneg_Ppos.
    by case: (AB.1 \in Ppos n); case: (AB.2 \in Ppos m).
  rewrite /Sneg.
  under [RHS]eq_bigr => Bs _ do under eq_bigr => I _ do
    rewrite -precone_addA [\big[_/_]_(j in Bs) w j + _]precone_addC
      precone_addA.
  by rewrite [RHS]exchange_big/= [RHS]pair_big/=.
rewrite (eq_bigl (fun AB : {set 'I_n} * {set 'I_m} =>
   (AB.1 \in Ppos n) && (AB.2 \in Pneg m))); last first.
  move=> AB /=; rewrite -[AB.2 \in Pneg m]negbK -in_Pneg_Ppos.
  by case: (AB.1 \in Ppos n); case: (AB.2 \in Ppos m).
rewrite /Spos.
under [RHS]eq_bigr => Bs _ do under eq_bigr => I _ do
  rewrite -precone_addA [\big[_/_]_(j in Bs) w j + _]precone_addC precone_addA.
by rewrite [RHS]exchange_big/= [RHS]pair_big/=.
Qed.

End SDcatSum.

Arguments sumP_catf {R B} {n m} u w K.
Arguments Spos_cat {R B C} f {n m} u w XB.
Arguments Sneg_cat {R B C} f {n m} u w XB.

(** ** [SD_concat] / [totmono_SD_cat] — the difference composes (the
       (7.1) inequality for the inner difference [SD f n u⃗] at the outer
       [m]-config), the engine of Lemma 7.20-[Δf]. *)

Section SDconcat.
Variable R : realType.
Variables B C : coneType R.
Variable f : B -> C.
Hypothesis Hf : is_totmono f.
Local Open Scope precone_scope.

(** The full [catf]-sum is the sum of the two families' full sums. *)
Lemma sumP_catf_T (n m : nat) (u : 'I_n -> B) (w : 'I_m -> B) :
  \big[precone_add/precone_zero]_(k : 'I_(n + m)) catf u w k =
  \big[precone_add/precone_zero]_(i : 'I_n) u i +
  \big[precone_add/precone_zero]_(j : 'I_m) w j.
Proof.
rewrite big_split_ord/=; congr precone_add.
- by apply: eq_bigr => i _; rewrite /catf; case: splitP => j /= Hj;
    [congr u; exact: ord_inj | move: (ltn_ord i); rewrite Hj ltnNge leq_addr].
- apply: eq_bigr => j _; rewrite /catf; case: splitP => i /= Hi.
    by move: (ltn_ord i); rewrite -Hi ltnNge leq_addr.
  by congr w; apply: ord_inj; move: Hi => /eqP; rewrite eqn_add2l => /eqP.
Qed.

(** **The (7.1) inequality for the inner difference [SD f n u⃗] at the
    outer [m]-config** — the [SD_concat] engine.  Each inner [Sε f n u⃗]
    splits as [Sε(catf u⃗ w⃗)] over the parity blocks ([Spos_cat]/[Sneg_cat]);
    [f]'s own total monotonicity at the concatenated [(n+m)]-config gives
    [Sneg(catf) ≤p Spos(catf)], and cancelling the shared [Sneg]-blocks
    leaves exactly [Sneg(SD f n u⃗) ≤p Spos(SD f n u⃗)]. *)
Lemma totmono_SD_cat (n m : nat) (u : 'I_n -> B) (w : 'I_m -> B) (XB : B)
    (Hc : cone_norm (XB +
       (\big[precone_add/precone_zero]_(i : 'I_n) u i +
        \big[precone_add/precone_zero]_(j : 'I_m) w j)) <= 1) :
  Sneg (SD f u) m w XB <=p Spos (SD f u) m w XB.
Proof.
(* Term-level [Sneg f ≤p Spos f] at every [Bs]-shifted inner config. *)
have inle (Bs : {set 'I_m}) :
    Sneg f n u (XB + \big[precone_add/precone_zero]_(j in Bs) w j) <=p
    Spos f n u (XB + \big[precone_add/precone_zero]_(j in Bs) w j).
  apply: (Sneg_le_Spos Hf); apply: le_trans Hc; apply: cone_normp.
  rewrite -precone_addA [\big[_/_]_(j in Bs) w j + _]precone_addC.
  by apply: precone_add_le_l; apply: precone_add_le_l; exact: sumP_sub_le.
(* Term-level [SD_E]: [Spos f = Sneg f + SD f]. *)
have splitE (Bs : {set 'I_m}) :
    Spos f n u (XB + \big[precone_add/precone_zero]_(j in Bs) w j) =
    Sneg f n u (XB + \big[precone_add/precone_zero]_(j in Bs) w j) +
    SD f u (XB + \big[precone_add/precone_zero]_(j in Bs) w j).
  by apply: SD_E; exact: inle.
(* The four parity blocks. *)
pose Spp := \big[precone_add/precone_zero]_(Bs in Ppos m)
   Spos f n u (XB + \big[precone_add/precone_zero]_(j in Bs) w j).
pose Snn := \big[precone_add/precone_zero]_(Bs in Pneg m)
   Sneg f n u (XB + \big[precone_add/precone_zero]_(j in Bs) w j).
pose Snp := \big[precone_add/precone_zero]_(Bs in Ppos m)
   Sneg f n u (XB + \big[precone_add/precone_zero]_(j in Bs) w j).
pose Spn := \big[precone_add/precone_zero]_(Bs in Pneg m)
   Spos f n u (XB + \big[precone_add/precone_zero]_(j in Bs) w j).
(* [f]-totmono at the concatenated config: [Sneg_cat ≤p Spos_cat]. *)
have Hcc : cone_norm (XB +
    \big[precone_add/precone_zero]_(k : 'I_(n + m)) catf u w k) <= 1.
  by rewrite sumP_catf_T.
have key := Sneg_le_Spos Hf Hcc.
rewrite (Spos_cat f u w XB) (Sneg_cat f u w XB) -/Spp -/Snn -/Snp -/Spn in key.
(* [Spos]/[Sneg] of [SD f u⃗] are the bare [Ppos m]/[Pneg m] blocks [Pp]/[Pn]. *)
rewrite /Spos /Sneg.
set Pp := \big[precone_add/precone_zero]_(Bs in Ppos m)
   SD f u (XB + \big[precone_add/precone_zero]_(j in Bs) w j).
set Pn := \big[precone_add/precone_zero]_(Bs in Pneg m)
   SD f u (XB + \big[precone_add/precone_zero]_(j in Bs) w j).
(* [Spp = Snp + Pp], [Spn = Snn + Pn] (the two block [SD_E]s). *)
have HPP : Spp = Snp + Pp.
  by rewrite /Spp /Snp /Pp -big_split/=; apply: eq_bigr => Bs _; exact: splitE.
have HPN : Spn = Snn + Pn.
  by rewrite /Spn /Snn /Pn -big_split/=; apply: eq_bigr => Bs _; exact: splitE.
(* Goal [Pn ≤p Pp]; [key : Snp + Spn ≤p Spp + Snn].  Substitute, cancel. *)
apply: (precone_le_addlI (Snp + Snn)).
move: key; rewrite HPP HPN.
rewrite precone_addA -[(Snp + Pp) + Snn]precone_addA [Pp + Snn]precone_addC.
by rewrite precone_addA.
Qed.

(** **Lemma 7.20 ([Δf] clause).**  For [f] totally monotonic and a
    direction family [u⃗] with [S := Σᵢ uᵢ] in the strict interior, the
    difference operator [Δf(u⃗) : B_u⃗ → C] is totally monotonic.

    Direct, via [SD_concat]: unfolding [is_totmono (Δf(u⃗))] over [B_u⃗],
    each summand [Δf(u⃗)(y + Σ_J W⃗)] reads on the [B]-side as
    [SD f n u⃗ (lc_val y + Σ_J (lc_val ∘ W⃗))] ([SD_Delta] + [lc_val_big]),
    so the whole [Sε(Δf(u⃗))] is [Sε (SD f n u⃗) m (lc_val ∘ W⃗) (lc_val y)];
    by [totmono_SD_cat] (the [SD_concat] engine) this is bounded
    [Sneg ≤p Spos] — precisely [f]'s own total monotonicity at the
    concatenated [(n+m)]-config (the centre/direction bound supplied by
    [lc_step1] on the local cone).  No nested-cone cast, no ω-continuity. *)
Lemma totmono_Delta (n : nat) (u : 'I_n -> B)
    (Hs : cone_norm (\big[precone_add/precone_zero]_(i : 'I_n) u i) < 1) :
  @is_totmono R (lc_coneType Hs) C (Delta f u).
Proof.
move=> m y W Hbd.
(* The [B]-side images of the local-cone data. *)
set XB := lc_val y; set ww := (fun j => lc_val (W j)).
(* Each [Sε] term of [Δf(u⃗)] reads on the [B]-side as the [SD f u⃗] term. *)
have termE (J : {set 'I_m}) :
    Delta f u (y + \big[precone_add/precone_zero]_(j in J) W j) =
    SD f u (XB + \big[precone_add/precone_zero]_(j in J) ww j).
  rewrite SD_Delta /XB /ww; congr (SD f u _).
  by rewrite lc_valD lc_val_big.
rewrite /tm_arg.
under eq_bigr => I _ do rewrite termE.
under [X in _ <=p X]eq_bigr => I _ do rewrite termE.
rewrite -/(Sneg (SD f u) m ww XB) -/(Spos (SD f u) m ww XB).
(* The concatenated [(n+m)]-config stays in [B_B], by [lc_step1]. *)
apply: totmono_SD_cat.
have key := lc_step1 Hs
  (w := y + \big[precone_add/precone_zero]_(j : 'I_m) W j).
rewrite lc_valD lc_val_big in key.
have Hball : lc_norm (y + \big[precone_add/precone_zero]_(j : 'I_m) W j) <= 1.
  by move: Hbd; rewrite /cone_norm/=.
apply: le_trans (key Hball); apply: cone_normp.
rewrite /XB /ww precone_addC -precone_addA.
by apply: precone_add_le_l; rewrite precone_addC; exact: precone_le_refl.
Qed.

End SDconcat.

Arguments sumP_catf_T {R B} {n m} u w.
Arguments totmono_SD_cat {R B C} f Hf {n m} u w XB Hc.
Arguments totmono_Delta {R B C} f Hf {n} u Hs.

(** ** Lemma 7.26 — the composition main lemma — Paper §7.3 (txt 3713)

    Paper Lemma 7.26: for totally monotonic [f, h₁,…,hₙ : B_B → C] and
    [g : B_C → D] with [∀x∈B_B, f(x) + Σᵢ hᵢ(x) ∈ B_C], the map

      [k(x) := Δg(h₁(x),…,hₙ(x))(f(x))]

    is totally monotonic.  On the B-side [k] reads as the [SD]-difference
    of [g] in the directions [hᵢ(x)] at the centre [f(x)]:

      [kfun g f h⃗ x := SD g n (fun i ↦ hᵢ x) (f x)] .

    We deliver here the two fully-proved cornerstones of the paper's
    [p]-induction:

    - the base case [p = 0] ([kfun_increasing], Lemma 7.25 for the
      composite): [k] is increasing on [B_B], read off the joint
      centre/direction monotonicity [SD_mono_full] of [g] (the centre [f x]
      and every direction [hᵢ x] grow as [x] does, since [f], [hᵢ] are
      increasing, and [SD g] is jointly increasing), the boundedness
      hypothesis [Hbd] supplying the unit-ball norm bound;

    - the **diagonal expansion** [dB_kfun] of the single-step difference
      [dB k u] (the engine of the [p ⤳ p+1] step, txt 3724–3731):

        [dB k u x = SD g (Δf(u)(x) :: (hᵢ(x+u))ᵢ) (f x)
                    + Σ_{k} SD g (hybₖ(h(x), Δh(u)(x))) (f x + h_k x)] ,

      i.e. the paper's [n+1]-term sum, with the would-be first
      Lemma-7.23 term [SD g (h(x)) (f x) = k x] *annihilated by the
      subtraction* ([dB_E] + [precone_cancel]).  Each summand is itself a
      [kfun]-shaped map at arity [n+1] (head) resp. [n] (hybrids), with
      centre [f] resp. [f + h_k] and directions drawn from
      [{Δf(u), hⱼ(·+u), hⱼ, Δhⱼ(u)}].  This is exactly the decomposition
      [SD_723] (Lemma 7.23 full telescope) applied to the shifted family
      [h(x+u) = h(x) + Δh(u)(x)] at the shifted centre [f(x+u) = f(x) +
      Δf(u)(x)].

    The remaining [p]-induction is closed in [ninc_kfun] below.  It cannot
    run on the *bare* carrier [B → C] (the head direction [Δf(u) = dB f u]
    is increasing but not totally monotonic on the plain ball — only on the
    *shifted* ball, [totmono_dB] — and the forward bridge
    [is_totmono ⇒ ∀p, Sinc p] is genuinely false on bare [B]).  Instead we
    run it on the *local-cone* predicate [is_n_increasing] (which recurses
    into [B_u], where [lc_step1] makes the plain and shifted balls coincide)
    *and quantify the induction over all source cones*: the [p.+1] step's
    goal at source [B_u] is discharged by the inductive hypothesis
    instantiated at source [B_u], so the explicit nested-cone transport
    [(B_{u₀})_{u⃗} = B_{u₀,u⃗}] is never needed.  See [ninc_kfun]. *)

Section Lemma726.
Variable R : realType.
Variables B C D : coneType R.
Variable g : C -> D.
Hypothesis Hg : is_totmono g.
Local Open Scope precone_scope.

(** The B-side composite difference [k(x) = Δg(h⃗(x))(f(x))]. *)
Definition kfun (n : nat) (f : B -> C) (h : 'I_n -> (B -> C)) : B -> D :=
  fun x => SD g (fun i => h i x) (f x).

(** **Lemma 7.25 for the composite / [Sinc 0] base case.**  [kfun] is
    increasing on [B_B]: as [x] grows the centre [f x] and every direction
    [hᵢ x] grow ([f], [hᵢ] increasing), and [SD g] is jointly increasing
    ([SD_mono_full]); the [n = 0] case is just [g] increasing
    ([totmono_increasing]). *)
Lemma kfun_increasing (n : nat) (f : B -> C) (h : 'I_n -> (B -> C))
    (Hf : is_increasing f)
    (Hh : forall i, is_increasing (h i))
    (Hbd : forall y, cone_norm y <= 1 ->
       cone_norm (f y +
         \big[precone_add/precone_zero]_(i : 'I_n) h i y) <= 1) :
  is_increasing (kfun f h).
Proof.
move=> x v Hxv; rewrite /kfun.
have Hx1 : cone_norm x <= 1.
  by apply: le_trans Hxv; apply: cone_normp; exists v.
have Hxv1 : cone_norm (x + v) <= 1 by exact: Hxv.
have Hcf : f x <=p f (x + v) by exact: Hf.
have Hch i : h i x <=p h i (x + v) by exact: Hh.
have Hbnd : cone_norm (f (x + v) +
    \big[precone_add/precone_zero]_(i : 'I_n) h i (x + v)) <= 1.
  exact: Hbd.
case: n h Hh Hbd Hbnd Hch => [|m] h Hh Hbd Hbnd Hch.
  rewrite !(@SD0 R C D g); case: Hcf => d Hd; rewrite Hd.
  apply: (totmono_increasing Hg).
  by move: Hbnd; rewrite big_ord0 precone_addr0 -Hd.
exact: (@SD_mono_full R C D g Hg m (h^~ x) (h^~ (x + v)) (f x) (f (x + v))
  Hcf Hch Hbnd).
Qed.

(** **The diagonal expansion [dB_kfun] (Lemma 7.23 applied, txt 3724).**
    The single-step difference of the composite splits as the paper's
    [n+1]-term sum, the first Lemma-7.23 term cancelling against [k x].
    The shifted family [h(x+u) = h(x) + Δh(u)(x)] and shifted centre
    [f(x+u) = f(x) + Δf(u)(x)] turn [k(x+u)] into the LHS of [SD_723]. *)
Lemma dB_kfun (n : nat) (f : B -> C) (h : 'I_n -> (B -> C))
    (Hf : is_increasing f) (Hh : forall i, is_increasing (h i))
    (Hbd : forall y, cone_norm y <= 1 ->
       cone_norm (f y +
         \big[precone_add/precone_zero]_(i : 'I_n) h i y) <= 1)
    (u : B) (x : B) (Hxu : cone_norm (x + u) <= 1) :
  dB (kfun f h) u x =
  SD g (vcons (dB f u x) (fun i => h i x + dB (h i) u x)) (f x) +
  \big[precone_add/precone_zero]_(k : 'I_n)
     SD g (hyb (fun i => h i x) (fun i => dB (h i) u x) k)
        (f x + h k x).
Proof.
have Hx1 : cone_norm x <= 1.
  by apply: le_trans Hxu; apply: cone_normp; exists u.
(* [f] and each [h i] are increasing at [x] in direction [u]. *)
have Hcf : f x <=p f (x + u) by exact: Hf.
have Hch i : h i x <=p h i (x + u) by exact: Hh.
(* [dB_E] term reads: [f(x+u) = f x + dB f u x], [h i (x+u) = ..]. *)
have EfU : f (x + u) = f x + dB f u x by exact: dB_E.
have EhU i : h i (x + u) = h i x + dB (h i) u x by exact: dB_E.
(* The shifted config stays in the ball, feeding [SD_723]. *)
have Hbnd : cone_norm (f (x + u) +
    \big[precone_add/precone_zero]_(i : 'I_n) h i (x + u)) <= 1 by exact: Hbd.
have HcS : cone_norm (f x + (dB f u x +
    \big[precone_add/precone_zero]_(i : 'I_n)
      (h i x + dB (h i) u x))) <= 1.
  rewrite precone_addA -EfU.
  by under eq_bigr => i _ do rewrite -EhU; exact: Hbnd.
(* [k(x+u)] is the LHS of [SD_723] with [u'=h(x)], [v'=Δh(u)(x)],
   head [u0=Δf(u)(x)], centre [f x]. *)
have Ekxu : kfun f h (x + u) =
    SD g (fun i => h i x + dB (h i) u x) (f x + dB f u x).
  rewrite /kfun -EfU; congr (SD g _ _); apply/funext => i; exact: EhU.
have step := SD_723 g Hg (fun i => h i x) (fun i => dB (h i) u x)
  (dB f u x) (f x) HcS.
(* [k] is increasing, so [dB_E] applies to [k] itself at [(x,u)]. *)
have Hkinc : is_increasing (kfun f h) by exact: kfun_increasing.
have Hkx : kfun f h x <=p kfun f h (x + u) by exact: Hkinc.
have Ek : kfun f h (x + u) = kfun f h x + dB (kfun f h) u x by exact: dB_E.
(* The first Lemma-7.23 term [SD g (h x) (f x) = k x] cancels. *)
apply: (@precone_cancel _ _ (kfun f h x)).
rewrite -Ek Ekxu step precone_addA.
by congr (_ + _).
Qed.

End Lemma726.

Arguments kfun {R B C D} g {n} f h.
Arguments kfun_increasing {R B C D} g Hg {n} f h Hf Hh Hbd.
Arguments dB_kfun {R B C D} g Hg {n} f h Hf Hh Hbd u x Hxu.

(** ** Sum engine for [is_n_increasing] — the additive [dB] on the ball
       (the closure machinery for Lemma 7.26)

    The local-cone [p]-increasing predicate [is_n_increasing] (findiff.v)
    recurses *into the local cone* [B_u] via [Δf(u) = Delta f (fun=>u)],
    exactly the recursion the paper's Lemma 7.26 needs ("[Δk(u)] is
    [p]-increasing from [B_u]").  We close it under finite sums.  The
    single-step difference [dB] is *additive on the ball* ([dB_add_at]):
    where [f], [g] are increasing at [(xb, u)] (e.g. on the unit ball),
    [dB (f+g) u xb = dB f u xb + dB g u xb] (by [dB_E] + cancellation), and
    [dB] depends only on the two endpoint values ([dB_congr]).  Since
    [is_n_increasing] is *ball-local* — its clauses (increasingness +
    [Delta]-recursion through [lc_step1]-admissible shifts) only probe
    unit-ball points — these give a congruence ([ninc_congr]) and the sum
    closure ([ninc_zero]/[ninc_add]/[ninc_bigP]). *)

Section NincSum.
Variable R : realType.
Variables B C : coneType R.
Local Open Scope precone_scope.

(** [dB] is additive at a point where both summands are increasing. *)
Lemma dB_add_at (f g : B -> C) (u xb : B)
    (Hf : f xb <=p f (xb + u)) (Hg : g xb <=p g (xb + u)) :
  dB (stm_add f g) u xb = dB f u xb + dB g u xb.
Proof.
have Hfg : stm_add f g xb <=p stm_add f g (xb + u).
  rewrite /stm_add; apply: precone_le_trans (precone_add_le_r _ Hf).
  exact: precone_add_le_l.
have E := dB_E (stm_add f g) u xb Hfg.
have Ef := dB_E f u xb Hf.
have Eg := dB_E g u xb Hg.
move: E; rewrite /stm_add Ef Eg.
have -> : f xb + dB f u xb + (g xb + dB g u xb)
    = (f xb + g xb) + (dB f u xb + dB g u xb).
  rewrite -!precone_addA; congr (_ + _).
  by rewrite precone_addA [dB f u xb + _]precone_addC -precone_addA.
by move/precone_cancel.
Qed.

(** [dB f u xb] depends only on the two endpoint values [f xb], [f(xb+u)]. *)
Lemma dB_congr (f g : B -> C) (u xb : B)
    (E0 : f xb = g xb) (E1 : f (xb + u) = g (xb + u)) :
  dB f u xb = dB g u xb.
Proof.
rewrite /dB /SD.
have Sp : Spos f 1 (fun _ : 'I_1 => u) xb = Spos g 1 (fun _ : 'I_1 => u) xb.
  by rewrite !Spos_oneu E1.
have Sn : Sneg f 1 (fun _ : 'I_1 => u) xb = Sneg g 1 (fun _ : 'I_1 => u) xb.
  by rewrite !Sneg_oneu E0.
by rewrite Sp Sn.
Qed.

(** [dB] of the zero map is [0], everywhere. *)
Lemma dB_zero (u xb : B) : dB (stm_zero B C) u xb = (0 : C).
Proof.
have Hle : (stm_zero B C) xb <=p (stm_zero B C) (xb + u).
  by rewrite /stm_zero; exact: precone_le_refl.
have E := dB_E (stm_zero B C) u xb Hle.
by move: E; rewrite /stm_zero precone_add0 => <-.
Qed.

End NincSum.

Arguments dB_add_at {R B C} f g u xb Hf Hg.
Arguments dB_congr {R B C} f g u xb E0 E1.
Arguments dB_zero {R B C} u xb.

(** [is_n_increasing p] depends only on the values on the unit ball: a
    congruence on the ball lifts through the local-cone recursion, because
    each [Delta f (fun=>u)] reads ([SD_Delta]) on the shifted [B]-points
    [lc_val x] and [lc_val x + u], both in [B_B] by [lc_step1]. *)
Lemma ninc_congr (p : nat) (R : realType) :
  forall (B C : coneType R) (f g : B -> C),
  (forall y : B, (cone_norm y <= 1)%R -> f y = g y) ->
  is_n_increasing p f -> is_n_increasing p g.
Proof.
elim: p R => [|p IHp] R B C f g Eqfg.
  move=> Hf x v Hxv; rewrite -!Eqfg//.
  - exact: Hf.
  - by apply: le_trans Hxv; apply: cone_normp; exists v.
move=> /= [Hinc Hrec]; split.
  move=> x v Hxv; rewrite -!Eqfg//.
  - exact: Hinc.
  - by apply: le_trans Hxv; apply: cone_normp; exists v.
move=> u Hu; apply: (IHp _ _ _ (Delta f (fun=> u))); last exact: Hrec.
move=> x Hx.
have Hball := lc_step1 Hu (w := x) Hx.
have key (y : B) :
    (\big[precone_add/precone_zero]_(i : 'I_1) (fun _ : 'I_1 => u) i + y
     = y + u)%PC.
  by rewrite big_ord1 precone_addC.
have Hlxu : (cone_norm (lc_val x + u)%PC <= 1)%R by rewrite -key; exact: Hball.
have Hlx : (cone_norm (lc_val x) <= 1)%R.
  by apply: le_trans Hx; exact: lc_val_norm_le.
by rewrite !SD_Delta; apply: dB_congr; exact: Eqfg.
Qed.

Arguments ninc_congr p {R B C} f g Eqfg.

(** The zero map is [n]-increasing, every [n], every source cone. *)
Lemma ninc_zero (p : nat) (R : realType) :
  forall (B C : coneType R), is_n_increasing p (stm_zero B C).
Proof.
elim: p R => [|p IHp] R B C; first by move=> x v _; exact: precone_le_refl.
split; first by move=> x v _; exact: precone_le_refl.
move=> u Hu.
have -> : Delta (stm_zero B C) (fun=> u) = stm_zero (lc_coneType Hu) C.
  by apply/funext => x; rewrite SD_Delta /stm_zero; exact: dB_zero.
exact: IHp.
Qed.

Arguments ninc_zero p {R B C}.

(** [is_n_increasing p f] gives [is_increasing f], for any [p]. *)
Lemma ninc_increasing (p : nat) (R : realType) (B C : coneType R)
    (f : B -> C) : is_n_increasing p f -> is_increasing f.
Proof. by case: p => [|p]// [Hinc _]. Qed.

Arguments ninc_increasing {p R B C} f.

(** A sum of [n]-increasing maps is [n]-increasing (generic source).  The
    [Delta]-recursion through [B_u] reduces — via [ninc_congr] and [dB]'s
    on-ball additivity [dB_add_at] (each summand increasing on the ball) —
    to the sum of the summands' own [Delta]-recursions. *)
Lemma ninc_add (p : nat) (R : realType) :
  forall (B C : coneType R) (f g : B -> C),
  is_n_increasing p f -> is_n_increasing p g ->
  is_n_increasing p (stm_add f g).
Proof.
elim: p R => [|p IHp] R B C f g.
  move=> Hf Hg x v Hxv; rewrite /stm_add.
  apply: precone_le_trans (precone_add_le_r _ (Hf x v Hxv)).
  exact: (precone_add_le_l _ (Hg x v Hxv)).
move=> [Hfi Hfr] [Hgi Hgr]; split.
  move=> x v Hxv; rewrite /stm_add.
  apply: precone_le_trans (precone_add_le_r _ (Hfi x v Hxv)).
  exact: (precone_add_le_l _ (Hgi x v Hxv)).
move=> u Hu.
apply: (ninc_congr p (stm_add (Delta f (fun=> u)) (Delta g (fun=> u)))).
  move=> x Hx.
  have Hball := lc_step1 Hu (w := x) Hx.
  have key (y : B) :
      (\big[precone_add/precone_zero]_(i : 'I_1) (fun _ : 'I_1 => u) i + y
       = y + u)%PC.
    by rewrite big_ord1 precone_addC.
  have Hlxu : (cone_norm (lc_val x + u)%PC <= 1)%R.
    by rewrite -key; exact: Hball.
  have Hf1 : (f (lc_val x) <=p f (lc_val x + u))%PC by exact: Hfi.
  have Hg1 : (g (lc_val x) <=p g (lc_val x + u))%PC by exact: Hgi.
  rewrite /stm_add !SD_Delta.
  rewrite -/(dB f u (lc_val x)) -/(dB g u (lc_val x)).
  rewrite -/(dB (stm_add f g) u (lc_val x)).
  by rewrite (dB_add_at f g u (lc_val x) Hf1 Hg1).
by apply: IHp; [exact: Hfr|exact: Hgr].
Qed.

Arguments ninc_add p {R B C} f g.

(** A finite [\sumP] of [n]-increasing maps is [n]-increasing.  This is the
    [is_n_increasing] analogue of [totmono_bigP] / [stable_bigP] — the
    closure that lets the sum [dB_kfun] of Lemma-7.23 summands stay
    [p]-increasing.  (The bare-[B] [Sinc] predicate cannot be summed: its
    [dB] recursion stays on [B], where [dB] additivity fails off the ball;
    the local-cone [is_n_increasing] avoids this, the gauge norm of [B_u]
    making the plain and shifted balls coincide.) *)
Lemma ninc_bigP (p : nat) (R : realType) (B C : coneType R)
    (T : finType) (A : {set T}) (g : T -> B -> C) :
  (forall i, i \in A -> is_n_increasing p (g i)) ->
  is_n_increasing p (\big[stm_add/stm_zero B C]_(i in A) g i).
Proof.
move=> Hg; elim/big_ind: _ => [|f1 f2 H1 H2|i iA].
- exact: ninc_zero.
- exact: ninc_add H1 H2.
- exact: Hg.
Qed.

Arguments ninc_bigP p {R B C T} A g.

(** [f ∘ lc_val : B_S → C] is totally monotonic ([totmono_shift_le] at
    shift [0]). *)
Lemma totmono_lcval (R : realType) (B C : coneType R) (f : B -> C)
    (S : B) (Hs : (cone_norm S < 1)%R) :
  is_totmono f -> is_totmono (fun x : lc_coneType Hs => f (lc_val x)).
Proof.
move=> Hf.
have := totmono_shift_le f S precone_zero Hs (precone_le0 S) Hf.
by congr is_totmono; apply/funext => x; rewrite precone_addr0.
Qed.

Arguments totmono_lcval {R B C} f {S} Hs.

(** ** Lemma 7.26 — the composition main lemma, generic-source induction
       — Paper §7.3 (txt 3713)

    Paper Lemma 7.26: for totally monotonic [f, h₁..hₙ : B_B → C] and
    [g : B_C → D] with [∀x∈B_B, f(x)+Σᵢ hᵢ(x) ∈ B_C], the composite
    [k(x) = Δg(h₁(x),…,hₙ(x))(f(x))] — read on the B-side as [kfun g f h⃗
    x = SD g (fun i ↦ hᵢ x)(f x)] — is totally monotonic.

    We deliver the paper's induction in full ([ninc_kfun]): *for every
    source cone, arity, and admissible data, [kfun g f h⃗] is
    [p]-increasing*, by induction on [p].

    - [p = 0]: [kfun_increasing] (Lemma 7.25 for the composite).
    - [p.+1]: for each direction [u], [Δk(u)] must be [p]-increasing *from
      [B_u]*.  By [SD_Delta] + [dB_kfun] (Lemma 7.23 full telescope, the
      first term annihilated by the subtraction) it equals — on the unit
      ball of [B_u] — a [\sumP] of [n+1] [kfun]-summands *at source [B_u]*:
      the head [kfun g (f∘lc_val) (dirH)] at arity [n+1], and [n] hybrids
      [kfun g (f∘lc_val + hₖ∘lc_val) (dirK k)] at arity [n].  Their
      directions are totally monotonic on [B_u] ([totmono_dirH]/[totmono_dirK]
      via [totmono_Delta]-style [totmono_dB_lc] and [totmono_shift_le]) and
      satisfy the codomain bound ([cod_head]/[cod_hyb], the hybrid sum being
      [≤p] the full shifted config which is in [B_C]).  *The inductive
      hypothesis applies at source [B_u]* — this is the generic-source
      device that sidesteps the explicit nested-cone transport: the recursion
      is just "the same theorem at the smaller source cone [B_u]".  The
      [\sumP] is [p]-increasing by [ninc_bigP]/[ninc_add]; the [ninc_congr]
      bridge transfers it to [Δk(u)].

    The full Lemma 7.26 (total monotonicity of [kfun]) and Theorem 7.30
    ([stable_comp]) follow at [n = 0] below. *)

Section Lemma726main.
Variable R : realType.
Variables C D : coneType R.
Variable g : C -> D.
Hypothesis Hg : is_totmono g.
Local Open Scope precone_scope.

(** The clean head direction family on [B_S]: [Δf(S)] prepended to the
    shifts [hᵢ(lc_val·+S)].  The shift direction is the cone centre [S]
    itself (in the recursion [S = Σᵢ uᵢ] of the one-element family). *)
Definition dirH (B : coneType R) (S : B) (HS : cone_norm S < 1)
    (n : nat) (f : B -> C) (h : 'I_n -> (B -> C))
    : 'I_n.+1 -> lc_coneType HS -> C :=
  fun i x => vcons (dB f S (lc_val x)) (fun j => h j (lc_val x + S)) i.

(** The clean hybrid direction family at split position [k]. *)
Definition dirK (B : coneType R) (S : B) (HS : cone_norm S < 1)
    (n : nat) (h : 'I_n -> (B -> C)) (k : 'I_n)
    : 'I_n -> lc_coneType HS -> C :=
  fun i x => if (i < k)%N then h i (lc_val x)
             else if i == k then dB (h i) S (lc_val x)
             else h i (lc_val x + S).

(** [Δf(S)] read on [B_S] is totally monotonic.  Mirrors [totmono_shift]:
    the [B_S]-config reads through [lc_val] as a shifted [B]-config of
    [dB f S], whose (7.1) bound is [totmono_dB] on the shifted ball, the
    norm side-condition being [lc_step1]. *)
Lemma totmono_dB_lc (B : coneType R) (S : B) (HS : cone_norm S < 1)
    (f : B -> C) (Hf : is_totmono f) :
  is_totmono (fun x : lc_coneType HS => dB f S (lc_val x)).
Proof.
move=> m xL wL Hnorm.
have argE (I : {set 'I_m}) :
    dB f S (lc_val (tm_arg xL wL I)) =
    dB f S (lc_val xL + \big[precone_add/precone_zero]_(i in I) lc_val (wL i)).
  by congr (dB f S _); rewrite /tm_arg lc_valD lc_val_big.
have Hc : cone_norm (lc_val xL + S +
    \big[precone_add/precone_zero]_(i : 'I_m) lc_val (wL i)) <= 1.
  have key := lc_step1 HS (w := xL +
    \big[precone_add/precone_zero]_(i : 'I_m) wL i) Hnorm.
  rewrite lc_valD lc_val_big in key.
  apply: le_trans key; apply: cone_normp.
  by rewrite (precone_addC (lc_val xL) S) -precone_addA; exact: precone_le_refl.
have := totmono_dB f Hf S (fun i => lc_val (wL i)) (lc_val xL) Hc.
rewrite /Sneg /Spos.
under eq_bigr => I _ do rewrite -argE.
by under [X in _ <=p X]eq_bigr => I _ do rewrite -argE.
Qed.

(** Each head direction is totally monotonic on [B_S]. *)
Lemma totmono_dirH (B : coneType R) (S : B) (HS : cone_norm S < 1)
    (n : nat) (f : B -> C) (h : 'I_n -> (B -> C))
    (Hf : is_totmono f) (Hh : forall i, is_totmono (h i)) (i : 'I_n.+1) :
  is_totmono (@dirH B S HS n f h i).
Proof.
rewrite /dirH; case: (unliftP ord0 i) => [j ->|->].
- under eq_fun => x do rewrite vconsS.
  exact: (totmono_shift_le (h j) S S HS (precone_le_refl S) (Hh j)).
- under eq_fun => x do rewrite vcons0.
  exact: (@totmono_dB_lc B S HS f Hf).
Qed.

(** Each hybrid direction is totally monotonic on [B_S]. *)
Lemma totmono_dirK (B : coneType R) (S : B) (HS : cone_norm S < 1)
    (n : nat) (h : 'I_n -> (B -> C))
    (Hh : forall i, is_totmono (h i)) (k i : 'I_n) :
  is_totmono (@dirK B S HS n h k i).
Proof.
rewrite /dirK; case: (ltngtP i k) => [Hik|Hik|Hik].
- exact: (totmono_lcval (h i) HS (Hh i)).
- have -> : (i == k) = false by rewrite -val_eqE gtn_eqF.
  exact: (totmono_shift_le (h i) S S HS (precone_le_refl S) (Hh i)).
- have -> : (i == k) = true by apply/eqP; exact: val_inj.
  exact: (@totmono_dB_lc B S HS (h i) (Hh i)).
Qed.

(** For [x] in the unit ball of [B_S], [lc_val x + S] stays in [B_B]. *)
Lemma lc_shift_ball (B : coneType R) (S : B) (HS : cone_norm S < 1)
    (x : lc_coneType HS) (Hx : cone_norm x <= 1) :
  cone_norm (lc_val x + S) <= 1.
Proof. by have key := lc_step1 HS (w := x) Hx; rewrite precone_addC. Qed.

(** Head codomain condition for the inductive hypothesis: the head config
    sum is exactly the full shifted config [f(x'+S) + Σⱼ hⱼ(x'+S) ∈ B_C]. *)
Lemma cod_head (B : coneType R) (S : B) (HS : cone_norm S < 1)
    (n : nat) (f : B -> C) (h : 'I_n -> (B -> C))
    (Hf : is_increasing f) (Hh : forall i, is_increasing (h i))
    (Hbd : forall y : B, cone_norm y <= 1 ->
       cone_norm (f y + \big[precone_add/precone_zero]_(i : 'I_n) h i y) <= 1)
    (x : lc_coneType HS) (Hx : cone_norm x <= 1) :
  cone_norm ((fun z : lc_coneType HS => f (lc_val z)) x +
    \big[precone_add/precone_zero]_(i : 'I_n.+1) (@dirH B S HS n f h) i x) <= 1.
Proof.
set x' := lc_val x.
have Hxu : cone_norm (x' + S) <= 1 by exact: lc_shift_ball.
have EfU : f (x' + S) = f x' + dB f S x' by apply: dB_E; exact: Hf.
have EhU i : h i (x' + S) = h i x' + dB (h i) S x' by apply: dB_E; exact: Hh.
rewrite /dirH; under eq_bigr => i _ do rewrite -/x'.
rewrite sum_vcons.
have -> : (f x' + (dB f S x' +
    \big[precone_add/precone_zero]_(j : 'I_n) h j (x' + S)))
    = f (x' + S) + \big[precone_add/precone_zero]_(j : 'I_n) h j (x' + S).
  by rewrite EfU precone_addA.
exact: Hbd.
Qed.

(** Hybrid codomain condition: the hybrid config sum is [≤p] the full
    shifted config sum (in [B_C]), hence has norm [≤ 1] by (Normp). *)
Lemma cod_hyb (B : coneType R) (S : B) (HS : cone_norm S < 1)
    (n : nat) (f : B -> C) (h : 'I_n -> (B -> C))
    (Hf : is_increasing f) (Hh : forall i, is_increasing (h i))
    (Hbd : forall y : B, cone_norm y <= 1 ->
       cone_norm (f y + \big[precone_add/precone_zero]_(i : 'I_n) h i y) <= 1)
    (k : 'I_n) (x : lc_coneType HS) (Hx : cone_norm x <= 1) :
  cone_norm ((stm_add (fun z : lc_coneType HS => f (lc_val z))
       (fun z => h k (lc_val z))) x +
    \big[precone_add/precone_zero]_(i : 'I_n) (@dirK B S HS n h k) i x) <= 1.
Proof.
set x' := lc_val x.
have Hxu : cone_norm (x' + S) <= 1 by exact: lc_shift_ball.
have EfU : f (x' + S) = f x' + dB f S x' by apply: dB_E; exact: Hf.
have EhU i : h i (x' + S) = h i x' + dB (h i) S x' by apply: dB_E; exact: Hh.
have Hfull : cone_norm (f (x' + S) +
    \big[precone_add/precone_zero]_(i : 'I_n) h i (x' + S)) <= 1 by exact: Hbd.
pose extra (i : 'I_n) : C :=
  if (i < k)%N then dB (h i) S x' else if i == k then h i x' else 0.
have decompi (i : 'I_n) :
    h i (x' + S) = (@dirK B S HS n h k) i x + extra i.
  rewrite /dirK /extra -/x' EhU.
  case: (ltngtP i k) => [Hik|Hik|Hik].
  - by [].
  - have -> : (i == k) = false by rewrite -val_eqE gtn_eqF.
    by rewrite precone_addr0.
  - have -> : (i == k) = true by apply/eqP; exact: val_inj.
    by rewrite precone_addC.
have Hsum : \big[precone_add/precone_zero]_(i : 'I_n) h i (x' + S) =
    \big[precone_add/precone_zero]_(i : 'I_n) (@dirK B S HS n h k) i x +
    \big[precone_add/precone_zero]_(i : 'I_n) extra i.
  rewrite -big_split/=; apply: eq_bigr => i _; exact: decompi.
set SK := \big[precone_add/precone_zero]_(i : 'I_n) (@dirK B S HS n h k) i x.
set SE := \big[precone_add/precone_zero]_(i : 'I_n) extra i.
have HhkSE : h k x' <=p SE.
  rewrite /SE (bigD1 k)//=.
  have -> : extra k = h k x' by rewrite /extra ltnn eqxx.
  by exists (\big[precone_add/precone_zero]_(i | i != k) extra i).
apply: le_trans Hfull; apply: cone_normp.
rewrite EfU Hsum -/SK -/SE /stm_add -/x'.
have [W' HW'] := HhkSE.
exists (dB f S x' + W').
rewrite HW' -!precone_addA; congr (_ + _).
by rewrite !precone_addA [dB f S x' + SK]precone_addC [_ + h k x']precone_addC
  -!precone_addA.
Qed.

(** **Lemma 7.26, generic-source [p]-induction.**  [kfun g f h⃗] is
    [p]-increasing for every source cone, arity, and admissible data. *)
Lemma ninc_kfun (p : nat) :
  forall (B : coneType R) (n : nat) (f : B -> C) (h : 'I_n -> (B -> C)),
  is_totmono f -> (forall i, is_totmono (h i)) ->
  (forall y : B, cone_norm y <= 1 ->
     cone_norm (f y + \big[precone_add/precone_zero]_(i : 'I_n) h i y) <= 1) ->
  is_n_increasing p (kfun g f h).
Proof.
elim: p => [|p IHp] B n f h Hf Hh Hbd.
  apply: (kfun_increasing g Hg) => //.
  - exact: (totmono_increasing Hf).
  - by move=> i; exact: (totmono_increasing (Hh i)).
split.
  apply: (kfun_increasing g Hg) => //.
  - exact: (totmono_increasing Hf).
  - by move=> i; exact: (totmono_increasing (Hh i)).
move=> u Hu'.
set S := \big[precone_add/precone_zero]_(i : 'I_1) (fun _ : 'I_1 => u) i.
have SeqU : S = u by rewrite /S big_ord1.
pose Fh : lc_coneType Hu' -> C := fun x => f (lc_val x).
pose HEAD : lc_coneType Hu' -> D := kfun g Fh (@dirH B S Hu' n f h).
pose Fk (k : 'I_n) : lc_coneType Hu' -> C :=
  stm_add (fun x => f (lc_val x)) (fun x => h k (lc_val x)).
pose HYB (k : 'I_n) : lc_coneType Hu' -> D :=
  kfun g (Fk k) (@dirK B S Hu' n h k).
have Htot_f : is_totmono Fh by exact: (totmono_lcval f Hu' Hf).
have HEADok : is_n_increasing p HEAD.
  apply: IHp; first exact: Htot_f.
  - exact: (@totmono_dirH B S Hu' n f h Hf Hh).
  - move=> x Hx.
    exact: (@cod_head B S Hu' n f h
      (totmono_increasing Hf) (fun i => totmono_increasing (Hh i)) Hbd x Hx).
have HYBok (k : 'I_n) : is_n_increasing p (HYB k).
  apply: IHp.
  - by apply: totmono_add; [exact: Htot_f|
      exact: (totmono_lcval (h k) Hu' (Hh k))].
  - exact: (@totmono_dirK B S Hu' n h Hh k).
  - move=> x Hx.
    exact: (@cod_hyb B S Hu' n f h
      (totmono_increasing Hf) (fun i => totmono_increasing (Hh i)) Hbd k x Hx).
pose Dtil : lc_coneType Hu' -> D :=
  stm_add HEAD
    (\big[stm_add/stm_zero (lc_coneType Hu') D]_(k in [set: 'I_n]) HYB k).
have HDtil : is_n_increasing p Dtil.
  apply: ninc_add; first exact: HEADok.
  by apply: ninc_bigP => k _; exact: HYBok.
apply: (ninc_congr p Dtil); last exact: HDtil.
move=> x Hx.
set x' := lc_val x.
rewrite SD_Delta -/x'.
have Hxu : cone_norm (x' + u) <= 1.
  by rewrite -SeqU; exact: (@lc_shift_ball B S Hu' x Hx).
have EK := dB_kfun g Hg f h (totmono_increasing Hf)
  (fun i => totmono_increasing (Hh i)) Hbd u x' Hxu.
rewrite -/(dB (kfun g f h) u x') EK.
have Hbigeval :
  (\big[stm_add/stm_zero (lc_coneType Hu') D]_(k in [set: 'I_n]) HYB k) x
    = \big[precone_add/precone_zero]_(k in [set: 'I_n]) HYB k x.
  by rewrite (@big_morph _ _ (fun F : lc_coneType Hu' -> D => F x)
    precone_zero precone_add (stm_zero (lc_coneType Hu') D) stm_add).
rewrite /Dtil /stm_add Hbigeval.
congr (_ + _).
  rewrite /HEAD /kfun /Fh /dirH -/x'.
  congr (SD g _ (f x')); apply/funext => i.
  rewrite SeqU; case: (unliftP ord0 i) => [j ->|->]; last by rewrite !vcons0.
  rewrite !vconsS.
  have EhU : h j (x' + u) = h j x' + dB (h j) u x'.
    by apply: dB_E; exact: (totmono_increasing (Hh j)).
  by rewrite EhU.
rewrite [LHS](eq_bigl predT); last by move=> k; rewrite finset.in_setT.
apply: eq_bigr => k _.
rewrite /HYB /kfun /Fk /dirK /stm_add /hyb -/x' SeqU.
congr (SD g _ (f x' + h k x')); apply/funext => i.
case: (ltngtP i k) => [Hik|Hik|Hik]//.
  have EhU : h i (x' + u) = h i x' + dB (h i) u x'.
    by apply: dB_E; exact: (totmono_increasing (Hh i)).
  by rewrite EhU.
by have -> : (i == k) = true by apply/eqP; exact: val_inj.
Qed.

End Lemma726main.

Arguments dirH {R C B} S HS {n} f h.
Arguments dirK {R C B} S HS {n} h k.
Arguments ninc_kfun {R C D} g Hg p B n f h Hf Hh Hbd.

(** ** ω-continuity and boundedness of a composite — Paper §7.4 (Thm 7.30)
       (the *unblocked* halves of [stable_comp])

    The composition theorem 7.30 — [g ∘ f] stable-and-measurable for [f, g]

    The composition theorem 7.30 — [g ∘ f] stable-and-measurable for [f, g]
    stable-and-measurable of norm [≤ 1] — has, by the paper's own remark,
    exactly *one* non-obvious ingredient: that [g ∘ f] is totally
    monotonic, "obtained by Lemma 7.26 applied with [n = 0]".  Everything
    else is direct.  We deliver those direct halves here, fully proved:

    - [scott_comp]: ω-continuity of [g ∘ f] composes.  A unit-ball chain
      [u] is sent by [f] (increasing, ω-continuous, norm [≤ 1] so it stays
      in [B_C]) to the unit-ball chain [f ∘ u] whose supremum is [f]'s
      ([cone_sup_at_ball] turning [f]'s radius-[1] [cone_sup_at] into a
      [cone_sup_ball]); [g]'s own ω-continuity then commutes through, the
      radius reconciled by [cone_sup_at_indep].

    - [bounded_comp]: [g ∘ f] is bounded ([g]'s bound at the [≤ 1]-bounded
      image [f x]).

    - [meas_path_comp]: path-preservation composes — [(g∘f)∘γ = g∘(f∘γ)],
      and [f∘γ] stays in [B_C] (norm [≤ 1]), so [g]'s path-preservation
      applies to it.

    The remaining ingredient [totmono_comp] ([g ∘ f] totally monotonic,
    the [n = 0] corollary of Lemma 7.26) is delivered after this section
    via [ninc_kfun] + [is_n_increasing_totmono]; the three lemmas below then
    assemble [stable_comp]/[meas_stable_comp].  The *generic-source*
    induction of [ninc_kfun] — run on the local-cone predicate
    [is_n_increasing], quantified over all source cones — sidesteps the
    explicit nested-cone transport (see [ninc_kfun]; the bare-[B] forward
    bridge [is_totmono ⇒ ∀p, Sinc p] is genuinely false). *)

Section CompClosure.
Variable R : realType.
Variables B C D : coneType R.
Local Open Scope precone_scope.

(** **ω-continuity composes.**  [f] ω-continuous, increasing, norm [≤ 1];
    [g] ω-continuous ⇒ [g ∘ f : B → D] is [is_scott_continuous_unit]. *)
Lemma scott_comp (f : B -> C) (g : C -> D)
    (Hfc : is_scott_continuous_unit f) (Hfi : is_increasing f)
    (Hfb : forall x, cone_norm x <= 1 -> cone_norm (f x) <= 1)
    (Hgc : is_scott_continuous_unit g) :
  is_scott_continuous_unit (fun x => g (f x)).
Proof.
move=> Mf u uch ub1 fuch fubMf Mfpos.
set x := cone_sup_ball u uch ub1.
have fch m : f (u m) <=p f (u m.+1).
  by have [d Hd] := uch m; rewrite Hd; apply: Hfi; rewrite -Hd; exact: ub1.
have fb1 m : cone_norm (f (u m)) <= 1 by apply: Hfb; exact: ub1.
have fxE : f x = cone_sup_ball (f \o u) fch fb1.
  have fb1' m : cone_norm (f (u m)) <= (1%:nng : {nonneg R})%:num by exact: fb1.
  have onepos : (0 < (1%:nng : {nonneg R})%:num)%R by rewrite /= ltr01.
  rewrite /x (Hfc 1%:nng u uch ub1 fch fb1' onepos).
  exact: (cone_sup_at_ball fch fb1 fb1' onepos).
rewrite /comp/= fxE (Hgc Mf (f \o u) fch fb1 fuch fubMf Mfpos).
exact: cone_sup_at_indep.
Qed.

(** **Boundedness composes** (bound [g]'s value at the [≤ 1]-image). *)
Lemma bounded_comp (f : B -> C) (g : C -> D)
    (Hfb : forall x, cone_norm x <= 1 -> cone_norm (f x) <= 1)
    (Hg : exists M : R, forall y, cone_norm y <= 1 -> cone_norm (g y) <= M) :
  exists M : R, forall x, cone_norm x <= 1 ->
    cone_norm ((fun x => g (f x)) x) <= M.
Proof. by have [M HM] := Hg; exists M => x Hx; apply: HM; exact: Hfb. Qed.

End CompClosure.

Arguments scott_comp {R B C D} f g Hfc Hfi Hfb Hgc.
Arguments bounded_comp {R B C D} f g Hfb Hg.

(** **Path-preservation composes** — Paper §7.4 (the measurable half of
    Thm 7.30).  [(g∘f)∘γ = g∘(f∘γ)]; the inner image [f∘γ] stays in [B_C]
    (norm [≤ 1] by [f]'s bound), so [g]'s path-preservation applies. *)
Lemma meas_path_comp (R : realType) (Ar : MeasSubcat R)
    (B C D : MCone.type Ar) (f : B -> C) (g : C -> D)
    (Hfb : forall x, cone_norm x <= 1 -> cone_norm (f x) <= 1)
    (Hfp : forall (X : ar_obj Ar) (γ : ar_carrier Ar X -> B),
       (forall r, cone_norm (γ r) <= 1) ->
       is_measurable_path (Ar:=Ar) (C:=B) γ ->
       is_measurable_path (Ar:=Ar) (C:=C) (fun r => f (γ r)))
    (Hgp : forall (X : ar_obj Ar) (γ : ar_carrier Ar X -> C),
       (forall r, cone_norm (γ r) <= 1) ->
       is_measurable_path (Ar:=Ar) (C:=C) γ ->
       is_measurable_path (Ar:=Ar) (C:=D) (fun r => g (γ r)))
    (X : ar_obj Ar) (γ : ar_carrier Ar X -> B)
    (Hγb : forall r, cone_norm (γ r) <= 1)
    (Hγ : is_measurable_path (Ar:=Ar) (C:=B) γ) :
  is_measurable_path (Ar:=Ar) (C:=D) (fun r => g (f (γ r))).
Proof.
apply: (Hgp X (fun r => f (γ r))); first by move=> r; apply: Hfb; exact: Hγb.
exact: Hfp.
Qed.

Arguments meas_path_comp {R Ar B C D} f g Hfb Hfp Hgp X γ Hγb Hγ.

(** ** Lemma 7.26 corollary + Theorem 7.30 — closure under composition

    [totmono_comp] is Lemma 7.26 at [n = 0]: [SD g () (f x) = g (f x)]
    ([SD0]), so [g ∘ f = kfun g f ()] is [p]-increasing for every [p]
    ([ninc_kfun], the [n = 0] codomain bound being [f]'s [≤ 1]-image
    [Hfb]); the closed-ball converse [is_n_increasing_totmono] then gives
    total monotonicity, its ω-continuity ingredient supplied by
    [scott_comp].  [stable_comp] assembles total monotonicity with
    [bounded_comp] and [scott_comp]; [meas_stable_comp] adds
    [meas_path_comp].  These close Theorem 7.30. *)

Section CompTotmono.
Variable R : realType.
Variables B C D : coneType R.
Local Open Scope precone_scope.

(** **[g ∘ f] totally monotonic** (Lemma 7.26 at [n = 0]). *)
Lemma totmono_comp (f : B -> C) (g : C -> D)
    (Hf : is_stable f) (Hg : is_stable g)
    (Hfb : forall x, cone_norm x <= 1 -> cone_norm (f x) <= 1) :
  is_totmono (fun x => g (f x)).
Proof.
have [Hfm Hfbd Hfc] := Hf.
have [Hgm Hgbd Hgc] := Hg.
have Ekf : kfun g f (fun _ : 'I_0 => stm_zero B C) = (fun x => g (f x)).
  by apply/funext => x; rewrite /kfun SD0.
have Hninc k : is_n_increasing k (fun x => g (f x)).
  rewrite -Ekf; apply: (ninc_kfun g Hgm) => //; first by case.
  by move=> y Hy; rewrite big_ord0 precone_addr0; exact: Hfb.
apply: (is_n_increasing_totmono _ Hninc).
exact: (scott_comp f g Hfc (totmono_increasing Hfm) Hfb Hgc).
Qed.

(** **[g ∘ f] stable** (Theorem 7.30, [coneType] form). *)
Lemma stable_comp (f : B -> C) (g : C -> D)
    (Hf : is_stable f) (Hg : is_stable g)
    (Hfb : forall x, cone_norm x <= 1 -> cone_norm (f x) <= 1) :
  is_stable (fun x => g (f x)).
Proof.
have [Hfm Hfbd Hfc] := Hf.
have [Hgm Hgbd Hgc] := Hg.
split.
- exact: totmono_comp Hf Hg Hfb.
- exact: (bounded_comp f g Hfb Hgbd).
- exact: (scott_comp f g Hfc (totmono_increasing Hfm) Hfb Hgc).
Qed.

End CompTotmono.

Arguments totmono_comp {R B C D} f g Hf Hg Hfb.
Arguments stable_comp {R B C D} f g Hf Hg Hfb.

(** **[g ∘ f] stable-and-measurable** (Theorem 7.30). *)
Lemma meas_stable_comp (R : realType) (Ar : MeasSubcat R)
    (B C D : MCone.type Ar) (f : B -> C) (g : C -> D)
    (Hf : is_meas_stable f) (Hg : is_meas_stable g)
    (Hfb : forall x, cone_norm x <= 1 -> cone_norm (f x) <= 1) :
  is_meas_stable (fun x => g (f x)).
Proof.
have [Hfs Hfp] := Hf.
have [Hgs Hgp] := Hg.
split; first exact: (stable_comp f g Hfs Hgs Hfb).
move=> X γ Hγb Hγ.
exact: (meas_path_comp f g Hfb Hfp Hgp X γ Hγb Hγ).
Qed.

Arguments meas_stable_comp {R Ar B C D} f g Hf Hg Hfb.

(** ** Status of §7.3 in this file
       (what is delivered here, and the precise remaining walls)

    Delivered (no [Admitted], no [Axiom]):

    - **[scott_shift_le]** / **[stable_shift_le]**: the dominated shift
      [x ↦ f(lc_val x + s)] of a totally-monotonic-and-ω-continuous
      (resp. stable) [f] by [s ≤p S] is ω-continuous (resp. stable) on
      [B_S = local_cone S].  ω-continuity composes [findiff.v]'s
      [lc_val_scott] (ω-continuity of the inclusion [lc_val : B_S → B])
      with [f]'s [is_scott_continuous_unit], the shift [+ s] commuting
      through the [B]-supremum by [sup_ball_addr].  *This is exactly the
      composition that [findiff.v] could not perform — it cannot import
      [diff_scott_at]/[is_scott_continuous_unit]; [compose.v] can.*

    - **[stable_bigP]**: a finite [\sumP] of stable maps is stable (the
      stable analogue of [findiff.v]'s [totmono_bigP]).

    - **[diff_scott_unit]**: the unit-ball restriction of [stablehom.v]'s
      [diff_scott_at] (the difference [g₀ ⊖ f₀] is ω-continuous when the
      split [g₀ = f₀ + w₀] holds on the chain and its supremum only).

    - **[stable_Delta_pos]** / **[stable_Delta_neg]**: the halves
      [Δ⁺f(u⃗)], [Δ⁻f(u⃗)] are *stable* on [B_u⃗] — each a finite [\sumP]
      ([stable_bigP]) of dominated shifts ([stable_shift_le]).

    - **[scott_Delta]** (Lemma 7.20, the ω-continuity ingredient of the
      [Δf(u⃗)] clause): [Δf(u⃗) : B_u⃗ → C] is [is_scott_continuous_unit]
      for a *stable* [f].  [Δf(u⃗) = Δ⁺ ⊖ Δ⁻] with [Δ⁺]/[Δ⁻] stable; the
      difference is ω-continuous by [diff_scott_unit], the split
      [Δ⁺ = Δ⁻ + Δf(u⃗)] holding on the unit ball by total monotonicity
      ([Sneg_le_Spos] read through [Delta_E]), and centre-monotonicity of
      [Δf(u⃗)] supplied by [findiff.v]'s [Delta_mono].

    B-side reformulation (Def 7.15 / Lemmas 7.16–7.18, no local cone):

    - **[dB]** / **[dB_E]**: the bare-[B] single-step difference
      [dB f u xb = SD f (fun↦u) xb = f(xb+u) ⊖ f(xb)], with the defining
      equation [f(xb+u) = f xb + dB f u xb] on the ball.  [dB f u : B → C]
      stays on [B].

    - **[Sinc]**: the B-side [p]-increasing predicate ([Sinc 0] = increasing;
      [Sinc p.+1 f] = increasing ∧ ∀ interior [u], [Sinc p (dB f u)]).  Its
      recursive call is on the *same* carrier [B → C], whereas
      [is_n_increasing] recurses into the *nested local cone* [lc_coneType
      Hu] — the carrier that forces the blocked cast.

    - **[Sinc_dB]** (Lemma 7.16, B-side): [(∀p, Sinc p f) ⇒ ∀p, Sinc p
      (dB f u)] for interior [u].  This is the **multi-direction bootstrap**
      the local-cone [is_n_increasing] could not take without the
      nested-cone transport; B-side it is a one-line projection (the second
      conjunct of [Sinc] at [p.+1]), because [dB f u] lives on bare [B].

    - **[totmono_dB]** (Lemma 7.18, B-side): for [f] totally monotonic and
      [u] interior, [dB f u] satisfies the (7.1) inequality
      [Sneg (dB f u) w xb ≤p Spos (dB f u) w xb] at every *shifted-ball*
      configuration [‖xb + u + Σᵢ wᵢ‖ ≤ 1].  The bare-[B] twin of
      [totmono_Delta1]: the two summed [n = 1] equations [SDpos_dB]/[SDneg_dB]
      ([Sε f (xb+u) = Sε f xb + Sε (dB f u) xb], by [dB_E] term-by-term)
      reduce the order to [Sdiff_mono] of [f] after one cancellation.  No
      local-cone cast; the only price is the *explicit* shifted-ball bound,
      which [B_u]/[lc_step1] supplied for free in [totmono_Delta1].

    - **[SD_consdB]** (Lemma 7.17/7.22, the B-side *nested* recurrence):
      [SD f (u₀ :: u⃗) xb = SD (dB f u₀) u⃗ xb] — the bare-[B] analogue of
      [Δf(u₀ :: u⃗) = Δ(Δf(u₀))(u⃗)] with no local cone.  The head difference
      of [SD f] in direction [u₀] *is* the [SD] of the single-step
      difference [dB f u₀]: the [SD]-cons recurrence [SD_cons] and the
      summed [n=1] splits [SDpos_dB]/[SDneg_dB] identify them after
      cancellation.  This is the linearity-in-[f] content of the §7.3
      composition track, on bare centres.

    - **[Sinc_conv_strict]** (B-side Theorem 7.19, *open*-ball converse):
      [(∀p, Sinc p g) ⇒] the (7.1) inequality at every strictly-interior
      configuration ([‖x + Σ uᵢ‖ < 1]).  Bare-[B] induction on the arity,
      peeling the head by [Spos_recur]/[Sneg_recur]: inside the open ball
      the head [u₀] is strictly interior, so [Sinc_dB] supplies
      [∀p, Sinc p (dB g u₀)] and the increasing-only splits
      [SDpos_dB_i]/[SDneg_dB_i] reduce the goal to the inductive hypothesis
      for [dB g u₀].  **This is where the shifted-vs-plain bound is
      reconciled**: the engine [SDpos_dB_i] consumes the *given* shifted
      bound [‖x + u₀ + Σ wᵢ‖ ≤ 1] (the arity-[n+1] config bound), while the
      inductive hypothesis for [dB g u₀] needs only the *weaker* plain bound
      [‖x + Σ wᵢ‖ < 1], which the config bound implies by norm-monotonicity.
      The head shift is absorbed into [dB], so no gauge conversion is
      needed — the bare-[B] recursion carries exactly the bounds it produces.

    - **[Sinc_totmono]** (B-side Theorem 7.19, *closed*-ball converse): a
      map [f] that is [Sinc p] for all [p] and [is_scott_continuous_unit]
      (i.e. the ω-continuity half of stability) is totally monotonic.  The
      boundary is reached by the scaling-chain limit of [Sinc_conv_strict]:
      a closed-ball [z] is the [cone_sup_ball] of the strictly-interior
      chain [λₘ ·: z] ([scale_chain_sup]), and ω-continuity passes the
      open-ball inequality to the boundary ([dsum_lub]/[dsum_ub]).  This is
      the bare-[B] twin of [findiff.v]'s [is_n_increasing_totmono], reusing
      its very machinery but with *no local-cone cast anywhere* — the
      nested-cone transport that blocked the [is_n_increasing] route is
      replaced by the [SD]-linearity recurrence [SD_consdB]/[Sinc_dB] and
      never appears.

    Lemma 7.23, general arity (the §7.3 telescope, [B]-side):

    - **[SD_split_idx]** (interior-position [SD_add]): if [v⃗ k = a + b]
      then [SD f v⃗ xb = SD f (v⃗[k:=a]) xb + SD f (v⃗[k:=b]) (xb + a)] — the
      head-only [SD_add] of [findiff.v] lifted to an *arbitrary* position
      [k], by transposing [k] to the head ([tperm ord0 k]), splitting, and
      transposing back ([SD_perm]).  No prefix-concatenation / ordinal cast
      is needed: the carrier ['I_n] is fixed throughout.

    - **[SD_diag]** (Lemma 7.23, diagonal split): [SD f (u⃗+v⃗) xb =
      SD f u⃗ xb + Σⱼ SD f (hybⱼ)(xb + uⱼ)], with [hybⱼ] the hybrid family
      [(u₁,…,u_{j-1}, vⱼ, u_{j+1}+v_{j+1},…)].  The general arity of
      [findiff.v]'s base [SD_723_1] (n = 1).  Proof by a *diagonal sweep*
      ([SD_diag_sweep]): [mixt j] is [u] before [j], [u+v] from [j] on (so
      [mixt 0 = u⃗+v⃗], [mixt n = u⃗]); each [SD_split_idx] at position [j]
      grows the [u]-prefix ([mixt j → mixt j.+1]) and emits the hybrid term
      [hybⱼ] at the single-direction-shifted centre [xb + uⱼ].  Telescoping
      [j = 0 .. n] collects [Σⱼ] and leaves [SD f u⃗ xb].  *The original
      "frozen head / prefix-concatenation" obstruction is sidestepped
      entirely*: the sweep never leaves the fixed ['I_n] carrier, so no
      [lshift]/[rshift]/[split] or [m + k.+1 = m.+1 + k] cast appears.

    - **[SD_723]** (Lemma 7.23, full telescope): [SD f (u⃗+v⃗)(xb + u₀) =
      SD f u⃗ xb + SD f (u₀ :: u⃗+v⃗) xb + Σⱼ SD f (hybⱼ)(xb + uⱼ)] — peel
      the head shift [u₀] by [SD_cons] (head term [Δf(u₀, u⃗+v⃗)(x)]), then
      split the residual diagonally by [SD_diag].  The general arity of
      [SD_723_1].

    The [SD_concat] composition engine + Lemma 7.20 ([Δf] clause):

    - **[catf]/[catset]/[catset_card]/[catset_odd]/[catset_Ppos]/
      [catset_Pneg]**: the concatenation [u⃗ ++ w⃗ : 'I_(n+m) → B] and the
      bijection [{set 'I_n} × {set 'I_m} ≃ {set 'I_(n+m)}] ([catset], via the
      [lshift]/[rshift] preimages [setL]/[setR]) with the parity
      *multiplicativity* [odd((n+m)−#K) = odd(n−#I) ⊕ odd(m−#J)]
      ([catset_odd]): [K ∈ Pε(n+m)] iff the [I]- and [J]-signs combine to
      [ε].  Cardinality splits [#catset = #I + #J] ([catset_card]) by the
      disjointness of the two images.

    - **[sumP_catf]/[sumP_catf_T]**: the [catf]-sum over [K] (resp. the full
      sum) splits as the [setL]-sum of [u⃗] plus the [setR]-sum of [w⃗],
      directly by [big_split_ord].

    - **[Spos_cat]/[Sneg_cat]** (the **[SD_concat]** identity at the level of
      the [Spos]/[Sneg] sums): reindexing [Sε f (n+m)(u⃗++w⃗) XB] over [catset]
      and splitting by parity ([catset_Ppos]/[catset_Pneg], [bigID] on
      [J∈Ppos m], [pair_big]) writes it as the two parity-classified blocks
      [Σ_{J∈Ppos m} Sε' f n u⃗ (XB+Σ_J w⃗) + Σ_{J∈Pneg m} Sε'' f n u⃗ (XB+Σ_J
      w⃗)] (same parity for [Spos], opposite for [Sneg]).  This is the
      discrete "higher difference = iterated difference" content: the inner
      [u⃗]-sums [Sε f n u⃗] reappear blockwise.

    - **[totmono_SD_cat]** (the **[SD_concat]** inequality, the engine of
      Lemma 7.20-[Δf]): for [f] totally monotonic and [‖XB + Σu⃗ + Σw⃗‖ ≤ 1],
      the inner difference [SD f u⃗ : B → C] satisfies the (7.1) inequality
      at the outer [m]-config: [Sneg (SD f u⃗) m w⃗ XB ≤p Spos (SD f u⃗) m w⃗
      XB].  Each inner [Spos f n u⃗ = Sneg f n u⃗ + SD f u⃗] ([SD_E]
      blockwise), so [Spos_cat]/[Sneg_cat] give the four parity blocks
      [Spp = Snp + Pp], [Spn = Snn + Pn]; [f]'s own total monotonicity at
      the concatenated [(n+m)]-config ([Sneg_le_Spos]) reads
      [Snp + Spn ≤p Spp + Snn], and cancelling the shared [Snp + Snn]
      ([precone_le_addlI]) leaves [Pn ≤p Pp], i.e. the claim.  *No global
      total monotonicity of the inner [SD f u⃗] is ever needed — the
      composition is reduced directly to [f]'s totmono one arity up.*

    - **[totmono_Delta]** (**Lemma 7.20, [Δf] clause**): [Δf(u⃗) : B_u⃗ → C]
      is totally monotonic for [f] totally monotonic.  Unfolding
      [is_totmono (Δf(u⃗))] over [B_u⃗], each summand [Δf(u⃗)(y + Σ_J W⃗)]
      reads on the [B]-side as [SD f u⃗ (lc_val y + Σ_J (lc_val∘W⃗))]
      ([SD_Delta] + [lc_val_big]), so [Sε(Δf(u⃗)) = Sε (SD f u⃗) m
      (lc_val∘W⃗) (lc_val y)]; the bound [Sneg ≤p Spos] is then exactly
      [totmono_SD_cat] (the [SD_concat] engine), the centre/direction ball
      bound supplied by [lc_step1] on the local cone.  **No nested-cone
      cast, no ω-continuity, no [Sinc] recursion** — the [SD_concat]
      identity reduces the higher difference's total monotonicity directly
      to [f]'s, one arity up.

    Design lesson — why the *forward* direction of B-side Theorem 7.19 is
    not pursued:

    - **Forward direction [totmono_Sinc]** ([is_totmono f ⇒ ∀p, Sinc p f]).
      *Genuinely false on bare [B] as stated.*  [Sinc (p.+1) f] demands
      [Sinc p (dB f u)] on the *plain* unit ball of bare [B]; but [dB f u]'s
      own total monotonicity only holds on the *shifted* ball ([totmono_dB]),
      and on bare [B] a plain-ball point need not be shifted-admissible
      ([‖x + v‖ ≤ 1] does not give [‖x + v + u‖ ≤ 1]).  On the local cone
      [B_u] the gauge norm makes the two balls coincide ([lc_step1]); on bare
      [B] they differ, so the [dB]-clause of [Sinc] can fail.  This is the
      reason the *converse* [Sinc_totmono] is the useful direction (and is
      delivered): [Sinc] is an *input* hypothesis there, supplied by
      [Sinc_dB] with its own bounds, never re-derived from [is_totmono].
      [totmono_Delta] (Lemma 7.20, [Δf] clause) avoids this wall entirely
      by going through the [SD_concat] identity rather than [Sinc].

    Lemma 7.26 (the Faà-di-Bruno-style main lemma) — the two cornerstones:

    - **[kfun]** / **[kfun_increasing]** (Lemma 7.25 for the composite, the
      [p = 0] base case): the B-side composite difference
      [kfun g f h⃗ x = SD g (fun i ↦ hᵢ x) (f x)] (i.e.
      [Δg(h₁(x),…,hₙ(x))(f(x))]) is increasing on [B_B], read off the joint
      centre/direction monotonicity [SD_mono_full] of [g] ([f], [hᵢ]
      increasing make the centre [f x] and every direction [hᵢ x] grow;
      [g]'s difference is jointly increasing), the [n = 0] case being [g]
      increasing.  The boundedness hypothesis [Hbd] ([∀x∈B_B, f(x)+Σhᵢ(x)
      ∈ B_C]) supplies the unit-ball norm bound.

    - **[dB_kfun]** (the diagonal expansion, the [p ⤳ p+1] engine, txt
      3724): the single-step difference of the composite splits as the
      paper's [n+1]-term sum [dB k u x = SD g (Δf(u)(x) :: (hᵢ(x+u))ᵢ)(f x)
      + Σₖ SD g (hybₖ(h(x),Δh(u)(x)))(f x + h_k x)], the would-be first
      Lemma-7.23 term [SD g (h(x))(f x) = k x] annihilated by the
      subtraction ([dB_E] + [precone_cancel]).  This is exactly [SD_723]
      (Lemma 7.23 full telescope) on the shifted family [h(x+u) = h(x) +
      Δh(u)(x)] at the shifted centre [f(x+u) = f(x) + Δf(u)(x)].

    Composition theorem (Thm 7.30) — the non-totmono halves:

    - **[scott_comp]** (ω-continuity composes) / **[bounded_comp]**
      (boundedness composes) / **[meas_path_comp]** (path-preservation
      composes): for [f, g] stable-and-measurable of norm [≤ 1], all of
      [g ∘ f]'s stability/measurability fields *except total monotonicity*
      are direct (ω-continuity via [cone_sup_at_ball]/[cone_sup_at_indep],
      [f]'s [≤ 1]-image keeping the chain/path in [B_C]).

    Lemma 7.26 and Theorem 7.30 (closure under composition):

    - **[ninc_kfun]** (Lemma 7.26, the generic-source [p]-induction): for
      *every* source cone, arity, and admissible data, [kfun g f h⃗] is
      [p]-increasing.  The bare-[B] wall (the forward bridge
      [is_totmono ⇒ ∀p, Sinc p] is false on bare [B]) is sidestepped by
      running the induction on the *local-cone* predicate [is_n_increasing]
      (which recurses into [B_u]) and *quantifying it over all source
      cones*: the [p.+1] step's goal at source [B_u] is discharged by the
      inductive hypothesis *instantiated at source [B_u]* — "the same
      theorem at the smaller cone" — so the explicit nested-cone transport
      [(B_{u₀})_{u⃗} = B_{u₀,u⃗}] never appears.  The [dB_kfun] summands
      become [kfun]s at source [B_u] whose directions are totally monotonic
      ([totmono_dirH]/[totmono_dirK], via [totmono_dB_lc]/[totmono_shift_le])
      and satisfy the codomain bound ([cod_head]/[cod_hyb]); the [\sumP] is
      [p]-increasing ([ninc_add]/[ninc_bigP]), transferred to [Δk(u)] by the
      ball-locality congruence [ninc_congr].

    - **[totmono_comp]/[stable_comp]/[meas_stable_comp]** (Theorem 7.30):
      [g ∘ f] is totally monotonic / stable / stable-and-measurable for
      [f, g] stable(-and-measurable) with [f] mapping the unit ball into the
      unit ball.  Total monotonicity is [ninc_kfun] at [n = 0]
      ([SD g () (f x) = g (f x)]) + the closed-ball converse
      [is_n_increasing_totmono] (ω-continuity from [scott_comp]); the other
      fields are [bounded_comp]/[scott_comp]/[meas_path_comp].

    - The [is_n_increasing] *sum engine* ([dB_add_at]/[dB_congr]/[dB_zero],
      [ninc_congr]/[ninc_zero]/[ninc_add]/[ninc_bigP]) is the
      [is_n_increasing] analogue of [totmono_bigP]/[stable_bigP].  The bare
      [Sinc] predicate cannot be summed — its [dB] recursion stays on [B],
      where [dB] additivity ([dB_add_at]) fails off the ball — so the
      summation is realised on the local-cone [is_n_increasing], whose
      gauge norm makes the plain and shifted balls of [B_u] coincide.

    The content of **Lemma 7.27** is delivered in
    [stable/scones_ccc.v] in the form actually consumed by the CCC: the
    total monotonicity of the evaluation map [Ev : (B ⇒ₛ C) × B → C]
    ([ev_totmono]). *)
