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

Require Import Icones.prelude.classical_extra.
Require Import Icones.prelude.nonneg_extra.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.omega_general.
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

    Deferred (with the precise wall):

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

    - **[totmono_Delta]** (Lemma 7.20, [Δf] clause): [Δf(u⃗) : B_u⃗ → C]
      totally monotonic for stable [f].  Now *one milestone away*:
      [Sinc_totmono] applies verbatim at the source cone [B := lc_coneType
      Hs] once we exhibit [∀p, Sinc p (Δf(u⃗))] on that local cone
      ([scott_Delta] already supplies the ω-continuity half).  The [Sinc]
      recursion of [Δf(u⃗)] on [B_u⃗] descends through [dB (Δf u⃗) u'], and
      by [SD_Delta] + the [SD]-cons recurrence each such difference is a
      *higher* bare-[B] difference [SD f (u' :: u⃗) ∘ lc_val] — exactly the
      iterated-[SD] / Lemma 7.23-general telescope below.  So [totmono_Delta]
      is gated only on the iterated-difference machinery (next milestone),
      not on any gauge bridge: [SD_consdB] is its first brick.  No
      [Admitted] is left.

    - **Lemma 7.23, general arity** (the full [Δf(u⃗+v⃗)(x+u)] telescope):
      [findiff.v] delivers the [n = 1] base [SD_723_1].  The general [n]
      case is the diagonal split
      [SD (u⃗+v⃗)(xb) = SD u⃗(xb) + Σⱼ SD(hybⱼ)(xb+uⱼ)] with [hybⱼ] the
      hybrid family [(u₁,…,u_{j-1}, vⱼ, u_{j+1}+v_{j+1},…)].  The natural
      induction (peel index 0 by [SD_add], recurse on the tail with a
      *frozen head* [a]) needs the frozen-head split
      [SD (a :: u⃗+v⃗)(xc) = SD (a :: u⃗)(xc) + Σₖ SD (a :: hybₖ)(xc + uₖ)],
      whose recursive step splits the tail at an *interior* position — the
      head-only [SD_add] applied after moving position [k] to the head by
      [SD_perm], with the attendant ordinal cast [m + k.+1 = m.+1 + k] and
      ['I_n] prefix-concatenation ([lshift]/[rshift]/[split]).  Crucially
      the interior term keeps the *single-direction* centre shift [xc + uₖ]
      (not the accumulated [xc + u₀ + … + uₖ]), so the frozen-head [a] and
      [xc] cannot be folded into the head-peel — the interior-position
      engine is genuinely required.  The [SD] engines ([SD_cons], [SD_add],
      [SD_perm], [SnB]) are all in place; only this prefix/reindex
      machinery is missing.  Independent of the [Sinc] equivalence;
      deferred per the strict priority order (the equivalence wall comes
      first). *)
