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
      difference, which the paper derives "from Theorem 7.19").

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
