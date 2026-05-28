(**md**************************************************************)
(** * The local cone — Paper §7.1

    Given an integrable (here: [coneType]) cone [B] and a point [x] in
    the closed unit ball [B_B], the *local cone* [B_x] is the precone of
    "admissible directions"

      P = { u : B | ∃ ε > 0, x + ε ·: u ∈ B_B } .

    Following the paper, [P] inherits the algebraic structure of [B]
    (zero, addition, scalar multiplication) and carries the *gauge norm*

      N(u) = (sup { λ > 0 | x + λ ·: u ∈ B_B })⁻¹ .

    Paper reference: §7.1 (pages 1:55–1:56), Lemma 7.1, Lemma 7.2,
    Example 7.3.

    Coverage in this file.
    - The carrier [local_cone x Hx] as the sigma type [{ u : B | localP }]
      over the admissibility predicate, with proof-irrelevant equality
      [lc_eq] derived from [Prop_irrelevance].
    - The algebraic operations [lc_zero], [lc_add], [lc_scale] and the
      full [isPrecone] instance — i.e. the algebraic half of Lemma 7.1.
    - The cone order on [B_x] coincides with that of [B]
      ([lc_leE]) — the observation used in the paper's (Normc) proof.
    - The gauge set [gauge_set] / its supremum [gauge_sup] and the gauge
      norm [lc_norm], with the reach lemmas of Lemma 7.2
      ([gauge_sup_reach], [gauge_sup_gt_out]), and the full [isCone]
      instance (Lemma 7.1).
    - The measurable / integrable structure of [B_x] (Example 7.3): the
      renormalized pullback test family [lc_mcone_M] with its (Mscomp),
      (Mssep), (Msnorm) closure, the [isMCone] instance, and — for
      [B : iconeType] — the [isICone] instance (integral as in [B]).

    Design notes.
    - The algebraic / cone development ([isPrecone], [isCone], Lemmas
      7.1, 7.2) needs only that [B] is a [coneType R] and [‖x‖_B ≤ 1].
      The measurability / integrability layer ([isMCone], [isICone],
      "computed as in [B]") needs [B : mconeType] / [iconeType] *and* the
      *strict* interior bound [‖x‖_B < 1] (Example 7.3): see the closing
      comment.  We therefore strengthen the section hypothesis [Hx] to
      [cnorm x < 1] throughout; the [≤ 1] facts are recovered via
      [ltW Hx] (named [Hxle]) so nothing in the cone development changes.
    - Membership is a [Prop]-existential; we use [Prop_irrelevance] so
      that two carrier elements are equal as soon as their [B]-components
      are.  This is what lets the algebraic axioms reduce to the
      corresponding facts in [B].
    - All four HB instances are *registered*: [isPrecone], [isCone],
      [isMCone] (test family the renormalized pullbacks), and [isICone]
      (integral inherited from [B] via [lc_val]).  So [B_x] is a full
      [iconeType Ar] at any strict interior point.  See the closing
      comment for the construction and exactly which lemmas discharge
      each axiom.
*)
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference archimedean.
From HB Require Import structures.

Require Import Icones.prelude.classical_extra.
Require Import Icones.prelude.nonneg_extra.
Require Import Icones.prelude.omegacpo.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.basic_lemmas.
From mathcomp.reals Require Import constructive_ereal.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import ereal measure.
From mathcomp.analysis Require Import lebesgue_integral_definition.
From mathcomp.analysis Require Import lebesgue_integral_nonneg.
From mathcomp.analysis Require Import lebesgue_integral_monotone_convergence.
From mathcomp.analysis Require Import lebesgue_integrable.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.icones.pettis.
Require Import Icones.icones.icone_integral.
Require Import Icones.icones.icone.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Import archimedean.Num.Theory.

Local Open Scope ring_scope.

(** ** A monotone running-maximum of a sequence of admissible steps

    To attain the gauge supremum (Lemma 7.2, "reach" half) and to prove
    (Normc) we approximate the supremum from below by an *increasing*
    sequence of admissible scalars.  [rmax e] turns an arbitrary
    sequence [e] of nonnegative reals into a monotone one, pointwise
    above [e] and only taking values among the [e k]'s — so it preserves
    any "downward-closed under value" property such as admissibility. *)

Section RunningMax.
Variable R : realType.
Variable e : nat -> {nonneg R}.

Fixpoint rmax (n : nat) : {nonneg R} :=
  match n with
  | 0 => e 0
  | m.+1 => if (rmax m)%:num <= (e m.+1)%:num then e m.+1 else rmax m
  end.

Lemma rmax_ge_e n : (e n)%:num <= (rmax n)%:num.
Proof.
case: n => [|m] //=; case: ifPn => [_|]; first by [].
by rewrite -ltNge => /ltW.
Qed.

Lemma rmax_mono n : (rmax n)%:num <= (rmax n.+1)%:num.
Proof. by rewrite /=; case: ifPn => // _. Qed.

Lemma rmax_is_e n : exists k, rmax n = e k.
Proof.
elim: n => [|m [k IH]]; first by exists 0.
by rewrite /=; case: ifPn => _; [exists m.+1 | exists k].
Qed.

End RunningMax.

(** ** The carrier of the local cone *)

Section LocalConeCarrier.
Variable R : realType.
Variable B : coneType R.
Variable x : B.
(** Paper §7.1, Example 7.3: the local cone is the differentiation of
    [B] at an *interior* point of the unit ball.  We take [‖x‖_B < 1]
    (strict): this is what closes the simplified [mcone_M_norm] field of
    [mcone.v] for the pullback test family (see [LocalMCone] below).  The
    non-strict facts of Lemmas 7.1/7.2 only ever consume [ltW Hx], so the
    algebraic / norm development below is unchanged in meaning. *)
Hypothesis Hx : cone_norm x < 1.
Let Hxle : cone_norm x <= 1 := ltW Hx.

(** Paper §7.1: a direction [u] is *admissible* at [x] when [x] can be
    pushed a positive amount along [u] while staying in the unit ball. *)
Definition localP (u : B) : Prop :=
  exists eps : {nonneg R}, 0 < eps%:num /\
    cone_norm (precone_add x (precone_scale eps u)) <= 1.

(** Paper §7.1: the carrier [P] of the local cone of [B] at [x]. *)
Definition local_cone : Type := { u : B | localP u }.

(** Coercion / projection helpers. *)
Definition lc_val (u : local_cone) : B := sval u.

(** Two elements of [local_cone] are equal once their [B]-values are:
    membership is a [Prop], discharged by [Prop_irrelevance]. *)
Lemma lc_eq (u v : local_cone) : lc_val u = lc_val v -> u = v.
Proof.
case: u => u Hu; case: v => v Hv /= euv.
by apply: (eq_exist Hu Hv euv); exact: Prop_irrelevance.
Qed.

(** ** Stability of admissibility under the operations of [B] *)

(** Decreasing the step keeps us in the ball: this is the workhorse for
    finding a common step shared by two admissible directions. *)
Lemma localP_le_eps (u : B) (e1 e2 : {nonneg R}) :
  e1%:num <= e2%:num ->
  cone_norm (precone_add x (precone_scale e2 u)) <= 1 ->
  cone_norm (precone_add x (precone_scale e1 u)) <= 1.
Proof.
move=> le12 Hin; apply: le_trans _ Hin; apply: cone_normp.
have d_ge0 : 0 <= e2%:num - e1%:num by rewrite subr_ge0.
exists (precone_scale (NngNum d_ge0) u).
rewrite -precone_addA; congr precone_add.
rewrite -precone_scale_DAl; congr precone_scale.
by apply: val_inj => /=; rewrite addrC subrK.
Qed.

(** Paper §7.1: [0] is admissible (it is the [0] of [B], and [x ∈ B_B]). *)
Lemma localP0 : localP precone_zero.
Proof.
exists 1%:nng; split; first by rewrite /= ltr01.
by rewrite precone_scale_0r precone_addr0.
Qed.

(** Paper §7.1: a non-negative scaling of an admissible direction is
    admissible.  For [r = 0] this is [localP0]; otherwise we use the step
    [ε/r]. *)
Lemma localP_scale (r : {nonneg R}) (u : B) :
  localP u -> localP (precone_scale r u).
Proof.
have [->|rpos] := eqVneq r 0%:nng.
  by rewrite precone_scale_0l => _; exact: localP0.
move=> [eps [eps_pos Hin]].
have rnum_pos : 0 < r%:num.
  rewrite lt0r nngnum_ge0 andbT; apply/eqP => r0.
  by move/eqP: rpos; apply; apply: val_inj.
have rinv_ge0 : 0 <= eps%:num / r%:num.
  by rewrite divr_ge0// nngnum_ge0.
exists (NngNum rinv_ge0); split.
  by rewrite /= divr_gt0.
rewrite -precone_scale_A.
have -> : ((NngNum rinv_ge0)%:num * r%:num)%:nng = eps.
  by apply: val_inj => /=; rewrite divfK ?gt_eqF.
exact: Hin.
Qed.

(** Paper §7.1: the sum of two admissible directions is admissible.
    With a common step [ε] (the smaller of the two), the convexity
    identity
      [x + (ε/2)·:(u₁ + u₂) = ½·:(x + ε·:u₁) + ½·:(x + ε·:u₂)]
    bounds the norm by [½ + ½ = 1]. *)
Lemma localP_add (u1 u2 : B) :
  localP u1 -> localP u2 -> localP (precone_add u1 u2).
Proof.
move=> [e1 [e1_pos H1]] [e2 [e2_pos H2]].
(* common step [e := min e1 e2] *)
pose e : R := Num.min e1%:num e2%:num.
have e_ge0 : 0 <= e by rewrite le_min !nngnum_ge0.
have e_pos : 0 < e by rewrite lt_min e1_pos e2_pos.
have le_e1 : e <= e1%:num by rewrite ge_min lexx.
have le_e2 : e <= e2%:num by rewrite ge_min lexx orbT.
have H1' := localP_le_eps (e1 := NngNum e_ge0) le_e1 H1.
have H2' := localP_le_eps (e1 := NngNum e_ge0) le_e2 H2.
(* half of the common step *)
have half_ge0 : 0 <= 2^-1 * e by rewrite mulr_ge0// invr_ge0 ler0n.
have half_pos : 0 < 2^-1 * e by rewrite mulr_gt0// invr_gt0 ltr0n.
exists (NngNum half_ge0); split; first by [].
(* the convexity identity *)
set xe1 := precone_add x (precone_scale (NngNum e_ge0) u1).
set xe2 := precone_add x (precone_scale (NngNum e_ge0) u2).
have half2_ge0 : (0 : R) <= 2^-1 by rewrite invr_ge0 ler0n.
pose h : {nonneg R} := NngNum half2_ge0.
have ACA : forall a b c d : B,
    precone_add (precone_add a b) (precone_add c d) =
    precone_add (precone_add a c) (precone_add b d).
  move=> a b c d; rewrite -!precone_addA; congr precone_add.
  by rewrite (precone_addC b) -precone_addA (precone_addC d).
have key : precone_add x (precone_scale (NngNum half_ge0)
              (precone_add u1 u2)) =
           precone_add (precone_scale h xe1) (precone_scale h xe2).
  rewrite /xe1 /xe2 !precone_scale_DAr -!precone_scale_A.
  have eqs : forall u : B,
      precone_scale (widen_itv (h%:num * (NngNum e_ge0)%:num)%:itv) u =
      precone_scale (NngNum half_ge0) u.
    by move=> u; congr precone_scale; apply: val_inj.
  rewrite !eqs ACA.
  have hxhx : precone_add (precone_scale h x) (precone_scale h x) = x.
    rewrite -precone_scale_DAl.
    have -> : (h%:num + h%:num)%:nng = 1%:nng :> {nonneg R}.
      by apply: val_inj => /=; rewrite -mulr2n -[_ *+ 2]mulr_natr mulVf.
    by rewrite precone_scale_1.
  by rewrite hxhx.
rewrite key.
apply: le_trans (cone_normt _ _) _.
rewrite !cone_normh /=.
rewrite -[X in _ <= X](_ : 2^-1 + 2^-1 = 1 :> R); last first.
  by rewrite -mulr2n -[_ *+ 2]mulr_natr mulVf.
by rewrite lerD// ler_piMr ?invr_ge0 ?ler0n -/xe1 -/xe2 //.
Qed.

(** ** Precone structure of the local cone — Lemma 7.1 (algebraic part) *)

(** The operations of [B_x] are the operations of [B], packaged with the
    admissibility witnesses proved above. *)
Definition lc_zero : local_cone := exist localP precone_zero localP0.

Definition lc_add (u v : local_cone) : local_cone :=
  exist localP (precone_add (sval u) (sval v))
    (localP_add (proj2_sig u) (proj2_sig v)).

Definition lc_scale (r : {nonneg R}) (u : local_cone) : local_cone :=
  exist localP (precone_scale r (sval u)) (localP_scale r (proj2_sig u)).

(** [lc_val] is a homomorphism: it commutes with the three operations.
    These are definitional but stated as named rewrite rules. *)
Lemma lc_val0 : lc_val lc_zero = precone_zero. Proof. by []. Qed.
Lemma lc_valD u v : lc_val (lc_add u v) = precone_add (lc_val u) (lc_val v).
Proof. by []. Qed.
Lemma lc_valZ r u : lc_val (lc_scale r u) = precone_scale r (lc_val u).
Proof. by []. Qed.

(** All [isPrecone] axioms reduce to the corresponding facts in [B] via
    [lc_eq] (equality on [B]-values), since [lc_val] is a homomorphism. *)

Lemma lc_addA : associative lc_add.
Proof. by move=> u v w; apply: lc_eq; rewrite !lc_valD precone_addA. Qed.

Lemma lc_addC : commutative lc_add.
Proof. by move=> u v; apply: lc_eq; rewrite !lc_valD precone_addC. Qed.

Lemma lc_add0 : left_id lc_zero lc_add.
Proof. by move=> u; apply: lc_eq; rewrite lc_valD lc_val0 precone_add0. Qed.

Lemma lc_scale_DAr (r : {nonneg R}) (u v : local_cone) :
  lc_scale r (lc_add u v) = lc_add (lc_scale r u) (lc_scale r v).
Proof.
by apply: lc_eq; rewrite !(lc_valD, lc_valZ) precone_scale_DAr.
Qed.

Lemma lc_scale_DAl (r s : {nonneg R}) (u : local_cone) :
  lc_scale (r%:num + s%:num)%:nng u = lc_add (lc_scale r u) (lc_scale s u).
Proof.
by apply: lc_eq; rewrite lc_valD !lc_valZ precone_scale_DAl.
Qed.

Lemma lc_scale_A (r s : {nonneg R}) (u : local_cone) :
  lc_scale (r%:num * s%:num)%:nng u = lc_scale r (lc_scale s u).
Proof. by apply: lc_eq; rewrite !lc_valZ precone_scale_A. Qed.

Lemma lc_scale_1 (u : local_cone) : lc_scale 1%:nng u = u.
Proof. by apply: lc_eq; rewrite lc_valZ precone_scale_1. Qed.

Lemma lc_scale_0r (r : {nonneg R}) : lc_scale r lc_zero = lc_zero.
Proof. by apply: lc_eq; rewrite lc_valZ lc_val0 precone_scale_0r. Qed.

Lemma lc_scale_0l (u : local_cone) : lc_scale 0%:nng u = lc_zero.
Proof. by apply: lc_eq; rewrite lc_valZ lc_val0 precone_scale_0l. Qed.

Lemma lc_cancel (u v w : local_cone) :
  lc_add u v = lc_add u w -> v = w.
Proof.
move=> /(congr1 lc_val); rewrite !lc_valD => /precone_cancel euw.
exact: lc_eq.
Qed.

Lemma lc_pos (u v : local_cone) :
  lc_add u v = lc_zero -> u = lc_zero /\ v = lc_zero.
Proof.
move=> /(congr1 lc_val); rewrite lc_valD lc_val0 => /precone_pos[Hu Hv].
by split; apply: lc_eq; rewrite lc_val0.
Qed.

(** Paper Lemma 7.1 (algebraic half): [B_x] is a precone whose [0] and
    operations are inherited from [B]. *)
HB.instance Definition _ := @isPrecone.Build R local_cone
  lc_zero lc_add lc_scale lc_addA lc_addC lc_add0
  lc_scale_DAr lc_scale_DAl lc_scale_A lc_scale_1
  lc_scale_0r lc_scale_0l lc_cancel lc_pos.

(** ** The cone order of [B_x] coincides with that of [B]

    Paper §7.1: "for [u, v ∈ P], we have [u ≤_P v] iff [u ≤_B v]".  This
    is the key observation used in the (Normc) proof. *)

(** A direction below an admissible one is admissible (same step). *)
Lemma localP_le (u v : B) :
  precone_le u v -> localP v -> localP u.
Proof.
move=> [d ->] [eps [eps_pos Hin]]; exists eps; split=> //.
apply: le_trans _ Hin; apply: cone_normp.
exists (precone_scale eps d); rewrite precone_scale_DAr precone_addA //.
Qed.

Lemma lc_leE (u v : local_cone) :
  precone_le u v <-> precone_le (lc_val u) (lc_val v).
Proof.
split=> [[w ->]|[d Hd]]; first by rewrite lc_valD; exists (lc_val w).
have Hadm : localP d.
  by apply: (localP_le (v := lc_val v)); [exists (lc_val u);
     rewrite precone_addC | exact: proj2_sig v].
by exists (exist localP d Hadm); apply: lc_eq; rewrite lc_valD.
Qed.

End LocalConeCarrier.

(** ** The gauge norm of the local cone — Paper §7.1 *)

Section GaugeNorm.
Variable R : realType.
Variable B : coneType R.
Variable x : B.
Hypothesis Hx : cone_norm x < 1.
Let Hxle : cone_norm x <= 1 := ltW Hx.

Local Open Scope classical_set_scope.

Local Notation P := (local_cone x).

(** The set of admissible *steps* (as plain reals) along [u]: those
    [λ ≥ 0] with [x + λ ·: u ∈ B_B].  Paper §7.1: the gauge is the
    inverse of its supremum. *)
Definition gauge_set (u : P) : set R :=
  [set s%:num | s in
    [set s : {nonneg R} | cone_norm (precone_add x (precone_scale s
       (lc_val u))) <= 1]].

(** [0] is always an admissible step, so the gauge set is non-empty. *)
Lemma gauge_set0 (u : P) : gauge_set u 0.
Proof.
exists 0%:nng => //=.
by rewrite precone_scale_0l precone_addr0.
Qed.

Lemma gauge_set_neq0 (u : P) : gauge_set u !=set0.
Proof. by exists 0; exact: gauge_set0. Qed.

(** For [u ≠ 0], every admissible step is bounded by [‖u‖_B⁻¹]: indeed
    [s ·: u ≤_B x + s ·: u], hence [s · ‖u‖_B ≤ 1]. *)
Lemma gauge_set_ub (u : P) :
  lc_val u <> precone_zero ->
  has_ubound (gauge_set u).
Proof.
move=> u_neq0.
have nu_pos : 0 < cone_norm (lc_val u).
  rewrite lt_neqAle cone_norm_ge0 andbT eq_sym.
  by apply/eqP => /cone_normz.
exists (cone_norm (lc_val u))^-1 => r [s /= Hin <-].
rewrite -(ler_pM2r nu_pos) mulVf ?gt_eqF//.
have Hle : precone_le (precone_scale s (lc_val u))
                      (precone_add x (precone_scale s (lc_val u))).
  by exists x; rewrite precone_addC.
apply: le_trans _ Hin.
by rewrite -cone_normh; exact: cone_normp.
Qed.

(** The supremum of the gauge set (the "reach" of [u] from [x]). *)
Definition gauge_sup (u : P) : R := sup (gauge_set u).

Lemma gauge_sup_ge0 (u : P) : 0 <= gauge_sup u.
Proof.
rewrite /gauge_sup.
have [u0|u0] := pselect (lc_val u = precone_zero).
  (* [u = 0]: the gauge set is unbounded (all steps admissible), so
     [sup] is [0] by [sup_out]. *)
  have noub : ~ has_ubound (gauge_set u).
    case=> M HM.
    have HM1 : forall s : {nonneg R}, s%:num <= M.
      move=> s; apply: HM; exists s => //=.
      by rewrite u0 precone_scale_0r precone_addr0.
    have M_ge0 : (0:R) <= M by apply: le_trans (HM1 0%:nng); rewrite nngnum0.
    have d_ge0 : (0:R) <= M + 1 by rewrite addr_ge0// ler01.
    by have := HM1 (NngNum d_ge0); rewrite leNgt => /negP; apply;
       rewrite ltrDl ltr01.
  rewrite sup_out; first by [].
  by case.
have Hsup : has_sup (gauge_set u).
  by split; [exact: gauge_set_neq0 | exact: gauge_set_ub].
by apply: sup_upper_bound => //; exact: gauge_set0.
Qed.

(** For [u ≠ 0] the gauge set has a (positive) supremum: the
    admissibility witness provides a strictly-positive admissible step. *)
Lemma has_sup_gauge (u : P) :
  lc_val u <> precone_zero -> has_sup (gauge_set u).
Proof.
by move=> u0; split; [exact: gauge_set_neq0 | exact: gauge_set_ub].
Qed.

Lemma gauge_sup_gt0 (u : P) :
  lc_val u <> precone_zero -> 0 < gauge_sup u.
Proof.
move=> u0; have [eps [eps_pos Hin]] := proj2_sig u.
apply: lt_le_trans eps_pos _.
rewrite /gauge_sup; apply: sup_upper_bound; first exact: has_sup_gauge.
by exists eps.
Qed.

(** Paper §7.1: the *gauge norm* of [B_x], [N(u) = (sup gauge_set u)⁻¹]. *)
Definition lc_norm (u : P) : R := (gauge_sup u)^-1.

(** Paper Lemma 7.2 (the "out" half): for [u ≠ 0], any step strictly
    beyond the reach [sup gauge_set u] leaves the unit ball.  (The
    restriction to [u ≠ 0] matches the paper's [u ∈ B_x \ {0}].) *)
Lemma gauge_sup_gt_out (u : P) (s : {nonneg R}) :
  lc_val u <> precone_zero ->
  gauge_sup u < s%:num ->
  ~ cone_norm (precone_add x (precone_scale s (lc_val u))) <= 1.
Proof.
move=> u0 Hgt Hin.
have : s%:num <= gauge_sup u.
  rewrite /gauge_sup; apply: sup_upper_bound; first exact: has_sup_gauge.
  by exists s.
by rewrite leNgt Hgt.
Qed.

(** The gauge norm is non-negative. *)
Lemma lc_norm_ge0 (u : P) : 0 <= lc_norm u.
Proof. by rewrite /lc_norm invr_ge0 gauge_sup_ge0. Qed.

(** (Normz) for the gauge norm: only the [0] direction has gauge [0].
    Indeed [lc_norm u = (gauge_sup u)⁻¹ = 0] forces [gauge_sup u = 0],
    which by [gauge_sup_gt0] can only happen for [u = 0]. *)
Lemma lc_normz (u : P) : lc_norm u = 0 -> lc_val u = precone_zero.
Proof.
rewrite /lc_norm => /eqP; rewrite invr_eq0 => /eqP Hsup0.
apply: contrapT => u0.
by move: (gauge_sup_gt0 u0); rewrite Hsup0 ltxx.
Qed.

(** (Normh) at the zero scalar, in [B_x]-norm terms: [lc_norm 0 = 0]. *)
Lemma lc_norm0 (u : P) : lc_val u = precone_zero -> lc_norm u = 0.
Proof.
move=> u0; rewrite /lc_norm /gauge_sup sup_out ?invr0//.
case=> _ [M HM].
have HM1 : forall s : {nonneg R}, s%:num <= M.
  move=> s; apply: HM; exists s => //=.
  by rewrite u0 precone_scale_0r precone_addr0.
have M_ge0 : (0:R) <= M by apply: le_trans (HM1 0%:nng); rewrite nngnum0.
have d_ge0 : (0:R) <= M + 1 by rewrite addr_ge0// ler01.
have := HM1 (NngNum d_ge0); rewrite leNgt => /negP; apply.
by rewrite ltrDl ltr01.
Qed.

(** ** Paper Lemma 7.2 (the "reach" half): the gauge supremum is attained

    For [u ≠ 0], the step [gauge_sup u] is itself admissible:
    [x + (gauge_sup u) ·: u ∈ B_B].  This is the point where the paper
    invokes ω-closedness of [B_B].  We approximate [gauge_sup u] from
    below by an increasing admissible chain [a_n] (built with [rmax] from
    the [sup_adherent] witnesses), form the unit-ball supremum
    [s = cone_sup_ball (n ↦ x + a_n ·: u)] (norm ≤ 1), and show
    [x + (gauge_sup u) ·: u = s]: the gap [t] (with
    [x + L ·: u = s + t]) satisfies [‖t‖ ≤ (L - a_n) ‖u‖ → 0], hence
    [t = 0] by (Normz).  This is the "scalar limit commutes with
    [cone_sup_ball]" fact, in the only form actually needed. *)
Lemma gauge_sup_reach (u : P) (Hu0 : lc_val u <> precone_zero) :
  cone_norm (precone_add x
     (precone_scale (NngNum (gauge_sup_ge0 u)) (lc_val u))) <= 1.
Proof.
have Hsup : has_sup (gauge_set u) := has_sup_gauge Hu0.
set L := gauge_sup u.
have L_ge0 : 0 <= L := gauge_sup_ge0 u.
set v := lc_val u.
have nv_pos : 0 < cone_norm v.
  rewrite lt_neqAle cone_norm_ge0 andbT eq_sym.
  by apply/eqP => /cone_normz.
have ade : forall n : nat,
    exists s : {nonneg R},
      cone_norm (precone_add x (precone_scale s v)) <= 1 /\
      L - n.+1%:R^-1 < s%:num.
  move=> n.
  have [d [s /= Hin sd] Hd] : exists2 d : R, gauge_set u d & L - n.+1%:R^-1 < d.
    by apply: sup_adherent => //; rewrite invr_gt0 ltr0n.
  by exists s; split=> //; rewrite sd.
pose e n := projT1 (cid (ade n)).
have eP : forall n,
    cone_norm (precone_add x (precone_scale (e n) v)) <= 1 /\
    L - n.+1%:R^-1 < (e n)%:num.
  by move=> n; exact: projT2 (cid (ade n)).
pose a n := rmax e n.
have a_adm : forall n, cone_norm (precone_add x (precone_scale (a n) v)) <= 1.
  move=> n; rewrite /a; have [k ->] := rmax_is_e e n; exact: (proj1 (eP k)).
have a_le_L : forall n, (a n)%:num <= L.
  move=> n; rewrite /L /gauge_sup; apply: sup_upper_bound => //.
  by exists (a n) => //; exact: a_adm.
have a_lb : forall n, L - n.+1%:R^-1 < (a n)%:num.
  move=> n; apply: lt_le_trans (proj2 (eP n)) _; exact: rmax_ge_e.
pose c n := precone_add x (precone_scale (a n) v).
have c_mono : forall n, precone_le (c n) (c n.+1).
  move=> n; rewrite /c; apply: precone_add_le_l.
  have da_ge0 : 0 <= (a n.+1)%:num - (a n)%:num.
    by rewrite subr_ge0; exact: rmax_mono.
  exists (precone_scale (NngNum da_ge0) v).
  rewrite -precone_scale_DAl; congr precone_scale.
  by apply: val_inj => /=; rewrite addrC subrK.
have c_ub1 : forall n, cone_norm (c n) <= 1 by exact: a_adm.
pose s := cone_sup_ball c c_mono c_ub1.
have s_norm : cone_norm s <= 1 := cone_sup_ball_norm c c_mono c_ub1.
pose xLv := precone_add x (precone_scale (NngNum L_ge0) v).
have c_le_xLv : forall n, precone_le (c n) xLv.
  move=> n; rewrite /c /xLv; apply: precone_add_le_l.
  have d_ge0 : 0 <= L - (a n)%:num by rewrite subr_ge0; exact: a_le_L.
  exists (precone_scale (NngNum d_ge0) v).
  rewrite -precone_scale_DAl; congr precone_scale.
  by apply: val_inj => /=; rewrite addrC subrK.
have s_le_xLv : precone_le s xLv.
  by apply: cone_sup_ball_lub => n; exact: c_le_xLv.
have [t Ht] := s_le_xLv.
have t_norm_bound : forall n,
    cone_norm t <= (L - (a n)%:num) * cone_norm v.
  move=> n.
  have d_ge0 : 0 <= L - (a n)%:num by rewrite subr_ge0; exact: a_le_L.
  have [w Hw] : precone_le (c n) s by exact: cone_sup_ball_ub.
  have E1 : xLv = precone_add (c n) (precone_scale (NngNum d_ge0) v).
    rewrite /xLv /c -precone_addA; congr precone_add.
    rewrite -precone_scale_DAl; congr precone_scale.
    by apply: val_inj => /=; rewrite addrC subrK.
  have E2 : xLv = precone_add (c n) (precone_add w t).
    by rewrite Ht Hw -precone_addA.
  have Heq : precone_scale (NngNum d_ge0) v = precone_add w t.
    by apply: (@precone_cancel _ _ (c n)); rewrite -E1 -E2.
  have t_le : precone_le t (precone_scale (NngNum d_ge0) v).
    by rewrite Heq precone_addC; exists w.
  have := cone_normp _ _ t_le.
  by rewrite cone_normh /=.
have t_norm_bound2 : forall n,
    cone_norm t <= n.+1%:R^-1 * cone_norm v.
  move=> n; apply: le_trans (t_norm_bound n) _.
  apply: ler_pM => //; first by rewrite subr_ge0; exact: a_le_L.
    by apply: ltW.
  rewrite lerBlDl addrC -lerBlDl; apply: ltW.
  by move: (a_lb n); rewrite ltrBlDl addrC -ltrBlDl.
have t_norm0 : cone_norm t <= 0.
  apply/unstable.ler_gtP => z z_pos.
  have nvz_pos : 0 < cone_norm v / z by rewrite divr_gt0.
  have HN := archi_boundP (ltW nvz_pos).
  set N := Num.bound (cone_norm v / z) in HN.
  apply: le_trans (t_norm_bound2 N) _.
  rewrite ler_pdivrMl ?ltr0n//.
  apply: ltW; apply: lt_le_trans (_ : N%:R * z <= N.+1%:R * z).
    by rewrite -ltr_pdivrMr.
  rewrite ler_wpM2r ?ltW//.
  by rewrite ltr_nat.
have t0 : t = precone_zero.
  by apply: cone_normz; apply/le_anti; rewrite t_norm0 cone_norm_ge0.
have xLv_eq : xLv = s by rewrite Ht t0 precone_addr0.
have -> : precone_scale (NngNum (gauge_sup_ge0 u)) (lc_val u) =
          precone_scale (NngNum L_ge0) v.
  by congr precone_scale; apply: val_inj.
by rewrite -/xLv xLv_eq.
Qed.

(** (Normh) helper: a positive rescaling divides the gauge supremum.
    [gauge_set (r ·: u)] is the [r⁻¹]-image of [gauge_set u]
    (substituting [s ↦ s·r] in the admissibility condition via
    [precone_scale_A]); taking [sup] gives the stated identity. *)
Lemma gauge_sup_scale (r : {nonneg R}) (u : P)
  (Hu0 : lc_val u <> precone_zero) (rpos : 0 < r%:num) :
  gauge_sup (lc_scale Hx r u) = r%:num^-1 * gauge_sup u.
Proof.
rewrite /gauge_sup.
have setE : gauge_set (lc_scale Hx r u) =
            [set r%:num^-1 * s | s in gauge_set u].
  apply/seteqP; split=> z.
  - move=> [w /= Hin <-].
    exists ((w%:num * r%:num)) => /=; last first.
      by rewrite mulrCA mulVf ?gt_eqF// mulr1.
    exists (NngNum (mulr_ge0 (nngnum_ge0 w) (nngnum_ge0 r))) => //=.
    rewrite (_ : NngNum (mulr_ge0 (nngnum_ge0 w) (nngnum_ge0 r))
                 = (w%:num * r%:num)%:nng); last by apply: val_inj.
    by rewrite precone_scale_A -/(lc_val u) in Hin *; exact: Hin.
  - move=> [s [w /= Hin sw] <-].
    have q_ge0 : 0 <= r%:num^-1 * w%:num by rewrite mulr_ge0// invr_ge0 ltW.
    exists (NngNum q_ge0) => /=; last by rewrite sw.
    rewrite -precone_scale_A.
    set sc := (X in cnorm (x + X *: _)%PC).
    have -> : sc = w.
      by rewrite /sc; apply: val_inj => /=; rewrite mulrAC mulVf ?gt_eqF// mul1r.
    exact: Hin.
have supZ : forall (k : R) (E : set R), 0 < k -> has_sup E ->
    sup [set k * s | s in E] = k * sup E.
  move=> k E k_pos hsE.
  have [E0 Eub] := hsE.
  have hsKE : has_sup [set k * s | s in E].
    split; first by case: E0 => e Ee; exists (k * e), e.
    case: Eub => M HM; exists (k * M) => z [s Es <-].
    by rewrite ler_pM2l//; apply: HM.
  apply/eqP; rewrite eq_le; apply/andP; split.
    apply: ge_sup; first by case: E0 => e Ee; exists (k * e), e.
    move=> z [s Es <-]; rewrite ler_pM2l//.
    by apply: sup_upper_bound.
  rewrite -ler_pdivlMl//.
  apply: ge_sup; first by case: E0 => e Ee; exists e.
  move=> s Es; rewrite ler_pdivlMl//.
  apply: (sup_upper_bound hsKE).
  by exists s => //; rewrite mulrC.
by rewrite setE supZ ?invr_gt0//; exact: has_sup_gauge Hu0.
Qed.

(** Paper Lemma 7.1, (Normh): the gauge norm is homogeneous,
    [lc_norm (r ·: u) = r · lc_norm u].  The interesting case [r > 0],
    [u ≠ 0] uses [gauge_sup_scale]; the others reduce to [lc_norm0]. *)
Lemma lc_normh (r : {nonneg R}) (u : P) :
  lc_norm (lc_scale Hx r u) = r%:num * lc_norm u.
Proof.
have [r0|rpos] := eqVneq r 0%:nng.
  rewrite r0 nngnum0 mul0r.
  apply: lc_norm0; rewrite lc_valZ.
  by rewrite (_ : 0%:nng = (0%:nng : {nonneg R})) // precone_scale_0l.
have rnum_pos : 0 < r%:num.
  rewrite lt_neqAle nngnum_ge0 andbT eq_sym.
  by apply: contra rpos => /eqP r0; apply/eqP/val_inj.
have [u0|un0] := pselect (lc_val u = precone_zero).
  rewrite (_ : lc_norm u = 0); last by apply: lc_norm0.
  rewrite mulr0; apply: lc_norm0; rewrite lc_valZ u0.
  by rewrite precone_scale_0r.
rewrite [in LHS]/lc_norm gauge_sup_scale// invfM invrK /lc_norm mulrC.
by congr (_ * _); rewrite invrK.
Qed.

(** Convexity estimate used for (Normt) (Paper Lemma 7.1):
    if [x + λᵢ ·: vᵢ ∈ B_B], then the harmonic-style step
    [μ = λ₁λ₂/(λ₁+λ₂)] is admissible for [v₁ + v₂], via the convex
    combination [μ ·: (v₁+v₂)] of the two admissible points with weights
    [λ₂/(λ₁+λ₂)] and [λ₁/(λ₁+λ₂)] summing to [1]. *)
Lemma gauge_convex (v1 v2 : B) (l1 l2 : {nonneg R})
  (l1pos : 0 < l1%:num) (l2pos : 0 < l2%:num)
  (Hin1 : cone_norm (precone_add x (precone_scale l1 v1)) <= 1)
  (Hin2 : cone_norm (precone_add x (precone_scale l2 v2)) <= 1) :
  forall (mu_ge0 : 0 <= l1%:num * l2%:num / (l1%:num + l2%:num)),
  cone_norm (precone_add x
     (precone_scale (NngNum mu_ge0) (precone_add v1 v2))) <= 1.
Proof.
move=> mu_ge0; set mu := l1%:num * l2%:num / (l1%:num + l2%:num) in mu_ge0 *.
have Spos : 0 < l1%:num + l2%:num by rewrite addr_gt0.
have w1_ge0 : 0 <= l2%:num / (l1%:num + l2%:num) by rewrite divr_ge0 ?ltW.
have w2_ge0 : 0 <= l1%:num / (l1%:num + l2%:num) by rewrite divr_ge0 ?ltW.
pose w1 : {nonneg R} := NngNum w1_ge0.
pose w2 : {nonneg R} := NngNum w2_ge0.
pose A := precone_add x (precone_scale l1 v1).
pose Bb := precone_add x (precone_scale l2 v2).
have key : precone_add x (precone_scale (NngNum mu_ge0) (precone_add v1 v2)) =
           precone_add (precone_scale w1 A) (precone_scale w2 Bb).
  rewrite /A /Bb !precone_scale_DAr -!precone_scale_A.
  have e_mu1 : widen_itv (w1%:num * l1%:num)%:itv = NngNum mu_ge0 :> {nonneg R}.
    by apply: val_inj => /=; rewrite /mu mulrAC (mulrC l2%:num).
  have e_mu2 : widen_itv (w2%:num * l2%:num)%:itv = NngNum mu_ge0 :> {nonneg R}.
    by apply: val_inj => /=; rewrite /mu mulrAC.
  rewrite e_mu1 e_mu2.
  have e_w : (w1%:num + w2%:num)%:nng = 1%:nng :> {nonneg R}.
    by apply: val_inj => /=; rewrite -mulrDl addrC mulfV// gt_eqF.
  have ACA : forall a b cc d : B,
      precone_add (precone_add a b) (precone_add cc d) =
      precone_add (precone_add a cc) (precone_add b d).
    move=> a b cc d; rewrite -!precone_addA; congr precone_add.
    by rewrite (precone_addC b) -precone_addA (precone_addC d).
  by rewrite ACA -precone_scale_DAl e_w precone_scale_1.
rewrite key.
apply: le_trans (cone_normt _ _) _.
rewrite !cone_normh /=.
apply: le_trans (_ : w1%:num * 1 + w2%:num * 1 <= 1).
  rewrite !mulr1; apply: lerD.
    by rewrite -[w1%:num]mulr1; apply: ler_wpM2l => //; exact: Hin1.
  by rewrite -[w2%:num]mulr1; apply: ler_wpM2l => //; exact: Hin2.
by rewrite !mulr1 -mulrDl addrC mulfV ?lexx// gt_eqF.
Qed.

(** Paper Lemma 7.1, (Normt): sub-additivity of the gauge norm.  The
    zero cases reduce to the value of [lc_norm] depending only on
    [lc_val].  Otherwise: given [ε > 0], pick admissible [λᵢ] with
    [λᵢ⁻¹ < lc_norm uᵢ + ε/2]; [gauge_convex] makes
    [μ = λ₁λ₂/(λ₁+λ₂)] admissible for [u₁+u₂], so
    [lc_norm (u₁+u₂) ≤ μ⁻¹ = λ₁⁻¹ + λ₂⁻¹ < lc_norm u₁ + lc_norm u₂ + ε]. *)
Lemma lc_normt (u1 u2 : P) :
  lc_norm (lc_add u1 u2) <= lc_norm u1 + lc_norm u2.
Proof.
have [z1|n1] := pselect (lc_val u1 = precone_zero).
  rewrite (_ : lc_norm u1 = 0); last exact: lc_norm0.
  rewrite add0r.
  have -> : lc_norm (lc_add u1 u2) = lc_norm u2.
    rewrite /lc_norm /gauge_sup; congr (_^-1); congr sup.
    by rewrite /gauge_set lc_valD z1 precone_add0.
  by [].
have [z2|n2] := pselect (lc_val u2 = precone_zero).
  rewrite (_ : lc_norm u2 = 0); last exact: lc_norm0.
  rewrite addr0.
  have -> : lc_norm (lc_add u1 u2) = lc_norm u1.
    rewrite /lc_norm /gauge_sup; congr (_^-1); congr sup.
    by rewrite /gauge_set lc_valD z2 precone_addr0.
  by [].
have g1pos : 0 < gauge_sup u1 by exact: gauge_sup_gt0.
have g2pos : 0 < gauge_sup u2 by exact: gauge_sup_gt0.
have add_n0 : lc_val (lc_add u1 u2) <> precone_zero.
  rewrite lc_valD => /precone_posl; exact: n1.
rewrite [lc_norm (lc_add _ _)]/lc_norm.
apply/ler_addgt0Pr => eps eps_pos.
have hs1 := has_sup_gauge n1.
have hs2 := has_sup_gauge n2.
have lc1_ge0 := lc_norm_ge0 u1.
have lc2_ge0 := lc_norm_ge0 u2.
have he2 : 0 < eps / 2 by rewrite divr_gt0.
pose tgt1 := (lc_norm u1 + eps / 2)^-1.
pose tgt2 := (lc_norm u2 + eps / 2)^-1.
have d1 : tgt1 < gauge_sup u1.
  rewrite /tgt1 /lc_norm -[X in _ < X]invrK ltf_pV2 ?posrE ?invr_gt0//.
    by rewrite ltrDl.
  by rewrite addr_gt0// invr_gt0.
have d2 : tgt2 < gauge_sup u2.
  rewrite /tgt2 /lc_norm -[X in _ < X]invrK ltf_pV2 ?posrE ?invr_gt0//.
    by rewrite ltrDl.
  by rewrite addr_gt0// invr_gt0.
have [l1 /= Hin1 Hl1] :
    exists2 l1 : {nonneg R},
      cone_norm (precone_add x (precone_scale l1 (lc_val u1))) <= 1
    & tgt1 < l1%:num.
  have := sup_adherent (eps := gauge_sup u1 - tgt1) _ hs1.
  rewrite subr_gt0 => /(_ d1)[d [s /= Hs se] He]; exists s => //.
  by move: He; rewrite opprB addrCA subrr addr0 se.
have [l2 /= Hin2 Hl2] :
    exists2 l2 : {nonneg R},
      cone_norm (precone_add x (precone_scale l2 (lc_val u2))) <= 1
    & tgt2 < l2%:num.
  have := sup_adherent (eps := gauge_sup u2 - tgt2) _ hs2.
  rewrite subr_gt0 => /(_ d2)[d [s /= Hs se] He]; exists s => //.
  by move: He; rewrite opprB addrCA subrr addr0 se.
have l1pos : 0 < l1%:num.
  apply: le_lt_trans Hl1; rewrite /tgt1 invr_ge0.
  by apply: addr_ge0 => //; apply: ltW.
have l2pos : 0 < l2%:num.
  apply: le_lt_trans Hl2; rewrite /tgt2 invr_ge0.
  by apply: addr_ge0 => //; apply: ltW.
have mu_ge0 : 0 <= l1%:num * l2%:num / (l1%:num + l2%:num).
  by rewrite divr_ge0 ?addr_ge0 ?mulr_ge0 ?ltW.
have Hmu := gauge_convex l1pos l2pos Hin1 Hin2 mu_ge0.
have mu_le : l1%:num * l2%:num / (l1%:num + l2%:num) <= gauge_sup (lc_add u1 u2).
  apply: sup_upper_bound; first exact: has_sup_gauge add_n0.
  by exists (NngNum mu_ge0) => //=; rewrite lc_valD; exact: Hmu.
have mu_pos : 0 < l1%:num * l2%:num / (l1%:num + l2%:num).
  by rewrite divr_gt0 ?addr_gt0 ?mulr_gt0.
apply: le_trans (_ : (l1%:num * l2%:num / (l1%:num + l2%:num))^-1 <= _).
  by rewrite lef_pV2 ?posrE//; apply: lt_le_trans mu_le.
have muinvE : (l1%:num * l2%:num / (l1%:num + l2%:num))^-1
            = l1%:num^-1 + l2%:num^-1.
  rewrite invfM invrK mulrDr invfM mulrAC mulVf ?gt_eqF// mul1r.
  by rewrite -mulrA mulVf ?gt_eqF// mulr1 addrC.
rewrite muinvE.
have b1 : l1%:num^-1 < lc_norm u1 + eps / 2.
  rewrite -[X in _ < X](invrK (lc_norm u1 + eps/2)).
  by rewrite ltf_pV2 ?posrE ?invr_gt0 ?addr_gt0// invr_gt0.
have b2 : l2%:num^-1 < lc_norm u2 + eps / 2.
  rewrite -[X in _ < X](invrK (lc_norm u2 + eps/2)).
  by rewrite ltf_pV2 ?posrE ?invr_gt0 ?addr_gt0// invr_gt0.
apply: ltW; apply: lt_le_trans (ltrD b1 b2) _.
by rewrite addrACA -splitr.
Qed.

(** ** (Normc) — ω-completeness of the unit ball of [B_x]

    Paper §7.1, (Normc) of Lemma 7.1.  For an increasing [B_x]-chain
    [w] with [lc_norm (w n) ≤ 1], the points [x + w n] form an
    increasing chain in the unit ball of [B] (each [x + w n ∈ B_B] by
    [dev_step1]).  Its [B]-supremum [S] dominates [x], so [S = x + W]
    for a [W ∈ B]; [W] is admissible (step [1] works since [S ∈ B_B]),
    is the [B]-lub of the [w n] (cancel [x]), and has [lc_norm W ≤ 1]
    (step [1] admissible).  As the order of [B_x] coincides with that of
    [B], [W] is also the [B_x]-lub. *)

(** Step [1] is admissible whenever [lc_norm w ≤ 1]: this realises the
    paper's observation [B_P = {u ∈ B | x + u ∈ B_B}]. *)
Lemma lc_step1 (w : P) : lc_norm w <= 1 ->
  cone_norm (precone_add x (lc_val w)) <= 1.
Proof.
move=> Hw.
have [w0|wn0] := pselect (lc_val w = precone_zero).
  by rewrite w0 precone_addr0.
have gpos : 0 < gauge_sup w by exact: gauge_sup_gt0.
have g_ge1 : 1 <= gauge_sup w.
  rewrite -[1]invr1 -lef_pV2 ?posrE ?ltr01// invrK.
  by move: Hw; rewrite /lc_norm.
have R1 := gauge_sup_reach wn0.
have step1 : cone_norm (precone_add x (precone_scale 1%:nng (lc_val w))) <= 1.
  by apply: (@localP_le_eps _ _ x (lc_val w) 1%:nng (NngNum (gauge_sup_ge0 w))).
by move: step1; rewrite precone_scale_1.
Qed.

(** Conversely, [x + u ∈ B_B] makes step [1] admissible, so it gives
    [lc_norm u ≤ 1] (when [u] is the [B]-value of a [B_x] element). *)
Lemma lc_step1_norm (u : P) :
  cone_norm (precone_add x (lc_val u)) <= 1 -> lc_norm u <= 1.
Proof.
move=> Hu.
have [u0|un0] := pselect (lc_val u = precone_zero).
  by rewrite lc_norm0// ler01.
have g_ge1 : 1 <= gauge_sup u.
  rewrite /gauge_sup; apply: sup_upper_bound; first exact: has_sup_gauge un0.
  by exists 1%:nng => //=; rewrite precone_scale_1.
rewrite /lc_norm -invr1 lef_pV2 ?posrE ?ltr01//.
exact: lt_le_trans (gauge_sup_gt0 un0) _.
Qed.

(** Cancellation for the order: [x + a ≤p x + b] gives [a ≤p b]. *)
Lemma lc_addxle (a b : B) :
  precone_le (precone_add x a) (precone_add x b) -> precone_le a b.
Proof.
move=> [z Hz]; exists z.
by apply: (@precone_cancel _ _ x); rewrite Hz precone_addA.
Qed.

Section LocalSupBall.
Variable w : nat -> P.
(** B-order chain hypothesis (the [B_x]-order one is converted to this
    via [lc_leE] when building the [isCone] instance). *)
Hypothesis wch : forall n, precone_le (lc_val (w n)) (lc_val (w n.+1)).
Hypothesis wb1 : forall n, lc_norm (w n) <= 1.

(** The translated chain [n ↦ x + (w n)] lives in [B_B]. *)
Let c n : B := precone_add x (lc_val (w n)).

Let c_mono n : precone_le (c n) (c n.+1).
Proof. by rewrite /c; apply: precone_add_le_l; exact: wch. Qed.

Let c_ub1 n : cone_norm (c n) <= 1.
Proof. by rewrite /c; apply: lc_step1; exact: wb1. Qed.

(** Its [B]-supremum. *)
Let S : B := cone_sup_ball c c_mono c_ub1.

Let S_norm : cone_norm S <= 1 := cone_sup_ball_norm c c_mono c_ub1.

Let xleS : precone_le x S.
Proof.
apply: (precone_le_trans (y := c 0)).
  by rewrite /c; exists (lc_val (w 0)).
exact: cone_sup_ball_ub.
Qed.

(** [S = x + W] with [W] the lub of the [w n]'s; [W] is admissible. *)
Definition lc_sup_val : B := projT1 (cid xleS).

Let SWE : S = precone_add x lc_sup_val := projT2 (cid xleS).

Lemma lc_sup_admissible : localP x lc_sup_val.
Proof.
exists 1%:nng; split; first by rewrite /= ltr01.
by rewrite precone_scale_1 -SWE.
Qed.

Definition lc_sup_ball : P := exist (localP x) lc_sup_val lc_sup_admissible.

(** Upper-bound and lub stated in [B]-order (on [lc_val]); the
    [B_x]-order versions follow via [lc_leE] at the instance site. *)
Lemma lc_sup_ball_ub n :
  precone_le (lc_val (w n)) (lc_val lc_sup_ball).
Proof.
apply: lc_addxle; rewrite -SWE.
exact: cone_sup_ball_ub.
Qed.

Lemma lc_sup_ball_lub (y : P) :
  (forall n, precone_le (lc_val (w n)) (lc_val y)) ->
  precone_le (lc_val lc_sup_ball) (lc_val y).
Proof.
move=> Hy.
apply: lc_addxle; rewrite -SWE.
apply: cone_sup_ball_lub => n.
by rewrite /c; apply: precone_add_le_l; exact: Hy.
Qed.

Lemma lc_sup_ball_norm : lc_norm lc_sup_ball <= 1.
Proof.
apply: lc_step1_norm => /=.
by rewrite -SWE.
Qed.

End LocalSupBall.

(** Paper Lemma 7.1: [B_x] is a cone.  We have proved (Normh)
    [lc_normh], (Normz) [lc_normz], (Normt) [lc_normt], (Normp)
    [lc_normp] (below), and (Normc) via [lc_sup_ball] and its three
    characterising lemmas. *)
Lemma lc_normp (u v : P) :
  precone_le (lc_val u) (lc_val v) -> lc_norm u <= lc_norm v.
Proof.
move=> uv.
have [v0|vn0] := pselect (lc_val v = precone_zero).
  have u0 : lc_val u = precone_zero.
    by case: uv => z Hz; apply: (@precone_posl _ _ _ z); rewrite -Hz.
  by rewrite !lc_norm0.
have [u0|un0] := pselect (lc_val u = precone_zero).
  by rewrite lc_norm0// lc_norm_ge0.
rewrite /lc_norm lef_pV2 ?posrE ?gauge_sup_gt0//.
rewrite /gauge_sup; apply: sup_le; last exact: has_sup_gauge un0.
  move=> s [t /= Hin <-]; exists (t%:num) => //; split; last by [].
  exists t => //=; apply: le_trans Hin.
  apply: cone_normp; apply: precone_add_le_l; apply: precone_scale_le.
  exact: uv.
exact: gauge_set_neq0.
Qed.

(** Paper Lemma 7.1: [B_x] is a cone, with [0], algebraic operations
    and order inherited from [B] and norm the gauge [lc_norm].  The five
    norm axioms are: (Normh) [lc_normh], (Normz) [lc_normz], (Normt)
    [lc_normt], (Normp) [lc_normp], and (Normc) the [lc_sup_ball]
    operator with its upper-bound, least-upper-bound and norm lemmas.
    The order [≤p] of [B_x] coincides with that of [B] ([lc_leE]), used
    to translate the [B]-order statements of (Normp) and the
    [lc_sup_ball] lemmas into the [B_x]-order shape required by the
    [isCone] mixin. *)
HB.instance Definition _ := @isCone.Build R (local_cone x)
  lc_norm
  lc_normh
  (fun (u : P) (H : lc_norm u = 0) => @lc_eq R B x u (lc_zero Hx) (lc_normz H))
  lc_normt
  (fun u v uv => lc_normp ((lc_leE Hx u v).1 uv))
  (fun u uch ub1 =>
     lc_sup_ball (w := u) (fun n => (lc_leE Hx (u n) (u n.+1)).1 (uch n)) ub1)
  (fun u uch ub1 n => (lc_leE Hx (u n) _).2
     (lc_sup_ball_ub (w := u)
        (fun n => (lc_leE Hx (u n) (u n.+1)).1 (uch n)) ub1 n))
  (fun u uch ub1 y Hy => (lc_leE Hx _ y).2
     (lc_sup_ball_lub (w := u)
        (fun n => (lc_leE Hx (u n) (u n.+1)).1 (uch n)) ub1
        (y := y) (fun n => (lc_leE Hx (u n) y).1 (Hy n))))
  (fun u uch ub1 => lc_sup_ball_norm (w := u)
     (fun n => (lc_leE Hx (u n) (u n.+1)).1 (uch n)) ub1).

End GaugeNorm.

(** The [coneType] of [B_x] with the admissibility witness [Hx]
    fixed.  The bare carrier [local_cone x] does not determine [Hx],
    so its canonical [Cone] structure is keyed by an extra
    [cnorm x < 1] argument; we name that family once here so the
    measurability layer below can resolve the [Cone] operations of
    [B_x] without leaving an [cnorm x < 1] placeholder. *)
Definition lc_coneType (R : realType) (B : coneType R) (x : B)
    (Hx : cone_norm x < 1) : coneType R :=
  local_cone_local_cone__canonical__cone_Cone Hx.

(** ** Norm domination: [‖lc_val u‖_B ≤ N(u)] — Paper §7.1 (p. 1:56)

    The paper records that [‖u‖_B ≤ ‖u‖_{B_x}] for every [u ∈ P].  This
    is what lets every [B]-test, pulled back along [lc_val], stay a
    valid test on [B_x] (it remains bounded by the gauge norm). *)
Section NormDom.
Variable R : realType.
Variable B : coneType R.
Variable x : B.
Hypothesis Hx : cone_norm x < 1.
Let Hxle : cone_norm x <= 1 := ltW Hx.
Local Notation P := (local_cone x).

(** Paper §7.1, p. 1:56: [‖u‖_B ≤ ‖u‖_{B_x}].  For [u ≠ 0], every
    admissible step [s] satisfies [s ≤ ‖lc_val u‖_B⁻¹] (Lemma 7.2
    style), hence [gauge_sup u ≤ ‖lc_val u‖_B⁻¹], i.e.
    [‖lc_val u‖_B ≤ (gauge_sup u)⁻¹ = N(u)]. *)
Lemma lc_val_norm_le (u : P) : cone_norm (lc_val u) <= lc_norm u.
Proof.
have [u0|un0] := pselect (lc_val u = precone_zero).
  by rewrite u0 cone_norm0 lc_norm_ge0.
have nu_pos : 0 < cone_norm (lc_val u).
  rewrite lt_neqAle cone_norm_ge0 andbT eq_sym.
  by apply/eqP => /cone_normz.
rewrite /lc_norm -[leLHS]invrK lef_pV2 ?posrE ?invr_gt0 ?gauge_sup_gt0//.
rewrite /gauge_sup; apply: ge_sup; first exact: gauge_set_neq0.
move=> s [t /= Hin <-].
rewrite -(ler_pM2r nu_pos) mulVf ?gt_eqF//.
have Hle : precone_le (precone_scale t (lc_val u))
                      (precone_add x (precone_scale t (lc_val u))).
  by exists x; rewrite precone_addC.
by apply: le_trans _ Hin; rewrite -cone_normh; exact: cone_normp.
Qed.

End NormDom.

(** ** Sup-ball compatibility with the inclusion — Paper §7.1 (Normc)

    The paper's (Normc) proof identifies the [B_x]-lub of an increasing
    unit-ball chain [(u_n)] as the [B]-lub of [(x + u_n)] minus [x].
    Here is that identity in operator form, used to transport the
    ω-continuity field [test_cont] of a [B]-test to its [B_x] pullback. *)
Section SupBallEq.
Variable R : realType.
Variable B : coneType R.
Variable x : B.
Hypothesis Hx : cone_norm x < 1.
Let Hxle : cone_norm x <= 1 := ltW Hx.

(** [B_x] as a [coneType] (see [lc_coneType]). *)
Local Notation LC := (lc_coneType Hx).

Variable u : nat -> LC.
Hypothesis uch : forall n, precone_le (u n) (u n.+1).
Hypothesis ub1 : forall n, cone_norm (u n) <= 1.

Let c n : B := precone_add x (lc_val (u n)).

Let cuch n : precone_le (lc_val (u n)) (lc_val (u n.+1)).
Proof. exact: (lc_leE Hx _ _).1 (uch n). Qed.

Let c_mono n : precone_le (c n) (c n.+1).
Proof. by rewrite /c; apply: precone_add_le_l; exact: cuch. Qed.

Let c_ub1 n : cone_norm (c n) <= 1.
Proof. by rewrite /c; apply: lc_step1; [exact: Hx | exact: ub1]. Qed.

(** Paper §7.1 (Normc): [x + (B_x-sup of u)] coincides with the
    [B]-sup of the translated chain [n ↦ x + u_n]. *)
Lemma lc_sup_ball_translate :
  precone_add x (lc_val (cone_sup_ball u uch ub1)) =
  cone_sup_ball c c_mono c_ub1.
Proof.
set S := cone_sup_ball c c_mono c_ub1.
have S_norm : cone_norm S <= 1 := cone_sup_ball_norm c c_mono c_ub1.
have xleSc : precone_le x S.
  apply: (precone_le_trans (y := c 0)); first by exists (lc_val (u 0)).
  exact: cone_sup_ball_ub.
have [W HW] := xleSc.
have Wadm : localP x W.
  exists 1%:nng; split; first by rewrite /= ltr01.
  by rewrite precone_scale_1 -HW.
pose w : LC := exist (localP x) W Wadm.
have lcw : lc_val w = W by [].
apply: precone_le_anti.
- rewrite HW; apply: precone_add_le_l.
  rewrite -[W]lcw.
  apply: (lc_leE Hx (cone_sup_ball u uch ub1) w).1.
  apply: (cone_sup_ball_lub u uch ub1) => n.
  apply: (lc_leE Hx (u n) w).2.
  rewrite lcw; apply: (lc_addxle (x:=x)).
  by rewrite -HW -/(c n); exact: cone_sup_ball_ub.
- apply: (cone_sup_ball_lub c c_mono c_ub1) => n.
  rewrite /c; apply: precone_add_le_l.
  exact: (lc_leE Hx (u n) _).1 (cone_sup_ball_ub u uch ub1 n).
Qed.

End SupBallEq.

(** ** Pullback of the test family along the inclusion — Paper §7.1

    Paper §7.1 (p. 1:56): "For each [X ∈ Ar] we define [M_X] as the set
    of all test functions [λr.λu. m(r, lc_val u)] for [m ∈ M^B_X]".  We
    build the pullback test [lc_test m : test_of Ar X B_x] and the
    family [lc_mcone_M] (which also admits the renormalized scalings
    [c ·: lc_test m] needed for (Msnorm) of [mcone.v]; see the status
    block below).  We prove the (Mscomp), (Mssep) and (Msnorm) closure
    conditions; the [isMCone] / [isICone] HB instances are registered
    further down. *)
Section LocalMCone.
Variable R : realType.
Variable Ar : MeasSubcat R.
Variable B : MCone.type Ar.
Variable x : B.
Hypothesis Hx : cone_norm x < 1.
Let Hxle : cone_norm x <= 1 := ltW Hx.

Local Notation LC := (lc_coneType Hx).

Section LocalTest.
Variable Y : ar_obj Ar.
Variable m : test_of Ar Y B.

(** Paper §7.1: the test [m] of [B] pulled back to [B_x] along the
    inclusion [lc_val]. *)
Definition lc_test_fun : ar_carrier Ar Y -> LC -> R :=
  fun r u => test_fun m r (lc_val u).

Lemma lc_test_meas (u : LC) :
  cone_norm u <= 1 ->
  measurable_fun [set: ar_carrier Ar Y] (fun r => lc_test_fun r u).
Proof.
move=> Hu; rewrite /lc_test_fun; apply: test_meas.
exact: le_trans (lc_val_norm_le Hx u) Hu.
Qed.

Lemma lc_test_ge0 (r : ar_carrier Ar Y) (u : LC) : 0 <= lc_test_fun r u.
Proof. exact: test_ge0. Qed.

Lemma lc_test_le1 (r : ar_carrier Ar Y) (u : LC) :
  cone_norm u <= 1 -> lc_test_fun r u <= 1.
Proof.
move=> Hu; rewrite /lc_test_fun; apply: test_le1.
exact: le_trans (lc_val_norm_le Hx u) Hu.
Qed.

Lemma lc_test_lin0 (r : ar_carrier Ar Y) : lc_test_fun r precone_zero = 0.
Proof. by rewrite /lc_test_fun lc_val0 test_lin0. Qed.

Lemma lc_test_linD (r : ar_carrier Ar Y) (u v : LC) :
  lc_test_fun r (precone_add u v) =
  lc_test_fun r u + lc_test_fun r v.
Proof. by rewrite /lc_test_fun lc_valD test_linD. Qed.

Lemma lc_test_linZ (r : ar_carrier Ar Y) (s : {nonneg R}) (u : LC) :
  lc_test_fun r (precone_scale s u) = s%:num * lc_test_fun r u.
Proof. by rewrite /lc_test_fun lc_valZ test_linZ. Qed.

(** Paper §7.1: ω-continuity transports along [lc_val] via the
    sup-ball identity [lc_sup_ball_translate]: writing [S] for the
    [B_x]-sup, [m r (lc_val S) = m r (x + lc_val S) - m r x] and the
    first summand is bounded by [test_cont] of [m] on the [B]-chain
    [n ↦ x + u_n]. *)
Lemma lc_test_cont (r : ar_carrier Ar Y)
  (u : nat -> LC)
  (uch : forall n, precone_le (u n) (u n.+1))
  (ub1 : forall n, cone_norm (u n) <= 1)
  (N : R) :
  (forall n, lc_test_fun r (u n) <= N) ->
  lc_test_fun r (cone_sup_ball u uch ub1) <= N.
Proof.
move=> HN; rewrite /lc_test_fun.
have key := lc_sup_ball_translate (u:=u) uch ub1.
have Hxc : test_fun m r (lc_val (cone_sup_ball u uch ub1)) =
           test_fun m r (x + lc_val (cone_sup_ball u uch ub1))%PC -
           test_fun m r x.
  by rewrite test_linD addrAC subrr add0r.
rewrite Hxc key lerBlDr.
apply: test_cont => n.
rewrite test_linD [in leRHS]addrC lerD2l.
exact: HN.
Qed.

Lemma lc_test_norm_le (r : ar_carrier Ar Y) (u : LC) :
  lc_test_fun r u <= cone_norm u.
Proof.
rewrite /lc_test_fun; apply: le_trans (test_norm_le _ _ _) _.
exact: lc_val_norm_le.
Qed.

(** Paper §7.1: [m] pulled back to [B_x]. *)
Definition lc_test : test_of Ar Y LC :=
  MkTestOf lc_test_meas lc_test_ge0 lc_test_le1
           lc_test_lin0 lc_test_linD lc_test_linZ
           lc_test_cont lc_test_norm_le.

End LocalTest.

Arguments lc_test {Y} m.

(** Paper §7.1: the test family of [B_x].  Beyond the pullbacks
    [lc_test m] of [B]'s tests, we also admit their *renormalized*
    scalings [c ·: lc_test m] ([c ≥ 0], the renormalization factor
    [1/‖m‖_{B_x}] of (Msnorm)).  A test [t] is in the family iff its
    underlying function is [(r,u) ↦ c · m(r, lc_val u)] for some
    [m ∈ M^B_Y] and [c ≥ 0]; this characterisation is closed under
    reindexing (scaling commutes with [test_reindex]) and still
    contains the bare pullbacks ([c = 1]) used for (Mssep). *)
Definition lc_mcone_M (Y : ar_obj Ar) : set (test_of Ar Y LC) :=
  [set t : test_of Ar Y LC | exists2 m, mcone_M Y m &
     exists2 c : R, 0 <= c &
       forall r u, test_fun t r u = c * test_fun m r (lc_val u)].

(** The bare pullback [lc_test m] is in the family (factor [c = 1]). *)
Lemma lc_mcone_M_pull (Y : ar_obj Ar) (m : test_of Ar Y B) :
  mcone_M Y m -> lc_mcone_M (lc_test m).
Proof. by move=> mM; exists m => //; exists 1 => // r u; rewrite mul1r. Qed.

(** Paper §7.1 (Mscomp): pullback commutes with reindexing,
    [test_reindex φ (lc_test m) = lc_test (test_reindex φ m)]. *)
Lemma lc_test_reindex (Y' Y : ar_obj Ar) (φ : ar_hom Ar Y' Y)
    (m : test_of Ar Y B) :
  test_reindex φ (lc_test m) = lc_test (test_reindex φ m).
Proof.
by apply: test_eq => s u; rewrite /test_reindex/= /test_reindex_fun/=.
Qed.

(** Paper §7.1 (Mscomp): the family is closed under reindexing.  A
    scaled pullback [(r,u) ↦ c · m(r, lc_val u)] reindexes to
    [(s,u) ↦ c · (test_reindex φ m)(s, lc_val u)], with the reindexed
    base test again in [M^B] by [B]'s (Mscomp). *)
Lemma lc_mcone_M_comp (Y' Y : ar_obj Ar) (φ : ar_hom Ar Y' Y)
    (t : test_of Ar Y LC) :
  lc_mcone_M t -> lc_mcone_M (test_reindex φ t).
Proof.
move=> [m mM [c c_ge0 Ht]]; exists (test_reindex φ m).
  exact: mcone_M_comp.
exists c => // s u.
by rewrite /test_reindex/= /test_reindex_fun/= Ht.
Qed.

(** Paper §7.1 (Mssep): arity-0 tests separate points of [B_x] —
    apply the separation hypothesis to the bare pullbacks
    [lc_test m] (which lie in the family) to separate the [lc_val]
    images by [B]'s (Mssep), then conclude with [lc_eq]. *)
Lemma lc_mcone_M_sep (u1 u2 : LC) :
  (forall t : test_of Ar (ar_zero Ar) LC,
    lc_mcone_M t ->
    test_fun t (ar_zero_pt Ar) u1 = test_fun t (ar_zero_pt Ar) u2) ->
  u1 = u2.
Proof.
move=> Hsep; apply: (lc_eq (x:=x)); apply: mcone_M_sep => m mM.
have Ht : lc_mcone_M (lc_test m) by exact: lc_mcone_M_pull.
by have := Hsep _ Ht.
Qed.

(** ** (Msnorm) for [B_x] — the renormalized-test construction

    Paper §7.1 (Example 7.3): at an interior point [‖x‖_B < 1] the
    gauge norm of [B_x] is reached by a *renormalized* pullback test.
    For [u ≠ 0] put [v := lc_val u], [λ* := gauge_sup u > 0],
    [z := x + λ* ·: v]; then [z ∈ B_B] with [‖z‖_B = 1]
    ([gauge_sup_reach] + [gauge_sup_gt_out]).  Applying [B]'s
    [mcone_M_norm] at [z] with a (small, uniform) slack [δ] gives a
    test [m] with [m(r0,z) ≥ 1 − δ].  Its [B_x]-dual norm
    [d(m) = sup_{‖w‖_{B_x}≤1} m(r0, lc_val w)] is bounded by
    [β := 1 − m(r0,x) ≥ 1 − ‖x‖_B > 0] and below by
    [m(r0,z) − m(r0,x) ≥ β − δ]; the renormalized test
    [t := (1/d(m)) ·: lc_test m] then satisfies
    [‖u‖_{B_x} ≤ t(r0,u) + ε]. *)

Local Notation r0 := (ar_zero_pt Ar).

(** The [B_x]-dual norm of a pullback test [lc_test m], i.e.
    [sup_{‖w‖_{B_x} ≤ 1} m(r0, lc_val w)]. *)
Definition lc_dnorm (m : test_of Ar (ar_zero Ar) B) : R :=
  sup [set test_fun m r0 (lc_val w) | w in [set w : LC | cone_norm w <= 1]].

Section DualNorm.
Variable m : test_of Ar (ar_zero Ar) B.

Let dset : set R :=
  [set test_fun m r0 (lc_val w) | w in [set w : LC | cone_norm w <= 1]].

Let dset_neq0 : nonempty dset.
Proof.
exists (test_fun m r0 (lc_val (precone_zero : LC))).
exists (precone_zero : LC) => //=.
by rewrite cone_norm0 ler01.
Qed.

Let dset_ub : has_ubound dset.
Proof.
exists 1 => z [w /= Hw <-].
apply: le_trans (test_norm_le _ _ _) _.
exact: le_trans (lc_val_norm_le Hx w) Hw.
Qed.

Let dset_hassup : has_sup dset.
Proof. by split. Qed.

(** Every unit-ball value [m(r0, lc_val w)] is below [d(m)]. *)
Lemma lc_dnorm_ub (w : LC) :
  cone_norm w <= 1 -> test_fun m r0 (lc_val w) <= lc_dnorm m.
Proof.
move=> Hw; apply: sup_upper_bound => //; exists w => //=.
Qed.

(** [d(m) ≥ 0]. *)
Lemma lc_dnorm_ge0 : 0 <= lc_dnorm m.
Proof.
apply: le_trans (lc_dnorm_ub (w := (precone_zero : LC)) _).
  by rewrite /lc_test_fun lc_val0 test_lin0.
by rewrite cone_norm0 ler01.
Qed.

(** Admissibility bound: [d(m) ≤ 1 − m(r0, x)].  For unit-ball [w],
    [x + lc_val w ∈ B_B] ([lc_step1]), so
    [m(r0,x) + m(r0, lc_val w) = m(r0, x + lc_val w) ≤ 1]. *)
Lemma lc_dnorm_le : lc_dnorm m <= 1 - test_fun m r0 x.
Proof.
apply: ge_sup => // z [w /= Hw <-].
rewrite lerBrDr addrC -test_linD.
apply: le_trans (test_norm_le _ _ _) _.
by apply: lc_step1 => //; rewrite -[lc_val w]/(lc_val w).
Qed.

(** Operator-norm bound: [m(r0, lc_val u) ≤ d(m) · ‖u‖_{B_x}] for *all*
    [u].  By homogeneity it reduces to the unit-ball bound
    [lc_dnorm_ub]: rescale [u] to gauge-norm [1]. *)
Lemma lc_dnorm_opnorm (u : LC) :
  test_fun m r0 (lc_val u) <= lc_dnorm m * cone_norm u.
Proof.
have [u0|un0] := pselect (lc_val u = precone_zero).
  rewrite u0 test_lin0 mulr_ge0//; first exact: lc_dnorm_ge0.
  exact: cone_norm_ge0.
have nu_pos : 0 < cone_norm u.
  rewrite (_ : cone_norm u = lc_norm u)//.
  by rewrite /lc_norm invr_gt0; exact: gauge_sup_gt0.
pose r := (cone_norm u)^-1.
have r_ge0 : 0 <= r by rewrite invr_ge0 ltW.
pose u' : LC := lc_scale Hx (NngNum r_ge0) u.
have u'_ball : cone_norm u' <= 1.
  rewrite (_ : cone_norm u' = lc_norm u')//.
  by rewrite /u' lc_normh /= /r mulVf ?gt_eqF.
have key := lc_dnorm_ub u'_ball.
move: key; rewrite /u' lc_valZ test_linZ /= /r.
rewrite ler_pdivrMl// => H.
by rewrite mulrC.
Qed.

End DualNorm.

(** Paper §7.1: at the reach, [‖x + λ* ·: v‖_B ≥ 1].  If it were
    [< 1], a slightly longer step [s = λ* + d] would still satisfy
    [‖x + s ·: v‖_B ≤ ‖z‖_B + d·‖v‖_B ≤ 1] for small [d > 0],
    contradicting [gauge_sup_gt_out] ([s > λ* = gauge_sup u]). *)
Lemma lc_z_norm_ge1 (u : LC) (un0 : lc_val u <> precone_zero) :
  1 <= cone_norm
    (precone_add x (precone_scale (NngNum (gauge_sup_ge0 Hx u)) (lc_val u))).
Proof.
set v := lc_val u; set L := gauge_sup u.
set z := precone_add x _.
rewrite leNgt; apply/negP => zlt1.
have gap_pos : 0 < 1 - cone_norm z by rewrite subr_gt0.
have cv_pos : 0 < cone_norm v + 1.
  by apply: lt_le_trans (_ : 1 <= _); [exact: ltr01 | rewrite lerDr cone_norm_ge0].
pose d : R := (1 - cone_norm z) / (2 * (cone_norm v + 1)).
have d_pos : 0 < d by rewrite divr_gt0 ?mulr_gt0 ?ltr0n.
have Ld_ge0 : 0 <= L + d by rewrite addr_ge0 ?gauge_sup_ge0 ?ltW.
have sgtL : L < (NngNum Ld_ge0)%:num by rewrite /= ltrDl.
have zd_eq : precone_add x (precone_scale (NngNum Ld_ge0) v) =
             precone_add z (precone_scale (NngNum (ltW d_pos)) v).
  rewrite /z -precone_addA; congr precone_add.
  rewrite -precone_scale_DAl; congr precone_scale.
  by apply: val_inj => /=; rewrite addrC.
have nle : cone_norm (precone_add x (precone_scale (NngNum Ld_ge0) v)) <= 1.
  rewrite zd_eq; apply: le_trans (cone_normt _ _) _.
  rewrite cone_normh /= -lerBrDl.
  rewrite /d -mulrA -[leRHS]mulr1 ler_wpM2l ?subr_ge0 ?ltW//.
  rewrite mulrC ltr_pdivrMr ?mulr_gt0 ?ltr0n// mul1r.
  rewrite mulrDr mulr1; apply: le_lt_trans (_ : 2 * cone_norm v < _).
    by rewrite ler_peMl ?cone_norm_ge0 ?ler1n.
  by rewrite ltrDl ltr0n.
exact: (gauge_sup_gt_out Hx un0 sgtL nle).
Qed.

(** ** Scaling a pullback test by a non-negative constant

    [c ·: lc_test m], with the operator-norm validity proof
    [Hnorm : c · m(r0, lc_val u) ≤ ‖u‖_{B_x}] for *all* [u].  This is
    the renormalized test [t] of (Msnorm): the factor [c = 1/‖m‖_{B_x}]
    rescales the pullback so it stays bounded by the gauge norm. *)
Section ScaledTest.
Variable m : test_of Ar (ar_zero Ar) B.
Variable c : R.
Hypothesis cge0 : 0 <= c.
Hypothesis Hnorm :
  forall u : LC, c * test_fun m r0 (lc_val u) <= cone_norm u.

Let f : ar_carrier Ar (ar_zero Ar) -> LC -> R :=
  fun r u => c * test_fun m r (lc_val u).

Let st_meas (u : LC) :
  cone_norm u <= 1 -> measurable_fun [set: _] (fun r => f r u).
Proof.
move=> Hu; rewrite /f.
have -> : (fun r => c * test_fun m r (lc_val u))
        = (functions.cst c) \* (fun r => test_fun m r (lc_val u)) by [].
apply: measurable_funM; first exact: measurable_cst.
by apply: test_meas; exact: le_trans (lc_val_norm_le Hx u) Hu.
Qed.

Let st_ge0 (r : ar_carrier Ar (ar_zero Ar)) (u : LC) : 0 <= f r u.
Proof. by rewrite /f mulr_ge0//; exact: test_ge0. Qed.

Let st_norm_le (r : ar_carrier Ar (ar_zero Ar)) (u : LC) :
  f r u <= cone_norm u.
Proof. by rewrite /f (ar_zero_ptE r); exact: Hnorm. Qed.

Let st_le1 (r : ar_carrier Ar (ar_zero Ar)) (u : LC) :
  cone_norm u <= 1 -> f r u <= 1.
Proof. by move=> Hu; apply: le_trans Hu; exact: st_norm_le. Qed.

Let st_lin0 (r : ar_carrier Ar (ar_zero Ar)) : f r precone_zero = 0.
Proof. by rewrite /f lc_val0 test_lin0 mulr0. Qed.

Let st_linD (r : ar_carrier Ar (ar_zero Ar)) (u v : LC) :
  f r (precone_add u v) = f r u + f r v.
Proof. by rewrite /f lc_valD test_linD mulrDr. Qed.

Let st_linZ (r : ar_carrier Ar (ar_zero Ar)) (s : {nonneg R}) (u : LC) :
  f r (precone_scale s u) = s%:num * f r u.
Proof. by rewrite /f lc_valZ test_linZ mulrCA. Qed.

Let st_cont (r : ar_carrier Ar (ar_zero Ar))
  (u : nat -> LC)
  (uch : forall n, precone_le (u n) (u n.+1))
  (ub1 : forall n, cone_norm (u n) <= 1) (N : R) :
  (forall n, f r (u n) <= N) -> f r (cone_sup_ball u uch ub1) <= N.
Proof.
move=> HN; rewrite /f.
have [->|cpos] := eqVneq c 0.
  by rewrite mul0r; exact: le_trans (st_ge0 r (u 0%N)) (HN 0%N).
have cgt0 : 0 < c by rewrite lt0r cpos cge0.
rewrite -ler_pdivlMl//; apply: (lc_test_cont (m := m)) => n.
by rewrite ler_pdivlMl//; have := HN n; rewrite /f.
Qed.

(** Paper §7.1: the renormalized scaled pullback as a [test_of]. *)
Definition lc_scaled_test : test_of Ar (ar_zero Ar) LC :=
  MkTestOf st_meas st_ge0 st_le1 st_lin0 st_linD st_linZ st_cont
           st_norm_le.

Lemma lc_scaled_testE (r : ar_carrier Ar (ar_zero Ar)) (u : LC) :
  test_fun lc_scaled_test r u = c * test_fun m r (lc_val u).
Proof. by []. Qed.

Lemma lc_scaled_test_inM :
  mcone_M (ar_zero Ar) m -> lc_mcone_M lc_scaled_test.
Proof. by move=> mM; exists m => //; exists c => // r u. Qed.

End ScaledTest.

(** Paper §7.1 / Example 7.3 (Msnorm): the renormalized pullback test
    reaches within ε of the gauge norm at an interior point.  See the
    section header for the full construction; the slack [δ] is chosen
    uniformly via the strict interior bound [1 − ‖x‖_B > 0]. *)
Lemma lc_mcone_M_norm (u : LC) (eps : R) :
  u <> precone_zero -> 0 < eps ->
  exists t : test_of Ar (ar_zero Ar) LC,
    lc_mcone_M t /\ cone_norm u <= test_fun t r0 u + eps.
Proof.
move=> u0 eps_pos.
have un0 : lc_val u <> precone_zero.
  by move=> e; apply: u0; apply: (lc_eq (x := x)); rewrite lc_val0.
set v := lc_val u; set L := gauge_sup u.
pose Lge0 := gauge_sup_ge0 Hx u.
have Lpos : 0 < L := gauge_sup_gt0 Hx un0.
set z := precone_add x (precone_scale (NngNum Lge0) v).
have zin : cone_norm z <= 1 := gauge_sup_reach Hx un0.
have zge1 : 1 <= cone_norm z := lc_z_norm_ge1 un0.
have zn0 : z <> precone_zero.
  move=> e; move: zge1; rewrite e cone_norm0 leNgt => /negP; apply.
  exact: ltr01.
set κ := 1 - cone_norm x.
have κpos : 0 < κ by rewrite subr_gt0.
pose δ : R := Num.min (eps * L * κ / 2) (κ / 2).
have δle1 : δ <= eps * L * κ / 2 by rewrite ge_min lexx.
have δle2 : δ <= κ / 2 by rewrite ge_min lexx orbT.
have δpos : 0 < δ.
  rewrite lt_min !mulr_gt0 ?invr_gt0 ?ltr0n ?eps_pos//.
have [m [mM Hm]] := mcone_M_norm z δ zn0 δpos.
set d := lc_dnorm m.
have dge0 : 0 <= d := lc_dnorm_ge0 m.
(* β := 1 − m(r0, x) ≥ κ > 0 *)
have mx_le : test_fun m r0 x <= cone_norm x := test_norm_le m r0 x.
have βpos : 0 < 1 - test_fun m r0 x.
  by rewrite subr_gt0; apply: le_lt_trans mx_le _; rewrite -subr_gt0.
have dle : d <= 1 - test_fun m r0 x := lc_dnorm_le m.
(* z-expansion m(r0,z) = m(r0,x) + L·m(r0,v) *)
have mzE : test_fun m r0 z = test_fun m r0 x + L * test_fun m r0 v.
  by rewrite /z test_linD test_linZ.
(* lower bound L·m(r0,v) ≥ 1 − δ − m(r0,x) ≥ β − δ *)
have mzlb : 1 - δ <= test_fun m r0 z.
  by rewrite lerBlDr; apply: le_trans zge1 Hm.
have Lmv_lb : 1 - δ - test_fun m r0 x <= L * test_fun m r0 v.
  rewrite lerBlDl; apply: le_trans mzlb _; rewrite mzE.
  by rewrite addrC.
(* d ≥ L·m(r0,v) via w₀ in the unit ball *)
have w0_ball :
  cone_norm (lc_scale Hx (NngNum Lge0) u : LC) <= 1.
  rewrite (_ : cone_norm _ = lc_norm (lc_scale Hx (NngNum Lge0) u))//.
  by rewrite lc_normh /lc_norm /= -/L mulfV ?lexx ?gt_eqF.
have d_lb : L * test_fun m r0 v <= d.
  have := lc_dnorm_ub m w0_ball.
  by rewrite lc_valZ test_linZ /=.
have βge : κ <= 1 - test_fun m r0 x by rewrite /κ lerD2l lerN2.
have κhalf_pos : 0 < κ / 2 by rewrite divr_gt0 ?ltr0n.
have dpos : 0 < d.
  apply: lt_le_trans d_lb; apply: lt_le_trans Lmv_lb.
  apply: lt_le_trans κhalf_pos _.
  rewrite addrAC lerBrDr; apply: le_trans _ βge.
  by rewrite [leRHS]splitr lerD2l.
(* the renormalized test t = (1/d) ·: lc_test m *)
have cge0 : 0 <= d^-1 by rewrite invr_ge0 ltW.
have Hnorm : forall w : LC, d^-1 * test_fun m r0 (lc_val w) <= cone_norm w.
  move=> w; have Hop := lc_dnorm_opnorm m w.
  rewrite -/d in Hop.
  rewrite -[leRHS]mul1r -(@mulVf _ d) ?gt_eqF// -mulrA.
  have d1ge0 : 0 <= d^-1 by rewrite invr_ge0 ltW.
  by rewrite (ler_wpM2l d1ge0).
exists (lc_scaled_test cge0 Hnorm); split.
  exact: lc_scaled_test_inM.
rewrite lc_scaled_testE -/v.
(* reduce to L⁻¹ ≤ d⁻¹·m(r0,v) + eps *)
rewrite (_ : cone_norm u = lc_norm u)// /lc_norm -/L.
set β := 1 - test_fun m r0 x.
have βpos' : 0 < β by [].
have βLpos : 0 < β * L by rewrite mulr_gt0.
(* β − δ ≤ L·m(r0,v) *)
have Lmv_lb' : β - δ <= L * test_fun m r0 v.
  by rewrite /β; move: Lmv_lb; rewrite addrAC.
(* lower bound d⁻¹·m(r0,v) ≥ (β−δ)/(βL) *)
have dvlb : (β - δ) / (β * L) <= d^-1 * test_fun m r0 v.
  apply: (@le_trans _ _ (β^-1 * test_fun m r0 v)).
    rewrite ler_pdivrMr// mulrACA mulVf ?gt_eqF// mul1r mulrC.
    exact: Lmv_lb'.
  rewrite ler_wpM2r ?test_ge0//.
  have inv_mono : β^-1 <= d^-1 by rewrite lef_pV2 ?posrE//.
  exact: inv_mono.
(* δ/(βL) ≤ eps *)
have κβ : κ <= β by rewrite /β /κ lerD2l lerN2.
have κ2β : κ / 2 <= β.
  apply: (le_trans _ κβ); apply: ler_piMr; first exact: ltW.
  by rewrite invf_le1 ?ler1n ?ltr0n.
have δβL_le : δ / (β * L) <= eps.
  rewrite ler_pdivrMr//.
  apply: le_trans δle1 _.
  have e1 : eps * L * κ / 2 = (eps * L) * (κ / 2) by rewrite mulrA.
  have e2 : eps * (β * L) = (eps * L) * β by rewrite mulrCA mulrC.
  have epsL_ge0 : 0 <= eps * L by rewrite mulr_ge0 ?ltW.
  by rewrite e1 e2 (ler_wpM2l epsL_ge0).
(* assemble: L⁻¹ = (β−δ)/(βL) + δ/(βL) ≤ d⁻¹·m(r0,v) + eps *)
have LinvE : L^-1 = (β - δ) / (β * L) + δ / (β * L).
  rewrite -mulrDl subrK invfM mulrA mulfV ?gt_eqF//.
  by rewrite mul1r.
rewrite LinvE; apply: lerD => //.
Qed.

(** Paper §7.1 / Example 7.3: [B_x] is a measurable cone.  The test
    family is the renormalized pullback family [lc_mcone_M]; (Mscomp),
    (Mssep), (Msnorm) are [lc_mcone_M_comp], [lc_mcone_M_sep],
    [lc_mcone_M_norm]. *)
HB.instance Definition _ := @isMCone.Build R Ar (local_cone x)
  lc_mcone_M lc_mcone_M_comp lc_mcone_M_sep lc_mcone_M_norm.

End LocalMCone.

(** ** [B_x] is an integrable cone — Paper §7.1 (p. 1:55, ~3189)

    "the integral [I^{B_x}_X(β, µ)] is computed as in [B]": for a
    measurable path [β : X → B_x] and a finite measure [µ], the integral
    is the [B]-integral [y] of [lc_val ∘ β], which is *admissible* at the
    interior point [x] ([‖x‖_B < 1] makes [x + ε ·: y ∈ B_B] for small
    [ε]) and hence sits in [B_x].  Its defining equation transfers along
    the renormalized pullback tests via [B]'s own [icone_integralP]. *)
Section LocalICone.
Variable R : realType.
Variable Ar : MeasSubcat R.
Variable B : ICone.type Ar.
Variable x : B.
Hypothesis Hx : cone_norm x < 1.
Let Hxle : cone_norm x <= 1 := ltW Hx.

(** [B_x] as an [mconeType] with the witness [Hx] fixed (mirrors
    [lc_coneType]; lets [is_measurable_path] resolve the [MCone]
    operations without an [cnorm x < 1] placeholder). *)
Local Notation LCM :=
  (local_cone_local_cone__canonical__mcone_MCone Hx).

Section LocalIntegral.
Variable X : ar_obj Ar.
Variable β : ar_carrier Ar X -> LCM.
Hypothesis Hβ : is_measurable_path β.
Variable µ : fmeas R (ar_carrier Ar X).

(** The [B]-shadow path [lc_val ∘ β]. *)
Let β' : ar_carrier Ar X -> B := fun r => lc_val (β r).

(** Its bound [Mβ] (inherited from [β]'s bound via [‖lc_val·‖ ≤ ‖·‖]). *)
Let Mβ : R := projT1 (cid (proj1 Hβ)).

Let β_bound r : cone_norm (β' r) <= Mβ.
Proof.
rewrite /β'; apply: le_trans (lc_val_norm_le Hx (β r)) _.
exact: projT2 (cid (proj1 Hβ)) r.
Qed.

(** [lc_val ∘ β] is a measurable path in [B]: its [B]-tests pull back to
    the bare pullback tests [lc_test], for which [β] is measurable. *)
Let Hβ' : is_measurable_path β'.
Proof.
split; first by exists Mβ; exact: β_bound.
move=> Y m mM.
have := (proj2 Hβ) Y (@lc_test R Ar B x Hx Y m) (lc_mcone_M_pull Hx mM).
by under eq_fun do rewrite /test_fun/= /lc_test_fun.
Qed.

(** The candidate integral [y : B] and its bound. *)
Let y : B := icone_integral β' Hβ' µ.

Let y_norm : cone_norm y <= Mβ * fmeas_norm µ.
Proof.
exact: (path_integral_norm_le (Mβ := Mβ) β_bound Hβ' y
          (icone_integralP β' Hβ' µ)).
Qed.

(** [y] is admissible at [x]: at the interior point [‖x‖_B < 1] a small
    step [ε] keeps [x + ε ·: y] in the unit ball. *)
Let y_adm : localP x y.
Proof.
set N := Mβ * fmeas_norm µ.
have Mβ_ge0 : 0 <= Mβ.
  by apply: le_trans (β_bound (ar_point Ar X)); exact: cone_norm_ge0.
have N_ge0 : 0 <= N by rewrite mulr_ge0 ?fmeas_norm_ge0.
pose eps := (1 - cone_norm x) / (2 * (N + 1)).
have N1_pos : 0 < N + 1 by apply: lt_le_trans (_ : 1 <= _); rewrite ?ltr01 ?lerDr.
have eps_gt0 : 0 < eps.
  by rewrite /eps divr_gt0 ?mulr_gt0 ?ltr0n ?subr_gt0.
have eps_ge0 : 0 <= eps := ltW eps_gt0.
exists (NngNum eps_ge0); split; first exact: eps_gt0.
apply: le_trans (cone_normt _ _) _.
rewrite cone_normh /= -lerBrDl.
apply: le_trans (_ : eps * N <= _).
  by rewrite ler_wpM2l// ?divr_ge0 ?mulr_ge0 ?ltr0n ?subr_ge0.
rewrite /eps -mulrA -[leRHS]mulr1 ler_wpM2l ?subr_ge0//.
rewrite ler_pdivrMl ?mulr_gt0 ?ltr0n// mulr1 mulrDr mulr1.
apply: le_trans (_ : 2 * N <= _); first by rewrite ler_peMl ?ler1n.
by rewrite lerDl ler0n.
Qed.

(** The integral packaged as a [B_x] element. *)
Let z : local_cone x := exist (localP x) y y_adm.

Let zE : lc_val z = y. Proof. by []. Qed.

(** Paper §7.1: [z] satisfies the Pettis equation in [B_x].  Pullback
    tests are scaled pullbacks [c · m'(·, lc_val·)]; the constant pulls
    out of the integral ([integralZl]) and the un-scaled equation is
    [B]'s own [icone_integralP] for [y]. *)
Lemma lc_path_integrable : is_path_integrable β µ.
Proof.
exists z => t [m mM [c c_ge0 Ht]] s.
have mmeas : measurable_fun [set: ar_carrier Ar X]
    (fun r => (test_fun m s (β' r))%:E).
  by apply/measurable_EFinP; exact: (measurable_test_path_section mM Hβ').
have mcst : measurable_fun [set: ar_carrier Ar X]
    (fun _ : ar_carrier Ar X => Mβ%:E).
  exact: measurable_cst.
have mfin : (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X])
    (test_fun m s (β' r))%:E \is a fin_num)%E.
  rewrite ge0_fin_numE; last first.
    by apply: integral_ge0 => r _; rewrite lee_fin; apply: test_ge0.
  apply: (@le_lt_trans _ _
    (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X]) Mβ%:E)%E).
    apply: ge0_le_integral => //.
    - by move=> r _; rewrite lee_fin; apply: test_ge0.
    - move=> r _; rewrite lee_fin.
      by apply: le_trans (test_norm_le _ _ _) (β_bound r).
  by rewrite integral_cst// ltey_eq fin_numM ?fmeas_setT_fin.
have mint : (fmeas_mu µ).-integrable [set: ar_carrier Ar X]
    (fun r => (test_fun m s (β' r))%:E).
  apply/integrableP; split=> //.
  under eq_integral => r _ do rewrite gee0_abs ?lee_fin ?test_ge0//.
  by rewrite ltey_eq mfin.
under eq_integral => r _ do rewrite Ht EFinM.
rewrite Ht zE (icone_integralP β' Hβ' µ m mM s).
by rewrite integralZl// fineM//=.
Qed.

End LocalIntegral.

(** Paper §7.1 (~3189): [B_x] is an integrable measurable cone. *)
Lemma lc_icone_exists (X : ar_obj Ar)
    (β : ar_carrier Ar X -> LCM) :
  is_measurable_path β ->
  forall µ : fmeas R (ar_carrier Ar X), is_path_integrable β µ.
Proof. by move=> Hβ µ; exact: lc_path_integrable. Qed.

HB.instance Definition _ := @isICone.Build R Ar (local_cone x)
  lc_icone_exists.

End LocalICone.

(**md**************************************************************)
(** ** Status: what is proved

    Proved here.
    - Carrier [local_cone] with proof-irrelevant equality [lc_eq].
    - Stability of admissibility: [localP0], [localP_add],
      [localP_scale], [localP_le], [localP_le_eps].
    - Paper Lemma 7.1 (algebraic half): the full [isPrecone] instance on
      [local_cone] — zero, [+], [·:] inherited from [B].
    - The order coincidence [lc_leE] (paper's "[u ≤_P v] iff [u ≤_B v]").
    - The gauge data: [gauge_set], its non-emptiness [gauge_set0] and
      bound [gauge_set_ub], the reach [gauge_sup] with [gauge_sup_ge0]
      and (for [u ≠ 0]) [gauge_sup_gt0], and the gauge norm [lc_norm]
      with [lc_norm_ge0], (Normz) [lc_normz] and [lc_norm0].
    - The "scalar limit commutes with [cone_sup_ball]" fact, proved in
      the exact form needed inside [gauge_sup_reach]:
      for an admissible chain [a_n ↑ gauge_sup u], the gap [t] between
      [x + (gauge_sup u) ·: u] and [cone_sup_ball (n ↦ x + a_n ·: u)]
      has [‖t‖ ≤ (gauge_sup u - a_n)‖u‖ → 0], hence [t = 0].  ([rmax]
      provides the monotone approximating chain.)
    - Paper Lemma 7.2 (the "out" half): [gauge_sup_gt_out]; and the
      "reach" half [gauge_sup_reach]: [x + (gauge_sup u) ·: u ∈ B_B].
    - Paper Lemma 7.1: the full [isCone] instance on [local_cone x].
      (Normh) [lc_normh] (via [gauge_sup_scale]), (Normz) [lc_normz],
      (Normt) [lc_normt] (via the convexity estimate [gauge_convex]),
      (Normp) [lc_normp], and (Normc) the [lc_sup_ball] operator with
      [lc_sup_ball_ub], [lc_sup_ball_lub], [lc_sup_ball_norm] — its
      [B]-supremum [x + W] is built from the [B_B]-chain [n ↦ x + w_n]
      ([lc_step1]) and [W] is admissible by step [1].
    - The measurability *infrastructure* of [B_x] (paper §7.1, p. 1:56),
      for [B : mconeType Ar] (or stronger): the named [coneType] family
      [lc_coneType Hx] (so the [Cone] operations of [B_x] resolve with a
      fixed admissibility witness), the norm-domination lemma
      [lc_val_norm_le] ([‖u‖_B ≤ ‖u‖_{B_x}]), the (Normc) operator
      identity [lc_sup_ball_translate], the *full* pullback test
      [lc_test m : test_of Ar X B_x] (all eight [test_of] fields proved,
      including ω-continuity [lc_test_cont] via [lc_sup_ball_translate]),
      and the (enriched) test family [lc_mcone_M].

    - Paper §7.1 / Example 7.3: the [isMCone] HB *instance* on
      [local_cone x] (so [B_x] is a full [mconeType]), at the *strict*
      interior point [‖x‖_B < 1] (section hypothesis [Hx]; the older
      [≤ 1] facts of Lemmas 7.1/7.2 are recovered through [ltW Hx]).
      The test family is the *renormalized* pullback family
      [lc_mcone_M = { (r,u) ↦ c · m(r, lc_val u) | m ∈ M^B, c ≥ 0 }];
      (Mscomp) [lc_mcone_M_comp] and (Mssep) [lc_mcone_M_sep] hold as
      for the bare pullbacks, and (Msnorm) [lc_mcone_M_norm] is closed
      by the renormalized test [(1/‖m‖_{B_x}) · lc_test m]: with the
      [B_x]-dual norm [lc_dnorm m = sup_{‖w‖_{B_x}≤1} m(r0, lc_val w)]
      ([lc_dnorm_ub], [lc_dnorm_le], [lc_dnorm_opnorm]), the reach point
      [z = x + λ* ·: v] (norm [1] by [gauge_sup_reach] + [lc_z_norm_ge1])
      and [B]'s own [mcone_M_norm] at [z] with a slack [δ] chosen
      uniformly via [1 − ‖x‖_B > 0].  The id-test undershoot of the
      simplified (Msnorm) is exactly what the renormalization factor
      [1/‖m‖_{B_x}] (≥ 1, the homothety factor of Example 7.3) repairs;
      this is *only* available at the strict interior, which is the
      paper's setting for local cones.

    - Paper §7.1 (~3189): the [isICone] HB *instance* on [local_cone x]
      (so [B_x] is a full [iconeType]) for [B : iconeType Ar].  The
      integral is "computed as in [B]" ([lc_icone_exists]): for a
      measurable path [β : X → B_x] and finite [µ], the [B]-integral
      [y = icone_integral (lc_val ∘ β)] is *admissible* at [x] ([y_adm],
      again using [‖x‖_B < 1] to keep [x + ε ·: y ∈ B_B]) and so packages
      to a [B_x] element [z]; its Pettis equation transfers along the
      renormalized pullback tests via [B]'s [icone_integralP] (the
      constant [c] factoring out of the integral by [integralZl]).
*)
