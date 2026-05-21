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
      ([gauge_sup_reach], [gauge_sup_gt_out]).

    Design notes.
    - [B] is taken to be a [coneType R]; the paper assumes integrability,
      but Lemma 7.1 and Lemma 7.2 only use the cone structure (norm,
      order, (Normc) ω-completeness of the unit ball).  The
      measurability / integrability instances "inherited as in [B]" are
      *deferred* (see the end of the file).
    - Membership is a [Prop]-existential; we use [Prop_irrelevance] so
      that two carrier elements are equal as soon as their [B]-components
      are.  This is what lets the algebraic axioms reduce to the
      corresponding facts in [B].
    - The full [isCone] instance (the norm axioms, in particular (Normc))
      is *not* registered: see the closing comment for exactly what is
      proved and what is left.
*)
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference.
From HB Require Import structures.

Require Import Icones.prelude.classical_extra.
Require Import Icones.prelude.nonneg_extra.
Require Import Icones.prelude.omegacpo.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(** ** The carrier of the local cone *)

Section LocalConeCarrier.
Variable R : realType.
Variable B : coneType R.
Variable x : B.
Hypothesis Hx : cone_norm x <= 1.

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
Hypothesis Hx : cone_norm x <= 1.

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

End GaugeNorm.

(**md**************************************************************)
(** ** Status: what is proved, and what is deferred

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
    - Paper Lemma 7.2 (the "out" half): [gauge_sup_gt_out] — any step
      strictly beyond [sup gauge_set u] leaves [B_B] (for [u ≠ 0]).

    Deferred (require a "scalar-limit commutes with the unit-ball
    supremum" lemma that is not part of the primitive cone API).
    - Paper Lemma 7.2 (the "reach" half): [x + (gauge_sup u) ·: u ∈ B_B].
      This is exactly where the paper invokes ω-closedness of [B_B]; in
      our encoding it amounts to showing
        [cone_sup_ball (n ↦ x + s_n ·: u) = x + (sup s_n) ·: u]
      for an admissible chain [s_n ↑ gauge_sup u], i.e. that the
      [cone_sup_ball] supremum commutes with the *scalar* limit.  The
      available [sup_ball_scaler] (basic_lemmas.v) commutes scaling with
      sup only for a *fixed* scalar; the varying-scalar version is a
      separate development.
    - The remaining norm axioms of [isCone] for [lc_norm]: (Normh) for
      [r > 0] (needs the rescaling identity
      [gauge_sup (r *: u) = gauge_sup u / r], a [sup]-image computation),
      (Normt) sub-additivity (the paper's [λ₁λ₂/(λ₁+λ₂)] estimate), and
      (Normc) ω-completeness (which needs the same scalar-limit lemma as
      the reach half).  Hence the [isCone] instance is NOT registered.
    - The measurability / integrability instances "inherited as in [B]"
      (paper §7.1, end): out of scope until the [isCone] instance lands.
*)
