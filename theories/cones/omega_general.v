(**md
   * General-radius suprema and Scott-continuity — foundation for §7

   The cone mixin (Normc) materialises completeness only for the *unit
   ball* [B_P]: [cone_sup_ball] takes an increasing chain bounded by
   [1]. The matching notion [is_omega_continuous] (paper §2.1,
   [basic_lemmas.v]) is therefore restricted to unit-ball chains in
   both input and output. For *linear* maps this is harmless — every
   bounded chain rescales into [B_P] — but for the *nonlinear* stable
   functions of §7 the rescaling argument no longer applies pointwise,
   so we need a genuinely radius-aware Scott-continuity notion.

   This file is purely ADDITIVE: it builds on top of [cone.v] and
   [basic_lemmas.v] without touching either.

   - [cone_sup_at M u …] : the supremum of a chain bounded by [M > 0],
     obtained by rescaling into [B_P], taking [cone_sup_ball], and
     scaling back. Its three characterising lemmas
     ([cone_sup_at_ub], [cone_sup_at_lub], [cone_sup_at_norm]) mirror
     the unit-ball ones; [cone_sup_at_ball] shows it extends
     [cone_sup_ball] (they agree at radius [1]).
   - [is_scott_continuous f] : commutation of [f] with [cone_sup_at]
     for chains of arbitrary positive radius. The bounds [M], [Mf] are
     passed as explicit arguments (see the design note at the
     definition) so downstream provers can supply them directly.
   - [linear_scott_of_omega] : the reusable bridge — a linear,
     [is_omega_continuous] map is [is_scott_continuous]. Proved once,
     via rescaling.
   - corollaries: addition (each argument), scaling, identity, and
     composition are [is_scott_continuous].
*)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference.

Require Import Icones.prelude.classical_extra.
Require Import Icones.prelude.nonneg_extra.
Require Import Icones.prelude.omegacpo.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.basic_lemmas.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(** ** The general-radius supremum [cone_sup_at]

    We carry the radius as [M : {nonneg R}] together with a strict
    positivity witness [0 < M%:num]; this keeps the [precone_scale]
    coercions definitional (scaling expects a [{nonneg R}]). The
    rescaling factor [1/M] is packaged as a [{nonneg R}] via
    [Mrec_nng] below. *)

Section ConeSupAt.
Variable R : realType.
Variable P : coneType R.
Implicit Types (x y : P).

(** The inverse [M%:num^-1] is non-negative whenever [0 < M%:num]. *)
Lemma Mrec_ge0 (M : {nonneg R}) : 0 < M%:num -> 0 <= (M%:num)^-1.
Proof. by move=> Mpos; rewrite invr_ge0 ltW. Qed.

(** The rescaling scalar [1/M : {nonneg R}]. *)
Definition Mrec_nng (M : {nonneg R}) (Mpos : 0 < M%:num) : {nonneg R} :=
  NngNum (Mrec_ge0 Mpos).

(** [M · (1/M) = 1] and [(1/M) · M = 1] at the level of [{nonneg R}]. *)
Lemma Mrec_mulV (M : {nonneg R}) (Mpos : 0 < M%:num) :
  M%:num * (Mrec_nng Mpos)%:num = 1.
Proof. by rewrite /= mulfV// gt_eqF. Qed.

Lemma Mrec_Vmul (M : {nonneg R}) (Mpos : 0 < M%:num) :
  (Mrec_nng Mpos)%:num * M%:num = 1.
Proof. by rewrite /= mulVf// gt_eqF. Qed.

(** Scaling by [M] then [1/M] (or vice versa) is the identity on [P]. *)
Lemma scale_MrecK (M : {nonneg R}) (Mpos : 0 < M%:num) x :
  precone_scale M (precone_scale (Mrec_nng Mpos) x) = x.
Proof.
rewrite -precone_scale_A.
have E : (M%:num * (Mrec_nng Mpos)%:num)%:nng = 1%:nng.
  by apply: val_inj; rewrite /= Mrec_mulV.
by rewrite E precone_scale_1.
Qed.

Lemma scale_MrecVK (M : {nonneg R}) (Mpos : 0 < M%:num) x :
  precone_scale (Mrec_nng Mpos) (precone_scale M x) = x.
Proof.
rewrite -precone_scale_A.
have E : ((Mrec_nng Mpos)%:num * M%:num)%:nng = 1%:nng.
  by apply: val_inj; rewrite /= Mrec_Vmul.
by rewrite E precone_scale_1.
Qed.

(** The rescaled chain [n ↦ (1/M) · uₙ] is increasing. *)
Lemma sup_at_rch (M : {nonneg R}) (u : nat -> P)
    (uch : forall n, precone_le (u n) (u n.+1)) :
  forall (Mpos : 0 < M%:num) n,
    precone_le (precone_scale (Mrec_nng Mpos) (u n))
               (precone_scale (Mrec_nng Mpos) (u n.+1)).
Proof. by move=> Mpos n; apply: precone_scale_le; exact: uch. Qed.

(** The rescaled chain lies in the unit ball when [‖uₙ‖ ≤ M]. *)
Lemma sup_at_rb1 (M : {nonneg R}) (u : nat -> P)
    (ubM : forall n, cone_norm (u n) <= M%:num) :
  forall (Mpos : 0 < M%:num) n,
    cone_norm (precone_scale (Mrec_nng Mpos) (u n)) <= 1.
Proof.
move=> Mpos n; rewrite cone_normh /=.
rewrite -(@ler_pM2l _ M%:num)// mulr1 mulrA mulfV ?gt_eqF// mul1r.
exact: ubM.
Qed.

(** The general-radius supremum: rescale the chain into [B_P], take the
    unit-ball supremum there, then scale back by [M]. *)
Definition cone_sup_at (M : {nonneg R}) (u : nat -> P)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ubM : forall n, cone_norm (u n) <= M%:num)
    (Mpos : 0 < M%:num) : P :=
  precone_scale M
    (cone_sup_ball (fun n => precone_scale (Mrec_nng Mpos) (u n))
       (sup_at_rch uch Mpos) (sup_at_rb1 ubM Mpos)).

(** [cone_sup_at] is an upper bound of the chain. *)
Lemma cone_sup_at_ub (M : {nonneg R}) (u : nat -> P)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ubM : forall n, cone_norm (u n) <= M%:num)
    (Mpos : 0 < M%:num) n :
  precone_le (u n) (cone_sup_at uch ubM Mpos).
Proof.
rewrite /cone_sup_at -[X in precone_le X _](scale_MrecK Mpos (u n)).
by apply: precone_scale_le; exact: cone_sup_ball_ub.
Qed.

(** [cone_sup_at] is the least upper bound of the chain. *)
Lemma cone_sup_at_lub (M : {nonneg R}) (u : nat -> P)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ubM : forall n, cone_norm (u n) <= M%:num)
    (Mpos : 0 < M%:num) y :
  (forall n, precone_le (u n) y) ->
  precone_le (cone_sup_at uch ubM Mpos) y.
Proof.
move=> uy; rewrite /cone_sup_at.
rewrite -[y](scale_MrecK Mpos y); apply: precone_scale_le.
apply: cone_sup_ball_lub => n.
by apply: precone_scale_le; exact: uy.
Qed.

(** The norm of [cone_sup_at] is bounded by the radius [M]. *)
Lemma cone_sup_at_norm (M : {nonneg R}) (u : nat -> P)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ubM : forall n, cone_norm (u n) <= M%:num)
    (Mpos : 0 < M%:num) :
  cone_norm (cone_sup_at uch ubM Mpos) <= M%:num.
Proof.
rewrite /cone_sup_at cone_normh -{2}[M%:num]mulr1.
by rewrite ler_pM2l//; exact: cone_sup_ball_norm.
Qed.

(** [cone_sup_at] is independent of the chosen radius: any two valid
    upper bounds [M], [M'] of the same chain produce the same supremum.
    This is immediate from the upper-bound / least-upper-bound
    characterisation, and is the technical engine behind the linear
    bridge (which rescales at a convenient common radius). *)
Lemma cone_sup_at_indep (M M' : {nonneg R}) (u : nat -> P)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ubM : forall n, cone_norm (u n) <= M%:num)
    (ubM' : forall n, cone_norm (u n) <= M'%:num)
    (Mpos : 0 < M%:num) (M'pos : 0 < M'%:num) :
  cone_sup_at uch ubM Mpos = cone_sup_at uch ubM' M'pos.
Proof.
apply: precone_le_anti.
- by apply: cone_sup_at_lub => n; exact: cone_sup_at_ub.
- by apply: cone_sup_at_lub => n; exact: cone_sup_at_ub.
Qed.

(** [cone_sup_at] genuinely extends [cone_sup_ball]: at radius [1] the
    two operators agree (for any unit-ball chain). *)
Lemma cone_sup_at_ball (u : nat -> P)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, cone_norm (u n) <= 1)
    (ubM : forall n, cone_norm (u n) <= (1%:nng : {nonneg R})%:num)
    (Mpos : 0 < (1%:nng : {nonneg R})%:num) :
  cone_sup_at uch ubM Mpos = cone_sup_ball u uch ub1.
Proof.
rewrite /cone_sup_at.
(* At [M = 1] the rescaling factor is [1], so both chains coincide. *)
have rE : Mrec_nng Mpos = 1%:nng.
  by apply: val_inj; rewrite /= invr1.
apply: precone_le_anti.
- rewrite -[X in (_ <=p X)%PC]precone_scale_1; apply: precone_scale_le.
  apply: cone_sup_ball_lub => n.
  by rewrite rE precone_scale_1; exact: cone_sup_ball_ub.
- rewrite precone_scale_1.
  apply: cone_sup_ball_lub => n.
  have un : u n = (Mrec_nng Mpos *: u n)%PC.
    by rewrite rE precone_scale_1.
  rewrite [X in (X <=p _)%PC]un.
  exact: (cone_sup_ball_ub (fun n => Mrec_nng Mpos *: u n)%PC).
Qed.

End ConeSupAt.

Arguments cone_sup_at {R P M u} uch ubM Mpos.

(** ** Radius-aware Scott-continuity

    Design note on the statement shape. We pass the radii [M], [Mf]
    and all chain side-conditions as *explicit arguments*, mirroring
    [is_omega_continuous] in [basic_lemmas.v]. This is deliberate:

    - Downstream provers (the §7 stable maps) construct the chains and
      their bounds locally and want to feed exactly those proofs in,
      rather than re-extracting an existentially-quantified bound.
    - It cleanly subsumes the unit-ball case — taking [M = Mf = 1] and
      using [cone_sup_at_ball] recovers a [cone_sup_ball] statement —
      so [linear_scott_of_omega] below can bridge to it.

    The image-chain hypotheses ([fuch], [fubMf]) are passed for the
    same [B_P → B_Q] reason documented at [is_omega_continuous]: a map
    increasing on a radius-[M] ball need not send it into the
    radius-[Mf] ball, so we cannot derive these from [f] alone. *)

Section ScottContinuous.
Variable R : realType.
Variables P Q : coneType R.

Definition is_scott_continuous (f : P -> Q) : Prop :=
  forall (M Mf : {nonneg R}) (u : nat -> P)
         (uch : forall n, precone_le (u n) (u n.+1))
         (ubM : forall n, cone_norm (u n) <= M%:num)
         (Mpos : 0 < M%:num)
         (fuch : forall n, precone_le (f (u n)) (f (u n.+1)))
         (fubMf : forall n, cone_norm (f (u n)) <= Mf%:num)
         (Mfpos : 0 < Mf%:num),
    f (cone_sup_at uch ubM Mpos) =
      cone_sup_at (u := f \o u) fuch fubMf Mfpos.

End ScottContinuous.

Arguments is_scott_continuous {R P Q}.

(** ** The linear lift: [is_omega_continuous] ⇒ [is_scott_continuous]

    The key reusable bridge. We rescale BOTH the input chain [u] and
    its image [f ∘ u] by a single common radius [K := max M Mf]: then
    [v := u/K] lands in [B_P] and [f ∘ v = (f ∘ u)/K] lands in [B_Q],
    so the OLD unit-ball ω-continuity applies to [v]. Linearity moves
    [f] through the outer [K]-scaling and through each [1/K], turning
    [f (K · sup_ball v)] into [K · sup_ball (f ∘ v) = cone_sup_at K
    (f ∘ u)]. Finally [cone_sup_at_indep] swaps the working radius [K]
    back to the user-supplied radii [M] (input) and [Mf] (output). *)

Section LinearScott.
Variable R : realType.
Variables P Q : coneType R.

Lemma linear_scott_of_omega (f : P -> Q) :
  is_linear f -> is_omega_continuous f -> is_scott_continuous f.
Proof.
move=> Hlin Hcont M Mf u uch ubM Mpos fuch fubMf Mfpos.
(* Common working radius [K = max M Mf], strictly positive. *)
have Kge0 : 0 <= Num.max M%:num Mf%:num by rewrite le_max nngnum_ge0.
pose K : {nonneg R} := NngNum Kge0.
have KM : M%:num <= K%:num by rewrite /= le_max lexx.
have KMf : Mf%:num <= K%:num by rewrite /= le_max lexx orbT.
have Kpos : 0 < K%:num by apply: lt_le_trans Mpos KM.
(* Both chains are bounded by [K]. *)
have ubK : forall n, cone_norm (u n) <= K%:num.
  by move=> n; apply: le_trans (ubM n) KM.
have fubK : forall n, cone_norm (f (u n)) <= K%:num.
  by move=> n; apply: le_trans (fubMf n) KMf.
(* Swap working radius to [K] on both sides via [cone_sup_at_indep]. *)
rewrite (cone_sup_at_indep uch ubM ubK Mpos Kpos).
rewrite (cone_sup_at_indep (u := f \o u) fuch fubMf fubK Mfpos Kpos).
rewrite {1}/cone_sup_at (basic_lemmas.linearZ Hlin).
(* Rescaled input chain [v := u/K] in [B_P]. *)
set v := fun n => precone_scale (Mrec_nng Kpos) (u n).
set vch := sup_at_rch uch Kpos.
set vb1 := sup_at_rb1 ubK Kpos.
(* Image chain [f ∘ v = (f ∘ u)/K] is increasing and in [B_Q]. *)
have fvch : forall n, precone_le ((f \o v) n) ((f \o v) n.+1).
  move=> n; rewrite /v /= !(basic_lemmas.linearZ Hlin).
  by apply: precone_scale_le; exact: fuch.
have fvb1 : forall n, cone_norm ((f \o v) n) <= 1.
  move=> n; rewrite /v /= (basic_lemmas.linearZ Hlin) cone_normh /=.
  rewrite -(@ler_pM2l _ K%:num)// mulr1 mulrA mulfV ?gt_eqF// mul1r.
  exact: fubK.
(* OLD unit-ball ω-continuity discharges the inner commutation. *)
rewrite (Hcont v vch vb1 fvch fvb1).
(* Goal: [K · sup_ball (f∘v)] = [cone_sup_at K (f∘u)]. The latter is
   [K · sup_ball ((f∘u)/K)]; since [f∘v = (f∘u)/K] pointwise, the two
   [cone_sup_ball]s coincide. *)
rewrite /cone_sup_at; congr (_ *: _)%PC.
apply: precone_le_anti.
- apply: cone_sup_ball_lub => n.
  have fvE : (f \o v) n = precone_scale (Mrec_nng Kpos) ((f \o u) n).
    by rewrite /v /= (basic_lemmas.linearZ Hlin).
  by rewrite fvE; exact: cone_sup_ball_ub.
- apply: cone_sup_ball_lub => n.
  have fvE : precone_scale (Mrec_nng Kpos) ((f \o u) n) = (f \o v) n.
    by rewrite /v /= (basic_lemmas.linearZ Hlin).
  by rewrite fvE; exact: cone_sup_ball_ub.
Qed.

End LinearScott.

Arguments linear_scott_of_omega {R P Q}.

(** ** Cone-operation corollaries

    The basic cone operations are [is_scott_continuous]. Scalar
    multiplication and the identity are linear, so they go through the
    [linear_scott_of_omega] bridge from their existing unit-ball
    proofs ([scaler_omega_continuous]); addition by a fixed element is
    *not* linear (it does not fix [0]), so we prove a dedicated
    general-radius commutation [sup_at_addr] (the radius-aware analogue
    of [sup_ball_addr]) and derive both one-sided variants from it. *)

Section Corollaries.
Variable R : realType.
Variable P : coneType R.
Implicit Types (x y : P) (r s : {nonneg R}).

(** Scalar multiplication [x ↦ r · x] is linear. *)
Lemma scale_is_linear r : is_linear (fun x : P => precone_scale r x).
Proof.
split.
- exact: precone_scale_0r.
- by move=> x y /=; rewrite precone_scale_DAr.
- move=> s x /=.
  rewrite -!precone_scale_A.
  by congr (_ *: _)%PC; apply: val_inj; rewrite /= mulrC.
Qed.

(** General-radius analogue of [sup_ball_addr] (single working radius
    [K] bounding both [u] and [u + y]). The supremum of the translated
    chain is the translate of the supremum. *)
Lemma sup_at_addr (K : {nonneg R}) (u : nat -> P) (y : P)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ubK : forall n, cone_norm (u n) <= K%:num)
    (auch : forall n,
       precone_le (precone_add (u n) y) (precone_add (u n.+1) y))
    (aubK : forall n, cone_norm (precone_add (u n) y) <= K%:num)
    (Kpos : 0 < K%:num) :
  cone_sup_at auch aubK Kpos = precone_add (cone_sup_at uch ubK Kpos) y.
Proof.
set s  := cone_sup_at auch aubK Kpos.
set su := cone_sup_at uch ubK Kpos.
have Dir1 : precone_le s (precone_add su y).
  apply: cone_sup_at_lub => n.
  by apply: precone_add_le_r; exact: cone_sup_at_ub.
have Dir2 : precone_le (precone_add su y) s.
  have wsex : forall n, exists w, s = precone_add (precone_add (u n) y) w.
    by move=> n; have := cone_sup_at_ub auch aubK Kpos n.
  pose ws (n : nat) : P := projT1 (cid (wsex n)).
  have ws_eq : forall n, s = precone_add (precone_add (u n) y) (ws n).
    by move=> n; exact: projT2 (cid (wsex n)).
  have u_w_const : forall n,
      precone_add (u n) (ws n) = precone_add (u 0) (ws 0).
    move=> n.
    have H0 : s = precone_add (precone_add (u 0) (ws 0)) y.
      by rewrite (ws_eq 0) -precone_addA (precone_addC y (ws 0)) precone_addA.
    have Hn : s = precone_add (precone_add (u n) (ws n)) y.
      by rewrite (ws_eq n) -precone_addA (precone_addC y (ws n)) precone_addA.
    have HH : precone_add (precone_add (u 0) (ws 0)) y =
              precone_add (precone_add (u n) (ws n)) y.
      by rewrite -H0.
    by symmetry; apply: precone_cancelr HH.
  have Hu_bnd : forall n, precone_le (u n) (precone_add (u 0) (ws 0)).
    by move=> n; rewrite -(u_w_const n); exists (ws n).
  have [z Hz] : precone_le su (precone_add (u 0) (ws 0)).
    by apply: cone_sup_at_lub.
  exists z.
  rewrite (ws_eq 0).
  rewrite -[in LHS]precone_addA (precone_addC y (ws 0)) precone_addA.
  rewrite Hz.
  rewrite -[in RHS]precone_addA (precone_addC y z) precone_addA //.
by apply: precone_le_anti.
Qed.

(** Addition by a fixed [y] on the right is Scott-continuous. *)
Lemma addr_scott_continuous (y : P) :
  is_scott_continuous (fun x : P => precone_add x y).
Proof.
move=> M Mf u uch ubM Mpos fuch fubMf Mfpos.
have Kge0 : 0 <= Num.max M%:num Mf%:num by rewrite le_max nngnum_ge0.
pose K : {nonneg R} := NngNum Kge0.
have KM : M%:num <= K%:num by rewrite /= le_max lexx.
have KMf : Mf%:num <= K%:num by rewrite /= le_max lexx orbT.
have Kpos : 0 < K%:num by apply: lt_le_trans Mpos KM.
have ubK : forall n, cone_norm (u n) <= K%:num.
  by move=> n; apply: le_trans (ubM n) KM.
have aubK : forall n, cone_norm (precone_add (u n) y) <= K%:num.
  by move=> n; apply: le_trans (fubMf n) KMf.
rewrite (cone_sup_at_indep uch ubM ubK Mpos Kpos).
rewrite (cone_sup_at_indep (u := fun n => precone_add (u n) y)
  fuch fubMf aubK Mfpos Kpos).
by symmetry; exact: (sup_at_addr uch ubK fuch aubK Kpos).
Qed.

(** Addition by a fixed [x] on the left is Scott-continuous. *)
Lemma addl_scott_continuous (x : P) :
  is_scott_continuous (fun y : P => precone_add x y).
Proof.
move=> M Mf u uch ubM Mpos fuch fubMf Mfpos.
have Kge0 : 0 <= Num.max M%:num Mf%:num by rewrite le_max nngnum_ge0.
pose K : {nonneg R} := NngNum Kge0.
have KM : M%:num <= K%:num by rewrite /= le_max lexx.
have KMf : Mf%:num <= K%:num by rewrite /= le_max lexx orbT.
have Kpos : 0 < K%:num by apply: lt_le_trans Mpos KM.
have ubK : forall n, cone_norm (u n) <= K%:num.
  by move=> n; apply: le_trans (ubM n) KM.
have aubK : forall n, cone_norm (precone_add (u n) x) <= K%:num.
  by move=> n; rewrite precone_addC; apply: le_trans (fubMf n) KMf.
have auch : forall n,
    precone_le (precone_add (u n) x) (precone_add (u n.+1) x).
  by move=> n; rewrite -!(precone_addC x); exact: fuch.
rewrite (cone_sup_at_indep uch ubM ubK Mpos Kpos).
rewrite (cone_sup_at_indep (u := fun n => precone_add x (u n))
  fuch fubMf (fun n => le_trans (fubMf n) KMf) Mfpos Kpos).
have swap : cone_sup_at fuch (fun n => le_trans (fubMf n) KMf) Kpos
          = cone_sup_at auch aubK Kpos.
  apply: precone_le_anti.
  - apply: cone_sup_at_lub => n.
    by rewrite (precone_addC x (u n)); exact: cone_sup_at_ub.
  - apply: cone_sup_at_lub => n.
    by rewrite (precone_addC (u n) x); exact: cone_sup_at_ub.
rewrite swap (sup_at_addr uch ubK auch aubK Kpos).
by rewrite precone_addC.
Qed.

(** Scalar multiplication is Scott-continuous (via the linear bridge). *)
Lemma scaler_scott_continuous (r : {nonneg R}) :
  is_scott_continuous (fun x : P => precone_scale r x).
Proof.
apply: linear_scott_of_omega; first exact: scale_is_linear.
exact: scaler_omega_continuous.
Qed.

(** The identity is linear, ω-continuous, hence Scott-continuous. *)
Lemma id_is_linear : is_linear (@id P).
Proof. by split. Qed.

Lemma id_omega_continuous : is_omega_continuous (@id P).
Proof.
move=> u uch ub1 fuch fub1.
congr (cone_sup_ball _ _ _); exact: Prop_irrelevance.
Qed.

Lemma id_scott_continuous : is_scott_continuous (@id P).
Proof.
apply: linear_scott_of_omega; first exact: id_is_linear.
exact: id_omega_continuous.
Qed.

End Corollaries.

Arguments scale_is_linear {R P}.
Arguments addr_scott_continuous {R P}.
Arguments addl_scott_continuous {R P}.
Arguments scaler_scott_continuous {R P}.
Arguments id_scott_continuous {R P}.

(** Closure under composition. Because [is_scott_continuous f] takes
    the image-chain bounds as side conditions, the composite [g ∘ f]
    needs to know that [f] sends a bounded increasing chain to a
    bounded increasing chain; we pass that as the hypothesis [Hbound]
    (it holds e.g. when [f] is linear, by [linmap_bounded]). *)
Section Composition.
Variable R : realType.
Variables P Q S : coneType R.

Lemma comp_scott_continuous (f : P -> Q) (g : Q -> S) :
  is_scott_continuous f -> is_scott_continuous g ->
  (forall (u : nat -> P) (M : {nonneg R}),
     (forall n, precone_le (u n) (u n.+1)) ->
     (forall n, cone_norm (u n) <= M%:num) -> 0 < M%:num ->
     exists Mf : {nonneg R},
       (forall n, precone_le (f (u n)) (f (u n.+1))) /\
       (forall n, cone_norm (f (u n)) <= Mf%:num) /\ 0 < Mf%:num) ->
  is_scott_continuous (g \o f).
Proof.
move=> Hf Hg Hbound M Mg u uch ubM Mpos gfuch gfubMg Mgpos.
have [Mf [fuch [fubMf Mfpos]]] := Hbound u M uch ubM Mpos.
rewrite /comp/= (Hf M Mf u uch ubM Mpos fuch fubMf Mfpos).
rewrite (Hg Mf Mg (f \o u) fuch fubMf Mfpos).
apply: cone_sup_at_indep.
Qed.

End Composition.

Arguments comp_scott_continuous {R P Q S}.
