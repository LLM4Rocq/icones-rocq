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

   This file builds on top of [cone.v] and [basic_lemmas.v]; the only
   thing it asks of the latter is the abstract translation-of-a-sup
   engine [precone_sup_addr] (shared with [sup_ball_addr]).

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
   - the *consolidated sup-calculus* (last section of the file): the
     supremum facts that used to be re-proved, in escalating
     generality, in [homs/linhom.v], [homs/bilin.v],
     [stable/totmono.v], [stable/stablehom.v], [stable/findiff.v],
     [stable/scones_ccc.v] and [programs/ex_reject_headline.v] —
     chain monotonicity, proof-irrelevance of the ball sup, the
     diagonal (binary) sup-addition identity, the iterated-(Normt)
     bound [cone_norm_sum], the finite-sum sup
     lemmas, the two-sup swap and the scaling chain — each stated
     once, at a general radius where the copies generalise, with the
     radius-1 corollaries in the shape the consumers use.
*)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference archimedean.

Require Import Icones.prelude.nonneg_extra.
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
    chain is the translate of the supremum.  Like [sup_ball_addr], an
    instance of the shared engine [precone_sup_addr]
    ([basic_lemmas.v]): only the upper-bound / least-upper-bound
    characterisation of the two suprema is used. *)
Lemma sup_at_addr (K : {nonneg R}) (u : nat -> P) (y : P)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ubK : forall n, cone_norm (u n) <= K%:num)
    (auch : forall n,
       precone_le (precone_add (u n) y) (precone_add (u n.+1) y))
    (aubK : forall n, cone_norm (precone_add (u n) y) <= K%:num)
    (Kpos : 0 < K%:num) :
  cone_sup_at auch aubK Kpos = precone_add (cone_sup_at uch ubK Kpos) y.
Proof.
apply: (precone_sup_addr (u := u)).
- exact: cone_sup_at_ub.
- exact: cone_sup_at_lub.
- exact: (cone_sup_at_ub auch aubK Kpos).
- exact: (cone_sup_at_lub auch aubK Kpos).
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

(** ** Consolidated sup-calculus

    The handful of supremum facts below had been re-proved, in
    escalating generality, all over the development:

    - diagonal (binary) sup-addition: [homs/linhom.v] (Sections
      [DiagonalSup] / [DiagonalSupEq], radius 1) and
      [stable/totmono.v] (Section [DiagonalSup]: an acknowledged port
      of the former, at radius 1 *and* at a general radius);
    - finite-sum sups: [stable/stablehom.v] (Sections [SumSup] /
      [AddlSumConeSup], radius 1) and [stable/findiff.v] (Section
      [SumSupAt], general radius — the most general copy);
    - the two-sup swap: [homs/linhom.v] ([cone_sup_ball_swap]) and
      [stable/stablehom.v] ([sh_sup_swap], whose comment records that
      it duplicates the former "to avoid a dependency");
    - proof-irrelevance of the ball sup: three verbatim copies of
      [cone_sup_ball_irr] in [homs/bilin.v], [stable/scones_ccc.v]
      and [programs/ex_reject_headline.v];
    - chain monotonicity ([n ≤ m → uₙ ≤p u_m]): inline [have]s in
      [homs/linhom.v] and twice in [stable/totmono.v];
    - the scaling chain [m ↦ λₘ ·: z] and its supremum:
      [stable/findiff.v] (Section [ScaleChain]).

    Everything is stated here ONCE, over a bare [coneType R] and at a
    GENERAL radius wherever the copies generalise, together with the
    radius-1 ([cone_sup_ball]) corollaries in exactly the shape the
    consumers use — so migrating a consumer is a name swap, not a
    proof rewrite.  Each statement notes the copies it subsumes. *)

Section ConsolidatedChain.
Variable R : realType.
Local Open Scope precone_scope.

(** Chain monotonicity for the cone order: an increasing chain is
    monotone in its index.  Subsumes [chain_mono_a] / [chain_mono_b]
    (linhom.v, [cone_sup_ball_addD_ge]) and the two local [chain_mono]
    haves of totmono.v ([sup_ball_addD], [sup_at_addD]). *)
Lemma precone_chain_le (P : preconeType R) (u : nat -> P)
    (uch : forall n, u n <=p u n.+1) (n m : nat) :
  (n <= m)%N -> u n <=p u m.
Proof.
elim: m => [|m IHm] nm.
  by move: nm; rewrite leqn0 => /eqP ->; exact: precone_le_refl.
case: (leqP n m) => Hk.
  by apply: precone_le_trans (IHm Hk) _; exact: uch.
have -> : n = m.+1 by apply/eqP; rewrite eqn_leq nm Hk.
exact: precone_le_refl.
Qed.

End ConsolidatedChain.

Arguments precone_chain_le {R P u} uch {n m}.

Section ConsolidatedSupCalculus.
Variable R : realType.
Variable P : coneType R.
Implicit Types (a b u : nat -> P) (x y : P).
Local Open Scope precone_scope.

(** *** Proof-irrelevance and the radius-1 bridge *)

(** The ball supremum depends only on the chain, not on the
    chain/bound witnesses.  Subsumes the three verbatim copies
    [cone_sup_ball_irr] of [homs/bilin.v], [stable/scones_ccc.v] and
    [programs/ex_reject_headline.v]. *)
Lemma cone_sup_ball_irr u
    (c1 c2 : forall n, u n <=p u n.+1)
    (b1 b2 : forall n, cone_norm (u n) <= 1) :
  cone_sup_ball u c1 b1 = cone_sup_ball u c2 b2.
Proof.
by apply: precone_le_anti; apply: cone_sup_ball_lub => n;
   exact: cone_sup_ball_ub.
Qed.

(** [1] is a legitimate radius. *)
Lemma nng1_pos : (0 < (1%:nng : {nonneg R})%:num)%R.
Proof. by rewrite /= ltr01. Qed.

(** The ball supremum IS the radius-1 [cone_sup_at]: the [<= 1] form
    of the bound hypothesis, ready for [rewrite].  (Repackaging of
    [cone_sup_at_ball]; the two are interchangeable but this
    orientation is the one the radius-1 corollaries below need.) *)
Lemma cone_sup_ball_atE u
    (uch : forall n, u n <=p u n.+1)
    (ub1 : forall n, cone_norm (u n) <= 1)
    (ubM : forall n, cone_norm (u n) <= (1%:nng : {nonneg R})%:num) :
  cone_sup_ball u uch ub1 = cone_sup_at uch ubM nng1_pos.
Proof. by rewrite (cone_sup_at_ball uch ub1 ubM nng1_pos). Qed.

(** *** Diagonal (binary) sup-addition *)

(** General radius: for chains [a], [b] and their diagonal sum all
    bounded by a common radius [M > 0], the supremum of the diagonal
    sum is the sum of the suprema.  Subsumes [sup_at_addD]
    (totmono.v, Section [DiagonalSup]). *)
Lemma cone_sup_at_addD (M : {nonneg R}) a b
  (ach : forall n, a n <=p a n.+1)
  (aubM : forall n, cone_norm (a n) <= M%:num)
  (bch : forall n, b n <=p b n.+1)
  (bubM : forall n, cone_norm (b n) <= M%:num)
  (sch : forall n, a n + b n <=p a n.+1 + b n.+1)
  (subM : forall n, cone_norm (a n + b n) <= M%:num)
  (Mpos : (0 < M%:num)%R) :
  cone_sup_at sch subM Mpos =
  cone_sup_at ach aubM Mpos + cone_sup_at bch bubM Mpos.
Proof.
set Sa := cone_sup_at ach aubM Mpos.
set Sb := cone_sup_at bch bubM Mpos.
set Ss := cone_sup_at sch subM Mpos.
apply: precone_le_anti.
  (* [Ss ≤p Sa + Sb] by [cone_sup_at_lub] with witnesses from the ubs. *)
  apply: cone_sup_at_lub => n.
  have [za Hza] : a n <=p Sa by exact: cone_sup_at_ub.
  have [zb Hzb] : b n <=p Sb by exact: cone_sup_at_ub.
  exists (za + zb); rewrite Hza Hzb -!precone_addA; congr precone_add.
  by rewrite precone_addA [za + b n]precone_addC -precone_addA.
(* Step 1: [a_n + b_k ≤p Ss] for all [n], [k]. *)
have ab_le_Ss n k : a n + b k <=p Ss.
  set m := maxn n k.
  apply: precone_le_trans (cone_sup_at_ub sch subM Mpos m).
  apply: (@precone_le_trans _ _ (a m + b k)).
    by apply: precone_add_le_r; exact: (precone_chain_le ach (leq_maxl n k)).
  by apply: precone_add_le_l; exact: (precone_chain_le bch (leq_maxr n k)).
(* [(a_n + b_k)_n] increasing and bounded by [M]. *)
have ch_ak_bk k n : a n + b k <=p a n.+1 + b k.
  by apply: precone_add_le_r; exact: ach.
have ub_ak_bk k n : cone_norm (a n + b k) <= M%:num.
  by apply: le_trans (cone_normp _ _ (ab_le_Ss n k)) _;
     exact: cone_sup_at_norm.
(* Step 2/3: [Sa + b_k ≤p Ss] for all [k]. *)
have Sa_bk_le_Ss k : Sa + b k <=p Ss.
  rewrite -(sup_at_addr ach aubM (ch_ak_bk k) (ub_ak_bk k) Mpos).
  by apply: cone_sup_at_lub => n; exact: ab_le_Ss.
(* [(b_k + Sa)_k] increasing and bounded by [M]. *)
have ch_bk_Sa k : b k + Sa <=p b k.+1 + Sa.
  by apply: precone_add_le_r; exact: bch.
have ub_bk_Sa k : cone_norm (b k + Sa) <= M%:num.
  rewrite precone_addC.
  by apply: le_trans (cone_normp _ _ (Sa_bk_le_Ss k)) _;
     exact: cone_sup_at_norm.
(* Step 4/5: [Sa + Sb ≤p Ss] via [sup_at_addr] on [b] with [y := Sa]. *)
rewrite -[Sa + Sb]/(Sa + Sb) precone_addC.
rewrite -(sup_at_addr bch bubM ch_bk_Sa ub_bk_Sa Mpos).
apply: cone_sup_at_lub => k.
by rewrite precone_addC; exact: Sa_bk_le_Ss.
Qed.

(** Radius 1.  Subsumes [cone_sup_ball_addD] (linhom.v, Section
    [DiagonalSupEq]) and [sup_ball_addD] (totmono.v). *)
Lemma cone_sup_ball_addD a b
  (ach : forall n, a n <=p a n.+1)
  (aub : forall n, cone_norm (a n) <= 1)
  (bch : forall n, b n <=p b n.+1)
  (bub : forall n, cone_norm (b n) <= 1)
  (sch : forall n, a n + b n <=p a n.+1 + b n.+1)
  (sub : forall n, cone_norm (a n + b n) <= 1) :
  cone_sup_ball (fun n => a n + b n) sch sub =
  cone_sup_ball a ach aub + cone_sup_ball b bch bub.
Proof.
rewrite (cone_sup_ball_atE ach aub aub) (cone_sup_ball_atE bch bub bub).
rewrite (cone_sup_ball_atE sch sub sub).
exact: cone_sup_at_addD.
Qed.

(** The two halves, in the shape linhom.v states them. *)
Lemma cone_sup_ball_addD_le a b
  (ach : forall n, a n <=p a n.+1)
  (aub : forall n, cone_norm (a n) <= 1)
  (bch : forall n, b n <=p b n.+1)
  (bub : forall n, cone_norm (b n) <= 1)
  (sch : forall n, a n + b n <=p a n.+1 + b n.+1)
  (sub : forall n, cone_norm (a n + b n) <= 1) :
  cone_sup_ball (fun n => a n + b n) sch sub <=p
  cone_sup_ball a ach aub + cone_sup_ball b bch bub.
Proof.
by rewrite (cone_sup_ball_addD ach aub bch bub sch sub); exact: precone_le_refl.
Qed.

Lemma cone_sup_ball_addD_ge a b
  (ach : forall n, a n <=p a n.+1)
  (aub : forall n, cone_norm (a n) <= 1)
  (bch : forall n, b n <=p b n.+1)
  (bub : forall n, cone_norm (b n) <= 1)
  (sch : forall n, a n + b n <=p a n.+1 + b n.+1)
  (sub : forall n, cone_norm (a n + b n) <= 1) :
  cone_sup_ball a ach aub + cone_sup_ball b bch bub <=p
  cone_sup_ball (fun n => a n + b n) sch sub.
Proof.
by rewrite (cone_sup_ball_addD ach aub bch bub sch sub); exact: precone_le_refl.
Qed.

(** *** Commutation of two suprema *)

(** The iterated unit-ball supremum of a doubly-indexed family
    commutes.  Subsumes [cone_sup_ball_swap] (linhom.v, Section
    [LinhomSupCont]) and its copy [sh_sup_swap] (stablehom.v, Section
    [ConeSupBallSwap]). *)
Lemma cone_sup_ball_swap (b : nat -> nat -> P)
    (b_row_ch : forall k n, b n k <=p b n.+1 k)
    (b_col_ch : forall n k, b n k <=p b n k.+1)
    (b_ub : forall n k, cone_norm (b n k) <= 1)
    (b_col_sup_ub : forall n,
       cone_norm (cone_sup_ball (b n) (b_col_ch n) (fun k => b_ub n k))
       <= 1)
    (b_col_sup_ch : forall n,
       cone_sup_ball (b n) (b_col_ch n) (fun k => b_ub n k) <=p
       cone_sup_ball (b n.+1) (b_col_ch n.+1) (fun k => b_ub n.+1 k))
    (b_row_sup_ub : forall k,
       cone_norm (cone_sup_ball (b^~ k) (b_row_ch k) (fun n => b_ub n k))
       <= 1)
    (b_row_sup_ch : forall k,
       cone_sup_ball (b^~ k) (b_row_ch k) (fun n => b_ub n k) <=p
       cone_sup_ball (b^~ k.+1) (b_row_ch k.+1) (fun n => b_ub n k.+1)) :
  cone_sup_ball
    (fun n => cone_sup_ball (b n) (b_col_ch n) (fun k => b_ub n k))
    b_col_sup_ch b_col_sup_ub =
  cone_sup_ball
    (fun k => cone_sup_ball (b^~ k) (b_row_ch k) (fun n => b_ub n k))
    b_row_sup_ch b_row_sup_ub.
Proof.
apply: precone_le_anti.
- apply: cone_sup_ball_lub => n; apply: cone_sup_ball_lub => k.
  have step1 : b n k <=p
      cone_sup_ball (b^~ k) (b_row_ch k) (fun n0 => b_ub n0 k).
    exact: cone_sup_ball_ub.
  apply: precone_le_trans step1 _; exact: cone_sup_ball_ub.
- apply: cone_sup_ball_lub => k; apply: cone_sup_ball_lub => n.
  have step1 : b n k <=p
      cone_sup_ball (b n) (b_col_ch n) (fun k0 => b_ub n k0).
    exact: cone_sup_ball_ub.
  apply: precone_le_trans step1 _; exact: cone_sup_ball_ub.
Qed.

End ConsolidatedSupCalculus.

Arguments cone_sup_ball_irr {R P} u {c1 c2 b1 b2}.
Arguments nng1_pos {R}.
Arguments cone_sup_ball_swap {R P}.

(** *** Finite sums of chains, at a general radius

    The diagonal sum [Σ_{i∈A} c i n] of finitely many chains escapes
    the unit ball (it sums up to [#|A|] terms of radius [M]), so its
    supremum is taken with [cone_sup_at] at the radius
    [(#|A|+1)·M].  Subsumes Section [SumSupAt] of [stable/findiff.v]
    (the most general copy) and, at [M = 1], Section [SumSup] of
    [stable/stablehom.v]. *)

(** The finite sums below are [bigop]s over [precone_add] /
    [precone_zero]; the [{set T}]-indexed [bigop] lemmas
    ([big_setU1], [big_set0], …) need that pair registered as a
    commutative monoid law.  This is the *unique* declaration site: it
    used to live in [stable/totmono.v] (Section [PreconeBig]), which
    now only keeps the [\sumP_(...)] notation alias. *)
Section PreconeComLaw.
Variable R : realType.
Variable P : preconeType R.

HB.instance Definition _ :=
  Monoid.isComLaw.Build P precone_zero precone_add
    (@precone_addA R P) (@precone_addC R P) (@precone_add0 R P).

End PreconeComLaw.

(** Iterated (Normt).  The cone-norm of a finite cone-sum is bounded by
    the sum of the norms of its terms.  This is a *pure* (Normt) fact:
    no chain, no uniform bound, no finiteness of the index type — every
    [#|A|·M]-style estimate below is an instantiation of it, as is the
    radius-1 [sumsup_chain_norm_le] of [stable/stablehom.v]. *)
Lemma cone_norm_sum (R : realType) (P : coneType R)
    (I : Type) (r : seq I) (Q : pred I) (u : I -> P) :
  cnorm (\big[precone_add/precone_zero]_(i <- r | Q i) u i)
    <= \sum_(i <- r | Q i) cnorm (u i).
Proof.
elim/big_rec2: _ => [|i y1 y2 _ Hy]; first by rewrite cone_norm0.
by apply: le_trans (cone_normt _ _) _; rewrite lerD.
Qed.

Section ConsolidatedSumSupAt.
Local Open Scope precone_scope.
Variable R : realType.
Variable P : coneType R.
Variable T : finType.
Variable c : T -> nat -> P.
Variable M : {nonneg R}.
Hypothesis cch : forall i n, c i n <=p c i n.+1.
Hypothesis cubM : forall i n, cone_norm (c i n) <= M%:num.
Hypothesis Mpos : (0 < M%:num)%R.

(** Per-index supremum [cone_sum_sup i = sup_n (c i n)]. *)
Definition cone_sum_sup (i : T) : P := cone_sup_at (cch i) (cubM i) Mpos.

(** The diagonal sum chain over a finite index set [A]. *)
Definition cone_sum_chain (A : {set T}) (n : nat) : P :=
  \big[precone_add/precone_zero]_(i in A) c i n.

(** The diagonal sum chain is [≤p]-increasing. *)
Lemma cone_sum_chain_ch (A : {set T}) n :
  cone_sum_chain A n <=p cone_sum_chain A n.+1.
Proof.
rewrite /cone_sum_chain; elim/big_rec2: _; first exact: precone_le_refl.
move=> i y1 y2 _ Hy; apply: precone_le_trans (precone_add_le_r _ (cch i n)).
exact: precone_add_le_l.
Qed.

(** Norm of the diagonal sum: [≤ #|A| · M] (iterated (Normt)). *)
Lemma cone_sum_chain_norm (A : {set T}) n :
  cone_norm (cone_sum_chain A n) <= (#|A|%:R * M%:num)%R.
Proof.
rewrite /cone_sum_chain.
have -> : (#|A|%:R * M%:num)%R = (\sum_(i in A) M%:num)%R.
  by rewrite sumr_const mulr_natl.
apply: le_trans (cone_norm_sum _ _ _) _.
by apply: ler_sum => i _; exact: cubM.
Qed.

(** A strictly-positive radius dominating [#|A| · M]: take [(#|A|+1)·M]. *)
Lemma cone_sum_radius_ge0 (A : {set T}) : (0 <= #|A|.+1%:R * M%:num :> R)%R.
Proof. by rewrite mulr_ge0 ?ler0n// ltW. Qed.

Definition cone_sum_radius (A : {set T}) : {nonneg R} :=
  NngNum (cone_sum_radius_ge0 A).

Lemma cone_sum_radius_pos (A : {set T}) : (0 < (cone_sum_radius A)%:num)%R.
Proof. by rewrite /cone_sum_radius/= mulr_gt0 ?ltr0n. Qed.

Lemma cone_sum_chain_radius (A : {set T}) n :
  cone_norm (cone_sum_chain A n) <= (cone_sum_radius A)%:num.
Proof.
apply: le_trans (cone_sum_chain_norm A n) _.
by rewrite /cone_sum_radius/= ler_wpM2r ?ltW// ltr_nat.
Qed.

(** Every diagonal element is below the finite sum of the per-index
    suprema.  Subsumes [dsum_ub] (findiff.v) and [sum_cone_sup_ub]
    (stablehom.v). *)
Lemma cone_sum_sup_ub (A : {set T}) n :
  cone_sum_chain A n <=p
  \big[precone_add/precone_zero]_(i in A) cone_sum_sup i.
Proof.
rewrite /cone_sum_chain; elim/big_rec2: _; first exact: precone_le_refl.
move=> i y1 y2 _ Hy.
apply: (precone_le_trans (y := cone_sum_sup i + y2)).
  by apply: precone_add_le_r; exact: cone_sup_at_ub.
by apply: precone_add_le_l.
Qed.

(** **Lub direction.** The finite sum of per-index suprema is the
    *least* upper bound of the diagonal chain.  Cardinality induction
    on [A]: each [a |: A'] step pulls out [cone_sum_sup a] via
    [big_setU1], reads the [A']-sum as a [cone_sup_at] (induction
    hypothesis), and recombines with the binary diagonal-sup identity
    [cone_sup_at_addD] at the common radius.  Subsumes [dsum_lub]
    (findiff.v) and [sum_cone_sup_lub] (stablehom.v). *)
Lemma cone_sum_sup_lub (A : {set T}) (y : P) :
  (forall n, cone_sum_chain A n <=p y) ->
  \big[precone_add/precone_zero]_(i in A) cone_sum_sup i <=p y.
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
have splitE n : cone_sum_chain A n = c a n + cone_sum_chain A' n.
  by rewrite /cone_sum_chain {1}AE (big_setU1 _ aA').
set Mb : {nonneg R} := cone_sum_radius A.
have Mbpos := cone_sum_radius_pos A.
have ca_ubMb n : cone_norm (c a n) <= Mb%:num.
  apply: le_trans (cubM a n) _; rewrite /Mb/= ler_peMl ?ltW//.
  by rewrite ltr1n ltnS card_gt0; apply/set0Pn; exists a.
have sumA'_ubMb n : cone_norm (cone_sum_chain A' n) <= Mb%:num.
  apply: le_trans (cone_sum_chain_norm A' n) _.
  rewrite /Mb/= ler_wpM2r ?ltW//.
  by rewrite ltr_nat ltnS; apply: subset_leq_card; exact: subsetDl.
have dch n : c a n + cone_sum_chain A' n <=p
             c a n.+1 + cone_sum_chain A' n.+1.
  apply: precone_le_trans (precone_add_le_r _ (cch a n)).
  exact: precone_add_le_l (cone_sum_chain_ch A' n).
have dubMb n : cone_norm (c a n + cone_sum_chain A' n) <= Mb%:num.
  by rewrite -splitE; exact: cone_sum_chain_radius.
(* [cone_sum_sup a] read at the working radius [Mb]. *)
have caE : cone_sum_sup a = cone_sup_at (cch a) ca_ubMb Mbpos.
  by rewrite /cone_sum_sup; apply: cone_sup_at_indep.
(* The [A']-sum is the [cone_sup_at] of its diagonal chain (via IH). *)
have sumA'E : \big[precone_add/precone_zero]_(i in A') cone_sum_sup i =
              cone_sup_at (cone_sum_chain_ch A') sumA'_ubMb Mbpos.
  apply: precone_le_anti.
  - by apply: IH => // n; exact: cone_sup_at_ub.
  - by apply: cone_sup_at_lub => n; exact: cone_sum_sup_ub.
rewrite AE (big_setU1 _ aA') caE sumA'E.
have key : cone_sup_at (cch a) ca_ubMb Mbpos
           + cone_sup_at (cone_sum_chain_ch A') sumA'_ubMb Mbpos
         = cone_sup_at dch dubMb Mbpos.
  by rewrite (cone_sup_at_addD (cch a) ca_ubMb (cone_sum_chain_ch A')
       sumA'_ubMb dch dubMb).
change (precone_add (cone_sup_at (cch a) ca_ubMb Mbpos)
          (cone_sup_at (cone_sum_chain_ch A') sumA'_ubMb Mbpos) <=p y).
rewrite key; apply: cone_sup_at_lub => n.
by apply: precone_le_trans (Hy n); rewrite splitE; exact: precone_le_refl.
Qed.

(** The finite sum of per-index suprema IS the supremum of the
    diagonal chain.  Subsumes [sum_cone_sup_eq] (stablehom.v, up to
    the choice of radius). *)
Lemma cone_sum_sup_eq (A : {set T}) :
  \big[precone_add/precone_zero]_(i in A) cone_sum_sup i =
  cone_sup_at (cone_sum_chain_ch A) (cone_sum_chain_radius A)
              (cone_sum_radius_pos A).
Proof.
apply: precone_le_anti.
- by apply: cone_sum_sup_lub => m; exact: cone_sup_at_ub.
- by apply: cone_sup_at_lub => m; exact: cone_sum_sup_ub.
Qed.

(** Adding a constant on the left commutes with the finite-sum sup:
    [Z + Σ_A sup] is the lub of [(Z + diagonal chain)].  Subsumes
    [addl_sum_cone_sup_lub] (stablehom.v). *)
Lemma cone_sum_sup_addl_lub (A : {set T}) (Z V : P) :
  (forall m, Z + cone_sum_chain A m <=p V) ->
  Z + \big[precone_add/precone_zero]_(i in A) cone_sum_sup i <=p V.
Proof.
move=> HZ; rewrite cone_sum_sup_eq.
set Apos := cone_sum_radius_pos A.
set ch := cone_sum_chain_ch A.
set ub := cone_sum_chain_radius A.
have azch m : cone_sum_chain A m + Z <=p cone_sum_chain A m.+1 + Z.
  by apply: precone_add_le_r; exact: ch.
have Kge0 : (0 <= (cone_sum_radius A)%:num + cone_norm Z)%R.
  by apply: addr_ge0; [exact: nngnum_ge0 | exact: cone_norm_ge0].
pose K : {nonneg R} := NngNum Kge0.
have Kpos : (0 < K%:num)%R.
  by apply: lt_le_trans Apos _; rewrite /= lerDl cone_norm_ge0.
have azub m : cone_norm (cone_sum_chain A m + Z) <= K%:num.
  by apply: le_trans (cone_normt _ _) _; rewrite /= lerD2r; exact: ub.
have ubK m : cone_norm (cone_sum_chain A m) <= K%:num.
  by apply: le_trans (ub m) _; rewrite /= lerDl cone_norm_ge0.
rewrite (cone_sup_at_indep ch ub ubK Apos Kpos) precone_addC.
rewrite -(sup_at_addr ch ubK azch azub Kpos).
by apply: cone_sup_at_lub => m; rewrite precone_addC; exact: HZ.
Qed.

End ConsolidatedSumSupAt.

Arguments cone_sum_sup {R P T} c {M} cch cubM Mpos i.
Arguments cone_sum_chain {R P T} c A n.
Arguments cone_sum_sup_ub {R P T c M} cch cubM Mpos A n.
Arguments cone_sum_sup_lub {R P T c M} cch cubM Mpos A y.
Arguments cone_sum_sup_eq {R P T c M} cch cubM Mpos A.
Arguments cone_sum_sup_addl_lub {R P T c M} cch cubM Mpos A Z V.

(** *** Finite sums of unit-ball chains (radius 1)

    The [cone_sup_ball] form of the three facts above, in exactly the
    shape [stable/stablehom.v] uses them (Sections [SumSup] /
    [AddlSumConeSup]): the per-index suprema are unit-ball suprema,
    while the diagonal sum is still handled at the general radius
    inside the proofs. *)

Section ConsolidatedSumSupBall.
Local Open Scope precone_scope.
Variable R : realType.
Variable P : coneType R.
Variable T : finType.
Variable c : T -> nat -> P.
Hypothesis cch : forall i n, c i n <=p c i n.+1.
Hypothesis cub : forall i n, cone_norm (c i n) <= 1.

(** The [{nonneg R}]-typed form of [cub], for the radius-1
    [cone_sup_at]. *)
Lemma cone_sum_ball_ub1 : forall i n,
  cone_norm (c i n) <= ((1%:nng : {nonneg R}))%:num.
Proof. by move=> i n; exact: cub. Qed.

(** The per-index ball suprema, read at radius [1]. *)
Lemma cone_sum_ball_supE (i : T) :
  cone_sup_ball (c i) (cch i) (cub i) =
  cone_sum_sup c cch cone_sum_ball_ub1 nng1_pos i.
Proof. by rewrite /cone_sum_sup; exact: cone_sup_ball_atE. Qed.

(** Subsumes [sum_cone_sup_ub] (stablehom.v). *)
Lemma cone_sum_ball_sup_ub (A : {set T}) n :
  cone_sum_chain c A n <=p
  \big[precone_add/precone_zero]_(i in A) cone_sup_ball (c i) (cch i) (cub i).
Proof.
rewrite (eq_bigr _ (fun i _ => cone_sum_ball_supE i)).
exact: cone_sum_sup_ub.
Qed.

(** Subsumes [sum_cone_sup_lub] (stablehom.v). *)
Lemma cone_sum_ball_sup_lub (A : {set T}) (y : P) :
  (forall n, cone_sum_chain c A n <=p y) ->
  \big[precone_add/precone_zero]_(i in A)
    cone_sup_ball (c i) (cch i) (cub i) <=p y.
Proof.
rewrite (eq_bigr _ (fun i _ => cone_sum_ball_supE i)).
exact: cone_sum_sup_lub.
Qed.

(** Subsumes [addl_sum_cone_sup_lub] (stablehom.v). *)
Lemma cone_sum_ball_sup_addl_lub (A : {set T}) (Z V : P) :
  (forall m, Z + cone_sum_chain c A m <=p V) ->
  Z + \big[precone_add/precone_zero]_(i in A)
        cone_sup_ball (c i) (cch i) (cub i) <=p V.
Proof.
rewrite (eq_bigr _ (fun i _ => cone_sum_ball_supE i)).
exact: cone_sum_sup_addl_lub.
Qed.

End ConsolidatedSumSupBall.

Arguments cone_sum_ball_sup_ub {R P T c} cch cub A n.
Arguments cone_sum_ball_sup_lub {R P T c} cch cub A y.
Arguments cone_sum_ball_sup_addl_lub {R P T c} cch cub A Z V.

(** *** The scaling chain [m ↦ λₘ ·: z]

    Every unit-ball point [z] is the supremum of the increasing chain
    of its strict rescalings [λₘ ·: z] with [λₘ = (m+1)/(m+2) ↑ 1]:
    the boundary of [B_P] is reached from the strict interior.  The
    least-upper-bound half is the Archimedean "the gap vanishes"
    argument.  Subsumes Section [ScaleChain] of [stable/findiff.v]. *)

Section ConsolidatedScaleChain.
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
Proof. by rewrite /= -[X in _ + X]mul1r -mulrDl natr1 mulfV. Qed.

Lemma scl_le1 (m : nat) : (scl m)%:num <= 1.
Proof. by rewrite -(scl_scc_num m) lerDl; exact: nngnum_ge0. Qed.

Lemma scl_num (m : nat) : (scl m)%:num = 1 - (scc m)%:num.
Proof. by rewrite -(scl_scc_num m) addrK. Qed.

(** Monotonicity of the ratios: [λₘ ≤ λₘ₊₁]. *)
Lemma scl_mono (m : nat) : (scl m)%:num <= (scl m.+1)%:num.
Proof.
by rewrite !scl_num lerB// lef_pV2 ?posrE ?ltr0n// ler_nat ltnS leqnSn.
Qed.

Local Open Scope precone_scope.

(** The chain [m ↦ λₘ ·: z] is increasing. *)
Lemma scchain_mono (z : P) (m : nat) : scl m *: z <=p scl m.+1 *: z.
Proof.
have d_ge0 : (0 <= (scl m.+1)%:num - (scl m)%:num)%R.
  by rewrite subr_ge0; exact: scl_mono.
exists (NngNum d_ge0 *: z).
rewrite -precone_scale_DAl; congr (_ *: z); apply: val_inj => /=.
by rewrite addrC subrK.
Qed.

(** It stays in the unit ball whenever [z] does. *)
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

End ConsolidatedScaleChain.

Arguments scl {R} m.
Arguments scc {R} m.
Arguments scl_le1 {R} m.
Arguments scl_num {R} m.
Arguments scale_chain_sup {R P} z Hz.
