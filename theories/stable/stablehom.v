(**md**************************************************************)
(** * The cone of stable measurable functions — Paper §7.2

    This file builds the carrier [stablehom B C] of the cone
    [B ⇒ₛ C] of *stable and measurable* functions, and climbs the HB
    tower as far as it cleanly goes.  It is the §7.2 analogue of
    [homs/linhom.v] (which builds [C ⊸ D] for *linear* maps).

    The predicate [is_meas_stable] and the Lemma 7.11 closure lemmas
    are delivered in [stable/totmono.v]; here we assemble them into a
    proof-irrelevant record and register the precone and cone HB
    instances.

    Paper reference: §7.2 (pages 1:56–1:59), Lemmas 7.11, 7.12,
    7.14, and the integrability paragraph (the §7.2 analogue of
    Lemma 5.4).

    Coverage in this file.
    - [stablehom B C] — the carrier record bundling a function
      [B -> C] with [is_meas_stable].  Proof-irrelevant extensionality
      [stablehom_eq].  This is the layer that compiles with no holes.
    - Lemma 7.11 *content* at the record level: the zero map [sh_zero]
      and the pointwise sum [sh_add] of two [stablehom]s are again
      [stablehom]s (reusing [meas_stable_zero] / [meas_stable_add]).
    - The operator/sup norm [sh_norm f = sup_{x∈B_B} ‖f x‖] (well
      defined since stable functions are bounded) with its upper-bound
      / least-upper-bound / non-negativity lemmas — the norm of
      Lemma 7.14, which needs no scaling.
    - [stable_scale_cont_ge1] — the totmono.v-deferred ω-continuity of
      nonneg scaling, *resolved for [r ≥ 1]* by the rescaling /
      [sup_ball_scaler] argument adapted from [linhom_scale_fun_
      continuous].

    What is NOT delivered (and why), see the closing [(**md ...*)]
    status block: the [isPrecone] HB instance, hence the [isCone] /
    [isMCone] / [isICone] layers.  The blocker is *exactly* the
    totmono.v deferral: nonneg scaling [r *: f] for [0 < r < 1] is not
    provably ω-continuous from [is_stable f] under the codebase's
    unit-ball-restricted [is_omega_continuous] (which we may not
    change), because the image chain [(f uₙ)] may have norm up to
    [1/r > 1] and so escapes the unit ball where [f]'s ω-continuity has
    any force.  The linear case escapes this via domain rescaling
    ([f(s·x) = s·f x]), which is unavailable for nonlinear stable [f]. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import measurable_structure measurable_function.

Require Import Icones.prelude.classical_extra.
Require Import Icones.prelude.nonneg_extra.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.path.
Require Import Icones.stable.totmono.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(** ** The carrier — Paper §7.2 (Def 7.10)

    A [stablehom B C] element is a function [B -> C] together with a
    proof that it is stable and measurable ([is_meas_stable], shape
    fixed in [totmono.v]).  We bundle exactly that one field; the
    coercion [sh_fun] recovers the underlying function. *)

Section StablehomCar.
Variable R : realType.
Variable Ar : MeasSubcat R.
Variables B C : MCone.type Ar.

(** Paper §7.2: the carrier of [B ⇒ₛ C]. *)
Record stablehom : Type := MkStablehom {
  sh_fun :> B -> C;
  sh_meas_stable : is_meas_stable sh_fun;
}.

(** Proof-irrelevant extensionality: two stable maps with the same
    underlying function are equal. *)
Lemma stablehom_eq (f g : stablehom) :
  (forall x, sh_fun f x = sh_fun g x) -> f = g.
Proof.
case: f => ff fs; case: g => gf gs /= Hfg.
have Hf : ff = gf by apply: funext.
move: fs; rewrite Hf => fs.
by congr MkStablehom; exact: Prop_irrelevance.
Qed.

End StablehomCar.

Arguments stablehom {R Ar} B C.
Arguments MkStablehom {R Ar B C}.
Arguments sh_fun {R Ar B C}.
Arguments sh_meas_stable {R Ar B C}.
Arguments stablehom_eq {R Ar B C}.

(** ** Increasingness from total monotonicity (workhorse)

    The [n = 1] sanity reformulation [totmono_increasing] of
    [totmono.v] gives [f x ≤p f (x + v)] when [‖x + v‖ ≤ 1].  We
    package the slightly more convenient "[x ≤p y] with [‖y‖ ≤ 1]"
    form, used pervasively below for the ω-continuity of scaling. *)

Section TmIncr.
Variable R : realType.
Variables P Q : coneType R.
Local Open Scope precone_scope.

Lemma tm_incr_le (f : P -> Q) (Hfm : is_totmono f) (x y : P) :
  x <=p y -> cone_norm y <= 1 -> f x <=p f y.
Proof.
move=> [v Hv] Hy; rewrite Hv.
by apply: (totmono_increasing Hfm); rewrite -Hv.
Qed.

End TmIncr.

Arguments tm_incr_le {R P Q f} Hfm {x y}.

(** ** Lemma 7.11 — ω-continuity of nonneg scaling, resolved for [r ≥ 1]

    [totmono.v] delivered [totmono_scale] and [bounded_scale] but
    deferred ω-continuity of [r *: f] for a *stable* (nonlinear) [f].
    We resolve it here for scalars [r ≥ 1].

    Argument (the totmono.v hint, made precise).  Let [u] be an
    increasing unit-ball chain whose scaled image [(r *: f uₙ)] is also
    in the unit ball — i.e. [‖r *: f uₙ‖ ≤ 1].  Since [r ≥ 1] and the
    cone norm is non-negative, [‖f uₙ‖ ≤ r·‖f uₙ‖ = ‖r *: f uₙ‖ ≤ 1]
    ([ler_peMl]); so the *unscaled* image chain [(f uₙ)] already lives
    in the unit ball.  Now [f]'s ω-continuity applies on [u] directly,
    giving [f (sup u) = sup_ball (f ∘ u)], and [sup_ball_scaler] pulls
    the scalar [r] out: [r *: sup_ball (f ∘ u) = sup_ball (r *: f ∘ u)],
    which is the [stm_scale]-chain sup, as required.

    For [0 < r < 1] the unit-ball encoding of [is_omega_continuous]
    is genuinely too weak (see the closing status block); the linear
    development sidesteps this by rescaling the *domain*
    ([f (s·x) = s·f x]), unavailable for nonlinear stable [f]. *)

Section ScaleContinuous.
Variable R : realType.
Variables P Q : coneType R.
Local Open Scope precone_scope.

Lemma stable_scale_cont_ge1 (r : {nonneg R}) (f : P -> Q) :
  is_stable f -> 1 <= r%:num -> is_omega_continuous (stm_scale r f).
Proof.
move=> [Hfm _ Hfc] rge1 u uch ub1 fuch fub1.
rewrite /stm_scale.
set Su := cone_sup_ball u uch ub1.
have fch : forall n, f (u n) <=p f (u n.+1).
  by move=> n; apply: (tm_incr_le Hfm (uch n)); exact: ub1.
have fub : forall n, cone_norm (f (u n)) <= 1.
  move=> n; have := fub1 n; rewrite /stm_scale cone_normh /= => H.
  by apply: le_trans H; apply: ler_peMl rge1; exact: cone_norm_ge0.
have fSu : f Su = cone_sup_ball (f \o u) fch fub by rewrite /Su; exact: Hfc.
have rfch : forall n, (r *: (f \o u) n) <=p (r *: (f \o u) n.+1).
  by move=> n /=; exact: precone_scale_le (fch n).
have rfub : forall n, cone_norm (r *: (f \o u) n) <= 1.
  by move=> n /=; have := fub1 n; rewrite /stm_scale.
rewrite fSu -(@sup_ball_scaler R Q r (f \o u) fch fub rfch rfub).
apply: precone_le_anti; apply: cone_sup_ball_lub => n /=; rewrite /stm_scale.
- exact: (cone_sup_ball_ub ((fun x => r *: f x) \o u) fuch fub1 n).
- exact: (cone_sup_ball_ub (fun n0 : nat => (r *: f (u n0))) rfch rfub n).
Qed.

End ScaleContinuous.

Arguments stable_scale_cont_ge1 {R P Q} r f.

(** ** Lemma 7.11 — the pointwise operations as [stablehom] records

    The zero map and the pointwise sum of two stable measurable maps
    are again stable measurable maps.  These are the parts of the
    precone (Lemma 7.11) that need no scaling, so they compile with no
    holes; the nonneg-scaling operation — and hence the [isPrecone] HB
    instance — is blocked (see closing status block). *)

Section StablehomOps.
Variable R : realType.
Variable Ar : MeasSubcat R.
Variables B C : MCone.type Ar.
Local Open Scope precone_scope.

(** Paper §7.2: the zero of [B ⇒ₛ C]. *)
Definition sh_zero : stablehom B C :=
  MkStablehom (stm_zero B C) (meas_stable_zero B C).

(** Paper §7.2: pointwise sum of two stable measurable maps. *)
Definition sh_add (f g : stablehom B C) : stablehom B C :=
  MkStablehom (stm_add (sh_fun f) (sh_fun g))
              (meas_stable_add (sh_meas_stable f) (sh_meas_stable g)).

(** Pointwise computation rules. *)
Lemma sh_zeroE (x : B) : sh_fun sh_zero x = precone_zero.
Proof. by []. Qed.

Lemma sh_addE (f g : stablehom B C) (x : B) :
  sh_fun (sh_add f g) x = (sh_fun f x + sh_fun g x)%PC.
Proof. by []. Qed.

(** The pointwise sum is associative / commutative / unital, witnessing
    the (semimodule) precone laws at the record level. *)
Lemma sh_addA : associative sh_add.
Proof. by move=> f g h; apply: stablehom_eq => x /=; exact: precone_addA. Qed.

Lemma sh_addC : commutative sh_add.
Proof. by move=> f g; apply: stablehom_eq => x /=; exact: precone_addC. Qed.

Lemma sh_add0 : left_id sh_zero sh_add.
Proof. by move=> f; apply: stablehom_eq => x /=; exact: precone_add0. Qed.

End StablehomOps.

Arguments sh_zero {R Ar} B C.
Arguments sh_add {R Ar B C}.

(** ** The operator / sup norm — Lemma 7.14

    [‖f‖ = sup_{x ∈ B_B} ‖f x‖], well defined because stable functions
    are bounded.  We deliver the norm and its upper-bound,
    least-upper-bound and non-negativity properties; these are the
    norm facts of Lemma 7.14 that do not depend on the precone scaling
    operation.  (The cone axioms (Normh)/(Normz)/(Normt)/(Normp) and
    (Normc) require the precone instance and are deferred with it.) *)

Local Open Scope classical_set_scope.

Section StablehomNorm.
Variable R : realType.
Variable Ar : MeasSubcat R.
Variables B C : MCone.type Ar.

(** The image norm-set [{‖f x‖ | ‖x‖ ≤ 1}]. *)
Definition sh_normset (f : stablehom B C) : set R :=
  [set y | exists x : B, cone_norm x <= 1 /\ y = cone_norm (sh_fun f x)].

(** Nonempty: contains [‖f 0‖] via [x := 0]. *)
Lemma sh_normset_nonempty (f : stablehom B C) : sh_normset f !=set0.
Proof.
exists (cone_norm (sh_fun f precone_zero)), precone_zero.
by split; first by rewrite cone_norm0.
Qed.

(** Bounded above: the boundedness witness [M] of [is_stable]. *)
Lemma sh_normset_has_ubound (f : stablehom B C) : has_ubound (sh_normset f).
Proof.
have [[_ [M HM] _] _] := sh_meas_stable f.
by exists M => _ [x [Hx ->]]; exact: HM.
Qed.

Lemma sh_normset_has_sup (f : stablehom B C) : has_sup (sh_normset f).
Proof.
by split; [exact: sh_normset_nonempty | exact: sh_normset_has_ubound].
Qed.

(** Paper Lemma 7.14: [‖f‖ = sup_{‖x‖ ≤ 1} ‖f x‖]. *)
Definition sh_norm (f : stablehom B C) : R := sup (sh_normset f).

(** Pointwise bound: [‖f x‖ ≤ ‖f‖] for [‖x‖ ≤ 1]. *)
Lemma sh_norm_ub (f : stablehom B C) (x : B) :
  cone_norm x <= 1 -> cone_norm (sh_fun f x) <= sh_norm f.
Proof.
move=> Hx; move/ubP : (sup_upper_bound (sh_normset_has_sup f)); apply.
by exists x.
Qed.

(** Least upper bound: any uniform pointwise bound dominates [‖f‖]. *)
Lemma sh_norm_lub (f : stablehom B C) (M : R) :
  (forall x : B, cone_norm x <= 1 -> cone_norm (sh_fun f x) <= M) ->
  sh_norm f <= M.
Proof.
move=> HM; apply: ge_sup; first exact: sh_normset_nonempty.
by move=> _ [x [Hx ->]]; exact: HM.
Qed.

Lemma sh_norm_ge0 (f : stablehom B C) : 0 <= sh_norm f.
Proof.
apply: le_trans (cone_norm_ge0 (sh_fun f precone_zero)) _.
by apply: sh_norm_ub; rewrite cone_norm0.
Qed.

End StablehomNorm.

Arguments sh_normset {R Ar B C}.
Arguments sh_norm {R Ar B C}.
Arguments sh_norm_ub {R Ar B C}.
Arguments sh_norm_lub {R Ar B C}.
Arguments sh_norm_ge0 {R Ar B C}.

(**md**************************************************************)
(** ** Status — what is delivered and what is deferred (and why)

    Delivered (no holes, no axioms):
    - [stablehom B C] carrier (Def 7.10) + proof-irrelevant
      extensionality [stablehom_eq].  This is the highest HB-tower
      layer reached: the carrier is a plain [Record], *not* yet a
      [preconeType] (see below).
    - [tm_incr_le] — total monotonicity ⇒ increasing along [≤p] with
      the larger point in the unit ball.
    - [stable_scale_cont_ge1] — the totmono.v-deferred ω-continuity of
      nonneg scaling, resolved for scalars [r ≥ 1].
    - Lemma 7.11 records [sh_zero] / [sh_add] (the no-scaling part of
      the precone), with [sh_addA] / [sh_addC] / [sh_add0].
    - Lemma 7.14 operator norm [sh_norm] with [sh_norm_ub] /
      [sh_norm_lub] / [sh_norm_ge0].

    Deferred — the [isPrecone] HB instance (Lemma 7.11) and therefore
    everything above it ([isCone] Lem 7.12/7.14, [isMCone], [isICone]).

    Why the precone is blocked.  A [preconeType] needs a *total*
    nonneg scaling [precone_scale : {nonneg R} -> P -> P], which here
    must be the pointwise [r *: f].  Packaging [r *: f] as a
    [stablehom] requires [is_meas_stable (stm_scale r f)], whose
    ω-continuity component fails for [0 < r < 1] under this codebase's
    encoding of ω-continuity:

      [is_omega_continuous f] (cones/basic_lemmas.v) only constrains
      [f] on increasing chains [u] whose *image* chain [(f uₙ)] also
      lies in the unit ball.  When proving [r *: f] ω-continuous we are
      given [‖r *: f uₙ‖ ≤ 1], i.e. [‖f uₙ‖ ≤ 1/r], which for [r < 1]
      is [> 1]: the chain [(f uₙ)] may leave the unit ball, where
      [is_omega_continuous f] says nothing, so [f (sup u)] is
      unconstrained and [r *: f (sup u) = sup (r *: f uₙ)] need not
      hold.  (One can exhibit a stable [f] with bound [M > 1] whose
      values on norm-[(1, M]] chains are arbitrary increasing/bounded,
      defeating the identity.)

    The paper's Lemma 7.11 is "straightforward" because Ehrhard–
    Geoffroy use the *unrestricted* Scott ω-continuity of Definition
    2.2 (sup of any bounded increasing sequence), not the unit-ball
    form used throughout this Rocq development.  The linear cone
    [C ⊸ D] ([homs/linhom.v]) dodges the same issue by rescaling the
    *domain* — [f (s·x) = s·f x] brings the image chain back into the
    unit ball — which is unavailable for nonlinear stable [f].

    Closing the precone (and the cone/mcone/icone tower) therefore
    needs one of: (i) strengthening [is_omega_continuous] / (Normc) to
    a radius-[ρ] ball form in [cones/{basic_lemmas,cone}.v]; or
    (ii) adding a "rescaled completeness" lemma [sup_ball_at] giving
    sups of chains bounded by [ρ ≥ 1].  Both are outside the
    single-file scope of this task (which forbids touching
    [basic_lemmas.v] / [cone.v] / [totmono.v]). *)
