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
      [stablehom_eq].
    - Lemma 7.11 — the zero map [sh_zero], the pointwise sum [sh_add]
      and the nonneg scaling [sh_scale] of [stablehom]s are again
      [stablehom]s (reusing [meas_stable_zero] / [meas_stable_add] /
      [stable_scale] + [meas_stable_scale]).  [sh_scale] is now
      available because the totmono.v migration to Scott-continuity
      ([is_scott_continuous_unit]) proved [stable_scale] for ALL [r].
    - The eleven precone axioms ([sh_addA]/[sh_addC]/[sh_add0],
      [sh_scale_DAr]/[sh_scale_DAl]/[sh_scale_A]/[sh_scale_1]/
      [sh_scale_0r]/[sh_scale_0l], [sh_cancel]/[sh_pos]) and the
      **[isPrecone] HB instance** — [stablehom B C : preconeType R].
    - Lemma 7.12 (the induced order): [sh_le_pointwise]
      ([f ≤p g] pointwise in [C]).
    - The operator/sup norm [sh_norm f = sup_{x∈B_B} ‖f x‖] (well
      defined since stable functions are bounded) with [sh_norm_ub] /
      [sh_norm_lub] / [sh_norm_ge0], and the cone-norm axioms (Normh)
      [sh_normh], (Normt) [sh_normt], (Normp) [sh_normp] — Lemma 7.14.

    What is NOT delivered (and why), see the closing status block:
    the [isCone] HB instance — blocked at (Normz), and hence [isMCone]
    / [isICone].  (Normz) ([‖f‖ = 0 ⇒ f = 0]) fails for the *total*-
    function carrier: [‖f‖ = 0] forces [f x = 0] only on the unit ball
    [B_B] (the domain of a stable map), but [stablehom] wraps a total
    [B -> C] whose values *outside* [B_B] are unconstrained by
    [is_meas_stable], so [f] need not be Leibniz-equal to [sh_zero].
    The linear cone [C ⊸ D] dodges this via linearity (a linear map
    null on [B_C] is null everywhere); a nonlinear stable map is not so
    determined.  Closing (Normz) needs the carrier to identify maps
    agreeing on [B_B] (a setoid/quotient or a canonical extension by
    [0] off [B_B]), a carrier-level change beyond resuming the tower. *)
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

(** ** Lemma 7.11 — nonneg scaling is now stable (full, all [r])

    [totmono.v] previously DEFERRED ω-continuity of [r *: f] for a
    *stable* (nonlinear) [f] (and [stablehom.v] only patched the
    [r ≥ 1] sub-case via domain-free rescaling).  With the migration to
    Scott-continuity ([is_scott_continuous_unit], general image radius)
    this is fully resolved in [totmono.v] by [stable_scale], for ALL
    [r : {nonneg R}].  The [r < 1] obstruction is gone: the image chain
    [r *: f∘u] is allowed to carry any radius [Mf], so no rescaling of
    the domain is needed.  We therefore reuse [stable_scale] /
    [meas_stable_scale] directly below; the old [stable_scale_cont_ge1]
    workaround is retired. *)

(** ** Lemma 7.11 — the pointwise operations as [stablehom] records

    The zero map, the pointwise sum and the nonneg scaling of stable
    measurable maps are again stable measurable maps (Lemma 7.11).  With
    [stable_scale] now proved in [totmono.v] (the migration payoff),
    scaling is no longer blocked, so all three operations and the eleven
    precone laws are available — we register the [isPrecone] HB instance
    below. *)

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

(** Measurable stability of [r *: f] from [is_meas_stable f]. *)
Lemma sh_scale_meas_stable (r : {nonneg R}) (f : stablehom B C) :
  is_meas_stable (stm_scale r (sh_fun f)).
Proof.
have [Hs Hp] := sh_meas_stable f; split; first exact: stable_scale.
exact: meas_stable_scale Hp.
Qed.

(** Paper §7.2: nonneg scaling of a stable measurable map. *)
Definition sh_scale (r : {nonneg R}) (f : stablehom B C) : stablehom B C :=
  MkStablehom (stm_scale r (sh_fun f)) (sh_scale_meas_stable r f).

(** Pointwise computation rules. *)
Lemma sh_zeroE (x : B) : sh_fun sh_zero x = precone_zero.
Proof. by []. Qed.

Lemma sh_addE (f g : stablehom B C) (x : B) :
  sh_fun (sh_add f g) x = (sh_fun f x + sh_fun g x)%PC.
Proof. by []. Qed.

Lemma sh_scaleE (r : {nonneg R}) (f : stablehom B C) (x : B) :
  sh_fun (sh_scale r f) x = (r *: sh_fun f x)%PC.
Proof. by []. Qed.

(** The pointwise sum is associative / commutative / unital, witnessing
    the (semimodule) precone laws at the record level. *)
Lemma sh_addA : associative sh_add.
Proof. by move=> f g h; apply: stablehom_eq => x /=; exact: precone_addA. Qed.

Lemma sh_addC : commutative sh_add.
Proof. by move=> f g; apply: stablehom_eq => x /=; exact: precone_addC. Qed.

Lemma sh_add0 : left_id sh_zero sh_add.
Proof. by move=> f; apply: stablehom_eq => x /=; exact: precone_add0. Qed.

(** Semimodule scaling laws — the eight scaling axioms of [isPrecone]. *)
Lemma sh_scale_DAr (r : {nonneg R}) (f g : stablehom B C) :
  sh_scale r (sh_add f g) = sh_add (sh_scale r f) (sh_scale r g).
Proof.
by apply: stablehom_eq => x /=; exact: precone_scale_DAr.
Qed.

Lemma sh_scale_DAl (r s : {nonneg R}) (f : stablehom B C) :
  sh_scale (r%:num + s%:num)%R%:nng f = sh_add (sh_scale r f) (sh_scale s f).
Proof.
by apply: stablehom_eq => x /=; exact: precone_scale_DAl.
Qed.

Lemma sh_scale_A (r s : {nonneg R}) (f : stablehom B C) :
  sh_scale (r%:num * s%:num)%R%:nng f = sh_scale r (sh_scale s f).
Proof.
by apply: stablehom_eq => x /=; exact: precone_scale_A.
Qed.

Lemma sh_scale_1 (f : stablehom B C) : sh_scale 1%:nng f = f.
Proof. by apply: stablehom_eq => x /=; exact: precone_scale_1. Qed.

Lemma sh_scale_0r (r : {nonneg R}) : sh_scale r sh_zero = sh_zero.
Proof. by apply: stablehom_eq => x /=; exact: precone_scale_0r. Qed.

Lemma sh_scale_0l (f : stablehom B C) :
  sh_scale (0%R%:nng : {nonneg R}) f = sh_zero.
Proof. by apply: stablehom_eq => x /=; exact: precone_scale_0l. Qed.

(** (Cancel) and (Pos) — pointwise from [C]. *)
Lemma sh_cancel (f g h : stablehom B C) :
  sh_add f g = sh_add f h -> g = h.
Proof.
move=> H; apply: stablehom_eq => x.
have /(congr1 (fun k => sh_fun k x)) := H.
exact: precone_cancel.
Qed.

Lemma sh_pos (f g : stablehom B C) :
  sh_add f g = sh_zero -> f = sh_zero /\ g = sh_zero.
Proof.
move=> H; split; apply: stablehom_eq => x;
  have /(congr1 (fun k => sh_fun k x)) /= := H.
- by move/precone_pos => -[].
- by move/precone_pos => -[].
Qed.

End StablehomOps.

Arguments sh_zero {R Ar} B C.
Arguments sh_add {R Ar B C}.
Arguments sh_scale {R Ar B C}.

(** ** Precone HB instance — Paper §7.2, Lemma 7.11

    The eleven precone axioms reduce pointwise to those of the codomain
    cone [C], exactly as for [linhom]'s [isPrecone]. *)

HB.instance Definition _ (R : realType) (Ar : MeasSubcat R)
    (B C : MCone.type Ar) :=
  @isPrecone.Build R (stablehom B C)
    (sh_zero B C) (@sh_add R Ar B C) (@sh_scale R Ar B C)
    (@sh_addA R Ar B C) (@sh_addC R Ar B C) (@sh_add0 R Ar B C)
    (@sh_scale_DAr R Ar B C) (@sh_scale_DAl R Ar B C)
    (@sh_scale_A R Ar B C) (@sh_scale_1 R Ar B C)
    (@sh_scale_0r R Ar B C) (@sh_scale_0l R Ar B C)
    (@sh_cancel R Ar B C) (@sh_pos R Ar B C).

(** Sanity check: [stablehom B C] is a [preconeType R]. *)
Section StablehomPreconeCheck.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : MCone.type Ar.

Check (stablehom B C : preconeType R).

End StablehomPreconeCheck.

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

(** ** Lemma 7.12 — the induced order [f ≤ g]

    With the [isPrecone] instance registered, the cone order [≤p] on
    [stablehom B C] is [∃ δ, g = f + δ].  Pointwise, this gives
    [sh_fun f x ≤p sh_fun g x] in [C], the engine for (Normp) and the
    sup-ball construction (Normc). *)

Section StablehomLePointwise.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : MCone.type Ar.

Lemma sh_le_pointwise (f g : stablehom B C) :
  precone_le f g ->
  forall x : B, precone_le (sh_fun f x) (sh_fun g x).
Proof.
move=> [δ Hδ] x; exists (sh_fun δ x).
by have /(congr1 (fun h => sh_fun h x)) /= := Hδ.
Qed.

End StablehomLePointwise.

Arguments sh_le_pointwise {R Ar B C}.

(** ** Cone axioms on [stablehom] — Paper §7.2 / Lemma 7.14

    (Normh)/(Normt)/(Normp) are sup manipulations on the image norm-set,
    identical to [linhom]'s; they need no linearity, only [cone_normh] /
    [cone_normt] / [cone_normp] of [C] applied pointwise. *)

Section StablehomConeAxioms.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : MCone.type Ar.
Implicit Types f g : stablehom B C.

(** (Normh) — scalar homogeneity of the operator norm. *)
Lemma sh_normh (r : {nonneg R}) f :
  sh_norm (sh_scale r f) = r%:num * sh_norm f.
Proof.
have rge0 : 0 <= r%:num by exact: nngnum_ge0.
have [rzero | rpos] := lerP r%:num 0.
  have req0 : r%:num = 0 by apply: le_anti; rewrite rzero rge0.
  rewrite req0 mul0r.
  apply: le_anti; apply/andP; split; last exact: sh_norm_ge0.
  apply: sh_norm_lub => x Hx /=.
  by rewrite /stm_scale cone_normh req0 mul0r.
apply: le_anti; apply/andP; split.
- apply: sh_norm_lub => x Hx /=.
  rewrite /stm_scale cone_normh.
  by rewrite ler_pM2l //; exact: sh_norm_ub.
- rewrite -ler_pdivlMl //.
  apply: sh_norm_lub => x Hx /=.
  rewrite ler_pdivlMl //.
  have Hin : sh_normset (sh_scale r f) (r%:num * cone_norm (sh_fun f x)).
    by exists x; split=> //=; rewrite /stm_scale cone_normh.
  by move/ubP : (sup_upper_bound (sh_normset_has_sup (sh_scale r f)))
    => /(_ _ Hin).
Qed.

(** (Normt) — triangle inequality of the operator norm. *)
Lemma sh_normt f g :
  sh_norm (sh_add f g) <= sh_norm f + sh_norm g.
Proof.
apply: sh_norm_lub => x Hx /=.
apply: le_trans (cone_normt _ _) _.
by rewrite lerD //; exact: sh_norm_ub.
Qed.

(** (Normp) — order monotonicity of the operator norm. *)
Lemma sh_normp f g :
  precone_le f g -> sh_norm f <= sh_norm g.
Proof.
move=> Hle; apply: sh_norm_lub => x Hx.
have Hpt := sh_le_pointwise f g Hle x.
apply: le_trans (sh_norm_ub g x Hx).
exact: cone_normp Hpt.
Qed.

End StablehomConeAxioms.

(**md**************************************************************)
(** ** Status — what is delivered and what is deferred (and why)

    Delivered (no holes, no axioms):
    - [stablehom B C] carrier (Def 7.10) + proof-irrelevant
      extensionality [stablehom_eq].
    - [tm_incr_le] — total monotonicity ⇒ increasing along [≤p] with
      the larger point in the unit ball.
    - Lemma 7.11 operations [sh_zero] / [sh_add] / [sh_scale] and the
      eleven precone axioms, registered as the **[isPrecone] HB
      instance**: [stablehom B C : preconeType R].  [sh_scale] is the
      migration payoff — [stable_scale] (totmono.v) now holds for ALL
      [r : {nonneg R}] under Scott-continuity, so nonneg scaling is no
      longer blocked.
    - Lemma 7.12 (induced order) [sh_le_pointwise].
    - Lemma 7.14 operator norm [sh_norm] with [sh_norm_ub] /
      [sh_norm_lub] / [sh_norm_ge0], and the cone-norm axioms (Normh)
      [sh_normh], (Normt) [sh_normt], (Normp) [sh_normp].

    Deferred — the [isCone] HB instance (and hence [isMCone] /
    [isICone]).  The blocker is (Normz), NOT scaling (the scaling
    blocker is now resolved by [stable_scale]).

    Why (Normz) is blocked.  (Normz) is [‖f‖ = 0 ⇒ f = 0].  Here
    [‖f‖ = sup_{x ∈ B_B} ‖f x‖], so [‖f‖ = 0] gives [f x = 0] only for
    [‖x‖ ≤ 1] — the domain [B_B] on which a stable map is constrained.
    But [stablehom] wraps a *total* function [B -> C], and
    [is_meas_stable f] places NO constraint on [f x] for [‖x‖ > 1]
    (total monotonicity ranges over [B_B], boundedness/Scott-continuity
    are unit-ball, path preservation uses unit-ball paths).  So a
    function null on [B_B] but arbitrary off it is a valid [stablehom]
    with [‖f‖ = 0] yet [f ≠ sh_zero] (which demands [f x = 0]
    everywhere via the Leibniz [stablehom_eq]).  Hence (Normz) fails.

    The linear cone [C ⊸ D] ([homs/linhom.v]) proves (Normz) via
    linearity: a linear map null on [B_C] is null everywhere (rescale
    any [y] into [B_C] and back).  A *nonlinear* stable map is not
    determined off [B_B] by its [B_B] values, so this route is gone.

    Closing (Normz) — and thus [isCone]/[isMCone]/[isICone] — needs a
    carrier-level change: identify [stablehom]s that agree on [B_B]
    (a setoid/quotient, or wrap functions canonically extended by [0]
    off [B_B] so that [B_B]-agreement gives Leibniz equality).  That is
    a carrier redesign beyond resuming the HB tower on the existing
    [stablehom] record, so we stop cleanly at the [isPrecone] layer
    (plus the no-scaling-blocked norm facts of Lemma 7.14). *)
