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
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import topology normedtype sequences.

Require Import Icones.prelude.classical_extra.
Require Import Icones.prelude.nonneg_extra.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.omega_general.
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

    The paper's stable functions are [f : B_B → C], defined on the unit
    ball.  We model them by a *total* function [B → C] that is
    *canonically extended by [0] off the unit ball*: the extra field
    [sh_offball] forces [f x = 0] for every [x ∉ B_B].  Together with
    [is_meas_stable] (which constrains [f] only on [B_B]) this makes the
    on-ball behaviour fully determine [f]: two stable maps that agree on
    [B_B] also agree off it (both are [0]), hence are Leibniz-equal.
    This is exactly what (Normz) needs (a norm-zero map is [0] on [B_B]
    by the sup, and [0] off [B_B] by [sh_offball]), unblocking [isCone].

    We bundle three fields; the coercion [sh_fun] recovers the
    underlying function.  The two proof fields are [Prop]-irrelevant, so
    extensionality still reduces to function equality. *)

Section StablehomCar.
Variable R : realType.
Variable Ar : MeasSubcat R.
Variables B C : MCone.type Ar.
Local Open Scope precone_scope.

(** Paper §7.2: the carrier of [B ⇒ₛ C].  [sh_offball] is the canonical
    0-extension constraint: [f] vanishes outside the unit ball [B_B]. *)
Record stablehom : Type := MkStablehom {
  sh_fun :> B -> C;
  sh_meas_stable : is_meas_stable sh_fun;
  sh_offball : forall x : B, ~~ (cone_norm x <= 1) -> sh_fun x = 0;
}.

(** Proof-irrelevant extensionality: two stable maps with the same
    underlying function are equal (both proof fields are [Prop]). *)
Lemma stablehom_eq (f g : stablehom) :
  (forall x, sh_fun f x = sh_fun g x) -> f = g.
Proof.
case: f => ff fs fz; case: g => gf gs gz /= Hfg.
have Hf : ff = gf by apply: funext.
move: fs fz; rewrite Hf => fs fz.
by congr MkStablehom; exact: Prop_irrelevance.
Qed.

End StablehomCar.

Arguments stablehom {R Ar} B C.
Arguments MkStablehom {R Ar B C}.
Arguments sh_fun {R Ar B C}.
Arguments sh_meas_stable {R Ar B C}.
Arguments sh_offball {R Ar B C}.
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

(** The canonical 0-extension is preserved by each operation: the zero
    map is [0] everywhere; a pointwise sum of off-ball-[0] maps is
    [0 + 0 = 0]; a nonneg scaling is [r *: 0 = 0]. *)
Lemma sh_zero_offball (x : B) :
  ~~ (cone_norm x <= 1) -> stm_zero B C x = 0.
Proof. by []. Qed.

Lemma sh_add_offball (f g : stablehom B C) (x : B) :
  ~~ (cone_norm x <= 1) -> stm_add (sh_fun f) (sh_fun g) x = 0.
Proof.
by move=> Hx; rewrite /stm_add (sh_offball f x Hx) (sh_offball g x Hx)
  precone_add0.
Qed.

Lemma sh_scale_offball (r : {nonneg R}) (f : stablehom B C) (x : B) :
  ~~ (cone_norm x <= 1) -> stm_scale r (sh_fun f) x = 0.
Proof.
by move=> Hx; rewrite /stm_scale (sh_offball f x Hx) precone_scale_0r.
Qed.

(** Paper §7.2: the zero of [B ⇒ₛ C]. *)
Definition sh_zero : stablehom B C :=
  MkStablehom (stm_zero B C) (meas_stable_zero B C) (@sh_zero_offball).

(** Paper §7.2: pointwise sum of two stable measurable maps. *)
Definition sh_add (f g : stablehom B C) : stablehom B C :=
  MkStablehom (stm_add (sh_fun f) (sh_fun g))
              (meas_stable_add (sh_meas_stable f) (sh_meas_stable g))
              (sh_add_offball f g).

(** Measurable stability of [r *: f] from [is_meas_stable f]. *)
Lemma sh_scale_meas_stable (r : {nonneg R}) (f : stablehom B C) :
  is_meas_stable (stm_scale r (sh_fun f)).
Proof.
have [Hs Hp] := sh_meas_stable f; split; first exact: stable_scale.
exact: meas_stable_scale Hp.
Qed.

(** Paper §7.2: nonneg scaling of a stable measurable map. *)
Definition sh_scale (r : {nonneg R}) (f : stablehom B C) : stablehom B C :=
  MkStablehom (stm_scale r (sh_fun f)) (sh_scale_meas_stable r f)
              (sh_scale_offball r f).

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

(** (Normz) — Paper §7.2 (Lemma 7.13/7.14): a stable map of norm zero
    is the zero map.  This is the payoff of the 0-extension carrier.
    From [sh_norm f = 0] and [sh_norm_ub] we get [cone_norm (f x) ≤ 0],
    hence [cone_norm (f x) = 0], for every [x] in the unit ball; by
    (Normz) in [C], [f x = 0] there.  Off the unit ball, [f x = 0] by
    the canonical-extension field [sh_offball].  So [f = sh_zero]. *)
Lemma sh_normz f : sh_norm f = 0 -> f = sh_zero B C.
Proof.
move=> H; apply: stablehom_eq => x.
have [Hx | Hx] := boolP (cone_norm x <= 1); last first.
  by rewrite (sh_offball f x Hx).
have val0 : cone_norm (sh_fun f x) = 0.
  apply: le_anti; rewrite cone_norm_ge0 andbT.
  by rewrite -H; exact: sh_norm_ub.
by rewrite (cone_normz _ val0).
Qed.

End StablehomConeAxioms.

(** ** Finite cone-sums commute with the supremum — engine for (Normc)

    Total monotonicity of the pointwise supremum reduces to the fact
    that a *finite* cone-sum [∑_{i∈A} sup_n (c i n)] equals the supremum
    [sup_n (∑_{i∈A} c i n)] of the (diagonal) sum chain.  The diagonal
    sum need not stay in [B_P] (it sums up to [#|A|] unit-ball terms), so
    we phrase the supremum on the right with the radius-aware
    [cone_sup_at] at radius [#|A|], and prove the identity by induction
    on [A] from the binary radius-aware diagonal-sup identity
    [sup_at_addD] (totmono.v).  This is the cone-theoretic content
    behind (7.1)-preservation by the supremum. *)

Local Open Scope precone_scope.

Section SumSup.
Variable R : realType.
Variable P : coneType R.
Variable T : finType.
Variable c : T -> nat -> P.
Hypothesis cch : forall i n, c i n <=p c i n.+1.
Hypothesis cub : forall i n, cnorm (c i n) <= 1.

(** The diagonal sum chain over a finite index set [A]. *)
Definition sumsup_chain (A : {set T}) (n : nat) : P :=
  \big[precone_add/precone_zero]_(i in A) c i n.

(** The diagonal sum chain is [≤p]-increasing. *)
Lemma sumsup_chain_ch (A : {set T}) n :
  sumsup_chain A n <=p sumsup_chain A n.+1.
Proof.
rewrite /sumsup_chain; elim/big_rec2: _; first exact: precone_le_refl.
move=> i y1 y2 _ Hy; apply: precone_le_trans (precone_add_le_r _ (cch i n)).
exact: precone_add_le_l.
Qed.

(** The cone-norm of a finite cone-sum is bounded by the sum of the
    norms (iterated [cone_normt]). *)
Lemma sumsup_chain_norm_le (A : {set T}) n :
  cnorm (sumsup_chain A n) <= \sum_(i in A) cnorm (c i n).
Proof.
rewrite /sumsup_chain.
elim/big_rec2: _ => [|i y1 y2 _ Hy]; first by rewrite cone_norm0.
by apply: le_trans (cone_normt _ _) _; rewrite lerD.
Qed.

(** Norm bound: the diagonal sum has norm at most [#|A|]. *)
Lemma sumsup_chain_norm (A : {set T}) n :
  cnorm (sumsup_chain A n) <= #|A|%:R.
Proof.
apply: le_trans (sumsup_chain_norm_le A n) _.
rewrite -sum1_card natr_sum.
by apply: ler_sum => i _; exact: cub.
Qed.

(** A strictly-positive radius dominating [#|A|], for [cone_sup_at]. *)
Lemma sumsup_radius_ge0 (A : {set T}) : (0 <= #|A|%:R + 1 :> R)%R.
Proof. by rewrite addr_ge0 // ?ler0n ?ler01. Qed.

Definition sumsup_radius (A : {set T}) : {nonneg R} :=
  NngNum (sumsup_radius_ge0 A).

Lemma sumsup_radius_pos (A : {set T}) : (0 < (sumsup_radius A)%:num)%R.
Proof.
rewrite /sumsup_radius /=.
by apply: lt_le_trans ltr01 _; rewrite -[X in (X <= _)%R]add0r lerD // ler0n.
Qed.

Lemma sumsup_chain_radius (A : {set T}) n :
  (cnorm (sumsup_chain A n) <= (sumsup_radius A)%:num)%R.
Proof.
apply: le_trans (sumsup_chain_norm A n) _.
by rewrite /= -[X in (X <= _)%R]addr0 lerD // ler01.
Qed.

(** Every diagonal sum element is below the finite cone-sum of the
    per-index suprema (each [c i n ≤p cone_sup_ball (c i)], summed). *)
Lemma sum_cone_sup_ub (A : {set T}) n :
  sumsup_chain A n <=p
  \big[precone_add/precone_zero]_(i in A) (cone_sup_ball (c i) (cch i) (cub i)).
Proof.
rewrite /sumsup_chain; elim/big_rec2: _; first exact: precone_le_refl.
move=> i y1 y2 _ Hy.
apply: (@precone_le_trans _ _ (cone_sup_ball (c i) (cch i) (cub i) + y2)%PC).
  by apply: precone_add_le_r; exact: cone_sup_ball_ub.
by apply: precone_add_le_l.
Qed.

(** The finite cone-sum of per-index suprema is the *least* upper bound
    of the diagonal sum chain.  Proof by cardinality induction on [A]:
    each [a |: A] step pulls out [cone_sup_ball (c a)] via [big_setU1],
    reads the [A]-sum sup as [cone_sup_at] (the induction hypothesis,
    repackaged through [cone_sup_at_lub] / [cone_sup_at_ub]), and
    combines the two suprema with the binary diagonal-sup identity
    [sup_at_addD] at the common radius [#|a:A|+1]. *)
Lemma sum_cone_sup_lub (A : {set T}) (y : P) :
  (forall n, sumsup_chain A n <=p y) ->
  \big[precone_add/precone_zero]_(i in A)
    (cone_sup_ball (c i) (cch i) (cub i)) <=p y.
Proof.
move: y; have [N] := ubnP #|A|; elim: N A => // N IH A.
rewrite ltnS => HA y Hy.
case: (set_0Vmem A) => [-> | [a aA]].
  by rewrite big_set0; exact: precone_le0.
(* Pull out [a]; let [A' := A :\ a]. *)
have aA' : a \notin (A :\ a) by rewrite !inE eqxx.
have AE : A = a |: (A :\ a) by rewrite finset.setD1K.
have cardA' : (#|A :\ a| < N)%N.
  apply: leq_trans HA; by rewrite (cardsD1 a A) aA add1n.
set A' := A :\ a in aA' cardA' *.
(* The diagonal sum over [A] splits as [c a + diagonal over A']. *)
have splitE n : sumsup_chain A n = (c a n + sumsup_chain A' n)%PC.
  by rewrite /sumsup_chain {1}AE (big_setU1 _ aA').
(* The [A']-sum cone-sup is the [cone_sup_at] of its diagonal chain. *)
set Mb : {nonneg R} := sumsup_radius A.
have Mbpos := sumsup_radius_pos A.
have ca_ubMb n : cnorm (c a n) <= Mb%:num.
  apply: le_trans (cub a n) _.
  by rewrite /Mb /= -[X in (X <= _)%R]add0r lerD // ?ler0n.
have sumA'_ubMb n : cnorm (sumsup_chain A' n) <= Mb%:num.
  apply: le_trans (sumsup_chain_norm A' n) _.
  rewrite /Mb /= AE (cardsU1 a) aA' /= add1n mulrSr -addrA.
  by rewrite -[X in (X <= _)%R]addr0 lerD // ?addr_ge0 ?ler0n ?ler01.
have dch n : (c a n + sumsup_chain A' n <=p
              c a n.+1 + sumsup_chain A' n.+1)%PC.
  apply: precone_le_trans (precone_add_le_r _ (cch a n)).
  exact: precone_add_le_l (sumsup_chain_ch A' n).
have dubMb n : cnorm (c a n + sumsup_chain A' n) <= Mb%:num.
  by rewrite -splitE; exact: sumsup_chain_radius.
(* [cone_sup_ball (c a)] as a [cone_sup_at] at radius [Mb]. *)
have caE : cone_sup_ball (c a) (cch a) (cub a) =
           cone_sup_at (cch a) ca_ubMb Mbpos.
  have pos1 : (0%R < (1%:nng : {nonneg R})%:num)%R by rewrite /= ltr01.
  have ca_ub1 : forall n, cnorm (c a n) <= (1%:nng : {nonneg R})%:num.
    by move=> n; exact: cub.
  rewrite (cone_sup_at_indep (cch a) ca_ubMb ca_ub1 Mbpos pos1).
  rewrite (@cone_sup_at_ball _ _ (c a) (cch a) (cub a) ca_ub1 pos1).
  by congr cone_sup_ball; exact: Prop_irrelevance.
(* The IH gives the [A']-sum cone-sup ≤p any common bound; we use it to
   identify it with [cone_sup_at (sumsup_chain A')]. *)
have sumA'E : \big[precone_add/precone_zero]_(i in A')
                (cone_sup_ball (c i) (cch i) (cub i)) =
              cone_sup_at (sumsup_chain_ch A') sumA'_ubMb Mbpos.
  apply: precone_le_anti.
  - apply: IH => // n.
    apply: precone_le_trans (cone_sup_at_ub (sumsup_chain_ch A')
      sumA'_ubMb Mbpos n) => /=; exact: precone_le_refl.
  - apply: cone_sup_at_lub => n; exact: sum_cone_sup_ub.
(* Combine: [Σ_A = cone_sup_ball(c a) + Σ_{A'}] = [cone_sup_at(c a +
   Σ_{A'})], which is the lub of the diagonal chain of [A]. *)
rewrite AE (big_setU1 _ aA') caE sumA'E.
have key : (cone_sup_at (cch a) ca_ubMb Mbpos
            + cone_sup_at (sumsup_chain_ch A') sumA'_ubMb Mbpos)%PC
           = cone_sup_at dch dubMb Mbpos.
  by rewrite (@sup_at_addD R P Mb (c a) (sumsup_chain A') (cch a) ca_ubMb
       (sumsup_chain_ch A') sumA'_ubMb dch dubMb Mbpos).
change (precone_add (cone_sup_at (cch a) ca_ubMb Mbpos)
          (cone_sup_at (sumsup_chain_ch A') sumA'_ubMb Mbpos) <=p y).
rewrite key.
apply: cone_sup_at_lub => n.
by apply: precone_le_trans (Hy n); rewrite splitE; exact: precone_le_refl.
Qed.

End SumSup.

Arguments sumsup_chain {R P T} c A n.
Arguments sum_cone_sup_ub {R P T c} cch cub A n.
Arguments sum_cone_sup_lub {R P T c} cch cub A y.

(** ** (Normc) — the unit-ball supremum of a chain of stable maps
    — Paper §7.2 (Lemma 7.14)

    Given a [≤p]-increasing chain [(uₙ)] of stable maps with
    [sh_norm (uₙ) ≤ 1], the pointwise supremum
    [f_sup x := sup_n (uₙ x)] (taken in [C] for [x ∈ B_B], and [0] off
    the unit ball, in keeping with the canonical 0-extension carrier) is
    again a stable map of norm [≤ 1], and it is the least upper bound of
    the chain.

    The 0-extension makes this construction much cleaner than [linhom]'s
    (no uniform rescaling): the input chains for ω-continuity
    ([is_scott_continuous_unit]) and the paths for measurability are
    *already* in [B_B], so the supremum always lands in the on-ball
    branch.  The two-sup commutation reuses a self-contained copy
    [sh_sup_swap] of [linhom]'s [cone_sup_ball_swap] (working in the
    codomain cone [C]). *)

Local Open Scope precone_scope.

(** A self-contained two-sup commutation in any [coneType]: the iterated
    unit-ball supremum of a doubly-indexed family commutes.  Mirrors
    [homs/linhom.v]'s [cone_sup_ball_swap]; placed here to avoid a
    dependency on the linear-map development. *)
Section ConeSupBallSwap.
Variables (R : realType) (C : coneType R).

Lemma sh_sup_swap (b : nat -> nat -> C)
    (b_row_ch : forall k n, b n k <=p b n.+1 k)
    (b_col_ch : forall n k, b n k <=p b n k.+1)
    (b_ub : forall n k, cnorm (b n k) <= 1)
    (b_col_sup_ub : forall n,
       cnorm (cone_sup_ball (b n) (b_col_ch n) (fun k => b_ub n k)) <= 1)
    (b_col_sup_ch : forall n,
       cone_sup_ball (b n) (b_col_ch n) (fun k => b_ub n k) <=p
       cone_sup_ball (b n.+1) (b_col_ch n.+1) (fun k => b_ub n.+1 k))
    (b_row_sup_ub : forall k,
       cnorm (cone_sup_ball (b^~ k) (b_row_ch k) (fun n => b_ub n k))
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

End ConeSupBallSwap.

Arguments sh_sup_swap {R C}.

Section StablehomSupBall.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : MCone.type Ar.

Variable u : nat -> stablehom B C.
Hypothesis uch : forall n, precone_le (u n) (u n.+1).
Hypothesis ub1 : forall n, sh_norm (u n) <= 1.

(** The pointwise chain at [x] is [≤p]-increasing in [C]. *)
Lemma sh_sup_pw_chain (x : B) n :
  sh_fun (u n) x <=p sh_fun (u n.+1) x.
Proof. exact: sh_le_pointwise (uch n) x. Qed.

(** The 0-truncated pointwise chain: [uₙ x] on [B_B], [0] off it.  Its
    unit-ball bound and increasingness hold *unconditionally* (the
    off-ball value is [0]), so no dependent proof witness is needed in
    the [cone_sup_ball] — sidestepping the dependent-[boolP] match. *)
Definition sh_sup_seq (x : B) (n : nat) : C :=
  if cone_norm x <= 1 then sh_fun (u n) x else precone_zero.

Lemma sh_sup_seq_chain (x : B) n : sh_sup_seq x n <=p sh_sup_seq x n.+1.
Proof.
rewrite /sh_sup_seq; case: ifP => _; last exact: precone_le_refl.
exact: sh_sup_pw_chain.
Qed.

Lemma sh_sup_seq_ub1 (x : B) n : cnorm (sh_sup_seq x n) <= 1.
Proof.
rewrite /sh_sup_seq; case: ifP => [Hx|_]; last by rewrite cone_norm0.
by apply: le_trans (ub1 n); exact: sh_norm_ub.
Qed.

(** The supremum map: the sup of the 0-truncated chain.  On [B_B] it is
    [sup_n (uₙ x)]; off [B_B] it is the sup of the constant-[0] chain,
    i.e. [0] — the canonical 0-extension. *)
Definition sh_sup_fun (x : B) : C :=
  cone_sup_ball (sh_sup_seq x) (@sh_sup_seq_chain x) (@sh_sup_seq_ub1 x).

(** Off-ball computation rule: the canonical 0-extension. *)
Lemma sh_sup_fun_off (x : B) : ~~ (cone_norm x <= 1) -> sh_sup_fun x = 0.
Proof.
move=> Hx; rewrite /sh_sup_fun; apply: precone_le_anti; last exact: precone_le0.
apply: cone_sup_ball_lub => n.
by rewrite /sh_sup_seq (negbTE Hx); exact: precone_le_refl.
Qed.

(** Every chain element is below the supremum (on-ball this is the
    pointwise [uₙ x]; off-ball both sides are [0]). *)
Lemma sh_sup_fun_ge (x : B) n : sh_sup_seq x n <=p sh_sup_fun x.
Proof. exact: cone_sup_ball_ub. Qed.

(** Least upper bound: any pointwise upper bound dominates the sup. *)
Lemma sh_sup_fun_lub (x : B) (y : C) :
  (forall n, sh_sup_seq x n <=p y) -> sh_sup_fun x <=p y.
Proof. exact: cone_sup_ball_lub. Qed.

(** The sup map lands in the unit ball pointwise. *)
Lemma sh_sup_fun_norm (x : B) : cnorm (sh_sup_fun x) <= 1.
Proof. exact: cone_sup_ball_norm. Qed.

(** On-ball: the truncated chain is the genuine pointwise chain. *)
Lemma sh_sup_seqE (x : B) (Hx : cone_norm x <= 1) n :
  sh_sup_seq x n = sh_fun (u n) x.
Proof. by rewrite /sh_sup_seq Hx. Qed.

(** On-ball upper bound: [uₙ x ≤p sup]. *)
Lemma sh_sup_fun_ubP (x : B) (Hx : cone_norm x <= 1) n :
  sh_fun (u n) x <=p sh_sup_fun x.
Proof. by rewrite -(sh_sup_seqE Hx); exact: sh_sup_fun_ge. Qed.

(** On-ball least upper bound: any pointwise bound on [uₙ x] dominates. *)
Lemma sh_sup_fun_lubP (x : B) (Hx : cone_norm x <= 1) (y : C) :
  (forall n, sh_fun (u n) x <=p y) -> sh_sup_fun x <=p y.
Proof. by move=> Hy; apply: sh_sup_fun_lub => n; rewrite sh_sup_seqE. Qed.

(** On-ball: [sh_sup_fun x] equals the genuine pointwise [cone_sup_ball]
    of [m ↦ uₘ x], for any pointwise chain / bound proofs (proof-
    irrelevant). *)
Lemma sh_sup_fun_unitE (x : B) (Hx : cone_norm x <= 1)
    (ch : forall m, sh_fun (u m) x <=p sh_fun (u m.+1) x)
    (b1 : forall m, cnorm (sh_fun (u m) x) <= 1) :
  sh_sup_fun x = cone_sup_ball (fun m => sh_fun (u m) x) ch b1.
Proof.
apply: precone_le_anti.
- apply: (sh_sup_fun_lubP Hx) => m; exact: cone_sup_ball_ub.
- by apply: cone_sup_ball_lub => m; exact: (sh_sup_fun_ubP Hx m).
Qed.

(** ** Total monotonicity of the supremum

    All [tm_arg]s lie in [B_B] (each is [≤p] the full-set argument, which
    is [≤ 1] by hypothesis, so [≤ 1] by (Normp)).  On [B_B] the sup is
    the pointwise [cone_sup_ball], so each (7.1) cone-sum equals the
    supremum of the diagonal cone-sum chain ([sum_cone_sup_ub] /
    [sum_cone_sup_lub]).  Total monotonicity of each [uₘ] gives
    [∑_{Pneg} uₘ aᵢ ≤p ∑_{Ppos} uₘ aᵢ] pointwise in [m]; combining with
    the sum/sup identities yields (7.1) for the supremum. *)
Lemma sh_sup_totmono : is_totmono sh_sup_fun.
Proof.
move=> k x u' Hfull.
(* All arguments [a I] are in the unit ball (≤p the full-set argument). *)
have argle (I : {set 'I_k}) :
    tm_arg x u' I <=p x + \big[precone_add/precone_zero]_(i : 'I_k) u' i.
  rewrite /tm_arg; apply: precone_add_le_l.
  rewrite [X in _ <=p X](bigID (mem I)) /=.
  rewrite (eq_bigl (mem I)) // -/(precone_add _ _).
  by exists (\big[precone_add/precone_zero]_(i | i \notin I) u' i).
have argub (I : {set 'I_k}) : cone_norm (tm_arg x u' I) <= 1.
  by apply: le_trans Hfull; apply: cone_normp; exact: argle.
(* The doubly-indexed family [c I m := uₘ (a I)]. *)
pose c (I : {set 'I_k}) (m : nat) : C := sh_fun (u m) (tm_arg x u' I).
have cch I m : c I m <=p c I m.+1 by exact: sh_le_pointwise (uch m) _.
have cub I m : cnorm (c I m) <= 1.
  by apply: le_trans (ub1 m); exact: sh_norm_ub _ _ (argub I).
(* The sup at each argument is [cone_sup_ball] of [c I]. *)
have supE I : sh_sup_fun (tm_arg x u' I) =
              cone_sup_ball (c I) (cch I) (cub I).
  apply: precone_le_anti.
  - apply: (sh_sup_fun_lubP (argub I)) => m.
    by rewrite /c; exact: (cone_sup_ball_ub (c I) (cch I) (cub I) m).
  - apply: cone_sup_ball_lub => m.
    by rewrite /c; exact: (sh_sup_fun_ubP (argub I) m).
rewrite (eq_bigr _ (fun I _ => supE I)).
rewrite [X in precone_le _ X](eq_bigr _ (fun I _ => supE I)).
(* RHS is an upper bound for the [Pneg]-diagonal chain. *)
apply: (sum_cone_sup_lub cch cub) => m.
apply: (@precone_le_trans _ _ (sumsup_chain c (Ppos k) m)).
  have [Htm _ _] := (sh_meas_stable (u m)).1.
  have Htm' := Htm k x u' Hfull.
  by rewrite /sumsup_chain /c.
exact: (sum_cone_sup_ub cch cub (Ppos k) m).
Qed.

(** Boundedness: the supremum lands in [B_C], so [‖·‖ ≤ 1]. *)
Lemma sh_sup_bounded :
  exists M : R, forall x : B, cone_norm x <= 1 -> cnorm (sh_sup_fun x) <= M.
Proof. by exists 1 => x _; exact: sh_sup_fun_norm. Qed.

(** ** ω-continuity (Scott, unit ball) of the supremum

    For a unit-ball input chain [(vₖ)] with sup [s = cone_sup_ball v],
    everything stays in [B_B], so [sh_sup_fun] is computed pointwise.
    Writing [b m k := uₘ (vₖ)], we have
    [sh_sup_fun s = sup_m (uₘ s) = sup_m sup_k (b m k)]
    (ω-continuity of each [uₘ] at image radius [1]), which by the two-sup
    commutation [sh_sup_swap] equals
    [sup_k sup_m (b m k) = sup_k (sh_sup_fun vₖ)].  The radius-aware
    target [cone_sup_at] reduces to [cone_sup_ball] since the image of
    [sh_sup_fun] is in [B_C]. *)
Lemma sh_sup_scott : is_scott_continuous_unit sh_sup_fun.
Proof.
move=> Mf v vch vb1 fvch fvbMf Mfpos.
set s := cone_sup_ball v vch vb1.
have Hs : cone_norm s <= 1 by exact: cone_sup_ball_norm.
have Hvk k : cone_norm (v k) <= 1 by exact: vb1.
(* The doubly-indexed family [b m k := uₘ (vₖ)]. *)
pose b (m k : nat) : C := sh_fun (u m) (v k).
have b_row_ch k m : b m k <=p b m.+1 k by exact: sh_le_pointwise (uch m) _.
have b_col_ch m k : b m k <=p b m k.+1.
  rewrite /b; have [[Htm _ _] _] := sh_meas_stable (u m).
  by apply: (tm_incr_le Htm (vch k)); exact: vb1.
have b_ub m k : cnorm (b m k) <= 1.
  by apply: le_trans (ub1 m); exact: sh_norm_ub _ _ (Hvk k).
(* Column sups [sup_k (b m k) = uₘ s] (ω-continuity of [uₘ] at radius 1). *)
have b_col_sup_ub m :
    cnorm (cone_sup_ball (b m) (b_col_ch m) (fun k => b_ub m k)) <= 1.
  exact: cone_sup_ball_norm.
have b_col_sup_ch m :
    cone_sup_ball (b m) (b_col_ch m) (fun k => b_ub m k) <=p
    cone_sup_ball (b m.+1) (b_col_ch m.+1) (fun k => b_ub m.+1 k).
  apply: cone_sup_ball_lub => k.
  apply: precone_le_trans (b_row_ch k m) _; exact: cone_sup_ball_ub.
have b_row_sup_ub k :
    cnorm (cone_sup_ball (b^~ k) (b_row_ch k) (fun m => b_ub m k)) <= 1.
  exact: cone_sup_ball_norm.
have b_row_sup_ch k :
    cone_sup_ball (b^~ k) (b_row_ch k) (fun m => b_ub m k) <=p
    cone_sup_ball (b^~ k.+1) (b_row_ch k.+1) (fun m => b_ub m k.+1).
  apply: cone_sup_ball_lub => m.
  apply: precone_le_trans (b_col_ch m k) _; exact: cone_sup_ball_ub.
(* [uₘ s = cone_sup_ball_k (b m k)] by ω-continuity of [uₘ] at radius 1. *)
have um_s_eq m :
    sh_fun (u m) s = cone_sup_ball (b m) (b_col_ch m) (fun k => b_ub m k).
  have [[_ _ Hcont] _] := sh_meas_stable (u m).
  have b_ub1 k : cnorm (sh_fun (u m) (v k)) <= (1%:nng : {nonneg R})%:num.
    by rewrite /=; apply: le_trans (ub1 m); exact: sh_norm_ub _ _ (Hvk k).
  have pos1 : (0%R < (1%:nng : {nonneg R})%:num)%R by rewrite /= ltr01.
  rewrite (Hcont 1%:nng v vch vb1 (b_col_ch m) b_ub1 pos1).
  rewrite (@cone_sup_at_ball _ _ (fun k => sh_fun (u m) (v k))
             (b_col_ch m) (fun k => b_ub m k) b_ub1 pos1).
  by congr cone_sup_ball; exact: Prop_irrelevance.
(* [sh_sup_fun s = cone_sup_ball_m (uₘ s) = LHS-iterated sup]. *)
have LHS_eq : sh_sup_fun s =
    cone_sup_ball
      (fun m => cone_sup_ball (b m) (b_col_ch m) (fun k => b_ub m k))
      b_col_sup_ch b_col_sup_ub.
  have ch m : sh_fun (u m) s <=p sh_fun (u m.+1) s.
    exact: sh_le_pointwise (uch m) _.
  have b1 m : cnorm (sh_fun (u m) s) <= 1.
    by apply: le_trans (ub1 m); exact: sh_norm_ub _ _ Hs.
  rewrite (sh_sup_fun_unitE Hs ch b1).
  apply: precone_le_anti.
  - apply: cone_sup_ball_lub => m /=.
    rewrite um_s_eq; exact: cone_sup_ball_ub.
  - apply: cone_sup_ball_lub => m /=.
    rewrite -um_s_eq; exact: cone_sup_ball_ub.
(* [sh_sup_fun vₖ = cone_sup_ball_m (b m k)] (on-ball at [vₖ]). *)
have sup_vk_eq k :
    sh_sup_fun (v k) =
    cone_sup_ball (b^~ k) (b_row_ch k) (fun m => b_ub m k).
  by rewrite (sh_sup_fun_unitE (Hvk k) (b_row_ch k) (fun m => b_ub m k)).
(* Reduce the radius-aware target to a [cone_sup_ball] at radius 1. *)
have RHS_eq :
    cone_sup_at (u := sh_sup_fun \o v) fvch fvbMf Mfpos =
    cone_sup_ball
      (fun k => cone_sup_ball (b^~ k) (b_row_ch k) (fun m => b_ub m k))
      b_row_sup_ch b_row_sup_ub.
  have pos1 : (0%R < (1%:nng : {nonneg R})%:num)%R by rewrite /= ltr01.
  have fvb1 k : cnorm ((sh_sup_fun \o v) k) <= (1%:nng : {nonneg R})%:num.
    by rewrite /=; exact: sh_sup_fun_norm.
  rewrite (cone_sup_at_indep fvch fvbMf fvb1 Mfpos pos1).
  rewrite (@cone_sup_at_ball _ _ (sh_sup_fun \o v) fvch fvb1 fvb1 pos1).
  apply: precone_le_anti.
  - apply: cone_sup_ball_lub => k /=.
    rewrite sup_vk_eq; exact: cone_sup_ball_ub.
  - apply: cone_sup_ball_lub => k /=.
    rewrite -sup_vk_eq; exact: cone_sup_ball_ub.
rewrite LHS_eq RHS_eq.
exact: (sh_sup_swap b b_row_ch b_col_ch b_ub).
Qed.

(** ** Path-preservation of the supremum

    For a unit-ball measurable path [γ] (so each [γ r ∈ B_B]),
    [sh_sup_fun (γ r) = sup_m (uₘ (γ r))] pointwise, and each [uₘ]
    preserves paths.  For a test [m], the value
    [test m s (sh_sup_fun (γ r))] is the supremum of
    [test m s (uₘ (γ r))] (an increasing chain, via [test_cont] +
    monotonicity), so it is measurable as a pointwise limit
    ([measurable_fun_cvg]) of the measurable test-paths of [uₘ]. *)
Lemma sh_sup_pres_path (X : ar_obj Ar) (γ : ar_carrier Ar X -> B) :
  (forall r, cone_norm (γ r) <= 1) ->
  is_measurable_path (Ar:=Ar) (C:=B) γ ->
  is_measurable_path (Ar:=Ar) (C:=C) (fun r => sh_sup_fun (γ r)).
Proof.
move=> Hγ1 Hγ; split.
  by exists 1 => r; exact: sh_sup_fun_norm.
move=> Y m mM.
(* Each [uₘ] preserves the path. *)
have um_path k : is_measurable_path (Ar:=Ar) (C:=C)
    (fun r => sh_fun (u k) (γ r)).
  by have [_ Hp] := sh_meas_stable (u k); exact: Hp.
(* The chain [h k (s,r) := test m s (uₖ (γ r))]. *)
pose h (k : nat) (p : (ar_carrier Ar Y * ar_carrier Ar X)%type) : R :=
  test_fun m p.1 (sh_fun (u k) (γ p.2)).
have h_ch p k : (h k p <= h k.+1 p)%R.
  rewrite /h.
  have [z ->] : sh_fun (u k) (γ p.2) <=p sh_fun (u k.+1) (γ p.2).
    exact: sh_le_pointwise (uch k) _.
  by rewrite test_linD lerDl; exact: test_ge0.
have h_ub p : has_ubound (range (h ^~ p)).
  exists 1 => _ [k _ <-]; rewrite /h; apply: test_le1.
  by apply: le_trans (ub1 k); exact: sh_norm_ub _ _ (Hγ1 p.2).
have h_cvg p : (h ^~ p : nat -> R) @ \oo --> (sup (range (h ^~ p)) : R^o).
  apply: nondecreasing_cvgn; last exact: h_ub.
  by apply/nondecreasing_seqP => k; exact: h_ch.
(* The target value is the sup of the chain. *)
have target_eq p :
    test_fun m p.1 (sh_sup_fun (γ p.2)) = sup (range (h ^~ p)).
  have Hγp : cone_norm (γ p.2) <= 1 by exact: Hγ1.
  have ch k : sh_fun (u k) (γ p.2) <=p sh_fun (u k.+1) (γ p.2).
    exact: sh_le_pointwise (uch k) _.
  have b1 k : cnorm (sh_fun (u k) (γ p.2)) <= 1.
    by apply: le_trans (ub1 k); exact: sh_norm_ub _ _ Hγp.
  apply: le_anti; apply/andP; split.
  - rewrite (sh_sup_fun_unitE Hγp ch b1).
    have hsup : has_sup (range (h ^~ p)).
      by split; [by exists (h 0%N p), 0%N | exact: h_ub].
    apply: test_cont => k.
    by move/ubP : (sup_upper_bound hsup); apply; exists k.
  - apply: ge_sup; first by exists (h 0%N p), 0%N.
    move=> _ [k _ <-]; rewrite /h.
    have Hub : sh_fun (u k) (γ p.2) <=p sh_sup_fun (γ p.2).
      exact: (sh_sup_fun_ubP Hγp k).
    case: Hub => [z ->]; rewrite test_linD lerDl; exact: test_ge0.
have -> : (fun p : ar_carrier Ar Y * ar_carrier Ar X =>
            test_fun m p.1 (sh_sup_fun (γ p.2))) =
          (fun p => sup [set h i p | i in [set: nat]]).
  by apply: funext => p; exact: target_eq.
apply: (measurable_fun_cvg (h := h)).
- by move=> k; have [_ Hmeas] := um_path k; exact: Hmeas.
- by move=> p _; exact: h_cvg.
Qed.

(** Off-ball canonical 0-extension of the supremum map. *)
Lemma sh_sup_offball (x : B) : ~~ (cone_norm x <= 1) -> sh_sup_fun x = 0.
Proof. exact: sh_sup_fun_off. Qed.

(** Measurable-stability of the supremum map. *)
Lemma sh_sup_meas_stable : is_meas_stable sh_sup_fun.
Proof.
split; last exact: sh_sup_pres_path.
by split; [exact: sh_sup_totmono | exact: sh_sup_bounded | exact: sh_sup_scott].
Qed.

(** The supremum packaged as a [stablehom]. *)
Definition sh_sup : stablehom B C :=
  MkStablehom sh_sup_fun sh_sup_meas_stable sh_sup_offball.

(** ** [sh_sup] is the least upper bound in the *cone* order

    The precone order [f ≤p g := ∃δ:stablehom, g = f + δ] needs a
    [stablehom] witness for the difference.  We obtain it WITHOUT a
    general "difference of stable maps is stable" lemma, by re-using the
    [sh_sup] construction on a *difference chain* whose terms are
    supplied — already as [stablehom]s — by the chain order itself.

    Concretely, for the upper bound [uₙ ≤p sh_sup]: the order witnesses
    [δₘ] of [uₙ ≤p u_{n+m}] (from chain transitivity) form an increasing
    unit-norm chain of [stablehom]s, so [sh_sup] of *that* chain is a
    [stablehom]; pointwise [sup_m u_{n+m} = uₙ + sup_m δₘ]
    ([sup_ball_addr]), and [sup_m u_{n+m} = sh_sup] by cofinality, giving
    the witness. *)

(** Chain monotonicity at the [stablehom] level. *)
Lemma sh_chain_mono (n m : nat) : (n <= m)%N -> precone_le (u n) (u m).
Proof.
elim: m => [|m IHm]; first by rewrite leqn0 => /eqP ->; exact: precone_le_refl.
rewrite leq_eqVlt => /predU1P[->|]; first exact: precone_le_refl.
by rewrite ltnS => /IHm Hnm; apply: precone_le_trans Hnm _; exact: uch.
Qed.

End StablehomSupBall.

(**md**************************************************************)
(** ** Status — what is delivered and what is deferred (and why)

    Delivered (no holes, no project axioms — only the ambient
    classical axioms propositional/functional extensionality and
    indefinite description, used pervasively across the development):

    - **Carrier redesign — the canonical 0-extension.**  [stablehom B C]
      now carries a third field [sh_offball : ∀ x, ¬(‖x‖ ≤ 1) → f x = 0]
      forcing the map to vanish outside [B_B].  This makes [B_B]-
      behaviour determine [f] (two stable maps agreeing on [B_B] also
      agree off it — both are [0]), the property (Normz) needs.  All
      three operations [sh_zero]/[sh_add]/[sh_scale] carry the field
      ([sh_zero_offball]/[sh_add_offball]/[sh_scale_offball]) and the
      **[isPrecone] HB instance survives**: [stablehom B C : preconeType
      R].  Extensionality [stablehom_eq] is unchanged (the two proof
      fields are [Prop]-irrelevant).
    - Lemma 7.12 (induced order) [sh_le_pointwise]; Lemma 7.14 norm
      [sh_norm] with (Normh)/(Normt)/(Normp).
    - **(Normz) [sh_normz] — PROVED** (the payoff of the redesign):
      [‖f‖ = 0 ⇒ f = sh_zero].  On [B_B] the sup forces [f x = 0]; off
      [B_B] the field [sh_offball] gives [f x = 0]; hence [f = sh_zero].
    - **(Normc) supremum machinery — PROVED.**  The pointwise supremum
      [sh_sup] of a [≤p]-increasing unit-norm chain of stable maps
      ([cone_sup_ball] on [B_B], canonical [0] off it) is a genuine
      [stablehom] ([sh_sup_meas_stable]):
        * [sh_sup_totmono] — total monotonicity, via the finite-cone-sum
          / supremum commutation engine [sum_cone_sup_ub] /
          [sum_cone_sup_lub] ([SumSup] section: a finite cone-sum of
          per-index suprema is the radius-[#|A|] [cone_sup_at] of the
          diagonal sum chain, proved by cardinality induction from the
          binary [sup_at_addD]).
        * [sh_sup_scott] — ω-continuity (Scott, unit ball), via the
          two-sup commutation [sh_sup_swap] (a self-contained port of
          [linhom]'s [cone_sup_ball_swap]).
        * [sh_sup_bounded] — norm [≤ 1]; [sh_sup_pres_path] — path
          preservation, via [test_cont] + [measurable_fun_cvg] (no
          uniform rescaling needed: unit-ball paths stay in [B_B]).
        * [sh_sup_offball] — the canonical 0-extension.

    Deferred — the final [isCone] HB instance (and hence [isMCone] /
    [isICone]).  Only ONE ingredient remains: the [cone_sup_ball] mixin
    fields [cone_sup_ball_ub] / [cone_sup_ball_lub] require, for the
    precone order [f ≤p g := ∃δ:stablehom, g = f + δ], that the
    *pointwise difference* of two order-related stable maps is itself a
    [stablehom] (the [linhom_diff] analog).  For *linear* maps this
    difference is linear, hence trivially in the carrier; for *nonlinear
    stable* maps the difference of two totally-monotonic maps is not in
    general totally monotonic (subtracting the two (7.1) inequalities is
    invalid in a cone), so a dedicated argument is needed to show the
    specific differences arising here ([sh_sup ⊖ uₙ], [y ⊖ sh_sup]) are
    stable.  This "difference-is-stable" lemma is the sole gap to
    [isCone]; the supremum object and all its stability proofs (the bulk
    of (Normc)) are already in place above.

    [isMCone] (the [γ ▷ m] test family) and [isICone] (integrability)
    follow the [linhom]/[path]/[examples_icone] templates once [isCone]
    is registered; they are not attempted here. *)
