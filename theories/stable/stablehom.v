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

    The full cone structure is now delivered (see the closing status
    block): the **[isCone] HB instance is REGISTERED** — [stablehom B C :
    coneType R].  (Normz) is unblocked by the canonical 0-extension
    carrier (the [sh_offball] field), and (Normc) is discharged by the
    pointwise supremum [sh_sup] together with the difference-is-stable
    construction (Lemma 7.12 backward, [sh_diff]) supplying the precone-
    order witnesses [sh_sup ⊖ uₙ] / [y ⊖ sh_sup] required by the
    [cone_sup_ball] mixin.  The measurability structure [isMCone] (the
    [γ ▷ m] test family, txt 3365) is also REGISTERED — [stablehom B C :
    mconeType Ar].  Only the integrability [isICone] (txt 3372) remains
    (see the closing status block for why it is deferred). *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
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
Require Import Icones.icones.pettis.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_integral.
Require Import Icones.mcones.test_pullback.

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

(** ** Adding a constant on the left commutes with the finite-sum-sup

    [Z + Σ_A cone_sup_ball(c)] is the lub of [(Z + sumsup_chain c A m)_m]:
    the finite cone-sum of per-index suprema equals the radius-[#|A|+1]
    [cone_sup_at] of the diagonal sum chain ([sum_cone_sup_eq], via
    [sum_cone_sup_ub] / [sum_cone_sup_lub] + [cone_sup_at] antisymmetry),
    and adding [Z] on the left commutes through [cone_sup_at]
    ([sup_at_addr], after a [precone_addC]).  This is the cone fact behind
    the supremum-passage of the alternating condition (Lemma 7.12). *)
Section AddlSumConeSup.
Variable R : realType.
Variable P : coneType R.
Variable T : finType.
Variable c : T -> nat -> P.
Hypothesis cch : forall i n, c i n <=p c i n.+1.
Hypothesis cub : forall i n, cnorm (c i n) <= 1.
Local Open Scope precone_scope.

(** [Σ_A cone_sup_ball(c)] as a radius-[#|A|+1] [cone_sup_at]. *)
Lemma sum_cone_sup_eq (A : {set T}) :
  \big[precone_add/precone_zero]_(i in A)
     (cone_sup_ball (c i) (cch i) (cub i)) =
  cone_sup_at (sumsup_chain_ch cch A) (sumsup_chain_radius cub A)
              (sumsup_radius_pos R A).
Proof.
apply: precone_le_anti.
- apply: (sum_cone_sup_lub cch cub) => m; exact: cone_sup_at_ub.
- by apply: cone_sup_at_lub => m; exact: (sum_cone_sup_ub cch cub).
Qed.

(** Left-add commutes: [Z + Σ_A cone_sup_ball(c) ≤p V] reduces to the
    pointwise diagonal bound [Z + sumsup_chain c A m ≤p V]. *)
Lemma addl_sum_cone_sup_lub (A : {set T}) (Z V : P) :
  (forall m, Z + sumsup_chain c A m <=p V) ->
  Z + \big[precone_add/precone_zero]_(i in A)
        (cone_sup_ball (c i) (cch i) (cub i)) <=p V.
Proof.
move=> HZ.
rewrite sum_cone_sup_eq.
set Mpos := sumsup_radius_pos R A.
set ch := sumsup_chain_ch cch A.
set ub := sumsup_chain_radius cub A.
(* [Z + cone_sup_at = cone_sup_at (sumsup_chain + Z)] (right form). *)
have azch m : sumsup_chain c A m + Z <=p sumsup_chain c A m.+1 + Z.
  by apply: precone_add_le_r; exact: ch.
have Kge0 : (0 <= (sumsup_radius R A)%:num + cnorm Z)%R.
  by rewrite addr_ge0 // ?cone_norm_ge0 // ltW.
pose K : {nonneg R} := NngNum Kge0.
have Kpos : (0 < K%:num)%R.
  by apply: lt_le_trans Mpos _; rewrite /= lerDl cone_norm_ge0.
have azub m : cnorm (sumsup_chain c A m + Z) <= K%:num.
  apply: le_trans (cone_normt _ _) _.
  by rewrite /= lerD2r; exact: ub.
have ubK m : cnorm (sumsup_chain c A m) <= K%:num.
  by apply: le_trans (ub m) _; rewrite /= lerDl cone_norm_ge0.
rewrite (cone_sup_at_indep ch ub ubK Mpos Kpos) precone_addC.
rewrite -(sup_at_addr ch ubK azch azub Kpos).
by apply: cone_sup_at_lub => m; rewrite precone_addC; exact: HZ.
Qed.

End AddlSumConeSup.

Arguments sum_cone_sup_eq {R P T c} cch cub A.
Arguments addl_sum_cone_sup_lub {R P T c} cch cub A Z V.

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

(** ** Radius-aware ω-continuity of a difference — Paper Lemma 2.10
       (general image radius)

    The codomain difference [w = g − f] (with [g x = f x + w x]) is
    ω-continuous on the unit ball *at any image radius* [Mf], provided
    [f] is increasing and [g] is Scott-continuous ([is_scott_continuous],
    [omega_general.v]).  This is the radius-aware analogue of
    [basic_lemmas.v]'s [diff_omega_continuous] (Lemma 2.10): we replace
    the unit-ball [cone_sup_ball] of the conclusion by the radius-[Mf]
    [cone_sup_at], use [g]'s Scott-continuity at input radius [1]
    ([cone_sup_at_ball] identifies the input [cone_sup_ball] with the
    radius-[1] [cone_sup_at]), and recombine the image suprema with the
    radius-aware [addl_scott_continuous].  Used below for the
    Scott-continuity of the stable difference [y ⊖ sh_sup] of Lemma 7.12
    backward (where the upper bound [y] has unconstrained norm). *)

Section DiffScottAt.
Variable R : realType.
Variables P Q : coneType R.
Local Open Scope precone_scope.

Lemma diff_scott_at
  (f g w : P -> Q)
  (Hg_cont : is_scott_continuous_unit g)
  (Hsplit : forall x, g x = f x + w x)
  (Mf Mg : {nonneg R}) (u : nat -> P)
  (uch : forall n, precone_le (u n) (u n.+1))
  (ub1 : forall n, cone_norm (u n) <= 1)
  (fxle : forall n, precone_le (f (u n)) (f (cone_sup_ball u uch ub1)))
  (wuch : forall n, precone_le (w (u n)) (w (u n.+1)))
  (wxch : forall n, precone_le (w (u n)) (w (cone_sup_ball u uch ub1)))
  (wubMf : forall n, cone_norm (w (u n)) <= Mf%:num)
  (Mfpos : (0 < Mf%:num)%R)
  (guch : forall n, precone_le (g (u n)) (g (u n.+1)))
  (gubMg : forall n, cone_norm (g (u n)) <= Mg%:num)
  (Mgpos : (0 < Mg%:num)%R) :
  w (cone_sup_ball u uch ub1) = cone_sup_at wuch wubMf Mfpos.
Proof.
set x := cone_sup_ball u uch ub1.
set y := cone_sup_at wuch wubMf Mfpos.
apply: precone_le_anti; last first.
  by apply: cone_sup_at_lub => n; exact: wxch.
(* Hard direction: [w x ≤p y].  Reduce to [f x + w x ≤p f x + y]. *)
have gx_eq : g x = cone_sup_at guch gubMg Mgpos.
  by rewrite /x (Hg_cont Mg u uch ub1 guch gubMg Mgpos).
have step1 n : precone_le (g (u n)) (f x + w (u n)).
  by rewrite (Hsplit (u n)); apply: precone_add_le_r; exact: fxle.
have Kge0 : (0 <= cone_norm (f x) + Mf%:num)%R.
  by rewrite addr_ge0 // ?cone_norm_ge0 // ltW.
pose K : {nonneg R} := NngNum Kge0.
have Kpos : (0 < K%:num)%R.
  by rewrite /= -[X in (X < _)%R]addr0 ler_ltD // ?cone_norm_ge0.
have fwch n : f x + w (u n) <=p f x + w (u n.+1).
  by apply: precone_add_le_l; exact: wuch.
have fwub n : cone_norm (f x + w (u n)) <= K%:num.
  by apply: le_trans (cone_normt _ _) _; rewrite /= lerD2l; exact: wubMf.
have step2 n : precone_le (g (u n)) (cone_sup_at fwch fwub Kpos).
  by apply: precone_le_trans (step1 n) _; exact: cone_sup_at_ub.
have step3 : precone_le (cone_sup_at guch gubMg Mgpos)
                        (cone_sup_at fwch fwub Kpos).
  by apply: cone_sup_at_lub => n; exact: step2.
have sumeq : cone_sup_at fwch fwub Kpos = f x + y.
  rewrite /y.
  by rewrite -(addl_scott_continuous (f x) Mf K (w \o u) wuch wubMf Mfpos
                fwch fwub Kpos).
have gx_le : precone_le (g x) (f x + y).
  by rewrite gx_eq -sumeq; exact: step3.
move: gx_le; rewrite (Hsplit x) => -[z Hz].
exists z.
have Hz' : f x + y = f x + (w x + z) by rewrite Hz -precone_addA.
exact: precone_cancel Hz'.
Qed.

End DiffScottAt.

Arguments diff_scott_at {R P Q f g w} Hg_cont Hsplit {Mf Mg u}.

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

(** ** Precone order left-cancellation
    [z + a ≤p z + b] entails [a ≤p b]: the difference witness commutes
    past [z] and is removed by left cancellation [precone_cancel]. *)
Section PreconeLeCancel.
Variable R : realType.
Variable P : preconeType R.
Local Open Scope precone_scope.

Lemma precone_le_addlI (z a b : P) : z + a <=p z + b -> a <=p b.
Proof.
move=> [w Hw]; exists w.
apply: (@precone_cancel R P z b (a + w)).
by rewrite Hw precone_addA.
Qed.

End PreconeLeCancel.

Arguments precone_le_addlI {R P z a b}.

(** ** Lemma 7.12 backward — the difference of two stable maps is stable
    — Paper §7.2 (txt 3345)
//
    Given [f, g : stablehom B C] with [f ≤ g] in the *stable* order —
    here split into the pointwise comparison [Hpw] (the [n = 0] case of
    Lemma 7.12) and the alternating condition [Halt] (the additive,
    subtraction-free form of "[g − f] is totally monotonic") — we build
    the difference [h := g ⊖ f] as a genuine [stablehom] satisfying
    [sh_add f h = g], i.e. [f ≤p g] in the precone order.
//
    The pointwise difference [shd_fun x] is the cone-cancellation witness
    of [f x ≤p g x] (extracted by [cid] from the *total* comparison
    [shd_le], which off the unit ball is [0 ≤p 0]); off [B_B] it collapses
    to [0] (the equation [0 = 0 + z] forces [z = 0]), preserving the
    canonical 0-extension.  Its three stability facts:
    - **total monotonicity** ([shd_totmono]) — substitute [g(a) = f(a) +
      h(a)] into [Halt], split the cone-sums ([sumP_add]), and cancel the
      common [Σf]-term in the precone order ([precone_le_addlI]); what
      remains is [Σ_{P⁻} h ≤p Σ_{P⁺} h], i.e. (7.1) for [h].
    - **ω-continuity** ([shd_scott]) — the radius-aware Lemma 2.10
      [diff_scott_at] (with [f] increasing, [g] Scott-continuous via the
      [is_scott_continuous] bridge [linear_scott_of_omega]…—here [g] is a
      stable map so we use its [is_scott_continuous_unit] field directly,
      repackaged as a [cone_sup_at] commutation).
    - **measurability** ([shd_pres_path]) — [test m s (h(γ r)) =
      test m s (g(γ r)) − test m s (f(γ r))] by [test_linD] on [shd_E],
      a difference of the measurable test-paths of [f], [g]
      ([measurable_funB]). *)

(** The alternating condition of Lemma 7.12: [g − f] is totally monotonic
    in additive, subtraction-free form.  Stated as a standalone predicate
    so the forward direction ([sh_alt_of_le]) and the supremum-passage
    lemmas ([sh_alt_sup_r] / [sh_alt_sup_l]) can be phrased about it. *)
Definition sh_alt (R : realType) (Ar : MeasSubcat R) (B C : MCone.type Ar)
    (f g : stablehom B C) : Prop :=
  forall (n : nat) (x : B) (v : 'I_n -> B),
    (cone_norm (x + \big[precone_add/precone_zero]_(i : 'I_n) v i)%PC <= 1) ->
    precone_le
      (\big[precone_add/precone_zero]_(I in Pneg n) sh_fun g (tm_arg x v I)
       + \big[precone_add/precone_zero]_(I in Ppos n) sh_fun f (tm_arg x v I))%PC
      (\big[precone_add/precone_zero]_(I in Ppos n) sh_fun g (tm_arg x v I)
       + \big[precone_add/precone_zero]_(I in Pneg n) sh_fun f (tm_arg x v I))%PC.

Arguments sh_alt {R Ar B C} f g.

Section StablehomDiff.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : MCone.type Ar.
Local Open Scope precone_scope.

Variables f g : stablehom B C.

(** The pointwise comparison on the unit ball ([n = 0] of Lemma 7.12). *)
Hypothesis Hpw :
  forall x : B, cone_norm x <= 1 -> precone_le (sh_fun f x) (sh_fun g x).

(** The alternating condition (Lemma 7.12). *)
Hypothesis Halt : sh_alt f g.

(** Pointwise comparison, made *total*: off the unit ball both maps are
    [0], so [0 ≤p 0] by reflexivity. *)
Lemma shd_le (x : B) : precone_le (sh_fun f x) (sh_fun g x).
Proof.
have [Hx | Hx] := boolP (cone_norm x <= 1); first exact: Hpw.
by rewrite (sh_offball f x Hx) (sh_offball g x Hx); exact: precone_le_refl.
Qed.

(** The pointwise difference [g x ⊖ f x] (the cone-cancellation witness). *)
Definition shd_fun (x : B) : C := projT1 (cid (shd_le x)).

(** Defining equation: [g x = f x + shd_fun x]. *)
Lemma shd_E (x : B) : sh_fun g x = sh_fun f x + shd_fun x.
Proof. exact: projT2 (cid (shd_le x)). Qed.

(** Off the unit ball the difference collapses to [0] (canonical
    0-extension): from [0 = 0 + shd_fun x = shd_fun x]. *)
Lemma shd_offball (x : B) : ~~ (cone_norm x <= 1) -> shd_fun x = 0.
Proof.
move=> Hx; have := shd_E x.
by rewrite (sh_offball f x Hx) (sh_offball g x Hx) precone_add0 => <-.
Qed.

(** Pointwise: [shd_fun x ≤p g x], hence bounded by [‖g‖]. *)
Lemma shd_le_g (x : B) : precone_le (shd_fun x) (sh_fun g x).
Proof. by exists (sh_fun f x); rewrite shd_E precone_addC. Qed.

(** *** Total monotonicity of the difference (Lemma 7.12 rearrangement) *)

(** A cone-sum of [g(a I)] splits as [Σ f(a I) + Σ shd_fun(a I)] via the
    defining equation [shd_E] and [sumP_add]. *)
Lemma shd_sumP_split (T : finType) (A : {set T}) (a : T -> B) :
  \big[precone_add/precone_zero]_(I in A) sh_fun g (a I) =
  (\big[precone_add/precone_zero]_(I in A) sh_fun f (a I))
  + (\big[precone_add/precone_zero]_(I in A) shd_fun (a I)).
Proof.
rewrite -sumP_add; apply: eq_bigr => I _; exact: shd_E.
Qed.

(** Lemma 7.12 rearrangement: the difference is totally monotonic. *)
Lemma shd_totmono : is_totmono shd_fun.
Proof.
move=> n x v Hxv.
pose a (I : {set 'I_n}) : B := tm_arg x v I.
have Hsplit_neg : \big[precone_add/precone_zero]_(I in Pneg n) sh_fun g (a I) =
    (\big[precone_add/precone_zero]_(I in Pneg n) sh_fun f (a I))
    + (\big[precone_add/precone_zero]_(I in Pneg n) shd_fun (a I)).
  exact: shd_sumP_split.
have Hsplit_pos : \big[precone_add/precone_zero]_(I in Ppos n) sh_fun g (a I) =
    (\big[precone_add/precone_zero]_(I in Ppos n) sh_fun f (a I))
    + (\big[precone_add/precone_zero]_(I in Ppos n) shd_fun (a I)).
  exact: shd_sumP_split.
set Sf_neg := \big[precone_add/precone_zero]_(I in Pneg n) sh_fun f (a I).
set Sf_pos := \big[precone_add/precone_zero]_(I in Ppos n) sh_fun f (a I).
set Sh_neg := \big[precone_add/precone_zero]_(I in Pneg n) shd_fun (a I).
set Sh_pos := \big[precone_add/precone_zero]_(I in Ppos n) shd_fun (a I).
(* [Halt] with [a] = [tm_arg x v]: [Σg⁻ + Σf⁺ ≤p Σg⁺ + Σf⁻]. *)
have HA := @Halt n x v Hxv.
rewrite -/a Hsplit_neg Hsplit_pos in HA.
(* HA : (Sf_neg + Sh_neg) + Sf_pos ≤p (Sf_pos + Sh_pos) + Sf_neg. *)
(* Rearrange both sides to (Sf_neg + Sf_pos) + S{neg,pos}. *)
apply: (precone_le_addlI (z := Sf_neg + Sf_pos)).
apply: (@precone_le_trans _ _ ((Sf_neg + Sh_neg) + Sf_pos)).
  rewrite -precone_addA [Sf_pos + Sh_neg]precone_addC precone_addA.
  exact: precone_le_refl.
apply: precone_le_trans HA _.
rewrite -[Sf_pos + Sh_pos + Sf_neg]precone_addA [Sh_pos + Sf_neg]precone_addC.
rewrite precone_addA [Sf_pos + Sf_neg]precone_addC.
exact: precone_le_refl.
Qed.

(** *** Boundedness, ω-continuity (Scott, unit ball), measurability *)

(** The difference is bounded on the unit ball by [‖g‖]. *)
Lemma shd_bounded :
  exists M : R, forall x : B, cone_norm x <= 1 -> cnorm (shd_fun x) <= M.
Proof.
exists (sh_norm g) => x Hx.
apply: le_trans (sh_norm_ub g x Hx).
exact: cone_normp (shd_le_g x).
Qed.

(** Increasingness of the difference on the unit ball (from [shd_totmono]
    via [tm_incr_le]). *)
Lemma shd_incr_le (x y : B) :
  x <=p y -> cone_norm y <= 1 -> shd_fun x <=p shd_fun y.
Proof. exact: (tm_incr_le shd_totmono). Qed.

(** ω-continuity (Scott, unit ball) of the difference, via [diff_scott_at]:
    [f] is increasing along the unit-ball chain (total monotonicity), and
    [g] is Scott-continuous (its [is_scott_continuous_unit] field). *)
Lemma shd_scott : is_scott_continuous_unit shd_fun.
Proof.
move=> Mf u uch ub1 hfuch hfubMf Mfpos.
set s := cone_sup_ball u uch ub1.
have Hs : cone_norm s <= 1 by exact: cone_sup_ball_norm.
(* [f], [g] are stable, hence totally monotonic and Scott-continuous. *)
have [[Hfm _ _] _] := sh_meas_stable f.
have [[Hgm _ Hgc] _] := sh_meas_stable g.
(* [f (u n)] ≤p [f s] (total monotonicity, [u n ≤p s], [‖s‖ ≤ 1]). *)
have fxle n : precone_le (sh_fun f (u n)) (sh_fun f s).
  by apply: (tm_incr_le Hfm); [exact: cone_sup_ball_ub | exact: Hs].
(* [shd (u n)] ≤p [shd s] likewise. *)
have wxch n : precone_le (shd_fun (u n)) (shd_fun s).
  by apply: shd_incr_le; [exact: cone_sup_ball_ub | exact: Hs].
(* [g] chain monotone and bounded by [Mg := ‖g‖ + 1]. *)
have Hg_chain n : sh_fun g (u n) <=p sh_fun g (u n.+1).
  exact: (tm_incr_le Hgm (uch n) (ub1 n.+1)).
have Mg_ge0 : (0 <= sh_norm g + 1)%R.
  by rewrite addr_ge0 // ?sh_norm_ge0 // ler01.
pose Mg : {nonneg R} := NngNum Mg_ge0.
have Mgpos : (0 < Mg%:num)%R.
  by rewrite /= -[X in (X < _)%R]add0r ler_ltD // ?sh_norm_ge0 // ltr01.
have Hg_chubMg n : cone_norm (sh_fun g (u n)) <= Mg%:num.
  by apply: le_trans (sh_norm_ub g _ (ub1 n)) _; rewrite /= lerDl ler01.
exact: (diff_scott_at Hgc (@shd_E) uch ub1 fxle hfuch wxch hfubMf Mfpos
          Hg_chain Hg_chubMg Mgpos).
Qed.

(** Stability of the difference (Def 7.7): total monotonicity, bounded,
    Scott-continuous. *)
Lemma shd_stable : is_stable shd_fun.
Proof.
split; [exact: shd_totmono | exact: shd_bounded | exact: shd_scott].
Qed.

(** *** Measurability of the difference (subtraction on [R])

    For a unit-ball measurable path [γ], [test m s (shd_fun (γ r))]
    equals [test m s (g(γ r)) − test m s (f(γ r))] (by [test_linD] on
    [shd_E]), a difference of the measurable test-paths of [g] and [f]. *)
Lemma shd_pres_path (X : ar_obj Ar) (γ : ar_carrier Ar X -> B) :
  (forall r, cone_norm (γ r) <= 1) ->
  is_measurable_path (Ar:=Ar) (C:=B) γ ->
  is_measurable_path (Ar:=Ar) (C:=C) (fun r => shd_fun (γ r)).
Proof.
move=> Hγ1 Hγ.
have [_ Hfp] := sh_meas_stable f.
have [_ Hgp] := sh_meas_stable g.
have Hfγ := Hfp X γ Hγ1 Hγ.
have Hgγ := Hgp X γ Hγ1 Hγ.
have [_ Hf_meas] := Hfγ.
have [_ Hg_meas] := Hgγ.
split.
  exists (sh_norm g) => r.
  apply: le_trans (sh_norm_ub g _ (Hγ1 r)).
  exact: cone_normp (shd_le_g (γ r)).
move=> Y m mM.
have -> :
  (fun p : (ar_carrier Ar Y * ar_carrier Ar X)%type =>
     test_fun m p.1 (shd_fun (γ p.2))) =
  (fun p : (ar_carrier Ar Y * ar_carrier Ar X)%type =>
     test_fun m p.1 (sh_fun g (γ p.2)) - test_fun m p.1 (sh_fun f (γ p.2))).
  apply: funext => p.
  have := shd_E (γ p.2); move/(congr1 (test_fun m p.1)).
  rewrite test_linD => H.
  by rewrite H addrAC subrr add0r.
by apply: measurable_funB; [exact: Hg_meas | exact: Hf_meas].
Qed.

(** Off the unit ball, [g(γ r)] need not vanish, but the path-version
    above is on-ball only; measurable-stability bundles them. *)
Lemma shd_meas_stable : is_meas_stable shd_fun.
Proof. by split; [exact: shd_stable | exact: shd_pres_path]. Qed.

(** The difference packaged as a [stablehom]. *)
Definition sh_diff : stablehom B C :=
  MkStablehom shd_fun shd_meas_stable shd_offball.

(** Paper Lemma 7.12 backward: [f + (g ⊖ f) = g], i.e. [f ≤p g]. *)
Lemma sh_add_diff : sh_add f sh_diff = g.
Proof. by apply: stablehom_eq => x /=; rewrite /stm_add shd_E. Qed.

(** Hence [f ≤p g] in the stable (precone) order. *)
Lemma sh_le_of_alt : precone_le f g.
Proof. by exists sh_diff; rewrite -sh_add_diff. Qed.

End StablehomDiff.

Arguments sh_le_of_alt {R Ar B C f g} Hpw Halt.

(** ** Lemma 7.12 forward — the stable order implies the alternating
    condition.  Given a stablehom witness [δ] with [g = f + δ], substitute
    [g(a) = f(a) + δ(a)] into both [Σg]-sums ([sumP_add]) and reduce to
    [Σ_{P⁻} δ ≤p Σ_{P⁺} δ] — total monotonicity of [δ] — after rearranging
    the common [Σf]-terms. *)
Section StablehomAltOfLe.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : MCone.type Ar.
Local Open Scope precone_scope.

Lemma sh_alt_of_le (f g : stablehom B C) : precone_le f g -> sh_alt f g.
Proof.
move=> [d Hd] n x v Hxv.
have dE (y : B) : sh_fun g y = sh_fun f y + sh_fun d y.
  by have /(congr1 (fun h => sh_fun h y)) /= := Hd.
set a := fun I : {set 'I_n} => tm_arg x v I.
have splitN : \big[precone_add/precone_zero]_(I in Pneg n) sh_fun g (a I) =
    (\big[precone_add/precone_zero]_(I in Pneg n) sh_fun f (a I))
    + (\big[precone_add/precone_zero]_(I in Pneg n) sh_fun d (a I)).
  by rewrite -sumP_add; apply: eq_bigr => I _; exact: dE.
have splitP : \big[precone_add/precone_zero]_(I in Ppos n) sh_fun g (a I) =
    (\big[precone_add/precone_zero]_(I in Ppos n) sh_fun f (a I))
    + (\big[precone_add/precone_zero]_(I in Ppos n) sh_fun d (a I)).
  by rewrite -sumP_add; apply: eq_bigr => I _; exact: dE.
set Sf_neg := \big[precone_add/precone_zero]_(I in Pneg n) sh_fun f (a I).
set Sf_pos := \big[precone_add/precone_zero]_(I in Ppos n) sh_fun f (a I).
set Sd_neg := \big[precone_add/precone_zero]_(I in Pneg n) sh_fun d (a I).
set Sd_pos := \big[precone_add/precone_zero]_(I in Ppos n) sh_fun d (a I).
rewrite -/a splitN splitP.
(* [d] is totally monotonic: [Sd_neg ≤p Sd_pos]. *)
have [[Hdm _ _] _] := sh_meas_stable d.
have Htm := Hdm n x v Hxv.
rewrite -/a -/Sd_neg -/Sd_pos in Htm.
(* Goal: (Sf_neg + Sd_neg) + Sf_pos ≤p (Sf_pos + Sd_pos) + Sf_neg. *)
apply: (@precone_le_trans _ _ ((Sf_neg + Sf_pos) + Sd_pos)).
  rewrite -[(Sf_neg + Sd_neg) + Sf_pos]precone_addA.
  rewrite [Sd_neg + Sf_pos]precone_addC precone_addA.
  by apply: precone_add_le_l.
rewrite -[(Sf_pos + Sd_pos) + Sf_neg]precone_addA.
rewrite [Sd_pos + Sf_neg]precone_addC precone_addA.
rewrite [Sf_pos + Sf_neg]precone_addC.
exact: precone_le_refl.
Qed.

End StablehomAltOfLe.

Arguments sh_alt_of_le {R Ar B C f g}.

(** ** (Normc) [cone_sup_ball_ub] — every chain element is below [sh_sup]
    — Paper Lemma 7.14

    The witness [δ_n := sh_sup ((u_{n+k} ⊖ uₙ)_k)] is the supremum of the
    difference chain whose terms are the order witnesses [u_{n+k} ⊖ uₙ]
    (themselves [stablehom]s, by chain monotonicity).  This chain is
    [≤p]-increasing (left-cancellation [precone_le_addlI]) and unit-norm
    (each [⊖]-term is [≤p u_{n+k}], so [≤ 1] by (Normp)).  Pointwise on
    [B_B], [uₙ x + δ_n x = supₖ(uₙ x + (u_{n+k} ⊖ uₙ) x) = supₖ u_{n+k} x =
    supₘ uₘ x = sh_sup x] by [sup_ball_addr] and cofinality; off [B_B] both
    sides are [0].  Hence [sh_sup = sh_add uₙ δ_n], i.e. [uₙ ≤p sh_sup]. *)

Section StablehomConeSup.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : MCone.type Ar.
Local Open Scope precone_scope.

Variable u : nat -> stablehom B C.
Hypothesis uch : forall n, precone_le (u n) (u n.+1).
Hypothesis ub1 : forall n, sh_norm (u n) <= 1.

Local Notation S := (sh_sup uch ub1).

(** The difference [u_{n+k} ⊖ uₙ], extracted from chain monotonicity. *)
Definition shu_diff (n k : nat) : stablehom B C :=
  projT1 (cid (sh_chain_mono uch (leq_addr k n))).

Lemma shu_diff_E (n k : nat) : u (n + k)%N = u n + shu_diff n k.
Proof. exact: projT2 (cid (sh_chain_mono uch (leq_addr k n))). Qed.

(** The difference chain is [≤p]-increasing (left-cancellation). *)
Lemma shu_diff_ch (n k : nat) : precone_le (shu_diff n k) (shu_diff n k.+1).
Proof.
apply: (precone_le_addlI (z := u n)).
rewrite -!shu_diff_E addnS; exact: uch.
Qed.

(** Each difference is [≤p u_{n+k}], hence unit-norm. *)
Lemma shu_diff_le (n k : nat) : precone_le (shu_diff n k) (u (n + k)%N).
Proof. by exists (u n); rewrite shu_diff_E precone_addC. Qed.

Lemma shu_diff_ub1 (n k : nat) : sh_norm (shu_diff n k) <= 1.
Proof.
apply: le_trans (ub1 (n + k)%N); apply: sh_normp; exact: shu_diff_le.
Qed.

(** Each chain element is below the supremum. *)
Lemma sh_sup_ball_ub n : precone_le (u n) S.
Proof.
set d := shu_diff n.
pose δ : stablehom B C := sh_sup (@shu_diff_ch n) (@shu_diff_ub1 n).
exists δ; apply: stablehom_eq => x /=.
have [Hx | Hx] := boolP (cone_norm x <= 1); last first.
  rewrite /stm_add (sh_offball (u n) x Hx).
  by rewrite (sh_sup_fun_off _ _ Hx) (sh_sup_fun_off _ _ Hx) precone_add0.
(* On-ball: [sh_sup x = uₙ x + δ x = supₖ (d k x + uₙ x)]. *)
have dch_x m : sh_fun (d m) x <=p sh_fun (d m.+1) x.
  exact: sh_le_pointwise (shu_diff_ch n m) x.
have db1_x m : cnorm (sh_fun (d m) x) <= 1.
  by apply: le_trans (shu_diff_ub1 n m); exact: sh_norm_ub _ _ Hx.
have δxE' : sh_sup_fun (shu_diff_ch n) (shu_diff_ub1 n) x =
    cone_sup_ball (fun m => sh_fun (d m) x) dch_x db1_x.
  by rewrite (sh_sup_fun_unitE (shu_diff_ch n) (shu_diff_ub1 n) Hx dch_x db1_x).
rewrite /stm_add δxE'.
(* pointwise chain/bound for [m ↦ d m x + uₙ x]. *)
have adch m : sh_fun (d m) x + sh_fun (u n) x <=p
              sh_fun (d m.+1) x + sh_fun (u n) x.
  by apply: precone_add_le_r; exact: dch_x.
have adub m : cnorm (sh_fun (d m) x + sh_fun (u n) x) <= 1.
  have -> : sh_fun (d m) x + sh_fun (u n) x = sh_fun (u (n + m)%N) x.
    by rewrite shu_diff_E precone_addC.
  by apply: le_trans (ub1 (n + m)%N); exact: sh_norm_ub _ _ Hx.
rewrite precone_addC -(sup_ball_addr dch_x db1_x adch adub).
(* Goal: sh_sup_fun x = cone_sup_ball (m ↦ d m x + uₙ x). *)
apply: precone_le_anti.
- apply: (sh_sup_fun_lubP uch ub1 Hx) => m.
  have [le|lt] := leqP n m.
    have -> : sh_fun (u m) x = sh_fun (d (m - n)%N) x + sh_fun (u n) x.
      have Em : u m = u n + shu_diff n (m - n)%N by rewrite -shu_diff_E subnKC.
      rewrite (_ : sh_fun (u m) x = sh_fun (u n + shu_diff n (m - n)%N) x);
        last by rewrite Em.
      by rewrite sh_addE precone_addC.
    exact: (cone_sup_ball_ub (fun m => sh_fun (d m) x + sh_fun (u n) x)).
  apply: (@precone_le_trans _ _ (sh_fun (u n) x)).
    by apply: sh_le_pointwise; apply: sh_chain_mono => //; exact: ltnW.
  apply: (@precone_le_trans _ _ (sh_fun (d 0%N) x + sh_fun (u n) x)).
    by exists (sh_fun (d 0%N) x); rewrite precone_addC.
  exact: (cone_sup_ball_ub
            (fun m => sh_fun (d m) x + sh_fun (u n) x) adch adub 0%N).
- apply: cone_sup_ball_lub => m.
  have -> : sh_fun (d m) x + sh_fun (u n) x = sh_fun (u (n + m)%N) x.
    by rewrite precone_addC shu_diff_E.
  exact: (sh_sup_fun_ubP uch ub1 Hx (n + m)%N).
Qed.

(** ** (Normc) [cone_sup_ball_lub] — [sh_sup] is the least upper bound
    — Paper Lemma 7.14 ("it is defined as a pointwise lub")

    Given a stable upper bound [y] of the chain, [sh_sup ≤p y] in the
    stable order.  We construct the difference [y ⊖ sh_sup] via the
    difference-is-stable master [sh_diff] (Lemma 7.12 backward): its
    pointwise hypothesis is the [C]-level lub [sh_sup x ≤p y x], and its
    alternating hypothesis [sh_alt sh_sup y] is the supremum-passage of
    the [sh_alt uₘ y] (each holds since [uₘ ≤p y], via the forward
    [sh_alt_of_le]).  The passage commutes the finite cone-sums
    [Σ_{P±} sh_sup(a)] with the chain supremum using the [SumSup] engine
    ([sh_sup_fun_unitE] / [sum_cone_sup_ub] / [addl_sum_cone_sup_lub]),
    exactly as total monotonicity of [sh_sup] does. *)

(** The alternating condition for [(sh_sup, y)], by supremum-passage. *)
Lemma sh_sup_alt_l (y : stablehom B C) :
  (forall m, precone_le (u m) y) -> sh_alt S y.
Proof.
move=> Hy k x v Hxv.
(* All [tm_arg]s are in [B_B] (≤p the full-set argument). *)
have argle (I : {set 'I_k}) :
    tm_arg x v I <=p x + \big[precone_add/precone_zero]_(i : 'I_k) v i.
  rewrite /tm_arg; apply: precone_add_le_l.
  rewrite [X in _ <=p X](bigID (mem I)) /= (eq_bigl (mem I)) //.
  by exists (\big[precone_add/precone_zero]_(i | i \notin I) v i).
have argub (I : {set 'I_k}) : cone_norm (tm_arg x v I) <= 1.
  by apply: le_trans Hxv; apply: cone_normp; exact: argle.
(* The doubly-indexed family [c I m := uₘ (a I)]. *)
pose c (I : {set 'I_k}) (m : nat) : C := sh_fun (u m) (tm_arg x v I).
have cch I m : c I m <=p c I m.+1 by exact: sh_le_pointwise (uch m) _.
have cub I m : cnorm (c I m) <= 1.
  by apply: le_trans (ub1 m); exact: sh_norm_ub _ _ (argub I).
(* [sh_sup(a I) = cone_sup_ball (c I)]. *)
have supE I : sh_fun S (tm_arg x v I) = cone_sup_ball (c I) (cch I) (cub I).
  rewrite /S /=; apply: precone_le_anti.
  - apply: (sh_sup_fun_lubP uch ub1 (argub I)) => m.
    by rewrite /c; exact: (cone_sup_ball_ub (c I) (cch I) (cub I) m).
  - apply: cone_sup_ball_lub => m.
    by rewrite /c; exact: (sh_sup_fun_ubP uch ub1 (argub I) m).
rewrite (eq_bigr _ (fun I _ => supE I)).
(* Push [Σ_{P⁻} y] into the [P⁺]-sup; bound each diagonal term. *)
apply: (addl_sum_cone_sup_lub cch cub (Ppos k)) => m.
(* [sumsup_chain c (Ppos k) m = Σ_{P⁺} uₘ(a)]. *)
apply: (@precone_le_trans _ _
  (\big[precone_add/precone_zero]_(I in Ppos k) sh_fun y (tm_arg x v I)
   + \big[precone_add/precone_zero]_(I in Pneg k) c^~ m I)).
  (* [sh_alt uₘ y] at this test data. *)
  have HA := sh_alt_of_le (Hy m) k x v Hxv.
  rewrite /sumsup_chain.
  by under eq_bigr => I _ do rewrite /c; exact: HA.
(* [Σ_{P⁻} uₘ(a) ≤p Σ_{P⁻} cone_sup_ball(c)]. *)
apply: precone_add_le_l.
rewrite (eq_bigr _ (fun I _ => supE I)).
exact: (sum_cone_sup_ub cch cub (Pneg k) m).
Qed.

(** [sh_sup] is the least upper bound: [sh_sup ≤p y]. *)
Lemma sh_sup_ball_lub (y : stablehom B C) :
  (forall m, precone_le (u m) y) -> precone_le S y.
Proof.
move=> Hy.
(* Pointwise [C]-level lub: [sh_sup x ≤p y x] on [B_B]. *)
have Hpw (z : B) : cone_norm z <= 1 ->
    precone_le (sh_fun S z) (sh_fun y z).
  move=> Hz; apply: (sh_sup_fun_lubP uch ub1 Hz) => m.
  exact: sh_le_pointwise (Hy m) z.
(* Build the difference [y ⊖ sh_sup] via the master [sh_diff]. *)
exact: (sh_le_of_alt Hpw (sh_sup_alt_l Hy)).
Qed.

(** (Normc) norm: the supremum has operator norm [≤ 1] (pointwise [≤ 1]
    on [B_B] by [sh_sup_fun_norm], lifted by [sh_norm_lub]). *)
Lemma sh_sup_ball_norm : sh_norm S <= 1.
Proof. by apply: sh_norm_lub => z _; exact: sh_sup_fun_norm. Qed.

End StablehomConeSup.

Arguments sh_sup_ball_ub {R Ar B C} u uch ub1 n.
Arguments sh_sup_ball_lub {R Ar B C} u uch ub1 y.
Arguments sh_sup_ball_norm {R Ar B C} u uch ub1.

(** ** [isCone] HB instance on [stablehom B C] — Paper §7.2 / Lemma 7.14

    With (Normh)/(Normt)/(Normp)/(Normz) already proved and (Normc)
    discharged via [sh_sup] + [sh_sup_ball_ub] / [sh_sup_ball_lub] /
    [sh_sup_ball_norm], we register [stablehom B C] as a [coneType R].
    The stable function cone [B ⇒ₛ C] is now a cone. *)

HB.instance Definition _ (R : realType) (Ar : MeasSubcat R)
    (B C : MCone.type Ar) :=
  @isCone.Build R (stablehom B C)
    (@sh_norm R Ar B C)
    (@sh_normh R Ar B C) (@sh_normz R Ar B C)
    (@sh_normt R Ar B C) (@sh_normp R Ar B C)
    (@sh_sup R Ar B C) (@sh_sup_ball_ub R Ar B C)
    (@sh_sup_ball_lub R Ar B C) (@sh_sup_ball_norm R Ar B C).

(** Sanity check: [stablehom B C] is a [coneType R] — Paper §7.2. *)
Section StablehomConeCheck.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : MCone.type Ar.

Check (stablehom B C : coneType R).

End StablehomConeCheck.

(** ** The [γ ▷ m] test family on [stablehom] — Paper §7.2 (txt 3365)

    Mirroring [linhom]'s [linhom_test], a test on [B ⇒ₛ C] is built from
    a unit-ball path [γ ∈ Path(Y, B)] and a [C]-test [m ∈ M^C_Y] by

      [(γ ▷ m)(s, f) := m s (sh_fun f (γ s))].

    The cone operations on [stablehom] are *pointwise* and [m] is linear
    in its second argument, so [(γ ▷ m)] is LINEAR in [f] — even though
    [f] itself is a *nonlinear* stable map.  The eight test fields reduce
    to those of [m]; only test-measurability ((Msmeas)) and ω-continuity
    use the [stablehom]-specific machinery: path-preservation of
    [is_meas_stable f] (so [f ∘ γ] is a measurable path of [C]) together
    with [measurable_test_path_section], and [sh_sup_fun_unitE] +
    [test_of_sup]. *)

Section StablehomTest.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : MCone.type Ar.
Variables (Y : ar_obj Ar) (γ : path_car Ar Y B).
Hypothesis γub : cone_norm γ <= 1.
Variable m : test_of Ar Y C.
Hypothesis mM : mcone_M Y m.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Pointwise unit-ball membership of [γ], from [γub] via
    [path_norm_ub]. *)
Lemma sh_test_γ_unit (s : ar_carrier Ar Y) : cone_norm (path_fun γ s) <= 1.
Proof. by apply: le_trans (path_norm_ub _ _) _; exact: γub. Qed.

(** Paper §7.2: the test body [(γ ▷ m)(s, f) := m s (f (γ s))]. *)
Definition sh_test_fun (s : ar_carrier Ar Y) (f : stablehom B C) : R :=
  test_fun m s (sh_fun f (path_fun γ s)).

(** (Msmeas) — for a unit-ball [f], the section [r ↦ m r (f (γ r))] is
    measurable.  [f ∘ γ] is a measurable path of [C] by the
    path-preservation field of [is_meas_stable f] (the path [γ] stays in
    the unit ball pointwise, [sh_test_γ_unit]); the section
    measurability is [measurable_test_path_section]. *)
Lemma sh_test_meas (f : stablehom B C) :
  cone_norm f <= 1 ->
  measurable_fun [set: ar_carrier Ar Y] (fun s => sh_test_fun s f).
Proof.
move=> _.
have [_ Hpres] := sh_meas_stable f.
have Hfγ : is_measurable_path (fun r => sh_fun f (path_fun γ r)).
  apply: Hpres; first by move=> r; exact: sh_test_γ_unit.
  exact: path_is_path γ.
rewrite /sh_test_fun.
have [_ Hg] := Hfγ.
have Hbase : measurable_fun
  [set: (ar_carrier Ar Y * ar_carrier Ar Y)%type]
  (fun p => test_fun m p.1 (sh_fun f (path_fun γ p.2))).
  exact: (Hg Y m mM).
have Hpair : measurable_fun [set: ar_carrier Ar Y]
  (fun s => (s, s) : ar_carrier Ar Y * ar_carrier Ar Y).
  by apply: measurable_fun_pair; exact: measurable_id.
pose F (p : ar_carrier Ar Y * ar_carrier Ar Y) : R :=
  test_fun m p.1 (sh_fun f (path_fun γ p.2)).
have -> : (fun s => test_fun m s (sh_fun f (path_fun γ s))) =
          F \o (fun s => (s, s)).
  by apply: funext.
exact: measurableT_comp.
Qed.

Lemma sh_test_ge0 (s : ar_carrier Ar Y) (f : stablehom B C) :
  0 <= sh_test_fun s f.
Proof. exact: test_ge0. Qed.

(** (Msmeas) — [(γ ▷ m)(s, f) ≤ 1] when [‖f‖ ≤ 1]: [‖f (γ s)‖ ≤ ‖f‖ ≤ 1]
    by [sh_norm_ub] (using [‖γ s‖ ≤ 1]). *)
Lemma sh_test_le1 (s : ar_carrier Ar Y) (f : stablehom B C) :
  cone_norm f <= 1 -> sh_test_fun s f <= 1.
Proof.
move=> Hf; apply: test_le1.
apply: le_trans (sh_norm_ub f (path_fun γ s) (sh_test_γ_unit s)) _.
exact: Hf.
Qed.

(** Linearity in [f] — the cone operations on [stablehom] are pointwise
    and [m] is linear in its second argument. *)
Lemma sh_test_lin0 (s : ar_carrier Ar Y) :
  sh_test_fun s (sh_zero B C) = 0.
Proof. by rewrite /sh_test_fun /= test_lin0. Qed.

Lemma sh_test_linD (s : ar_carrier Ar Y) (f1 f2 : stablehom B C) :
  sh_test_fun s (sh_add f1 f2) = sh_test_fun s f1 + sh_test_fun s f2.
Proof. by rewrite /sh_test_fun /= test_linD. Qed.

Lemma sh_test_linZ
    (s : ar_carrier Ar Y) (r : {nonneg R}) (f : stablehom B C) :
  sh_test_fun s (sh_scale r f) = r%:num * sh_test_fun s f.
Proof. by rewrite /sh_test_fun /= test_linZ. Qed.

(** ω-continuity in [f]: the value at the cone-supremum of a unit-ball
    chain is the supremum of the test-values.  On [B_B], [sh_sup]
    computes pointwise ([sh_sup_fun_unitE]); then [test_of_sup] of [m]
    gives the supremum identity. *)
Lemma sh_test_cont
    (s : ar_carrier Ar Y)
    (u : nat -> stablehom B C)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, cone_norm (u n) <= 1)
    (N : R) :
  (forall n, sh_test_fun s (u n) <= N) ->
  sh_test_fun s (cone_sup_ball u uch ub1) <= N.
Proof.
move=> HN.
have Hγ : cone_norm (path_fun γ s) <= 1 by exact: sh_test_γ_unit.
have ch : forall n, sh_fun (u n) (path_fun γ s) <=p
                    sh_fun (u n.+1) (path_fun γ s).
  by move=> n; exact: sh_le_pointwise (uch n) (path_fun γ s).
have b1 : forall n, cnorm (sh_fun (u n) (path_fun γ s)) <= 1.
  move=> n.
  apply: le_trans (sh_norm_ub (u n) (path_fun γ s) Hγ) _; exact: ub1.
rewrite /sh_test_fun /=.
rewrite (sh_sup_fun_unitE uch ub1 Hγ ch b1).
rewrite (test_of_sup m s ch b1).
apply: ge_sup.
  by exists (test_fun m s (sh_fun (u 0%N) (path_fun γ s))), 0%N.
by move=> _ [n _ <-]; exact: HN.
Qed.

(** Pointwise upper bound [(γ ▷ m)(s, f) ≤ ‖f‖]. *)
Lemma sh_test_norm_le (s : ar_carrier Ar Y) (f : stablehom B C) :
  sh_test_fun s f <= cone_norm f.
Proof.
apply: le_trans (test_norm_le _ _ _) _.
have [Hx | Hx] := boolP (cone_norm (path_fun γ s) <= 1); last first.
  rewrite (sh_offball f _ Hx) cone_norm0; exact: sh_norm_ge0.
exact: sh_norm_ub f (path_fun γ s) Hx.
Qed.

(** The packaged test, abbreviated [γ ▷ m]. *)
Definition sh_test : test_of Ar Y (stablehom B C) :=
  MkTestOf sh_test_meas sh_test_ge0 sh_test_le1
           sh_test_lin0 sh_test_linD sh_test_linZ
           sh_test_cont sh_test_norm_le.

End StablehomTest.

Arguments sh_test {R Ar B C Y}.

(** ** The measurability structure on [stablehom] — Paper §7.2

    [M^{B⇒ₛC}_Y := { γ ▷ m | γ ∈ Path(Y, B), ‖γ‖ ≤ 1, m ∈ M^C_Y }]. *)

Section StablehomMCone.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : MCone.type Ar.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Definition sh_mcone_M (Y : ar_obj Ar) :
    set (test_of Ar Y (stablehom B C)) :=
  [set p | exists (γ : path_car Ar Y B) (γub : cone_norm γ <= 1)
                  (m : test_of Ar Y C) (mM : mcone_M Y m),
    p = sh_test γ γub m mM].

(** (Mscomp) — reindexing by [ψ : ar_hom Y' Y]: the reindexed test is
    [(γ ∘ ψ) ▷ (m ∘ (ψ × C))]. *)
Lemma sh_mcone_M_comp
  (Y' Y : ar_obj Ar) (ψ : ar_hom Ar Y' Y)
  (p : test_of Ar Y (stablehom B C)) :
  sh_mcone_M p ->
  sh_mcone_M (test_reindex ψ p).
Proof.
case=> γ [γub [m [mM ->]]].
have Hγψ : is_measurable_path (path_fun γ \o ψ).
  exact: reindex_path_measurable ψ (path_is_path γ).
pose γ' : path_car Ar Y' B := MkPath Hγψ.
have γ'ub : cone_norm γ' <= 1.
  apply: ge_sup; first exact: path_normset_nonempty.
  move=> _ [r ->].
  apply: le_trans (path_norm_ub γ (ψ r)) _; exact: γub.
have mM' : mcone_M Y' (test_reindex ψ m) by exact: mcone_M_comp.
exists γ', γ'ub, (test_reindex ψ m), mM'.
apply: test_eq => s f /=.
by rewrite /sh_test_fun /test_reindex_fun /=.
Qed.

(** Helper: constant path [γ_x : ar_carrier Z -> B] at arbitrary arity,
    measurable, with [‖γ_x‖ = ‖x‖]. *)
Section ConstPathAtArity.
Variables (Z : ar_obj Ar) (x : B).

Let const_x_fun : ar_carrier Ar Z -> B := fun _ => x.

Lemma sh_const_x_is_path :
  is_measurable_path (Ar:=Ar) (C:=B) (X:=Z) const_x_fun.
Proof. exact: const_path_measurable. Qed.

Definition sh_const_x_path_arity : path_car Ar Z B :=
  MkPath sh_const_x_is_path.

Lemma sh_const_x_path_arity_normE :
  path_norm sh_const_x_path_arity = cone_norm x.
Proof.
apply: le_anti; apply/andP; split.
- apply: ge_sup; first exact: path_normset_nonempty.
  by move=> _ [r ->] /=; exact: lexx.
- have Hin : path_normset sh_const_x_path_arity (cone_norm x).
    by exists (ar_point Ar Z).
  by move/ubP : (sup_upper_bound (path_normset_has_sup sh_const_x_path_arity));
    apply.
Qed.

End ConstPathAtArity.

(** Specialization at [Z = ar_zero], used in (Mssep)/(Msnorm). *)
Definition sh_const_x_path (x : B) : path_car Ar (ar_zero Ar) B :=
  sh_const_x_path_arity (ar_zero Ar) x.

Lemma sh_const_x_path_normE (x : B) :
  path_norm (sh_const_x_path x) = cone_norm x.
Proof. exact: sh_const_x_path_arity_normE. Qed.

(** (Mssep) — arity-0 tests separate stable maps.  As in [linhom], we
    rescale [x ∈ B] to the unit ball, evaluate the constant-path test,
    and use linearity of [m] (not of [f]) to scale back. *)
Lemma sh_mcone_M_sep (f1 f2 : stablehom B C) :
  (forall p : test_of Ar (ar_zero Ar) (stablehom B C),
    sh_mcone_M (Y:=ar_zero Ar) p ->
    test_fun p (ar_zero_pt Ar) f1 = test_fun p (ar_zero_pt Ar) f2) ->
  f1 = f2.
Proof.
move=> Hsep; apply: stablehom_eq => x.
(* On-ball [x] only matters: off-ball both maps are 0. *)
have [Hx1 | Hx1] := boolP (cone_norm x <= 1); last first.
  by rewrite (sh_offball f1 _ Hx1) (sh_offball f2 _ Hx1).
apply: mcone_M_sep => m mM.
have Hγx_unit : cone_norm (sh_const_x_path x) <= 1.
  by rewrite /cone_norm /= sh_const_x_path_normE.
have HinM : sh_mcone_M (Y:=ar_zero Ar)
  (sh_test (sh_const_x_path x) Hγx_unit m mM).
  by exists (sh_const_x_path x), Hγx_unit, m, mM.
have Heq := Hsep _ HinM.
by rewrite /sh_test /sh_test_fun /= in Heq.
Qed.

(** (Msnorm) — given [f ≠ 0] and [ε > 0], a witness test [p = γ_x ▷ m]
    at arity 0 with [‖f‖ ≤ p(f) + ε].  We pick an adherent [x ∈ B_B] with
    [‖f‖ ≤ ‖f x‖ + ε/2], then apply (Msnorm) of [C] to [f x] (when
    [f x ≠ 0]) or note [‖f‖ ≤ ε/2] (when [f x = 0]).  Unlike [linhom] no
    rescaling-by-linearity of [f] is needed: [x] is already on [B_B]. *)
Lemma sh_mcone_M_norm (f : stablehom B C) (eps : R) :
  f <> sh_zero B C -> 0 < eps ->
  exists p : test_of Ar (ar_zero Ar) (stablehom B C),
    sh_mcone_M (Y:=ar_zero Ar) p /\
    cone_norm f <= test_fun p (ar_zero_pt Ar) f + eps.
Proof.
move=> fne eps_pos.
have eps2_pos : 0 < eps / 2 by rewrite divr_gt0.
have norm_pos : 0 < cone_norm f.
  rewrite lt_def cone_norm_ge0 andbT.
  by apply/eqP => Hn0; apply: fne; exact: sh_normz Hn0.
have has_sup_f : has_sup (sh_normset f).
  exact: sh_normset_has_sup.
have [v Hv1 Hv2] := sup_adherent eps2_pos has_sup_f.
case: Hv1 => x0 [Hx0_le1 Hx0_eq].
have HnormR : cone_norm f <= cone_norm (sh_fun f x0) + eps / 2.
  rewrite -lerBlDr ltW //.
  by rewrite -/(sh_norm f) -Hx0_eq.
have Hγx0_unit : cone_norm (sh_const_x_path x0) <= 1.
  by rewrite /cone_norm /= sh_const_x_path_normE.
have [eqz | nez] : sh_fun f x0 = precone_zero \/
                   sh_fun f x0 <> precone_zero.
  by case: (pselect (sh_fun f x0 = precone_zero)); tauto.
- (* [f x0 = 0]: then ‖f‖ ≤ ε/2 ≤ ε; any family test witnesses. *)
  have norm_le_e2 : cone_norm f <= eps / 2.
    apply: le_trans HnormR _.
    by rewrite eqz cone_norm0 add0r.
  (* (Msnorm) of [C] needs a nonzero point; if all [f x] are 0 then
     [f = sh_zero], contradicting [fne].  But for the witness we only
     need *some* arity-0 family test; take [γ_{x0} ▷ m0] for any
     [m0 ∈ M^C_0].  Since [‖f‖ ≤ ε/2 ≤ ε ≤ p(f) + ε], it works. *)
  have [x1 nz1] : exists x1, sh_fun f x1 <> precone_zero.
    apply: contrapT => Hne; apply: fne.
    apply: stablehom_eq => x.
    apply: contrapT => Hr.
    by apply: Hne; exists x.
  have [m0 [mM0 _]] :=
    @mcone_M_norm R Ar C (sh_fun f x1) eps nz1 eps_pos.
  exists (sh_test (sh_const_x_path x0) Hγx0_unit m0 mM0); split.
    by exists (sh_const_x_path x0), Hγx0_unit, m0, mM0.
  rewrite /sh_test /= /sh_test_fun /=.
  apply: le_trans norm_le_e2 _.
  have e2_le_e : eps / 2 <= eps.
    by rewrite ler_pdivrMr // ler_peMr // ?ler1n // ltW.
  apply: le_trans e2_le_e _.
  rewrite -[X in X <= _]add0r lerD //.
  exact: test_ge0.
- (* [f x0 ≠ 0]: (Msnorm) of [C] at [f x0] with [ε/2]. *)
  have [m [mM Hm]] :=
    @mcone_M_norm R Ar C (sh_fun f x0) (eps / 2) nez eps2_pos.
  exists (sh_test (sh_const_x_path x0) Hγx0_unit m mM); split.
    by exists (sh_const_x_path x0), Hγx0_unit, m, mM.
  rewrite /sh_test /= /sh_test_fun /=.
  apply: le_trans HnormR _.
  apply: le_trans (lerD Hm (lexx (eps / 2))) _.
  rewrite -addrA lerD2l.
  have ->: (eps / 2 + eps / 2 = eps)%R.
    have two_ne0 : (2 : R) != 0 by rewrite pnatr_eq0.
    have step : (eps / 2 + eps / 2) * 2 = eps * 2.
      rewrite mulrDl !mulfVK //.
      by have ->: (2 = 1 + 1 :> R)%R by [];
         rewrite mulrDr mulr1.
    exact: (mulIf two_ne0 step).
  exact: lexx.
Qed.

End StablehomMCone.

(** ** [isMCone] HB instance for [stablehom B C] — Paper §7.2 *)

HB.instance Definition _ (R : realType) (Ar : MeasSubcat R)
    (B C : MCone.type Ar) :=
  @isMCone.Build R Ar (stablehom B C)
    (@sh_mcone_M R Ar B C)
    (@sh_mcone_M_comp R Ar B C)
    (@sh_mcone_M_sep R Ar B C)
    (@sh_mcone_M_norm R Ar B C).

(** ** Sanity check: [stablehom B C] is an [mconeType Ar] *)
Section StablehomMConeCheck.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : MCone.type Ar.

Check (stablehom B C : mconeType Ar).

End StablehomMConeCheck.

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

    - **Difference-is-stable — Lemma 7.12 backward — PROVED.**  For
      [f, g] with [f ≤ g] in the *stable* order (pointwise comparison
      [Hpw] = the [n = 0] case, plus the alternating condition
      [sh_alt f g]), the difference [h := g ⊖ f] ([shd_fun], the
      cone-cancellation witness extracted by [cid]) is a genuine
      [stablehom] with [sh_add f h = g] ([sh_diff] / [sh_add_diff] /
      [sh_le_of_alt]):
        * total monotonicity ([shd_totmono]) — substitute [g(a)=f(a)+h(a)]
          into [sh_alt], split the cone-sums ([sumP_add]) and cancel the
          common [Σf]-terms in the precone order ([precone_le_addlI]),
          leaving [Σ_{P⁻}h ≤p Σ_{P⁺}h];
        * ω-continuity ([shd_scott]) — the radius-aware Lemma 2.10
          [diff_scott_at] ([f] increasing along the chain, [g]
          Scott-continuous via its [is_scott_continuous_unit] field,
          recombined with [addl_scott_continuous]);
        * measurability ([shd_pres_path]) — [test m s (h(γ r))] is the
          difference of the measurable test-paths of [g], [f]
          ([test_linD] on [shd_E], then [measurable_funB]).
      The forward direction ([sh_alt_of_le]) shows [precone_le f g ⇒
      sh_alt f g].
    - **(Normc) [cone_sup_ball] order facts — PROVED.**
        * [sh_sup_ball_ub] — every chain element is below [sh_sup]: the
          witness [sh_sup ⊖ uₙ] is the [sh_sup] of the difference chain
          [(u_{n+k} ⊖ uₙ)_k] (order witnesses, [stablehom]s by chain
          monotonicity + [precone_le_addlI]), with the on-ball cofinality
          identity discharged by [sup_ball_addr].
        * [sh_sup_ball_lub] — [sh_sup] is the least upper bound: the
          difference [y ⊖ sh_sup] is built by the [sh_diff] master, whose
          alternating hypothesis [sh_alt sh_sup y] is the supremum-passage
          of the [sh_alt uₘ y] (forward direction + the [SumSup]
          finite-sum/sup commutation [addl_sum_cone_sup_lub]).
        * [sh_sup_ball_norm] — operator norm [≤ 1].
    - **[isCone] HB instance — REGISTERED.**  [stablehom B C : coneType
      R]: the stable function cone [B ⇒ₛ C] is a cone (Paper §7.2 /
      Lemmas 7.11, 7.12, 7.14).

    - **[isMCone] HB instance — REGISTERED.**  [stablehom B C : mconeType
      Ar] (Paper §7.2, txt 3365: the measurability structure "as in
      [C ⊸ D]").  The test family is

        [M^{B⇒ₛC}_Y := { γ ▷ m | γ ∈ Path(Y, B), ‖γ‖ ≤ 1, m ∈ M^C_Y }]

      with body [(γ ▷ m)(s, f) := m s (sh_fun f (γ s))] ([sh_test_fun],
      packaged as [sh_test]).  Although a [stablehom] [f] is a *nonlinear*
      stable map, [(γ ▷ m)] is *linear in [f]* because the cone
      operations on [stablehom] are pointwise and [m] is linear in its
      second argument — so (test_lin0)/(test_linD)/(test_linZ)
      ([sh_test_lin0]/[sh_test_linD]/[sh_test_linZ]) reduce directly to
      those of [m].  The non-trivial test fields:
        * test-measurability ((Msmeas), [sh_test_meas]) — the
          path-preservation field of [is_meas_stable f] makes [f ∘ γ] a
          measurable path of [C] (the path [γ] stays in [B_B] pointwise,
          [sh_test_γ_unit], from [‖γ‖ ≤ 1] via [path_norm_ub]); the
          diagonal joint measurability is then [is_measurable_path]'s
          second component composed with [s ↦ (s, s)].
        * ω-continuity ((Mscont), [sh_test_cont]) — on [B_B] the cone-sup
          [sh_sup] computes pointwise ([sh_sup_fun_unitE]), then
          [test_of_sup] of [m] (from [test_pullback.v]) gives the sup
          identity.
      The (Mscomp)/(Mssep)/(Msnorm) closure ([sh_mcone_M_comp]/
      [sh_mcone_M_sep]/[sh_mcone_M_norm]) mirrors [linhom]'s
      [linhom_mcone_M_*], using the constant-path helper
      [sh_const_x_path] at arity 0; (Mssep)/(Msnorm) reduce to
      [mcone_M_sep]/[mcone_M_norm] of [C].  Unlike [linhom], (Mssep)
      needs no rescaling-by-linearity of [f] (off-ball maps are [0] via
      [sh_offball], on-ball [x] is fed directly through the constant
      path).  Reuses [mcone.v]'s [test_of]/[test_reindex]/[mcone_M_*],
      [path.v]'s [path_car]/[path_norm_ub]/[const_path_measurable], and
      [icone_integral.v]'s [measurable_test_path_section] +
      [test_pullback.v]'s [test_of_sup].

    Deferred — [isICone] (integrability, txt 3372/3373).  The pointwise
    Pettis integral [f(x) := icone_integral (r ↦ sh_fun (η r) x) µ]
    (0-extended off [B_B]) must be shown a [stablehom], i.e. totally
    monotonic, bounded, [is_scott_continuous_unit] and path-preserving.
    Boundedness ([path_integral_norm_le]) and total monotonicity (a
    finite-cone-sum / integral commutation built from [big_ind2] +
    [path_integral_eq_addB], closed by [icone_integral_chain_le]) are
    in reach with the imported [icone_integral.v] machinery.  The
    *blocker* is the [is_scott_continuous_unit] field: it demands the
    *radius-aware* identity [f (cone_sup_ball u) = cone_sup_at (f ∘ u)
    Mf …] at a general image radius [Mf] (the integral of unit-ball
    inputs has image norm up to [‖η‖·‖µ‖ > 1]).  [icone_integral.v]'s
    [integral_omega_cont_path] proves only the *unit-ball-image*
    [cone_sup_ball] version (it assumes [β_bound : ‖β n r‖ ≤ 1] and
    [µ_norm ≤ 1]); a [cone_sup_at] general-radius port — a fresh
    monotone-convergence lemma — would be required, plus the
    joint-measurability (via [test_pullback]/Fubini) of the bivariate
    integrand for the path-preservation field.  As these are each new
    sub-developments and the brief forbids any holes, [isICone] is left
    for a follow-up; everything below is hole-free and depends only on
    the ambient classical axioms. *)
