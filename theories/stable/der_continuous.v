(**md**************************************************************************)
(* # The dereliction functor [Der] preserves all limits — Paper Theorem 7.34  *)
(*   ([th:derfuns-preserves-limits])                                          *)
(*                                                                            *)
(*   The dereliction inclusion [Der = ders : ICones → SCones] preserves all   *)
(*   limits.  A category with all small products and equalisers has all       *)
(*   limits, so — exactly as in the paper — this reduces to two facts:        *)
(*                                                                            *)
(*   - PRODUCTS.  Products are defined in the *same* way in both categories   *)
(*     ([icones_prod]), so [Der] preserves them on the nose: the SCones       *)
(*     product structure ([scones_proj]/[scones_tuple], [scones_cat.v]) is    *)
(*     built on the very same [icones_prod] object, and [scones_proj i =      *)
(*     ders (icones_proj i)] ([der_preserves_prod_proj]); the universal       *)
(*     property is [scones_tuple_proj]/[scones_tuple_unique] of               *)
(*     [scones_cat.v].                                                         *)
(*                                                                            *)
(*   - EQUALISERS ([der_eq_med]/[_factor]/[_unique]).  For [f, g : D1 → D2]   *)
(*     with equaliser [(E, e)] in [ICones] (the [icones_eq]/[icones_eq_incl]  *)
(*     of §4), the pair [(Der E, Der e)] is the equaliser of [Der f], [Der g] *)
(*     in [SCones].  Given [h : SCones(H, D1)] with                           *)
(*     [Der f ∘ h = Der g ∘ h], the per-point equation [f (h x) = g (h x)]   *)
(*     (on the unit ball — the paper's "[h] ranges in [E]") lets us           *)
(*     co-restrict [h] to a [SCones(H, E)]-valued stable map [h0], the unique *)
(*     mediator since [Der e = cones_eq_val] (clamped) is faithful.  Because  *)
(*     [Der] is the identity on underlying functions and the cone order /     *)
(*     norm / measurability of [E] are the restriction of those of [D1] to    *)
(*     [M E ⊆ M D1], the co-restriction is literally [h] viewed as landing in *)
(*     [E]; its stability reduces clause-by-clause to that of [h] through the *)
(*     faithful inclusion [cones_eq_val] — far simpler than the internal-hom  *)
(*     co-restriction of [limpl_continuous.v] (Thm 5.9).                       *)
(*                                                                            *)
(*   This file is pure [ICones]/[SCones] limit theory, axiom-free               *)
(*   relative to the classical base of mathcomp-analysis.  Theorem 7.34       *)
(*   is the INPUT consumed by the M-SAFT machinery of                          *)
(*   [Icones.homs.representable] to build the left adjoint [E] of [Der]     *)
(*   (the exponential, PLAN §13.4); it must not itself consume the            *)
(*   resulting exponential.                                                   *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import measurable_structure measurable_function.

Require Import Icones.prelude.nonneg_extra.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.omega_general.
Require Import Icones.cones.cone_cat.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.path.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_cat.
Require Import Icones.stable.totmono.
Require Import Icones.stable.findiff.
Require Import Icones.stable.compose.
Require Import Icones.stable.scones_cat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** Products — Paper Theorem 7.34, products case

    Products are defined in the same way in both categories: the SCones
    product of a family [(D_i)_{i ∈ I}] is the very same [icones_prod D]
    object, with projection [scones_proj i = ders (icones_proj i)]
    ([scones_cat.v]) and tupling [scones_tuple] with the universal
    property [scones_tuple_proj] / [scones_tuple_unique].  [Der]
    therefore preserves the product on the nose. *)

Section DerProducts.
Variable R : realType.
Variable Ar : MeasSubcat R.
Variable I : Type.
Variable D : I -> ICone.type Ar.

(** [Der] sends the [i]-th [ICones] projection to the [i]-th [SCones]
    projection (definitional): [Der π_i = SCones-π_i]. *)
Lemma der_preserves_prod_proj (i : I) :
  ders (icones_proj i) = scones_proj D i.
Proof. by []. Qed.

End DerProducts.

(** ** Equalisers — Paper Theorem 7.34, equalisers case

    Fix [f, g : D1 → D2] in [ICones] with equaliser [(E, e)] (where
    [E := icones_eq f g] and [e := icones_eq_incl f g], Paper §4 Thm
    4.16).  We show [(Der E, Der e)] is the equaliser of [Der f], [Der g]
    in [SCones]. *)

Section DerEqualiser.
Variables (R : realType) (Ar : MeasSubcat R).
Variables D1 D2 : ICone.type Ar.
Variables f g : icones_hom Ar D1 D2.

Local Notation E := (icones_eq f g).
Local Notation e := (icones_eq_incl f g).
Local Notation Lfun k := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones k))).

(** Paper §4 (factorisation, transported through [Der]): [Der f ∘ Der e
    = Der g ∘ Der e].  By functoriality of [Der] ([ders_comp]) applied to
    [f ∘ e = g ∘ e] ([icones_eq_incl_equ]). *)
Lemma der_eq_equ :
  scones_comp (ders f) (ders e) = scones_comp (ders g) (ders e).
Proof. by rewrite -!ders_comp icones_eq_incl_equ. Qed.

(** *** The equaliser inclusion [cones_eq_val] is ω-continuous / scott

    The underlying function of [e] is [cones_eq_val]; as it is the linear
    function of an [icones_hom] it is ω-continuous, hence
    [is_scott_continuous] ([linear_scott_of_omega]).  We need this to
    commute the co-restriction's value with [cone_sup_at]. *)

Lemma der_incl_omega :
  is_omega_continuous (fun x : E => cones_eq_val x).
Proof.
(* The equaliser sup is computed through [cones_eq_val]: identify the
   abstract sup with the concrete witness [cones_eq_sup_ball], whose
   underlying value *is* the [D1]-sup of the chain.  (This used to be
   definitional, and needed a two-sided antisymmetry argument.) *)
move=> v vch vb1 fvch fvb1.
by rewrite (cones_eq_cone_sup_ballE vch vb1).
Qed.

Lemma der_incl_linear : is_linear (fun x : E => cones_eq_val x).
Proof.
exact: (cones_hom_linear (mcones_hom_cones (icones_hom_mcones e))).
Qed.

Lemma der_incl_scott : is_scott_continuous (fun x : E => cones_eq_val x).
Proof. exact: (linear_scott_of_omega _ der_incl_linear der_incl_omega). Qed.

(** *** The co-restriction of a stable map landing (on the ball) in [E] *)

Section CoRestrict.
Variable H : ICone.type Ar.
Variable h : scones_hom H D1.
Hypothesis Hh : scones_comp (ders f) h = scones_comp (ders g) h.

(** The equalising equation holds *everywhere*: on the unit ball it is
    the hypothesis read pointwise (all clamps transparent, [h x] in the
    ball by [sc_image_ball]); off the unit ball [h x = 0] ([sc_offball])
    and [f 0 = g 0 = 0] (linearity).  Hence the co-restricted point is
    well-defined for every [x]. *)
Lemma der_eq_all (x : H) : Lfun f (sc_fun h x) = Lfun g (sc_fun h x).
Proof.
have [Hx|Hx] := boolP (cone_norm x <= 1).
  have := congr1 (fun k : scones_hom H D2 => sc_fun k x) Hh.
  rewrite /= !(sc_clamp_ball Hx) /ders /=.
  by rewrite !(sc_clamp_ball (sc_image_ball h Hx)).
rewrite (sc_offball h x Hx).
have [f0 _ _] := cones_hom_linear (mcones_hom_cones (icones_hom_mcones f)).
have [g0 _ _] := cones_hom_linear (mcones_hom_cones (icones_hom_mcones g)).
by rewrite f0 g0.
Qed.

(** The co-restricted underlying function [H → E]: [h x] packaged with
    the equaliser witness. *)
Definition der_corestr_fun (x : H) : E := MkConesEq (der_eq_all x).

(** Its underlying [D1]-value is [h x]. *)
Lemma der_corestr_funE (x : H) :
  cones_eq_val (der_corestr_fun x) = sc_fun h x.
Proof. by []. Qed.

(** *** Stability of the co-restriction, reduced through [cones_eq_val]

    Each [is_meas_stable] clause for [der_corestr_fun : H → E] reduces to
    the corresponding clause for [h : H → D1], because the order / norm /
    measurability of [E] are the restriction of those of [D1] along the
    faithful inclusion [cones_eq_val]. *)

(** Projection of an [E]-cone-sum is the componentwise [D1]-cone-sum
    (the inclusion [cones_eq_val] is a [precone] morphism). *)
Lemma der_corestr_val_big (T : finType) (A : {set T}) (k : T -> E) :
  cones_eq_val (\big[precone_add/precone_zero]_(j in A) k j) =
  \big[precone_add/precone_zero]_(j in A) cones_eq_val (k j).
Proof. by elim/big_rec2: _ => [|j s s' _ <-]. Qed.

(** Total monotonicity — the (7.1) inequality on [E] follows from the one
    on [D1] (via the inclusion, [Htm] for [h]): the [D1]-witness [z] lifts
    to an [E]-witness because, the two cone-sums being in [E] and
    [val Sp = val Sn + z], cancellation in [D2] forces [f z = g z]. *)
Lemma der_corestr_totmono : is_totmono der_corestr_fun.
Proof.
move=> n x u Hz.
have [[Htm _ _] _] := sc_meas_stable h.
have HD1 :
  precone_le (\big[precone_add/precone_zero]_(I0 in Pneg n)
                cones_eq_val (der_corestr_fun (tm_arg x u I0)))
             (\big[precone_add/precone_zero]_(I0 in Ppos n)
                cones_eq_val (der_corestr_fun (tm_arg x u I0))).
  rewrite (eq_bigr (fun I0 => sc_fun h (tm_arg x u I0))); last first.
    by move=> I0 _; rewrite der_corestr_funE.
  rewrite [X in precone_le _ X]
    (eq_bigr (fun I0 => sc_fun h (tm_arg x u I0))); last first.
    by move=> I0 _; rewrite der_corestr_funE.
  exact: Htm.
case: HD1 => z Hz'.
rewrite -!der_corestr_val_big in Hz'.
have Hzeq : Lfun f z = Lfun g z.
  have [_ HfD _] := cones_hom_linear (mcones_hom_cones (icones_hom_mcones f)).
  have [_ HgD _] := cones_hom_linear (mcones_hom_cones (icones_hom_mcones g)).
  pose Sn := \big[precone_add/precone_zero]_(I0 in Pneg n)
               der_corestr_fun (tm_arg x u I0).
  pose Sp := \big[precone_add/precone_zero]_(I0 in Ppos n)
               der_corestr_fun (tm_arg x u I0).
  have HSn : Lfun f (cones_eq_val Sn) = Lfun g (cones_eq_val Sn)
    by exact: cones_eq_eq.
  have HSp : Lfun f (cones_eq_val Sp) = Lfun g (cones_eq_val Sp)
    by exact: cones_eq_eq.
  apply: (@precone_cancel _ _ (Lfun f (cones_eq_val Sn))).
  transitivity (Lfun f (cones_eq_val Sp)).
    by rewrite Hz' HfD.
  transitivity (Lfun g (cones_eq_val Sp)); first exact: HSp.
  by rewrite Hz' HgD HSn.
exists (MkConesEq Hzeq).
apply: cones_eq_extensional.
by rewrite /= Hz'.
Qed.

(** Boundedness on the unit ball: [‖h0 x‖_E = ‖h x‖_{D1} ≤ ‖h‖ ≤ 1]
    ([sc_image_ball]). *)
Lemma der_corestr_bounded :
  exists M : R, forall x : H, cone_norm x <= 1 ->
    cone_norm (der_corestr_fun x) <= M.
Proof.
exists 1 => x Hx.
rewrite -[cone_norm (der_corestr_fun x)]/(cones_eq_norm (der_corestr_fun x)).
rewrite /cones_eq_norm der_corestr_funE.
exact: (sc_image_ball h Hx).
Qed.

(** ω-continuity on the unit ball.  Apply [cones_eq_extensional]: the
    underlying [D1]-value of [h0 (sup u)] is [h (sup u) = cone_sup_at
    (h ∘ u)] ([h]'s ω-continuity); the underlying value of the [E]-sup_at
    [sup_at (h0 ∘ u)] is [cone_sup_at (cones_eq_val ∘ h0 ∘ u) =
    cone_sup_at (h ∘ u)] ([der_incl_scott]).  Both [cone_sup_at]s are over
    the pointwise-equal chain [h ∘ u]. *)
Lemma der_corestr_scott : is_scott_continuous_unit der_corestr_fun.
Proof.
move=> Mf u uch ub1 fuch fubMf Mfpos.
have [[_ _ Hsc] _] := sc_meas_stable h.
apply: cones_eq_extensional.
rewrite der_corestr_funE.
have huch : forall n, precone_le (sc_fun h (u n)) (sc_fun h (u n.+1)).
  by move=> n; rewrite -!der_corestr_funE; apply: cones_eq_le_underlying;
     exact: fuch.
have hubMf : forall n, cone_norm (sc_fun h (u n)) <= Mf%:num.
  by move=> n; rewrite -der_corestr_funE; have := fubMf n; rewrite /cones_eq_norm.
rewrite (Hsc Mf u uch ub1 huch hubMf Mfpos).
have hch' : forall n,
    precone_le (cones_eq_val (der_corestr_fun (u n)))
               (cones_eq_val (der_corestr_fun (u n.+1))).
  by move=> n; rewrite !der_corestr_funE.
have hub' : forall n,
    cone_norm (cones_eq_val (der_corestr_fun (u n))) <= Mf%:num.
  by move=> n; rewrite der_corestr_funE.
rewrite (der_incl_scott fuch fubMf Mfpos hch' hub' Mfpos).
apply: precone_le_anti.
- apply: cone_sup_at_lub => n.
  apply: precone_le_trans (cone_sup_at_ub hch' hub' Mfpos n).
  rewrite der_corestr_funE; exact: precone_le_refl.
- apply: cone_sup_at_lub => n.
  apply: precone_le_trans (cone_sup_at_ub huch hubMf Mfpos n).
  exact: precone_le_refl.
Qed.

(** Measurable-path preservation — reflected from [h] through the
    inclusion.  An [E]-test is [eqTest m] for a [D1]-test [m]; evaluated
    at [h0 (γ r)] it is [m (s, cones_eq_val (h0 (γ r))) = m (s, h (γ r))],
    measurable since [h ∘ γ] is a measurable [D1]-path ([h]'s path
    preservation). *)
Lemma der_corestr_pres_path (X : ar_obj Ar) (γ : ar_carrier Ar X -> H) :
  (forall r, cone_norm (γ r) <= 1) ->
  is_measurable_path (Ar:=Ar) (C:=H) γ ->
  is_measurable_path (Ar:=Ar) (C:=E) (fun r => der_corestr_fun (γ r)).
Proof.
move=> Hγb Hγ.
have [_ Hp] := sc_meas_stable h.
have Hhγ := Hp X γ Hγb Hγ.
split.
  case: Hhγ => [[M HM] _]; exists M => r.
  rewrite -[cone_norm (der_corestr_fun (γ r))]/
            (cones_eq_norm (der_corestr_fun (γ r))).
  rewrite /cones_eq_norm der_corestr_funE.
  exact: HM.
move=> Y m mM.
case: mM => p pM ->.
have [_ Hpm] := Hhγ.
have := Hpm Y p pM.
apply: eq_measurable_fun => sr _ /=.
by rewrite /eqTest /= /eqTest_fun der_corestr_funE.
Qed.

(** The co-restriction is measurable-stable. *)
Lemma der_corestr_meas_stable : is_meas_stable der_corestr_fun.
Proof.
split; first split.
- exact: der_corestr_totmono.
- exact: der_corestr_bounded.
- exact: der_corestr_scott.
- exact: der_corestr_pres_path.
Qed.

(** *** The mediator [der_eq_med : SCones(H, E)]

    The record-level clamp ([sc_clamp]) re-0-extends [der_corestr_fun]
    off the unit ball (it already vanishes there, since [h] does) and
    supplies the [sc_offball] field; the on-ball behaviour, hence
    stability and norm, are unchanged. *)

Lemma der_eq_med_meas_stable : is_meas_stable (sc_clamp der_corestr_fun).
Proof. exact: sc_clamp_meas_stable der_corestr_meas_stable. Qed.

Lemma der_eq_med_norm_le1 : sc_norm (sc_clamp der_corestr_fun) <= 1.
Proof.
apply: sc_norm_lub => x Hx; rewrite (sc_clamp_ball Hx).
have [M HM] := der_corestr_bounded.
rewrite -[cone_norm (der_corestr_fun x)]/(cones_eq_norm (der_corestr_fun x)).
rewrite /cones_eq_norm der_corestr_funE.
exact: (sc_image_ball h Hx).
Qed.

Definition der_eq_med : scones_hom H E :=
  MkSconesHom (sc_clamp der_corestr_fun) der_eq_med_meas_stable
    der_eq_med_norm_le1 (sc_clamp_offball_field _).

(** Factorisation: [Der e ∘ der_eq_med = h].  On the ball both clamps
    unfold, [Der e] applied to [h0 x] (in the ball) is [cones_eq_val
    (h0 x) = h x]; off the ball both sides are [0]. *)
Lemma der_eq_med_factor : scones_comp (ders e) der_eq_med = h.
Proof.
apply: scones_hom_eq => x; rewrite /=.
have [Hx|Hx] := boolP (cone_norm x <= 1); last first.
  by rewrite (sc_clamp_offball Hx) (sc_offball h x Hx).
rewrite !(sc_clamp_ball Hx).
have Hball : cone_norm (der_corestr_fun x) <= 1.
  rewrite -[cone_norm (der_corestr_fun x)]/(cones_eq_norm (der_corestr_fun x)).
  rewrite /cones_eq_norm der_corestr_funE.
  exact: (sc_image_ball h Hx).
rewrite /ders /= (sc_clamp_ball Hball).
exact: der_corestr_funE.
Qed.

(** Uniqueness: any [h' : SCones(H, E)] with [Der e ∘ h' = h] equals
    [der_eq_med].  [Der e]'s underlying function is (clamped)
    [cones_eq_val], which is faithful ([cones_eq_extensional]); on the
    ball the equation forces [cones_eq_val (h' x) = h x = cones_eq_val
    (der_eq_med x)], off the ball both are [0]. *)
Lemma der_eq_med_unique (h' : scones_hom H E) :
  scones_comp (ders e) h' = h -> h' = der_eq_med.
Proof.
move=> Hh'.
apply: scones_hom_eq => x; rewrite /=.
have [Hx|Hx] := boolP (cone_norm x <= 1); last first.
  by rewrite (sc_clamp_offball Hx) (sc_offball h' x Hx).
rewrite (sc_clamp_ball Hx).
apply: cones_eq_extensional.
rewrite der_corestr_funE.
(* From [Der e ∘ h' = h], pointwise on the ball:
   [cones_eq_val (h' x) = h x]. *)
have := congr1 (fun k : scones_hom H D1 => sc_fun k x) Hh'.
rewrite /= (sc_clamp_ball Hx).
have Hball : cone_norm (sc_fun h' x) <= 1 := sc_image_ball h' Hx.
by rewrite /ders /= (sc_clamp_ball Hball).
Qed.

End CoRestrict.

End DerEqualiser.

Arguments der_eq_equ {R Ar D1 D2} f g.
Arguments der_eq_med {R Ar D1 D2 f g H} h.
Arguments der_eq_med_factor {R Ar D1 D2 f g H} h.
Arguments der_eq_med_unique {R Ar D1 D2 f g H} h.

(** ** Wrap-up — Paper Theorem 7.34: [Der] preserves all limits

    A category with all small products and equalisers has all (small)
    limits, and a functor preserving both preserves all limits.  The two
    deliverables above are exactly those facts for [Der]:

    - products: [der_preserves_prod_proj] together with the SCones
      product universal property [scones_tuple_proj] / [scones_tuple_unique]
      of [scones_cat.v] (the SCones product *is* the [ICones] product);

    - equalisers: [der_eq_equ] (the transported factorisation) together
      with [der_eq_med] / [der_eq_med_factor] / [der_eq_med_unique] (the
      equaliser universal property of [(Der E, Der e)] for [Der f],
      [Der g]).

    [der_continuous] below bundles the equaliser half as a single record,
    the concrete per-consumer input that Theorem 7.34 feeds, via the
    M-SAFT machinery of [Icones.homs.representable], to construct the
    left adjoint [E] of [Der] (the exponential, PLAN §13.4).  This
    limit-preservation is the *input* to SAFT, not a consumer of the
    (later) exponential structure. *)

Section DerContinuous.
Variables (R : realType) (Ar : MeasSubcat R).

(** Preservation of all equalisers: for [f, g : D1 → D2] the pair
    [(Der E, Der e)] equalises [Der f], [Der g] in [SCones] and is
    universal. *)
Record der_continuous : Prop := MkDerContinuous {
  dc_eq_equ :
    forall (D1 D2 : ICone.type Ar) (f g : icones_hom Ar D1 D2),
      scones_comp (ders f) (ders (icones_eq_incl f g)) =
      scones_comp (ders g) (ders (icones_eq_incl f g));
  dc_eq_med :
    forall (D1 D2 : ICone.type Ar) (f g : icones_hom Ar D1 D2)
           (Hobj : ICone.type Ar) (h : scones_hom Hobj D1),
      scones_comp (ders f) h = scones_comp (ders g) h ->
      { h0 : scones_hom Hobj (icones_eq f g)
      | scones_comp (ders (icones_eq_incl f g)) h0 = h
        /\ forall h' : scones_hom Hobj (icones_eq f g),
             scones_comp (ders (icones_eq_incl f g)) h' = h -> h' = h0 };
}.

(** Paper Theorem 7.34 (equaliser half): [Der] preserves equalisers.
    Together with product-preservation ([der_preserves_prod_proj] above),
    this gives preservation of all small limits — the SAFT input consumed by
    [bang_construct] / [tensor_construct]. (The name [der_preserves_limits]
    refers to that whole; this lemma's type is the equaliser component.) *)
Theorem der_preserves_limits : der_continuous.
Proof.
split.
- by move=> D1 D2 f g; exact: der_eq_equ.
- move=> D1 D2 f g Hobj h Hh.
  exists (der_eq_med h Hh); split.
  + exact: (der_eq_med_factor h Hh).
  + move=> h' Hh'.
    exact: (der_eq_med_unique h Hh h' Hh').
Qed.

End DerContinuous.

Arguments der_continuous {R Ar}.
Arguments der_preserves_limits {R Ar}.
