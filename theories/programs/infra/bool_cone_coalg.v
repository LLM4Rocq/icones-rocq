(**md *** PPL CBV chapter infrastructure — §9.7 coalgebra on [bool_cone_car]

    This file is NOT part of the Ehrhard-Geoffroy 2025 formalization
    (paper §2-§9).  It hand-rolls a [!]-coalgebra structure on the
    2-point sub-probability cone [bool_cone_car Ar] of
    [theories/programs/infra/bool_cone.v], mirroring the §9.7-style
    [FMeas_coalgebra] of [theories/homs/coalgebra.v].

    Mathematical content.  The §9.7 coalgebra on [FMeas X] is
    [Coalg_X(µ) = ∫ prom(δ_x) dµ(x)].  Specialised to the 2-point cone
    (which morally is [FMeas {true, false}] but is built concretely
    here, without a [measurableType] backing), the integral degenerates
    to a finite sum:
    [[
       bool_coalg_str (p · δ_T + q · δ_F)
         = p · prom(bool_dirac_true) + q · prom(bool_dirac_false)
    ]]
    in [Bang Ar (bool_cone_car Ar)].

    Why this matters for the PPL.  With [tbool ↦ bool_cone_coalg], the
    induced commutative comonoid on [⟦tbool⟧] is the DIAGONAL
    pushforward, so [let x = Bernoulli(p) in (x, x)] denotes
    [p · (T,T) + (1-p) · (F,F)] (shared-sample) instead of
    [p² · (T,T) + p(1-p) · (T,F) + (1-p)p · (F,T) + (1-p)² · (F,F)]
    (independent-product) that the [bang_cofree] structure would give.

    Construction.  We use the universal-property co-pairing
    [bool_case_icones_hom] of [bool_case_hom.v] with the two branches
    set to [prom bool_dirac_true] and [prom bool_dirac_false] in
    [Bang Ar (bool_cone_car Ar)] (both unit-ball by [prom_ball]).  The
    two coalgebra laws reduce, on the basis points [bool_dirac_true]
    and [bool_dirac_false], to the comonad identities
    [der ∘ prom = id], [dig ∘ prom = prom ∘ prom], and the basis
    identity [bool_coalg_str (bool_dirac_true) = prom(bool_dirac_true)]
    (and similarly for [false]).

    See also: [theories/homs/coalgebra.v] (the prototype, on [FMeas X]),
    [theories/programs/infra/bool_cone.v] (the carrier),
    [theories/programs/infra/bool_case_hom.v] (the universal-property
    combinator), [theories/programs/ppl_cbv.v] (the consumer). *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference.

Require Import Icones.prelude.nonneg_extra.
Require Import Icones.cones.precone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.cone.
Require Import Icones.cones.cone_cat.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_cat.
Require Import Icones.homs.linhom.
Require Import Icones.homs.seely.
Require Import Icones.homs.exp_adjunction.
Require Import Icones.homs.bang.
Require Import Icones.homs.coalgebra.
Require Import Icones.homs.em_cat.
Require Import Icones.programs.infra.bool_cone.
Require Import Icones.programs.infra.bool_case_hom.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section BoolConeCoalg.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation T := (bool_cone_car Ar).

(** Underlying linear function of an [icones_hom] (same chain as
    [coalgebra.v]). *)
Local Notation Lfun h := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

(** The two promoted basis points are in the unit ball. *)
Lemma prom_bool_dirac_true_ball :
  (cone_norm (prom (bool_dirac_true : T) : Bang Ar T) <= 1)%R.
Proof. by apply: prom_ball; rewrite bool_dirac_true_norm. Qed.

Lemma prom_bool_dirac_false_ball :
  (cone_norm (prom (bool_dirac_false : T) : Bang Ar T) <= 1)%R.
Proof. by apply: prom_ball; rewrite bool_dirac_false_norm. Qed.

(** ** The §9.7-style structure map [bool_coalg_str : T ⊸ !T]

    Built via the universal-property co-pairing [bool_case_icones_hom]
    with branches [prom bool_dirac_true] and [prom bool_dirac_false].
    Pointwise:
    [[
       bool_coalg_str (MkBoolCone p q)
         = p · prom(bool_dirac_true) + q · prom(bool_dirac_false)
    ]]
    in [Bang Ar T]. *)
Definition bool_coalg_str : icones_hom Ar T (Bang Ar T) :=
  bool_case_icones_hom
    (prom (bool_dirac_true : T))
    (prom (bool_dirac_false : T))
    prom_bool_dirac_true_ball
    prom_bool_dirac_false_ball.

(** ** Basis-point computations *)

(** On the true basis: [bool_coalg_str(δ_T) = prom(δ_T)]. *)
Lemma bool_coalg_str_true :
  Lfun bool_coalg_str bool_dirac_true = prom (bool_dirac_true : T).
Proof.
rewrite /bool_coalg_str /bool_case_icones_hom.
rewrite (linhom_iconesE _ (bool_case_linhom_norm_le1 _ _ _ _) bool_dirac_true).
rewrite /linhom_fun /=.
exact: bool_case_true.
Qed.

(** On the false basis: [bool_coalg_str(δ_F) = prom(δ_F)]. *)
Lemma bool_coalg_str_false :
  Lfun bool_coalg_str bool_dirac_false = prom (bool_dirac_false : T).
Proof.
rewrite /bool_coalg_str /bool_case_icones_hom.
rewrite (linhom_iconesE _ (bool_case_linhom_norm_le1 _ _ _ _) bool_dirac_false).
rewrite /linhom_fun /=.
exact: bool_case_false.
Qed.

(** ** Universal-property dispatch: two [icones_hom] out of [T] are
    equal iff they agree on the two basis points. *)

(** Pointwise expansion: every [x : T] is the co-pairing of the basis
    points with itself.  Concretely [x = bool_case x δ_T δ_F]. *)
Lemma bool_cone_basis_expand (x : T) :
  x = bool_case x bool_dirac_true bool_dirac_false.
Proof.
case: x => p q.
rewrite /bool_case /bool_dirac_true /bool_dirac_false /=.
apply: bool_cone_eq; apply: nngnum_inj;
  rewrite /precone_add /precone_scale /= /bc_add /bc_scale /=.
- by rewrite mulr1 mulr0 addr0.
- by rewrite mulr0 mulr1 add0r.
Qed.

(** Universal-property dispatch.  Any [icones_hom] [h : T → B] is
    determined by [h(δ_T)] and [h(δ_F)]: by linearity,
    [h(x) = h(bool_case x δ_T δ_F)
          = bool_case x (h δ_T) (h δ_F)]. *)
Lemma bool_cone_dispatch (B : ICone.type Ar)
    (f g : icones_hom Ar T B) :
  Lfun f bool_dirac_true = Lfun g bool_dirac_true ->
  Lfun f bool_dirac_false = Lfun g bool_dirac_false ->
  f = g.
Proof.
move=> Ht Hf.
apply: icones_hom_eq => x.
have [_ linfD linfZ] : is_linear (Lfun f) := cones_hom_linear _.
have [_ lingD lingZ] : is_linear (Lfun g) := cones_hom_linear _.
rewrite [in LHS](bool_cone_basis_expand x).
rewrite [in RHS](bool_cone_basis_expand x).
rewrite /bool_case.
rewrite linfD linfZ linfZ.
rewrite lingD lingZ lingZ.
by rewrite Ht Hf.
Qed.

(** ** The two coalgebra laws *)

(** Counit: [der ∘ bool_coalg_str = id].  Reduces on each basis point
    via [bool_coalg_str_(true/false)] and [der_prom] (with the
    Dirac norms [= 1]). *)
Lemma bool_coalg_counit :
  icones_comp (der T) bool_coalg_str = icones_id Ar T.
Proof.
apply: bool_cone_dispatch.
- rewrite /=.
  rewrite -[LHS]/(Lfun (der T) (Lfun bool_coalg_str bool_dirac_true)).
  rewrite bool_coalg_str_true.
  rewrite (der_prom bool_dirac_true); first by [].
  by rewrite bool_dirac_true_norm.
- rewrite /=.
  rewrite -[LHS]/(Lfun (der T) (Lfun bool_coalg_str bool_dirac_false)).
  rewrite bool_coalg_str_false.
  rewrite (der_prom bool_dirac_false); first by [].
  by rewrite bool_dirac_false_norm.
Qed.

(** Coassoc: [dig ∘ bool_coalg_str = !(bool_coalg_str) ∘ bool_coalg_str].
    Reduces on each basis point.  On [δ_T]:
    - LHS = [dig(prom δ_T) = prom(prom δ_T)]  ([dig_prom]),
    - RHS = [!(bool_coalg_str)(prom δ_T) = prom(bool_coalg_str δ_T)
           = prom(prom δ_T)]               ([bang_fmap_prom] +
                                            [bool_coalg_str_true]).
    Similarly on [δ_F]. *)
Lemma bool_coalg_coassoc :
  icones_comp (dig T) bool_coalg_str =
  icones_comp (bang_fmap bool_coalg_str) bool_coalg_str.
Proof.
apply: bool_cone_dispatch.
- rewrite /=.
  rewrite -[LHS]/(Lfun (dig T) (Lfun bool_coalg_str bool_dirac_true)).
  rewrite -[RHS]/(Lfun (bang_fmap bool_coalg_str)
                       (Lfun bool_coalg_str bool_dirac_true)).
  rewrite bool_coalg_str_true.
  rewrite (dig_prom bool_dirac_true);
    last by rewrite bool_dirac_true_norm.
  rewrite (bang_fmap_prom bool_coalg_str bool_dirac_true);
    last by rewrite bool_dirac_true_norm.
  by rewrite bool_coalg_str_true.
- rewrite /=.
  rewrite -[LHS]/(Lfun (dig T) (Lfun bool_coalg_str bool_dirac_false)).
  rewrite -[RHS]/(Lfun (bang_fmap bool_coalg_str)
                       (Lfun bool_coalg_str bool_dirac_false)).
  rewrite bool_coalg_str_false.
  rewrite (dig_prom bool_dirac_false);
    last by rewrite bool_dirac_false_norm.
  rewrite (bang_fmap_prom bool_coalg_str bool_dirac_false);
    last by rewrite bool_dirac_false_norm.
  by rewrite bool_coalg_str_false.
Qed.

(** ** Package as a [Coalgebra Ar]. *)
Definition bool_cone_coalg : Coalgebra Ar :=
  MkCoalgebra bool_coalg_counit bool_coalg_coassoc.

(** Sanity: its underlying carrier is [bool_cone_car Ar]. *)
Lemma bool_cone_coalg_obj : coalg_obj bool_cone_coalg = T.
Proof. by []. Qed.

(** Sanity: its structure map is [bool_coalg_str]. *)
Lemma bool_cone_coalg_str_E : coalg_str bool_cone_coalg = bool_coalg_str.
Proof. by []. Qed.

End BoolConeCoalg.

Arguments bool_coalg_str {R Ar}.
Arguments bool_coalg_str_true {R Ar}.
Arguments bool_coalg_str_false {R Ar}.
Arguments bool_cone_basis_expand {R Ar} x.
Arguments bool_cone_dispatch {R Ar B} f g.
Arguments bool_coalg_counit {R Ar}.
Arguments bool_coalg_coassoc {R Ar}.
Arguments bool_cone_coalg {R Ar}.
Arguments bool_cone_coalg_obj {R Ar}.
Arguments bool_cone_coalg_str_E {R Ar}.
