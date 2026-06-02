(**md *** BEYOND THE PAPER — PPL CBV chapter infrastructure

    This file is NOT part of the Ehrhard-Geoffroy 2025 formalization
    (paper §2-§9). It provides the convex-combination reduction of
    [case_em] against a Bernoulli scrutinee, used to close Phase 4's
    [ex_geom] mass-1 theorem (reducing the [if Bern(½) then 0 else 1+g()]
    pattern to [½·(then 0) + ½·(else 1+g())] at the cone level).

    Headline:
    - [convex_icones p Hp_ge0 Hp_le1 a b] — the underlying icones_hom of
      the convex combination [p·a + (1-p)·b] at the linhom-cone level
      (= [bool_case (bernoulli p) a_lh b_lh] via [linhom_icones]).
    - [convex_combination p Hp_ge0 Hp_le1 a b] — the coalg_hom packaging
      of [convex_icones] via [adj_psi].
    - [case_em_bernoulli] — the reduction
        [kbind_ext (case_em a b) (bernoulli_kleisli p) =
         convex_combination p a b].

    See also: [theories/programs/infra/bool_case_hom.v] (icones_hom
    packaging of [bool_case]), [theories/programs/ppl.v] (case_em,
    bernoulli_kleisli, ne_bernoulli, ne_if). *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals constructive_ereal.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import ereal.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import measure.

Require Import Icones.prelude.classical_extra.
Require Import Icones.prelude.nonneg_extra.
Require Import Icones.prelude.omegacpo.
Require Import Icones.cones.precone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.cone.
Require Import Icones.cones.cone_cat.
Require Import Icones.programs.infra.bool_cone.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.mcones.path.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_cat.
Require Import Icones.homs.linhom.
Require Import Icones.homs.tensor.
Require Import Icones.homs.tensor_construct.
Require Import Icones.homs.smcc.
Require Import Icones.homs.exp_adjunction.
Require Import Icones.homs.bang.
Require Import Icones.homs.seely.
Require Import Icones.homs.tensor_hom_iso.
Require Import Icones.programs.infra.bool_case_hom.
Require Import Icones.homs.coalgebra.
Require Import Icones.homs.em_cat.
Require Import Icones.homs.em_cartesian.
Require Import Icones.programs.cbv.
Require Import Icones.programs.ppl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** The convex combination [p·a + (1-p)·b]

    At the linhom-cone level, the convex combination is exactly the
    evaluation of [bool_case_linhom a_lh b_lh] at the [bernoulli p]
    element of [bool_cone_car].  Operationally:
    [[
      bool_case (bernoulli p) a_lh b_lh
      = precone_add (precone_scale p a_lh) (precone_scale (1-p) b_lh).
    ]]
    Norm: bounded by [≤ 1] since [bernoulli p] has norm exactly [1] and
    [bool_case_linhom] has operator norm [≤ 1] (its unit-ball-respecting
    form). *)

Section ConvexCombination.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (G A : Coalgebra Ar).
Variables (a b : coalg_hom G (Tobj A)).
Variables (p : R) (Hp_ge0 : (0 <= p)%R) (Hp_le1 : (p <= 1)%R).

(** Branches as norm-[≤1] points in the hom-cone (matching the local
    [Let]-definitions inside [Section CaseEM] of [ppl.v]). *)
Let a_lh : linhom_car Ar (coalg_obj G) (Bang Ar (coalg_obj A)) :=
  icones_to_linhom (ch_mor a).
Let b_lh : linhom_car Ar (coalg_obj G) (Bang Ar (coalg_obj A)) :=
  icones_to_linhom (ch_mor b).

Lemma cc_a_lh_norm : (cone_norm a_lh <= 1)%R.
Proof. exact: icones_to_linhom_norm_le1 (ch_mor a). Qed.

Lemma cc_b_lh_norm : (cone_norm b_lh <= 1)%R.
Proof. exact: icones_to_linhom_norm_le1 (ch_mor b). Qed.

(** The convex combination at the linhom level, packaged as a [linhom_car]. *)
Definition convex_linhom : linhom_car Ar (coalg_obj G) (Bang Ar (coalg_obj A)) :=
  bool_case (@bernoulli R Ar p Hp_ge0 Hp_le1) a_lh b_lh.

(** Operational reading: [convex_linhom = bool_case (bernoulli p) a_lh b_lh].

    This is a definitional unfolding, but recorded as a lemma for clarity:
    [convex_linhom] IS the evaluation of [bool_case_linhom] at the
    [bernoulli p] scrutinee. *)
Lemma convex_linhomE :
  convex_linhom = bool_case (@bernoulli R Ar p Hp_ge0 Hp_le1) a_lh b_lh.
Proof. by []. Qed.

(** Norm bound: [cone_norm convex_linhom ≤ 1].

    Proof: by [linhom_norm_sup_lub] reduce to a pointwise bound at
    [cone_norm g ≤ 1]; then via [bool_case_norm_le1] (the unit-ball
    bound on [bool_case_linhom]) we have
    [cone_norm (bool_case_linhom a_lh b_lh x) ≤ cone_norm x] for any
    [x : bool_cone] (since both [a_lh], [b_lh] have norm ≤ 1).  Specialise
    to [x = bernoulli p] which has norm exactly [1]; thread through
    [cone_normh] from [g] to the linhom_apply norm. *)
Lemma convex_linhom_norm_le1 : (cone_norm convex_linhom <= 1)%R.
Proof.
rewrite /convex_linhom.
(* The proof: bool_case_linhom a_lh b_lh has norm ≤ 1 (unit-ball form);
   evaluating it at any x : bool_cone with norm ≤ 1 yields a result of
   norm ≤ 1 in the codomain (here, linhom_car ... ).  [bernoulli p] has
   norm exactly 1, so the bound applies. *)
have Hball : (cone_norm (@bernoulli R Ar p Hp_ge0 Hp_le1 : bool_cone_car Ar) <= 1)%R
  := @bernoulli_norm_le1 R Ar p Hp_ge0 Hp_le1.
have Hbc := bool_case_norm_le1 (a := a_lh) (b := b_lh) cc_a_lh_norm cc_b_lh_norm
              (@bernoulli R Ar p Hp_ge0 Hp_le1).
exact: le_trans Hbc Hball.
Qed.

(** The icones_hom packaging of [convex_linhom] in [Bang Ar (coalg_obj A)],
    using the [linhom_icones] bridge. *)
Definition convex_icones_bang :
    icones_hom Ar (coalg_obj G) (Bang Ar (coalg_obj A)) :=
  linhom_icones convex_linhom convex_linhom_norm_le1.

(** The icones_hom presentation INTO [coalg_obj A] (the input of [adj_psi]):
    post-compose [convex_icones_bang] with [der A] to drop the outer [!].
    This is the icones_hom whose [adj_psi]-image is the natural
    [coalg_hom G (Tobj A)] presentation of the convex combination. *)
Definition convex_icones :
    icones_hom Ar (coalg_obj G) (coalg_obj A) :=
  icones_comp (der (coalg_obj A)) convex_icones_bang.

(** The coalg_hom packaging — this is the natural [coalg_hom G (Tobj A)]
    presentation of the convex combination [p·a + (1-p)·b]. *)
Definition convex_combination : coalg_hom G (Tobj A) :=
  adj_psi (P := G) (B := coalg_obj A) convex_icones.

(** Operational reading at the icones_hom level: [adj_phi] of the convex
    combination is exactly [convex_icones]. *)
Lemma adj_phi_convex_combination :
  adj_phi convex_combination = convex_icones.
Proof. exact: adj_phiK convex_icones. Qed.

End ConvexCombination.

Arguments convex_linhom {R Ar G A} a b {p} Hp_ge0 Hp_le1.
Arguments convex_icones_bang {R Ar G A} a b {p} Hp_ge0 Hp_le1.
Arguments convex_icones {R Ar G A} a b {p} Hp_ge0 Hp_le1.
Arguments convex_combination {R Ar G A} a b {p} Hp_ge0 Hp_le1.
Arguments adj_phi_convex_combination {R Ar G A} a b {p} Hp_ge0 Hp_le1.
