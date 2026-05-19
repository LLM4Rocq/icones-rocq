(** * Paper Theorem 6.5 — [Skern ↪ ICones] is fully faithful

    Paper reference: §6.1, lines 3057–3069 of [paper/icones.txt].

    The functor [Klin : Skern → ICones] sends [X ∈ Ar] to [FMeas(X)]
    and a substochastic kernel [κ : X → FMeas(Y)] to its associated
    integrable linear map [I^{FMeas(Y)}_X(κ) : FMeas(X) → FMeas(Y)]
    (paper §6 Thm 6.1). Paper Theorem 6.5 states that this functor
    is full and faithful — a direct corollary of Thm 6.1, the
    [Path(X, B) ≃ FMeas(X) ⊸ B] isomorphism proved in [bilin.v].

    Coverage in this file:

    - [Skern_to_ICones_obj X := fmeas R (ar_carrier Ar X)] —
      the on-objects part of [Klin] (paper §6.1, line 3058: [Klin]
      maps [X ∈ Ar] to [FMeas(X)]).

    - [Skern_to_ICones_mor κ] — the on-morphisms part of [Klin],
      packaging [int_to_linhom κ] as an [icones_hom Ar (FMeas X)
      (FMeas Y)]. The packaging uses the fact that [path_norm κ ≤ 1]
      forces [cone_norm (int_to_linhom κ µ) ≤ cone_norm µ] pointwise
      (the [cones_hom_norm_le1] requirement). All five fields of
      [int_to_linhom] (linearity, ω-continuity, boundedness,
      measurable-path preservation, integral preservation) come from
      [bilin.v]; the pointwise norm bound is added using
      [path_integral_norm_le] with constant [1].

    - [Skern_to_ICones_faithful] — paper Thm 6.5 faithful direction:
      [Skern_to_ICones_mor κ1 = Skern_to_ICones_mor κ2 → κ1 = κ2].
      Direct from the round-trip [K ∘ I = id] of [bilin.v]
      ([K_I_int_to_linhom_path_E]).

    - [Skern_to_ICones_full] — paper Thm 6.5 full direction: for every
      [f : icones_hom (FMeas X) (FMeas Y)], there exists [κ : Skern X Y]
      with [Skern_to_ICones_mor κ = f]. Take [κ := linhom_to_int f]
      (with norm bound [path_norm κ ≤ linhom_norm f ≤ 1]); the equation
      follows from the other round-trip [I ∘ K = id] of [bilin.v]
      ([I_K_int_to_linhom_E]).

    - [Skern_to_ICones_fully_faithful] — paper Thm 6.5, combining the
      two. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals constructive_ereal.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import ereal sequences.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measure.
From mathcomp.analysis Require Import lebesgue_integral_definition.
Import numFieldTopology.Exports.

Require Import Icones.prelude.classical_extra.
Require Import Icones.prelude.nonneg_extra.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.cone_cat.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.mcones.path.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.pettis.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_integral.
Require Import Icones.icones.examples_icone.
Require Import Icones.icones.fubini.
Require Import Icones.icones.icone_cat.
Require Import Icones.homs.linhom.
Require Import Icones.homs.bilin.
Require Import Icones.kernels.skern.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** Paper §6.1, line 3058: [Klin] on objects *)

Section SkernToIConesObj.
Variables (R : realType) (Ar : MeasSubcat R).

(** [Klin X := FMeas(X)]. *)
Definition Skern_to_ICones_obj (X : ar_obj Ar) : ICone.type Ar :=
  fmeas R (ar_carrier Ar X).

End SkernToIConesObj.

Arguments Skern_to_ICones_obj {R Ar}.

(** ** Paper §6.1, line 3057: [Klin] on morphisms

    For [κ : Skern X Y], the value [Klin(κ) := I^{FMeas(Y)}_X(κ)] is
    the integrable linear map from [bilin.v]. We package it as an
    [icones_hom] by re-exhibiting the five fields of [int_to_linhom]
    (which already deliver everything we need) plus the pointwise
    [cones_hom_norm_le1] bound, which uses the unit-norm hypothesis
    [path_norm κ ≤ 1]. *)

Section SkernToIConesMor.
Variables (R : realType) (Ar : MeasSubcat R).
Variables X Y : ar_obj Ar.
Variable κ : Skern_hom Ar X Y.

Local Notation κp := (skern_path κ).
Local Notation κf := (path_fun κp).
Local Notation Hκp := (path_is_path κp).

(** The underlying function of [Klin(κ)]. *)
Local Notation Klin_fun :=
  (@int_to_linhom_fun R Ar X (fmeas R (ar_carrier Ar Y)) κp).

(** Pointwise norm bound: [cone_norm (Klin κ µ) ≤ cone_norm µ] — uses
    [path_norm κ ≤ 1] and [path_integral_norm_le]. *)
Lemma Skern_to_ICones_mor_norm_le1 (µ : fmeas R (ar_carrier Ar X)) :
  cone_norm (Klin_fun µ) <= cone_norm µ.
Proof.
rewrite /int_to_linhom_fun.
have Hub : cone_norm (icone_integral κf Hκp µ) <=
           path_norm κp * fmeas_norm µ.
  apply: (path_integral_norm_le (Mβ := path_norm κp)).
  - exact: path_norm_ub.
  - exact: Hκp.
  - exact: icone_integralP.
apply: le_trans Hub _.
have -> : cone_norm µ = 1 * cone_norm µ by rewrite mul1r.
apply: ler_pM.
- exact: path_norm_ge0.
- exact: cone_norm_ge0.
- exact: skern_norm_le1.
- exact: lexx.
Qed.

(** The [cones_hom] core of [Klin(κ)]. *)
Definition Skern_to_ICones_mor_chom :
    cones_hom (fmeas R (ar_carrier Ar X)) (fmeas R (ar_carrier Ar Y)) :=
  ConesHom Klin_fun
    (int_to_linhom_fun_linear κp)
    (int_to_linhom_fun_continuous κp)
    Skern_to_ICones_mor_norm_le1.

(** Path-preservation upgrade to [mcones_hom]. *)
Lemma Skern_to_ICones_mor_pres_path
  (Z : ar_obj Ar) (γ : ar_carrier Ar Z -> fmeas R (ar_carrier Ar X))
  (Hγ : is_measurable_path γ) :
  is_measurable_path
    (fun r => cones_hom_fun Skern_to_ICones_mor_chom (γ r)).
Proof.
exact: (int_to_linhom_fun_pres_path κp Hγ).
Qed.

(** The [mcones_hom] upgrade. *)
Definition Skern_to_ICones_mor_mhom :
    mcones_hom Ar (fmeas R (ar_carrier Ar X)) (fmeas R (ar_carrier Ar Y)) :=
  MkMConesHom Skern_to_ICones_mor_chom Skern_to_ICones_mor_pres_path.

(** Integral-preservation upgrade to [icones_hom]. *)
Lemma Skern_to_ICones_mor_pres_int
  (Z : ar_obj Ar) (β : ar_carrier Ar Z -> fmeas R (ar_carrier Ar X))
  (Hβ : is_measurable_path β)
  (µ : fmeas R (ar_carrier Ar Z)) :
  cones_hom_fun (mcones_hom_cones Skern_to_ICones_mor_mhom)
                (icone_integral β Hβ µ) =
  icone_integral
    (fun r => cones_hom_fun (mcones_hom_cones Skern_to_ICones_mor_mhom)
                            (β r))
    (mcones_hom_pres_path Skern_to_ICones_mor_mhom Z β Hβ) µ.
Proof.
rewrite /=.
have Hpres := int_to_linhom_fun_pres_int κp Hβ µ.
rewrite /int_to_linhom_fun in Hpres |- *.
apply: (eq_trans Hpres).
by congr (icone_integral _ _ _).
Qed.

(** Paper §6.1, line 3057: [Klin(κ)] packaged as an [icones_hom]. *)
Definition Skern_to_ICones_mor :
    icones_hom Ar (fmeas R (ar_carrier Ar X)) (fmeas R (ar_carrier Ar Y)) :=
  MkIConesHom Skern_to_ICones_mor_mhom Skern_to_ICones_mor_pres_int.

(** Compute: [Klin(κ) µ = icone_integral κ _ µ]. *)
Lemma Skern_to_ICones_mor_E (µ : fmeas R (ar_carrier Ar X)) :
  cones_hom_fun (mcones_hom_cones (icones_hom_mcones Skern_to_ICones_mor)) µ
    = icone_integral κf Hκp µ.
Proof. by []. Qed.

End SkernToIConesMor.

Arguments Skern_to_ICones_mor {R Ar X Y}.

(** ** Paper Theorem 6.5 — faithfulness

    Given [κ1, κ2 : Skern X Y] with [Klin(κ1) = Klin(κ2)] in
    [icones_hom], the underlying functions agree pointwise on every
    [µ], in particular on every Dirac. Hence the [linhom_to_int] of
    the underlying [linhom_car]s agree, and the round-trip identity
    [K ∘ I = id] (paper Thm 6.1, [K_I_int_to_linhom_path_E]) gives
    [κ1 = κ2]. *)

Section SkernToIConesFaithful.
Variables (R : realType) (Ar : MeasSubcat R).
Variables X Y : ar_obj Ar.

(** Paper Theorem 6.5 — faithful direction. *)
Theorem Skern_to_ICones_faithful (κ1 κ2 : Skern_hom Ar X Y) :
  Skern_to_ICones_mor κ1 = Skern_to_ICones_mor κ2 -> κ1 = κ2.
Proof.
move=> Heq.
(* Both [skern_path κ1] and [skern_path κ2] satisfy
   [linhom_to_int (int_to_linhom (skern_path κi)) = skern_path κi]. *)
have HK1 := K_I_int_to_linhom_path_E (skern_path κ1).
have HK2 := K_I_int_to_linhom_path_E (skern_path κ2).
(* From the equality of [icones_hom]s, derive equality of the
   underlying functions, then equality of [int_to_linhom]s. *)
have fun_eq : forall µ : fmeas R (ar_carrier Ar X),
  int_to_linhom_fun (skern_path κ1) µ =
  int_to_linhom_fun (skern_path κ2) µ.
  move=> µ.
  have := f_equal
    (fun f : icones_hom Ar _ _ =>
       cones_hom_fun (mcones_hom_cones (icones_hom_mcones f)) µ) Heq.
  by [].
(* Then [int_to_linhom κ1 = int_to_linhom κ2] as [linhom_car]. *)
have linhom_eq_pkg :
    int_to_linhom (skern_path κ1) = int_to_linhom (skern_path κ2).
  apply: linhom_eq => x; exact: fun_eq.
(* Apply [linhom_to_int] to both sides; use [K ∘ I = id]. *)
have path_eq_pkg : skern_path κ1 = skern_path κ2.
  rewrite -HK1 -HK2.
  by congr linhom_to_int.
exact: Skern_hom_eq.
Qed.

End SkernToIConesFaithful.

Arguments Skern_to_ICones_faithful {R Ar X Y}.

(** ** Paper Theorem 6.5 — fullness

    For every [f : icones_hom (FMeas X) (FMeas Y)], we construct
    [κ := linhom_to_int (icones_to_linhom f) : Skern X Y].

    The auxiliary helper [icones_to_linhom f] packages an
    [icones_hom] as a [linhom_car]; the operator norm of the result
    is bounded by [1] thanks to [cones_hom_norm_le1], hence the
    associated path is in the unit ball.

    The functorial-image equation [Skern_to_ICones_mor κ = f] follows
    from the round-trip [I ∘ K = id]. *)

Section SkernToIConesFull.
Variables (R : realType) (Ar : MeasSubcat R).
Variables X Y : ar_obj Ar.

(** ** Helper: convert an [icones_hom] to a [linhom_car]

    The pointwise norm bound [cnorm (f x) ≤ cnorm x] implies the
    boundedness [exists M, ∀ x, cnorm x ≤ 1 → cnorm (f x) ≤ M]
    with [M := 1]. The other four fields come from the underlying
    [cones_hom] / [mcones_hom] / [icones_hom_pres_int]. *)

Variable f : icones_hom Ar (fmeas R (ar_carrier Ar X))
                          (fmeas R (ar_carrier Ar Y)).

Local Notation ff := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones f))).

Local Lemma icones_to_linhom_bounded :
  exists M : R,
    forall x : fmeas R (ar_carrier Ar X),
      cone_norm x <= 1 -> cone_norm (ff x) <= M.
Proof.
exists 1 => x Hx.
apply: le_trans Hx.
exact: cones_hom_norm_le1.
Qed.

Local Definition icones_to_linhom_pre :
    linhom_pre Ar (fmeas R (ar_carrier Ar X))
                  (fmeas R (ar_carrier Ar Y)) :=
  MkLinhomPre ff
    (@cones_hom_linear R _ _ (mcones_hom_cones (icones_hom_mcones f)))
    (@cones_hom_continuous R _ _ (mcones_hom_cones (icones_hom_mcones f)))
    icones_to_linhom_bounded
    (mcones_hom_pres_path (icones_hom_mcones f)).

Local Definition icones_to_linhom :
    linhom_car Ar (fmeas R (ar_carrier Ar X))
                  (fmeas R (ar_carrier Ar Y)) :=
  MkLinhom icones_to_linhom_pre (icones_hom_pres_int f).

(** The candidate Skern morphism: [κ := r ↦ f (\d_r)]. *)
Local Definition icones_to_skern_path :
    path_car Ar X (fmeas R (ar_carrier Ar Y)) :=
  linhom_to_int icones_to_linhom.

(** Norm bound: every value [f (\d_r)] has norm ≤ [cone_norm (\d_r)] ≤ 1
    by [cones_hom_norm_le1] and [dirac_fmeas_norm]. *)
Local Lemma icones_to_skern_norm_le1 :
  path_norm icones_to_skern_path <= 1.
Proof.
apply: ge_sup; first exact: path_normset_nonempty.
move=> _ [r ->] /=.
rewrite /linhom_to_int_fun /linhom_fun /=.
apply: le_trans (cones_hom_norm_le1
                   (mcones_hom_cones (icones_hom_mcones f))
                   (dirac_fmeas r)) _.
by rewrite dirac_fmeas_norm.
Qed.

(** Paper §6.1: the inverse map [K^B_X : icones_hom → Skern]. *)
Local Definition icones_to_skern : Skern_hom Ar X Y :=
  MkSkernHom icones_to_skern_path icones_to_skern_norm_le1.

(** The image of the inverse equals [f]. *)
Lemma Skern_to_ICones_mor_to_skern :
  Skern_to_ICones_mor icones_to_skern = f.
Proof.
have HIK : int_to_linhom (linhom_to_int icones_to_linhom) = icones_to_linhom.
  exact: I_K_int_to_linhom_E.
apply: icones_hom_eq => µ /=.
have := f_equal
  (fun g : linhom_car _ _ _ => linhom_fun g µ) HIK.
by [].
Qed.

End SkernToIConesFull.

Arguments icones_to_skern {R Ar X Y}.
Arguments Skern_to_ICones_mor_to_skern {R Ar X Y}.

(** ** Paper Theorem 6.5 — full direction *)

Section SkernToIConesFullThm.
Variables (R : realType) (Ar : MeasSubcat R).
Variables X Y : ar_obj Ar.

(** Paper Theorem 6.5 — full direction. *)
Theorem Skern_to_ICones_full
    (f : icones_hom Ar (fmeas R (ar_carrier Ar X))
                       (fmeas R (ar_carrier Ar Y))) :
  exists κ : Skern_hom Ar X Y, Skern_to_ICones_mor κ = f.
Proof.
exists (icones_to_skern f); exact: Skern_to_ICones_mor_to_skern.
Qed.

End SkernToIConesFullThm.

Arguments Skern_to_ICones_full {R Ar X Y}.

(** ** Paper Theorem 6.5 — fully faithful

    Combining faithfulness and fullness. *)

Section SkernToIConesFullyFaithful.
Variables (R : realType) (Ar : MeasSubcat R).

(** Paper Theorem 6.5. *)
Theorem Skern_to_ICones_fully_faithful (X Y : ar_obj Ar) :
  (forall κ1 κ2 : Skern_hom Ar X Y,
     Skern_to_ICones_mor κ1 = Skern_to_ICones_mor κ2 -> κ1 = κ2) /\
  (forall f : icones_hom Ar (fmeas R (ar_carrier Ar X))
                            (fmeas R (ar_carrier Ar Y)),
     exists κ : Skern_hom Ar X Y, Skern_to_ICones_mor κ = f).
Proof.
by split; [exact: Skern_to_ICones_faithful | exact: Skern_to_ICones_full].
Qed.

End SkernToIConesFullyFaithful.

Arguments Skern_to_ICones_fully_faithful {R Ar} X Y.

(** ** Functoriality of [Klin] — paper §6.1

    [Klin] preserves identity and composition: [Klin(δ_X) = id] in
    [ICones] and [Klin(κ_2 ∘ κ_1) = Klin(κ_2) ∘ Klin(κ_1)]. Stated
    as supplementary facts, since fully faithful is the MVP. *)

Section SkernToIConesFunctoriality.
Variables (R : realType) (Ar : MeasSubcat R).

(** Paper §6.1: [Klin(δ_X) = id_{FMeas(X)}]. *)
Lemma Skern_to_ICones_mor_id (X : ar_obj Ar) :
  Skern_to_ICones_mor (Skern_id Ar X) =
  icones_id Ar (fmeas R (ar_carrier Ar X)).
Proof.
apply: icones_hom_eq => µ /=.
rewrite /int_to_linhom_fun /=.
have Heq := icone_integral_dirac_path (X:=X) µ.
rewrite /dirac_path /= in Heq.
by apply: (eq_trans _ Heq); congr (icone_integral _ _ _).
Qed.

(** Paper §6.1: [Klin(κ_2 ∘ κ_1) = Klin(κ_2) ∘ Klin(κ_1)]. *)
Lemma Skern_to_ICones_mor_comp
    (X Y Z : ar_obj Ar)
    (κ1 : Skern_hom Ar X Y) (κ2 : Skern_hom Ar Y Z) :
  Skern_to_ICones_mor (Skern_comp κ1 κ2) =
  icones_comp (Skern_to_ICones_mor κ2) (Skern_to_ICones_mor κ1).
Proof.
apply: icones_hom_eq => µ /=.
have Hpres :=
  int_to_linhom_fun_pres_int (skern_path κ2)
    (path_is_path (skern_path κ1)) µ.
rewrite /int_to_linhom_fun in Hpres |- *.
rewrite /Skern_comp_path /=.
symmetry.
apply: (eq_trans Hpres).
by congr (icone_integral _ _ _).
Qed.

End SkernToIConesFunctoriality.

(** ** Sanity checks — paper Thm 6.5 deliverables *)

Section MVPSanity.
Variables (R : realType) (Ar : MeasSubcat R).
Variables X Y : ar_obj Ar.

(** Functor on objects. *)
Check (@Skern_to_ICones_obj R Ar X : ICone.type Ar).

(** Functor on morphisms. *)
Check (fun κ : Skern_hom Ar X Y =>
         Skern_to_ICones_mor κ :
         icones_hom Ar (fmeas R (ar_carrier Ar X))
                       (fmeas R (ar_carrier Ar Y))).

(** Paper Thm 6.5 — faithful. *)
Check (Skern_to_ICones_faithful :
  forall κ1 κ2 : Skern_hom Ar X Y,
    Skern_to_ICones_mor κ1 = Skern_to_ICones_mor κ2 -> κ1 = κ2).

(** Paper Thm 6.5 — full. *)
Check (Skern_to_ICones_full :
  forall f : icones_hom Ar (fmeas R (ar_carrier Ar X))
                           (fmeas R (ar_carrier Ar Y)),
    exists κ : Skern_hom Ar X Y, Skern_to_ICones_mor κ = f).

(** Paper Thm 6.5 — fully faithful, the MVP. *)
Check (Skern_to_ICones_fully_faithful X Y).

End MVPSanity.
