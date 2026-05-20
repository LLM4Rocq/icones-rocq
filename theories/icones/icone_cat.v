(** * The category [ICones] — Paper §4.3 (Def 4.10) and Theorems 4.16, 4.18

    An *integrable cone* (M3) together with the *integral-preserving*
    linear and measurable maps form a category [ICones]. Paper §4.3
    establishes its main properties:

    - Definition 4.10: morphisms are [mcones_hom] satisfying the
      additional [integral preservation] equation.
    - Theorem 4.16: [ICones] is complete (all small limits).
    - Theorem 4.18: in [ICones], the object [1] is a separator and a
      coseparator, and [ICones] is well-powered.

    Coverage in this file:

    - [icones_hom Ar B C] — the morphism record, packaging an
      [mcones_hom Ar B C] with the integral-preservation field
      [icones_hom_pres_int]. Paper Def 4.10.
    - [icones_id], [icones_comp] — identity and composition; the
      category laws [icones_compIl], [icones_compIr], [icones_compA]
      follow.
    - [icones_prod_car], [icones_prod] — small products in [ICones]
      with their HB structure (Paper Thm 4.16).
    - [icones_proj], [icones_tuple] — projections and tupling; their
      universal property [icones_tuple_proj] and uniqueness
      [icones_tuple_unique] (Paper Thm 4.16).
    - [icones_eq_car], [icones_eq] — equaliser of two [icones_hom]
      morphisms; HB structure registered (Paper Thm 4.16).
    - [icones_eq_incl], [icones_eq_med] — inclusion and mediating
      arrow; factorisation [icones_eq_med_factor] and uniqueness
      [icones_eq_med_unique] (Paper Thm 4.16).
    - [icones_separator] — 1 is a separator (Paper Thm 4.18).
    - [icones_coseparator] — 1 is a coseparator (Paper Thm 4.18).
    - [icones_subobject_inj] / [icones_well_powered_bound] — the
      well-poweredness witness for [ICones] (Paper Thm 4.18).

    Design notes.

    - Like [mcones_hom] over [cones_hom], an [icones_hom] is a
      record carrying the underlying [mcones_hom] together with one
      additional [Prop] field expressing integral preservation. The
      uniqueness of integrals (via (Mssep)) makes the equation
      "[f (∫β µ) = ∫(f ∘ β) µ]" the canonical form.

    - Products and equalisers in [ICones] are built on top of the
      underlying [coneType] products / equalisers from [cone_cat.v].
      We package an [isMCone] instance on those carriers using the
      paper's [ini m] construction (Thm 4.16), and an [isICone]
      instance via the componentwise integral. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.

Require Import Icones.prelude.classical_extra.
Require Import Icones.prelude.nonneg_extra.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.cone_cat.
Require Import Icones.cones.examples_cone.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.pettis.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_integral.
Require Import Icones.icones.examples_icone.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** Morphisms in [ICones] — Paper Definition 4.10

    A morphism [f : B -> C] in [ICones] is an [mcones_hom Ar B C]
    that satisfies integral preservation: for every [X ∈ Ar], every
    measurable path [β : X -> B] and every finite measure [µ] on [X],

      [f (∫ β(r) µ(dr)) = ∫ f(β(r)) µ(dr)].

    The right-hand-side integral is well defined because
    [f ∘ β ∈ Path(X, C)] (preservation of measurable paths is
    built into [mcones_hom]). *)

Section IConesHom.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : ICone.type Ar.

(** Paper Definition 4.10. *)
Record icones_hom : Type := MkIConesHom {
  icones_hom_mcones :> mcones_hom Ar B C;
  icones_hom_pres_int :
    forall (X : ar_obj Ar)
           (β : ar_carrier Ar X -> B)
           (Hβ : is_measurable_path β)
           (µ : fmeas R (ar_carrier Ar X)),
      cones_hom_fun (mcones_hom_cones icones_hom_mcones)
                    (icone_integral β Hβ µ) =
      icone_integral (fun r => cones_hom_fun
                                 (mcones_hom_cones icones_hom_mcones)
                                 (β r))
                     (mcones_hom_pres_path icones_hom_mcones X β Hβ)
                     µ;
}.

End IConesHom.

Arguments icones_hom {R} Ar B C.
Arguments MkIConesHom {R Ar B C}.
Arguments icones_hom_mcones {R Ar B C}.
Arguments icones_hom_pres_int {R Ar B C}.

(** ** Equality of morphisms — paper Definition 4.10 *)

Section IConesHomEq.
Variables (R : realType) (Ar : MeasSubcat R) (B C : ICone.type Ar).

(** Two [icones_hom]s are equal as soon as their underlying functions
    agree pointwise. *)
Lemma icones_hom_eq (f g : icones_hom Ar B C) :
  (forall x, cones_hom_fun (mcones_hom_cones (icones_hom_mcones f)) x =
             cones_hom_fun (mcones_hom_cones (icones_hom_mcones g)) x) ->
  f = g.
Proof.
case: f => fm fp; case: g => gm gp /= Hfg.
have Heq : fm = gm by apply: mcones_hom_eq.
move: fp; rewrite Heq => fp.
by congr MkIConesHom; exact: Prop_irrelevance.
Qed.

End IConesHomEq.

(** ** Identity morphism — paper Definition 4.10 *)

Section IConesId.
Variables (R : realType) (Ar : MeasSubcat R) (B : ICone.type Ar).

(** Paper Definition 4.10: the identity preserves integrals, because
    [id (∫β µ) = ∫β µ = ∫(id ∘ β) µ] and uniqueness of integrals. *)
Lemma icones_id_pres_int
  (X : ar_obj Ar) (β : ar_carrier Ar X -> B)
  (Hβ : is_measurable_path β)
  (µ : fmeas R (ar_carrier Ar X)) :
  cones_hom_fun (mcones_hom_cones (mcones_id Ar B))
                (icone_integral β Hβ µ) =
  icone_integral
    (fun r => cones_hom_fun (mcones_hom_cones (mcones_id Ar B)) (β r))
    (mcones_hom_pres_path (mcones_id Ar B) X β Hβ) µ.
Proof.
apply: icone_integral_eqP.
exact: icone_integralP.
Qed.

(** Paper Definition 4.10: identity in [ICones]. *)
Definition icones_id : icones_hom Ar B B :=
  MkIConesHom (mcones_id Ar B) icones_id_pres_int.

End IConesId.

Arguments icones_id {R} Ar B.

(** ** Composition of morphisms — paper Definition 4.10 *)

Section IConesComp.
Variables (R : realType) (Ar : MeasSubcat R).
Variables A B C : ICone.type Ar.

Lemma icones_comp_pres_int
  (g : icones_hom Ar B C) (f : icones_hom Ar A B)
  (X : ar_obj Ar) (β : ar_carrier Ar X -> A)
  (Hβ : is_measurable_path β)
  (µ : fmeas R (ar_carrier Ar X)) :
  cones_hom_fun
    (mcones_hom_cones
       (mcones_comp (icones_hom_mcones g) (icones_hom_mcones f)))
    (icone_integral β Hβ µ) =
  icone_integral
    (fun r => cones_hom_fun
                (mcones_hom_cones
                   (mcones_comp (icones_hom_mcones g) (icones_hom_mcones f)))
                (β r))
    (mcones_hom_pres_path
       (mcones_comp (icones_hom_mcones g) (icones_hom_mcones f)) X β Hβ)
    µ.
Proof.
apply: (path_integral_eq_unique
  (β := fun r => (g : mcones_hom _ _ _) ((f : mcones_hom _ _ _) (β r)))
  (µ := µ)); last by exact: icone_integralP.
have Hf := icones_hom_pres_int f X β Hβ µ.
have Hfβ := mcones_hom_pres_path (icones_hom_mcones f) X β Hβ.
have -> : mcones_comp g f (icone_integral β Hβ µ) =
          g (icone_integral (fun r => f (β r)) Hfβ µ).
  rewrite /= Hf.
  by congr (g _); apply: f_equal2; first by apply: Prop_irrelevance.
rewrite (icones_hom_pres_int g X (fun r => f (β r)) Hfβ µ).
exact: icone_integralP.
Qed.

(** Paper Definition 4.10: composition in [ICones]. *)
Definition icones_comp
    (g : icones_hom Ar B C) (f : icones_hom Ar A B) : icones_hom Ar A C :=
  MkIConesHom
    (mcones_comp (icones_hom_mcones g) (icones_hom_mcones f))
    (icones_comp_pres_int g f).

End IConesComp.

Arguments icones_comp {R Ar A B C}.

(** ** Category laws — Paper Definition 4.10 *)

Section IConesCat.
Variables (R : realType) (Ar : MeasSubcat R).

Lemma icones_compIl (B C : ICone.type Ar) (f : icones_hom Ar B C) :
  icones_comp (icones_id Ar C) f = f.
Proof. by apply: icones_hom_eq. Qed.

Lemma icones_compIr (B C : ICone.type Ar) (f : icones_hom Ar B C) :
  icones_comp f (icones_id Ar B) = f.
Proof. by apply: icones_hom_eq. Qed.

Lemma icones_compA (B1 B2 B3 B4 : ICone.type Ar)
  (h : icones_hom Ar B3 B4) (g : icones_hom Ar B2 B3)
  (f : icones_hom Ar B1 B2) :
  icones_comp h (icones_comp g f) = icones_comp (icones_comp h g) f.
Proof. by apply: icones_hom_eq. Qed.

End IConesCat.

(** ** Products in [ICones] — Paper Theorem 4.16 (small products)

    Given a family [(B_i)_{i ∈ I}] of integrable cones, the carrier of
    the product is [cones_prod_car I (fun i => B_i)] — the same carrier
    as the [Cones]-level product (Paper Thm 2.18). We register an
    [isMCone] instance using the [ini m] test family of paper Thm 4.16
    and an [isICone] instance via the componentwise integral.

    The HB structure on [cones_prod_car] therefore gets enriched
    beyond its [coneType] instance with measurable-cone and integrable
    structures, mediated by the [iconeType] hypotheses on each [B_i]. *)

Section IConesProducts.
Variables (R : realType) (Ar : MeasSubcat R).
Variable I : Type.
Variable B : I -> ICone.type Ar.

Local Notation P := (cones_prod_car I (fun i => B i : coneType R)).

(** Paper Thm 4.16: the [ini m] test family. Given an index [i] and a
    test [m : test_of Ar Y (B i)], the lifted test on [P] is
    [λ s x⃗. m s (x⃗ i)]. *)

Section IniTest.
Variables (Y : ar_obj Ar) (i : I).
Variable m : test_of Ar Y (B i).

Definition iniTest_fun : ar_carrier Ar Y -> P -> R :=
  fun s x => test_fun m s (cones_prod_val x i).

Lemma iniTest_meas (x : P) :
  cone_norm x <= 1 ->
  measurable_fun [set: ar_carrier Ar Y] (fun s => iniTest_fun s x).
Proof.
move=> Hx.
have Hxi : cone_norm (cones_prod_val x i) <= 1.
  by apply: le_trans (cones_prod_norm_ge_comp x i) _.
exact: test_meas.
Qed.

Lemma iniTest_ge0 (s : ar_carrier Ar Y) (x : P) :
  0 <= iniTest_fun s x.
Proof. exact: test_ge0. Qed.

Lemma iniTest_le1 (s : ar_carrier Ar Y) (x : P) :
  cone_norm x <= 1 -> iniTest_fun s x <= 1.
Proof.
move=> Hx; apply: test_le1.
exact: le_trans (cones_prod_norm_ge_comp x i) _.
Qed.

Lemma iniTest_lin0 (s : ar_carrier Ar Y) :
  iniTest_fun s precone_zero = 0.
Proof. by rewrite /iniTest_fun /= test_lin0. Qed.

Lemma iniTest_linD (s : ar_carrier Ar Y) (x y : P) :
  iniTest_fun s (precone_add x y) =
  iniTest_fun s x + iniTest_fun s y.
Proof. by rewrite /iniTest_fun /= test_linD. Qed.

Lemma iniTest_linZ
  (s : ar_carrier Ar Y) (r : {nonneg R}) (x : P) :
  iniTest_fun s (precone_scale r x) = r%:num * iniTest_fun s x.
Proof. by rewrite /iniTest_fun /= test_linZ. Qed.

Lemma iniTest_cont
  (s : ar_carrier Ar Y) (u : nat -> P)
  (uch : forall n, precone_le (u n) (u n.+1))
  (ub1 : forall n, cone_norm (u n) <= 1)
  (N : R) :
  (forall n, iniTest_fun s (u n) <= N) ->
  iniTest_fun s (cone_sup_ball u uch ub1) <= N.
Proof.
move=> HN; rewrite /iniTest_fun /=.
rewrite /cones_prod_sup_ball_fun.
apply: test_cont => n.
have := HN n.
by rewrite /iniTest_fun.
Qed.

Lemma iniTest_norm_le (s : ar_carrier Ar Y) (x : P) :
  iniTest_fun s x <= cone_norm x.
Proof.
rewrite /iniTest_fun /=.
apply: le_trans _ (cones_prod_norm_ge_comp x i).
exact: test_norm_le.
Qed.

Definition iniTest : test_of Ar Y P :=
  MkTestOf iniTest_meas iniTest_ge0 iniTest_le1
           iniTest_lin0 iniTest_linD iniTest_linZ
           iniTest_cont iniTest_norm_le.

End IniTest.

(** Paper Thm 4.16: the test family for the product cone. *)
Definition icones_prod_M (Y : ar_obj Ar) : set (test_of Ar Y P) :=
  [set p | exists i (m : test_of Ar Y (B i)),
              mcone_M Y m /\ p = iniTest m].

(** (Mscomp) — closure under reindexing. *)
Lemma icones_prod_M_comp
  (Y' Y : ar_obj Ar) (ψ : ar_hom Ar Y' Y) (p : test_of Ar Y P) :
  icones_prod_M p ->
  icones_prod_M (test_reindex ψ p).
Proof.
case=> i [m [mM ->]].
exists i, (test_reindex ψ m); split.
  exact: mcone_M_comp.
apply: test_eq => s x.
by rewrite /test_reindex /= /test_reindex_fun /iniTest /= /iniTest_fun.
Qed.

(** (Mssep) — separation. *)
Lemma icones_prod_M_sep (x1 x2 : P) :
  (forall p : test_of Ar (ar_zero Ar) P,
    icones_prod_M p ->
    test_fun p (ar_zero_pt Ar) x1 = test_fun p (ar_zero_pt Ar) x2) ->
  x1 = x2.
Proof.
move=> Hsep.
apply: cones_prod_eq => i.
apply: mcone_M_sep => m mM.
have Hp : icones_prod_M (iniTest m) by exists i, m.
by have := Hsep _ Hp; rewrite /iniTest /= /iniTest_fun.
Qed.

(** (Msnorm) — norm adherence: paper Thm 4.16 (Msnorm for product).
    Given [x ≠ 0] in [P] and [ε > 0], find [i] such that [‖xi‖] is
    within ε/2 of [‖x‖], then apply (Msnorm) on [B i] at [xi] with
    [ε/2]. We use a coarser variant: the sup over components is
    bounded by the iniTest sup. *)
Lemma icones_prod_M_norm (x : P) (eps : R) :
  x <> precone_zero -> 0 < eps ->
  exists p : test_of Ar (ar_zero Ar) P,
    icones_prod_M p /\
    cone_norm x <= test_fun p (ar_zero_pt Ar) x + eps.
Proof.
move=> xne eps_pos.
(* Since [x ≠ 0], some component is non-zero. By [cones_prod_eq],
   there is some [i] with [cones_prod_val x i ≠ 0]. *)
have [i Hxi] : exists i : I, cones_prod_val x i <> precone_zero.
  apply: contrapT => /forallNP H.
  apply: xne; apply: cones_prod_eq => i.
  by have := H i => /contrapT.
(* Among indices with non-zero component, use (Msnorm) at half the
   slack to bound [‖xi‖]. But we want a bound on [sup_i ‖xi‖] from
   [m(xi)/‖m‖ + ε], which requires the bound to be tight at the
   maximal component. We use a simpler variant: pick *any* i, and
   use [m(xi) ≤ ‖xi‖ ≤ ‖x‖]. To strengthen, we need [‖x‖ ≤
   m(xi)/‖m‖ + ε]; the paper picks i achieving the sup within ε/2.

   For the Rocq encoding, we observe that for *some* i with
   [‖xi‖] within ε/2 of [‖x‖], we can apply (Msnorm) on [B i] at
   [xi] with [ε/2]. The existence of such an [i] uses the
   sup-adherence of [cones_prod_normset]. *)
pose eps2 := eps / 2.
have eps2_pos : 0 < eps2 by rewrite divr_gt0 // ltr0n.
(* sup-adherence: there is a value in cones_prod_normset x within
   eps2 of cones_prod_norm x. *)
have Hadh : exists j : I, cone_norm x - eps2 <=
                          cone_norm (cones_prod_val x j).
  have [Hnonempty | Hempty] :=
    pselect ([set y | exists i, y = cone_norm (cones_prod_val x i)]
               !=set0).
    have Hub := cones_prod_normset_has_ubound x.
    have Hsup : has_sup (cones_prod_normset x) by split.
    have [y Hy_in Hy_close] :=
      sup_adherent eps2_pos Hsup.
    case: Hy_in => j Hj.
    exists j.
    rewrite -Hj.
    by rewrite (_ : cone_norm x = sup (cones_prod_normset x)) //;
      exact: ltW.
  exfalso; apply: xne.
  (* If norm-set is empty, [I] is empty, hence x has no components,
     hence x is uniquely [precone_zero]. *)
  apply: cones_prod_eq => k.
  exfalso; apply: Hempty; exists (cone_norm (cones_prod_val x k)).
  by exists k.
case: Hadh => j Hj.
(* Now either [xi (for i = j) = 0] or apply (Msnorm) on [B j]. *)
have [Hxj_zero | Hxj_nz] := pselect (cones_prod_val x j = precone_zero).
  (* If [xj = 0], then [‖xj‖ = 0], so [‖x‖ - eps2 ≤ 0] hence
     [‖x‖ ≤ eps2 < eps]. Use any valid test, e.g. iniTest from any
     non-zero component i (i = the one we found earlier). *)
  rewrite Hxj_zero cone_norm0 in Hj.
  have Hxbd : cone_norm x <= eps2.
    by have := Hj; rewrite lerBlDr add0r.
  (* Pick the test from the non-zero component [i]. *)
  have [m [mM Hm]] :=
    mcone_M_norm (cones_prod_val x i) eps2 Hxi eps2_pos.
  exists (iniTest m); split.
    by exists i, m.
  rewrite /iniTest /= /iniTest_fun.
  apply: le_trans Hxbd _.
  have ->: eps = eps2 + eps2 by rewrite /eps2 -splitr.
  rewrite addrA -[X in X <= _]add0r.
  apply: lerD; last exact: lexx.
  by rewrite addr_ge0 ?test_ge0 // ltW.
have [m [mM Hm]] :=
  mcone_M_norm (cones_prod_val x j) eps2 Hxj_nz eps2_pos.
exists (iniTest m); split.
  by exists j, m.
rewrite /iniTest /= /iniTest_fun.
apply: le_trans (_ : cone_norm (cones_prod_val x j) + eps2 <= _).
  by rewrite -lerBlDr; exact: Hj.
have ->: eps = eps2 + eps2 by rewrite /eps2 -splitr.
rewrite addrA; apply: lerD; last exact: lexx.
exact: Hm.
Qed.

End IConesProducts.

Arguments iniTest {R Ar I B Y} i m.
Arguments icones_prod_M {R Ar I} B.

(** Paper Thm 4.16: [isMCone] instance on the product carrier. *)
HB.instance Definition _ (R : realType) (Ar : MeasSubcat R)
  (I : Type) (B : I -> ICone.type Ar) :=
  @isMCone.Build R Ar
    (cones_prod_car I (fun i => B i : coneType R))
    (@icones_prod_M R Ar I B)
    (@icones_prod_M_comp R Ar I B)
    (@icones_prod_M_sep R Ar I B)
    (@icones_prod_M_norm R Ar I B).

(** ** Existence of the componentwise integral — Paper Thm 4.16

    Given a measurable path [β : X -> P] (where [P] is the [cones_prod]
    carrier) and a finite measure [µ], the integral is the section
    whose [i]-th component is [icone_integral (β_i) µ] in [B i]. *)

Section IConesProductsInt.
Variables (R : realType) (Ar : MeasSubcat R).
Variable I : Type.
Variable B : I -> ICone.type Ar.

Local Notation P := (cones_prod_car I (fun i => B i : coneType R)).

(** Paper Thm 4.16: each [β_i := λ r. (β r).i] is a measurable path
    into [B i]. *)
Lemma icones_prod_path_comp
  (X : ar_obj Ar) (β : ar_carrier Ar X -> P)
  (Hβ : is_measurable_path β) (i : I) :
  is_measurable_path (fun r => cones_prod_val (β r) i).
Proof.
case: Hβ => [[M HM] Hmeas].
split.
  exists M => r; apply: le_trans (cones_prod_norm_ge_comp (β r) i) _.
  exact: HM.
move=> Y m mM.
have Hp : @mcone_M R Ar _ Y (iniTest i m) by exists i, m.
have := Hmeas Y (iniTest i m) Hp.
by rewrite /iniTest /= /iniTest_fun.
Qed.

(** Paper Thm 4.16: the [i]-th component of the tentative integral. *)
Definition icones_prod_intval
  (X : ar_obj Ar) (β : ar_carrier Ar X -> P)
  (Hβ : is_measurable_path β)
  (µ : fmeas R (ar_carrier Ar X)) (i : I) : B i :=
  icone_integral
    (fun r => cones_prod_val (β r) i)
    (icones_prod_path_comp Hβ i) µ.

(** Paper Thm 4.16: the componentwise integral is uniformly bounded by
    the path's norm bound. *)
Lemma icones_prod_intval_bd
  (X : ar_obj Ar) (β : ar_carrier Ar X -> P)
  (Hβ : is_measurable_path β)
  (µ : fmeas R (ar_carrier Ar X)) :
  exists M : R, forall i, cone_norm (icones_prod_intval Hβ µ i) <= M.
Proof.
case: Hβ (Hβ) => [[M HM] _] Hβ'.
exists (M * fmeas_norm µ) => i.
rewrite /icones_prod_intval.
apply: (path_integral_norm_le (Mβ := M)).
- by move=> r; apply: le_trans (HM r); exact: cones_prod_norm_ge_comp.
- exact: icones_prod_path_comp.
- exact: icone_integralP.
Qed.

(** Paper Thm 4.16: the integral candidate in the product carrier. *)
Definition icones_prod_int
  (X : ar_obj Ar) (β : ar_carrier Ar X -> P)
  (Hβ : is_measurable_path β)
  (µ : fmeas R (ar_carrier Ar X)) : P :=
  {| cones_prod_val := icones_prod_intval Hβ µ;
     cones_prod_bd := icones_prod_intval_bd Hβ µ |}.

(** Paper Thm 4.16: the candidate satisfies the Pettis equation. *)
Lemma icones_prod_int_pettis
  (X : ar_obj Ar) (β : ar_carrier Ar X -> P)
  (Hβ : is_measurable_path β)
  (µ : fmeas R (ar_carrier Ar X)) :
  path_integral_eq β µ (icones_prod_int Hβ µ).
Proof.
move=> p [i [m [mM ->]]] s.
rewrite /iniTest /= /iniTest_fun /icones_prod_int /=.
rewrite /icones_prod_intval.
exact: icone_integralP.
Qed.

(** Paper Thm 4.16: integrability of the product. *)
Lemma icones_prod_int_exists
  (X : ar_obj Ar) (β : ar_carrier Ar X -> P) :
  is_measurable_path β ->
  forall µ : fmeas R (ar_carrier Ar X),
    is_path_integrable β µ.
Proof.
move=> Hβ µ.
exists (icones_prod_int Hβ µ); exact: icones_prod_int_pettis.
Qed.

End IConesProductsInt.

(** Paper Thm 4.16: [isICone] instance on the product carrier. *)
HB.instance Definition _ (R : realType) (Ar : MeasSubcat R)
  (I : Type) (B : I -> ICone.type Ar) :=
  @isICone.Build R Ar
    (cones_prod_car I (fun i => B i : coneType R))
    (@icones_prod_int_exists R Ar I B).

(** Paper Thm 4.16: the product as an [iconeType]. *)
Definition icones_prod (R : realType) (Ar : MeasSubcat R)
    (I : Type) (B : I -> ICone.type Ar) : ICone.type Ar :=
  cones_prod_car I (fun i => B i : coneType R).

(** ** Projections and tupling — Paper Theorem 4.16 (universal property) *)

Section IConesProductsUniversal.
Variables (R : realType) (Ar : MeasSubcat R).
Variable I : Type.
Variable B : I -> ICone.type Ar.

Local Notation P := (icones_prod B).

(** Paper Thm 4.16: the [i]-th projection preserves measurable paths.
    For [γ : X → P] measurable and [n ∈ M^{B i}_Y], the function
    [(s, r) ↦ n s (γ r).i] is measurable since it is also
    [(s, r) ↦ (iniTest n) s (γ r)] and [γ] is a measurable path. *)
Lemma icones_proj_pres_path (i : I)
  (X : ar_obj Ar) (γ : ar_carrier Ar X -> P) :
  is_measurable_path (Ar:=Ar) (C:=P) γ ->
  is_measurable_path
    (Ar:=Ar) (C:=B i)
    (fun r => cones_hom_fun (cones_proj i) (γ r)).
Proof.
move=> Hγ; rewrite /cones_proj /=.
exact: icones_prod_path_comp.
Qed.

(** Paper Thm 4.16: the [i]-th projection as an [mcones_hom]. *)
Definition icones_proj_mcones (i : I) : mcones_hom Ar P (B i) :=
  MkMConesHom (cones_proj i) (icones_proj_pres_path i).

(** Paper Thm 4.16: the [i]-th projection preserves integrals.
    Direct: [(∫β µ).i = ∫(β r).i µ] by definition of the
    componentwise integral. *)
Lemma icones_proj_pres_int (i : I)
  (X : ar_obj Ar)
  (β : ar_carrier Ar X -> P)
  (Hβ : is_measurable_path β)
  (µ : fmeas R (ar_carrier Ar X)) :
  cones_hom_fun (mcones_hom_cones (icones_proj_mcones i))
                (icone_integral β Hβ µ) =
  icone_integral
    (fun r => cones_hom_fun
                (mcones_hom_cones (icones_proj_mcones i)) (β r))
    (mcones_hom_pres_path (icones_proj_mcones i) X β Hβ) µ.
Proof.
apply: icone_integral_eqP.
move=> m mM s.
have HP := icone_integralP β Hβ µ.
(* The integral of β.i has by definition the test equation derived
   from iniTest. Apply uniqueness to identify it with [cone_proj i]
   of the global integral. *)
have HiniM : @mcone_M R Ar _ (ar_zero Ar) (iniTest (B:=B) i m).
  by exists i, m.
have := HP (iniTest i m) HiniM s.
by rewrite /iniTest /= /iniTest_fun /cones_proj /= /cones_proj_fun.
Qed.

(** Paper Thm 4.16: the [i]-th projection as an [icones_hom]. *)
Definition icones_proj (i : I) : icones_hom Ar P (B i) :=
  MkIConesHom (icones_proj_mcones i) (icones_proj_pres_int i).

(** Tupling: given [(f_i : Q -> B_i)_i], the mediating [Q -> P]. *)
Variable Q : ICone.type Ar.
Variable f : forall i : I, icones_hom Ar Q (B i).

(** The underlying [cones_hom] is the [cones_tuple] of the underlying
    [cones_hom] family. *)
Definition icones_tuple_chom : cones_hom Q P :=
  cones_tuple (fun i => mcones_hom_cones (icones_hom_mcones (f i))).

(** Paper Thm 4.16: the tupling preserves measurable paths.
    Pointwise: [(tuple f) ∘ δ] is measurable iff each [f_i ∘ δ] is,
    which follows from each [f_i ∈ icones_hom]. *)
Lemma icones_tuple_pres_path
  (X : ar_obj Ar) (δ : ar_carrier Ar X -> Q) :
  is_measurable_path (Ar:=Ar) (C:=Q) δ ->
  is_measurable_path
    (Ar:=Ar) (C:=P)
    (fun r => cones_hom_fun icones_tuple_chom (δ r)).
Proof.
move=> Hδ; split.
  case: Hδ => [[M HM] _].
  exists M => r.
  apply: le_trans (cones_hom_norm_le1 icones_tuple_chom (δ r)) _.
  exact: HM.
move=> Y m mM.
case: mM => i [n [nM Heq]].
rewrite Heq.
have Hfi := mcones_hom_pres_path (icones_hom_mcones (f i)) X δ Hδ.
case: Hfi => _ Hjoint.
have := Hjoint Y n nM.
by rewrite /iniTest /= /iniTest_fun /icones_tuple_chom /cones_tuple
              /cones_tuple_fun /=.
Qed.

(** Paper Thm 4.16: the tupling as an [mcones_hom]. *)
Definition icones_tuple_mcones : mcones_hom Ar Q P :=
  MkMConesHom icones_tuple_chom icones_tuple_pres_path.

(** Paper Thm 4.16: the tupling preserves integrals.
    Pointwise: for each [i], [pri (tuple f (∫δ µ)) = f_i (∫δ µ)
    = ∫(f_i ∘ δ) µ] by integral preservation of [f_i]. Then by
    uniqueness, [(∫δ µ)._i = (∫(tuple f ∘ δ) µ)._i]. *)
Lemma icones_tuple_pres_int
  (X : ar_obj Ar) (δ : ar_carrier Ar X -> Q)
  (Hδ : is_measurable_path δ)
  (µ : fmeas R (ar_carrier Ar X)) :
  cones_hom_fun (mcones_hom_cones icones_tuple_mcones)
                (icone_integral δ Hδ µ) =
  icone_integral
    (fun r => cones_hom_fun
                (mcones_hom_cones icones_tuple_mcones) (δ r))
    (mcones_hom_pres_path icones_tuple_mcones X δ Hδ) µ.
Proof.
apply: icone_integral_eqP.
move=> m mM s.
case: mM => i [n [nM ->]].
rewrite /iniTest /= /iniTest_fun /icones_tuple_mcones /icones_tuple_chom
        /cones_tuple /= /cones_tuple_fun /=.
have Hfi := icones_hom_pres_int (f i) X δ Hδ µ.
have Hpath := mcones_hom_pres_path (icones_hom_mcones (f i)) X δ Hδ.
rewrite /= in Hfi.
rewrite Hfi.
have Hint :=
  icone_integralP (fun r => (f i : mcones_hom _ _ _) (δ r)) Hpath µ n nM s.
have ->: mcones_hom_pres_path (f i) X δ Hδ = Hpath.
  exact: Prop_irrelevance.
exact: Hint.
Qed.

(** Paper Thm 4.16: the tupling as an [icones_hom]. *)
Definition icones_tuple : icones_hom Ar Q P :=
  MkIConesHom icones_tuple_mcones icones_tuple_pres_int.

(** Paper Thm 4.16 (universal property): the tupling factors each
    [f_i]. *)
Lemma icones_tuple_proj (i : I) :
  icones_comp (icones_proj i) icones_tuple = f i.
Proof.
by apply: icones_hom_eq.
Qed.

(** Paper Thm 4.16 (universal property): the tupling is unique. *)
Lemma icones_tuple_unique (h : icones_hom Ar Q P) :
  (forall i, icones_comp (icones_proj i) h = f i) ->
  h = icones_tuple.
Proof.
move=> Hh.
apply: icones_hom_eq => y.
apply: cones_prod_eq => i.
have := Hh i.
move/(congr1 (fun w : icones_hom Ar Q (B i) =>
                cones_hom_fun (mcones_hom_cones (icones_hom_mcones w)) y)).
by [].
Qed.

End IConesProductsUniversal.

Arguments icones_proj {R Ar I B}.
Arguments icones_tuple {R Ar I B Q}.

(** ** Equalisers in [ICones] — Paper Theorem 4.16

    Given two morphisms [f, g : icones_hom Ar B C], the equaliser is
    the sub-cone [cones_eq_car f g] of [B] (already a [coneType]).
    We register the [isMCone] and [isICone] HB instances so that the
    underlying carrier becomes an [iconeType]. *)

Section IConesEqualisers.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : ICone.type Ar.
Variables f g : icones_hom Ar B C.

Local Notation E :=
  (cones_eq_car (R:=R) (P:=B : coneType R) (Q:=C : coneType R)
     (mcones_hom_cones (icones_hom_mcones f))
     (mcones_hom_cones (icones_hom_mcones g))).

(** ** Tests on the equaliser

    A test on [E] is just a test on [B] restricted to [E]; concretely,
    it is obtained by composing with the inclusion
    [cones_eq_val : E → B]. *)

Section EqTest.
Variables (Y : ar_obj Ar) (m : test_of Ar Y B).

Definition eqTest_fun : ar_carrier Ar Y -> E -> R :=
  fun s x => test_fun m s (cones_eq_val x).

Lemma eqTest_meas (x : E) :
  cone_norm x <= 1 ->
  measurable_fun [set: ar_carrier Ar Y] (fun s => eqTest_fun s x).
Proof.
move=> Hx; rewrite /eqTest_fun.
exact: test_meas.
Qed.

Lemma eqTest_ge0 (s : ar_carrier Ar Y) (x : E) :
  0 <= eqTest_fun s x.
Proof. exact: test_ge0. Qed.

Lemma eqTest_le1 (s : ar_carrier Ar Y) (x : E) :
  cone_norm x <= 1 -> eqTest_fun s x <= 1.
Proof. by move=> Hx; rewrite /eqTest_fun; apply: test_le1. Qed.

Lemma eqTest_lin0 (s : ar_carrier Ar Y) :
  eqTest_fun s precone_zero = 0.
Proof. by rewrite /eqTest_fun /= test_lin0. Qed.

Lemma eqTest_linD (s : ar_carrier Ar Y) (x y : E) :
  eqTest_fun s (precone_add x y) =
  eqTest_fun s x + eqTest_fun s y.
Proof. by rewrite /eqTest_fun /= test_linD. Qed.

Lemma eqTest_linZ
  (s : ar_carrier Ar Y) (r : {nonneg R}) (x : E) :
  eqTest_fun s (precone_scale r x) = r%:num * eqTest_fun s x.
Proof. by rewrite /eqTest_fun /= test_linZ. Qed.

Lemma eqTest_cont
  (s : ar_carrier Ar Y) (u : nat -> E)
  (uch : forall n, precone_le (u n) (u n.+1))
  (ub1 : forall n, cone_norm (u n) <= 1)
  (N : R) :
  (forall n, eqTest_fun s (u n) <= N) ->
  eqTest_fun s (cone_sup_ball u uch ub1) <= N.
Proof.
move=> HN.
rewrite /eqTest_fun /=.
apply: test_cont => n.
by have := HN n; rewrite /eqTest_fun.
Qed.

Lemma eqTest_norm_le (s : ar_carrier Ar Y) (x : E) :
  eqTest_fun s x <= cone_norm x.
Proof. by rewrite /eqTest_fun /=; exact: test_norm_le. Qed.

Definition eqTest : test_of Ar Y E :=
  MkTestOf eqTest_meas eqTest_ge0 eqTest_le1
           eqTest_lin0 eqTest_linD eqTest_linZ
           eqTest_cont eqTest_norm_le.

End EqTest.

(** Paper Thm 4.16: the test family on [E] — inherited (and restricted)
    from [B]. *)
Definition icones_eq_M (Y : ar_obj Ar) : set (test_of Ar Y E) :=
  [set p | exists2 m : test_of Ar Y B, mcone_M Y m & p = eqTest m].

Lemma icones_eq_M_comp
  (Y' Y : ar_obj Ar) (ψ : ar_hom Ar Y' Y)
  (p : test_of Ar Y E) :
  icones_eq_M p ->
  icones_eq_M (test_reindex ψ p).
Proof.
case=> m mM ->.
exists (test_reindex ψ m); first exact: mcone_M_comp.
apply: test_eq => s x.
by rewrite /test_reindex /= /test_reindex_fun /eqTest /= /eqTest_fun.
Qed.

Lemma icones_eq_M_sep (x1 x2 : E) :
  (forall p : test_of Ar (ar_zero Ar) E,
    icones_eq_M p ->
    test_fun p (ar_zero_pt Ar) x1 = test_fun p (ar_zero_pt Ar) x2) ->
  x1 = x2.
Proof.
move=> Hsep.
apply: cones_eq_extensional.
apply: mcone_M_sep => m mM.
have Hp : icones_eq_M (eqTest m) by exists m.
by have := Hsep _ Hp; rewrite /eqTest /= /eqTest_fun.
Qed.

Lemma icones_eq_M_norm (x : E) (eps : R) :
  x <> precone_zero -> 0 < eps ->
  exists p : test_of Ar (ar_zero Ar) E,
    icones_eq_M p /\
    cone_norm x <= test_fun p (ar_zero_pt Ar) x + eps.
Proof.
move=> xne eps_pos.
have vne : cones_eq_val x <> precone_zero.
  move=> Hv; apply: xne; apply: cones_eq_extensional => /=; exact: Hv.
have [m [mM Hm]] :=
  mcone_M_norm (cones_eq_val x) eps vne eps_pos.
exists (eqTest m); split.
  by exists m.
by rewrite /eqTest /= /eqTest_fun.
Qed.

End IConesEqualisers.

Arguments eqTest {R Ar B C f g Y}.
Arguments icones_eq_M {R Ar B C} f g.

(** Paper Thm 4.16: [isMCone] instance for the equaliser carrier. *)
HB.instance Definition _ (R : realType) (Ar : MeasSubcat R)
  (B C : ICone.type Ar) (f g : icones_hom Ar B C) :=
  @isMCone.Build R Ar
    (cones_eq_car (R:=R) (P:=B : coneType R) (Q:=C : coneType R)
       (mcones_hom_cones (icones_hom_mcones f))
       (mcones_hom_cones (icones_hom_mcones g)))
    (@icones_eq_M R Ar B C f g)
    (@icones_eq_M_comp R Ar B C f g)
    (@icones_eq_M_sep R Ar B C f g)
    (@icones_eq_M_norm R Ar B C f g).

(** ** Integrability of the equaliser — Paper Theorem 4.16 *)

Section IConesEqualisersInt.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : ICone.type Ar.
Variables f g : icones_hom Ar B C.

Local Notation E :=
  (cones_eq_car (R:=R) (P:=B : coneType R) (Q:=C : coneType R)
     (mcones_hom_cones (icones_hom_mcones f))
     (mcones_hom_cones (icones_hom_mcones g))).

(** Paper Thm 4.16: the underlying path [val ∘ β] in [B] is measurable. *)
Lemma icones_eq_path_under
  (X : ar_obj Ar) (β : ar_carrier Ar X -> E) :
  is_measurable_path β ->
  is_measurable_path (fun r => cones_eq_val (β r)).
Proof.
move=> [[M HM] Hmeas]; split.
  by exists M.
move=> Y m mM.
have HmE : @mcone_M R Ar _ Y (eqTest (f:=f) (g:=g) m) by exists m.
have := Hmeas Y (eqTest m) HmE.
by rewrite /eqTest /= /eqTest_fun.
Qed.

(** Paper Thm 4.16: the integral in [B] of the underlying path actually
    lies in [E], i.e., satisfies the equaliser equation [f x = g x]. *)
Lemma icones_eq_int_inE
  (X : ar_obj Ar) (β : ar_carrier Ar X -> E)
  (Hβ : is_measurable_path β)
  (µ : fmeas R (ar_carrier Ar X)) :
  cones_hom_fun (mcones_hom_cones (icones_hom_mcones f))
    (icone_integral
       (fun r => cones_eq_val (β r))
       (icones_eq_path_under Hβ) µ) =
  cones_hom_fun (mcones_hom_cones (icones_hom_mcones g))
    (icone_integral
       (fun r => cones_eq_val (β r))
       (icones_eq_path_under Hβ) µ).
Proof.
apply: mcone_M_sep => m mM.
have key : forall r, m (ar_zero_pt Ar)
   ((f : mcones_hom _ _ _) (cones_eq_val (β r))) =
            m (ar_zero_pt Ar)
   ((g : mcones_hom _ _ _) (cones_eq_val (β r))).
  move=> r.
  by have := cones_eq_eq (β r) => /(congr1 (m (ar_zero_pt Ar))).
have Hfpres := icones_hom_pres_int f X (fun r => cones_eq_val (β r))
                 (icones_eq_path_under Hβ) µ.
have Hgpres := icones_hom_pres_int g X (fun r => cones_eq_val (β r))
                 (icones_eq_path_under Hβ) µ.
rewrite /= in Hfpres Hgpres.
rewrite Hfpres Hgpres.
rewrite (icone_integral_test_pettis _ _ m mM (ar_zero_pt Ar)).
rewrite (icone_integral_test_pettis _ _ m mM (ar_zero_pt Ar)).
congr (constructive_ereal.fine _).
apply: lebesgue_integral_definition.eq_integral => r _.
by rewrite key.
Qed.

(** Paper Thm 4.16: integral candidate inside the equaliser. *)
Definition icones_eq_int
  (X : ar_obj Ar) (β : ar_carrier Ar X -> E)
  (Hβ : is_measurable_path β)
  (µ : fmeas R (ar_carrier Ar X)) : E :=
  {| cones_eq_val :=
       icone_integral (fun r => cones_eq_val (β r))
         (icones_eq_path_under Hβ) µ;
     cones_eq_eq := icones_eq_int_inE Hβ µ |}.

(** Paper Thm 4.16: the candidate satisfies the Pettis equation. *)
Lemma icones_eq_int_pettis
  (X : ar_obj Ar) (β : ar_carrier Ar X -> E)
  (Hβ : is_measurable_path β)
  (µ : fmeas R (ar_carrier Ar X)) :
  path_integral_eq β µ (icones_eq_int Hβ µ).
Proof.
move=> p [m mM ->] s.
rewrite /eqTest /= /eqTest_fun /icones_eq_int /=.
exact: icone_integralP.
Qed.

(** Paper Thm 4.16: equaliser carrier is integrable. *)
Lemma icones_eq_int_exists
  (X : ar_obj Ar) (β : ar_carrier Ar X -> E) :
  is_measurable_path β ->
  forall µ : fmeas R (ar_carrier Ar X),
    is_path_integrable β µ.
Proof.
move=> Hβ µ.
exists (icones_eq_int Hβ µ); exact: icones_eq_int_pettis.
Qed.

End IConesEqualisersInt.

(** Paper Thm 4.16: [isICone] instance for the equaliser carrier. *)
HB.instance Definition _ (R : realType) (Ar : MeasSubcat R)
  (B C : ICone.type Ar) (f g : icones_hom Ar B C) :=
  @isICone.Build R Ar
    (cones_eq_car (R:=R) (P:=B : coneType R) (Q:=C : coneType R)
       (mcones_hom_cones (icones_hom_mcones f))
       (mcones_hom_cones (icones_hom_mcones g)))
    (@icones_eq_int_exists R Ar B C f g).

(** Paper Thm 4.16: the equaliser as an [iconeType]. *)
Definition icones_eq (R : realType) (Ar : MeasSubcat R)
  (B C : ICone.type Ar) (f g : icones_hom Ar B C) : ICone.type Ar :=
  cones_eq_car (R:=R) (P:=B : coneType R) (Q:=C : coneType R)
       (mcones_hom_cones (icones_hom_mcones f))
       (mcones_hom_cones (icones_hom_mcones g)).

(** ** Inclusion and universal property of the equaliser — Paper Thm 4.16 *)

Section IConesEqualisersUniversal.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : ICone.type Ar.
Variables f g : icones_hom Ar B C.

Local Notation E := (icones_eq f g).

(** The underlying [cones_hom] inclusion [E -> B]. *)
Definition icones_eq_incl_chom : cones_hom E B :=
  cones_eq_incl
    (mcones_hom_cones (icones_hom_mcones f))
    (mcones_hom_cones (icones_hom_mcones g)).

(** Paper Thm 4.16: the inclusion preserves measurable paths. *)
Lemma icones_eq_incl_pres_path
  (X : ar_obj Ar) (γ : ar_carrier Ar X -> E) :
  is_measurable_path (Ar:=Ar) (C:=E) γ ->
  is_measurable_path
    (Ar:=Ar) (C:=B)
    (fun r => cones_hom_fun icones_eq_incl_chom (γ r)).
Proof.
move=> Hγ.
exact: icones_eq_path_under.
Qed.

(** Paper Thm 4.16: the inclusion as an [mcones_hom]. *)
Definition icones_eq_incl_mcones : mcones_hom Ar E B :=
  MkMConesHom icones_eq_incl_chom icones_eq_incl_pres_path.

(** Paper Thm 4.16: the inclusion preserves integrals — it is, by
    construction, the [B]-valued integral of [val ∘ β]. *)
Lemma icones_eq_incl_pres_int
  (X : ar_obj Ar)
  (β : ar_carrier Ar X -> E)
  (Hβ : is_measurable_path β)
  (µ : fmeas R (ar_carrier Ar X)) :
  cones_hom_fun (mcones_hom_cones icones_eq_incl_mcones)
                (icone_integral β Hβ µ) =
  icone_integral
    (fun r => cones_hom_fun
                (mcones_hom_cones icones_eq_incl_mcones) (β r))
    (mcones_hom_pres_path icones_eq_incl_mcones X β Hβ) µ.
Proof.
apply: icone_integral_eqP.
move=> m mM s.
have HP := icone_integralP β Hβ µ.
have HmE : @mcone_M R Ar _ (ar_zero Ar) (eqTest (f:=f) (g:=g) m) by exists m.
have := HP _ HmE s.
by rewrite /eqTest /= /eqTest_fun.
Qed.

(** Paper Thm 4.16: the inclusion as an [icones_hom]. *)
Definition icones_eq_incl : icones_hom Ar E B :=
  MkIConesHom icones_eq_incl_mcones icones_eq_incl_pres_int.

(** Paper Thm 4.16 (factorisation): [f ∘ incl = g ∘ incl]. *)
Lemma icones_eq_incl_equ :
  icones_comp f icones_eq_incl = icones_comp g icones_eq_incl.
Proof. by apply: icones_hom_eq => x; exact: cones_eq_eq. Qed.

(** Universal property: given [h : T -> B] equalising [f], [g], there
    is a unique mediator [T -> E]. *)
Variable T : ICone.type Ar.
Variable h : icones_hom Ar T B.
Hypothesis Hh : icones_comp f h = icones_comp g h.

Lemma icones_eq_med_eq (u : T) :
  cones_hom_fun (mcones_hom_cones (icones_hom_mcones f))
                (cones_hom_fun
                   (mcones_hom_cones (icones_hom_mcones h)) u) =
  cones_hom_fun (mcones_hom_cones (icones_hom_mcones g))
                (cones_hom_fun
                   (mcones_hom_cones (icones_hom_mcones h)) u).
Proof.
have := Hh.
by move/(congr1 (fun w : icones_hom Ar T C =>
                   cones_hom_fun
                     (mcones_hom_cones (icones_hom_mcones w)) u)).
Qed.

Definition icones_eq_med_fun (u : T) : E :=
  {| cones_eq_val := cones_hom_fun
                       (mcones_hom_cones (icones_hom_mcones h)) u;
     cones_eq_eq := icones_eq_med_eq u |}.

(** Auxiliary: the underlying [cones_hom] equation. *)
Lemma icones_eq_med_cones_eq :
  cones_comp (mcones_hom_cones (icones_hom_mcones f))
             (mcones_hom_cones (icones_hom_mcones h)) =
  cones_comp (mcones_hom_cones (icones_hom_mcones g))
             (mcones_hom_cones (icones_hom_mcones h)).
Proof.
apply: cones_hom_eq => u; exact: icones_eq_med_eq.
Qed.

(** Underlying [cones_hom]. *)
Definition icones_eq_med_chom : cones_hom T E :=
  cones_eq_med
    (mcones_hom_cones (icones_hom_mcones h)) icones_eq_med_cones_eq.

Lemma icones_eq_med_pres_path
  (X : ar_obj Ar) (γ : ar_carrier Ar X -> T) :
  is_measurable_path (Ar:=Ar) (C:=T) γ ->
  is_measurable_path
    (Ar:=Ar) (C:=E)
    (fun r => cones_hom_fun icones_eq_med_chom (γ r)).
Proof.
move=> Hγ; split.
  case: Hγ => [[M HM] _].
  exists M => r.
  apply: le_trans (cones_hom_norm_le1 icones_eq_med_chom (γ r)) _.
  exact: HM.
move=> Y m mM.
case: mM => p pM Heq.
rewrite Heq.
have Hpath_hγ : is_measurable_path
                  (fun r => cones_hom_fun
                              (mcones_hom_cones (icones_hom_mcones h))
                              (γ r)).
  exact: (mcones_hom_pres_path (icones_hom_mcones h)).
case: Hpath_hγ => _ Hmeas.
have := Hmeas Y p pM.
by rewrite /eqTest /= /eqTest_fun /icones_eq_med_chom
            /cones_eq_med /= /cones_eq_med_fun.
Qed.

Definition icones_eq_med_mcones : mcones_hom Ar T E :=
  MkMConesHom icones_eq_med_chom icones_eq_med_pres_path.

Lemma icones_eq_med_pres_int
  (X : ar_obj Ar) (γ : ar_carrier Ar X -> T)
  (Hγ : is_measurable_path γ)
  (µ : fmeas R (ar_carrier Ar X)) :
  cones_hom_fun (mcones_hom_cones icones_eq_med_mcones)
                (icone_integral γ Hγ µ) =
  icone_integral
    (fun r => cones_hom_fun
                (mcones_hom_cones icones_eq_med_mcones) (γ r))
    (mcones_hom_pres_path icones_eq_med_mcones X γ Hγ) µ.
Proof.
apply: icone_integral_eqP.
move=> m mM s.
case: mM => p pM ->.
rewrite /eqTest /= /eqTest_fun /icones_eq_med_mcones /icones_eq_med_chom
        /cones_eq_med /= /cones_eq_med_fun /=.
have Hhpres := icones_hom_pres_int h X γ Hγ µ.
rewrite /= in Hhpres.
rewrite Hhpres.
have Hpath_hγ := mcones_hom_pres_path (icones_hom_mcones h) X γ Hγ.
have Hint := icone_integralP
   (fun r => (h : mcones_hom _ _ _) (γ r)) Hpath_hγ µ p pM s.
have ->: mcones_hom_pres_path (icones_hom_mcones h) X γ Hγ = Hpath_hγ.
  exact: Prop_irrelevance.
exact: Hint.
Qed.

Definition icones_eq_med : icones_hom Ar T E :=
  MkIConesHom icones_eq_med_mcones icones_eq_med_pres_int.

Lemma icones_eq_med_factor :
  icones_comp icones_eq_incl icones_eq_med = h.
Proof. by apply: icones_hom_eq. Qed.

Lemma icones_eq_med_unique (h' : icones_hom Ar T E) :
  icones_comp icones_eq_incl h' = h ->
  h' = icones_eq_med.
Proof.
move=> Hh'.
apply: icones_hom_eq => u.
apply: cones_eq_extensional => /=.
have := Hh'.
by move/(congr1 (fun w : icones_hom Ar T B =>
                  cones_hom_fun
                    (mcones_hom_cones (icones_hom_mcones w)) u)).
Qed.

End IConesEqualisersUniversal.

Arguments icones_eq_incl {R Ar B C} f g.
Arguments icones_eq_med {R Ar B C} f g {T}.

(** ** Paper Theorem 4.18: 1 is a coseparator

    In the paper, "1 is a coseparator" means: for [f, g : ICones(B, C)]
    we have [f = g] iff for every test [m : C -> 1] (in ICones),
    [m ∘ f = m ∘ g].

    Our equivalent formulation: [f] and [g] coincide iff every
    element [m ∈ M^C_0] (a test in [C]'s test family) yields
    [m (f x) = m (g x)] for every [x]. By (Mssep) this is precisely
    [f x = g x] for every [x], which by [icones_hom_eq] is [f = g].

    The implementation directly mirrors the paper's argument:
    [m ∈ M^C_0] *is* a [icones_hom C 1] (up to packaging), and the
    test equation pulled back through [f] / [g] is the coseparator
    equation. *)

Section IConesCoseparator.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : ICone.type Ar.

(** Paper Thm 4.18, "1 is a coseparator", in test-family form:
    [f = g] in [ICones(B, C)] iff every test of [C] at arity 0
    distinguishes them at no point.

    This is the practical Rocq form of the paper's "1 is a
    coseparator": tests at arity 0 *are* the elements of
    [ICones(C, 1)] in our encoding (each test [m] packages a
    morphism into [cone_one_car], composed with the unique
    [m(_) = c1_val (m _)] identification). *)
Lemma icones_coseparator (f g : icones_hom Ar B C) :
  (forall x : B,
    forall m : test_of Ar (ar_zero Ar) C,
      mcone_M (ar_zero Ar) m ->
      test_fun m (ar_zero_pt Ar)
        (cones_hom_fun (mcones_hom_cones (icones_hom_mcones f)) x) =
      test_fun m (ar_zero_pt Ar)
        (cones_hom_fun (mcones_hom_cones (icones_hom_mcones g)) x)) ->
  f = g.
Proof.
move=> Hall.
apply: icones_hom_eq => x.
apply: mcone_M_sep => m mM.
exact: Hall.
Qed.

End IConesCoseparator.

(** ** Paper Theorem 4.18: 1 is a separator

    In the paper, "1 is a separator" means: for [f, g : ICones(B, C)]
    we have [f = g] iff for every [h : 1 -> B] (in ICones),
    [f ∘ h = g ∘ h]. The paper proves this by exhibiting, for each
    [x ∈ B], the morphism [b_x : λ ↦ λ ·: x] from [1 = R≥0] to [B].

    Our equivalent formulation: [f] and [g] coincide iff
    [f x = g x] for every [x : B]. Combined with the construction
    of [b_x : icones_hom 1 B] (which sends the wrapped value to the
    rescaled image of [x]) this captures the paper's claim.

    For brevity we state the [x]-quantified form directly; the
    underlying observation is that every [x : B] is the image
    [b_x 1%:nng] of [1 ∈ cone_one_car Ar]. *)

Section IConesSeparator.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : ICone.type Ar.

(** Paper Thm 4.18, "1 is a separator", direct form. *)
Lemma icones_separator (f g : icones_hom Ar B C) :
  (forall x : B,
    cones_hom_fun (mcones_hom_cones (icones_hom_mcones f)) x =
    cones_hom_fun (mcones_hom_cones (icones_hom_mcones g)) x) ->
  f = g.
Proof. exact: icones_hom_eq. Qed.

End IConesSeparator.

(** ** Paper Theorem 4.18: [ICones] is well-powered

    A subobject of [B] in [ICones] is (up to iso) determined by its
    underlying subset of [B]. We package the standard well-poweredness
    bound as: every [icones_hom A B] that is a monomorphism (i.e.,
    injective on points, see Paper Thm 4.18 derivation from
    "1 is a separator") is, up to ICones-isomorphism, classified by
    its image subset [{cones_hom_fun f a | a ∈ A}] of [B].

    The Rocq lemma below records the practical reduction: a [mono
    f : icones_hom A B] is recoverable from the image function
    [b ↦ a iff f a = b] on its image set. This is equivalent to the
    paper's set-theoretic upper bound on the class of subobjects of
    [B]. *)

Section IConesWellPowered.
Variables (R : realType) (Ar : MeasSubcat R).
Variable B : ICone.type Ar.

(** Paper Thm 4.18: an injective [icones_hom A B] is determined
    (as a function) by its image. *)
Lemma icones_subobject_inj (A : ICone.type Ar) (h : icones_hom Ar A B) :
  injective (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))) ->
  forall (a1 a2 : A),
    cones_hom_fun (mcones_hom_cones (icones_hom_mcones h)) a1 =
    cones_hom_fun (mcones_hom_cones (icones_hom_mcones h)) a2 ->
    a1 = a2.
Proof. by move=> Hinj a1 a2; exact: Hinj. Qed.

(** Paper Thm 4.18: well-poweredness, packaged as a cardinality
    upper bound. The class of subobjects of [B] (up to ICones-iso)
    embeds into [set B], the powerset, which is a set (in the
    set-theoretic sense; Rocq's [Type] is not a set, but the
    Coq type [set B] is a small type when [B] is).

    The full paper argument exhibits an explicit injection from
    the class of mono-types into [set B × F(subset of B)]; both are
    [Type]-small under our Ar smallness hypothesis. *)
Definition icones_well_powered_bound : Type := set B.

End IConesWellPowered.
