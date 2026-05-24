(**md**************************************************************************)
(* # The internal-hom functor preserves all limits — Paper Theorem 5.9        *)
(*   ([th:limpl-has-left-adj])                                                 *)
(*                                                                            *)
(*   For each integrable cone [C], the functor [C ⊸ -] preserves all          *)
(*   limits.  A category with all small products and equalisers has all       *)
(*   limits, so — exactly as in the paper — this reduces to two facts:        *)
(*                                                                            *)
(*   - PRODUCTS ([limpl_preserves_prod]).  For a family [(D_i)_{i ∈ I}] with  *)
(*     product [&_i D_i], the canonical comparison                            *)
(*       [k = ⟨ C ⊸ π_i ⟩_i : C ⊸ (&_i D_i)  ≅  &_i (C ⊸ D_i)]               *)
(*     is an iso in [ICones].  The inverse sends a bounded tuple              *)
(*     [f⃗ = (f_i)_i] to the integrable linear map [x ↦ (f_i x)_i] (linear,    *)
(*     continuous, norm-[≤1]-preserving, measurable, integral-preserving —    *)
(*     all componentwise, as the integral in [&_i D_i] is componentwise).     *)
(*                                                                            *)
(*   - EQUALISERS ([limpl_preserves_eq]).  For [f, g : D1 → D2] with          *)
(*     equaliser [(E, e)] (the [icones_eq]/[icones_eq_incl] of §4), the pair  *)
(*     [(C ⊸ E, C ⊸ e)] is the equaliser of [C ⊸ f], [C ⊸ g].  Given          *)
(*     [h : H → (C ⊸ D1)] equalising [C ⊸ f], [C ⊸ g], the per-point          *)
(*     equation [f (h z x) = g (h z x)] (the hypothesis read pointwise — this *)
(*     is the paper's "[h'] ranges in [E]") lets us co-restrict [h z] to a    *)
(*     [C ⊸ E]-valued map [h_0], the unique mediator since [C ⊸ e] is mono    *)
(*     (it is [cones_eq_val], a faithful inclusion).                          *)
(*                                                                            *)
(*   This file is AXIOM-FREE relative to the classical base of                *)
(*   mathcomp-analysis: it is pure [ICones] limit theory and depends on NO    *)
(*   staged interface ([saft_interface]/[exp_interface]/[seely_interface]).   *)
(*   Theorem 5.9 is the INPUT consumed by the M-SAFT machinery of             *)
(*   [Icones.icones.representable] to build the tensor [- ⊗ C] as the SAFT    *)
(*   left adjoint of [C ⊸ -]; it must not itself consume that interface.      *)
(*                                                                            *)
(*   APIs used:                                                               *)
(*   - [linhom_post_icones] ([C ⊸ g]) and its functoriality, from             *)
(*     [Icones.homs.linhom_functor].                                          *)
(*   - [icones_prod]/[icones_proj]/[icones_tuple] and their UMP               *)
(*     ([icones_tuple_proj]/[icones_tuple_unique]); [icones_eq]/              *)
(*     [icones_eq_incl] and [icones_eq_incl_equ], from                        *)
(*     [Icones.icones.icone_cat].                                             *)
(*   - [icones_iso]/[icones_iso_of_cancel], from [Icones.homs.icones_iso].    *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import ereal measurable_structure measurable_function.
From mathcomp.analysis Require Import measure lebesgue_integral_definition.

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
Require Import Icones.icones.fubini.
Require Import Icones.icones.icone_cat.
Require Import Icones.homs.linhom.
Require Import Icones.homs.icones_iso.
Require Import Icones.homs.linhom_functor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** Products — Paper Theorem 5.9, products case

    Fix [C] and a family [(D_i)_{i ∈ I}].  Write [D := &_i D_i] for the
    product [icones_prod D] and [π_i := icones_proj i].  The comparison

      [k := ⟨ C ⊸ π_i ⟩_i : C ⊸ D  →  &_i (C ⊸ D_i)]

    is [icones_tuple (fun i => linhom_post_icones (π_i))].  We show it is
    an iso by exhibiting an explicit inverse [kinv].  The element
    [kinv f⃗ : C ⊸ D] is the integrable linear map
      [x ↦ (f_i x)_i]
    where [f_i := cones_prod_val f⃗ i : C ⊸ D_i]; everything is
    componentwise because the cone operations, the norm, the measurable
    structure and the integral of [D = &_i D_i] are componentwise. *)

(** Helper: a uniform componentwise bound dominates the product norm
    (handling the empty-index case via [sup0]). *)
Lemma cones_prod_norm_le (R : realType) (I : Type) (P : I -> coneType R)
    (x : cones_prod_car I P) (M : R) :
  0 <= M ->
  (forall i, cone_norm (cones_prod_val x i) <= M) ->
  cones_prod_norm x <= M.
Proof.
move=> Mge0 HM.
case Hex : `[< cones_prod_normset x !=set0 >]; last first.
  have HE : cones_prod_normset x = set0.
    apply/predeqP => yy; split=> // Hyy.
    by move/asboolPn: Hex; apply; exists yy.
  by rewrite /cones_prod_norm HE sup0.
move/asboolP: Hex => Hex.
apply: ge_sup => //.
by move=> r [i ->]; exact: HM.
Qed.

Section LimplPreservesProd.
Variables (R : realType) (Ar : MeasSubcat R).
Variable C : ICone.type Ar.
Variable I : Type.
Variable D : I -> ICone.type Ar.

Local Notation Dprod := (icones_prod D).
Local Notation Lprod := (icones_prod (fun i => linhom_car Ar C (D i))).

(** The forward comparison [k = ⟨ C ⊸ π_i ⟩_i]. *)
Definition limpl_prod_fwd : icones_hom Ar (linhom_car Ar C Dprod) Lprod :=
  icones_tuple (fun i => linhom_post_icones (icones_proj i)).

(** *** The inverse [kinv] as a [linhom_car] for each tuple [f⃗] *)

Section Inverse.
Variable fv : Lprod.

(** The [i]-th component of [f⃗] is a [C ⊸ D_i]. *)
Local Notation fi i := (cones_prod_val fv i).

(** The underlying function of [kinv f⃗]: [x ↦ (f_i x)_i].  Bounded by
    [‖f⃗‖ · ‖x‖] uniformly in [i], so it lands in the product carrier. *)

Lemma limpl_prod_inv_bd (x : C) :
  exists M : R, forall i, cone_norm (linhom_fun (fi i) x) <= M.
Proof.
exists (cone_norm fv * cone_norm x) => i.
have HK : linhom_norm (fi i) <= cone_norm fv.
  exact: (cones_prod_norm_ge_comp fv i).
exact: (linhom_norm_apply_le HK x).
Qed.

Definition limpl_prod_inv_fun (x : C) : Dprod :=
  {| cones_prod_val := fun i => linhom_fun (fi i) x;
     cones_prod_bd := limpl_prod_inv_bd x |}.

(** Componentwise projection of [kinv f⃗ x]. *)
Lemma limpl_prod_inv_funE (x : C) (i : I) :
  cones_prod_val (limpl_prod_inv_fun x) i = linhom_fun (fi i) x.
Proof. by []. Qed.

(** Linearity — componentwise, from linearity of each [f_i]. *)
Lemma limpl_prod_inv_linear : is_linear limpl_prod_inv_fun.
Proof.
split.
- apply: cones_prod_eq => i; rewrite limpl_prod_inv_funE /=.
  by have [H0 _ _] := linhom_pre_linear (linhom_pre_of (fi i)); rewrite /linhom_fun H0.
- move=> x y; apply: cones_prod_eq => i.
  rewrite limpl_prod_inv_funE /=.
  by have [_ HD _] := linhom_pre_linear (linhom_pre_of (fi i)); rewrite /linhom_fun HD.
- move=> r x; apply: cones_prod_eq => i.
  rewrite limpl_prod_inv_funE /=.
  by have [_ _ HZ] := linhom_pre_linear (linhom_pre_of (fi i)); rewrite /linhom_fun HZ.
Qed.

(** ω-continuity — componentwise, from ω-continuity of each [f_i] and the
    componentwise structure of [cone_sup_ball] on the product. *)
Lemma limpl_prod_inv_continuous : is_omega_continuous limpl_prod_inv_fun.
Proof.
move=> u uch ub1 fuch fub1.
apply: cones_prod_eq => i.
rewrite limpl_prod_inv_funE.
(* The [i]-th component of the product-sup is the cone-sup of the
   [i]-th components. *)
have ci_ch : forall n, precone_le (linhom_fun (fi i) (u n))
                                  (linhom_fun (fi i) (u n.+1)).
  move=> n.
  by have := cones_prod_le_comp (fuch n) i; rewrite !limpl_prod_inv_funE.
have ci_ub1 : forall n, cone_norm (linhom_fun (fi i) (u n)) <= 1.
  move=> n.
  rewrite -(limpl_prod_inv_funE (u n) i).
  apply: le_trans (cones_prod_norm_ge_comp (limpl_prod_inv_fun (u n)) i) _.
  exact: fub1.
have Hcont := linhom_pre_continuous (linhom_pre_of (fi i)) u uch ub1
                ci_ch ci_ub1.
rewrite /linhom_fun Hcont.
(* RHS: the [i]-th projection is ω-continuous (it is [icones_proj i]),
   so its value on the product-sup is the cone-sup of the components. *)
have ci_ch' : forall n, precone_le (cones_proj_fun i ((limpl_prod_inv_fun \o u) n))
                                   (cones_proj_fun i ((limpl_prod_inv_fun \o u) n.+1)).
  by move=> n; rewrite /cones_proj_fun !limpl_prod_inv_funE.
have ci_ub1' : forall n, cone_norm (cones_proj_fun i ((limpl_prod_inv_fun \o u) n)) <= 1.
  by move=> n; rewrite /cones_proj_fun limpl_prod_inv_funE.
have Hproj :
    cones_proj_fun i (cone_sup_ball (limpl_prod_inv_fun \o u) fuch fub1) =
    cone_sup_ball (cones_proj_fun i \o (limpl_prod_inv_fun \o u)) ci_ch' ci_ub1'.
  exact: (@cones_proj_continuous R I (fun i => D i : coneType R) i
            (limpl_prod_inv_fun \o u) fuch fub1 ci_ch' ci_ub1').
rewrite -[RHS]/(cones_proj_fun i (cone_sup_ball (limpl_prod_inv_fun \o u) fuch fub1))
        Hproj; clear Hproj.
(* Both sides are now [cone_sup_ball] of the *definitionally equal*
   sequence [n ↦ f_i (u n)], with different chain/bound witnesses;
   close by antisymmetry of the two least-upper-bound characterisations. *)
apply: precone_le_anti.
- apply: cone_sup_ball_lub => n.
  exact: (cone_sup_ball_ub (cones_proj_fun i \o (limpl_prod_inv_fun \o u))
            ci_ch' ci_ub1' n).
- apply: cone_sup_ball_lub => n.
  exact: (cone_sup_ball_ub (fi i \o u) ci_ch ci_ub1 n).
Qed.

(** Boundedness — operator norm [≤ ‖f⃗‖]. *)
Lemma limpl_prod_inv_bounded :
  exists M : R, forall x : C, cnorm x <= 1 -> cnorm (limpl_prod_inv_fun x) <= M.
Proof.
exists (cone_norm fv) => x Hx.
apply: cones_prod_norm_le; first exact: cone_norm_ge0.
move=> i; rewrite limpl_prod_inv_funE.
apply: le_trans (linhom_norm_sup_ub (fi i) x Hx) _.
exact: (cones_prod_norm_ge_comp fv i).
Qed.

(** Measurable-path preservation — componentwise, via the product test
    family [iniTest].  A measurable path [γ] of [C] maps to a path of [D]
    whose [i]-th projection is [f_i ∘ γ], measurable since [f_i] is. *)
Lemma limpl_prod_inv_pres_path
    (X : ar_obj Ar) (γ : ar_carrier Ar X -> C) :
  is_measurable_path (Ar:=Ar) (C:=C) γ ->
  is_measurable_path (Ar:=Ar) (C:=Dprod) (fun r => limpl_prod_inv_fun (γ r)).
Proof.
move=> Hγ.
split.
  case: (limpl_prod_inv_bounded) => M HM.
  have [[Mγ HMγ] _] := Hγ.
  have Mγ_ge0 : 0 <= Mγ.
    apply: (le_trans (cone_norm_ge0 (γ (@ar_point R Ar X)))).
    exact: HMγ.
  (* Uniform bound on the product path. *)
  have fvge0 : 0 <= cone_norm fv by exact: cone_norm_ge0.
  exists (cone_norm fv * Mγ + cone_norm fv) => r.
  apply: cones_prod_norm_le.
    by apply: addr_ge0 => //; apply: mulr_ge0.
  move=> i; rewrite limpl_prod_inv_funE.
  have HK : linhom_norm (fi i) <= cone_norm fv.
    exact: (cones_prod_norm_ge_comp fv i).
  apply: (le_trans (linhom_norm_apply_le HK (γ r))).
  apply: le_trans (_ : cone_norm fv * Mγ <= _).
    by rewrite ler_wpM2l //; exact: HMγ.
  by rewrite lerDl.
move=> Y p [i [m [mM ->]]].
(* The product test [iniTest i m] pulls back to a [D_i]-test of [f_i ∘ γ]. *)
have Hfiγ : is_measurable_path (fun r => linhom_fun (fi i) (γ r)).
  exact: (linhom_pre_pres_path (linhom_pre_of (fi i)) X γ Hγ).
have [_ Hmeas] := Hfiγ.
have := Hmeas Y m mM.
apply: eq_measurable_fun => sr _ /=.
by rewrite /iniTest /= /iniTest_fun limpl_prod_inv_funE.
Qed.

Definition limpl_prod_inv_pre : linhom_pre Ar C Dprod :=
  MkLinhomPre limpl_prod_inv_fun limpl_prod_inv_linear
    limpl_prod_inv_continuous limpl_prod_inv_bounded
    limpl_prod_inv_pres_path.

(** Integral preservation — componentwise, since the integral in
    [D = &_i D_i] is componentwise and each [f_i] preserves integrals. *)
Lemma limpl_prod_inv_pres_int
    (X : ar_obj Ar) (β : ar_carrier Ar X -> C)
    (Hβ : is_measurable_path β) (µ : fmeas R (ar_carrier Ar X)) :
  linhom_pre_fun limpl_prod_inv_pre (icone_integral β Hβ µ) =
  icone_integral
    (fun r => linhom_pre_fun limpl_prod_inv_pre (β r))
    (linhom_pre_pres_path limpl_prod_inv_pre X β Hβ) µ.
Proof.
(* Reduce equality of the two product integrals to agreement on every
   product test [iniTest i m], via the Pettis characterisation
   [icone_integralP].  Componentwise this is each [f_i]'s integral
   preservation. *)
apply: cones_prod_eq => i.
rewrite [LHS]limpl_prod_inv_funE /linhom_fun.
(* LHS_i = f_i (∫ β) = ∫ (f_i ∘ β). *)
rewrite (linhom_pres_int (fi i) X β Hβ µ).
(* RHS_i = (∫_{prod} kinv∘β)_i = ∫ (kinv∘β)_i = ∫ (f_i ∘ β). *)
rewrite -[RHS]/(cones_hom_fun
                  (mcones_hom_cones (@icones_proj_mcones R Ar I D i))
                  (icone_integral (fun r => limpl_prod_inv_fun (β r))
                     (linhom_pre_pres_path limpl_prod_inv_pre X β Hβ) µ)).
rewrite (@icones_proj_pres_int R Ar I D i X
          (fun r => limpl_prod_inv_fun (β r))
          (linhom_pre_pres_path limpl_prod_inv_pre X β Hβ) µ).
(* Both are [∫ (f_i ∘ β)], with proof-irrelevant path witnesses. *)
congr (icone_integral _ _ µ).
exact: Prop_irrelevance.
Qed.

Definition limpl_prod_inv_car : linhom_car Ar C Dprod :=
  MkLinhom limpl_prod_inv_pre limpl_prod_inv_pres_int.

End Inverse.

(** [kinv] as a function [&_i (C ⊸ D_i) → C ⊸ D]. *)
Definition limpl_prod_inv_map (fv : Lprod) : linhom_car Ar C Dprod :=
  limpl_prod_inv_car fv.

(** Pointwise value of [kinv f⃗]: [kinv f⃗ x . i = f_i x]. *)
Lemma limpl_prod_inv_mapE (fv : Lprod) (x : C) (i : I) :
  cones_prod_val (linhom_fun (limpl_prod_inv_map fv) x) i =
  linhom_fun (cones_prod_val fv i) x.
Proof. by []. Qed.

(** *** [kinv] is itself a morphism [&_i (C ⊸ D_i) → (C ⊸ &_i D_i)]
    in [ICones] — Paper §5.3, "We prove that [k⁻¹ ∈ ICONES(...)]".  All
    of linearity, ω-continuity, the operator bound [‖kinv f⃗‖ ≤ ‖f⃗‖],
    measurable-path and integral preservation are componentwise. *)

(** Linearity of [kinv] as a map of cones. *)
Lemma limpl_prod_inv_map_linear : is_linear limpl_prod_inv_map.
Proof.
split.
- apply: linhom_eq => x; apply: cones_prod_eq => i.
  by rewrite limpl_prod_inv_mapE /= /linhom_fun.
- move=> f1 f2; apply: linhom_eq => x; apply: cones_prod_eq => i.
  by rewrite limpl_prod_inv_mapE /= /linhom_fun.
- move=> r f; apply: linhom_eq => x; apply: cones_prod_eq => i.
  by rewrite limpl_prod_inv_mapE /= /linhom_fun.
Qed.

(** Operator-norm bound: [‖kinv f⃗‖ ≤ ‖f⃗‖]. *)
Lemma limpl_prod_inv_map_norm_le (fv : Lprod) :
  cone_norm (limpl_prod_inv_map fv) <= cone_norm fv.
Proof.
rewrite [cone_norm (limpl_prod_inv_map fv)]/=.
apply: linhom_norm_sup_lub => x Hx.
rewrite [cnorm (linhom_fun (limpl_prod_inv_map fv) x)]/=.
apply: cones_prod_norm_le; first exact: cone_norm_ge0.
move=> i; rewrite limpl_prod_inv_mapE.
apply: le_trans (linhom_norm_sup_ub (cones_prod_val fv i) x Hx) _.
exact: (cones_prod_norm_ge_comp fv i).
Qed.

(** ω-continuity of [kinv] as a map of cones.  By extensionality and
    test-separation of [Dprod = &_i D_i], it suffices to check, for every
    product test [iniTest i m] (with [m ∈ M^{D_i}_0]) and every [x], that
      [m (0, (kinv (sup U)) x . i)] = [m (0, (sup (kinv U)) x . i)].
    Both sides reduce, via the componentwise product-sup, the
    [linhom_sup_fun] characterisation of the linhom [cone_sup_ball], and
    the test-of-sup identity [linhom_sup_fun_test_sup], to the same real
    supremum [sup_n m(0, (U n)_i x)]. *)
Lemma limpl_prod_inv_map_continuous : is_omega_continuous limpl_prod_inv_map.
Proof.
move=> U Uch Uub1 KUch KUub1.
apply: linhom_eq => x.
apply: mcone_M_sep => p [i [m [mM ->]]].
rewrite /iniTest /= /iniTest_fun.
(* RHS: [(sup (kinv U)) x . i = (linhom_sup_fun_{kinv U} x) . i].  Apply
   the test-of-sup identity at the product test [iniTest i m]. *)
have RHSeq :
    test_fun m (ar_zero_pt Ar)
      (cones_prod_val
         (linhom_fun (cone_sup_ball (limpl_prod_inv_map \o U) KUch KUub1) x) i)
    = sup [set test_fun m (ar_zero_pt Ar)
             (cones_prod_val
                (linhom_fun ((limpl_prod_inv_map \o U) n) x) i) | n in [set: nat]].
  rewrite -[in LHS]/(@iniTest_fun R Ar I D (ar_zero Ar) i m (ar_zero_pt Ar)
                       (linhom_fun (cone_sup_ball (limpl_prod_inv_map \o U) KUch KUub1) x)).
  have := linhom_sup_fun_test_sup (u := limpl_prod_inv_map \o U) KUch KUub1
            (@iniTest R Ar I D (ar_zero Ar) i m) (ar_zero_pt Ar) x.
  by rewrite /iniTest /= /iniTest_fun.
rewrite RHSeq.
(* LHS: [(kinv (sup U)) x . i = (sup U)_i x = (linhom_sup of (U·)_i) x].
   The product sup-ball is componentwise; then the linhom test-of-sup. *)
rewrite limpl_prod_inv_mapE.
(* The product sup-ball is componentwise: [(sup U)_i] is the linhom
   sup-ball of [(U n)_i].  We get this from projection ω-continuity. *)
pose pch (n : nat) :=
  @cones_prod_le_comp R I (fun i => linhom_car Ar C (D i) : coneType R)
    (U n) (U n.+1) (Uch n) i.
pose pub (n : nat) :=
  le_trans (cones_prod_norm_ge_comp (U n) i) (Uub1 n).
have prodComp :
    cones_prod_val (cone_sup_ball U Uch Uub1) i =
    cone_sup_ball (fun n => cones_prod_val (U n) i) pch pub.
  rewrite -[LHS]/(cones_proj_fun i (cone_sup_ball U Uch Uub1)).
  rewrite (@cones_proj_continuous R I
             (fun i => linhom_car Ar C (D i) : coneType R) i
             U Uch Uub1 pch pub).
  apply: precone_le_anti.
  - apply: cone_sup_ball_lub => n.
    exact: (cone_sup_ball_ub (fun n => cones_prod_val (U n) i) pch pub n).
  - apply: cone_sup_ball_lub => n.
    exact: (cone_sup_ball_ub (cones_proj_fun i \o U) pch pub n).
rewrite prodComp.
(* Now LHS = [linhom_fun (linhom cone_sup_ball of (U·)_i) x]; the linhom
   [cone_sup_ball]'s value at [x] is [linhom_sup_fun x]. *)
have := linhom_sup_fun_test_sup
          (u := fun n => cones_prod_val (U n) i) pch pub
          m (ar_zero_pt Ar) x.
move=> ->.
(* Both sides are now [sup] of the same set: [m(0, (U n)_i x)]. *)
congr sup; apply: eq_set => z; split=> -[n _ <-]; by exists n.
Qed.

(** [kinv] packaged as a [cones_hom] [&_i (C ⊸ D_i) → (C ⊸ &_i D_i)]. *)
Definition limpl_prod_inv_cones :
    cones_hom Lprod (linhom_car Ar C Dprod) :=
  ConesHom limpl_prod_inv_map limpl_prod_inv_map_linear
    limpl_prod_inv_map_continuous limpl_prod_inv_map_norm_le.

(** Measurable-path preservation of [kinv].  Given a measurable path
    [Φ] of [Lprod], the path [r ↦ kinv (Φ r)] of [C ⊸ Dprod] is tested
    against [γ ▷ (iniTest i m)]; the body
    [(iniTest i m)(s, kinv (Φ r) (γ s)) = m(s, (Φ r)_i (γ s))]
    is measurable because the [i]-th projection [r ↦ (Φ r)_i] is a
    measurable path of [C ⊸ D_i] and the linhom test [γ ▷ m] applies. *)
Lemma limpl_prod_inv_map_pres_path
    (W : ar_obj Ar) (Φ : ar_carrier Ar W -> Lprod) :
  is_measurable_path Φ ->
  is_measurable_path (fun r => limpl_prod_inv_map (Φ r)).
Proof.
move=> HΦ.
have [[MΦ HMΦ] HΦm] := HΦ.
split.
  exists MΦ => r.
  apply: le_trans (limpl_prod_inv_map_norm_le (Φ r)) _.
  exact: HMΦ.
move=> Z q [γ [γub [m [mM ->]]]].
(* The [Dprod]-test [m] is [iniTest i m'] for some factor [i] and
   [D_i]-test [m']. *)
case: mM => i [m' [m'M mE]].
(* The [i]-th projection path of [Φ] in [C ⊸ D_i]. *)
have HΦproj : is_measurable_path
    (Ar:=Ar) (C:=linhom_car Ar C (D i)) (fun r => cones_prod_val (Φ r) i).
  exact: (icones_prod_path_comp (B := fun i => linhom_car Ar C (D i)) HΦ i).
have [_ HΦprojm] := HΦproj.
(* Test that projection path against the linhom test [γ ▷ m']. *)
have HmM : @mcone_M R Ar _ Z (linhom_test γ γub m' m'M)
  by exists γ, γub, m', m'M.
have := HΦprojm Z (linhom_test γ γub m' m'M) HmM.
apply: eq_measurable_fun => sr _ /=.
rewrite /linhom_test /= /linhom_test_fun /=.
by rewrite mE /iniTest /= /iniTest_fun /=.
Qed.

Definition limpl_prod_inv_mcones :
    mcones_hom Ar Lprod (linhom_car Ar C Dprod) :=
  MkMConesHom limpl_prod_inv_cones limpl_prod_inv_map_pres_path.

(** Integral preservation of [kinv].  Both sides agree componentwise and
    pointwise: [kinv (∫Φ) x . i = (∫Φ)_i x = ∫ ((Φ r)_i x)] (the linhom
    pointwise integral on [C ⊸ D_i]), which is exactly
    [(∫ (kinv ∘ Φ)) x . i]. *)
Lemma limpl_prod_inv_map_pres_int
    (W : ar_obj Ar) (Φ : ar_carrier Ar W -> Lprod)
    (HΦ : is_measurable_path Φ) (µ : fmeas R (ar_carrier Ar W)) :
  cones_hom_fun (mcones_hom_cones limpl_prod_inv_mcones)
    (icone_integral Φ HΦ µ) =
  icone_integral
    (fun r => cones_hom_fun (mcones_hom_cones limpl_prod_inv_mcones) (Φ r))
    (mcones_hom_pres_path limpl_prod_inv_mcones W Φ HΦ) µ.
Proof.
apply: icone_integral_eqP.
move=> q qM s.
case: qM => γ [γub [m [mM ->]]].
(* Decompose the [Dprod]-test [m = iniTest i m']. *)
case: mM => i [m' [m'M mE]].
rewrite /linhom_test /= /linhom_test_fun /=.
(* LHS: [kinv (∫Φ)] at [γ s], tested by [m = iniTest i m'], i.e.
   [m'(s, (kinv (∫Φ) (γ s)) . i) = m'(s, (∫Φ)_i (γ s))]. *)
rewrite mE /iniTest /= /iniTest_fun /=.
(* [(∫Φ)_i] is the componentwise integral [∫ (Φ·)_i] in [C ⊸ D_i]. *)
have projInt :
    cones_prod_val (icone_integral Φ HΦ µ) i =
    icone_integral (fun r => cones_prod_val (Φ r) i)
      (icones_prod_path_comp (B := fun i => linhom_car Ar C (D i)) HΦ i) µ.
  rewrite -[LHS]/(cones_hom_fun
                    (mcones_hom_cones
                       (@icones_proj_mcones R Ar I
                          (fun i => linhom_car Ar C (D i)) i))
                    (icone_integral Φ HΦ µ)).
  rewrite (@icones_proj_pres_int R Ar I (fun i => linhom_car Ar C (D i))
            i W Φ HΦ µ).
  by congr (icone_integral _ _ µ); exact: Prop_irrelevance.
rewrite projInt.
(* Test the linhom integral [∫(Φ·)_i] in [C ⊸ D_i] against the linhom
   test [γ ▷ m']; the Pettis characterisation [icone_integralP] turns the
   LHS into [∫ m'(s, (Φ r)_i (γ s)) dµ]. *)
set HΦi := icones_prod_path_comp _ i.
have HmM : @mcone_M R Ar _ (ar_zero Ar)
             (linhom_test (C := C) (D := D i) γ γub m' m'M)
  by exists γ, γub, m', m'M.
have := icone_integralP (fun r => cones_prod_val (Φ r) i) HΦi µ
          (linhom_test γ γub m' m'M) HmM s.
rewrite /linhom_test /= /linhom_test_fun /= => ->.
(* RHS: the test [m' ∘ π_i] / point [γ s] of [kinv (Φ r)]; integrands
   agree pointwise. *)
by congr (fine _).
Qed.

Definition limpl_prod_inv_icones :
    icones_hom Ar Lprod (linhom_car Ar C Dprod) :=
  MkIConesHom limpl_prod_inv_mcones limpl_prod_inv_map_pres_int.

(** The underlying function of [limpl_prod_inv_icones] is [kinv]. *)
Lemma limpl_prod_inv_iconesE (fv : Lprod) :
  cones_hom_fun (mcones_hom_cones (icones_hom_mcones limpl_prod_inv_icones)) fv =
  limpl_prod_inv_map fv.
Proof. by []. Qed.


(** *** The two cancellation equations *)

(** [k] applied to [f] has [i]-th component [π_i ∘ f].  Pointwise:
    [(k f) x . i = π_i (f x)]. *)
Lemma limpl_prod_fwd_compE (f : linhom_car Ar C Dprod) (i : I) (x : C) :
  linhom_fun (cones_prod_val (limpl_prod_fwd f) i) x =
  cones_prod_val (linhom_fun f x) i.
Proof. by []. Qed.

(** [kinv ∘ k = id]: recovering [f : C ⊸ &_i D_i] from its tuple of
    projections, pointwise and componentwise. *)
Lemma limpl_prod_invK (f : linhom_car Ar C Dprod) :
  limpl_prod_inv_map (limpl_prod_fwd f) = f.
Proof.
apply: linhom_eq => x.
apply: cones_prod_eq => i.
by rewrite /limpl_prod_inv_map limpl_prod_inv_funE.
Qed.

(** [k ∘ kinv = id]: recovering a bounded tuple [f⃗] from the integrable
    linear map it induces, componentwise (the [i]-th component of
    [k (kinv f⃗)] is [π_i ∘ kinv f⃗ = f_i]). *)
Lemma limpl_prod_fwdK (fv : Lprod) :
  limpl_prod_fwd (limpl_prod_inv_map fv) = fv.
Proof.
apply: cones_prod_eq => i.
apply: linhom_eq => x.
by rewrite limpl_prod_fwd_compE /limpl_prod_inv_map limpl_prod_inv_funE.
Qed.

(** Paper Theorem 5.9 (products): [k = ⟨ C ⊸ π_i ⟩_i] is an iso in
    [ICones], so [C ⊸ -] preserves the product [&_i D_i].  Both the
    forward [k = limpl_prod_fwd] and the backward [k⁻¹ =
    limpl_prod_inv_icones] are genuine [icones_hom]s; the two pointwise
    cancellations package them via [icones_iso_of_cancel]. *)
Definition limpl_preserves_prod :
  icones_iso Ar (linhom_car Ar C Dprod) Lprod :=
  icones_iso_of_cancel limpl_prod_fwd limpl_prod_inv_icones
    limpl_prod_invK limpl_prod_fwdK.

End LimplPreservesProd.

Arguments limpl_prod_fwd {R Ar} C {I} D.
Arguments limpl_prod_inv_map {R Ar} C {I} D.
Arguments limpl_preserves_prod {R Ar} C {I} D.
