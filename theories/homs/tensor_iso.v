(**md**************************************************************************)
(* # Thm 5.12 [tensor_hom_iso] — the FULL iso (Paper §5.4)                     *)
(*                                                                            *)
(*   This file completes the discharge of the SAFT/tensor interface by        *)
(*   building, on top of the AXIOM-FREE [tensor_construct] / [tensor_hom_iso]  *)
(*   modules, the inverse [Ψ] of [Φ] as a genuine [icones_hom] and assembling  *)
(*   the isomorphism of integrable cones                                       *)
(*                                                                            *)
(*     [Φ_{B,C,D} : (B⊗C)⊸D  ≅  B⊸(C⊸D)]   (Paper Thm 5.12 / §5.4).            *)
(*                                                                            *)
(*   The mechanism is the paper's: the residual obstruction (Ψ's value at a    *)
(*   GENERAL [z ∈ B⊗C] is opaque) is sidestepped by                            *)
(*                                                                            *)
(*   - [lfun_path_swap] (Paper [lemma:lfun-path-swap]): a path-valued swap,    *)
(*     built from the proved [swap_lin_path];                                  *)
(*   - [path_tens_to_one] (Paper [lemma:path-tens-to-one]): a function         *)
(*     [η : X → (B⊗C)⊸1] is a genuine measurable path as soon as it is bounded *)
(*     and measurable ON PURE TENSORS — NO density needed;                     *)
(*                                                                            *)
(*   so [Ψ]'s path field reduces (via [Psi_innerE]) to pure-tensor data, and   *)
(*   [Ψ]'s integral field follows from [Φ] injective + [Φ] preserves           *)
(*   integrals.  Everything is AXIOM-FREE (the 3 classical [boolp] axioms      *)
(*   only).  NO [saft_interface] import.                                       *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals constructive_ereal.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import ereal.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import measure.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import lebesgue_integral_definition.
From mathcomp.analysis Require Import lebesgue_integral_monotone_convergence.
From mathcomp.analysis Require Import topology normedtype sequences.
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
Require Import Icones.mcones.test_pullback.
Require Import Icones.icones.pettis.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_integral.
Require Import Icones.icones.examples_icone.
Require Import Icones.icones.icone_cat.
Require Import Icones.icones.representable.
Require Import Icones.homs.linhom.
Require Import Icones.homs.linhom_functor.
Require Import Icones.homs.icones_iso.
Require Import Icones.homs.limpl_continuous.
Require Import Icones.homs.bilin.
Require Import Icones.homs.tensor_construct.
Require Import Icones.homs.tensor_hom_iso.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Import Icones_tensor_construct.
Import Icones_tensor_hom_iso.

Module Icones_tensor_iso.

(** ** Pointwise evaluation of a [Path]-integral — Paper Thm 4.12

    The integral in [Path(X, B)] is computed pointwise: evaluating the
    path-integral [∫ η dν] at a point [s ∈ X] gives the [B]-integral of
    the section [r ↦ η(r)(s)].  Both sides satisfy the same Pettis
    specification (uniqueness in [B] via [icone_integral_eqP]); we obtain
    the identity directly from the Pettis spec of the [Path]-integral
    applied to the test [φ ▷ m] with [φ] the constant-[s] arrow. *)

Section PathIntEval.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (X : ar_obj Ar) (B : iconeType Ar).
Variables (Y' : ar_obj Ar).
Variable η : ar_carrier Ar Y' -> path_car Ar X B.
Hypothesis Hη : is_measurable_path η.
Variable ν : fmeas R (ar_carrier Ar Y').

(** The section [r ↦ η(r)(s)] is a measurable path in [B]. *)
Lemma path_int_section_meas (s : ar_carrier Ar X) :
  is_measurable_path (fun r : ar_carrier Ar Y' => path_fun (η r) s).
Proof.
have [[M HM] Hη_meas] := Hη.
split.
  exists M => r; apply: le_trans (path_norm_ub (η r) s) _; exact: HM.
move=> Z m mM.
pose pm : test_of Ar Z (path_car Ar X B) :=
  path_test (const_zs Z s) m mM.
have pmM : mcone_M Z pm by exists (const_zs Z s), m, mM.
have := Hη_meas Z pm pmM.
by under [in X0 in measurable_fun _ X0 -> _]eq_fun do
  rewrite /pm /path_test/= /path_test_fun/=.
Qed.

(** Paper Thm 4.12: [(∫ η dν)(s) = ∫ η(r)(s) dν]. *)
Lemma path_int_eval (s : ar_carrier Ar X) :
  path_fun (icone_integral η Hη ν) s =
  icone_integral (fun r => path_fun (η r) s) (path_int_section_meas s) ν.
Proof.
apply: icone_integral_eqP => m mM z.
(* The [Path]-test [(const_s) ▷ m] at arity 0 is in [path_mcone_M]; its
   Pettis spec for the [Path]-integral gives exactly the identity. *)
pose pm : test_of Ar (ar_zero Ar) (path_car Ar X B) :=
  path_test (const_zs (ar_zero Ar) s) m mM.
have pmM : mcone_M (ar_zero Ar) pm
  by exists (const_zs (ar_zero Ar) s), m, mM.
have HP := icone_integralP η Hη ν pm pmM z.
move: HP; rewrite /pm /path_test /= /path_test_fun /= => ->.
by [].
Qed.

End PathIntEval.

(** ** Evaluation of a [Path] at a point — [eval_path] as a [linhom_car]

    For a fixed [r ∈ X], the evaluation [γ ↦ γ(r) : Path(X, E) → E] is an
    integrable linear map of operator norm [≤ 1].  All cone operations on
    [Path(X, E)] (zero/sum/scale/sup) are POINTWISE, so linearity and
    ω-continuity are immediate; path/integral preservation are
    [path_int_section_meas] / [path_int_eval]. *)

Section EvalPath.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (X : ar_obj Ar) (E : ICone.type Ar).
Variable r : ar_carrier Ar X.

Local Notation P := (path_car Ar X E).

Definition eval_path_fun (γ : P) : E := path_fun γ r.

Lemma eval_path_linear : is_linear eval_path_fun.
Proof. by split=> [|x y|s x] //; rewrite /eval_path_fun. Qed.

Lemma eval_path_norm_le1 (γ : P) : cone_norm (eval_path_fun γ) <= cone_norm γ.
Proof. exact: path_norm_ub. Qed.

Lemma eval_path_bounded :
  exists M : R, forall γ : P, cnorm γ <= 1 -> cnorm (eval_path_fun γ) <= M.
Proof. by exists 1 => γ Hγ; apply: le_trans (eval_path_norm_le1 γ) _. Qed.

Lemma eval_path_continuous : is_omega_continuous eval_path_fun.
Proof.
move=> u uch ub1 fuch fub1.
rewrite /eval_path_fun.
(* [cone_sup_ball] in [Path] is [path_sup_ball], whose value at [r] is
   the [E]-[cone_sup_ball] of the pointwise sections. *)
rewrite -[path_fun (cone_sup_ball u uch ub1) r]/(path_sup_ball_fun uch ub1 r).
rewrite /path_sup_ball_fun.
exact: cone_sup_ball_irr.
Qed.

Lemma eval_path_pres_path
    (W : ar_obj Ar) (δ : ar_carrier Ar W -> P) :
  is_measurable_path δ ->
  is_measurable_path (fun w => eval_path_fun (δ w)).
Proof.
move=> Hδ; rewrite /eval_path_fun; exact: (path_int_section_meas Hδ r).
Qed.

Definition eval_path_pre : linhom_pre Ar P E :=
  MkLinhomPre eval_path_fun eval_path_linear eval_path_continuous
              eval_path_bounded
              (fun W δ Hδ => eval_path_pres_path (W:=W) (δ:=δ) Hδ).

Lemma eval_path_pres_int
    (W : ar_obj Ar) (δ : ar_carrier Ar W -> P)
    (Hδ : is_measurable_path δ) (µ : fmeas R (ar_carrier Ar W)) :
  linhom_pre_fun eval_path_pre (icone_integral δ Hδ µ) =
  icone_integral
    (fun w => linhom_pre_fun eval_path_pre (δ w))
    (linhom_pre_pres_path eval_path_pre W δ Hδ) µ.
Proof.
rewrite /eval_path_pre /= /eval_path_fun (path_int_eval Hδ µ r).
by congr icone_integral; exact: Prop_irrelevance.
Qed.

Definition eval_path : linhom_car Ar P E :=
  MkLinhom eval_path_pre eval_path_pres_int.

Lemma eval_pathE (γ : P) : linhom_fun eval_path γ = path_fun γ r.
Proof. by []. Qed.

Lemma eval_path_norm : cone_norm eval_path <= 1.
Proof.
rewrite -[cone_norm _]/(linhom_norm eval_path).
by apply: linhom_norm_sup_lub => γ Hγ; apply: le_trans (eval_path_norm_le1 γ) _.
Qed.

End EvalPath.

Arguments eval_path {R Ar X E} r.
Arguments eval_pathE {R Ar X E} r.

(** ** Pointwise evaluation of a [C ⊸ D]-integral — Paper Lemma 5.4

    The integral in the internal hom [C ⊸ D] is computed pointwise too:
    [(∫ η dµ)(y) = ∫ η(r)(y) dµ].  Same uniqueness argument as
    [path_int_eval], using the [C ⊸ D]-test [γ_y ▷ m] with [γ_y] the
    constant unit-ball-rescaled [C]-path at [y]. *)

Section LinhomIntEval.
Variables (R : realType) (Ar : MeasSubcat R).
Variables C D : ICone.type Ar.
Variables (Y' : ar_obj Ar).
Variable η : ar_carrier Ar Y' -> linhom_car Ar C D.
Hypothesis Hη : is_measurable_path η.
Variable µ : fmeas R (ar_carrier Ar Y').

(** The section [r ↦ η(r)(y)] is a measurable path in [D]. *)
Lemma linhom_int_section_meas (y : C) :
  is_measurable_path (fun r : ar_carrier Ar Y' => linhom_fun (η r) y).
Proof.
have [[M HM] Hη_meas] := Hη.
split.
  exists (M * (cone_norm y + 1)) => r.
  apply: le_trans (linhom_norm_apply_le (lexx _) y) _.
  apply: ler_pM; [exact: linhom_norm_ge0|exact: cone_norm_ge0| |].
  - exact: (HM r).
  - by rewrite lerDl ler01.
move=> Z m mM.
(* Rescale [y] into the unit ball and test [η] against [γ_{y'} ▷ m]. *)
have S_pos : 0 < cone_norm y + 1 by exact: cnorm_succ_pos.
have Sinv_ge0 : 0 <= (cone_norm y + 1)^-1 by rewrite invr_ge0 ltW.
pose Sinv : {nonneg R} := NngNum Sinv_ge0.
pose y' : C := precone_scale Sinv y.
have Hy'_unit : cone_norm y' <= 1.
  rewrite /y' cone_normh /=.
  rewrite mulrC ler_pdivrMr // mul1r.
  by rewrite -[X in X <= _]addr0 lerD2l ler01.
have Hγy'_unit : cone_norm (const_x_path_arity Z y') <= 1.
  by rewrite /cone_norm /= const_x_path_arity_normE.
pose p := linhom_test (const_x_path_arity Z y') Hγy'_unit m mM.
have pM : linhom_mcone_M (Y := Z) p.
  by exists (const_x_path_arity Z y'), Hγy'_unit, m, mM.
have := Hη_meas Z p pM.
(* [p (s, η r) = m s (η r (y'))]; rescale [y' → y] via [test_linZ]. *)
move=> Hbase.
have HE : (fun q : (ar_carrier Ar Z * ar_carrier Ar Y')%type =>
            test_fun m q.1 (linhom_fun (η q.2) y)) =
          (fun q => (cone_norm y + 1) *
                    test_fun (linhom_test (const_x_path_arity Z y')
                                 Hγy'_unit m mM) q.1 (η q.2)).
  apply: funext => q.
  rewrite /linhom_test /linhom_test_fun /= /const_x_path_arity /=.
  have [_ _ HZ] := linhom_pre_linear (linhom_pre_of (η q.2)).
  rewrite /y'.
  rewrite -[linhom_fun (η q.2) (Sinv *: y)%PC]/(η q.2 (Sinv *: y)%PC).
  rewrite HZ test_linZ /=.
  rewrite -[linhom_fun (η q.2) y]/(η q.2 y).
  by rewrite mulrA mulfV ?mul1r // gt_eqF.
rewrite HE.
apply: measurable_funM; first exact: measurable_cst.
exact: Hbase.
Qed.

(** Paper Lemma 5.4: [(∫ η dµ)(y) = ∫ η(r)(y) dµ]. *)
Lemma linhom_int_eval (y : C) :
  linhom_fun (icone_integral η Hη µ) y =
  icone_integral (fun r => linhom_fun (η r) y) (linhom_int_section_meas y) µ.
Proof.
apply: icone_integral_eqP => m mM z.
have S_pos : 0 < cone_norm y + 1 by exact: cnorm_succ_pos.
have Sinv_ge0 : 0 <= (cone_norm y + 1)^-1 by rewrite invr_ge0 ltW.
pose Sinv : {nonneg R} := NngNum Sinv_ge0.
pose y' : C := precone_scale Sinv y.
have Hy'_unit : cone_norm y' <= 1.
  rewrite /y' cone_normh /=.
  rewrite mulrC ler_pdivrMr // mul1r.
  by rewrite -[X in X <= _]addr0 lerD2l ler01.
have Hγy'_unit : cone_norm (const_x_path y') <= 1.
  by rewrite /cone_norm /= const_x_path_normE.
pose p := linhom_test (const_x_path y') Hγy'_unit m mM.
have pM : linhom_mcone_M (Y := ar_zero Ar) p.
  by exists (const_x_path y'), Hγy'_unit, m, mM.
have HP := icone_integralP η Hη µ p pM z.
(* LHS via [test_linZ]: m z ((∫η)(y)) = (cnorm y + 1) · p(z, ∫η). *)
have LE : test_fun m z (linhom_fun (icone_integral η Hη µ) y) =
          (cone_norm y + 1) * test_fun p z (icone_integral η Hη µ).
  rewrite /p /linhom_test /linhom_test_fun /= /const_x_path /const_x_path_arity /=.
  have [_ _ HZ] := linhom_pre_linear (linhom_pre_of (icone_integral η Hη µ)).
  rewrite /y'.
  rewrite -[linhom_fun (icone_integral η Hη µ) (Sinv *: y)%PC]
            /((icone_integral η Hη µ : linhom_car _ _ _) (Sinv *: y)%PC).
  rewrite HZ test_linZ /=.
  rewrite -[linhom_fun (icone_integral η Hη µ) y]
            /((icone_integral η Hη µ : linhom_car _ _ _) y).
  by rewrite mulrA mulfV ?mul1r // gt_eqF.
rewrite LE HP.
(* RHS integrand: m z (η r (y)) = (cnorm y + 1) · p(z, η r). *)
have rwint : forall r, (test_fun m z (linhom_fun (η r) y))%:E =
    ((cone_norm y + 1) * test_fun p z (η r))%:E.
  move=> r.
  rewrite /p /linhom_test /linhom_test_fun /= /const_x_path /const_x_path_arity /=.
  have [_ _ HZ] := linhom_pre_linear (linhom_pre_of (η r)).
  rewrite /y'.
  rewrite -[linhom_fun (η r) (Sinv *: y)%PC]/(η r (Sinv *: y)%PC).
  rewrite HZ test_linZ /=.
  rewrite -[linhom_fun (η r) y]/(η r y).
  by rewrite mulrA mulfV ?mul1r // gt_eqF.
under [in RHS]eq_integral => r _ do rewrite rwint EFinM.
rewrite lebesgue_integral_nonneg.ge0_integralZl_EFin//; last 2 first.
- apply/measurable_EFinP.
  have [_ HM2] := Hη.
  have Hpr := HM2 (ar_zero Ar) p pM.
  have := measurable_comp (F := setT) measurableT (subsetT _) Hpr
            (measurable_fun_pair (measurable_cst z) (@measurable_id _ _ setT)).
  by [].
- by rewrite addr_ge0 ?cone_norm_ge0 ?ler01.
have [[M HM] HM2] := Hη.
have Ifin : (\int[fmeas_mu µ]_x (test_fun p z (η x))%:E)%E \is a fin_num.
  rewrite ge0_fin_numE; last by apply: integral_ge0 => r _; rewrite lee_fin;
    exact: test_ge0.
  apply: (@le_lt_trans _ _
    (\int[fmeas_mu µ]_(x in [set: ar_carrier Ar Y']) M%:E)%E).
    apply: ge0_le_integral => //.
    - by move=> r _; rewrite lee_fin; exact: test_ge0.
    - apply/measurable_EFinP.
      have Hpr := HM2 (ar_zero Ar) p pM.
      have := measurable_comp (F := setT) measurableT (subsetT _) Hpr
                (measurable_fun_pair (measurable_cst z) (@measurable_id _ _ setT)).
      by [].
    - move=> r _; rewrite lee_fin /p.
      by apply: le_trans (linhom_test_norm_le Hγy'_unit m z (η r)) _; exact: HM.
  rewrite -[(fun=> M%:E)]/(cst M%:E) lebesgue_integral_nonneg.integral_cst//.
  by rewrite ltey_eq fin_numM// fmeas_setT_fin.
by rewrite fineM// fin_numE.
by move=> r _; rewrite lee_fin; exact: test_ge0.
Qed.

End LinhomIntEval.

(** ** Evaluation of an internal hom at a point — [eval_at] as a [linhom_car]

    For a fixed [y ∈ C], the evaluation [φ ↦ φ(y) : (C ⊸ D) → D] is an
    integrable linear map (operator norm [≤ ‖y‖], so [linhom_car] but not
    necessarily of norm [≤ 1]).  Linearity / ω-continuity are the
    pointwise [linhom] laws; path/integral preservation are
    [linhom_int_section_meas] / [linhom_int_eval]. *)

Section EvalAt.
Variables (R : realType) (Ar : MeasSubcat R).
Variables C D : ICone.type Ar.
Variable y : C.

Local Notation L := (linhom_car Ar C D).

Definition eval_at_fun (φ : L) : D := linhom_fun φ y.

Lemma eval_at_linear : is_linear eval_at_fun.
Proof.
rewrite /eval_at_fun; split.
- by rewrite -[linhom_fun (0%PC : L) y]/(linhom_fun (linhom_zero C D) y).
- by move=> f g; rewrite -[linhom_fun (f + g)%PC y]/(linhom_add_fun f g y).
- by move=> s f; rewrite -[linhom_fun (s *: f)%PC y]/(linhom_scale_fun s f y).
Qed.

Lemma eval_at_norm_le (φ : L) :
  cone_norm (eval_at_fun φ) <= cone_norm φ * cone_norm y.
Proof. exact: linhom_norm_apply_le (lexx _) y. Qed.

Lemma eval_at_bounded :
  exists M : R, forall φ : L, cnorm φ <= 1 -> cnorm (eval_at_fun φ) <= M.
Proof.
exists (cone_norm y) => φ Hφ.
apply: le_trans (eval_at_norm_le φ) _.
by rewrite -[X in _ <= X]mul1r; apply: ler_wpM2r => //; exact: cone_norm_ge0.
Qed.

(** Test-value of a [D]-[cone_sup_ball] is the [sup] of the test-values:
    by [test_cont] ([≤], with [N := sup]) and monotonicity of tests
    ([≥], each chain element [≤ sup_ball]). *)
Lemma eval_at_test_sup_ball
    (v : nat -> D)
    (vch : forall n, precone_le (v n) (v n.+1))
    (vb1 : forall n, cone_norm (v n) <= 1)
    (Z : ar_obj Ar) (m : test_of Ar Z D) (s : ar_carrier Ar Z) :
  test_fun m s (cone_sup_ball v vch vb1) =
  sup [set test_fun m s (v n) | n in [set: nat]].
Proof.
have HS : has_sup [set test_fun m s (v n) | n in [set: nat]].
  split; first by exists (test_fun m s (v 0%N)), 0%N.
  exists 1 => _ [n _ <-].
  by apply: le_trans (test_le1 m s (vb1 n)).
apply/le_anti/andP; split.
- apply: test_cont => n.
  by apply: sup_upper_bound => //; exists n.
- apply: ge_sup; first by exists (test_fun m s (v 0%N)), 0%N.
  move=> _ [n _ <-].
  have [w ->] := cone_sup_ball_ub v vch vb1 n.
  by rewrite test_linD lerDl; exact: test_ge0.
Qed.

Lemma eval_at_continuous : is_omega_continuous eval_at_fun.
Proof.
move=> u uch ub1 fuch fub1.
rewrite /eval_at_fun.
apply: mcone_M_sep => m mM.
set s := ar_zero_pt Ar.
rewrite -[linhom_fun (cone_sup_ball u uch ub1) y]/(linhom_sup_fun uch ub1 y).
rewrite (linhom_sup_fun_test_sup uch ub1 m s y).
rewrite (eval_at_test_sup_ball fuch fub1 m s).
by congr (sup _).
Qed.

Lemma eval_at_pres_path
    (W : ar_obj Ar) (δ : ar_carrier Ar W -> L) :
  is_measurable_path δ ->
  is_measurable_path (fun w => eval_at_fun (δ w)).
Proof.
move=> Hδ; rewrite /eval_at_fun; exact: (linhom_int_section_meas Hδ y).
Qed.

Definition eval_at_pre : linhom_pre Ar L D :=
  MkLinhomPre eval_at_fun eval_at_linear eval_at_continuous
              eval_at_bounded
              (fun W δ Hδ => eval_at_pres_path (W:=W) (δ:=δ) Hδ).

Lemma eval_at_pres_int
    (W : ar_obj Ar) (δ : ar_carrier Ar W -> L)
    (Hδ : is_measurable_path δ) (µ : fmeas R (ar_carrier Ar W)) :
  linhom_pre_fun eval_at_pre (icone_integral δ Hδ µ) =
  icone_integral
    (fun w => linhom_pre_fun eval_at_pre (δ w))
    (linhom_pre_pres_path eval_at_pre W δ Hδ) µ.
Proof.
rewrite /eval_at_pre /= /eval_at_fun (linhom_int_eval Hδ µ y).
by congr icone_integral; exact: Prop_irrelevance.
Qed.

Definition eval_at : linhom_car Ar L D :=
  MkLinhom eval_at_pre eval_at_pres_int.

Lemma eval_atE (φ : L) : linhom_fun eval_at φ = linhom_fun φ y.
Proof. by []. Qed.

End EvalAt.

Arguments eval_at {R Ar C D} y.
Arguments eval_atE {R Ar C D} y.

(** ** Paper [lemma:lfun-path-swap] — the path-valued swap

    Given [f ∈ ICones(B, Path(X, C ⊸ D))], the "transpose"
    [f'(y)(r)(x) = f(x)(r)(y)] is an element of
    [ICones(C, Path(X, B ⊸ D))].

    The inner element [swap_inner f r y : B ⊸ D] (the map
    [x ↦ f(x)(r)(y)]) is assembled by COMPOSITION of the already-built
    integrable maps: [eval_at y ∘ eval_path r ∘ (f as linhom)], so all
    five [linhom_car] fields come for free from [linhom_comp].  Its
    computation law [swap_innerE] is [linhom_compE] applied twice. *)

Section SwapInner.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (X : ar_obj Ar) (B C D : ICone.type Ar).
Variable f : icones_hom Ar B (path_car Ar X (linhom_car Ar C D)).

(** [swap_inner f r y : B ⊸ D], the map [x ↦ f(x)(r)(y)]. *)
Definition swap_inner (r : ar_carrier Ar X) (y : C) : linhom_car Ar B D :=
  linhom_comp (eval_at y) (linhom_comp (eval_path r) (icones_to_linhom f)).

Lemma swap_innerE (r : ar_carrier Ar X) (y : C) (x : B) :
  linhom_fun (swap_inner r y) x =
  linhom_fun (path_fun ((f : icones_hom _ _ _) x) r) y.
Proof.
rewrite /swap_inner !linhom_compE eval_atE eval_pathE.
by rewrite icones_to_linhomE.
Qed.

End SwapInner.

Arguments swap_inner {R Ar X B C D} f r y.
Arguments swap_innerE {R Ar X B C D} f r y x.

(** The transpose path [r ↦ swap_inner f r y] is a measurable path of
    [B ⊸ D].  Mirrors the reindexing argument of [swap_lin_path]: test
    the [Path(X, C⊸D)]-path [s ↦ f(β s)] (which [f] preserves) at the
    product arity [Y × X] against the [Path]-test [(ar_prod_snd) ▷
    ((y-section of) m reindexed by ar_prod_fst)], and pull back along the
    diagonal in [X]. *)

Section SwapInnerPath.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (X : ar_obj Ar) (B C D : ICone.type Ar).
Variable f : icones_hom Ar B (path_car Ar X (linhom_car Ar C D)).
Variable y : C.

Lemma swap_inner_path :
  is_measurable_path (fun r => swap_inner f r y).
Proof.
split.
  exists (cone_norm y) => r.
  rewrite -[cone_norm (swap_inner f r y)]/(linhom_norm (swap_inner f r y)).
  apply: linhom_norm_sup_lub => x Hx.
  rewrite swap_innerE.
  have Hphi : cone_norm (path_fun ((f : icones_hom _ _ _) x) r) <= 1.
    apply: le_trans (path_norm_ub ((f : icones_hom _ _ _) x) r) _.
    apply: le_trans (cones_hom_norm_le1 (mcones_hom_cones (icones_hom_mcones f)) x) _.
    exact: Hx.
  by have := linhom_norm_apply_le Hphi y; rewrite mul1r.
move=> Y p [β [βub [mD [mDM ->]]]].
(* The [Path(X,C⊸D)]-path [s ↦ f(β s)], which [f] preserves. *)
have Hfβ : is_measurable_path (fun s => (f : icones_hom _ _ _) (path_fun β s)).
  exact: (mcones_hom_pres_path (icones_hom_mcones f) Y (path_fun β) (path_is_path β)).
have S_pos : 0 < cone_norm y + 1 by exact: cnorm_succ_pos.
have Sinv_ge0 : 0 <= (cone_norm y + 1)^-1 by rewrite invr_ge0 ltW.
pose Sinv : {nonneg R} := NngNum Sinv_ge0.
pose y' : C := precone_scale Sinv y.
have Hy'_unit : cone_norm y' <= 1.
  rewrite /y' cone_normh /=.
  rewrite mulrC ler_pdivrMr // mul1r.
  by rewrite -[X in X <= _]addr0 lerD2l ler01.
(* Reindex [f(β ·)] (over Y) to a path at arity [ar_prod Y X] picking Y. *)
pose Pfst : ar_carrier Ar (ar_prod Ar Y X) -> path_car Ar X (linhom_car Ar C D)
  := fun q => (f : icones_hom _ _ _) (path_fun β (ar_prod_fst Y X q)).
have HPfst : is_measurable_path Pfst.
  exact: (reindex_path_measurable (ar_prod_fst Y X) Hfβ).
(* The inner (C⊸D)-test: evaluate at y' (unit-ball const path), test with
   mD reindexed to pick the Y-coordinate. *)
have Hγ' : cone_norm (const_x_path_arity (ar_prod Ar Y X) y') <= 1.
  by rewrite /cone_norm /= const_x_path_arity_normE.
pose mDfst : test_of Ar (ar_prod Ar Y X) D := test_reindex (ar_prod_fst Y X) mD.
have mDfstM : mcone_M (ar_prod Ar Y X) mDfst by exact: mcone_M_comp.
pose mCD : test_of Ar (ar_prod Ar Y X) (linhom_car Ar C D) :=
  linhom_test (const_x_path_arity (ar_prod Ar Y X) y') Hγ' mDfst mDfstM.
have mCDM : mcone_M (ar_prod Ar Y X) mCD.
  by exists (const_x_path_arity (ar_prod Ar Y X) y'), Hγ', mDfst, mDfstM.
(* The Path(X,C⊸D)-test picking X-coordinate via ar_prod_snd. *)
pose mP : test_of Ar (ar_prod Ar Y X) (path_car Ar X (linhom_car Ar C D)) :=
  path_test (ar_prod_snd Y X) mCD mCDM.
have mPM : mcone_M (ar_prod Ar Y X) mP by exists (ar_prod_snd Y X), mCD, mCDM.
have [_ HPfstm] := HPfst.
have HPtest := HPfstm (ar_prod Ar Y X) mP mPM.
pose ψ (sr : (ar_carrier Ar Y * ar_carrier Ar X)%type) :
  (ar_carrier Ar (ar_prod Ar Y X) * ar_carrier Ar (ar_prod Ar Y X))%type :=
  (ar_prod_cast (sr.1, sr.2), ar_prod_cast (sr.1, sr.2)).
have ψ_meas : measurable_fun [set: (ar_carrier Ar Y * ar_carrier Ar X)%type] ψ.
  apply: measurable_fun_pair.
  - apply: (measurableT_comp (ar_prod_cast_meas Ar Y X)).
    by apply: measurable_fun_pair; [exact: measurable_fst|exact: measurable_snd].
  - apply: (measurableT_comp (ar_prod_cast_meas Ar Y X)).
    by apply: measurable_fun_pair; [exact: measurable_fst|exact: measurable_snd].
rewrite (_ : (fun p0 : (ar_carrier Ar Y * ar_carrier Ar X)%type =>
                linhom_test β βub mD mDM p0.1 (swap_inner f p0.2 y)) =
             (fun sr : (ar_carrier Ar Y * ar_carrier Ar X)%type =>
                (cone_norm y + 1) * (mP (ψ sr).1 (Pfst (ψ sr).2)))); last first.
  apply: funext => sr.
  rewrite /ψ /mP /Pfst /path_test /= /path_test_fun /=.
  rewrite /mCD /linhom_test /linhom_test_fun /= /const_x_path_arity /=.
  rewrite /mDfst /test_reindex /test_reindex_fun /=.
  rewrite /ar_prod_fst /ar_prod_fst_fun /ar_prod_snd /ar_prod_snd_fun !ar_prod_castK /=.
  rewrite swap_innerE.
  rewrite /y'.
  have [_ _ HZ] :=
    linhom_pre_linear (linhom_pre_of (path_fun ((f : icones_hom _ _ _) (β sr.1)) sr.2)).
  rewrite -[linhom_fun (path_fun _ sr.2) (Sinv *: y)%PC]
            /((path_fun ((f : icones_hom _ _ _) (β sr.1)) sr.2) (Sinv *: y)%PC).
  rewrite HZ /= test_linZ /=.
  by rewrite mulrA mulfV ?mul1r // gt_eqF.
apply: measurable_funM; first exact: measurable_cst.
exact: (measurable_comp (F := setT) measurableT (subsetT _) HPtest ψ_meas).
Qed.

End SwapInnerPath.

Arguments swap_inner_path {R Ar X B C D} f y.

(** ** Paper [lemma:lfun-path-swap] — assembled as an [icones_hom]

    [lfun_path_swap f : icones_hom C (Path(X, B⊸D))], the transpose
    [y ↦ (r ↦ (x ↦ f(x)(r)(y)))], with computation law [lfun_path_swapE]:
    [(lfun_path_swap f y)(r)(x) = f(x)(r)(y)]. *)

Section LfunPathSwap.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (X : ar_obj Ar) (B C D : ICone.type Ar).
Variable f : icones_hom Ar B (path_car Ar X (linhom_car Ar C D)).

Local Notation PBD := (path_car Ar X (linhom_car Ar B D)).

(** The transpose value [lfps y : Path(X, B⊸D)]. *)
Definition lfps (y : C) : PBD := MkPath (swap_inner_path f y).

Lemma lfpsE (y : C) (r : ar_carrier Ar X) (x : B) :
  linhom_fun (path_fun (lfps y) r) x =
  linhom_fun (path_fun ((f : icones_hom _ _ _) x) r) y.
Proof. by rewrite /lfps /= swap_innerE. Qed.

Lemma lfps_linear : is_linear lfps.
Proof.
split.
- apply: path_eq => r /=; apply: linhom_eq => x.
  rewrite swap_innerE.
  have [Z0 _ _] :=
    linhom_pre_linear (linhom_pre_of (path_fun ((f : icones_hom _ _ _) x) r)).
  rewrite -[linhom_fun (path_fun ((f : icones_hom _ _ _) x) r) 0%PC]
            /(path_fun ((f : icones_hom _ _ _) x) r 0%PC).
  rewrite Z0.
  by rewrite [linhom_fun (path_zero_fun (linhom_car Ar B D) r) x]/= /path_zero_fun /=
             [linhom_fun (0%PC : linhom_car Ar B D) x]/= /linhom_zero_fun.
- move=> y1 y2; apply: path_eq => r /=; apply: linhom_eq => x.
  rewrite swap_innerE.
  rewrite [linhom_fun (swap_inner f r y1 + swap_inner f r y2)%PC x]/linhom_fun /=
          /linhom_add_fun.
  rewrite -!/(linhom_fun (swap_inner f r y1) x) -!/(linhom_fun (swap_inner f r y2) x).
  rewrite !swap_innerE.
  have [_ HD _] :=
    linhom_pre_linear (linhom_pre_of (path_fun ((f : icones_hom _ _ _) x) r)).
  rewrite -[linhom_fun (path_fun ((f : icones_hom _ _ _) x) r) (y1 + y2)%PC]
            /(path_fun ((f : icones_hom _ _ _) x) r (y1 + y2)%PC).
  by rewrite HD.
- move=> s y; apply: path_eq => r /=; apply: linhom_eq => x.
  rewrite swap_innerE.
  rewrite [linhom_fun (s *: swap_inner f r y)%PC x]/linhom_fun /= /linhom_scale_fun.
  rewrite -!/(linhom_fun (swap_inner f r y) x) !swap_innerE.
  have [_ _ HZ] :=
    linhom_pre_linear (linhom_pre_of (path_fun ((f : icones_hom _ _ _) x) r)).
  rewrite -[linhom_fun (path_fun ((f : icones_hom _ _ _) x) r) (s *: y)%PC]
            /(path_fun ((f : icones_hom _ _ _) x) r (s *: y)%PC).
  by rewrite HZ.
Qed.

Lemma lfps_norm_le (y : C) : cone_norm (lfps y) <= cone_norm y.
Proof.
rewrite /cone_norm /=.
apply: ge_sup; first exact: path_normset_nonempty.
move=> _ [r ->] /=.
rewrite -[cnorm (swap_inner f r y)]/(linhom_norm (swap_inner f r y)).
apply: linhom_norm_sup_lub => x Hx.
rewrite swap_innerE.
have Hphi : cone_norm (path_fun ((f : icones_hom _ _ _) x) r) <= 1.
  apply: le_trans (path_norm_ub ((f : icones_hom _ _ _) x) r) _.
  apply: le_trans (cones_hom_norm_le1 (mcones_hom_cones (icones_hom_mcones f)) x) _.
  exact: Hx.
by have := linhom_norm_apply_le Hphi y; rewrite mul1r.
Qed.

Lemma lfps_bounded :
  exists M : R, forall y : C, cnorm y <= 1 -> cnorm (lfps y) <= M.
Proof. by exists 1 => y Hy; apply: le_trans (lfps_norm_le y) _. Qed.

(** Helper: for a fixed [r], the inner map [y ↦ swap_inner f r y : B⊸D] is
    ω-continuous in [y].  Reduce via [linhom_mcone_M_sep] on the codomain
    [B⊸D]: an arity-0 test is [β ▷ mD]; the value at [swap_inner f r y] is
    [mD(s, f(β s)(r)(y))], and [φ := path_fun (f (β s)) r : C⊸D] is itself
    ω-continuous, so both sides collapse to [sup_n mD(s, φ(u n))] —
    LHS via [φ]'s ω-continuity + [eval_at_test_sup_ball], RHS via the
    [B⊸D]-sup-ball law [linhom_sup_fun_test_sup]. *)
Lemma swap_inner_continuous (r : ar_carrier Ar X) :
  is_omega_continuous (fun y => swap_inner f r y).
Proof.
move=> u uch ub1 fuch fub1.
apply: (@linhom_mcone_M_sep _ _ B D) => p [β [βub [mD [mDM Hp]]]].
rewrite Hp /linhom_test /linhom_test_fun /=.
set s := ar_zero_pt Ar.
rewrite swap_innerE.
(* φ := path_fun (f (β s)) r : C⊸D, ω-continuous in its argument. *)
set φ := path_fun ((f : icones_hom _ _ _) (path_fun β s)) r.
have φcont : is_omega_continuous (linhom_fun φ).
  by rewrite -[linhom_fun φ]/(linhom_pre_fun (linhom_pre_of φ));
     exact: linhom_pre_continuous.
(* RHS: the [B⊸D]-sup-ball applied at [β s] is the [linhom_sup_fun]. *)
rewrite (linhom_sup_fun_test_sup (u := [eta swap_inner f r] \o u)
           fuch fub1 mD s (path_fun β s)).
(* LHS: φ (cone_sup_ball u …) = cone_sup_ball (φ∘u) … by ω-cont of φ. *)
have Hch : forall n, precone_le (linhom_fun φ (u n)) (linhom_fun φ (u n.+1)).
  move=> n; have [w Hw] := uch n.
  exists (linhom_fun φ w).
  have [_ HD _] := linhom_pre_linear (linhom_pre_of φ).
  by rewrite Hw -[linhom_fun φ _]/(φ _) HD.
have φnorm : linhom_norm φ <= 1.
  rewrite /φ.
  apply: le_trans (path_norm_ub ((f : icones_hom _ _ _) (path_fun β s)) r) _.
  apply: le_trans
    (cones_hom_norm_le1 (mcones_hom_cones (icones_hom_mcones f)) (path_fun β s)) _.
  by apply: le_trans (path_norm_ub β s) _; exact: βub.
have Hub : forall n, cone_norm (linhom_fun φ (u n)) <= 1.
  move=> n; apply: le_trans (linhom_norm_apply_le (lexx _) (u n)) _.
  rewrite -[X in _ <= X]mulr1; apply: ler_pM;
    [exact: linhom_norm_ge0|exact: cone_norm_ge0|exact: φnorm|exact: ub1].
rewrite (φcont u uch ub1 Hch Hub).
rewrite (eval_at_test_sup_ball Hch Hub mD s).
congr (sup _); apply: eq_imagel => n _ /=.
by rewrite swap_innerE.
Qed.

(** ω-continuity of [lfps] (into the [Path] codomain).  [cone_sup_ball]
    in [Path(X, B⊸D)] is pointwise ([path_sup_ball_fun]); the value at
    [r] of [lfps] is [swap_inner f r], so the identity reduces, at each
    [r], to [swap_inner_continuous r] (modulo [cone_sup_ball_irr]). *)
Lemma lfps_continuous : is_omega_continuous lfps.
Proof.
move=> u uch ub1 fuch fub1.
apply: path_eq => r /=.
rewrite /path_sup_ball_fun.
rewrite (swap_inner_continuous uch ub1
  (path_sup_ball_chain_pw fuch r) (path_sup_ball_ub1_pw fub1 r)).
exact: cone_sup_ball_irr.
Qed.

(** Path-preservation of [lfps]: for a measurable [C]-path [δ : W → C],
    [w ↦ lfps (δ w)] is a measurable path of [Path(X, B⊸D)].

    Reduce via the [Path(X,B⊸D)] test family: a test is [φ ▷ m] with
    [φ : Z → X] an arrow and [m] a [B⊸D]-test [= β ▷ mD].  The value at
    [lfps (δ w)] is [mD(s, f(β s)(φ s)(δ w))].  We obtain its joint
    measurability in [(s, w)] by testing the [Path(X,C⊸D)]-path
    [s ↦ f(β s)] (which [f] preserves), reindexed to the product arity
    [Z × W], against the test that picks the [X]-coordinate via
    [φ ∘ fst], evaluates the inner [C⊸D] at the rescaled [δ ∘ snd]
    (unit ball), and tests [D] with [mD ∘ fst]; then pull back along the
    diagonal and rescale. *)
Lemma lfps_pres_path
    (W : ar_obj Ar) (δ : ar_carrier Ar W -> C) :
  is_measurable_path δ ->
  is_measurable_path (fun w => lfps (δ w)).
Proof.
move=> Hδ.
have [[Mδ HMδ] Hδm] := Hδ.
have Mδ_ge0 : 0 <= Mδ.
  by apply: le_trans (HMδ (ar_point Ar W)); exact: cone_norm_ge0.
split.
  exists Mδ => w.
  by apply: le_trans (lfps_norm_le (δ w)) _; exact: HMδ.
move=> Z p [φ [m [mM ->]]].
have [β [βub [mD [mDM Hm]]]] : linhom_mcone_M (Y := Z) m by exact: mM.
subst m.
(* The [Path(X,C⊸D)]-path [s ↦ f(β s)], which [f] preserves. *)
have Hfβ : is_measurable_path (fun s => (f : icones_hom _ _ _) (path_fun β s)).
  exact: (mcones_hom_pres_path (icones_hom_mcones f) Z (path_fun β) (path_is_path β)).
(* Rescale [δ] into the unit ball uniformly by [(Mδ+1)⁻¹]. *)
have S_pos : 0 < Mδ + 1 by apply: le_lt_trans Mδ_ge0 _; rewrite ltrDl ltr01.
have Sinv_ge0 : 0 <= (Mδ + 1)^-1 by rewrite invr_ge0 ltW.
pose Sinv : {nonneg R} := NngNum Sinv_ge0.
(* Reindex [f(β ·)] (over Z) to a path at arity [ar_prod Z W] picking Z. *)
pose Pfst : ar_carrier Ar (ar_prod Ar Z W) -> path_car Ar X (linhom_car Ar C D)
  := fun q => (f : icones_hom _ _ _) (path_fun β (ar_prod_fst Z W q)).
have HPfst : is_measurable_path Pfst.
  exact: (reindex_path_measurable (ar_prod_fst Z W) Hfβ).
(* The rescaled [C]-path [δ ∘ snd] at arity [ar_prod Z W], unit ball. *)
pose δsnd : ar_carrier Ar (ar_prod Ar Z W) -> C :=
  fun q => precone_scale Sinv (δ (ar_prod_snd Z W q)).
have Hδscaled : is_measurable_path (fun w => precone_scale Sinv (δ w)).
  exact: (path_scale_is_path Sinv (MkPath Hδ)).
have Hδsnd : is_measurable_path δsnd.
  exact: (reindex_path_measurable (ar_prod_snd Z W) Hδscaled).
pose δA : path_car Ar (ar_prod Ar Z W) C := MkPath Hδsnd.
have δA_ub : cone_norm δA <= 1.
  rewrite /cone_norm /=.
  apply: ge_sup; first exact: path_normset_nonempty.
  move=> _ [q ->] /=.
  rewrite /δsnd cone_normh /=.
  rewrite mulrC ler_pdivrMr // mul1r.
  by apply: le_trans (HMδ (ar_prod_snd Z W q)) _; rewrite lerDl.
(* The C⊸D-test: evaluate at δA, test with mD reindexed to pick Z. *)
pose mDfst : test_of Ar (ar_prod Ar Z W) D := test_reindex (ar_prod_fst Z W) mD.
have mDfstM : mcone_M (ar_prod Ar Z W) mDfst by exact: mcone_M_comp.
pose mCD : test_of Ar (ar_prod Ar Z W) (linhom_car Ar C D) :=
  linhom_test δA δA_ub mDfst mDfstM.
have mCDM : mcone_M (ar_prod Ar Z W) mCD.
  by exists δA, δA_ub, mDfst, mDfstM.
(* The Path(X,C⊸D)-test picking X-coordinate via [φ ∘ fst]. *)
pose φfst : ar_hom Ar (ar_prod Ar Z W) X :=
  [the {mfun _ >-> _} of φ \o ar_prod_fst Z W].
pose mP : test_of Ar (ar_prod Ar Z W) (path_car Ar X (linhom_car Ar C D)) :=
  path_test φfst mCD mCDM.
have mPM : mcone_M (ar_prod Ar Z W) mP by exists φfst, mCD, mCDM.
have [_ HPfstm] := HPfst.
have HPtest := HPfstm (ar_prod Ar Z W) mP mPM.
pose ψ (sw : (ar_carrier Ar Z * ar_carrier Ar W)%type) :
  (ar_carrier Ar (ar_prod Ar Z W) * ar_carrier Ar (ar_prod Ar Z W))%type :=
  (ar_prod_cast (sw.1, sw.2), ar_prod_cast (sw.1, sw.2)).
have ψ_meas : measurable_fun [set: (ar_carrier Ar Z * ar_carrier Ar W)%type] ψ.
  apply: measurable_fun_pair.
  - apply: (measurableT_comp (ar_prod_cast_meas Ar Z W)).
    by apply: measurable_fun_pair; [exact: measurable_fst|exact: measurable_snd].
  - apply: (measurableT_comp (ar_prod_cast_meas Ar Z W)).
    by apply: measurable_fun_pair; [exact: measurable_fst|exact: measurable_snd].
rewrite (_ : (fun p0 : (ar_carrier Ar Z * ar_carrier Ar W)%type =>
                path_test φ (linhom_test β βub mD mDM) mM p0.1 (lfps (δ p0.2))) =
             (fun sw : (ar_carrier Ar Z * ar_carrier Ar W)%type =>
                (Mδ + 1) * (mP (ψ sw).1 (Pfst (ψ sw).2)))); last first.
  apply: funext => sw.
  rewrite /ψ /mP /Pfst /path_test /= /path_test_fun /=.
  rewrite /mCD /linhom_test /linhom_test_fun /= /δA /=.
  rewrite /mDfst /test_reindex /test_reindex_fun /=.
  rewrite /φfst /=.
  rewrite /ar_prod_fst /ar_prod_fst_fun /ar_prod_snd /ar_prod_snd_fun !ar_prod_castK /=.
  rewrite /lfps /= swap_innerE.
  have Hδeval : δsnd (ar_prod_cast (sw.1, sw.2)) = (Sinv *: δ sw.2)%PC.
    by rewrite /δsnd /= /ar_prod_snd_fun ar_prod_castK.
  rewrite Hδeval.
  have [_ _ HZ] :=
    linhom_pre_linear (linhom_pre_of (path_fun ((f : icones_hom _ _ _) (β sw.1)) (φ sw.1))).
  rewrite -[linhom_fun (path_fun _ (φ sw.1)) (Sinv *: δ sw.2)%PC]
            /((path_fun ((f : icones_hom _ _ _) (β sw.1)) (φ sw.1)) (Sinv *: δ sw.2)%PC).
  rewrite HZ /= test_linZ /=.
  by rewrite mulrA mulfV ?mul1r // gt_eqF.
apply: measurable_funM; first exact: measurable_cst.
exact: (measurable_comp (F := setT) measurableT (subsetT _) HPtest ψ_meas).
Qed.

(** Integral-preservation of [lfps]: [lfps (∫δ) = ∫ (lfps ∘ δ)] in
    [Path(X, B⊸D)].  By [icone_integral_eqP] it suffices to check the
    Pettis specification at arity-0 path-tests [const_r r ▷ (β ▷ mD)].
    The value at [lfps z] reduces (via [lfpsE]) to [mD(z, φ(z'))] with
    [φ := f(β z')(r) : C⊸D] (a genuine integral-preserving [linhom]) and
    [z' ∈ C], so both sides equal [fine ∫ mD(z, φ(δ w)) dµ] — the LHS via
    [φ]'s integral law + the [D]-integral Pettis spec, the RHS via the
    section-integral identity. *)
Lemma lfps_pres_int
    (W : ar_obj Ar) (δ : ar_carrier Ar W -> C)
    (Hδ : is_measurable_path δ) (µ : fmeas R (ar_carrier Ar W)) :
  lfps (icone_integral δ Hδ µ) =
  icone_integral (fun w => lfps (δ w)) (lfps_pres_path Hδ) µ.
Proof.
apply: icone_integral_eqP => p pM z.
have [φa [m [mM ->]]] : path_mcone_M (Y := ar_zero Ar) p by exact: pM.
have [β [βub [mD [mDM Hm]]]] : linhom_mcone_M (Y := ar_zero Ar) m by exact: mM.
subst m.
(* φ := f(β (φa z))(r) where r := φa z : the X-coordinate of the path test. *)
set r := φa z.
set φ := path_fun ((f : icones_hom _ _ _) (path_fun β z)) r.
(* LHS reduces to [mD z (φ (∫δ))]. *)
have LE : test_fun (path_test φa (linhom_test β βub mD mDM) mM) z
            (lfps (icone_integral δ Hδ µ)) =
          test_fun mD z (linhom_fun φ (icone_integral δ Hδ µ)).
  rewrite /path_test /= /path_test_fun /=
          /linhom_test /linhom_test_fun /= /lfps /= swap_innerE.
  by [].
rewrite LE.
(* [φ (∫δ) = ∫ (φ ∘ δ)] by [φ]'s integral law. *)
rewrite -[linhom_fun φ (icone_integral δ Hδ µ)]/(φ (icone_integral δ Hδ µ)).
rewrite (linhom_pres_int φ W δ Hδ µ).
(* The [D]-integral Pettis spec against [mD]. *)
rewrite (icone_integralP _ (linhom_pre_pres_path φ W δ Hδ) µ mD mDM z).
(* The integrands match pointwise. *)
congr (fine _); apply: eq_integral => w _; congr (_%:E).
rewrite /path_test /= /path_test_fun /=
        /linhom_test /linhom_test_fun /= /lfps /= swap_innerE.
by [].
Qed.

(** [lfun_path_swap f : ICones(C, Path(X, B⊸D))], assembled from the five
    [lfps] fields (Paper [lemma:lfun-path-swap]). *)
Definition lfps_cones : cones_hom C PBD :=
  ConesHom lfps lfps_linear lfps_continuous lfps_norm_le.

Definition lfps_mcones : mcones_hom Ar C PBD :=
  MkMConesHom lfps_cones (fun W δ Hδ => lfps_pres_path (W:=W) (δ:=δ) Hδ).

Lemma lfps_mcones_pres_int
    (W : ar_obj Ar) (δ : ar_carrier Ar W -> C)
    (Hδ : is_measurable_path δ) (µ : fmeas R (ar_carrier Ar W)) :
  cones_hom_fun (mcones_hom_cones lfps_mcones) (icone_integral δ Hδ µ) =
  icone_integral
    (fun w => cones_hom_fun (mcones_hom_cones lfps_mcones) (δ w))
    (mcones_hom_pres_path lfps_mcones W δ Hδ) µ.
Proof.
rewrite -[cones_hom_fun _ _]/(lfps (icone_integral δ Hδ µ)) (lfps_pres_int Hδ µ).
by congr icone_integral; exact: Prop_irrelevance.
Qed.

Definition lfun_path_swap : icones_hom Ar C PBD :=
  MkIConesHom lfps_mcones lfps_mcones_pres_int.

Lemma lfun_path_swapE (y : C) (r : ar_carrier Ar X) (x : B) :
  linhom_fun (path_fun ((lfun_path_swap : icones_hom _ _ _) y) r) x =
  linhom_fun (path_fun ((f : icones_hom _ _ _) x) r) y.
Proof. by rewrite -[(lfun_path_swap : icones_hom _ _ _) y]/(lfps y) lfpsE. Qed.

End LfunPathSwap.

Arguments lfps {R Ar X B C D} f y.
Arguments lfpsE {R Ar X B C D} f y r x.
Arguments lfun_path_swap {R Ar X B C D} f.
Arguments lfun_path_swapE {R Ar X B C D} f y r x.


(** ** Prereq for P3/P5 — the unit iso [1 ⊸ C ≅ C] ([linhom_one_iso])

    Paper §5.5 (Eq 5.3 ingredient): the canonical iso of integrable
    cones [1 ⊸ C ≅ C], with forward "evaluate at the unit [1 ∈ R≥0]"
    and inverse the "linear point" [c ↦ (s ↦ (c1_val s) ·: c)].  Both
    directions are genuine [icones_hom]s.  Needed for P3 (the
    [1 ↔ 1⊸1] bridge in [path_tens_to_one]) and later for the unitors
    [λ]/[ρ]. *)

(** *** The "linear point" inner map [lin_pt c : 1 ⊸ C]

    For a fixed [c : C], the map [s ↦ (c1_val s) ·: c] from the unit
    cone to [C].  Structurally identical to [tensor_hom_iso]'s
    [line_fun] (a fixed vector scaled by the unit-cone variable), with
    codomain a plain ICone [C] rather than an internal hom. *)

Section LinPt.
Variables (R : realType) (Ar : MeasSubcat R).
Variable C : ICone.type Ar.
Variable c : C.
Local Notation One := (cone_one_car Ar).

Definition lin_pt_fun (s : One) : C := precone_scale (c1_val s) c.

Lemma lin_pt_linear : is_linear lin_pt_fun.
Proof.
rewrite /lin_pt_fun; split.
- by rewrite (_ : c1_val (0%PC : One) = 0%:nng) ?precone_scale_0l //.
- by move=> x y; rewrite -precone_scale_DAl; congr precone_scale.
- by move=> r x; rewrite -precone_scale_A; congr precone_scale.
Qed.

Lemma lin_pt_norm_le (s : One) :
  cone_norm (lin_pt_fun s) <= cone_norm s * cone_norm c.
Proof.
rewrite /lin_pt_fun cone_normh.
by rewrite -[cone_norm s]/((c1_val s)%:num).
Qed.

Lemma lin_pt_bounded :
  exists M : R, forall s : One, cnorm s <= 1 -> cnorm (lin_pt_fun s) <= M.
Proof.
exists (cone_norm c) => s Hs.
apply: le_trans (lin_pt_norm_le s) _.
by rewrite -[X in _ <= X]mul1r; apply: ler_wpM2r => //; exact: cone_norm_ge0.
Qed.

(** ω-continuity in [s]: mirrors [tensor_hom_iso.line_continuous]; the
    sup commutes with scaling a fixed vector by the unit-cone variable. *)
Lemma lin_pt_continuous : is_omega_continuous lin_pt_fun.
Proof.
move=> u uch ub1 fuch fub1.
set L := c1_val (cone_sup_ball u uch ub1).
set sb := cone_sup_ball (lin_pt_fun \o u) fuch fub1.
have HuL : forall n, ((c1_val (u n))%:num <= L%:num)%R.
  move=> n.
  have := cone_sup_ball_ub u uch ub1 n.
  by move=> /(cone_normp _ _); rewrite /cone_norm /= /c1_norm /=.
have s_le : (sb <=p lin_pt_fun (cone_sup_ball u uch ub1))%PC.
  apply: cone_sup_ball_lub => n; apply: (linear_increasing (lin_pt_linear)).
  exact: cone_sup_ball_ub.
apply/esym/precone_le_anti => //.
have [t Ht] := s_le.
have t_bound : forall n,
    (cone_norm t <= (L%:num - (c1_val (u n))%:num) * cone_norm c)%R.
  move=> n.
  have [w Hw] : (lin_pt_fun (u n) <=p sb)%PC by exact: cone_sup_ball_ub.
  have dn_ge0 : (0 <= L%:num - (c1_val (u n))%:num)%R by rewrite subr_ge0 HuL.
  pose dn : {nonneg R} := NngNum dn_ge0.
  have E1 : lin_pt_fun (cone_sup_ball u uch ub1) =
            (lin_pt_fun (u n) + precone_scale dn c)%PC.
    rewrite /lin_pt_fun -[(_ + _)%PC]/(precone_add (precone_scale (c1_val (u n)) c)
                                       (precone_scale dn c)).
    rewrite -precone_scale_DAl; congr (precone_scale _ c); apply: val_inj => /=.
    by rewrite addrC subrK.
  have E2 : lin_pt_fun (cone_sup_ball u uch ub1) =
            (lin_pt_fun (u n) + (w + t))%PC.
    by rewrite Ht Hw -precone_addA.
  have Heq : precone_scale dn c = (w + t)%PC.
    by apply: (@precone_cancel _ _ (lin_pt_fun (u n))); rewrite -E1 -E2.
  have t_le : (t <=p precone_scale dn c)%PC.
    by rewrite Heq precone_addC; exists w.
  have := cone_normp _ _ t_le.
  by rewrite cone_normh.
have LsupE : L%:num = sup [set (c1_val (u n))%:num | n in [set: nat]].
  exact: c1_sup_ball_E.
have t_norm0 : (cone_norm t <= 0)%R.
  apply/unstable.ler_gtP => e e_pos.
  have hs : has_sup [set (c1_val (u n))%:num | n in [set: nat]].
    split; first by exists (c1_val (u 0%N))%:num, 0%N.
    by exists 1 => _ [n _ <-]; have := ub1 n; rewrite /cone_norm /= /c1_norm /=.
  set nc := cone_norm c.
  have nc_ge0 : (0 <= nc)%R by exact: cone_norm_ge0.
  have den_pos : (0 < nc + 1)%R by rewrite ltr_pwDr // ler01.
  have e'_pos : (0 < e / (nc + 1))%R by rewrite divr_gt0.
  have [a [n _ Hae] Ha] := sup_adherent e'_pos hs.
  move: Ha; rewrite -Hae -LsupE => Ha.
  apply: le_trans (t_bound n) _.
  rewrite -/nc.
  apply: le_trans (_ : (e / (nc + 1)) * nc <= e)%R.
    rewrite ler_wpM2r //; apply: ltW.
    by rewrite ltrBlDr addrC -ltrBlDr.
  rewrite -mulrA ler_piMr ?ltW //.
  rewrite mulrC ltr_pdivrMr // mul1r ltrDl.
  exact: ltr01.
have t0 : t = precone_zero.
  by apply: cone_normz; apply/le_anti; rewrite t_norm0 cone_norm_ge0.
by rewrite Ht t0 precone_addr0; exact: precone_le_refl.
Qed.

(** Path-preservation in [s]: tests of [C] are arbitrary [m]; the
    pulled-back test of [lin_pt c ∘ γ] factors as
    [c1_val(γ s) · m(s, c)] — a product of two measurable functions. *)
Lemma lin_pt_pres_path (X : ar_obj Ar) (γ : ar_carrier Ar X -> One) :
  is_measurable_path γ ->
  is_measurable_path (fun s => lin_pt_fun (γ s)).
Proof.
move=> Hγ.
have [[M HM] _] := Hγ.
split.
  exists (M * cone_norm c) => s.
  apply: le_trans (lin_pt_norm_le (γ s)) _.
  by apply: ler_wpM2r; [exact: cone_norm_ge0|exact: HM].
move=> Y m mM.
have -> : (fun q : (ar_carrier Ar Y * ar_carrier Ar X)%type =>
            test_fun m q.1 (lin_pt_fun (γ q.2))) =
          (fun q => (c1_val (γ q.2))%:num * test_fun m q.1 c).
  by apply: funext => q; rewrite /lin_pt_fun test_linZ.
rewrite [X in measurable_fun _ X](_ : _ =
  ((fun s => test_fun m s c) \o fst) \*
  ((fun s => (c1_val (γ s))%:num) \o snd)); last first.
  by apply: funext => q; rewrite /GRing.mul /= mulrC.
apply: measurable_funM.
- apply: (measurable_comp (F := setT) measurableT (subsetT _) _ measurable_fst).
  have Hconst := @const_path_measurable R Ar C Y c.
  have [_ Hcm] := Hconst.
  have Hbase := Hcm Y m mM.
  have -> : (fun s : ar_carrier Ar Y => test_fun m s c) =
            (fun p : ar_carrier Ar Y * ar_carrier Ar Y => test_fun m p.1 c)
              \o (fun s => (s, s)).
    by apply: funext.
  apply: (measurable_comp (F := setT) measurableT (subsetT _) Hbase).
  by apply: measurable_fun_pair; exact: measurable_id.
- apply: (measurable_comp (F := setT) measurableT (subsetT _) _ measurable_snd).
  exact: (measurable_test_path_section (B := cone_one_car Ar)
            (m := ConeOneMConeAux.id_test (R:=R) (Ar:=Ar) (ar_zero Ar))
            (erefl) Hγ (ar_zero_pt Ar)).
Qed.

Definition lin_pt_pre : linhom_pre Ar One C :=
  MkLinhomPre lin_pt_fun lin_pt_linear lin_pt_continuous
              lin_pt_bounded
              (fun X g Hg => lin_pt_pres_path (X:=X) (γ:=g) Hg).

(** Integral-preservation in [s]: by [icone_integral_eqP] on [C]; the
    obligation reduces (via [test_linZ] + the [1]-cone integral
    [icone_integralP] against [id_test]) to the scalar identity
    [c1_val(∫β) · K = ∫ (c1_val(β s) · K)]. *)
Lemma lin_pt_pres_int
  (X : ar_obj Ar) (β : ar_carrier Ar X -> One)
  (Hβ : is_measurable_path β) (µ : fmeas R (ar_carrier Ar X)) :
  linhom_pre_fun lin_pt_pre (icone_integral β Hβ µ) =
  icone_integral
    (fun s => linhom_pre_fun lin_pt_pre (β s))
    (linhom_pre_pres_path lin_pt_pre X β Hβ) µ.
Proof.
apply: icone_integral_eqP => p pM s.
rewrite /= /lin_pt_fun test_linZ.
set K : R := test_fun p s c.
have HcInt : (c1_val (icone_integral β Hβ µ))%:num =
  fine (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X])
          ((c1_val (β r))%:num)%:E).
  have := icone_integralP β Hβ µ
            (ConeOneMConeAux.id_test (R:=R) (Ar:=Ar) (ar_zero Ar)) erefl
            (ar_zero_pt Ar).
  by [].
rewrite HcInt.
rewrite [in RHS](eq_integral (fun r => (((c1_val (β r))%:num)%:E * K%:E)%E));
  last by move=> r _; rewrite /= test_linZ -/K -EFinM.
have Hmeas_c : measurable_fun [set: ar_carrier Ar X]
    (fun x : ar_carrier Ar X => ((c1_val (β x))%:num)%:E).
  apply/measurable_EFinP.
  exact: (measurable_test_path_section (B := cone_one_car Ar)
            (m := ConeOneMConeAux.id_test (R:=R) (Ar:=Ar) (ar_zero Ar))
            (erefl) Hβ (ar_zero_pt Ar)).
have [Mb HMb] : exists M : R, forall r, ((c1_val (β r))%:num <= M)%R.
  by have := Hβ; case=> -[Mb HMb] _; exists Mb => r;
     have := HMb r; rewrite /cone_norm /= /c1_norm /=.
have Kge0 : (0 <= K)%R by rewrite /K; exact: test_ge0.
have Hfin : (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X])
              ((c1_val (β r))%:num)%:E < +oo)%E.
  apply: (@le_lt_trans _ _
    (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X]) Mb%:E)%E).
    apply: (ge0_le_integral _ measurableT _ Hmeas_c (measurable_cst _)).
    - by move=> r _; rewrite lee_fin.
    - by move=> r _; rewrite lee_fin HMb.
  rewrite -[(fun=> Mb%:E)]/(cst Mb%:E) lebesgue_integral_nonneg.integral_cst//.
  by rewrite ltey_eq fin_numM// fmeas_setT_fin.
rewrite lebesgue_integral_nonneg.ge0_integralZr//;
  try by move=> r _; rewrite lee_fin.
rewrite fineM//.
by rewrite ge0_fin_numE//; apply: integral_ge0 => r _; rewrite lee_fin.
Qed.

Definition lin_pt : linhom_car Ar One C :=
  MkLinhom lin_pt_pre lin_pt_pres_int.

Lemma lin_ptE (s : One) :
  linhom_fun lin_pt s = precone_scale (c1_val s) c.
Proof. by []. Qed.

(** [lin_pt c] evaluated at the unit [1] is [c]. *)
Lemma lin_pt_unit :
  linhom_fun lin_pt (MkConeOne Ar 1%:nng) = c.
Proof. by rewrite lin_ptE (_ : c1_val _ = 1%:nng) ?precone_scale_1. Qed.

End LinPt.

Arguments lin_pt {R Ar C} c.
Arguments lin_ptE {R Ar C} c s.
Arguments lin_pt_unit {R Ar C} c.


(** *** The unit iso [1 ⊸ C ≅ C] ([linhom_one_iso])

    Forward [eval1] = "evaluate at the unit [1]" (= [eval_at 1], norm
    [≤ 1]); backward [lo_lift] = the linear-point map [c ↦ lin_pt c].
    Both are genuine [icones_hom]s; the round-trips are
    [eval1 (lin_pt c) = c] ([lin_pt_unit]) and
    [lin_pt (φ 1) = φ] (linearity of [φ] in the unit-cone argument). *)

Section LinhomOneIso.
Variables (R : realType) (Ar : MeasSubcat R).
Variable C : ICone.type Ar.
Local Notation One := (cone_one_car Ar).
Local Notation L := (linhom_car Ar One C).

(** The unit element [1 ∈ 1 = R≥0]. *)
Definition c1_one : One := MkConeOne Ar 1%:nng.

(** **** Forward: evaluate at the unit *)

Lemma eval1_norm : cone_norm (eval_at c1_one : linhom_car Ar L C) <= 1.
Proof.
rewrite -[cone_norm _]/(linhom_norm _).
apply: linhom_norm_sup_lub => φ Hφ.
rewrite eval_atE.
apply: le_trans (linhom_norm_apply_le (lexx _) _) _.
rewrite (_ : cone_norm c1_one = 1); first by rewrite mulr1.
by rewrite /cone_norm /= /c1_norm /=.
Qed.

Definition eval1 : icones_hom Ar L C := linhom_icones (eval_at c1_one) eval1_norm.

Lemma eval1E (φ : L) : eval1 φ = linhom_fun φ c1_one.
Proof. by rewrite -[eval1 φ]/(hfun (linhom_icones _ _) φ) linhom_iconesE eval_atE. Qed.

(** **** Backward: the linear-point map [c ↦ lin_pt c] *)

Lemma lo_lift_linear : is_linear (lin_pt (C:=C)).
Proof.
split.
- apply: linhom_eq => s; rewrite lin_ptE precone_scale_0r.
  by rewrite -[linhom_fun _ s]/(linhom_fun (linhom_zero One C) s).
- move=> x y; apply: linhom_eq => s.
  rewrite lin_ptE.
  rewrite -[linhom_fun (lin_pt x + lin_pt y)%PC s]
            /(linhom_add_fun (lin_pt x) (lin_pt y) s).
  rewrite /linhom_add_fun /= !lin_ptE.
  by rewrite precone_scale_DAr.
- move=> r x; apply: linhom_eq => s.
  rewrite lin_ptE.
  rewrite -[linhom_fun (r *: lin_pt x)%PC s]/(linhom_scale_fun r (lin_pt x) s).
  rewrite /linhom_scale_fun /= !lin_ptE.
  rewrite -!precone_scale_A; congr precone_scale.
  apply: val_inj => /=.
  by rewrite !nng_mulE mulrC.
Qed.

Lemma lo_lift_norm_le1 (c : C) : cone_norm (lin_pt c) <= cone_norm c.
Proof.
rewrite -[cone_norm (lin_pt c)]/(linhom_norm (lin_pt c)).
apply: linhom_norm_sup_lub => s Hs.
rewrite lin_ptE.
rewrite cone_normh -[X in _ <= X]mul1r.
apply: ler_wpM2r; first exact: cone_norm_ge0.
by rewrite -[(c1_val s)%:num]/(cone_norm s).
Qed.

(** ω-continuity in [c]: via [linhom_mcone_M_sep] + [linhom_sup_fun_test_sup];
    each [C]-test reduces (via [test_linZ]) to scaling the [C]-sup. *)
Lemma lo_lift_continuous : is_omega_continuous (lin_pt (C:=C)).
Proof.
move=> u uch ub1 fuch fub1.
apply: (@linhom_mcone_M_sep _ _ One C) => p [δ [δub [m [mM Hp]]]].
rewrite Hp /linhom_test /linhom_test_fun /=.
set s := ar_zero_pt Ar.
rewrite lin_ptE.
rewrite (linhom_sup_fun_test_sup (u := [eta lin_pt (C:=C)] \o u)
           fuch fub1 m s (path_fun δ s)).
rewrite test_linZ.
rewrite (eval_at_test_sup_ball uch ub1 m s).
rewrite [in RHS](_ :
  [set m s (linhom_fun (([eta lin_pt] \o u) n) (path_fun δ s)) | n in [set: nat]] =
  [set (c1_val (path_fun δ s))%:num * m s (u n) | n in [set: nat]]); last first.
  by apply: eq_imagel => n _ /=; rewrite lin_ptE test_linZ.
have HsupS : has_sup [set m s (u n) | n in [set: nat]].
  split; first by exists (m s (u 0%N)), 0%N.
  by exists 1 => _ [n _ <-]; apply: le_trans (test_le1 m s (ub1 n)).
rewrite sup_scaleM //.
- congr (sup _); rewrite eqEsubset; split.
    by move=> _ [_ [n _ <-] <-]; exists n.
  by move=> _ [n _ <-]; exists (m s (u n)) => //; exists n.
- by case: HsupS.
- by case: HsupS.
Qed.

Lemma lo_lift_bounded :
  exists M : R, forall c : C, cnorm c <= 1 -> cnorm (lin_pt c) <= M.
Proof. by exists 1 => c Hc; apply: le_trans (lo_lift_norm_le1 c) _. Qed.

(** Path-preservation in [c]: tests of [1⊸C] are [δ ▷ m]; the value at
    [lin_pt (γ w)] factors as [c1_val(δ s) · m(s, γ w)] — a product of a
    measurable [s]-function and the jointly-measurable [m(s, γ w)]. *)
Lemma lo_lift_pres_path (W : ar_obj Ar) (γ : ar_carrier Ar W -> C) :
  is_measurable_path γ ->
  is_measurable_path (fun w => lin_pt (γ w)).
Proof.
move=> Hγ.
have [[M HM] Hγm] := Hγ.
split.
  exists M => w; apply: le_trans (lo_lift_norm_le1 (γ w)) _; exact: HM.
move=> Y p [δ [δub [m [mM ->]]]].
rewrite /linhom_test /=.
have -> : (fun q : (ar_carrier Ar Y * ar_carrier Ar W)%type =>
            linhom_test_fun δ m q.1 (lin_pt (γ q.2))) =
          (fun q => (c1_val (path_fun δ q.1))%:num * test_fun m q.1 (γ q.2)).
  by apply: funext => q; rewrite /linhom_test_fun /= lin_ptE test_linZ.
rewrite [X in measurable_fun _ X](_ : _ =
  ((fun s => (c1_val (path_fun δ s))%:num) \o fst) \*
  (fun q => test_fun m q.1 (γ q.2))); last first.
  by apply: funext => q.
apply: measurable_funM.
- apply: (measurable_comp (F := setT) measurableT (subsetT _) _ measurable_fst).
  exact: (measurable_test_path_section (B := cone_one_car Ar)
            (m := ConeOneMConeAux.id_test (R:=R) (Ar:=Ar) (ar_zero Ar))
            (erefl) (path_is_path δ) (ar_zero_pt Ar)).
- exact: (Hγm Y m mM).
Qed.

Definition lo_lift_pre : linhom_pre Ar C L :=
  MkLinhomPre (lin_pt (C:=C)) lo_lift_linear lo_lift_continuous
              lo_lift_bounded
              (fun W g Hg => lo_lift_pres_path (W:=W) (γ:=g) Hg).

(** Integral-preservation in [c]: by [icone_integral_eqP] on [1⊸C]; tests
    are [δ ▷ m], for which the obligation reduces (via [test_linZ] + the
    [C]-integral Pettis spec) to the scalar identity
    [c1_val(δ s) · m(s, ∫γ) = ∫ (c1_val(δ s) · m(s, γ w))]. *)
Lemma lo_lift_pres_int (W : ar_obj Ar) (γ : ar_carrier Ar W -> C)
  (Hγ : is_measurable_path γ) (µ : fmeas R (ar_carrier Ar W)) :
  linhom_pre_fun lo_lift_pre (icone_integral γ Hγ µ) =
  icone_integral
    (fun w => linhom_pre_fun lo_lift_pre (γ w))
    (linhom_pre_pres_path lo_lift_pre W γ Hγ) µ.
Proof.
apply: icone_integral_eqP => p pM s.
have [δ [δub [m [mM ->]]]] : linhom_mcone_M (Y := ar_zero Ar) p by exact: pM.
rewrite /= /linhom_test /linhom_test_fun /= !lin_ptE !test_linZ.
set Ks : R := (c1_val (path_fun δ s))%:num.
(* LHS: Ks * m(s, ∫γ) = Ks * ∫ m(s, γ w) by the C-integral Pettis spec. *)
rewrite (icone_integralP γ Hγ µ m mM s).
(* The integrand of the [C]-section [r ↦ m s (γ r)] is bounded measurable. *)
have meas_g : measurable_fun [set: ar_carrier Ar W]
    (fun w => (test_fun m s (γ w))%:E).
  apply/measurable_EFinP.
  have [_ Hγm] := Hγ.
  have Hb := Hγm (ar_zero Ar) m mM.
  have -> : (fun w => test_fun m s (γ w)) =
            (fun q : ar_carrier Ar (ar_zero Ar) * ar_carrier Ar W =>
               test_fun m q.1 (γ q.2)) \o (fun w => (s, w)).
    by apply: funext.
  apply: (measurable_comp (F := setT) measurableT (subsetT _) Hb).
  by apply: measurable_fun_pair; [exact: measurable_cst|exact: measurable_id].
(* RHS integrand: c1_val(δ s) * m(s, γ w) = Ks%:E * (m s (γ w))%:E. *)
under [in RHS]eq_integral => w _ do rewrite /= lin_ptE test_linZ EFinM.
rewrite lebesgue_integral_nonneg.ge0_integralZl_EFin//.
- rewrite fineM// /Ks ge0_fin_numE;
    last by apply: integral_ge0 => w _; rewrite lee_fin test_ge0.
  have [[Mb HMb] _] := Hγ.
  apply: (@le_lt_trans _ _
    (\int[fmeas_mu µ]_(w in [set: ar_carrier Ar W]) Mb%:E)%E).
    apply: (ge0_le_integral _ measurableT _ meas_g (measurable_cst _)).
    - by move=> w _; rewrite lee_fin test_ge0.
    - by move=> w _; rewrite lee_fin; apply: le_trans (test_norm_le m s (γ w)) _.
  rewrite -[(fun=> Mb%:E)]/(cst Mb%:E) lebesgue_integral_nonneg.integral_cst//.
  by rewrite ltey_eq fin_numM// fmeas_setT_fin.
- by move=> w _; rewrite lee_fin test_ge0.
Qed.

Definition lo_lift_mcones : mcones_hom Ar C L :=
  MkMConesHom (ConesHom (lin_pt (C:=C)) lo_lift_linear lo_lift_continuous
                lo_lift_norm_le1)
    (fun W g Hg => lo_lift_pres_path (W:=W) (γ:=g) Hg).

Lemma lo_lift_mcones_pres_int (W : ar_obj Ar) (γ : ar_carrier Ar W -> C)
  (Hγ : is_measurable_path γ) (µ : fmeas R (ar_carrier Ar W)) :
  cones_hom_fun (mcones_hom_cones lo_lift_mcones) (icone_integral γ Hγ µ) =
  icone_integral
    (fun w => cones_hom_fun (mcones_hom_cones lo_lift_mcones) (γ w))
    (mcones_hom_pres_path lo_lift_mcones W γ Hγ) µ.
Proof.
rewrite -[cones_hom_fun _ _]/(lin_pt (icone_integral γ Hγ µ)).
rewrite -[lin_pt _]/(linhom_pre_fun lo_lift_pre (icone_integral γ Hγ µ)).
rewrite (lo_lift_pres_int Hγ µ).
by congr icone_integral; exact: Prop_irrelevance.
Qed.

Definition lo_lift : icones_hom Ar C L :=
  MkIConesHom lo_lift_mcones lo_lift_mcones_pres_int.

Lemma lo_liftE (c : C) (s : One) :
  linhom_fun (lo_lift c) s = precone_scale (c1_val s) c.
Proof. by rewrite -[lo_lift c]/(lin_pt c) lin_ptE. Qed.

(** **** The iso [1 ⊸ C ≅ C] *)

Lemma linhom_one_fwdK (φ : L) : lo_lift (eval1 φ) = φ.
Proof.
apply: linhom_eq => s.
rewrite lo_liftE eval1E.
(* [c1_val s · φ(1) = φ(c1_val s · 1) = φ s], by linearity of [φ]. *)
have [_ _ HZ] := linhom_pre_linear (linhom_pre_of φ).
rewrite -[precone_scale (c1_val s) (linhom_fun φ c1_one)]
          /(precone_scale (c1_val s) (linhom_pre_fun (linhom_pre_of φ) c1_one)).
rewrite -HZ.
congr (linhom_fun φ _).
by apply: cone_one_eq; apply: val_inj => /=; rewrite mulr1.
Qed.

Lemma linhom_one_bwdK (c : C) : eval1 (lo_lift c) = c.
Proof. by rewrite eval1E lo_liftE (_ : c1_val c1_one = 1%:nng) ?precone_scale_1. Qed.

Definition linhom_one_iso : icones_iso Ar L C :=
  icones_iso_of_cancel eval1 lo_lift linhom_one_fwdK linhom_one_bwdK.

End LinhomOneIso.

Arguments c1_one {R} Ar.
Arguments eval1 {R Ar C}.
Arguments eval1E {R Ar C} φ.
Arguments lo_lift {R Ar C}.
Arguments lo_liftE {R Ar C} c s.
Arguments linhom_one_iso {R Ar} C.


(** ** Paper [lemma:path-tens-to-one] — [path_tens_to_one]

    A function [η : X → ((B⊗C) ⊸ 1)] that is bounded and JOINTLY
    MEASURABLE ON PURE TENSORS is a genuine measurable path of
    [(B⊗C) ⊸ 1].  NO pure-tensor density is needed.

    The route (Paper §5.4):
    - Lift each scalar [η(r)(b⊗c) ∈ 1] into [1⊸1] via [lin_pt] (whose
      value at the unit is [η(r)(b⊗c)] by [lin_pt_unit]), and package the
      pure-tensor family into a morphism
      [eta' : icones_hom B (C ⊸ Path(X, 1⊸1))].
    - Uncurry to [icones_hom (B⊗C) (Path(X, 1⊸1))] and apply
      [lfun_path_swap] (with [B':=B⊗C], [C':=D':=1]) to obtain
      [h : icones_hom 1 (Path(X, (B⊗C)⊸1))].
    - Conclude [path_fun (h 1) r = η r] by [linhom_tensor_ext] (Paper
      Prop 5.14, pure-tensor extensionality — NOT density), so [η] is the
      [path_fun] of the genuine [Path] [h 1]. *)

Section PathTensToOne.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (B C : ICone.type Ar).
Variable (X : ar_obj Ar).
Local Notation One := (cone_one_car Ar).
Local Notation BC := (tensor B C).
Local Notation L11 := (linhom_car Ar One One).
Local Notation PX := (path_car Ar X L11).

Variable η : ar_carrier Ar X -> linhom_car Ar BC One.
Hypothesis Hη1 : forall r, cone_norm (η r) <= 1.

(** The pure-tensor joint-measurability hypothesis: for any arity [Z], any
    arrow [φ : Z → X] (selecting the [η]-index), and any measurable
    [B]-path [β] and [C]-path [γ] over [Z], the scalar
    [s ↦ c1_val(η(φ s)(β s ⊗ γ s))] is measurable on [Z].

    Stated through [id_test] (the singleton [1]-cone test) to force the
    [R]-valued measurable codomain.  The arrow [φ] decouples the [η]-index
    from the tensor factors — exactly the flexibility the [Path]/integral
    fields of [eta'] consume (via [ar_prod] reindexing). *)
Hypothesis ηpt :
  forall (Z : ar_obj Ar) (φ : ar_hom Ar Z X)
         (β : ar_carrier Ar Z -> B) (γ : ar_carrier Ar Z -> C),
    is_measurable_path β -> is_measurable_path γ ->
    measurable_fun [set: ar_carrier Ar Z]
      (fun s => test_fun (ConeOneMConeAux.id_test (R:=R) (Ar:=Ar) (ar_zero Ar))
                  (ar_zero_pt Ar) (linhom_fun (η (φ s)) (ptensor (β s) (γ s)))).

(** The composite integrable map [Q b r : C ⊸ (1⊸1)], the map
    [c ↦ lin_pt (η r (b⊗c))].  Built as
    [lo_lift ∘ (η r) ∘ (τ b)], so all five [linhom_car] fields are free. *)
Definition pt_Q (b : B) (r : ar_carrier Ar X) : linhom_car Ar C L11 :=
  linhom_comp (icones_to_linhom (lo_lift (C:=One)))
    (linhom_comp (η r) (hfun (tauL B C) b)).

Lemma pt_QE (b : B) (r : ar_carrier Ar X) (c : C) :
  linhom_fun (pt_Q b r) c = lin_pt (linhom_fun (η r) (ptensor b c)).
Proof.
rewrite /pt_Q !linhom_compE icones_to_linhomE.
rewrite -[hfun (lo_lift (C:=One)) _]/(lin_pt _).
by rewrite -/(ptensor b c).
Qed.

(** The inner path [r ↦ pt_Q b r c = lin_pt (η r (b⊗c)) : Path(X, 1⊸1)]
    is measurable, by [lo_lift_pres_path] from the [1]-path
    [r ↦ η r (b⊗c)].  Its joint measurability against a [1]-test at arity
    [Z] is the pure-tensor hypothesis [ηpt] at arity [ar_prod Z X], with
    the [η]-index selected by [ar_prod_snd] and constant tensor factors
    [b], [c] — pulled back along the diagonal [ar_prod_cast]. *)
Lemma pt_inner_path (b : B) (c : C) :
  is_measurable_path (fun r => linhom_fun (pt_Q b r) c).
Proof.
have Hbase : is_measurable_path (fun r => linhom_fun (η r) (ptensor b c)).
  split.
    exists (cone_norm (ptensor b c)) => r.
    apply: le_trans (linhom_norm_apply_le (lexx _) (ptensor b c)) _.
    by rewrite -[X in _ <= X]mul1r; apply: ler_wpM2r;
       [exact: cone_norm_ge0|exact: Hη1].
  move=> Z m mM.
  (* The [1]-cone test family is the singleton [id_test]. *)
  have -> : m = ConeOneMConeAux.id_test (R:=R) (Ar:=Ar) Z by exact: mM.
  have HZX := ηpt (ar_prod_snd Z X)
    (@const_path_measurable R Ar B (ar_prod Ar Z X) b)
    (@const_path_measurable R Ar C (ar_prod Ar Z X) c).
  rewrite (_ : (fun p : ar_carrier Ar Z * ar_carrier Ar X =>
     ConeOneMConeAux.id_test Z p.1 (linhom_fun (η p.2) (ptensor b c))) =
     (fun s : ar_carrier Ar (ar_prod Ar Z X) =>
      ConeOneMConeAux.id_test (ar_zero Ar) (ar_zero_pt Ar)
        (linhom_fun (η (ar_prod_snd Z X s)) (ptensor b c)))
       \o (@ar_prod_cast R Ar Z X)); last first.
    apply: funext => p.
    rewrite /= /ar_prod_snd /ar_prod_snd_fun ar_prod_castK /=.
    by rewrite /ConeOneMConeAux.id_test /= /ConeOneMConeAux.id_test_fun /=.
  exact: (measurable_comp (F := setT) measurableT (subsetT _) HZX
            (ar_prod_cast_meas Ar Z X)).
have := lo_lift_pres_path (C:=One) (W:=X)
  (γ:=fun r => linhom_fun (η r) (ptensor b c)) Hbase.
by under [in X0 in is_measurable_path X0 -> _]eq_fun do rewrite -pt_QE.
Qed.

(** The inner path value [eta_path b c : Path(X, 1⊸1)]. *)
Definition eta_path (b : B) (c : C) : PX := MkPath (pt_inner_path b c).

Lemma eta_pathE (b : B) (c : C) (r : ar_carrier Ar X) :
  path_fun (eta_path b c) r = lin_pt (linhom_fun (η r) (ptensor b c)).
Proof. by rewrite /eta_path /= pt_QE. Qed.

(** [path_fun (eta_path b c) r = linhom_fun (pt_Q b r) c] — bridges the
    inner path to the composite integrable map [pt_Q b r], whose [c]-slot
    fields (linearity/ω-continuity/integral) are inherited for free. *)
Lemma eta_pathQ (b : B) (c : C) (r : ar_carrier Ar X) :
  path_fun (eta_path b c) r = linhom_fun (pt_Q b r) c.
Proof. by rewrite eta_pathE pt_QE. Qed.

(** *** The inner map [eta_inner b : C ⊸ Path(X, 1⊸1)] (fixed [b]). *)

Section EtaInner.
Variable b : B.

(** Linearity in [c]: [Path] operations are pointwise in [r]; at each [r]
    the value is [linhom_fun (pt_Q b r) c], linear by [pt_Q]'s linearity. *)
Lemma eta_inner_linear : is_linear (eta_path b).
Proof.
have Qlin r := linhom_pre_linear (linhom_pre_of (pt_Q b r)).
split.
- apply: path_eq => r /=.
  have [Z0 _ _] := Qlin r.
  rewrite -[linhom_fun (pt_Q b r) 0%PC]/(linhom_pre_fun (linhom_pre_of (pt_Q b r)) 0%PC).
  by rewrite Z0 /path_zero_fun.
- move=> c1 c2; apply: path_eq => r /=.
  have [_ HD _] := Qlin r.
  rewrite -[linhom_fun (pt_Q b r) (c1 + c2)%PC]
            /(linhom_pre_fun (linhom_pre_of (pt_Q b r)) (c1 + c2)%PC).
  by rewrite HD.
- move=> s c; apply: path_eq => r /=.
  have [_ _ HZ] := Qlin r.
  rewrite -[linhom_fun (pt_Q b r) (s *: c)%PC]
            /(linhom_pre_fun (linhom_pre_of (pt_Q b r)) (s *: c)%PC).
  by rewrite HZ.
Qed.

(** Boundedness in [c]: the inner [Path]-norm is the [sup] over [r] of the
    [1⊸1]-norms [‖pt_Q b r c‖ ≤ ‖η r‖ · ‖b‖ · ‖c‖ ≤ M · ‖b‖] for unit [c]. *)
Lemma eta_inner_bounded :
  exists M : R, forall c : C, cnorm c <= 1 -> cnorm (eta_path b c) <= M.
Proof.
exists (cone_norm b) => c Hc.
rewrite -[cnorm (eta_path b c)]/(path_norm (eta_path b c)).
apply: ge_sup; first exact: path_normset_nonempty.
move=> _ [r ->] /=.
rewrite pt_QE.
apply: le_trans (lo_lift_norm_le1 (linhom_fun (η r) (ptensor b c))) _.
apply: le_trans (linhom_norm_apply_le (lexx _) (ptensor b c)) _.
have HbcN : cone_norm (ptensor b c) <= cone_norm b.
  apply: le_trans (ptensor_norm_le b c) _.
  by rewrite -[X in _ <= X]mulr1; apply: ler_wpM2l; [exact: cone_norm_ge0|exact: Hc].
apply: le_trans (ler_wpM2r (cone_norm_ge0 _) (Hη1 r)) _.
by rewrite mul1r.
Qed.

(** ω-continuity in [c]: [Path]-sup is pointwise in [r] ([path_sup_ball_fun]);
    at each [r] the value is [pt_Q b r], itself ω-continuous as a [linhom]. *)
Lemma eta_inner_continuous : is_omega_continuous (eta_path b).
Proof.
move=> u uch ub1 fuch fub1.
apply: path_eq => r /=.
rewrite /path_sup_ball_fun.
have Qcont : is_omega_continuous (linhom_fun (pt_Q b r)).
  by rewrite -[linhom_fun (pt_Q b r)]/(linhom_pre_fun (linhom_pre_of (pt_Q b r)));
     exact: linhom_pre_continuous.
rewrite (Qcont u uch ub1 (path_sup_ball_chain_pw fuch r) (path_sup_ball_ub1_pw fub1 r)).
exact: cone_sup_ball_irr.
Qed.

(** Path-preservation in [c]: for a measurable [C]-path [δ : W → C],
    [w ↦ eta_path b (δ w)] is a measurable path of [Path(X, 1⊸1)].

    Reduce via the [Path(X,1⊸1)] test family: a test is [φ ▷ m] with
    [φ : Y → X] an arrow and [m] a [1⊸1]-test [= ζ ▷ m₂] ([ζ] a [1]-path,
    [m₂] the singleton [id_test]).  The value at [eta_path b (δ w)] is
    [c1_val(ζ s) · c1_val(η (φ s)(b ⊗ δ w))] — a product of [ζ]'s
    measurable [1]-section and the pure-tensor scalar, whose joint
    measurability in [(s, w)] is [ηpt] at arity [ar_prod Y W] with
    [η]-index [φ ∘ fst], constant factor [b], moving factor [δ ∘ snd],
    pulled back along the diagonal [ar_prod_cast]. *)
Lemma eta_inner_pres_path (W : ar_obj Ar) (δ : ar_carrier Ar W -> C) :
  is_measurable_path δ ->
  is_measurable_path (fun w => eta_path b (δ w)).
Proof.
move=> Hδ.
have [[Mδ HMδ] Hδm] := Hδ.
have Mδ_ge0 : 0 <= Mδ.
  by apply: le_trans (HMδ (ar_point Ar W)); exact: cone_norm_ge0.
split.
  exists (cone_norm b * Mδ)%R => w.
  rewrite -[cnorm (eta_path b (δ w))]/(path_norm (eta_path b (δ w))).
  apply: ge_sup; first exact: path_normset_nonempty.
  move=> _ [r ->] /=.
  rewrite pt_QE.
  apply: le_trans (lo_lift_norm_le1 (linhom_fun (η r) (ptensor b (δ w)))) _.
  apply: le_trans (linhom_norm_apply_le (lexx _) (ptensor b (δ w))) _.
  apply: le_trans (ler_wpM2l (cone_norm_ge0 (η r)) (ptensor_norm_le b (δ w))) _.
  rewrite mulrA.
  apply: ler_pM.
  - by rewrite mulr_ge0 // cone_norm_ge0.
  - exact: cone_norm_ge0.
  - rewrite -[X in _ <= X]mul1r; apply: ler_pM;
      [exact: cone_norm_ge0|exact: cone_norm_ge0|exact: Hη1|exact: lexx].
  - exact: HMδ.
move=> Y p pM.
have [φ [m1 [m1M Hp]]] : path_mcone_M (Y := Y) p by exact: pM.
have [ζ [ζub [m2 [m2M Hm1]]]] : linhom_mcone_M (Y := Y) m1 by exact: m1M.
subst p m1.
have m2E : forall (s' : ar_carrier Ar Y) (v : One), m2 s' v = (c1_val v)%:num.
  have -> : m2 = ConeOneMConeAux.id_test (R:=R) (Ar:=Ar) Y by exact: m2M.
  by move=> s' v; rewrite /ConeOneMConeAux.id_test /= /ConeOneMConeAux.id_test_fun /=.
rewrite (_ : (fun p : ar_carrier Ar Y * ar_carrier Ar W =>
   path_test φ (linhom_test ζ ζub m2 m2M) m1M p.1 (eta_path b (δ p.2))) =
   (fun p => (c1_val (path_fun ζ p.1))%:num *
             (c1_val (linhom_fun (η (φ p.1)) (ptensor b (δ p.2))))%:num)); last first.
  apply: funext => p.
  rewrite /path_test /= /path_test_fun /=.
  rewrite /linhom_test /= /linhom_test_fun /=.
  rewrite pt_QE lin_ptE.
  rewrite test_linZ.
  by rewrite m2E.
apply: measurable_funM.
- rewrite (_ : (fun x : ar_carrier Ar Y * ar_carrier Ar W => (c1_val (ζ x.1))%:num) =
     (fun s' : ar_carrier Ar Y =>
        ConeOneMConeAux.id_test (R:=R) (Ar:=Ar) (ar_zero Ar) (ar_zero_pt Ar) (path_fun ζ s'))
       \o fst); last by apply: funext => x;
       rewrite /= /ConeOneMConeAux.id_test /= /ConeOneMConeAux.id_test_fun.
  apply: (measurable_comp (F := setT) measurableT (subsetT _) _ measurable_fst).
  exact: (measurable_test_path_section (B := cone_one_car Ar)
            (m := ConeOneMConeAux.id_test (R:=R) (Ar:=Ar) (ar_zero Ar))
            (erefl) (path_is_path ζ) (ar_zero_pt Ar)).
- pose φfw : ar_hom Ar (ar_prod Ar Y W) X :=
    [the {mfun _ >-> _} of φ \o ar_prod_fst Y W].
  have HYW := ηpt φfw
    (@const_path_measurable R Ar B (ar_prod Ar Y W) b)
    (reindex_path_measurable (ar_prod_snd Y W) Hδ).
  rewrite (_ : (fun x : ar_carrier Ar Y * ar_carrier Ar W =>
     (c1_val (linhom_fun (η (φ x.1)) (ptensor b (δ x.2))))%:num) =
     (fun s : ar_carrier Ar (ar_prod Ar Y W) =>
      ConeOneMConeAux.id_test (ar_zero Ar) (ar_zero_pt Ar)
        (linhom_fun (η (φfw s)) (ptensor b (δ (ar_prod_snd Y W s)))))
       \o (@ar_prod_cast R Ar Y W)); last first.
    apply: funext => p.
    rewrite /φfw /= /ar_prod_fst /ar_prod_fst_fun /ar_prod_snd /ar_prod_snd_fun
            !ar_prod_castK /=.
    by rewrite /ConeOneMConeAux.id_test /= /ConeOneMConeAux.id_test_fun /=.
  exact: (measurable_comp (F := setT) measurableT (subsetT _) HYW
            (ar_prod_cast_meas Ar Y W)).
Qed.

Definition eta_inner_pre : linhom_pre Ar C PX :=
  MkLinhomPre (eta_path b) eta_inner_linear eta_inner_continuous
              eta_inner_bounded
              (fun W δ Hδ => eta_inner_pres_path (W:=W) (δ:=δ) Hδ).

(** Integral-preservation in [c]: by [icone_integral_eqP] on [Path(X,1⊸1)]
    it suffices to check the Pettis spec at an arity-0 path-test
    [φ ▷ (ζ ▷ m₂)].  The value at [eta_path b c] is
    [c1_val(ζ z) · c1_val(η (φ z)(b ⊗ c))]; the [(B⊗C)⊸1]-section
    [c ↦ η (φ z)(b ⊗ c)] is the integral-preserving composite
    [LL := (η (φ z)) ∘ (τ b)], so [c1_val(LL(∫δ)) = ∫ c1_val(LL(δ w))] by
    [LL]'s integral law + the [1]-cone [icone_integralP] at [id_test], and
    the scalar [c1_val(ζ z)] factors out via [ge0_integralZl_EFin]. *)
Lemma eta_inner_pres_int (W : ar_obj Ar) (δ : ar_carrier Ar W -> C)
    (Hδ : is_measurable_path δ) (µ : fmeas R (ar_carrier Ar W)) :
  linhom_pre_fun eta_inner_pre (icone_integral δ Hδ µ) =
  icone_integral
    (fun w => linhom_pre_fun eta_inner_pre (δ w))
    (linhom_pre_pres_path eta_inner_pre W δ Hδ) µ.
Proof.
rewrite -[linhom_pre_fun eta_inner_pre]/(eta_path b).
have HE : icone_integral (fun w => eta_path b (δ w))
            (eta_inner_pres_path Hδ) µ =
          icone_integral (fun w => eta_path b (δ w))
            (linhom_pre_pres_path eta_inner_pre W δ Hδ) µ.
  by congr icone_integral; exact: Prop_irrelevance.
rewrite -HE.
apply: icone_integral_eqP => p pM z.
have [φ [m1 [m1M Hp]]] : path_mcone_M (Y := ar_zero Ar) p by exact: pM.
have [ζ [ζub [m2 [m2M Hm1]]]] : linhom_mcone_M (Y := ar_zero Ar) m1 by exact: m1M.
subst p m1.
have m2E : forall (s' : ar_carrier Ar (ar_zero Ar)) (v : One),
    m2 s' v = (c1_val v)%:num.
  have -> : m2 = ConeOneMConeAux.id_test (R:=R) (Ar:=Ar) (ar_zero Ar) by exact: m2M.
  by move=> s' v; rewrite /ConeOneMConeAux.id_test /= /ConeOneMConeAux.id_test_fun /=.
set K : R := (c1_val (path_fun ζ z))%:num.
have valE : forall c : C,
    path_test φ (linhom_test ζ ζub m2 m2M) m1M z (eta_path b c) =
    K * (c1_val (linhom_fun (η (φ z)) (ptensor b c)))%:num.
  move=> c.
  rewrite /path_test /= /path_test_fun /= /linhom_test /= /linhom_test_fun /=.
  rewrite pt_QE lin_ptE test_linZ m2E.
  by rewrite /K.
rewrite valE.
under [in RHS]eq_integral => r _ do rewrite valE.
pose r0 := φ z.
pose LL : linhom_car Ar C One := linhom_comp (η r0) (hfun (tauL B C) b).
have LLE : forall c : C, linhom_fun (η r0) (ptensor b c) = linhom_fun LL c.
  by move=> c; rewrite /LL linhom_compE -/(ptensor b c).
rewrite -/r0.
under [in RHS]eq_integral => r _ do rewrite LLE.
rewrite LLE.
have HLLint := linhom_pres_int LL W δ Hδ µ.
have Hsec : (c1_val (linhom_fun LL (icone_integral δ Hδ µ)))%:num =
  fine (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar W])
          ((c1_val (linhom_fun LL (δ r)))%:num)%:E).
  rewrite -[linhom_fun LL (icone_integral δ Hδ µ)]/(LL (icone_integral δ Hδ µ)).
  rewrite HLLint.
  have := icone_integralP (fun r => LL (δ r)) (linhom_pre_pres_path LL W δ Hδ) µ
            (ConeOneMConeAux.id_test (R:=R) (Ar:=Ar) (ar_zero Ar)) erefl (ar_zero_pt Ar).
  by [].
rewrite Hsec.
have Kge0 : 0 <= K by rewrite /K.
have meas_f : measurable_fun [set: ar_carrier Ar W]
    (fun r => ((c1_val (linhom_fun LL (δ r)))%:num)%:E).
  apply/measurable_EFinP.
  exact: (measurable_test_path_section (B := cone_one_car Ar)
            (m := ConeOneMConeAux.id_test (R:=R) (Ar:=Ar) (ar_zero Ar))
            (erefl) (linhom_pre_pres_path LL W δ Hδ) (ar_zero_pt Ar)).
under [in RHS]eq_integral => r _ do rewrite EFinM.
rewrite lebesgue_integral_nonneg.ge0_integralZl_EFin//.
rewrite fineM//.
rewrite ge0_fin_numE; last by apply: integral_ge0 => r _; rewrite lee_fin.
have [[Mδ HMδ] _] := Hδ.
apply: (@le_lt_trans _ _
  (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar W]) (cone_norm LL * Mδ)%:E)%E).
  apply: (ge0_le_integral _ measurableT _ meas_f (measurable_cst _)).
  - by move=> r _; rewrite lee_fin.
  - move=> r _; rewrite lee_fin.
    rewrite -[(c1_val (linhom_fun LL (δ r)))%:num]/(cone_norm (linhom_fun LL (δ r))).
    apply: le_trans (linhom_norm_apply_le (lexx _) (δ r)) _.
    by apply: ler_wpM2l; [exact: linhom_norm_ge0|exact: HMδ].
rewrite -[(fun=> _)]/(cst (cone_norm LL * Mδ)%:E)
        lebesgue_integral_nonneg.integral_cst//.
by rewrite ltey_eq fin_numM// fmeas_setT_fin.
Qed.

End EtaInner.

(** The inner element [eta_inner b : C ⊸ Path(X, 1⊸1)]. *)
Definition eta_inner (b : B) : linhom_car Ar C PX :=
  MkLinhom (eta_inner_pre b) (@eta_inner_pres_int b).

Lemma eta_innerE (b : B) (c : C) (r : ar_carrier Ar X) :
  path_fun (linhom_fun (eta_inner b) c) r =
  lin_pt (linhom_fun (η r) (ptensor b c)).
Proof. by rewrite -[linhom_fun (eta_inner b) c]/(eta_path b c) eta_pathE. Qed.

(** Bilinearity of the pure tensor in the [B]-slot — [τ = tauL B C] is an
    [icones_hom], so its underlying function is linear. *)
Lemma ptensor_linB (b1 b2 : B) (c : C) :
  ptensor (b1 + b2)%PC c = (ptensor b1 c + ptensor b2 c)%PC.
Proof.
have [_ HD _] := cones_hom_linear (mcones_hom_cones (icones_hom_mcones (tauL B C))).
rewrite /ptensor.
rewrite -[hfun (tauL B C) (b1 + b2)%PC]
          /(cones_hom_fun (mcones_hom_cones (icones_hom_mcones (tauL B C))) (b1 + b2)%PC).
rewrite HD.
by rewrite [linhom_fun (_ + _)%PC c]/linhom_fun /= /linhom_add_fun /=.
Qed.

Lemma ptensor_zeroB (c : C) : ptensor (0%PC : B) c = (0%PC : BC).
Proof.
have [Z0 _ _] := cones_hom_linear (mcones_hom_cones (icones_hom_mcones (tauL B C))).
rewrite /ptensor.
rewrite -[hfun (tauL B C) (0%PC : B)]
          /(cones_hom_fun (mcones_hom_cones (icones_hom_mcones (tauL B C))) (0%PC : B)).
rewrite Z0.
by rewrite [linhom_fun (0%PC : linhom_car Ar C BC) c]/linhom_fun /= /linhom_zero_fun.
Qed.

Lemma ptensor_scaleB (s : {nonneg R}) (b : B) (c : C) :
  ptensor (s *: b)%PC c = (s *: ptensor b c)%PC.
Proof.
have [_ _ HZ] := cones_hom_linear (mcones_hom_cones (icones_hom_mcones (tauL B C))).
rewrite /ptensor.
rewrite -[hfun (tauL B C) (s *: b)%PC]
          /(cones_hom_fun (mcones_hom_cones (icones_hom_mcones (tauL B C))) (s *: b)%PC).
rewrite HZ.
by rewrite [linhom_fun (s *: _)%PC c]/linhom_fun /= /linhom_scale_fun.
Qed.

(** *** The outer morphism [eta' : ICones(B, C ⊸ Path(X, 1⊸1))]

    [eta' b := eta_inner b].  All five fields in the [b]-slot reduce, via
    the pointwise [linhom_car C PX] / [PX] / [1⊸1] structure and the
    bilinearity [ptensor_*B], to facts about [η] / [lin_pt] (linearity,
    ω-continuity, norm, path, integral) — symmetric to the inner [c]-slot
    fields.  Norm decrease [≤ 1] uses the unit-ball hypothesis [Hη1]. *)

(** Linearity in [b]. *)
Lemma eta_outer_linear : is_linear eta_inner.
Proof.
split.
- apply: linhom_eq => c; apply: path_eq => r /=.
  rewrite pt_QE ptensor_zeroB.
  have [Z0 _ _] := linhom_pre_linear (linhom_pre_of (η r)).
  rewrite -[linhom_fun (η r) 0%PC]/(linhom_pre_fun (linhom_pre_of (η r)) 0%PC) Z0.
  have [Z0' _ _] := @lo_lift_linear R Ar One.
  rewrite -[lin_pt 0%PC]/(lin_pt (C:=One) 0%PC) Z0'.
  by rewrite /path_zero_fun.
- move=> b1 b2; apply: linhom_eq => c; apply: path_eq => r /=.
  rewrite !pt_QE ptensor_linB.
  have [_ HD _] := linhom_pre_linear (linhom_pre_of (η r)).
  rewrite -[linhom_fun (η r) (ptensor b1 c + ptensor b2 c)%PC]
            /(linhom_pre_fun (linhom_pre_of (η r)) (ptensor b1 c + ptensor b2 c)%PC) HD.
  have [_ HD' _] := @lo_lift_linear R Ar One.
  rewrite -[lin_pt (linhom_fun (η r) (ptensor b1 c) + linhom_fun (η r) (ptensor b2 c))%PC]
            /(lin_pt (C:=One)
                (linhom_fun (η r) (ptensor b1 c) + linhom_fun (η r) (ptensor b2 c))%PC) HD'.
  by [].
- move=> s b; apply: linhom_eq => c; apply: path_eq => r /=.
  rewrite !pt_QE ptensor_scaleB.
  have [_ _ HZ] := linhom_pre_linear (linhom_pre_of (η r)).
  rewrite -[linhom_fun (η r) (s *: ptensor b c)%PC]
            /(linhom_pre_fun (linhom_pre_of (η r)) (s *: ptensor b c)%PC) HZ.
  have [_ _ HZ'] := @lo_lift_linear R Ar One.
  rewrite -[lin_pt (s *: linhom_fun (η r) (ptensor b c))%PC]
            /(lin_pt (C:=One) (s *: linhom_fun (η r) (ptensor b c))%PC) HZ'.
  by [].
Qed.

(** Norm decrease [‖eta_inner b‖ ≤ ‖b‖]: each layer's value at unit [c]
    is [‖lin_pt(η r (b⊗c))‖ ≤ ‖η r‖·‖b‖·‖c‖ ≤ ‖b‖]. *)
Lemma eta_outer_norm (b : B) : cone_norm (eta_inner b) <= cone_norm b.
Proof.
rewrite -[cone_norm (eta_inner b)]/(linhom_norm (eta_inner b)).
apply: linhom_norm_sup_lub => c Hc.
rewrite -[cnorm (linhom_fun (eta_inner b) c)]/(path_norm (linhom_fun (eta_inner b) c)).
apply: ge_sup; first exact: path_normset_nonempty.
move=> _ [r ->].
rewrite eta_innerE.
apply: le_trans (lo_lift_norm_le1 (linhom_fun (η r) (ptensor b c))) _.
apply: le_trans (linhom_norm_apply_le (lexx _) (ptensor b c)) _.
have HbcN : cone_norm (ptensor b c) <= cone_norm b.
  apply: le_trans (ptensor_norm_le b c) _.
  by rewrite -[X in _ <= X]mulr1; apply: ler_wpM2l; [exact: cone_norm_ge0|exact: Hc].
apply: le_trans (ler_wpM2r (cone_norm_ge0 _) (Hη1 r)) _.
by rewrite mul1r.
Qed.

(** The [b]-slot composite integrable map [pt_QB c r : B ⊸ (1⊸1)], the map
    [b ↦ lin_pt (η r (b⊗c))] — built as
    [lo_lift ∘ (η r) ∘ (eval_at c) ∘ τ], so ω-continuous for free. *)
Definition pt_QB (c : C) (r : ar_carrier Ar X) : linhom_car Ar B L11 :=
  linhom_comp (icones_to_linhom (lo_lift (C:=One)))
    (linhom_comp (η r) (linhom_comp (eval_at c) (icones_to_linhom (tauL B C)))).

Lemma pt_QBE (c : C) (r : ar_carrier Ar X) (b : B) :
  linhom_fun (pt_QB c r) b = lin_pt (linhom_fun (η r) (ptensor b c)).
Proof.
rewrite /pt_QB !linhom_compE icones_to_linhomE.
rewrite -[hfun (lo_lift (C:=One)) _]/(lin_pt _).
rewrite eval_atE icones_to_linhomE.
by rewrite -/(ptensor b c).
Qed.

(** ω-continuity in [b].  Reduce via [linhom_mcone_M_sep] for the codomain
    [C ⊸ Path(X, 1⊸1)]: an arity-0 test [γ_C ▷ (φ ▷ (ζ ▷ m₂))] evaluated at
    [eta_inner b] is [m₂(linhom_fun (pt_QB c' r0 b) (ζ))] with [c' := γ_C],
    [r0 := φ]; both sides collapse to [sup_n m₂(pt_QB c' r0 (u n)(ζ))] — LHS
    via [pt_QB c' r0]'s ω-continuity + [linhom_sup_fun_test_sup], RHS via
    the codomain's own [linhom_sup_fun_test_sup]. *)
Lemma eta_outer_continuous : is_omega_continuous eta_inner.
Proof.
move=> u uch ub1 fuch fub1.
apply: (@linhom_mcone_M_sep _ _ C PX) => p.
move=> [γC [γCub [mPX [mPXM Hp]]]].
have [φ [m1 [m1M HmPX]]] : path_mcone_M (Y := ar_zero Ar) mPX by exact: mPXM.
have [ζ [ζub [m2 [m2M Hm1]]]] : linhom_mcone_M (Y := ar_zero Ar) m1 by exact: m1M.
rewrite Hp /linhom_test /linhom_test_fun /=.
set s0 := ar_zero_pt Ar.
have mPXred : forall (γ : PX),
    mPX s0 γ = m2 s0 (linhom_fun (path_fun γ (φ s0)) (path_fun ζ s0)).
  move=> γ.
  by rewrite HmPX /path_test /= /path_test_fun /= Hm1
             /linhom_test /= /linhom_test_fun /=.
rewrite !mPXred.
set c' := path_fun γC s0.
set r0 := φ s0.
rewrite -[linhom_fun (eta_inner (cone_sup_ball u uch ub1)) c']
          /(eta_path (cone_sup_ball u uch ub1) c').
rewrite eta_pathE -pt_QBE.
have Hc'1 : cone_norm c' <= 1.
  by apply: le_trans (path_norm_ub γC s0) _; rewrite -[path_norm γC]/(cnorm γC).
set φlh := pt_QB c' r0.
have φcont : is_omega_continuous (linhom_fun φlh).
  by rewrite -[linhom_fun φlh]/(linhom_pre_fun (linhom_pre_of φlh));
     exact: linhom_pre_continuous.
have φnorm : linhom_norm φlh <= 1.
  rewrite -[linhom_norm φlh]/(cone_norm φlh).
  apply: linhom_norm_sup_lub => b Hb.
  rewrite pt_QBE.
  apply: le_trans (lo_lift_norm_le1 (linhom_fun (η r0) (ptensor b c'))) _.
  apply: le_trans (linhom_norm_apply_le (lexx _) (ptensor b c')) _.
  apply: le_trans (ler_wpM2r (cone_norm_ge0 _) (Hη1 r0)) _.
  rewrite mul1r.
  apply: le_trans (ptensor_norm_le b c') _.
  by apply: mulr_ile1; [exact: cone_norm_ge0|exact: cone_norm_ge0|exact: Hb|exact: Hc'1].
have Hch : forall n, precone_le (linhom_fun φlh (u n)) (linhom_fun φlh (u n.+1)).
  move=> n; have [w Hw] := uch n.
  exists (linhom_fun φlh w).
  have [_ HD _] := linhom_pre_linear (linhom_pre_of φlh).
  by rewrite Hw -[linhom_fun φlh _]/(linhom_pre_fun (linhom_pre_of φlh) _) HD.
have Hub : forall n, cone_norm (linhom_fun φlh (u n)) <= 1.
  move=> n; apply: le_trans (linhom_norm_apply_le (lexx _) (u n)) _.
  rewrite -[X in _ <= X]mulr1; apply: ler_pM;
    [exact: linhom_norm_ge0|exact: cone_norm_ge0|exact: φnorm|exact: ub1].
rewrite (φcont u uch ub1 Hch Hub).
rewrite -[linhom_fun (cone_sup_ball (linhom_fun φlh \o u) Hch Hub) (ζ s0)]
          /(linhom_sup_fun Hch Hub (ζ s0)).
rewrite (linhom_sup_fun_test_sup Hch Hub m2 s0 (ζ s0)).
rewrite -[r0]/(φ s0).
rewrite -(mPXred (linhom_fun (cone_sup_ball (eta_inner \o u) fuch fub1) c')).
rewrite -[linhom_fun (cone_sup_ball (eta_inner \o u) fuch fub1) c']
          /(linhom_sup_fun fuch fub1 c').
rewrite (linhom_sup_fun_test_sup fuch fub1 mPX s0 c').
congr (sup _); apply: eq_imagel => n _ /=.
rewrite (mPXred (linhom_fun (eta_inner (u n)) c')).
congr (m2 s0 (linhom_fun _ (ζ s0))).
rewrite -[linhom_fun (eta_inner (u n)) c' (φ s0)]
          /(path_fun (linhom_fun (eta_inner (u n)) c') (φ s0)).
rewrite eta_innerE.
by rewrite pt_QBE.
Qed.

(** Path-preservation in [b]: for a measurable [B]-path [δb : W → B],
    [w ↦ eta_inner (δb w)] is a measurable path of [C ⊸ Path(X, 1⊸1)].
    Mirrors [eta_inner_pres_path] (roles of [b] and [c] swapped): a
    [C⊸PX]-test [γ_C ▷ (φ ▷ (ζ ▷ m₂))] evaluates to
    [c1_val(ζ s) · c1_val(η (φ s)((δb w) ⊗ (γ_C s)))]; joint measurability
    in [(s, w)] is [ηpt] at arity [ar_prod Y W] with [η]-index [φ ∘ fst],
    moving [B]-factor [δb ∘ snd], moving [C]-factor [γ_C ∘ fst]. *)
Lemma eta_outer_pres_path (W : ar_obj Ar) (δb : ar_carrier Ar W -> B) :
  is_measurable_path δb ->
  is_measurable_path (fun w => eta_inner (δb w)).
Proof.
move=> Hδb.
have [[Mδ HMδ] Hδbm] := Hδb.
have Mδ_ge0 : 0 <= Mδ.
  by apply: le_trans (HMδ (ar_point Ar W)); exact: cone_norm_ge0.
split.
  exists Mδ => w.
  by apply: le_trans (eta_outer_norm (δb w)) _; exact: HMδ.
move=> Y p pM.
have [γC [γCub [mPX [mPXM Hp]]]] : linhom_mcone_M (Y := Y) p by exact: pM.
have [φ [m1 [m1M HmPX]]] : path_mcone_M (Y := Y) mPX by exact: mPXM.
have [ζ [ζub [m2 [m2M Hm1]]]] : linhom_mcone_M (Y := Y) m1 by exact: m1M.
subst p mPX m1.
have m2E : forall (s' : ar_carrier Ar Y) (v : One), m2 s' v = (c1_val v)%:num.
  have -> : m2 = ConeOneMConeAux.id_test (R:=R) (Ar:=Ar) Y by exact: m2M.
  by move=> s' v; rewrite /ConeOneMConeAux.id_test /= /ConeOneMConeAux.id_test_fun /=.
rewrite (_ : (fun p : ar_carrier Ar Y * ar_carrier Ar W =>
   linhom_test γC γCub (path_test φ (linhom_test ζ ζub m2 m2M) m1M) mPXM p.1
     (eta_inner (δb p.2))) =
   (fun p => (c1_val (path_fun ζ p.1))%:num *
             (c1_val (linhom_fun (η (φ p.1))
                        (ptensor (δb p.2) (path_fun γC p.1))))%:num)); last first.
  apply: funext => p.
  rewrite /linhom_test /= /linhom_test_fun /=.
  rewrite pt_QE lin_ptE test_linZ m2E.
  by [].
apply: measurable_funM.
- rewrite (_ : (fun x : ar_carrier Ar Y * ar_carrier Ar W => (c1_val (ζ x.1))%:num) =
     (fun s' : ar_carrier Ar Y =>
        ConeOneMConeAux.id_test (R:=R) (Ar:=Ar) (ar_zero Ar) (ar_zero_pt Ar) (path_fun ζ s'))
       \o fst); last by apply: funext => x;
       rewrite /= /ConeOneMConeAux.id_test /= /ConeOneMConeAux.id_test_fun.
  apply: (measurable_comp (F := setT) measurableT (subsetT _) _ measurable_fst).
  exact: (measurable_test_path_section (B := cone_one_car Ar)
            (m := ConeOneMConeAux.id_test (R:=R) (Ar:=Ar) (ar_zero Ar))
            (erefl) (path_is_path ζ) (ar_zero_pt Ar)).
- pose φfw : ar_hom Ar (ar_prod Ar Y W) X :=
    [the {mfun _ >-> _} of φ \o ar_prod_fst Y W].
  have HYW := ηpt φfw
    (reindex_path_measurable (ar_prod_snd Y W) Hδb)
    (reindex_path_measurable (ar_prod_fst Y W) (path_is_path γC)).
  rewrite (_ : (fun x : ar_carrier Ar Y * ar_carrier Ar W =>
     (c1_val (linhom_fun (η (φ x.1)) (ptensor (δb x.2) (path_fun γC x.1))))%:num) =
     (fun s : ar_carrier Ar (ar_prod Ar Y W) =>
      ConeOneMConeAux.id_test (ar_zero Ar) (ar_zero_pt Ar)
        (linhom_fun (η (φfw s))
           (ptensor (δb (ar_prod_snd Y W s)) (path_fun γC (ar_prod_fst Y W s)))))
       \o (@ar_prod_cast R Ar Y W)); last first.
    apply: funext => p.
    rewrite /φfw /= /ar_prod_fst /ar_prod_fst_fun /ar_prod_snd /ar_prod_snd_fun
            !ar_prod_castK /=.
    by rewrite /ConeOneMConeAux.id_test /= /ConeOneMConeAux.id_test_fun /=.
  exact: (measurable_comp (F := setT) measurableT (subsetT _) HYW
            (ar_prod_cast_meas Ar Y W)).
Qed.

(** Integral-preservation in [b].  By [icone_integral_eqP] on [C ⊸ Path(X,
    1⊸1)] it suffices to check the Pettis spec at an arity-0 test
    [γ_C ▷ (φ ▷ (ζ ▷ m₂))]; the value at [eta_inner b] is
    [c1_val(ζ z) · c1_val(η (φ z)(b ⊗ c'))] with [c' := γ_C z].  The
    [B]-section [b ↦ η (φ z)(b ⊗ c')] is the integral-preserving composite
    [LLb := (η (φ z)) ∘ (eval_at c') ∘ τ], so the identity reduces to
    [LLb]'s integral law + the [1]-cone [icone_integralP] at [id_test],
    [c1_val(ζ z)] factoring out via [ge0_integralZl_EFin]. *)
Lemma eta_outer_pres_int (W : ar_obj Ar) (δb : ar_carrier Ar W -> B)
    (Hδb : is_measurable_path δb) (µ : fmeas R (ar_carrier Ar W)) :
  eta_inner (icone_integral δb Hδb µ) =
  icone_integral (fun w => eta_inner (δb w)) (eta_outer_pres_path Hδb) µ.
Proof.
apply: icone_integral_eqP => p pM z.
have [γC [γCub [mPX [mPXM Hp]]]] : linhom_mcone_M (Y := ar_zero Ar) p by exact: pM.
have [φ [m1 [m1M HmPX]]] : path_mcone_M (Y := ar_zero Ar) mPX by exact: mPXM.
have [ζ [ζub [m2 [m2M Hm1]]]] : linhom_mcone_M (Y := ar_zero Ar) m1 by exact: m1M.
subst p mPX m1.
have m2E : forall (s' : ar_carrier Ar (ar_zero Ar)) (v : One),
    m2 s' v = (c1_val v)%:num.
  have -> : m2 = ConeOneMConeAux.id_test (R:=R) (Ar:=Ar) (ar_zero Ar) by exact: m2M.
  by move=> s' v; rewrite /ConeOneMConeAux.id_test /= /ConeOneMConeAux.id_test_fun /=.
set K : R := (c1_val (path_fun ζ z))%:num.
set c' := path_fun γC z.
set r0 := φ z.
have valE : forall b : B,
    linhom_test γC γCub (path_test φ (linhom_test ζ ζub m2 m2M) m1M) mPXM z
      (eta_inner b) =
    K * (c1_val (linhom_fun (η r0) (ptensor b c')))%:num.
  move=> b.
  rewrite /linhom_test /= /linhom_test_fun /=.
  rewrite /path_test /= /path_test_fun /=.
  rewrite pt_QE lin_ptE test_linZ m2E.
  by rewrite /K /c' /r0.
rewrite valE.
under [in RHS]eq_integral => w _ do rewrite valE.
pose LLb : linhom_car Ar B One :=
  linhom_comp (η r0) (linhom_comp (eval_at c') (icones_to_linhom (tauL B C))).
have LLbE : forall b : B, linhom_fun (η r0) (ptensor b c') = linhom_fun LLb b.
  move=> b; rewrite /LLb !linhom_compE icones_to_linhomE eval_atE.
  by rewrite -/(ptensor b c').
rewrite LLbE.
under [in RHS]eq_integral => w _ do rewrite LLbE.
have HLLbint := linhom_pres_int LLb W δb Hδb µ.
have Hsec : (c1_val (linhom_fun LLb (icone_integral δb Hδb µ)))%:num =
  fine (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar W])
          ((c1_val (linhom_fun LLb (δb r)))%:num)%:E).
  rewrite -[linhom_fun LLb (icone_integral δb Hδb µ)]/(LLb (icone_integral δb Hδb µ)).
  rewrite HLLbint.
  have := icone_integralP (fun r => LLb (δb r)) (linhom_pre_pres_path LLb W δb Hδb) µ
            (ConeOneMConeAux.id_test (R:=R) (Ar:=Ar) (ar_zero Ar)) erefl (ar_zero_pt Ar).
  by [].
rewrite Hsec.
have Kge0 : 0 <= K by rewrite /K.
have meas_f : measurable_fun [set: ar_carrier Ar W]
    (fun r => ((c1_val (linhom_fun LLb (δb r)))%:num)%:E).
  apply/measurable_EFinP.
  exact: (measurable_test_path_section (B := cone_one_car Ar)
            (m := ConeOneMConeAux.id_test (R:=R) (Ar:=Ar) (ar_zero Ar))
            (erefl) (linhom_pre_pres_path LLb W δb Hδb) (ar_zero_pt Ar)).
under [in RHS]eq_integral => r _ do rewrite EFinM.
rewrite lebesgue_integral_nonneg.ge0_integralZl_EFin//.
rewrite fineM//.
rewrite ge0_fin_numE; last by apply: integral_ge0 => r _; rewrite lee_fin.
have [[Mδ HMδ] _] := Hδb.
apply: (@le_lt_trans _ _
  (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar W]) (cone_norm LLb * Mδ)%:E)%E).
  apply: (ge0_le_integral _ measurableT _ meas_f (measurable_cst _)).
  - by move=> r _; rewrite lee_fin.
  - move=> r _; rewrite lee_fin.
    rewrite -[(c1_val (linhom_fun LLb (δb r)))%:num]/(cone_norm (linhom_fun LLb (δb r))).
    apply: le_trans (linhom_norm_apply_le (lexx _) (δb r)) _.
    by apply: ler_wpM2l; [exact: linhom_norm_ge0|exact: HMδ].
rewrite -[(fun=> _)]/(cst (cone_norm LLb * Mδ)%:E)
        lebesgue_integral_nonneg.integral_cst//.
by rewrite ltey_eq fin_numM// fmeas_setT_fin.
Qed.

(** *** Assembly of the morphism [eta' : ICones(B, C ⊸ Path(X, 1⊸1))]. *)
Definition eta_outer_cones : cones_hom B (linhom_car Ar C PX) :=
  ConesHom eta_inner eta_outer_linear eta_outer_continuous eta_outer_norm.

Definition eta_outer_mcones : mcones_hom Ar B (linhom_car Ar C PX) :=
  MkMConesHom eta_outer_cones
    (fun W δb Hδb => eta_outer_pres_path (W:=W) (δb:=δb) Hδb).

Lemma eta_outer_mcones_pres_int
    (W : ar_obj Ar) (δb : ar_carrier Ar W -> B)
    (Hδb : is_measurable_path δb) (µ : fmeas R (ar_carrier Ar W)) :
  cones_hom_fun (mcones_hom_cones eta_outer_mcones) (icone_integral δb Hδb µ) =
  icone_integral
    (fun w => cones_hom_fun (mcones_hom_cones eta_outer_mcones) (δb w))
    (mcones_hom_pres_path eta_outer_mcones W δb Hδb) µ.
Proof.
rewrite -[cones_hom_fun _ _]/(eta_inner (icone_integral δb Hδb µ)).
rewrite (eta_outer_pres_int Hδb µ).
by congr icone_integral; exact: Prop_irrelevance.
Qed.

Definition eta' : icones_hom Ar B (linhom_car Ar C PX) :=
  MkIConesHom eta_outer_mcones eta_outer_mcones_pres_int.

Lemma eta'E (b : B) (c : C) (r : ar_carrier Ar X) :
  path_fun (linhom_fun ((eta' : icones_hom _ _ _) b) c) r =
  lin_pt (linhom_fun (η r) (ptensor b c)).
Proof. by rewrite -[(eta' : icones_hom _ _ _) b]/(eta_inner b) eta_innerE. Qed.

(** *** Paper [lemma:path-tens-to-one] (norm-≤1 case) — [η] is a path.

    Uncurry [eta'] to [euc : ICones(B⊗C, Path(X, 1⊸1))]; apply
    [lfun_path_swap] (with [B':=B⊗C], [C':=D':=1]) to get
    [h : ICones(1, Path(X, (B⊗C)⊸1))].  Then [path_fun (h 1) r = η r] by
    [linhom_tensor_ext] (pure-tensor extensionality): on a pure tensor
    [b⊗c], [(h 1)(r)(b⊗c) = euc(b⊗c)(r)(1) = lin_pt(η r (b⊗c))(1)
    = η r (b⊗c)] (by [tensor_uncurryK], [eta'E], [lin_pt_unit]).  Hence
    [η = path_fun (h 1)], a genuine [Path]. *)
Lemma path_tens_to_one_unit : is_measurable_path η.
Proof.
pose euc : icones_hom Ar BC PX := tensor_uncurry eta'.
pose h := lfun_path_swap (X:=X) (B:=BC) (C:=cone_one_car Ar) (D:=cone_one_car Ar) euc.
have key : forall r, path_fun ((h : icones_hom _ _ _) (c1_one Ar)) r = η r.
  move=> r.
  apply: linhom_tensor_ext => b c.
  rewrite (lfun_path_swapE euc (c1_one Ar) r (ptensor b c)).
  have Huncbc : path_fun ((euc : icones_hom _ _ _) (ptensor b c)) r =
                lin_pt (linhom_fun (η r) (ptensor b c)).
    rewrite /euc.
    have HH := tensor_curryEp (tensor_uncurry eta') b c.
    rewrite tensor_uncurryK in HH.
    rewrite -HH.
    rewrite -[linhom_fun (hfun eta' b) c r]/(path_fun (linhom_fun (hfun eta' b) c) r).
    by rewrite -[hfun eta' b]/(eta_inner b) eta_innerE.
  rewrite Huncbc.
  by rewrite lin_pt_unit.
have Heq : η = (fun r => path_fun ((h : icones_hom _ _ _) (c1_one Ar)) r).
  by apply: funext => r; rewrite key.
rewrite Heq.
exact: (path_is_path ((h : icones_hom _ _ _) (c1_one Ar))).
Qed.

End PathTensToOne.

Arguments path_tens_to_one_unit {R Ar B C X} η Hη1 ηpt.

(** ** [path_tens_to_one] — the general (merely BOUNDED) case

    For [η] bounded by [M] (not necessarily [≤ 1]), rescale into the unit
    ball [ηs r := (M+1)⁻¹ ·: η r] (norm [≤ 1]; the pure-tensor hypothesis
    [ηpt] scales by the constant [(M+1)⁻¹]); [path_tens_to_one_unit] gives
    [ηs] is a path; then [η r = (M+1) ·: ηs r], a path by
    [path_scale_is_path]. *)

Section PathTensToOneGen.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (B C : ICone.type Ar).
Variable (X : ar_obj Ar).
Local Notation One := (cone_one_car Ar).
Local Notation BC := (tensor B C).
Variable η : ar_carrier Ar X -> linhom_car Ar BC One.
Hypothesis ηbound : exists M : R, forall r, cone_norm (η r) <= M.
Hypothesis ηpt :
  forall (Z : ar_obj Ar) (φ : ar_hom Ar Z X)
         (β : ar_carrier Ar Z -> B) (γ : ar_carrier Ar Z -> C),
    is_measurable_path β -> is_measurable_path γ ->
    measurable_fun [set: ar_carrier Ar Z]
      (fun s => test_fun (ConeOneMConeAux.id_test (R:=R) (Ar:=Ar) (ar_zero Ar))
                  (ar_zero_pt Ar) (linhom_fun (η (φ s)) (ptensor (β s) (γ s)))).

Lemma path_tens_to_one : is_measurable_path η.
Proof.
have [M HM] := ηbound.
have M_ge0 : 0 <= M by apply: le_trans (HM (ar_point Ar X)); exact: cone_norm_ge0.
have S_pos : 0 < M + 1 by apply: le_lt_trans M_ge0 _; rewrite ltrDl ltr01.
have Sinv_ge0 : 0 <= (M + 1)^-1 by rewrite invr_ge0 ltW.
pose Sinv : {nonneg R} := NngNum Sinv_ge0.
pose Spos : {nonneg R} := NngNum (ltW S_pos).
pose ηs (r : ar_carrier Ar X) : linhom_car Ar BC One := linhom_scale Sinv (η r).
(* [ηs] is in the unit ball. *)
have Hηs1 : forall r, cone_norm (ηs r) <= 1.
  move=> r.
  rewrite -[cone_norm (ηs r)]/(linhom_norm (ηs r)) /ηs linhom_normh /=.
  rewrite mulrC -ler_pdivlMr ?invr_gt0 // mul1r invrK.
  by apply: le_trans (HM r) _; rewrite lerDl ler01.
(* [ηs] inherits the pure-tensor hypothesis, scaled by the constant [Sinv]. *)
have ηspt : forall (Z : ar_obj Ar) (φ : ar_hom Ar Z X)
    (β : ar_carrier Ar Z -> B) (γ : ar_carrier Ar Z -> C),
    is_measurable_path β -> is_measurable_path γ ->
    measurable_fun [set: ar_carrier Ar Z]
      (fun s => test_fun (ConeOneMConeAux.id_test (R:=R) (Ar:=Ar) (ar_zero Ar))
                  (ar_zero_pt Ar) (linhom_fun (ηs (φ s)) (ptensor (β s) (γ s)))).
  move=> Z φ β γ Hβ Hγ.
  rewrite (_ : (fun s =>
      test_fun (ConeOneMConeAux.id_test (R:=R) (Ar:=Ar) (ar_zero Ar))
        (ar_zero_pt Ar) (linhom_fun (ηs (φ s)) (ptensor (β s) (γ s)))) =
    (fun s => Sinv%:num *
      test_fun (ConeOneMConeAux.id_test (R:=R) (Ar:=Ar) (ar_zero Ar))
        (ar_zero_pt Ar) (linhom_fun (η (φ s)) (ptensor (β s) (γ s))))); last first.
    apply: funext => s.
    by rewrite /ηs /= /ConeOneMConeAux.id_test /= /ConeOneMConeAux.id_test_fun /=.
  by apply: measurable_funM; [exact: measurable_cst|exact: (ηpt φ Hβ Hγ)].
have HηsP := path_tens_to_one_unit ηs Hηs1 ηspt.
(* [η r = (M+1) ·: ηs r], a path by [path_scale_is_path]. *)
have Heq : η = (fun r => precone_scale Spos (ηs r)).
  apply: funext => r; apply: linhom_eq => z.
  rewrite -[linhom_fun (Spos *: ηs r)%PC z]/(linhom_scale_fun Spos (ηs r) z)
            /linhom_scale_fun /=.
  rewrite -[linhom_fun (ηs r) z]/(linhom_scale_fun Sinv (η r) z) /linhom_scale_fun /=.
  rewrite -precone_scale_A.
  have -> : (widen_itv (Spos%:num * Sinv%:num)%:itv : {nonneg R}) = 1%:nng.
    by apply: val_inj => /=; rewrite mulfV// gt_eqF.
  by rewrite precone_scale_1.
rewrite Heq.
exact: (path_scale_is_path Spos (MkPath HηsP)).
Qed.

End PathTensToOneGen.

Arguments path_tens_to_one {R Ar B C X} η ηbound ηpt.

(** ** [path_tens_to_X] — Paper [lemma:path-tens-to-one] at GENERAL codomain

    The P4 generalisation of [path_tens_to_one] from the scalar codomain
    [1] to an arbitrary integrable cone [D].  A function
    [η : X → (B⊗C)⊸D] that is BOUNDED and measurable ON PURE TENSORS
    (against every [D]-test) is a genuine measurable path of [(B⊗C)⊸D].

    The construction is the P3 one VERBATIM with [D] in place of the inner
    scalar [1]: [lin_pt (C:=D)] / [lo_lift (C:=D)] (already general-[C]);
    the inner codomain becomes [Path(X, 1⊸D)]; [lfun_path_swap] runs with
    [C':=1], [D':=D]; [lin_pt_unit] recovers values.  The ONLY change is in
    the three test-driven fields ([pt_inner_path], the [eta]-slot
    path/integral preservation), where the singleton [1]-test [id_test]
    (value [c1_val]) is replaced by a GENERAL [D]-test [mD] (value
    [test_fun mD s ·]); the pure-tensor hypothesis [ηpt] is correspondingly
    stated against an arbitrary [D]-test. *)

Section PathTensToX.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (B C D : ICone.type Ar).
Variable (X : ar_obj Ar).
Local Notation One := (cone_one_car Ar).
Local Notation BC := (tensor B C).
Local Notation L1D := (linhom_car Ar One D).
Local Notation PX := (path_car Ar X L1D).

Variable η : ar_carrier Ar X -> linhom_car Ar BC D.
Hypothesis Hη1 : forall r, cone_norm (η r) <= 1.

(** The pure-tensor joint-measurability hypothesis, at a general [D]-test:
    for any arity [Z], any [D]-test [mD ∈ M_Z(D)], any arrow [φ : Z → X],
    and any measurable [B]-path [β], [C]-path [γ] over [Z], the scalar
    [s ↦ mD(s, η(φ s)(β s ⊗ γ s))] is measurable on [Z].  Test position
    and [η]-index both move with the SAME [s] (the joint form delivered by
    a measurable path [H] of [B⊸(C⊸D)] via [Psi_innerE]). *)
Hypothesis ηpt :
  forall (Z : ar_obj Ar) (mD : test_of Ar Z D) (mDM : mcone_M Z mD)
         (φ : ar_hom Ar Z X)
         (β : ar_carrier Ar Z -> B) (γ : ar_carrier Ar Z -> C),
    is_measurable_path β -> is_measurable_path γ ->
    measurable_fun [set: ar_carrier Ar Z]
      (fun s => test_fun mD s (linhom_fun (η (φ s)) (ptensor (β s) (γ s)))).

(** The composite integrable map [pt_Q b r : C ⊸ (1⊸D)], the map
    [c ↦ lin_pt (η r (b⊗c))], as [lo_lift ∘ (η r) ∘ (τ b)]. *)
Definition ptX_Q (b : B) (r : ar_carrier Ar X) : linhom_car Ar C L1D :=
  linhom_comp (icones_to_linhom (lo_lift (C:=D)))
    (linhom_comp (η r) (hfun (tauL B C) b)).

Lemma ptX_QE (b : B) (r : ar_carrier Ar X) (c : C) :
  linhom_fun (ptX_Q b r) c = lin_pt (linhom_fun (η r) (ptensor b c)).
Proof.
rewrite /ptX_Q !linhom_compE icones_to_linhomE.
rewrite -[hfun (lo_lift (C:=D)) _]/(lin_pt _).
by rewrite -/(ptensor b c).
Qed.

(** The inner path [r ↦ ptX_Q b r c = lin_pt (η r (b⊗c)) : Path(X, 1⊸D)]
    is measurable, by [lo_lift_pres_path] from the [D]-path
    [r ↦ η r (b⊗c)].  Its joint measurability against a [D]-test [m] at
    arity [Z] is the pure-tensor hypothesis [ηpt] at arity [ar_prod Z X],
    with the [D]-test [m] reindexed to read the [Z]-coordinate
    ([test_reindex (ar_prod_fst Z X)]), the [η]-index selected by
    [ar_prod_snd], and constant tensor factors [b], [c]. *)
Lemma ptX_inner_path (b : B) (c : C) :
  is_measurable_path (fun r => linhom_fun (ptX_Q b r) c).
Proof.
have Hbase : is_measurable_path (fun r => linhom_fun (η r) (ptensor b c)).
  split.
    exists (cone_norm (ptensor b c)) => r.
    apply: le_trans (linhom_norm_apply_le (lexx _) (ptensor b c)) _.
    by rewrite -[X in _ <= X]mul1r; apply: ler_wpM2r;
       [exact: cone_norm_ge0|exact: Hη1].
  move=> Z m mM.
  pose mZ : test_of Ar (ar_prod Ar Z X) D := test_reindex (ar_prod_fst Z X) m.
  have mZM : mcone_M (ar_prod Ar Z X) mZ by exact: mcone_M_comp.
  have HZX := ηpt mZM (ar_prod_snd Z X)
    (@const_path_measurable R Ar B (ar_prod Ar Z X) b)
    (@const_path_measurable R Ar C (ar_prod Ar Z X) c).
  rewrite (_ : (fun p : ar_carrier Ar Z * ar_carrier Ar X =>
     test_fun m p.1 (linhom_fun (η p.2) (ptensor b c))) =
     (fun s : ar_carrier Ar (ar_prod Ar Z X) =>
      test_fun mZ s (linhom_fun (η (ar_prod_snd Z X s)) (ptensor b c)))
       \o (@ar_prod_cast R Ar Z X)); last first.
    apply: funext => p.
    rewrite /= /mZ /test_reindex /test_reindex_fun /=.
    rewrite /ar_prod_snd /ar_prod_snd_fun /ar_prod_fst /ar_prod_fst_fun
            !ar_prod_castK /=.
    by [].
  exact: (measurable_comp (F := setT) measurableT (subsetT _) HZX
            (ar_prod_cast_meas Ar Z X)).
have := lo_lift_pres_path (C:=D) (W:=X)
  (γ:=fun r => linhom_fun (η r) (ptensor b c)) Hbase.
by under [in X0 in is_measurable_path X0 -> _]eq_fun do rewrite -ptX_QE.
Qed.

Definition etaX_path (b : B) (c : C) : PX := MkPath (ptX_inner_path b c).

Lemma etaX_pathE (b : B) (c : C) (r : ar_carrier Ar X) :
  path_fun (etaX_path b c) r = lin_pt (linhom_fun (η r) (ptensor b c)).
Proof. by rewrite /etaX_path /= ptX_QE. Qed.

Lemma etaX_pathQ (b : B) (c : C) (r : ar_carrier Ar X) :
  path_fun (etaX_path b c) r = linhom_fun (ptX_Q b r) c.
Proof. by rewrite etaX_pathE ptX_QE. Qed.

(** *** The inner map [etaX_inner b : C ⊸ Path(X, 1⊸D)] (fixed [b]). *)

Section EtaXInner.
Variable b : B.

Lemma etaX_inner_linear : is_linear (etaX_path b).
Proof.
have Qlin r := linhom_pre_linear (linhom_pre_of (ptX_Q b r)).
split.
- apply: path_eq => r /=.
  have [Z0 _ _] := Qlin r.
  rewrite -[linhom_fun (ptX_Q b r) 0%PC]/(linhom_pre_fun (linhom_pre_of (ptX_Q b r)) 0%PC).
  by rewrite Z0 /path_zero_fun.
- move=> c1 c2; apply: path_eq => r /=.
  have [_ HD _] := Qlin r.
  rewrite -[linhom_fun (ptX_Q b r) (c1 + c2)%PC]
            /(linhom_pre_fun (linhom_pre_of (ptX_Q b r)) (c1 + c2)%PC).
  by rewrite HD.
- move=> s c; apply: path_eq => r /=.
  have [_ _ HZ] := Qlin r.
  rewrite -[linhom_fun (ptX_Q b r) (s *: c)%PC]
            /(linhom_pre_fun (linhom_pre_of (ptX_Q b r)) (s *: c)%PC).
  by rewrite HZ.
Qed.

Lemma etaX_inner_bounded :
  exists M : R, forall c : C, cnorm c <= 1 -> cnorm (etaX_path b c) <= M.
Proof.
exists (cone_norm b) => c Hc.
rewrite -[cnorm (etaX_path b c)]/(path_norm (etaX_path b c)).
apply: ge_sup; first exact: path_normset_nonempty.
move=> _ [r ->] /=.
rewrite ptX_QE.
apply: le_trans (lo_lift_norm_le1 (linhom_fun (η r) (ptensor b c))) _.
apply: le_trans (linhom_norm_apply_le (lexx _) (ptensor b c)) _.
have HbcN : cone_norm (ptensor b c) <= cone_norm b.
  apply: le_trans (ptensor_norm_le b c) _.
  by rewrite -[X in _ <= X]mulr1; apply: ler_wpM2l; [exact: cone_norm_ge0|exact: Hc].
apply: le_trans (ler_wpM2r (cone_norm_ge0 _) (Hη1 r)) _.
by rewrite mul1r.
Qed.

Lemma etaX_inner_continuous : is_omega_continuous (etaX_path b).
Proof.
move=> u uch ub1 fuch fub1.
apply: path_eq => r /=.
rewrite /path_sup_ball_fun.
have Qcont : is_omega_continuous (linhom_fun (ptX_Q b r)).
  by rewrite -[linhom_fun (ptX_Q b r)]/(linhom_pre_fun (linhom_pre_of (ptX_Q b r)));
     exact: linhom_pre_continuous.
rewrite (Qcont u uch ub1 (path_sup_ball_chain_pw fuch r) (path_sup_ball_ub1_pw fub1 r)).
exact: cone_sup_ball_irr.
Qed.

(** Path-preservation in [c]: tests of [Path(X,1⊸D)] are [φ ▷ (ζ ▷ mD)]
    with [φ:Y→X], [ζ] a [1]-path, [mD] a [D]-test.  The value at
    [etaX_path b (δ w)] is [c1_val(ζ s) · mD(s, η (φ s)(b ⊗ δ w))] — the
    product of [ζ]'s measurable [1]-section and the pure-tensor scalar,
    whose joint measurability is [ηpt] at arity [ar_prod Y W] (test [mD]
    reindexed by [ar_prod_fst], [η]-index [φ ∘ fst], moving [C]-factor
    [δ ∘ snd]). *)
Lemma etaX_inner_pres_path (W : ar_obj Ar) (δ : ar_carrier Ar W -> C) :
  is_measurable_path δ ->
  is_measurable_path (fun w => etaX_path b (δ w)).
Proof.
move=> Hδ.
have [[Mδ HMδ] Hδm] := Hδ.
have Mδ_ge0 : 0 <= Mδ.
  by apply: le_trans (HMδ (ar_point Ar W)); exact: cone_norm_ge0.
split.
  exists (cone_norm b * Mδ)%R => w.
  rewrite -[cnorm (etaX_path b (δ w))]/(path_norm (etaX_path b (δ w))).
  apply: ge_sup; first exact: path_normset_nonempty.
  move=> _ [r ->] /=.
  rewrite ptX_QE.
  apply: le_trans (lo_lift_norm_le1 (linhom_fun (η r) (ptensor b (δ w)))) _.
  apply: le_trans (linhom_norm_apply_le (lexx _) (ptensor b (δ w))) _.
  apply: le_trans (ler_wpM2l (cone_norm_ge0 (η r)) (ptensor_norm_le b (δ w))) _.
  rewrite mulrA.
  apply: ler_pM.
  - by rewrite mulr_ge0 // cone_norm_ge0.
  - exact: cone_norm_ge0.
  - rewrite -[X in _ <= X]mul1r; apply: ler_pM;
      [exact: cone_norm_ge0|exact: cone_norm_ge0|exact: Hη1|exact: lexx].
  - exact: HMδ.
move=> Y p pM.
have [φ [m1 [m1M Hp]]] : path_mcone_M (Y := Y) p by exact: pM.
have [ζ [ζub [mD [mDM Hm1]]]] : linhom_mcone_M (Y := Y) m1 by exact: m1M.
subst p m1.
rewrite (_ : (fun p : ar_carrier Ar Y * ar_carrier Ar W =>
   path_test φ (linhom_test ζ ζub mD mDM) m1M p.1 (etaX_path b (δ p.2))) =
   (fun p => (c1_val (path_fun ζ p.1))%:num *
             test_fun mD p.1 (linhom_fun (η (φ p.1)) (ptensor b (δ p.2))))); last first.
  apply: funext => p.
  rewrite /path_test /= /path_test_fun /=.
  rewrite /linhom_test /= /linhom_test_fun /=.
  rewrite ptX_QE lin_ptE.
  by rewrite test_linZ.
apply: measurable_funM.
- rewrite (_ : (fun x : ar_carrier Ar Y * ar_carrier Ar W => (c1_val (ζ x.1))%:num) =
     (fun s' : ar_carrier Ar Y =>
        ConeOneMConeAux.id_test (R:=R) (Ar:=Ar) (ar_zero Ar) (ar_zero_pt Ar) (path_fun ζ s'))
       \o fst); last by apply: funext => x;
       rewrite /= /ConeOneMConeAux.id_test /= /ConeOneMConeAux.id_test_fun.
  apply: (measurable_comp (F := setT) measurableT (subsetT _) _ measurable_fst).
  exact: (measurable_test_path_section (B := cone_one_car Ar)
            (m := ConeOneMConeAux.id_test (R:=R) (Ar:=Ar) (ar_zero Ar))
            (erefl) (path_is_path ζ) (ar_zero_pt Ar)).
- pose φfw : ar_hom Ar (ar_prod Ar Y W) X :=
    [the {mfun _ >-> _} of φ \o ar_prod_fst Y W].
  pose mDfw : test_of Ar (ar_prod Ar Y W) D := test_reindex (ar_prod_fst Y W) mD.
  have mDfwM : mcone_M (ar_prod Ar Y W) mDfw by exact: mcone_M_comp.
  have HYW := ηpt mDfwM φfw
    (@const_path_measurable R Ar B (ar_prod Ar Y W) b)
    (reindex_path_measurable (ar_prod_snd Y W) Hδ).
  rewrite (_ : (fun x : ar_carrier Ar Y * ar_carrier Ar W =>
     test_fun mD x.1 (linhom_fun (η (φ x.1)) (ptensor b (δ x.2)))) =
     (fun s : ar_carrier Ar (ar_prod Ar Y W) =>
      test_fun mDfw s
        (linhom_fun (η (φfw s)) (ptensor b (δ (ar_prod_snd Y W s)))))
       \o (@ar_prod_cast R Ar Y W)); last first.
    apply: funext => p.
    rewrite /φfw /mDfw /test_reindex /test_reindex_fun /=.
    rewrite /ar_prod_fst /ar_prod_fst_fun /ar_prod_snd /ar_prod_snd_fun
            !ar_prod_castK /=.
    by [].
  exact: (measurable_comp (F := setT) measurableT (subsetT _) HYW
            (ar_prod_cast_meas Ar Y W)).
Qed.

Definition etaX_inner_pre : linhom_pre Ar C PX :=
  MkLinhomPre (etaX_path b) etaX_inner_linear etaX_inner_continuous
              etaX_inner_bounded
              (fun W δ Hδ => etaX_inner_pres_path (W:=W) (δ:=δ) Hδ).

(** Integral-preservation in [c]: by [icone_integral_eqP] on [Path(X,1⊸D)]
    at an arity-0 path-test [φ ▷ (ζ ▷ mD)].  The value at [etaX_path b c]
    is [c1_val(ζ z) · mD(z, η (φ z)(b ⊗ c))]; the [(B⊗C)⊸D]-section
    [c ↦ η (φ z)(b ⊗ c)] is the integral-preserving composite
    [LL := (η (φ z)) ∘ (τ b)], so [mD(z, LL(∫δ)) = ∫ mD(z, LL(δ w))] by
    [LL]'s integral law + the [D]-test [icone_integralP], and the scalar
    [c1_val(ζ z)] factors out via [ge0_integralZl_EFin]. *)
Lemma etaX_inner_pres_int (W : ar_obj Ar) (δ : ar_carrier Ar W -> C)
    (Hδ : is_measurable_path δ) (µ : fmeas R (ar_carrier Ar W)) :
  linhom_pre_fun etaX_inner_pre (icone_integral δ Hδ µ) =
  icone_integral
    (fun w => linhom_pre_fun etaX_inner_pre (δ w))
    (linhom_pre_pres_path etaX_inner_pre W δ Hδ) µ.
Proof.
rewrite -[linhom_pre_fun etaX_inner_pre]/(etaX_path b).
have HE : icone_integral (fun w => etaX_path b (δ w))
            (etaX_inner_pres_path Hδ) µ =
          icone_integral (fun w => etaX_path b (δ w))
            (linhom_pre_pres_path etaX_inner_pre W δ Hδ) µ.
  by congr icone_integral; exact: Prop_irrelevance.
rewrite -HE.
apply: icone_integral_eqP => p pM z.
have [φ [m1 [m1M Hp]]] : path_mcone_M (Y := ar_zero Ar) p by exact: pM.
have [ζ [ζub [mD [mDM Hm1]]]] : linhom_mcone_M (Y := ar_zero Ar) m1 by exact: m1M.
subst p m1.
set K : R := (c1_val (path_fun ζ z))%:num.
have valE : forall c : C,
    path_test φ (linhom_test ζ ζub mD mDM) m1M z (etaX_path b c) =
    K * test_fun mD z (linhom_fun (η (φ z)) (ptensor b c)).
  move=> c.
  rewrite /path_test /= /path_test_fun /= /linhom_test /= /linhom_test_fun /=.
  rewrite ptX_QE lin_ptE test_linZ.
  by rewrite /K.
rewrite valE.
under [in RHS]eq_integral => r _ do rewrite valE.
pose r0 := φ z.
pose LL : linhom_car Ar C D := linhom_comp (η r0) (hfun (tauL B C) b).
have LLE : forall c : C, linhom_fun (η r0) (ptensor b c) = linhom_fun LL c.
  by move=> c; rewrite /LL linhom_compE -/(ptensor b c).
rewrite -/r0.
under [in RHS]eq_integral => r _ do rewrite LLE.
rewrite LLE.
have HLLint := linhom_pres_int LL W δ Hδ µ.
have Hsec : test_fun mD z (linhom_fun LL (icone_integral δ Hδ µ)) =
  fine (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar W])
          (test_fun mD z (linhom_fun LL (δ r)))%:E).
  rewrite -[linhom_fun LL (icone_integral δ Hδ µ)]/(LL (icone_integral δ Hδ µ)).
  rewrite HLLint.
  have := icone_integralP (fun r => LL (δ r)) (linhom_pre_pres_path LL W δ Hδ) µ
            mD mDM z.
  by [].
rewrite Hsec.
have Kge0 : 0 <= K by rewrite /K.
have meas_f : measurable_fun [set: ar_carrier Ar W]
    (fun r => (test_fun mD z (linhom_fun LL (δ r)))%:E).
  apply/measurable_EFinP.
  exact: (measurable_test_path_section (B := D)
            (m := mD) mDM (linhom_pre_pres_path LL W δ Hδ) z).
under [in RHS]eq_integral => r _ do rewrite EFinM.
rewrite lebesgue_integral_nonneg.ge0_integralZl_EFin//;
  last by move=> r _; rewrite lee_fin test_ge0.
rewrite fineM//.
rewrite ge0_fin_numE; last by apply: integral_ge0 => r _; rewrite lee_fin test_ge0.
have [[Mδ HMδ] _] := Hδ.
apply: (@le_lt_trans _ _
  (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar W]) (cone_norm LL * Mδ)%:E)%E).
  apply: (ge0_le_integral _ measurableT _ meas_f (measurable_cst _)).
  - by move=> r _; rewrite lee_fin test_ge0.
  - move=> r _; rewrite lee_fin.
    apply: le_trans (test_norm_le mD z (linhom_fun LL (δ r))) _.
    apply: le_trans (linhom_norm_apply_le (lexx _) (δ r)) _.
    by apply: ler_wpM2l; [exact: linhom_norm_ge0|exact: HMδ].
rewrite -[(fun=> _)]/(cst (cone_norm LL * Mδ)%:E)
        lebesgue_integral_nonneg.integral_cst//.
by rewrite ltey_eq fin_numM// fmeas_setT_fin.
Qed.

End EtaXInner.

(** The inner element [etaX_inner b : C ⊸ Path(X, 1⊸D)]. *)
Definition etaX_inner (b : B) : linhom_car Ar C PX :=
  MkLinhom (etaX_inner_pre b) (@etaX_inner_pres_int b).

Lemma etaX_innerE (b : B) (c : C) (r : ar_carrier Ar X) :
  path_fun (linhom_fun (etaX_inner b) c) r =
  lin_pt (linhom_fun (η r) (ptensor b c)).
Proof. by rewrite -[linhom_fun (etaX_inner b) c]/(etaX_path b c) etaX_pathE. Qed.

(** Bilinearity of the pure tensor in the [B]-slot. *)
Lemma ptX_linB (b1 b2 : B) (c : C) :
  ptensor (b1 + b2)%PC c = (ptensor b1 c + ptensor b2 c)%PC.
Proof.
have [_ HD _] := cones_hom_linear (mcones_hom_cones (icones_hom_mcones (tauL B C))).
rewrite /ptensor.
rewrite -[hfun (tauL B C) (b1 + b2)%PC]
          /(cones_hom_fun (mcones_hom_cones (icones_hom_mcones (tauL B C))) (b1 + b2)%PC).
rewrite HD.
by rewrite [linhom_fun (_ + _)%PC c]/linhom_fun /= /linhom_add_fun /=.
Qed.

Lemma ptX_zeroB (c : C) : ptensor (0%PC : B) c = (0%PC : BC).
Proof.
have [Z0 _ _] := cones_hom_linear (mcones_hom_cones (icones_hom_mcones (tauL B C))).
rewrite /ptensor.
rewrite -[hfun (tauL B C) (0%PC : B)]
          /(cones_hom_fun (mcones_hom_cones (icones_hom_mcones (tauL B C))) (0%PC : B)).
rewrite Z0.
by rewrite [linhom_fun (0%PC : linhom_car Ar C BC) c]/linhom_fun /= /linhom_zero_fun.
Qed.

Lemma ptX_scaleB (s : {nonneg R}) (b : B) (c : C) :
  ptensor (s *: b)%PC c = (s *: ptensor b c)%PC.
Proof.
have [_ _ HZ] := cones_hom_linear (mcones_hom_cones (icones_hom_mcones (tauL B C))).
rewrite /ptensor.
rewrite -[hfun (tauL B C) (s *: b)%PC]
          /(cones_hom_fun (mcones_hom_cones (icones_hom_mcones (tauL B C))) (s *: b)%PC).
rewrite HZ.
by rewrite [linhom_fun (s *: _)%PC c]/linhom_fun /= /linhom_scale_fun.
Qed.

(** *** The outer morphism [etaX' : ICones(B, C ⊸ Path(X, 1⊸D))]. *)

Lemma etaX_outer_linear : is_linear etaX_inner.
Proof.
split.
- apply: linhom_eq => c; apply: path_eq => r /=.
  rewrite ptX_QE ptX_zeroB.
  have [Z0 _ _] := linhom_pre_linear (linhom_pre_of (η r)).
  rewrite -[linhom_fun (η r) 0%PC]/(linhom_pre_fun (linhom_pre_of (η r)) 0%PC) Z0.
  have [Z0' _ _] := @lo_lift_linear R Ar D.
  rewrite -[lin_pt 0%PC]/(lin_pt (C:=D) 0%PC) Z0'.
  by rewrite /path_zero_fun.
- move=> b1 b2; apply: linhom_eq => c; apply: path_eq => r /=.
  rewrite !ptX_QE ptX_linB.
  have [_ HD _] := linhom_pre_linear (linhom_pre_of (η r)).
  rewrite -[linhom_fun (η r) (ptensor b1 c + ptensor b2 c)%PC]
            /(linhom_pre_fun (linhom_pre_of (η r)) (ptensor b1 c + ptensor b2 c)%PC) HD.
  have [_ HD' _] := @lo_lift_linear R Ar D.
  rewrite -[lin_pt (linhom_fun (η r) (ptensor b1 c) + linhom_fun (η r) (ptensor b2 c))%PC]
            /(lin_pt (C:=D)
                (linhom_fun (η r) (ptensor b1 c) + linhom_fun (η r) (ptensor b2 c))%PC) HD'.
  by [].
- move=> s b; apply: linhom_eq => c; apply: path_eq => r /=.
  rewrite !ptX_QE ptX_scaleB.
  have [_ _ HZ] := linhom_pre_linear (linhom_pre_of (η r)).
  rewrite -[linhom_fun (η r) (s *: ptensor b c)%PC]
            /(linhom_pre_fun (linhom_pre_of (η r)) (s *: ptensor b c)%PC) HZ.
  have [_ _ HZ'] := @lo_lift_linear R Ar D.
  rewrite -[lin_pt (s *: linhom_fun (η r) (ptensor b c))%PC]
            /(lin_pt (C:=D) (s *: linhom_fun (η r) (ptensor b c))%PC) HZ'.
  by [].
Qed.

Lemma etaX_outer_norm (b : B) : cone_norm (etaX_inner b) <= cone_norm b.
Proof.
rewrite -[cone_norm (etaX_inner b)]/(linhom_norm (etaX_inner b)).
apply: linhom_norm_sup_lub => c Hc.
rewrite -[cnorm (linhom_fun (etaX_inner b) c)]/(path_norm (linhom_fun (etaX_inner b) c)).
apply: ge_sup; first exact: path_normset_nonempty.
move=> _ [r ->].
rewrite etaX_innerE.
apply: le_trans (lo_lift_norm_le1 (linhom_fun (η r) (ptensor b c))) _.
apply: le_trans (linhom_norm_apply_le (lexx _) (ptensor b c)) _.
have HbcN : cone_norm (ptensor b c) <= cone_norm b.
  apply: le_trans (ptensor_norm_le b c) _.
  by rewrite -[X in _ <= X]mulr1; apply: ler_wpM2l; [exact: cone_norm_ge0|exact: Hc].
apply: le_trans (ler_wpM2r (cone_norm_ge0 _) (Hη1 r)) _.
by rewrite mul1r.
Qed.

(** The [b]-slot composite integrable map [ptX_QB c r : B ⊸ (1⊸D)],
    [b ↦ lin_pt (η r (b⊗c))] = [lo_lift ∘ (η r) ∘ (eval_at c) ∘ τ]. *)
Definition ptX_QB (c : C) (r : ar_carrier Ar X) : linhom_car Ar B L1D :=
  linhom_comp (icones_to_linhom (lo_lift (C:=D)))
    (linhom_comp (η r) (linhom_comp (eval_at c) (icones_to_linhom (tauL B C)))).

Lemma ptX_QBE (c : C) (r : ar_carrier Ar X) (b : B) :
  linhom_fun (ptX_QB c r) b = lin_pt (linhom_fun (η r) (ptensor b c)).
Proof.
rewrite /ptX_QB !linhom_compE icones_to_linhomE.
rewrite -[hfun (lo_lift (C:=D)) _]/(lin_pt _).
rewrite eval_atE icones_to_linhomE.
by rewrite -/(ptensor b c).
Qed.

Lemma etaX_outer_continuous : is_omega_continuous etaX_inner.
Proof.
move=> u uch ub1 fuch fub1.
apply: (@linhom_mcone_M_sep _ _ C PX) => p.
move=> [γC [γCub [mPX [mPXM Hp]]]].
have [φ [m1 [m1M HmPX]]] : path_mcone_M (Y := ar_zero Ar) mPX by exact: mPXM.
have [ζ [ζub [m2 [m2M Hm1]]]] : linhom_mcone_M (Y := ar_zero Ar) m1 by exact: m1M.
rewrite Hp /linhom_test /linhom_test_fun /=.
set s0 := ar_zero_pt Ar.
have mPXred : forall (γ : PX),
    mPX s0 γ = m2 s0 (linhom_fun (path_fun γ (φ s0)) (path_fun ζ s0)).
  move=> γ.
  by rewrite HmPX /path_test /= /path_test_fun /= Hm1
             /linhom_test /= /linhom_test_fun /=.
rewrite !mPXred.
set c' := path_fun γC s0.
set r0 := φ s0.
rewrite -[linhom_fun (etaX_inner (cone_sup_ball u uch ub1)) c']
          /(etaX_path (cone_sup_ball u uch ub1) c').
rewrite etaX_pathE -ptX_QBE.
have Hc'1 : cone_norm c' <= 1.
  by apply: le_trans (path_norm_ub γC s0) _; rewrite -[path_norm γC]/(cnorm γC).
set φlh := ptX_QB c' r0.
have φcont : is_omega_continuous (linhom_fun φlh).
  by rewrite -[linhom_fun φlh]/(linhom_pre_fun (linhom_pre_of φlh));
     exact: linhom_pre_continuous.
have φnorm : linhom_norm φlh <= 1.
  rewrite -[linhom_norm φlh]/(cone_norm φlh).
  apply: linhom_norm_sup_lub => b Hb.
  rewrite ptX_QBE.
  apply: le_trans (lo_lift_norm_le1 (linhom_fun (η r0) (ptensor b c'))) _.
  apply: le_trans (linhom_norm_apply_le (lexx _) (ptensor b c')) _.
  apply: le_trans (ler_wpM2r (cone_norm_ge0 _) (Hη1 r0)) _.
  rewrite mul1r.
  apply: le_trans (ptensor_norm_le b c') _.
  by apply: mulr_ile1; [exact: cone_norm_ge0|exact: cone_norm_ge0|exact: Hb|exact: Hc'1].
have Hch : forall n, precone_le (linhom_fun φlh (u n)) (linhom_fun φlh (u n.+1)).
  move=> n; have [w Hw] := uch n.
  exists (linhom_fun φlh w).
  have [_ HD _] := linhom_pre_linear (linhom_pre_of φlh).
  by rewrite Hw -[linhom_fun φlh _]/(linhom_pre_fun (linhom_pre_of φlh) _) HD.
have Hub : forall n, cone_norm (linhom_fun φlh (u n)) <= 1.
  move=> n; apply: le_trans (linhom_norm_apply_le (lexx _) (u n)) _.
  rewrite -[X in _ <= X]mulr1; apply: ler_pM;
    [exact: linhom_norm_ge0|exact: cone_norm_ge0|exact: φnorm|exact: ub1].
rewrite (φcont u uch ub1 Hch Hub).
rewrite -[linhom_fun (cone_sup_ball (linhom_fun φlh \o u) Hch Hub) (ζ s0)]
          /(linhom_sup_fun Hch Hub (ζ s0)).
rewrite (linhom_sup_fun_test_sup Hch Hub m2 s0 (ζ s0)).
rewrite -[r0]/(φ s0).
rewrite -(mPXred (linhom_fun (cone_sup_ball (etaX_inner \o u) fuch fub1) c')).
rewrite -[linhom_fun (cone_sup_ball (etaX_inner \o u) fuch fub1) c']
          /(linhom_sup_fun fuch fub1 c').
rewrite (linhom_sup_fun_test_sup fuch fub1 mPX s0 c').
congr (sup _); apply: eq_imagel => n _ /=.
rewrite (mPXred (linhom_fun (etaX_inner (u n)) c')).
congr (m2 s0 (linhom_fun _ (ζ s0))).
rewrite -[linhom_fun (etaX_inner (u n)) c' (φ s0)]
          /(path_fun (linhom_fun (etaX_inner (u n)) c') (φ s0)).
rewrite etaX_innerE.
by rewrite ptX_QBE.
Qed.

(** Path-preservation in [b]. *)
Lemma etaX_outer_pres_path (W : ar_obj Ar) (δb : ar_carrier Ar W -> B) :
  is_measurable_path δb ->
  is_measurable_path (fun w => etaX_inner (δb w)).
Proof.
move=> Hδb.
have [[Mδ HMδ] Hδbm] := Hδb.
have Mδ_ge0 : 0 <= Mδ.
  by apply: le_trans (HMδ (ar_point Ar W)); exact: cone_norm_ge0.
split.
  exists Mδ => w.
  by apply: le_trans (etaX_outer_norm (δb w)) _; exact: HMδ.
move=> Y p pM.
have [γC [γCub [mPX [mPXM Hp]]]] : linhom_mcone_M (Y := Y) p by exact: pM.
have [φ [m1 [m1M HmPX]]] : path_mcone_M (Y := Y) mPX by exact: mPXM.
have [ζ [ζub [mD [mDM Hm1]]]] : linhom_mcone_M (Y := Y) m1 by exact: m1M.
subst p mPX m1.
rewrite (_ : (fun p : ar_carrier Ar Y * ar_carrier Ar W =>
   linhom_test γC γCub (path_test φ (linhom_test ζ ζub mD mDM) m1M) mPXM p.1
     (etaX_inner (δb p.2))) =
   (fun p => (c1_val (path_fun ζ p.1))%:num *
             test_fun mD p.1 (linhom_fun (η (φ p.1))
                        (ptensor (δb p.2) (path_fun γC p.1))))); last first.
  apply: funext => p.
  rewrite /linhom_test /= /linhom_test_fun /=.
  rewrite ptX_QE lin_ptE test_linZ.
  by [].
apply: measurable_funM.
- rewrite (_ : (fun x : ar_carrier Ar Y * ar_carrier Ar W => (c1_val (ζ x.1))%:num) =
     (fun s' : ar_carrier Ar Y =>
        ConeOneMConeAux.id_test (R:=R) (Ar:=Ar) (ar_zero Ar) (ar_zero_pt Ar) (path_fun ζ s'))
       \o fst); last by apply: funext => x;
       rewrite /= /ConeOneMConeAux.id_test /= /ConeOneMConeAux.id_test_fun.
  apply: (measurable_comp (F := setT) measurableT (subsetT _) _ measurable_fst).
  exact: (measurable_test_path_section (B := cone_one_car Ar)
            (m := ConeOneMConeAux.id_test (R:=R) (Ar:=Ar) (ar_zero Ar))
            (erefl) (path_is_path ζ) (ar_zero_pt Ar)).
- pose φfw : ar_hom Ar (ar_prod Ar Y W) X :=
    [the {mfun _ >-> _} of φ \o ar_prod_fst Y W].
  pose mDfw : test_of Ar (ar_prod Ar Y W) D := test_reindex (ar_prod_fst Y W) mD.
  have mDfwM : mcone_M (ar_prod Ar Y W) mDfw by exact: mcone_M_comp.
  have HYW := ηpt mDfwM φfw
    (reindex_path_measurable (ar_prod_snd Y W) Hδb)
    (reindex_path_measurable (ar_prod_fst Y W) (path_is_path γC)).
  rewrite (_ : (fun x : ar_carrier Ar Y * ar_carrier Ar W =>
     test_fun mD x.1 (linhom_fun (η (φ x.1)) (ptensor (δb x.2) (path_fun γC x.1)))) =
     (fun s : ar_carrier Ar (ar_prod Ar Y W) =>
      test_fun mDfw s
        (linhom_fun (η (φfw s))
           (ptensor (δb (ar_prod_snd Y W s)) (path_fun γC (ar_prod_fst Y W s)))))
       \o (@ar_prod_cast R Ar Y W)); last first.
    apply: funext => p.
    rewrite /φfw /mDfw /test_reindex /test_reindex_fun /=.
    rewrite /ar_prod_fst /ar_prod_fst_fun /ar_prod_snd /ar_prod_snd_fun
            !ar_prod_castK /=.
    by [].
  exact: (measurable_comp (F := setT) measurableT (subsetT _) HYW
            (ar_prod_cast_meas Ar Y W)).
Qed.

(** Integral-preservation in [b]. *)
Lemma etaX_outer_pres_int (W : ar_obj Ar) (δb : ar_carrier Ar W -> B)
    (Hδb : is_measurable_path δb) (µ : fmeas R (ar_carrier Ar W)) :
  etaX_inner (icone_integral δb Hδb µ) =
  icone_integral (fun w => etaX_inner (δb w)) (etaX_outer_pres_path Hδb) µ.
Proof.
apply: icone_integral_eqP => p pM z.
have [γC [γCub [mPX [mPXM Hp]]]] : linhom_mcone_M (Y := ar_zero Ar) p by exact: pM.
have [φ [m1 [m1M HmPX]]] : path_mcone_M (Y := ar_zero Ar) mPX by exact: mPXM.
have [ζ [ζub [mD [mDM Hm1]]]] : linhom_mcone_M (Y := ar_zero Ar) m1 by exact: m1M.
subst p mPX m1.
set K : R := (c1_val (path_fun ζ z))%:num.
set c' := path_fun γC z.
set r0 := φ z.
have valE : forall b : B,
    linhom_test γC γCub (path_test φ (linhom_test ζ ζub mD mDM) m1M) mPXM z
      (etaX_inner b) =
    K * test_fun mD z (linhom_fun (η r0) (ptensor b c')).
  move=> b.
  rewrite /linhom_test /= /linhom_test_fun /=.
  rewrite /path_test /= /path_test_fun /=.
  rewrite ptX_QE lin_ptE test_linZ.
  by rewrite /K /c' /r0.
rewrite valE.
under [in RHS]eq_integral => w _ do rewrite valE.
pose LLb : linhom_car Ar B D :=
  linhom_comp (η r0) (linhom_comp (eval_at c') (icones_to_linhom (tauL B C))).
have LLbE : forall b : B, linhom_fun (η r0) (ptensor b c') = linhom_fun LLb b.
  move=> b; rewrite /LLb !linhom_compE icones_to_linhomE eval_atE.
  by rewrite -/(ptensor b c').
rewrite LLbE.
under [in RHS]eq_integral => w _ do rewrite LLbE.
have HLLbint := linhom_pres_int LLb W δb Hδb µ.
have Hsec : test_fun mD z (linhom_fun LLb (icone_integral δb Hδb µ)) =
  fine (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar W])
          (test_fun mD z (linhom_fun LLb (δb r)))%:E).
  rewrite -[linhom_fun LLb (icone_integral δb Hδb µ)]/(LLb (icone_integral δb Hδb µ)).
  rewrite HLLbint.
  have := icone_integralP (fun r => LLb (δb r)) (linhom_pre_pres_path LLb W δb Hδb) µ
            mD mDM z.
  by [].
rewrite Hsec.
have Kge0 : 0 <= K by rewrite /K.
have meas_f : measurable_fun [set: ar_carrier Ar W]
    (fun r => (test_fun mD z (linhom_fun LLb (δb r)))%:E).
  apply/measurable_EFinP.
  exact: (measurable_test_path_section (B := D)
            (m := mD) mDM (linhom_pre_pres_path LLb W δb Hδb) z).
under [in RHS]eq_integral => r _ do rewrite EFinM.
rewrite lebesgue_integral_nonneg.ge0_integralZl_EFin//;
  last by move=> r _; rewrite lee_fin test_ge0.
rewrite fineM//.
rewrite ge0_fin_numE; last by apply: integral_ge0 => r _; rewrite lee_fin test_ge0.
have [[Mδ HMδ] _] := Hδb.
apply: (@le_lt_trans _ _
  (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar W]) (cone_norm LLb * Mδ)%:E)%E).
  apply: (ge0_le_integral _ measurableT _ meas_f (measurable_cst _)).
  - by move=> r _; rewrite lee_fin test_ge0.
  - move=> r _; rewrite lee_fin.
    apply: le_trans (test_norm_le mD z (linhom_fun LLb (δb r))) _.
    apply: le_trans (linhom_norm_apply_le (lexx _) (δb r)) _.
    by apply: ler_wpM2l; [exact: linhom_norm_ge0|exact: HMδ].
rewrite -[(fun=> _)]/(cst (cone_norm LLb * Mδ)%:E)
        lebesgue_integral_nonneg.integral_cst//.
by rewrite ltey_eq fin_numM// fmeas_setT_fin.
Qed.

(** *** Assembly of [etaX' : ICones(B, C ⊸ Path(X, 1⊸D))]. *)
Definition etaX_outer_cones : cones_hom B (linhom_car Ar C PX) :=
  ConesHom etaX_inner etaX_outer_linear etaX_outer_continuous etaX_outer_norm.

Definition etaX_outer_mcones : mcones_hom Ar B (linhom_car Ar C PX) :=
  MkMConesHom etaX_outer_cones
    (fun W δb Hδb => etaX_outer_pres_path (W:=W) (δb:=δb) Hδb).

Lemma etaX_outer_mcones_pres_int
    (W : ar_obj Ar) (δb : ar_carrier Ar W -> B)
    (Hδb : is_measurable_path δb) (µ : fmeas R (ar_carrier Ar W)) :
  cones_hom_fun (mcones_hom_cones etaX_outer_mcones) (icone_integral δb Hδb µ) =
  icone_integral
    (fun w => cones_hom_fun (mcones_hom_cones etaX_outer_mcones) (δb w))
    (mcones_hom_pres_path etaX_outer_mcones W δb Hδb) µ.
Proof.
rewrite -[cones_hom_fun _ _]/(etaX_inner (icone_integral δb Hδb µ)).
rewrite (etaX_outer_pres_int Hδb µ).
by congr icone_integral; exact: Prop_irrelevance.
Qed.

Definition etaX' : icones_hom Ar B (linhom_car Ar C PX) :=
  MkIConesHom etaX_outer_mcones etaX_outer_mcones_pres_int.

Lemma etaX'E (b : B) (c : C) (r : ar_carrier Ar X) :
  path_fun (linhom_fun ((etaX' : icones_hom _ _ _) b) c) r =
  lin_pt (linhom_fun (η r) (ptensor b c)).
Proof. by rewrite -[(etaX' : icones_hom _ _ _) b]/(etaX_inner b) etaX_innerE. Qed.

(** *** Paper [lemma:path-tens-to-one] at codomain [D] (norm-≤1 case).

    Uncurry [etaX'] to [euc : ICones(B⊗C, Path(X, 1⊸D))]; apply
    [lfun_path_swap] (with [B':=B⊗C], [C':=1], [D':=D]) to get
    [h : ICones(1, Path(X, (B⊗C)⊸D))].  Then [path_fun (h 1) r = η r] by
    [linhom_tensor_ext] (pure-tensor extensionality): on a pure tensor
    [b⊗c], [(h 1)(r)(b⊗c) = euc(b⊗c)(r)(1) = lin_pt(η r (b⊗c))(1)
    = η r (b⊗c)] (by [tensor_uncurryK], [etaX'E], [lin_pt_unit]). *)
Lemma path_tens_to_X_unit : is_measurable_path η.
Proof.
pose euc : icones_hom Ar BC PX := tensor_uncurry etaX'.
pose h := lfun_path_swap (X:=X) (B:=BC) (C:=cone_one_car Ar) (D:=D) euc.
have key : forall r, path_fun ((h : icones_hom _ _ _) (c1_one Ar)) r = η r.
  move=> r.
  apply: linhom_tensor_ext => b c.
  rewrite (lfun_path_swapE euc (c1_one Ar) r (ptensor b c)).
  have Huncbc : path_fun ((euc : icones_hom _ _ _) (ptensor b c)) r =
                lin_pt (linhom_fun (η r) (ptensor b c)).
    rewrite /euc.
    have HH := tensor_curryEp (tensor_uncurry etaX') b c.
    rewrite tensor_uncurryK in HH.
    rewrite -HH.
    rewrite -[linhom_fun (hfun etaX' b) c r]/(path_fun (linhom_fun (hfun etaX' b) c) r).
    by rewrite -[hfun etaX' b]/(etaX_inner b) etaX_innerE.
  rewrite Huncbc.
  by rewrite lin_pt_unit.
have Heq : η = (fun r => path_fun ((h : icones_hom _ _ _) (c1_one Ar)) r).
  by apply: funext => r; rewrite key.
rewrite Heq.
exact: (path_is_path ((h : icones_hom _ _ _) (c1_one Ar))).
Qed.

End PathTensToX.

Arguments path_tens_to_X_unit {R Ar B C D X} η Hη1 ηpt.

(** ** [path_tens_to_X] — the general (merely BOUNDED) case at codomain [D] *)

Section PathTensToXGen.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (B C D : ICone.type Ar).
Variable (X : ar_obj Ar).
Local Notation One := (cone_one_car Ar).
Local Notation BC := (tensor B C).
Variable η : ar_carrier Ar X -> linhom_car Ar BC D.
Hypothesis ηbound : exists M : R, forall r, cone_norm (η r) <= M.
Hypothesis ηpt :
  forall (Z : ar_obj Ar) (mD : test_of Ar Z D) (mDM : mcone_M Z mD)
         (φ : ar_hom Ar Z X)
         (β : ar_carrier Ar Z -> B) (γ : ar_carrier Ar Z -> C),
    is_measurable_path β -> is_measurable_path γ ->
    measurable_fun [set: ar_carrier Ar Z]
      (fun s => test_fun mD s (linhom_fun (η (φ s)) (ptensor (β s) (γ s)))).

Lemma path_tens_to_X : is_measurable_path η.
Proof.
have [M HM] := ηbound.
have M_ge0 : 0 <= M by apply: le_trans (HM (ar_point Ar X)); exact: cone_norm_ge0.
have S_pos : 0 < M + 1 by apply: le_lt_trans M_ge0 _; rewrite ltrDl ltr01.
have Sinv_ge0 : 0 <= (M + 1)^-1 by rewrite invr_ge0 ltW.
pose Sinv : {nonneg R} := NngNum Sinv_ge0.
pose Spos : {nonneg R} := NngNum (ltW S_pos).
pose ηs (r : ar_carrier Ar X) : linhom_car Ar BC D := linhom_scale Sinv (η r).
have Hηs1 : forall r, cone_norm (ηs r) <= 1.
  move=> r.
  rewrite -[cone_norm (ηs r)]/(linhom_norm (ηs r)) /ηs linhom_normh /=.
  rewrite mulrC -ler_pdivlMr ?invr_gt0 // mul1r invrK.
  by apply: le_trans (HM r) _; rewrite lerDl ler01.
have ηspt : forall (Z : ar_obj Ar) (mD : test_of Ar Z D) (mDM : mcone_M Z mD)
    (φ : ar_hom Ar Z X)
    (β : ar_carrier Ar Z -> B) (γ : ar_carrier Ar Z -> C),
    is_measurable_path β -> is_measurable_path γ ->
    measurable_fun [set: ar_carrier Ar Z]
      (fun s => test_fun mD s (linhom_fun (ηs (φ s)) (ptensor (β s) (γ s)))).
  move=> Z mD mDM φ β γ Hβ Hγ.
  rewrite (_ : (fun s =>
      test_fun mD s (linhom_fun (ηs (φ s)) (ptensor (β s) (γ s)))) =
    (fun s => Sinv%:num *
      test_fun mD s (linhom_fun (η (φ s)) (ptensor (β s) (γ s))))); last first.
    apply: funext => s.
    rewrite /ηs.
    rewrite -[linhom_fun (Sinv *: η (φ s))%PC (ptensor (β s) (γ s))]
              /(linhom_scale_fun Sinv (η (φ s)) (ptensor (β s) (γ s))).
    by rewrite /linhom_scale_fun /= test_linZ.
  by apply: measurable_funM; [exact: measurable_cst|exact: (ηpt mDM φ Hβ Hγ)].
have HηsP := path_tens_to_X_unit ηs Hηs1 ηspt.
have Heq : η = (fun r => precone_scale Spos (ηs r)).
  apply: funext => r; apply: linhom_eq => z.
  rewrite -[linhom_fun (Spos *: ηs r)%PC z]/(linhom_scale_fun Spos (ηs r) z)
            /linhom_scale_fun /=.
  rewrite -[linhom_fun (ηs r) z]/(linhom_scale_fun Sinv (η r) z) /linhom_scale_fun /=.
  rewrite -precone_scale_A.
  have -> : (widen_itv (Spos%:num * Sinv%:num)%:itv : {nonneg R}) = 1%:nng.
    by apply: val_inj => /=; rewrite mulfV// gt_eqF.
  by rewrite precone_scale_1.
rewrite Heq.
exact: (path_scale_is_path Spos (MkPath HηsP)).
Qed.

End PathTensToXGen.

Arguments path_tens_to_X {R Ar B C D X} η ηbound ηpt.

(** ** Thm 5.12 [tensor_hom_iso] — the inverse [Ψ] as an [icones_hom]

    The inverse [Ψ : B⊸(C⊸D) → (B⊗C)⊸D] sends [h] to [Psi_inner h] (the
    element [b⊗c ↦ h(b)(c)], Paper Eq 5.1 inverse).  Each structure
    field reduces, via the pure-tensor law [Psi_innerE] and the
    pure-tensor extensionality [linhom_tensor_ext] (Prop 5.14), to a
    fact about [h] itself:
    - LINEARITY: equalities of [(B⊗C)⊸D] elements, reduced by
      [linhom_tensor_ext] to pointwise [Psi_innerE] + the pointwise
      structure of [B⊸(C⊸D)].
    - NORM [≤1]: [Psi_inner h] equals (by [linhom_tensor_ext]) the EXACT
      [‖h‖]-rescaling [‖h‖ · icones_to_linhom(tensor_uncurry(‖h‖⁻¹·h))],
      whose operator norm is [‖h‖ · ‖icones_to_linhom(…)‖ ≤ ‖h‖] by
      [icones_to_linhom_norm_le1].  The [‖h‖ = 0] edge is closed by
      [cone_normz] ([h = 0]).
    - ω-CONTINUITY: reduced by [linhom_tensor_ext] to a [D]-equation at
      [b⊗c], then by [mcone_M_sep] to a real-sup identity, with the
      "evaluate at [b] then [c]" map [ev_bc := eval_at c ∘ eval_at b :
      (B⊸(C⊸D)) ⊸ D] supplying the [linhom] ω-continuity ([test_of_sup])
      on the LHS and [linhom_sup_fun_test_sup] the RHS.
    - PATH-preservation: [r ↦ Psi_inner (H r)] is a measurable path by
      [path_tens_to_X] (codomain [D]); its pure-tensor hypothesis [ηpt]
      is [H]'s own path-preservation read through [Psi_innerE].
    - INTEGRAL-preservation: via [Φ(Ψ h) = h] ([cod_eq] + pointwise
      [Phi_iconesE]/[Psi_innerE]) + [Φ]'s integral law [Phi_pres_int]. *)

Section PsiIConesHom.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C D : ICone.type Ar.

Local Notation BC := (tensor B C).
Local Notation Dom := (linhom_car Ar B (linhom_car Ar C D)).
Local Notation Cod := (linhom_car Ar BC D).

(** The underlying map [Ψ : Dom → Cod]. *)
Definition Psi_map (h : Dom) : Cod := Psi_inner h.

(** *** Linearity of [Ψ] — pure [Psi_innerE] + linearity of [h]. *)
Lemma Psi_linear : is_linear Psi_map.
Proof.
split.
- apply: linhom_tensor_ext => b c; rewrite /Psi_map Psi_innerE.
  rewrite [linhom_fun (0%PC : Cod) (ptensor b c)]/linhom_fun /= /linhom_zero_fun.
  have Z0d : linhom_fun (0%PC : Dom) b = (0%PC : linhom_car Ar C D).
    by have [Z0 _ _] := linhom_pre_linear (linhom_pre_of (0%PC : Dom)); exact: Z0.
  rewrite Z0d.
  by rewrite [linhom_fun (0%PC : linhom_car Ar C D) c]/linhom_fun /= /linhom_zero_fun.
- move=> h1 h2; apply: linhom_tensor_ext => b c.
  rewrite /Psi_map Psi_innerE.
  rewrite [linhom_fun (Psi_inner h1 + Psi_inner h2)%PC (ptensor b c)]/linhom_fun /=
          /linhom_add_fun.
  rewrite -!/(linhom_fun (Psi_inner _) (ptensor b c)) !Psi_innerE.
  rewrite [linhom_fun (h1 + h2)%PC b]/linhom_fun /= /linhom_add_fun.
  by rewrite [linhom_fun (_ + _)%PC c]/linhom_fun /= /linhom_add_fun.
- move=> r h; apply: linhom_tensor_ext => b c.
  rewrite /Psi_map Psi_innerE.
  rewrite [linhom_fun (r *: Psi_inner h)%PC (ptensor b c)]/linhom_fun /=
          /linhom_scale_fun.
  rewrite -!/(linhom_fun (Psi_inner _) (ptensor b c)) !Psi_innerE.
  rewrite [linhom_fun (r *: h)%PC b]/linhom_fun /= /linhom_scale_fun.
  by rewrite [linhom_fun (_ *: _)%PC c]/linhom_fun /= /linhom_scale_fun.
Qed.

(** *** Norm decrease [‖Ψ h‖ ≤ ‖h‖] via the [‖h‖]-rescaling identity. *)

Lemma Psi_norm_le1 (h : Dom) : cone_norm (Psi_map h) <= cone_norm h.
Proof.
have nh_ge0 : 0 <= cone_norm h by exact: cone_norm_ge0.
have nhinv_ge0 : 0 <= (cone_norm h)^-1 by rewrite invr_ge0.
pose nh : {nonneg R} := NngNum nh_ge0.
pose nhinv : {nonneg R} := NngNum nhinv_ge0.
pose g : linhom_car Ar B (linhom_car Ar C D) := linhom_scale nhinv h.
have Hg : cone_norm g <= 1.
  rewrite -[cone_norm g]/(linhom_norm g) /g linhom_normh /=.
  have [/eqP h0 | hpos] := boolP (cone_norm h == 0).
    by rewrite h0 invr0 mul0r.
  by rewrite mulVf// lexx.
pose Q : Cod :=
  linhom_scale nh (icones_to_linhom (tensor_uncurry (linhom_icones g Hg))).
have HQE : Q = Psi_map h.
  apply: linhom_tensor_ext => b c.
  rewrite /Q /Psi_map Psi_innerE.
  rewrite -[linhom_fun (linhom_scale nh _) (ptensor b c)]
            /(linhom_scale_fun nh _ (ptensor b c)) /linhom_scale_fun /=.
  rewrite icones_to_linhomE.
  rewrite -[hfun (tensor_uncurry (linhom_icones g Hg)) (ptensor b c)]
            /((tensor_uncurry (linhom_icones g Hg) : icones_hom _ _ _) (ptensor b c)).
  have HH := tensor_curryEp (tensor_uncurry (linhom_icones g Hg)) b c.
  rewrite tensor_uncurryK in HH.
  rewrite -/(ptensor b c) in HH.
  rewrite -HH (linhom_iconesE g Hg b).
  rewrite /g -[linhom_fun (linhom_scale nhinv h) b]/(linhom_scale_fun nhinv h b)
            /linhom_scale_fun /=.
  rewrite -[linhom_fun (linhom_scale nhinv (linhom_fun h b)) c]
            /(linhom_scale_fun nhinv (linhom_fun h b) c) /linhom_scale_fun /=.
  rewrite -precone_scale_A.
  have [/eqP h0 | hpos] := boolP (cone_norm h == 0).
    have hz : h = (0%PC : Dom) by apply: cone_normz; rewrite -[cone_norm h]/(cnorm h) h0.
    rewrite hz.
    have ->: linhom_fun (linhom_fun (0%PC : Dom) b) c = (precone_zero : D) by [].
    by rewrite precone_scale_0r.
  have -> : (widen_itv (nh%:num * nhinv%:num)%:itv : {nonneg R}) = 1%:nng.
    by apply: val_inj => /=; rewrite mulfV.
  by rewrite precone_scale_1.
rewrite -HQE /Q.
rewrite -[cone_norm (linhom_scale nh _)]/(linhom_norm (linhom_scale nh _)) linhom_normh /=.
rewrite -[cone_norm h]/(nh%:num) -[X in _ <= X]mulr1.
apply: ler_wpM2l; first exact: nngnum_ge0.
exact: icones_to_linhom_norm_le1.
Qed.

(** *** ω-continuity of [Ψ].

    Reduce by [linhom_tensor_ext] to a [D]-equation at [b⊗c]; then by
    [mcone_M_sep] to a real-sup identity at each [D]-test [mD].  The
    inner [c] is rescaled into the unit ball ([c' := (‖c‖+1)⁻¹·c]) so
    that [γ_{c'} ▷ mD] is a genuine [C⊸D]-test; the [b]-sup is then
    unfolded by [linhom_sup_fun_test_sup] on [Dom = B⊸(C⊸D)] (which
    rescales [b] internally), and the [Cod = (B⊗C)⊸D] sup by another
    [linhom_sup_fun_test_sup] at [b⊗c]; both give the scaled real-sup
    [sup_n mD(s₀, u_n(b)(c'))], matched by [sup_scaleM]. *)
Lemma Psi_continuous : is_omega_continuous Psi_map.
Proof.
move=> u uch ub1 fuch fub1.
apply: linhom_tensor_ext => b c.
set s0 := ar_zero_pt Ar.
apply: mcone_M_sep => mD mDM.
have S_pos : 0 < cone_norm c + 1 by exact: cnorm_succ_pos.
have Sinv_ge0 : 0 <= (cone_norm c + 1)^-1 by rewrite invr_ge0 ltW.
pose Sinv : {nonneg R} := NngNum Sinv_ge0.
pose c' : C := precone_scale Sinv c.
have Hc'_unit : cone_norm c' <= 1.
  rewrite /c' cone_normh /=.
  rewrite mulrC ler_pdivrMr // mul1r.
  by rewrite -[X in X <= _]addr0 lerD2l ler01.
have Hγc' : cone_norm (const_x_path c') <= 1.
  by rewrite /cone_norm /= const_x_path_normE.
pose mCD : test_of Ar (ar_zero Ar) (linhom_car Ar C D) :=
  linhom_test (const_x_path c') Hγc' mD mDM.
have mCDM : linhom_mcone_M (Y := ar_zero Ar) mCD.
  by exists (const_x_path c'), Hγc', mD, mDM.
(* The c-rescaling: for any h : Dom, mD(s₀, h(b)(c)) = (‖c‖+1)·mCD(s₀, h(b)). *)
have rescE : forall h : Dom,
    test_fun mD s0 (linhom_fun (Psi_inner h) (ptensor b c)) =
    (cone_norm c + 1) * test_fun mCD s0 (linhom_fun h b).
  move=> h; rewrite Psi_innerE.
  rewrite /mCD /linhom_test /linhom_test_fun /= /const_x_path /const_x_path_arity /=.
  have [_ _ HZ] := linhom_pre_linear (linhom_pre_of (linhom_fun h b)).
  rewrite /c'.
  rewrite -[linhom_fun (linhom_fun h b) (Sinv *: c)%PC]
            /((linhom_fun h b) (Sinv *: c)%PC).
  rewrite HZ test_linZ /=.
  by rewrite mulrA mulfV ?mul1r // gt_eqF.
(* LHS: mD(s₀, Ψ(sup u)(b⊗c)) = (‖c‖+1)·mCD(s₀, (sup u)(b)). *)
rewrite -[X in test_fun mD s0 (linhom_fun X (ptensor b c))]
          /(Psi_map (cone_sup_ball u uch ub1)).
rewrite (rescE (cone_sup_ball u uch ub1)).
rewrite -[linhom_fun (cone_sup_ball u uch ub1) b]/(linhom_sup_fun uch ub1 b).
rewrite (linhom_sup_fun_test_sup uch ub1 mCD s0 b).
(* RHS: mD(s₀, (sup_n Ψ(u_n))(b⊗c)). *)
rewrite -[linhom_fun (cone_sup_ball (Psi_map \o u) fuch fub1) (ptensor b c)]
          /(linhom_sup_fun fuch fub1 (ptensor b c)).
rewrite (linhom_sup_fun_test_sup fuch fub1 mD s0 (ptensor b c)).
(* Both real-sup sets coincide via [rescE] on each [u_n]. *)
have HsupS : has_sup [set test_fun mCD s0 (linhom_fun (u n) b) | n in [set: nat]].
  split; first by exists (test_fun mCD s0 (linhom_fun (u 0%N) b)), 0%N.
  exists (cone_norm b) => _ [n _ <-].
  apply: le_trans (test_norm_le mCD s0 (linhom_fun (u n) b)) _.
  apply: le_trans (linhom_norm_apply_le (lexx _) b) _.
  rewrite -[X in _ <= X]mul1r; apply: ler_wpM2r;
    [exact: cone_norm_ge0|exact: ub1].
rewrite sup_scaleM; first last.
- by case: HsupS.
- by case: HsupS.
- exact: ltW.
have evalE : forall n,
    test_fun mD s0 (linhom_fun (Psi_map (u n)) (ptensor b c)) =
    (cone_norm c + 1) * test_fun mCD s0 (linhom_fun (u n) b).
  by move=> n; rewrite -[linhom_fun (Psi_map (u n)) (ptensor b c)]
               /(linhom_fun (Psi_inner (u n)) (ptensor b c)) (rescE (u n)).
congr (sup _); rewrite eqEsubset; split.
- move=> _ [_ [n _ <-] <-]; exists n => //; exact: esym (evalE n).
- move=> _ [n _ <-]; rewrite evalE.
  by exists (test_fun mCD s0 (linhom_fun (u n) b)) => //; exists n.
Qed.

(** *** Boundedness of [Ψ] (operator norm [≤ 1]). *)
Lemma Psi_bounded :
  exists M : R, forall h : Dom, cnorm h <= 1 -> cnorm (Psi_map h) <= M.
Proof. by exists 1 => h Hh; apply: le_trans (Psi_norm_le1 h) _. Qed.

(** [Ψ] packaged as a [cones_hom]. *)
Definition Psi_cones : cones_hom Dom Cod :=
  ConesHom Psi_map Psi_linear Psi_continuous Psi_norm_le1.

(** *** Measurable-path preservation of [Ψ] — via [path_tens_to_X].

    For a measurable path [H] of [B⊸(C⊸D)], [r ↦ Psi_inner (H r)] is a
    measurable path of [(B⊗C)⊸D] by [path_tens_to_X]: it is bounded
    ([Psi_norm_le1] + [H]'s bound) and measurable on pure tensors.  The
    pure-tensor hypothesis [ηpt] — [s ↦ mD(s, (H(φ s))(β s)(γ s))]
    measurable on [Z] — is [H]'s own path-preservation tested against the
    nested [Dom]-test [β' ▷ (γ' ▷ mD)] (with [β], [γ] rescaled into the
    unit ball, recovered by [test_linZ]) composed with the diagonal
    [s ↦ (s, φ s)]. *)
Lemma Psi_pres_path
    (W : ar_obj Ar) (H : ar_carrier Ar W -> Dom) :
  is_measurable_path H ->
  is_measurable_path (fun r => Psi_map (H r)).
Proof.
move=> HH.
have [[MH HMH] HHm] := HH.
have MH_ge0 : 0 <= MH by apply: le_trans (HMH (ar_point Ar W)); exact: cone_norm_ge0.
apply: (@path_tens_to_X _ _ B C D W (fun r => Psi_map (H r))).
  exists MH => r; apply: le_trans (Psi_norm_le1 (H r)) _; exact: HMH.
move=> Z mD mDM φ β γ Hβ Hγ.
(* Rescale β, γ into the unit ball. *)
have [[Mβ HMβ] _] := Hβ.
have [[Mγ HMγ] _] := Hγ.
have Mβ_ge0 : 0 <= Mβ by apply: le_trans (HMβ (ar_point Ar Z)); exact: cone_norm_ge0.
have Mγ_ge0 : 0 <= Mγ by apply: le_trans (HMγ (ar_point Ar Z)); exact: cone_norm_ge0.
have Sβ_pos : 0 < Mβ + 1 by apply: le_lt_trans Mβ_ge0 _; rewrite ltrDl ltr01.
have Sγ_pos : 0 < Mγ + 1 by apply: le_lt_trans Mγ_ge0 _; rewrite ltrDl ltr01.
have Sβinv_ge0 : 0 <= (Mβ + 1)^-1 by rewrite invr_ge0 ltW.
have Sγinv_ge0 : 0 <= (Mγ + 1)^-1 by rewrite invr_ge0 ltW.
pose Sβinv : {nonneg R} := NngNum Sβinv_ge0.
pose Sγinv : {nonneg R} := NngNum Sγinv_ge0.
pose β' (s : ar_carrier Ar Z) : B := precone_scale Sβinv (β s).
pose γ' (s : ar_carrier Ar Z) : C := precone_scale Sγinv (γ s).
have Hβ' : is_measurable_path β' by exact: (path_scale_is_path Sβinv (MkPath Hβ)).
have Hγ' : is_measurable_path γ' by exact: (path_scale_is_path Sγinv (MkPath Hγ)).
have Hβ'1 : forall s, cone_norm (β' s) <= 1.
  move=> s; rewrite /β' cone_normh /=.
  rewrite mulrC -ler_pdivlMr ?invr_gt0 // mul1r invrK.
  by apply: le_trans (HMβ s) _; rewrite lerDl ler01.
have Hγ'1 : forall s, cone_norm (γ' s) <= 1.
  move=> s; rewrite /γ' cone_normh /=.
  rewrite mulrC -ler_pdivlMr ?invr_gt0 // mul1r invrK.
  by apply: le_trans (HMγ s) _; rewrite lerDl ler01.
pose Pβ' : path_car Ar Z B := MkPath Hβ'.
pose Pγ' : path_car Ar Z C := MkPath Hγ'.
have Pβ'ub : cone_norm Pβ' <= 1.
  rewrite /cone_norm /=; apply: ge_sup; first exact: path_normset_nonempty.
  by move=> _ [s ->] /=; exact: Hβ'1.
have Pγ'ub : cone_norm Pγ' <= 1.
  rewrite /cone_norm /=; apply: ge_sup; first exact: path_normset_nonempty.
  by move=> _ [s ->] /=; exact: Hγ'1.
pose mCD : test_of Ar Z (linhom_car Ar C D) :=
  linhom_test Pγ' Pγ'ub mD mDM.
have mCDM : linhom_mcone_M (Y := Z) mCD by exists Pγ', Pγ'ub, mD, mDM.
pose p : test_of Ar Z Dom := linhom_test Pβ' Pβ'ub mCD mCDM.
have pM : linhom_mcone_M (Y := Z) p by exists Pβ', Pβ'ub, mCD, mCDM.
(* H's path-preservation, composed with the diagonal [s ↦ (s, φ s)]. *)
have Hbase := HHm Z p pM.
have Hdiag : measurable_fun [set: ar_carrier Ar Z]
    (fun s => p s (H (φ s))).
  rewrite (_ : (fun s => p s (H (φ s))) =
    (fun q : (ar_carrier Ar Z * ar_carrier Ar W)%type => p q.1 (H q.2))
      \o (fun s => (s, φ s))); last by apply: funext.
  apply: (measurable_comp (F := setT) measurableT (subsetT _) Hbase).
  by apply: measurable_fun_pair; [exact: measurable_id|exact: measurable_funPT].
(* Rewrite the goal as [Sβ · Sγ · (s ↦ p s (H(φ s)))]. *)
rewrite (_ : (fun s => test_fun mD s (linhom_fun (Psi_map (H (φ s)))
                (ptensor (β s) (γ s)))) =
   (fun s => (Mβ + 1) * ((Mγ + 1) * p s (H (φ s))))); last first.
  apply: funext => s.
  rewrite /Psi_map Psi_innerE.
  rewrite /p /mCD /linhom_test /linhom_test_fun /=.
  have [_ _ HZβ] := linhom_pre_linear (linhom_pre_of (H (φ s))).
  have [_ _ HZγ] :=
    linhom_pre_linear (linhom_pre_of (linhom_fun (H (φ s)) (β s))).
  rewrite /Pβ' /Pγ' /= /β' /γ'.
  rewrite -[linhom_fun (H (φ s)) (Sβinv *: β s)%PC]/((H (φ s)) (Sβinv *: β s)%PC).
  rewrite HZβ.
  rewrite -[linhom_fun (Sβinv *: linhom_fun (H (φ s)) (β s))%PC (Sγinv *: γ s)%PC]
            /(linhom_scale_fun Sβinv (linhom_fun (H (φ s)) (β s)) (Sγinv *: γ s)%PC).
  rewrite /linhom_scale_fun /=.
  rewrite -[linhom_fun (linhom_fun (H (φ s)) (β s)) (Sγinv *: γ s)%PC]
            /((linhom_fun (H (φ s)) (β s)) (Sγinv *: γ s)%PC).
  rewrite HZγ !test_linZ /=.
  rewrite [RHS]mulrCA.
  rewrite [(Mβ + 1) * ((Mβ + 1)^-1 * _)]mulrA mulfV ?gt_eqF // mul1r.
  by rewrite mulrA mulfV ?gt_eqF // mul1r.
apply: measurable_funM; first exact: measurable_cst.
by apply: measurable_funM; [exact: measurable_cst|exact: Hdiag].
Qed.

(** [Ψ] packaged as an [mcones_hom]. *)
Definition Psi_mcones : mcones_hom Ar Dom Cod :=
  MkMConesHom Psi_cones (fun W H HH => Psi_pres_path (W:=W) (H:=H) HH).

(** *** Integral-preservation of [Ψ].

    Via [Φ] being a left inverse: [Φ(Ψ h) = h] ([cod_eq] + pointwise
    [Phi_iconesE]/[Psi_innerE]).  Both [Φ] and [Ψ] preserve paths, and
    [Φ] preserves integrals ([Phi_pres_int]); applying [Φ]'s integral law
    to the [Ψ]-image and cancelling [Φ] by injectivity yields [Ψ]'s. *)
Lemma PhiPsi (h : Dom) : Phi_map (Psi_map h) = h.
Proof.
apply: cod_eq => b c.
rewrite -[linhom_fun (linhom_fun (Phi_map (Psi_map h)) b) c]
          /(linhom_fun (linhom_fun
             (cones_hom_fun (mcones_hom_cones (icones_hom_mcones Phi_icones))
                (Psi_map h)) b) c).
by rewrite Phi_iconesE /Psi_map Psi_innerE.
Qed.

(** [Φ] is injective ([Φ(g₁)=Φ(g₂)] ⇒ pure-tensor agreement ⇒ [g₁=g₂]). *)
Lemma Phi_inj : injective (Phi_map (B:=B) (C:=C) (D:=D)).
Proof.
move=> g1 g2 Heq.
apply: linhom_tensor_ext => b c.
have := f_equal (fun w : Dom => linhom_fun (linhom_fun w b) c) Heq.
by rewrite /Phi_map !Phi_innerE.
Qed.

Lemma Psi_pres_int
    (W : ar_obj Ar) (H : ar_carrier Ar W -> Dom)
    (HH : is_measurable_path H) (µ : fmeas R (ar_carrier Ar W)) :
  cones_hom_fun (mcones_hom_cones Psi_mcones) (icone_integral H HH µ) =
  icone_integral
    (fun r => cones_hom_fun (mcones_hom_cones Psi_mcones) (H r))
    (mcones_hom_pres_path Psi_mcones W H HH) µ.
Proof.
rewrite -[cones_hom_fun (mcones_hom_cones Psi_mcones) (icone_integral H HH µ)]
          /(Psi_map (icone_integral H HH µ)).
(* Apply the injective [Φ] to both sides. *)
apply: Phi_inj.
rewrite PhiPsi.
(* RHS: Φ(∫ (Ψ∘H)) = ∫ (Φ∘Ψ∘H) = ∫ H by [Phi_pres_int] + [PhiPsi]. *)
set PsiH := fun r => cones_hom_fun (mcones_hom_cones Psi_mcones) (H r).
set HPsiH := mcones_hom_pres_path Psi_mcones W H HH.
rewrite -[Phi_map (icone_integral PsiH HPsiH µ)]
          /(cones_hom_fun (mcones_hom_cones (@Phi_mcones _ _ B C D))
              (icone_integral PsiH HPsiH µ)).
rewrite (@Phi_pres_int _ _ B C D W PsiH HPsiH µ).
(* The integrand [Φ(Ψ(H r))] equals [H r] pointwise; integrals agree. *)
have Hfun : (fun r => cones_hom_fun (mcones_hom_cones (@Phi_mcones _ _ B C D)) (PsiH r))
            = H.
  apply: funext => r.
  rewrite -[cones_hom_fun (mcones_hom_cones (@Phi_mcones _ _ B C D)) (PsiH r)]
            /(Phi_map (Psi_map (H r))).
  exact: PhiPsi.
move: (mcones_hom_pres_path (@Phi_mcones _ _ B C D) W PsiH HPsiH).
rewrite Hfun => HH'.
by congr icone_integral; exact: Prop_irrelevance.
Qed.

(** [Ψ] packaged as a genuine [icones_hom] (Thm 5.12 inverse). *)
Definition Psi_icones : icones_hom Ar Dom Cod :=
  MkIConesHom Psi_mcones Psi_pres_int.

Lemma Psi_iconesE (h : Dom) (b : B) (c : C) :
  linhom_fun
    (cones_hom_fun (mcones_hom_cones (icones_hom_mcones Psi_icones)) h)
    (ptensor b c)
  = linhom_fun (linhom_fun h b) c.
Proof. by rewrite -[cones_hom_fun _ _]/(Psi_map h) /Psi_map Psi_innerE. Qed.

End PsiIConesHom.

Arguments Psi_map {R Ar B C D}.
Arguments Psi_icones {R Ar B C D}.
Arguments Psi_iconesE {R Ar B C D}.
Arguments PhiPsi {R Ar B C D}.
Arguments Phi_inj {R Ar B C D}.

(** ** Thm 5.12 [tensor_hom_iso] — the FULL iso [(B⊗C)⊸D ≅ B⊸(C⊸D)]

    Assembled from the forward [Φ = Phi_icones] and the inverse
    [Ψ = Psi_icones] via [icones_iso_of_cancel].  The round-trips are
    pure-tensor extensionality facts:
    - [Φ(Ψ h) = h] is [PhiPsi];
    - [Ψ(Φ g) = g] is [linhom_tensor_ext] ([Ψ(Φ g)] and [g] agree on
      pure tensors via [Psi_iconesE] + [Phi_iconesE]). *)

Section TensorHomIso.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C D : ICone.type Ar.

Local Notation BC := (tensor B C).
Local Notation Dom := (linhom_car Ar BC D).
Local Notation Cod := (linhom_car Ar B (linhom_car Ar C D)).

Lemma PsiPhi (g : Dom) : Psi_map (Phi_map g) = g.
Proof.
apply: linhom_tensor_ext => b c.
rewrite -[linhom_fun (Psi_map (Phi_map g)) (ptensor b c)]
          /(linhom_fun (cones_hom_fun
             (mcones_hom_cones (icones_hom_mcones Psi_icones)) (Phi_map g))
            (ptensor b c)).
rewrite Psi_iconesE.
rewrite -[linhom_fun (linhom_fun (Phi_map g) b) c]
          /(linhom_fun (linhom_fun
             (cones_hom_fun (mcones_hom_cones (icones_hom_mcones Phi_icones)) g) b) c).
by rewrite Phi_iconesE.
Qed.

Definition tensor_hom_iso : icones_iso Ar Dom Cod :=
  icones_iso_of_cancel Phi_icones Psi_icones PsiPhi PhiPsi.

End TensorHomIso.

Arguments tensor_hom_iso {R Ar} B C D.

End Icones_tensor_iso.

(**md**************************************************************************)
(* # STATUS — tensor_hom_iso discharge (this file)                            *)
(*                                                                            *)
(* DONE (axiom-free; Print Assumptions = the 3 classical [boolp] axioms only, *)
(* NO [saft_interface] symbols):                                              *)
(*                                                                            *)
(*  P1 — pointwise integral-evaluation foundation:                            *)
(*    - [path_int_eval] / [path_int_section_meas] (Thm 4.12): the Path(X,B)   *)
(*      integral is pointwise.                                                *)
(*    - [eval_path r] : Path(X,E) ⊸ E (a [linhom_car], norm ≤ 1).             *)
(*    - [linhom_int_eval] / [linhom_int_section_meas] (Lemma 5.4): the C⊸D    *)
(*      integral is pointwise.                                                *)
(*    - [eval_at y] : (C⊸D) ⊸ D (a [linhom_car], norm ≤ ‖y‖), ω-continuity    *)
(*      via [mcone_M_sep] + [linhom_sup_fun_test_sup] + [eval_at_test_sup_ball].*)
(*                                                                            *)
(*  P2 (core) — toward Paper [lemma:lfun-path-swap]:                          *)
(*    - [swap_inner f r y : B⊸D] (x ↦ f(x)(r)(y)) via [linhom_comp] of        *)
(*      [eval_at]/[eval_path]; [swap_innerE] computation.                     *)
(*    - ★ [swap_inner_path]: r ↦ swap_inner f r y is a measurable path of     *)
(*      B⊸D (the hardest measurability step; [swap_lin_path]-style            *)
(*      [ar_prod] reindexing).                                                *)
(*                                                                            *)
(*  P2 (assembly) — [lfps f : C -> Path(X, B⊸D)] (value                      *)
(*    [y ↦ MkPath (swap_inner_path f y)]) with [lfpsE] computation, and       *)
(*    [lfps_linear] / [lfps_norm_le] / [lfps_bounded] DONE.                    *)
(*                                                                            *)
(*  ★ P2 (rest) — DONE: [lfun_path_swap : icones_hom C (Path(X, B⊸D))]        *)
(*    (Paper [lemma:lfun-path-swap]), assembled from [lfps] with all five     *)
(*    [icones_hom] fields proved (+ [lfun_path_swapE] computation):           *)
(*    - [swap_inner_continuous] / [lfps_continuous]: ω-continuity, via        *)
(*      [linhom_mcone_M_sep] + [linhom_sup_fun_test_sup] + the inner          *)
(*      [linhom]'s own ω-continuity + [eval_at_test_sup_ball], then [path]'s  *)
(*      pointwise [cone_sup_ball].                                            *)
(*    - [lfps_pres_path]: PATH-preservation, the [swap_inner_path]-style      *)
(*      [ar_prod] reindexing/Pettis, one codomain-layer up, rescaling the     *)
(*      moving [C]-path into the unit ball + diagonal pullback.               *)
(*    - [lfps_pres_int]: INTEGRAL-preservation, via [icone_integral_eqP] +    *)
(*      the inner [linhom]'s [linhom_pres_int] + the D-integral Pettis spec.  *)
(*    Verified AXIOM-FREE (Print Assumptions [lfun_path_swap] = 3 boolp).     *)
(*                                                                            *)
(*  ★ PREREQ — DONE: [linhom_one_iso C : icones_iso (1⊸C) C] (the unit iso    *)
(*    [1 ⊸ C ≅ C], Paper §5.5 / Eq 5.3 ingredient), AXIOM-FREE (verified      *)
(*    Print Assumptions = 3 boolp):                                          *)
(*    - [lin_pt c : 1⊸C] — the linear-point map [s ↦ (c1_val s)·c]; all       *)
(*      five [linhom_car] fields ([lin_pt_continuous] mirrors                 *)
(*      [tensor_hom_iso.line_continuous]; [lin_pt_pres_int] via the [1]-cone  *)
(*      [icone_integralP] at [id_test]).                                      *)
(*    - forward [eval1 := eval_at 1] (norm ≤ 1, via [eval1_norm]); backward   *)
(*      [lo_lift := c ↦ lin_pt c] as a full [icones_hom C (1⊸C)]              *)
(*      ([lo_lift_continuous] via [linhom_mcone_M_sep] + [sup_scaleM];        *)
(*      [lo_lift_pres_int] via the [1⊸C]-test [δ▷m] + the [C]-integral        *)
(*      Pettis spec + [ge0_integralZl_EFin]).                                 *)
(*    - round-trips [linhom_one_fwdK] (linearity of [φ] at the unit) /        *)
(*      [linhom_one_bwdK] ([lin_pt_unit]); iso via [icones_iso_of_cancel].    *)
(*    Reusable for P3 (the [1]↔[1⊸1] bridge) AND P5's unitor [ρ].            *)
(*                                                                            *)
(*  ★ P3 — DONE: [path_tens_to_one] (Paper [lemma:path-tens-to-one]),         *)
(*    AXIOM-FREE (Print Assumptions = 3 boolp).  η : X → (B⊗C)⊸1 BOUNDED +    *)
(*    pure-tensor measurable ([ηpt]: for arity Z, arrow φ:Z→X, B-path β,      *)
(*    C-path γ, [s ↦ c1_val(η(φ s)(β s ⊗ γ s))] measurable on Z) ⇒ a genuine  *)
(*    measurable path.  Built bottom-up:                                      *)
(*    - [pt_Q b r := lo_lift ∘ (η r) ∘ (τ b) : C ⊸ (1⊸1)] (value             *)
(*      [c ↦ lin_pt(η r (b⊗c))]) and [pt_QB c r : B ⊸ (1⊸1)] (the b-slot      *)
(*      composite) — both genuine [linhom_car]s, supplying the c-/b-slot      *)
(*      linearity/ω-continuity/integral for free.                             *)
(*    - inner [eta_inner b : C ⊸ Path(X,1⊸1)] (value [c ↦ MkPath             *)
(*      (r ↦ lin_pt(η r (b⊗c)))], path [pt_inner_path] via [lo_lift_pres_path]*)
(*      + [ηpt] reindexed over [ar_prod]); all 6 [linhom_car] fields proved   *)
(*      ([eta_inner_{linear,bounded,continuous,pres_path,pres_int}]).         *)
(*    - outer [eta' : ICones(B, C⊸Path(X,1⊸1))] (value [eta_inner]); all 5    *)
(*      [icones_hom] fields ([eta_outer_{linear,norm,continuous,pres_path,    *)
(*      pres_int}]) via the symmetric b-slot [ar_prod] reindexing +           *)
(*      [ptensor_{linB,zeroB,scaleB}] (τ's bilinearity).                      *)
(*    - [euc := tensor_uncurry eta' : ICones(B⊗C, Path(X,1⊸1))]; apply        *)
(*      [lfun_path_swap] → [h : ICones(1, Path(X,(B⊗C)⊸1))]; conclude         *)
(*      [path_fun (h 1) r = η r] by [linhom_tensor_ext] (Prop 5.14) +         *)
(*      [tensor_uncurryK] + [eta'E] + [lin_pt_unit]; hence [η = path_fun(h 1)]*)
(*      ([path_tens_to_one_unit]).  General BOUNDED case: rescale into the    *)
(*      unit ball by [(M+1)⁻¹] + [path_scale_is_path].                        *)
(*    [Arguments path_tens_to_one {R Ar B C X} η ηbound ηpt].                 *)
(*                                                                            *)
(*  ★ P4 part 1 — DONE: [path_tens_to_X] (Paper [lemma:path-tens-to-one] at   *)
(*    a GENERAL codomain [D]), AXIOM-FREE (Print Assumptions = 3 boolp).  The  *)
(*    P3 construction VERBATIM with [D] in place of the inner scalar [1]:      *)
(*    [lin_pt (C:=D)] / [lo_lift (C:=D)] (already general-[C]); the inner       *)
(*    codomain becomes [Path(X, 1⊸D)] ([etaX_*]); [lfun_path_swap] runs with  *)
(*    [C':=1], [D':=D]; [lin_pt_unit] recovers values.  The ONLY change vs P3 *)
(*    is in the three test-driven fields ([ptX_inner_path], the [etaX]-slot   *)
(*    path/integral preservation), where the singleton [1]-test [id_test]      *)
(*    (value [c1_val]) becomes a GENERAL [D]-test [mD] (value [test_fun mD s]) *)
(*    reindexed via [test_reindex (ar_prod_fst …)] + [mcone_M_comp]; the       *)
(*    pure-tensor hypothesis [ηpt] is stated against an arbitrary [D]-test.    *)
(*    [Arguments path_tens_to_X {R Ar B C D X} η ηbound ηpt].                  *)
(*                                                                            *)
(*  ★★ P4 parts 2–3 — DONE: [Psi_icones] + [tensor_hom_iso] (MILESTONE,        *)
(*    discharges [saft_interface] Parameter #10), AXIOM-FREE (verified         *)
(*    Print Assumptions [tensor_hom_iso] = 3 boolp; NO [saft_interface]).      *)
(*    - [Psi_icones : icones_hom (B⊸(C⊸D)) ((B⊗C)⊸D)], map [Psi_inner].       *)
(*      LINEARITY: [linhom_tensor_ext] + pointwise [Psi_innerE].  NORM-≤1:     *)
(*      [Psi_inner h] equals (by [linhom_tensor_ext]) the EXACT [‖h‖]-rescaling*)
(*      [‖h‖·icones_to_linhom(tensor_uncurry(‖h‖⁻¹·h))], norm ≤ ‖h‖·1 by       *)
(*      [icones_to_linhom_norm_le1]; the [‖h‖=0] edge closed by [cone_normz].  *)
(*      ω-CONTINUITY: [linhom_tensor_ext] → [D]-equation at [b⊗c] →            *)
(*      [mcone_M_sep] real-sup identity, [c] rescaled to the unit ball, two    *)
(*      [linhom_sup_fun_test_sup] + [sup_scaleM].  PATH: [Psi_pres_path] via   *)
(*      [path_tens_to_X], [ηpt] = [H]'s path-preservation through [Psi_innerE]*)
(*      tested against the nested [Dom]-test [β'▷(γ'▷mD)] + diagonal [(id,φ)]. *)
(*      INTEGRAL: [Psi_pres_int] via [Phi_inj] (Φ injective by                 *)
(*      [linhom_tensor_ext]+[Phi_iconesE]) + [Phi_pres_int] + [PhiPsi]         *)
(*      ([Φ(Ψ h)=h]).                                                          *)
(*    - [tensor_hom_iso := icones_iso_of_cancel Phi_icones Psi_icones]; the    *)
(*      round-trips are [Ψ(Φ g)=g] ([PsiPhi], [linhom_tensor_ext] +           *)
(*      [Psi_iconesE]+[Phi_iconesE]) and [Φ(Ψ h)=h] ([PhiPsi]).               *)
(*      [Arguments tensor_hom_iso {R Ar} B C D] — matches Param #10 exactly.   *)
(*                                                                            *)
(* REMAINING ROUTE (concrete; next iteration):                               *)
(*  P5 — structural isos α/λ/ρ/σ + …E laws via [yoneda_iso] + prereq isos     *)
(*    [linhom_one_iso] (1⊸C≅C), [hom_one_bij] (ICones(1,B⊸C)≅ICones(B,C)),    *)
(*    [swap_lin_lin] (B1⊸(B2⊸C)≅B2⊸(B1⊸C), Fubini core = [swap_lin_path]).    *)
(*    Discharges Parameters #11–#18.                                          *)
(*  P6 — re-point tensor.v/smcc.v off saft_interface; delete saft_interface.v.*)
(******************************************************************************)
