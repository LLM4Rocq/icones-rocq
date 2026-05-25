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


End Icones_tensor_iso.
