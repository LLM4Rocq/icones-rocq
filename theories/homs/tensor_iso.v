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
(* REMAINING ROUTE (concrete; next iteration):                               *)
(*  P3 — [path_tens_to_one]: η : X → (B⊗C)⊸1 bounded + pure-tensor measurable *)
(*    ⇒ a genuine path.  Build η' : B → (C ⊸ Path(X, 1⊸1)) from the          *)
(*    pure-tensor data (lifting each scalar η(r)(x⊗y) ∈ 1 into [1⊸1] by the   *)
(*    "scale-by" map [line_fun]); η' preserves integrals "since ⊗ preserves   *)
(*    integrals" ([tensor_path] machinery); set η'' := tensor_uncurry η' :    *)
(*    icones_hom (B⊗C) (Path(X, 1⊸1)); apply [lfun_path_swap] (with B':=B⊗C,  *)
(*    C':=D':=1) → h : icones_hom 1 (Path(X, (B⊗C)⊸1)); conclude η = h(1) by  *)
(*    [linhom_tensor_ext] (pure-tensor ext).                                  *)
(*    PREREQ for the [1] ↔ [1⊸1] bridge: a small iso [cone_one_car ≅          *)
(*    (cone_one_car ⊸ cone_one_car)] (forward = [line_fun]-style scale map,   *)
(*    backward = eval-at-unit) — this is the [linhom_one_iso] (1⊸C≅C) of P5   *)
(*    specialised to C:=1, and is the only missing piece to start P3.         *)
(*  P4 — [Psi_icones] + [tensor_hom_iso]: Ψ's path field via P3 (applied to   *)
(*    Ψ), Ψ's integral field via [Phi_icones] injective + [Phi_pres_int];     *)
(*    assemble [icones_iso_of_cancel Phi_icones Psi_icones] (round-trips from  *)
(*    [Phi_innerE]/[Psi_innerE]/[linhom_tensor_ext]).  Discharges Parameter   *)
(*    #10 [tensor_hom_iso].                                                    *)
(*  P5 — structural isos α/λ/ρ/σ + …E laws via [yoneda_iso] + prereq isos     *)
(*    [linhom_one_iso] (1⊸C≅C), [hom_one_bij] (ICones(1,B⊸C)≅ICones(B,C)),    *)
(*    [swap_lin_lin] (B1⊸(B2⊸C)≅B2⊸(B1⊸C), Fubini core = [swap_lin_path]).    *)
(*    Discharges Parameters #11–#18.                                          *)
(*  P6 — re-point tensor.v/smcc.v off saft_interface; delete saft_interface.v.*)
(******************************************************************************)
