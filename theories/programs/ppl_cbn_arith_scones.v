(**md*** BEYOND THE PAPER — [add_FMeas] / [mul_FMeas] as [scones_hom]s

    The M5 consumer of the diagonal bilinear stability bridge
    [meas_stable_diag_bilinear_tensor] of
    [theories/stable/diag_bilinear_tensor.v].

    ** What this file delivers (all axiom-free modulo 3 [boolp] axioms)

    1. [meas_stable_bin_bilinear_tensor] — the BINARY companion of the
       diagonal bridge: for [Phi : icones_hom (tensor A B) C], the
       function [p ↦ Phi (ptensor (sprod_fst p) (sprod_snd p))] from
       [sprod A B] to [C] is meas-stable.  Derived from the diagonal
       bridge by an [icones_hom] lift.

    2. [add_FMeas_lax_icones] — the bilinear arithmetic combinator as
       [icones_hom (tensor (FMeas R_obj) (FMeas R_obj)) (FMeas R_obj)],
       built by composing [fmeas_lax] (paper §9) with [FMeas_fmap
       add_meas'] (pushforward through [+]).  The mul-variant
       [mul_FMeas_lax_icones] is identical with [mul_meas'].

    3. [add_FMeas_scones] / [mul_FMeas_scones] — the final
       [scones_hom (sprod (FMeas R_obj) (FMeas R_obj)) (FMeas R_obj)]
       packagings, obtained by applying the binary bridge to the
       respective [icones_hom]s.

    4. [add_FMeas_scones_E] / [mul_FMeas_scones_E] — pointwise
       computation rules on the unit ball:
         [sc_fun add_FMeas_scones p = add_FMeas (sprod_fst p) (sprod_snd p)]
       (and likewise for [mul]).

    ** Why this file matters

    The bridge of [diag_bilinear_tensor.v] handled the *diagonal*
    case [g ↦ Phi(g ⊗ K g)] — the one needed by the higher-order
    [Yfix_arr_g] cascade.  For the M5 CBN trunk wave, we need the
    *binary* case [(mu, nu) ↦ Phi(mu ⊗ nu)] so that [add_FMeas] /
    [mul_FMeas] can be installed as honest [scones_hom]s alongside
    the (γ)-degenerate clauses of [ppl_cbn_eff.v].

    ** Author

    Guillaume Baudart <guillaume.baudart@inria.fr>. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals signed constructive_ereal.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import measure dirac_measure.

Require Import Icones.prelude.classical_extra.
Require Import Icones.prelude.nonneg_extra.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.omega_general.
Require Import Icones.cones.cone_cat.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.mcones.path.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_cat.
Require Import Icones.homs.linhom.
Require Import Icones.homs.bilin.
Require Import Icones.homs.fmeas_lax.
Require Import Icones.homs.coalgebra.
Require Import Icones.homs.tensor.
Require Import Icones.homs.smcc.
Require Import Icones.stable.totmono.
Require Import Icones.stable.stablehom.
Require Import Icones.stable.compose.
Require Import Icones.stable.scones_cat.
Require Import Icones.stable.scones_ccc.
Require Import Icones.stable.stab_lin_swap.
Require Import Icones.stable.diag_bilinear_tensor.
Require Import Icones.programs.ppl.
Require Import Icones.programs.ppl_cbn_arith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** §1 — The binary bilinear stability bridge

    Companion of [meas_stable_diag_bilinear_tensor]: replaces the
    diagonal [g ↦ Phi(g ⊗ K g)] by the BINARY pair
    [p ↦ Phi(sprod_fst p ⊗ sprod_snd p)].  Derived by lifting
    [Phi] through [tensor_mor (icones_proj true) (icones_id)] and
    applying the diagonal bridge with [G := sprod A B] and
    [K := sprod_snd p].

    Concretely, for [Phi : icones_hom (tensor A B) C]:
    [[
       Phi_lift := icones_comp Phi
                     (tensor_mor (icones_proj true) (icones_id B))
                : icones_hom (tensor (sprod A B) B) C.
       (Phi_lift)(p ⊗ b) = Phi (sprod_fst p ⊗ b).
    ]]
    Apply the diagonal bridge with [K p := sprod_snd p]
    (meas-stable as the underlying function of an [icones_hom]). *)

Section MeasStableBinBilinearTensor.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (A B C : ICone.type Ar).

Local Open Scope precone_scope.

(** [sprod_snd] is meas-stable: it is the underlying function of
    the [icones_hom] projection [icones_proj false] on [sprod_fam]. *)
Lemma sprod_snd_meas_stable :
  is_meas_stable (sprod_snd (X:=A) (Y:=B)).
Proof.
apply: (meas_stable_eq_on_ball (sprod_snd (X:=A) (Y:=B))
          _ (@icones_meas_stable R Ar _ _
              (icones_proj (B:=sprod_fam A B) false))).
by move=> p _.
Qed.

(** [sprod_fst] is meas-stable. *)
Lemma sprod_fst_meas_stable :
  is_meas_stable (sprod_fst (X:=A) (Y:=B)).
Proof.
apply: (meas_stable_eq_on_ball (sprod_fst (X:=A) (Y:=B))
          _ (@icones_meas_stable R Ar _ _
              (icones_proj (B:=sprod_fam A B) true))).
by move=> p _.
Qed.

(** The binary bridge: for any bilinear [Phi : icones_hom (A ⊗ B) C],
    the function [p ↦ Phi(sprod_fst p ⊗ sprod_snd p)] is meas-stable
    as a map [sprod A B → C].

    Derivation via the diagonal bridge applied to
    [Phi_lift := Phi ∘ (icones_proj true ⊗ id_B)]. *)
Lemma meas_stable_bin_bilinear_tensor
    (Phi : icones_hom Ar (tensor Ar A B) C) :
  is_meas_stable
    (fun p : sprod A B =>
       Phi (ptensor (sprod_fst p) (sprod_snd p))).
Proof.
pose Phi_lift : icones_hom Ar (tensor Ar (sprod A B) B) C :=
  icones_comp Phi (tensor_mor (icones_proj (B:=sprod_fam A B) true)
                              (icones_id Ar B)).
have HK_ms : is_meas_stable (sprod_snd (X:=A) (Y:=B))
  by exact: sprod_snd_meas_stable.
have Hbridge :
    is_meas_stable
      (fun p : sprod A B => Phi_lift (ptensor p (sprod_snd p))).
  exact: meas_stable_diag_bilinear_tensor _ Phi_lift HK_ms.
apply: (meas_stable_eq_on_ball _ _ Hbridge) => p _.
rewrite /Phi_lift.
rewrite -[icones_comp _ _ _]/(Phi (tensor_mor
  (icones_proj (B:=sprod_fam A B) true) (icones_id Ar B)
  (ptensor p (sprod_snd p)))).
by rewrite tensor_morE.
Qed.

End MeasStableBinBilinearTensor.

Arguments meas_stable_bin_bilinear_tensor {R Ar A B C}.

(** ** §2 — [add_FMeas_lax_icones] : the binary arithmetic bilinear

    The [icones_hom (tensor (FMeas R_obj) (FMeas R_obj)) (FMeas R_obj)]
    underlying [add_FMeas]: the composite
    [[
       tensor (FMeas R_obj) (FMeas R_obj)
         ─[fmeas_lax R_obj R_obj]→     FMeas (ar_prod R_obj R_obj)
         ─[FMeas_fmap add_meas']→      FMeas R_obj.
    ]]

    Computation rule [add_FMeas_lax_icones_pt] (pointwise on a pure
    tensor [µ ⊗p ν]):
    [[
       (add_FMeas_lax_icones)(µ ⊗p ν)
         = Lfun (FMeas_fmap add_meas') (fmeas_lax_pre µ ν)
         = add_FMeas µ ν.
    ]] *)

Section AddFMeasLaxIcones.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

Local Notation add_meas' :=
  (@add_meas R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas).
Local Notation mul_meas' :=
  (@mul_meas R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas).

Definition add_FMeas_lax_icones :
    icones_hom Ar
      (tensor Ar (FMeas R_obj) (FMeas R_obj))
      (FMeas R_obj) :=
  icones_comp (FMeas_fmap add_meas') (fmeas_lax R_obj R_obj).

Definition mul_FMeas_lax_icones :
    icones_hom Ar
      (tensor Ar (FMeas R_obj) (FMeas R_obj))
      (FMeas R_obj) :=
  icones_comp (FMeas_fmap mul_meas') (fmeas_lax R_obj R_obj).

(** Pointwise on a pure tensor: matches [add_FMeas]. *)
Lemma add_FMeas_lax_icones_pt (mu nu : FMeas R_obj) :
  add_FMeas_lax_icones (ptensor mu nu) =
  add_FMeas R_carrier_eq R_carrier_meas R_to_carrier_meas mu nu.
Proof.
rewrite /add_FMeas_lax_icones.
rewrite -[icones_comp _ _ _]
  /(Lfun (FMeas_fmap add_meas') (Lfun (fmeas_lax R_obj R_obj)
    (ptensor mu nu))).
by rewrite (fmeas_lax_E mu nu) /add_FMeas.
Qed.

Lemma mul_FMeas_lax_icones_pt (mu nu : FMeas R_obj) :
  mul_FMeas_lax_icones (ptensor mu nu) =
  mul_FMeas R_carrier_eq R_carrier_meas R_to_carrier_meas mu nu.
Proof.
rewrite /mul_FMeas_lax_icones.
rewrite -[icones_comp _ _ _]
  /(Lfun (FMeas_fmap mul_meas') (Lfun (fmeas_lax R_obj R_obj)
    (ptensor mu nu))).
by rewrite (fmeas_lax_E mu nu) /mul_FMeas.
Qed.

End AddFMeasLaxIcones.

Arguments add_FMeas_lax_icones {R Ar R_obj}
  R_carrier_eq R_carrier_meas R_to_carrier_meas.
Arguments mul_FMeas_lax_icones {R Ar R_obj}
  R_carrier_eq R_carrier_meas R_to_carrier_meas.
Arguments add_FMeas_lax_icones_pt {R Ar R_obj}
  R_carrier_eq R_carrier_meas R_to_carrier_meas.
Arguments mul_FMeas_lax_icones_pt {R Ar R_obj}
  R_carrier_eq R_carrier_meas R_to_carrier_meas.

(** ** §3 — [add_FMeas_scones] / [mul_FMeas_scones]

    The [scones_hom (sprod (FMeas R_obj) (FMeas R_obj)) (FMeas R_obj)]
    packagings, obtained by applying the binary bridge to
    [add_FMeas_lax_icones] / [mul_FMeas_lax_icones]. *)

Section AddFMeasScones.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

Local Notation add_FMeas_icones' :=
  (add_FMeas_lax_icones R_carrier_eq R_carrier_meas R_to_carrier_meas).
Local Notation mul_FMeas_icones' :=
  (mul_FMeas_lax_icones R_carrier_eq R_carrier_meas R_to_carrier_meas).

(** The raw functions on [sprod (FMeas R_obj) (FMeas R_obj)]. *)

Definition add_FMeas_pair_fun (p : sprod (FMeas R_obj) (FMeas R_obj)) :
    FMeas R_obj :=
  add_FMeas_icones' (ptensor (sprod_fst p) (sprod_snd p)).

Definition mul_FMeas_pair_fun (p : sprod (FMeas R_obj) (FMeas R_obj)) :
    FMeas R_obj :=
  mul_FMeas_icones' (ptensor (sprod_fst p) (sprod_snd p)).

Lemma add_FMeas_pair_fun_meas_stable :
  is_meas_stable add_FMeas_pair_fun.
Proof.
exact: (meas_stable_bin_bilinear_tensor add_FMeas_icones').
Qed.

Lemma mul_FMeas_pair_fun_meas_stable :
  is_meas_stable mul_FMeas_pair_fun.
Proof.
exact: (meas_stable_bin_bilinear_tensor mul_FMeas_icones').
Qed.

(** Norm bounds on the unit ball: [|add_FMeas mu nu| ≤ |mu| · |nu| ≤
    1] when both are in the unit ball. *)
Lemma add_FMeas_pair_fun_norm_le1
    (p : sprod (FMeas R_obj) (FMeas R_obj)) :
  (cone_norm p <= 1)%R -> (cone_norm (add_FMeas_pair_fun p) <= 1)%R.
Proof.
move=> Hp.
have Hfst : (cone_norm (sprod_fst p : FMeas R_obj) <= 1)%R.
  apply: le_trans Hp.
  by have := cones_prod_norm_ge_comp p true.
have Hsnd : (cone_norm (sprod_snd p : FMeas R_obj) <= 1)%R.
  apply: le_trans Hp.
  by have := cones_prod_norm_ge_comp p false.
rewrite /add_FMeas_pair_fun.
rewrite (add_FMeas_lax_icones_pt R_carrier_eq R_carrier_meas
                                  R_to_carrier_meas).
exact: add_FMeas_norm_le1.
Qed.

Lemma mul_FMeas_pair_fun_norm_le1
    (p : sprod (FMeas R_obj) (FMeas R_obj)) :
  (cone_norm p <= 1)%R -> (cone_norm (mul_FMeas_pair_fun p) <= 1)%R.
Proof.
move=> Hp.
have Hfst : (cone_norm (sprod_fst p : FMeas R_obj) <= 1)%R.
  apply: le_trans Hp.
  by have := cones_prod_norm_ge_comp p true.
have Hsnd : (cone_norm (sprod_snd p : FMeas R_obj) <= 1)%R.
  apply: le_trans Hp.
  by have := cones_prod_norm_ge_comp p false.
rewrite /mul_FMeas_pair_fun.
rewrite (mul_FMeas_lax_icones_pt R_carrier_eq R_carrier_meas
                                  R_to_carrier_meas).
exact: mul_FMeas_norm_le1.
Qed.

(** *** The [scones_hom] packaging — point-level 0-extension via
    [sc_clamp]. *)

Lemma add_FMeas_clamp_norm_le1 :
  (sc_norm (sc_clamp add_FMeas_pair_fun) <= 1)%R.
Proof.
apply: sc_norm_lub => x Hx.
rewrite (sc_clamp_ball Hx).
exact: add_FMeas_pair_fun_norm_le1.
Qed.

Lemma mul_FMeas_clamp_norm_le1 :
  (sc_norm (sc_clamp mul_FMeas_pair_fun) <= 1)%R.
Proof.
apply: sc_norm_lub => x Hx.
rewrite (sc_clamp_ball Hx).
exact: mul_FMeas_pair_fun_norm_le1.
Qed.

Definition add_FMeas_scones :
    scones_hom (sprod (FMeas R_obj) (FMeas R_obj)) (FMeas R_obj) :=
  MkSconesHom (sc_clamp add_FMeas_pair_fun)
    (sc_clamp_meas_stable add_FMeas_pair_fun_meas_stable)
    add_FMeas_clamp_norm_le1
    (sc_clamp_offball_field _).

Definition mul_FMeas_scones :
    scones_hom (sprod (FMeas R_obj) (FMeas R_obj)) (FMeas R_obj) :=
  MkSconesHom (sc_clamp mul_FMeas_pair_fun)
    (sc_clamp_meas_stable mul_FMeas_pair_fun_meas_stable)
    mul_FMeas_clamp_norm_le1
    (sc_clamp_offball_field _).

(** *** Pointwise computation rules on the unit ball.

    On a unit-ball point [p], the scones evaluates to the underlying
    [add_FMeas]/[mul_FMeas] of the two components. *)
Lemma add_FMeas_scones_E (p : sprod (FMeas R_obj) (FMeas R_obj)) :
  (cone_norm p <= 1)%R ->
  sc_fun add_FMeas_scones p =
  add_FMeas R_carrier_eq R_carrier_meas R_to_carrier_meas
            (sprod_fst p) (sprod_snd p).
Proof.
move=> Hp.
rewrite /add_FMeas_scones /= (sc_clamp_ball Hp).
rewrite /add_FMeas_pair_fun.
exact: (add_FMeas_lax_icones_pt R_carrier_eq R_carrier_meas
                                R_to_carrier_meas).
Qed.

Lemma mul_FMeas_scones_E (p : sprod (FMeas R_obj) (FMeas R_obj)) :
  (cone_norm p <= 1)%R ->
  sc_fun mul_FMeas_scones p =
  mul_FMeas R_carrier_eq R_carrier_meas R_to_carrier_meas
            (sprod_fst p) (sprod_snd p).
Proof.
move=> Hp.
rewrite /mul_FMeas_scones /= (sc_clamp_ball Hp).
rewrite /mul_FMeas_pair_fun.
exact: (mul_FMeas_lax_icones_pt R_carrier_eq R_carrier_meas
                                R_to_carrier_meas).
Qed.

End AddFMeasScones.

Arguments add_FMeas_pair_fun {R Ar R_obj}
  R_carrier_eq R_carrier_meas R_to_carrier_meas.
Arguments mul_FMeas_pair_fun {R Ar R_obj}
  R_carrier_eq R_carrier_meas R_to_carrier_meas.
Arguments add_FMeas_scones {R Ar R_obj}
  R_carrier_eq R_carrier_meas R_to_carrier_meas.
Arguments mul_FMeas_scones {R Ar R_obj}
  R_carrier_eq R_carrier_meas R_to_carrier_meas.
Arguments add_FMeas_scones_E {R Ar R_obj}
  R_carrier_eq R_carrier_meas R_to_carrier_meas p.
Arguments mul_FMeas_scones_E {R Ar R_obj}
  R_carrier_eq R_carrier_meas R_to_carrier_meas p.

(** ** §4 — Dirac identity at the [scones_hom] level

    [sc_fun add_FMeas_scones (sprod_pair δ_a δ_b) = δ_{a+b}].  Direct
    from [add_FMeas_scones_E] + [sprod_fstE] + [sprod_sndE] +
    [add_FMeas_dirac]. *)

Section AddFMeasSconesDirac.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Local Notation add_FMeas_scones' :=
  (add_FMeas_scones R_carrier_eq R_carrier_meas R_to_carrier_meas).
Local Notation mul_FMeas_scones' :=
  (mul_FMeas_scones R_carrier_eq R_carrier_meas R_to_carrier_meas).

Lemma add_FMeas_scones_dirac (a b : R) :
  sc_fun add_FMeas_scones'
    (sprod_pair (dirac_fmeas (R_to_carrier R_carrier_eq a) : FMeas R_obj)
                (dirac_fmeas (R_to_carrier R_carrier_eq b) : FMeas R_obj)) =
  dirac_fmeas (R_to_carrier R_carrier_eq (a + b)).
Proof.
have Hball :
  (cone_norm (sprod_pair
    (dirac_fmeas (R_to_carrier R_carrier_eq a) : FMeas R_obj)
    (dirac_fmeas (R_to_carrier R_carrier_eq b) : FMeas R_obj))
   <= 1)%R.
  exact: sprod_pair_norm_le1
    (dirac_fmeas_norm_le1 _) (dirac_fmeas_norm_le1 _).
rewrite (add_FMeas_scones_E _ R_carrier_meas R_to_carrier_meas _ Hball).
rewrite sprod_fstE sprod_sndE.
exact: add_FMeas_dirac.
Qed.

Lemma mul_FMeas_scones_dirac (a b : R) :
  sc_fun mul_FMeas_scones'
    (sprod_pair (dirac_fmeas (R_to_carrier R_carrier_eq a) : FMeas R_obj)
                (dirac_fmeas (R_to_carrier R_carrier_eq b) : FMeas R_obj)) =
  dirac_fmeas (R_to_carrier R_carrier_eq (a * b)).
Proof.
have Hball :
  (cone_norm (sprod_pair
    (dirac_fmeas (R_to_carrier R_carrier_eq a) : FMeas R_obj)
    (dirac_fmeas (R_to_carrier R_carrier_eq b) : FMeas R_obj))
   <= 1)%R.
  exact: sprod_pair_norm_le1
    (dirac_fmeas_norm_le1 _) (dirac_fmeas_norm_le1 _).
rewrite (mul_FMeas_scones_E _ R_carrier_meas R_to_carrier_meas _ Hball).
rewrite sprod_fstE sprod_sndE.
exact: mul_FMeas_dirac.
Qed.

End AddFMeasSconesDirac.

Arguments add_FMeas_scones_dirac {R Ar R_obj}
  R_carrier_eq R_carrier_meas R_to_carrier_meas a b.
Arguments mul_FMeas_scones_dirac {R Ar R_obj}
  R_carrier_eq R_carrier_meas R_to_carrier_meas a b.
