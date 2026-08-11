(** * The integrable linear-map cone — Paper §5.1 + §5.2

    Given two integrable cones [C, D : iconeType Ar], the paper
    constructs the *integrable cone of linear, ω-continuous,
    integral-preserving maps* [C ⊸ D].  This file delivers:

    - [linhom_car C D] — the carrier record bundling a function
      [C -> D] together with proofs of: linearity, ω-continuity,
      *boundedness*, measurable-path preservation, integral
      preservation. (We do **not** require the pointwise unit-norm
      bound that [cones_hom] enforces — paper §5.1 paragraph 1 builds
      [C ⊸ D] as the set of maps [f] such that, for some ε > 0,
      [εf] is in [ICones(C, D)]. Equivalently, [f] is bounded.)
    - [isPrecone] HB instance — pointwise [0], [+], [*:]. Paper §5.1.
    - [isCone] HB instance — operator-norm (the M1 [linmap_norm]) plus
      pointwise (Normc). Paper §5.1.
    - [isMCone] HB instance — Paper Def 5.4 / Lemma 5.3 prerequisites:
      the test family [γ ▷ m] for [γ ∈ Path(X, C)] and [m ∈ M^D_X],
      acting by [(γ ▷ m)(s, f) := m(s, f(γ(s)))], plus its (Mscomp),
      (Mssep), (Msnorm) closure.
    - [isICone] HB instance — Paper Lemma 5.4: every measurable path
      [η : X -> C ⊸ D] has a pointwise integral
      [(∫η dµ)(x) := ∫(r ↦ η(r)(x)) dµ] in [D].

    Paper §5.2 (bilinear maps, Def 5.6): a separately-linear,
    jointly-measurable + integral-preserving bilinear map
    [f : C₁ × C₂ -> D] is the same data as a morphism
    [F : C₁ -> C₂ ⊸ D]. We deliver this bijection at the level of
    underlying functions.

    The symmetric monoidal closure [⊗ ⊣ ⊸] of paper §5.4 is delivered
    by [tensor.v]/[smcc.v], NOT by this file. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals constructive_ereal.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import ereal.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import measure.
From mathcomp.analysis Require Import lebesgue_integral_definition.
From mathcomp.analysis Require Import lebesgue_integral_nonneg.
From mathcomp.analysis Require Import lebesgue_integral_monotone_convergence.
From mathcomp.analysis Require Import topology normedtype sequences.
Import numFieldTopology.Exports.

Require Import Icones.prelude.nonneg_extra.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.cone_cat.
Require Import Icones.cones.omega_general.
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

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** The carrier — Paper §5.1 / Def 5.2

    A [linhom_car Ar C D] element is a linear, ω-continuous,
    *bounded*, measurable-path-preserving, integral-preserving map
    [C -> D].

    Paper §5.1, paragraph 1: "the set of all [f : C → D] such that,
    for some ε > 0, one has [εf ∈ ICones(C, D)]". This is the cone of
    bounded linear ω-continuous integral-preserving maps. The unit
    ball recovers [ICones(C, D)]. *)

Section LinhomPre.
Variables (R : realType) (Ar : MeasSubcat R).
Variables C D : ICone.type Ar.

(** Paper §5.1: the *pre-carrier* of [C ⊸ D] — a bounded linear
    ω-continuous measurable-path-preserving map.  We separate
    integral preservation from path preservation so that we can
    use the "path-preservation" field [linhom_pre_pres_path]
    inside the type of the "integral-preservation" field of
    [linhom_car].  This is the same record-layering pattern used by
    [cones_hom → mcones_hom → icones_hom] in M1 / M2 / M3. *)
Record linhom_pre : Type := MkLinhomPre {
  linhom_pre_fun :> C -> D;
  linhom_pre_linear : is_linear linhom_pre_fun;
  linhom_pre_continuous : is_omega_continuous linhom_pre_fun;
  linhom_pre_bounded :
    exists M : R,
      forall x : C, cnorm x <= 1 -> cnorm (linhom_pre_fun x) <= M;
  linhom_pre_pres_path :
    forall (X : ar_obj Ar) (γ : ar_carrier Ar X -> C),
      is_measurable_path (Ar:=Ar) (C:=C) γ ->
      is_measurable_path
        (Ar:=Ar) (C:=D) (fun r => linhom_pre_fun (γ r));
}.

(** Extensionality at the [linhom_pre] level. *)
Lemma linhom_pre_eq (f g : linhom_pre) :
  (forall x, linhom_pre_fun f x = linhom_pre_fun g x) -> f = g.
Proof.
case: f => ff fl fc fb fp; case: g => gf gl gc gb gp /= Hfg.
have Hf : ff = gf by apply: funext.
move: fl fc fb fp; rewrite Hf => fl fc fb fp.
by congr MkLinhomPre; exact: Prop_irrelevance.
Qed.

End LinhomPre.

Arguments linhom_pre {R} Ar C D.
Arguments MkLinhomPre {R Ar C D}.
Arguments linhom_pre_fun {R Ar C D}.
Arguments linhom_pre_linear {R Ar C D}.
Arguments linhom_pre_continuous {R Ar C D}.
Arguments linhom_pre_bounded {R Ar C D}.
Arguments linhom_pre_pres_path {R Ar C D}.

Section LinhomCar.
Variables (R : realType) (Ar : MeasSubcat R).
Variables C D : ICone.type Ar.

(** Paper §5.1: the integrable-linear-map carrier — adds the
    integral-preservation field on top of [linhom_pre]. *)
Record linhom_car : Type := MkLinhom {
  linhom_pre_of :> linhom_pre Ar C D;
  linhom_pres_int :
    forall (X : ar_obj Ar)
           (β : ar_carrier Ar X -> C)
           (Hβ : is_measurable_path β)
           (µ : fmeas R (ar_carrier Ar X)),
      linhom_pre_fun linhom_pre_of (icone_integral β Hβ µ) =
      icone_integral
        (fun r => linhom_pre_fun linhom_pre_of (β r))
        (linhom_pre_pres_path linhom_pre_of X β Hβ) µ;
}.

(** Convenience: the underlying function of a [linhom_car]. *)
Definition linhom_fun (f : linhom_car) : C -> D :=
  linhom_pre_fun (linhom_pre_of f).

(** Two [linhom_car] elements are equal iff their underlying
    functions agree pointwise. *)
Lemma linhom_eq (f g : linhom_car) :
  (forall x, linhom_fun f x = linhom_fun g x) -> f = g.
Proof.
case: f => fp fi; case: g => gp gi /= Hfg.
have Hp : fp = gp by apply: linhom_pre_eq.
move: fi {Hfg}; rewrite Hp => fi.
by congr MkLinhom; exact: Prop_irrelevance.
Qed.

End LinhomCar.

Arguments linhom_car {R} Ar C D.
Arguments MkLinhom {R Ar C D}.
Arguments linhom_pre_of {R Ar C D}.
Arguments linhom_pres_int {R Ar C D}.
Arguments linhom_fun {R Ar C D}.

(** ** Pointwise zero — Paper §5.1 *)

Section LinhomZero.
Variables (R : realType) (Ar : MeasSubcat R).
Variables C D : ICone.type Ar.

Definition linhom_zero_fun : C -> D := fun _ => precone_zero.

Lemma linhom_zero_linear : is_linear linhom_zero_fun.
Proof.
split.
- by [].
- by move=> x y; rewrite precone_add0.
- by move=> r x; rewrite precone_scale_0r.
Qed.

Lemma linhom_zero_continuous : is_omega_continuous linhom_zero_fun.
Proof.
move=> u uch ub1 fuch fub1.
rewrite /linhom_zero_fun.
apply: precone_le_anti.
- by exists (cone_sup_ball
    (linhom_zero_fun \o u) fuch fub1); rewrite precone_add0.
- apply: cone_sup_ball_lub => n.
  by rewrite /=; exact: precone_le_refl.
Qed.

Lemma linhom_zero_bounded :
  exists M : R, forall x : C, cnorm x <= 1 -> cnorm (linhom_zero_fun x) <= M.
Proof. exists 0 => x _; by rewrite /linhom_zero_fun cone_norm0. Qed.

Lemma linhom_zero_pres_path
  (X : ar_obj Ar) (γ : ar_carrier Ar X -> C) :
  is_measurable_path (Ar:=Ar) (C:=C) γ ->
  is_measurable_path (Ar:=Ar) (C:=D) (fun r => linhom_zero_fun (γ r)).
Proof. by move=> _; exact: const_path_measurable. Qed.

(** Pre-carrier packaging for [linhom_zero]. *)
Definition linhom_zero_pre : linhom_pre Ar C D :=
  MkLinhomPre linhom_zero_fun linhom_zero_linear linhom_zero_continuous
              linhom_zero_bounded linhom_zero_pres_path.

Lemma linhom_zero_pres_int
  (X : ar_obj Ar) (β : ar_carrier Ar X -> C)
  (Hβ : is_measurable_path β)
  (µ : fmeas R (ar_carrier Ar X)) :
  linhom_pre_fun linhom_zero_pre (icone_integral β Hβ µ) =
  icone_integral
    (fun r => linhom_pre_fun linhom_zero_pre (β r))
    (linhom_pre_pres_path linhom_zero_pre X β Hβ) µ.
Proof.
apply: icone_integral_eqP => m mM s /=.
rewrite /linhom_zero_fun test_lin0.
have -> : (fun _ : ar_carrier Ar X => (0 : R)%:E) =
          cst 0%E :> (_ -> \bar R) by apply: funext.
by rewrite integral0.
Qed.

(** Paper §5.1: the zero of [C ⊸ D]. *)
Definition linhom_zero : linhom_car Ar C D :=
  MkLinhom linhom_zero_pre linhom_zero_pres_int.

End LinhomZero.

Arguments linhom_zero {R Ar} C D.
Arguments linhom_zero_fun {R Ar} C D.

(** ** Pointwise sum-of-chain identity — Paper §5.1 (key lemma)

    To support the [isPrecone] / [isCone] structure on [linhom_car],
    we need:
    [sup_n (a_n + b_n) = sup_n a_n + sup_n b_n]
    for increasing chains [a_n, b_n] in [B] whose diagonal sum stays
    in [B]. This is the *diagonal-sup identity* in cones — a
    consequence of (Normp), (Cancel) and (Normc).

    The mathematical content now lives, once and at a general radius,
    in the consolidated sup-calculus of [cones/omega_general.v]
    ([cone_sup_at_addD], with the radius-1 corollaries
    [cone_sup_ball_addD] / [_le] / [_ge]).  What follows are the
    radius-1 instances in the exact shape this file — and the
    blueprint — refers to, so that the [isPrecone] / [isCone]
    instances on [linhom_car] below read unchanged. *)

Section DiagonalSup.
Variable R : realType.
Variable P : coneType R.
Implicit Types (a b : nat -> P).

Local Open Scope precone_scope.

(** The diagonal sup is [≤p] the pointwise sum of sups. *)
Lemma cone_sup_ball_addD_le a b
  (ach : forall n, a n <=p a n.+1)
  (aub : forall n, cnorm (a n) <= 1)
  (bch : forall n, b n <=p b n.+1)
  (bub : forall n, cnorm (b n) <= 1)
  (sch : forall n, precone_add (a n) (b n) <=p precone_add (a n.+1) (b n.+1))
  (sub : forall n, cnorm (precone_add (a n) (b n)) <= 1) :
  cone_sup_ball (fun n => precone_add (a n) (b n)) sch sub
    <=p precone_add (cone_sup_ball a ach aub) (cone_sup_ball b bch bub).
Proof. exact: omega_general.cone_sup_ball_addD_le. Qed.

(** The reverse direction. *)
Lemma cone_sup_ball_addD_ge a b
  (ach : forall n, a n <=p a n.+1)
  (aub : forall n, cnorm (a n) <= 1)
  (bch : forall n, b n <=p b n.+1)
  (bub : forall n, cnorm (b n) <= 1)
  (sch : forall n, precone_add (a n) (b n) <=p precone_add (a n.+1) (b n.+1))
  (sub : forall n, cnorm (precone_add (a n) (b n)) <= 1) :
  precone_add (cone_sup_ball a ach aub) (cone_sup_ball b bch bub)
    <=p cone_sup_ball (fun n => precone_add (a n) (b n)) sch sub.
Proof. exact: omega_general.cone_sup_ball_addD_ge. Qed.

End DiagonalSup.

(** ** Diagonal-sup identity — the equality form *)
Section DiagonalSupEq.
Variable R : realType.
Variable P : coneType R.
Implicit Types (a b : nat -> P).

Local Open Scope precone_scope.

(** Paper §5.1: the full diagonal-sup identity. *)
Lemma cone_sup_ball_addD a b
  (ach : forall n, a n <=p a n.+1)
  (aub : forall n, cnorm (a n) <= 1)
  (bch : forall n, b n <=p b n.+1)
  (bub : forall n, cnorm (b n) <= 1)
  (sch : forall n, precone_add (a n) (b n) <=p precone_add (a n.+1) (b n.+1))
  (sub : forall n, cnorm (precone_add (a n) (b n)) <= 1) :
  cone_sup_ball (fun n => precone_add (a n) (b n)) sch sub =
  precone_add (cone_sup_ball a ach aub) (cone_sup_ball b bch bub).
Proof. exact: omega_general.cone_sup_ball_addD. Qed.

End DiagonalSupEq.

(** ** Pointwise sum-of-chain identity (continued)


    The standard one-sided ω-continuity result [sup_ball_addr]
    handles the case where one summand is fixed; the diagonal case
    here is reduced to two applications of [sup_ball_addr] after
    rescaling.  Layered delivery:

    - The *type* [linhom_car Ar C D] (above) and a [linhom_zero]
      element are delivered fully and unconditionally.
    - The **bilinear ↔ linhom bijection** (paper §5.2 / Def 5.6) is
      delivered at the *function level*; this does not require the
      cone structure on [linhom_car] to be in place.
    - The HB-instance registration of [isPrecone] / [isCone] /
      [isMCone] / [isICone] on [linhom_car Ar C D] comes later in
      this file (the four-instance tower mirroring [path.v]; the
      technical block is the diagonal-sup identity above for
      [isCone]'s (Normc), and Lemma 5.4 for [isICone]).

    The bilinear ↔ linhom bijection (paper §5.2) is delivered below
    without depending on the HB tower; it is the cleanest invariant
    of the [linhom_car] construction. *)

(** ** Pointwise addition and scaling at the function level

    Below we provide the bare-function pointwise [+] and [*:]
    operators on [linhom_car], together with their preservation of
    linearity, ω-continuity (under the auxiliary unit-ball
    hypothesis), and boundedness.  At this stage we do **not**
    package them as [linhom_car] elements (which would require the
    full diagonal-sup identity); that comes later in the file. *)

Section LinhomAlgebra.
Variables (R : realType) (Ar : MeasSubcat R).
Variables C D : ICone.type Ar.

(** Pointwise addition at the underlying-function level. *)
Definition linhom_add_fun (f g : linhom_car Ar C D) : C -> D :=
  fun x => precone_add (linhom_fun f x) (linhom_fun g x).

(** Pointwise scaling at the underlying-function level. *)
Definition linhom_scale_fun (r : {nonneg R}) (f : linhom_car Ar C D) : C -> D :=
  fun x => precone_scale r (linhom_fun f x).

(** Linearity of the pointwise sum. *)
Lemma linhom_add_fun_linear (f g : linhom_car Ar C D) :
  is_linear (linhom_add_fun f g).
Proof.
have [Hf0 HfD HfZ] := linhom_pre_linear (linhom_pre_of f).
have [Hg0 HgD HgZ] := linhom_pre_linear (linhom_pre_of g).
split.
- by rewrite /linhom_add_fun /linhom_fun /= Hf0 Hg0 precone_add0.
- move=> x y; rewrite /linhom_add_fun /linhom_fun /= HfD HgD.
  rewrite -!precone_addA; congr precone_add.
  by rewrite [in RHS]precone_addC -precone_addA
             [precone_add (linhom_pre_fun (linhom_pre_of g) y) _]precone_addC.
- move=> r x; rewrite /linhom_add_fun /linhom_fun /= HfZ HgZ.
  by rewrite -precone_scale_DAr.
Qed.

(** Linearity of the pointwise scaling. *)
Lemma linhom_scale_fun_linear (r : {nonneg R}) (f : linhom_car Ar C D) :
  is_linear (linhom_scale_fun r f).
Proof.
have [Hf0 HfD HfZ] := linhom_pre_linear (linhom_pre_of f).
split.
- by rewrite /linhom_scale_fun /linhom_fun /= Hf0 precone_scale_0r.
- by move=> x y; rewrite /linhom_scale_fun /linhom_fun /= HfD precone_scale_DAr.
- move=> s x; rewrite /linhom_scale_fun /linhom_fun /= HfZ.
  rewrite -!precone_scale_A; congr precone_scale.
  apply: val_inj => /=; exact: mulrC.
Qed.

(** Boundedness of the pointwise sum, with composite bound [Mf + Mg]. *)
Lemma linhom_add_fun_bounded (f g : linhom_car Ar C D) :
  exists M : R,
    forall x : C, cnorm x <= 1 -> cnorm (linhom_add_fun f g x) <= M.
Proof.
have [Mf HMf] := linhom_pre_bounded (linhom_pre_of f).
have [Mg HMg] := linhom_pre_bounded (linhom_pre_of g).
exists (Mf + Mg) => x Hx.
apply: le_trans (cone_normt _ _) _.
apply: lerD.
- exact: HMf.
- exact: HMg.
Qed.

(** Boundedness of the pointwise scaling, with bound [r * Mf]. *)
Lemma linhom_scale_fun_bounded (r : {nonneg R}) (f : linhom_car Ar C D) :
  exists M : R,
    forall x : C, cnorm x <= 1 -> cnorm (linhom_scale_fun r f x) <= M.
Proof.
have [Mf HMf] := linhom_pre_bounded (linhom_pre_of f).
exists (r%:num * Mf) => x Hx.
rewrite /linhom_scale_fun cone_normh.
have rge0 : 0 <= r%:num by exact: nngnum_ge0.
have [-> | rpos] := eqVneq r%:num 0.
  by rewrite !mul0r.
by rewrite ler_pM2l ?lt_def ?rpos ?rge0 //; exact: HMf.
Qed.

(** ω-continuity of the pointwise sum.

    Paper §5.1: given a chain [u] in [B_C] with [f∘u + g∘u] in [B_D]
    (so that [‖(f+g)(u_n)‖ ≤ 1]), we have:
    - [‖f(u_n)‖ ≤ ‖(f+g)(u_n)‖ ≤ 1] by Normp;
    - [‖g(u_n)‖ ≤ ‖(f+g)(u_n)‖ ≤ 1] by Normp;
    Hence [f(sup u_n) = sup(f∘u_n)] and [g(sup u_n) = sup(g∘u_n)] by
    ω-continuity of [f] and [g], and the result is the diagonal-sup
    identity [cone_sup_ball_addD]. *)
Lemma linhom_add_fun_continuous (f g : linhom_car Ar C D) :
  is_omega_continuous (linhom_add_fun f g).
Proof.
move=> u uch ub1 fuch fub1.
have Hf_cont := linhom_pre_continuous (linhom_pre_of f).
have Hg_cont := linhom_pre_continuous (linhom_pre_of g).
(* Pointwise bounds: ‖f(u_n)‖ ≤ 1 and ‖g(u_n)‖ ≤ 1. *)
have fub : forall n, cnorm (linhom_fun f (u n)) <= 1.
  move=> n.
  have := fub1 n; rewrite /linhom_add_fun => Hsum.
  apply: le_trans Hsum.
  apply: cone_normp.
  by exists (linhom_fun g (u n)).
have gub : forall n, cnorm (linhom_fun g (u n)) <= 1.
  move=> n.
  have := fub1 n; rewrite /linhom_add_fun => Hsum.
  apply: le_trans Hsum.
  apply: cone_normp.
  by exists (linhom_fun f (u n)); rewrite precone_addC.
(* Pointwise chains: f(u_n) ≤p f(u_{n+1}) and same for g.
   By linearity, f is increasing. *)
have Hf_lin := linhom_pre_linear (linhom_pre_of f).
have Hg_lin := linhom_pre_linear (linhom_pre_of g).
have fch : forall n, precone_le (linhom_fun f (u n))
                                 (linhom_fun f (u n.+1)).
  move=> n; rewrite /linhom_fun.
  exact: (linear_increasing Hf_lin) _ _ (uch n).
have gch : forall n, precone_le (linhom_fun g (u n))
                                 (linhom_fun g (u n.+1)).
  move=> n; rewrite /linhom_fun.
  exact: (linear_increasing Hg_lin) _ _ (uch n).
(* Apply f, g ω-continuity. *)
have fsup_eq : linhom_fun f (cone_sup_ball u uch ub1) =
               cone_sup_ball (linhom_fun f \o u) fch fub.
  exact: Hf_cont.
have gsup_eq : linhom_fun g (cone_sup_ball u uch ub1) =
               cone_sup_ball (linhom_fun g \o u) gch gub.
  exact: Hg_cont.
(* LHS: (f+g)(sup u) = f(sup u) + g(sup u) = sup(f∘u) + sup(g∘u). *)
have LHS_eq : linhom_add_fun f g (cone_sup_ball u uch ub1) =
              precone_add (cone_sup_ball (linhom_fun f \o u) fch fub)
                          (cone_sup_ball (linhom_fun g \o u) gch gub).
  by rewrite /linhom_add_fun -fsup_eq -gsup_eq.
rewrite LHS_eq.
(* RHS: sup((f+g)∘u) = sup(f∘u_n + g∘u_n).
   Apply the diagonal-sup identity. *)
symmetry.
have fch' : forall n,
    precone_le ((linhom_fun f \o u) n) ((linhom_fun f \o u) n.+1)
  by exact: fch.
have gch' : forall n,
    precone_le ((linhom_fun g \o u) n) ((linhom_fun g \o u) n.+1)
  by exact: gch.
have ub1c' : forall n, cnorm ((linhom_fun f \o u) n) <= 1 by exact: fub.
have ub1c'' : forall n, cnorm ((linhom_fun g \o u) n) <= 1 by exact: gub.
have sch' : forall n,
    precone_le (precone_add ((linhom_fun f \o u) n)
                            ((linhom_fun g \o u) n))
               (precone_add ((linhom_fun f \o u) n.+1)
                            ((linhom_fun g \o u) n.+1)).
  by move=> n; exact: fuch.
have sub' : forall n,
    cnorm (precone_add ((linhom_fun f \o u) n) ((linhom_fun g \o u) n)) <= 1.
  by move=> n; exact: fub1.
have key := @cone_sup_ball_addD R D _ _ fch' ub1c' gch' ub1c'' sch' sub'.
(* The sup-ball of (linhom_add_fun f g ∘ u) equals the diagonal sum
   sup-ball. Both have the same underlying chain (using Prop_irrelevance
   for the witness equalities). *)
have csb_eq :
  cone_sup_ball (linhom_add_fun f g \o u) fuch fub1 =
  cone_sup_ball
    (fun n => precone_add ((linhom_fun f \o u) n) ((linhom_fun g \o u) n))
    sch' sub'.
  apply: precone_le_anti.
  + apply: cone_sup_ball_lub => n.
    have -> : (linhom_add_fun f g \o u) n =
              precone_add ((linhom_fun f \o u) n) ((linhom_fun g \o u) n).
      by rewrite /= /linhom_add_fun.
    exact: cone_sup_ball_ub.
  + apply: cone_sup_ball_lub => n.
    have <- : (linhom_add_fun f g \o u) n =
              precone_add ((linhom_fun f \o u) n) ((linhom_fun g \o u) n).
      by rewrite /= /linhom_add_fun.
    exact: cone_sup_ball_ub.
rewrite csb_eq key.
(* Now both sides agree up to Prop_irrelevance on witnesses. *)
have e1 : fch = fch' by exact: Prop_irrelevance.
have e2 : fub = ub1c' by exact: Prop_irrelevance.
have e3 : gch = gch' by exact: Prop_irrelevance.
have e4 : gub = ub1c'' by exact: Prop_irrelevance.
by rewrite e1 e2 e3 e4.
Qed.

(** ω-continuity of the pointwise scaling.

    Strategy: use [sup_ball_scaler] in reverse and ω-continuity of [f]
    on a rescaled chain. Concretely:
    - Define [s := max 1 Mf] and [sinv := 1/s]. Then [‖sinv·u_n‖ ≤ 1]
      and [‖f(sinv·u_n)‖ = sinv·‖f u_n‖ ≤ sinv·Mf ≤ 1], so both [sinv·u]
      and [f∘(sinv·u)] are chains in B_C and B_D respectively.
    - By f's ω-continuity on the rescaled chain (sinv·u), [f(sinv·sup u)
      = sup(sinv·f u_n)] (using [sup_ball_scaler] on the LHS to identify
      [sinv·sup u = sup(sinv·u)]).
    - Pre-scaling by [r·s] and using [s·sinv = 1] gives
      [r·f(sup u) = sup(r·f u_n)] which is what we want, since
      [sup(r·sinv·f u_n) = sinv·sup(r·f u_n)] (by sup_ball_scaler on
      the [r·f u_n] chain, which IS unit-ball by hypothesis [fub1]).
*)
Lemma linhom_scale_fun_continuous (r : {nonneg R}) (f : linhom_car Ar C D) :
  is_omega_continuous (linhom_scale_fun r f).
Proof.
move=> u uch ub1 fuch fub1.
have Hf_cont := linhom_pre_continuous (linhom_pre_of f).
have Hf_lin := linhom_pre_linear (linhom_pre_of f).
have [_ HfD HfZ] := Hf_lin.
(* Build s := max 1 Mf and sinv := 1/s. *)
have [Mf HMf] := linhom_pre_bounded (linhom_pre_of f).
have Mfge0 : 0 <= Mf.
  apply: le_trans (HMf precone_zero _); first exact: cone_norm_ge0.
  by rewrite cone_norm0.
pose s_num : R := Order.max 1 Mf.
have s_pos : 0 < s_num by rewrite /s_num lt_max ltr01.
have s_ge1 : 1 <= s_num by rewrite /s_num le_max lexx.
have s_geMf : Mf <= s_num by rewrite /s_num le_max lexx orbT.
have s_ge0 : 0 <= s_num by exact: ltW.
pose s : {nonneg R} := NngNum s_ge0.
have sinv_ge0 : 0 <= s_num^-1 by rewrite invr_ge0 ltW.
pose sinv : {nonneg R} := NngNum sinv_ge0.
have nng_eq : forall (a b : {nonneg R}), a%:num = b%:num -> a = b.
  by move=> a b /val_inj.
have s_mul_sinv : s%:num * sinv%:num = 1.
  by rewrite /= mulfV // gt_eqF.
have sinv_mul_s : sinv%:num * s%:num = 1.
  by rewrite /= mulVf // gt_eqF.
have s_sinv : (s%:num * sinv%:num)%:nng = 1%:nng.
  by apply: nng_eq => /=; rewrite s_mul_sinv.
have sinv_s : (sinv%:num * s%:num)%:nng = 1%:nng.
  by apply: nng_eq => /=; rewrite sinv_mul_s.
(* The rescaled chain (sinv · u_n). *)
have vch : forall n, precone_le (precone_scale sinv (u n))
                                 (precone_scale sinv (u n.+1)).
  by move=> n; exact: precone_scale_le (uch n).
have sinv_le_1 : sinv%:num <= 1.
  by rewrite /= invf_le1 // s_ge1.
have vub : forall n, cnorm (precone_scale sinv (u n)) <= 1.
  move=> n; rewrite cone_normh.
  apply: le_trans (ler_pM sinv_ge0 (cone_norm_ge0 _)
                          sinv_le_1 (ub1 n)) _.
  by rewrite mulr1.
(* Image-chain [f(sinv·u_n)]. *)
have fvch : forall n,
    precone_le (linhom_fun f (precone_scale sinv (u n)))
               (linhom_fun f (precone_scale sinv (u n.+1))).
  by move=> n; exact: (linear_increasing Hf_lin) _ _ (vch n).
have sinv_Mf_le_1 : sinv%:num * Mf <= 1.
  have e : sinv%:num * Mf <= sinv%:num * s_num.
    by rewrite ler_pM2l // /= invr_gt0.
  apply: le_trans e _; rewrite /=.
  by rewrite mulVf // gt_eqF.
have fvub : forall n, cnorm (linhom_fun f (precone_scale sinv (u n))) <= 1.
  move=> n; rewrite /linhom_fun HfZ cone_normh /=.
  apply: le_trans (ler_pM sinv_ge0 (cone_norm_ge0 _)
                          (lexx _) (HMf _ (ub1 n))) _.
  exact: sinv_Mf_le_1.
(* By f's ω-continuity: f(sup(sinv·u)) = sup(f∘(sinv·u)). *)
have fv_sup : linhom_fun f (cone_sup_ball _ vch vub) =
              cone_sup_ball
                (linhom_fun f \o (fun n => precone_scale sinv (u n)))
                fvch fvub.
  exact: Hf_cont.
(* sup(sinv·u) = sinv·sup(u). *)
have v_sup : cone_sup_ball _ vch vub =
             precone_scale sinv (cone_sup_ball u uch ub1).
  exact: (@sup_ball_scaler R C sinv u uch ub1 vch vub).
(* So f(sinv·sup u) = sinv·f(sup u). *)
have lhs_eq : linhom_fun f (cone_sup_ball _ vch vub) =
              precone_scale sinv (linhom_fun f (cone_sup_ball u uch ub1)).
  by rewrite v_sup /linhom_fun HfZ.
(* Key identity from f's ω-continuity (after rescaling by sinv): *)
have fv_eq : (linhom_fun f \o (fun n => precone_scale sinv (u n))) =
             (fun n => precone_scale sinv (linhom_fun f (u n))).
  by apply: funext => n /=; rewrite /linhom_fun HfZ.
(* (sinv·f u_n) is a unit-ball chain. *)
have sinv_fu_ch : forall n,
    precone_le (precone_scale sinv (linhom_fun f (u n)))
               (precone_scale sinv (linhom_fun f (u n.+1))).
  move=> n; apply: precone_scale_le.
  have [_ HfD' HfZ'] := Hf_lin.
  exact: (linear_increasing Hf_lin) _ _ (uch n).
have sinv_fu_ub : forall n,
    cnorm (precone_scale sinv (linhom_fun f (u n))) <= 1.
  move=> n; rewrite cone_normh /=.
  apply: le_trans (ler_pM sinv_ge0 (cone_norm_ge0 _)
                          (lexx _) (HMf _ (ub1 n))) _.
  exact: sinv_Mf_le_1.
(* From fv_sup + fv_eq + lhs_eq + Prop_irrelevance:
   sinv · f(sup u) = cone_sup_ball (sinv · f u_n) sinv_fu_ch sinv_fu_ub. *)
have main_sinv_eq :
    precone_scale sinv (linhom_fun f (cone_sup_ball u uch ub1)) =
    cone_sup_ball (fun n => precone_scale sinv (linhom_fun f (u n)))
                  sinv_fu_ch sinv_fu_ub.
  rewrite -lhs_eq fv_sup.
  apply: precone_le_anti; apply: cone_sup_ball_lub => n.
  - have -> : (linhom_fun f \o (fun n0 => precone_scale sinv (u n0))) n =
              precone_scale sinv (linhom_fun f (u n)).
      by rewrite /= /linhom_fun HfZ.
    exact: cone_sup_ball_ub.
  - have <- : (linhom_fun f \o (fun n0 => precone_scale sinv (u n0))) n =
              precone_scale sinv (linhom_fun f (u n)).
      by rewrite /= /linhom_fun HfZ.
    exact: cone_sup_ball_ub.
(* (sinv · (r·f u_n)) is unit-ball. *)
have sinv_rfu_ch : forall n,
    precone_le (precone_scale sinv (linhom_scale_fun r f (u n)))
               (precone_scale sinv (linhom_scale_fun r f (u n.+1))).
  by move=> n; exact: precone_scale_le (fuch n).
have sinv_rfu_ub : forall n,
    cnorm (precone_scale sinv (linhom_scale_fun r f (u n))) <= 1.
  move=> n; rewrite cone_normh /=.
  apply: le_trans (ler_pM sinv_ge0 (cone_norm_ge0 _)
                          sinv_le_1 (fub1 n)) _.
  by rewrite mulr1.
(* By sup_ball_scaler on (r · f u_n) chain (which IS unit-ball):
   sup_n (sinv·(r·f u_n)) = sinv · sup_n (r·f u_n). *)
have scaled_sup_eq :
  cone_sup_ball (fun n => precone_scale sinv (linhom_scale_fun r f (u n)))
                sinv_rfu_ch sinv_rfu_ub =
  precone_scale sinv (cone_sup_ball (linhom_scale_fun r f \o u) fuch fub1).
  exact: (@sup_ball_scaler R D sinv _ fuch fub1 sinv_rfu_ch sinv_rfu_ub).
(* Algebra: sinv·(r·f u_n) = r·sinv·f u_n. So the chains [sinv · (r·f u_n)]
   and [r · (sinv·f u_n)] yield equal sup-balls. *)
have rsinv_fu_ch : forall n,
    precone_le (precone_scale r (precone_scale sinv (linhom_fun f (u n))))
               (precone_scale r (precone_scale sinv (linhom_fun f (u n.+1)))).
  by move=> n; exact: precone_scale_le (sinv_fu_ch n).
have rsinv_fu_ub : forall n,
    cnorm (precone_scale r (precone_scale sinv (linhom_fun f (u n)))) <= 1.
  move=> n.
  have eq_form : precone_scale r (precone_scale sinv (linhom_fun f (u n))) =
                 precone_scale sinv (linhom_scale_fun r f (u n)).
    rewrite /linhom_scale_fun /linhom_fun /= -!precone_scale_A.
    have eq1 : (r%:num * sinv%:num)%:nng = (sinv%:num * r%:num)%:nng.
      by apply: val_inj => /=; exact: mulrC.
    by rewrite eq1.
  rewrite eq_form; exact: sinv_rfu_ub.
have chain_swap_eq :
  cone_sup_ball (fun n => precone_scale sinv (linhom_scale_fun r f (u n)))
                sinv_rfu_ch sinv_rfu_ub =
  cone_sup_ball
    (fun n => precone_scale r (precone_scale sinv (linhom_fun f (u n))))
    rsinv_fu_ch rsinv_fu_ub.
  apply: precone_le_anti; apply: cone_sup_ball_lub => n.
  - have <- : precone_scale r (precone_scale sinv (linhom_fun f (u n))) =
              precone_scale sinv (linhom_scale_fun r f (u n)).
      rewrite /linhom_scale_fun /linhom_fun /= -!precone_scale_A.
      have eq1 : (r%:num * sinv%:num)%:nng = (sinv%:num * r%:num)%:nng.
        by apply: val_inj => /=; exact: mulrC.
      by rewrite eq1.
    exact: cone_sup_ball_ub.
  - have -> : precone_scale r (precone_scale sinv (linhom_fun f (u n))) =
              precone_scale sinv (linhom_scale_fun r f (u n)).
      rewrite /linhom_scale_fun /linhom_fun /= -!precone_scale_A.
      have eq1 : (r%:num * sinv%:num)%:nng = (sinv%:num * r%:num)%:nng.
        by apply: val_inj => /=; exact: mulrC.
      by rewrite eq1.
    exact: cone_sup_ball_ub.
(* By sup_ball_scaler on (sinv · f u_n) chain with scalar r:
   sup_n (r · (sinv·f u_n)) = r · sup_n (sinv·f u_n) = r · sinv · f(sup u). *)
have r_sinv_fu_sup_eq :
  cone_sup_ball
    (fun n => precone_scale r (precone_scale sinv (linhom_fun f (u n))))
    rsinv_fu_ch rsinv_fu_ub =
  precone_scale r
    (cone_sup_ball (fun n => precone_scale sinv (linhom_fun f (u n)))
                   sinv_fu_ch sinv_fu_ub).
  exact: (@sup_ball_scaler R D r _
            sinv_fu_ch sinv_fu_ub rsinv_fu_ch rsinv_fu_ub).
(* Combine: sinv · (r · f(sup u)) = sinv · sup_n (r·f u_n). *)
have core_eq : precone_scale sinv
                 (precone_scale r (linhom_fun f (cone_sup_ball u uch ub1))) =
               precone_scale sinv
                 (cone_sup_ball (linhom_scale_fun r f \o u) fuch fub1).
  rewrite -scaled_sup_eq chain_swap_eq r_sinv_fu_sup_eq.
  by rewrite -main_sinv_eq -!precone_scale_A
             (_ : (sinv%:num * r%:num)%:nng = (r%:num * sinv%:num)%:nng)
             ?precone_scale_A //;
     apply: val_inj => /=; exact: mulrC.
(* Multiply both sides by s: s · sinv · _ = _ (since s·sinv = 1). *)
have multiply_s : forall x : D, precone_scale s (precone_scale sinv x) = x.
  by move=> x; rewrite -precone_scale_A s_sinv precone_scale_1.
rewrite /linhom_scale_fun.
rewrite -(multiply_s (precone_scale r (linhom_fun f _))).
rewrite -[in RHS](multiply_s (cone_sup_ball _ _ _)).
by congr precone_scale.
Qed.

(** Path-preservation of pointwise sum. *)
Lemma linhom_add_fun_pres_path (f g : linhom_car Ar C D)
  (X : ar_obj Ar) (γ : ar_carrier Ar X -> C) :
  is_measurable_path γ ->
  is_measurable_path (fun r => linhom_add_fun f g (γ r)).
Proof.
move=> Hγ.
have Hfγ : is_measurable_path (fun r => linhom_fun f (γ r)).
  exact: (linhom_pre_pres_path (linhom_pre_of f)).
have Hgγ : is_measurable_path (fun r => linhom_fun g (γ r)).
  exact: (linhom_pre_pres_path (linhom_pre_of g)).
have [[Mf HMf] Hf_meas] := Hfγ.
have [[Mg HMg] Hg_meas] := Hgγ.
split.
  exists (Mf + Mg) => r.
  apply: le_trans (cone_normt _ _) _.
  by apply: lerD; [exact: HMf | exact: HMg].
move=> Y m mM.
have -> :
  (fun p : (ar_carrier Ar Y * ar_carrier Ar X)%type =>
    test_fun m p.1 (linhom_add_fun f g (γ p.2))) =
  (fun p : (ar_carrier Ar Y * ar_carrier Ar X)%type =>
    test_fun m p.1 (linhom_fun f (γ p.2)) +
    test_fun m p.1 (linhom_fun g (γ p.2))).
  by apply: funext => p; rewrite /linhom_add_fun test_linD.
by apply: measurable_funD;
  [exact: Hf_meas | exact: Hg_meas].
Qed.

(** Path-preservation of pointwise scaling. *)
Lemma linhom_scale_fun_pres_path (r : {nonneg R}) (f : linhom_car Ar C D)
  (X : ar_obj Ar) (γ : ar_carrier Ar X -> C) :
  is_measurable_path γ ->
  is_measurable_path (fun s => linhom_scale_fun r f (γ s)).
Proof.
move=> Hγ.
have Hfγ : is_measurable_path (fun s => linhom_fun f (γ s)).
  exact: (linhom_pre_pres_path (linhom_pre_of f)).
have [[Mf HMf] Hf_meas] := Hfγ.
split.
  exists (r%:num * Mf) => s.
  rewrite /linhom_scale_fun cone_normh.
  have rge0 : 0 <= r%:num by exact: nngnum_ge0.
  have [r0 | rpos] := eqVneq r%:num 0.
    by rewrite r0 !mul0r.
  by rewrite ler_pM2l ?lt_def ?rpos ?rge0 //; exact: HMf.
move=> Y m mM.
have -> :
  (fun p : (ar_carrier Ar Y * ar_carrier Ar X)%type =>
    test_fun m p.1 (linhom_scale_fun r f (γ p.2))) =
  (fun p : (ar_carrier Ar Y * ar_carrier Ar X)%type =>
    r%:num * test_fun m p.1 (linhom_fun f (γ p.2))).
  by apply: funext => p; rewrite /linhom_scale_fun test_linZ.
by apply: measurable_funM; [exact: measurable_cst | exact: Hf_meas].
Qed.

(** Integral-preservation of pointwise sum. *)
Lemma linhom_add_fun_pres_int (f g : linhom_car Ar C D)
  (X : ar_obj Ar) (β : ar_carrier Ar X -> C)
  (Hβ : is_measurable_path β)
  (µ : fmeas R (ar_carrier Ar X)) :
  linhom_add_fun f g (icone_integral β Hβ µ) =
  icone_integral (fun r => linhom_add_fun f g (β r))
    (linhom_add_fun_pres_path f g Hβ) µ.
Proof.
have Hpf := linhom_pres_int f X β Hβ µ.
have Hpg := linhom_pres_int g X β Hβ µ.
have Hfγ := linhom_pre_pres_path (linhom_pre_of f) X β Hβ.
have Hgγ := linhom_pre_pres_path (linhom_pre_of g) X β Hβ.
rewrite /linhom_add_fun /linhom_fun Hpf Hpg.
(* The sum of integrals satisfies the Pettis equation for the sum
   chain, by path_integral_eq_addB. Uniqueness gives equality with
   the icone_integral of the sum chain. *)
apply: icone_integral_eqP.
exact: (@path_integral_eq_addB R Ar D X µ _ _ _ _ Hfγ Hgγ
              (icone_integralP _ _ µ) (icone_integralP _ _ µ)).
Qed.

(** Integral-preservation of pointwise scaling. *)
Lemma linhom_scale_fun_pres_int (r : {nonneg R}) (f : linhom_car Ar C D)
  (X : ar_obj Ar) (β : ar_carrier Ar X -> C)
  (Hβ : is_measurable_path β)
  (µ : fmeas R (ar_carrier Ar X)) :
  linhom_scale_fun r f (icone_integral β Hβ µ) =
  icone_integral (fun s => linhom_scale_fun r f (β s))
    (linhom_scale_fun_pres_path r f Hβ) µ.
Proof.
have Hpf := linhom_pres_int f X β Hβ µ.
have Hfγ := linhom_pre_pres_path (linhom_pre_of f) X β Hβ.
rewrite /linhom_scale_fun /linhom_fun Hpf.
apply: icone_integral_eqP.
exact: (@path_integral_eq_scaleB R Ar D X µ r _ _ Hfγ
          (icone_integralP _ _ µ)).
Qed.

End LinhomAlgebra.

Arguments linhom_add_fun {R Ar C D}.
Arguments linhom_scale_fun {R Ar C D}.
Arguments linhom_add_fun_continuous {R Ar C D}.
Arguments linhom_scale_fun_continuous {R Ar C D}.
Arguments linhom_add_fun_pres_path {R Ar C D}.
Arguments linhom_scale_fun_pres_path {R Ar C D}.
Arguments linhom_add_fun_pres_int {R Ar C D}.
Arguments linhom_scale_fun_pres_int {R Ar C D}.

(** ** Pointwise addition / scaling as [linhom_car] — Paper §5.1 *)

Section LinhomAlgPack.
Variables (R : realType) (Ar : MeasSubcat R).
Variables C D : ICone.type Ar.

(** Pointwise addition packaged as a [linhom_pre]. *)
Definition linhom_add_pre (f g : linhom_car Ar C D) : linhom_pre Ar C D :=
  MkLinhomPre (linhom_add_fun f g)
              (linhom_add_fun_linear f g)
              (linhom_add_fun_continuous f g)
              (linhom_add_fun_bounded f g)
              (linhom_add_fun_pres_path f g).

(** Pointwise scaling packaged as a [linhom_pre]. *)
Definition linhom_scale_pre (r : {nonneg R}) (f : linhom_car Ar C D) :
    linhom_pre Ar C D :=
  MkLinhomPre (linhom_scale_fun r f)
              (linhom_scale_fun_linear r f)
              (linhom_scale_fun_continuous r f)
              (linhom_scale_fun_bounded r f)
              (linhom_scale_fun_pres_path r f).

(** Pointwise addition as a [linhom_car]. *)
Definition linhom_add (f g : linhom_car Ar C D) : linhom_car Ar C D :=
  MkLinhom (linhom_add_pre f g) (linhom_add_fun_pres_int f g).

(** Pointwise scaling as a [linhom_car]. *)
Definition linhom_scale (r : {nonneg R}) (f : linhom_car Ar C D) :
    linhom_car Ar C D :=
  MkLinhom (linhom_scale_pre r f) (linhom_scale_fun_pres_int r f).

End LinhomAlgPack.

Arguments linhom_add {R Ar C D}.
Arguments linhom_scale {R Ar C D}.

(** ** Precone axioms for [linhom_car] — Paper §5.1

    All algebraic axioms reduce to pointwise (Cancel), (Pos), and the
    [{nonneg R}]-semimodule laws of [D]. *)

Section LinhomPrecone.
Variables (R : realType) (Ar : MeasSubcat R).
Variables C D : ICone.type Ar.

Lemma linhom_addA : associative (@linhom_add R Ar C D).
Proof.
move=> f1 f2 f3; apply: linhom_eq => x /=.
exact: precone_addA.
Qed.

Lemma linhom_addC : commutative (@linhom_add R Ar C D).
Proof. move=> f1 f2; apply: linhom_eq => x /=; exact: precone_addC. Qed.

Lemma linhom_add0 : left_id (@linhom_zero R Ar C D) linhom_add.
Proof. by move=> f; apply: linhom_eq => x /=; exact: precone_add0. Qed.

Lemma linhom_scale_DAr (r : {nonneg R}) (f1 f2 : linhom_car Ar C D) :
  linhom_scale r (linhom_add f1 f2) =
  linhom_add (linhom_scale r f1) (linhom_scale r f2).
Proof.
apply: linhom_eq => x /=; exact: precone_scale_DAr.
Qed.

Lemma linhom_scale_DAl (r s : {nonneg R}) (f : linhom_car Ar C D) :
  linhom_scale (r%:num + s%:num)%:nng f =
  linhom_add (linhom_scale r f) (linhom_scale s f).
Proof.
apply: linhom_eq => x /=; exact: precone_scale_DAl.
Qed.

Lemma linhom_scale_A (r s : {nonneg R}) (f : linhom_car Ar C D) :
  linhom_scale (r%:num * s%:num)%:nng f =
  linhom_scale r (linhom_scale s f).
Proof.
apply: linhom_eq => x /=; exact: precone_scale_A.
Qed.

Lemma linhom_scale_1 (f : linhom_car Ar C D) : linhom_scale 1%:nng f = f.
Proof. apply: linhom_eq => x /=; exact: precone_scale_1. Qed.

Lemma linhom_scale_0r (r : {nonneg R}) :
  linhom_scale r (linhom_zero C D) = linhom_zero C D.
Proof. apply: linhom_eq => x /=; exact: precone_scale_0r. Qed.

Lemma linhom_scale_0l (f : linhom_car Ar C D) :
  linhom_scale 0%:nng f = linhom_zero C D.
Proof. apply: linhom_eq => x /=; exact: precone_scale_0l. Qed.

Lemma linhom_cancel (f1 f2 f3 : linhom_car Ar C D) :
  linhom_add f1 f2 = linhom_add f1 f3 -> f2 = f3.
Proof.
move=> H; apply: linhom_eq => x.
have /(congr1 (fun h => linhom_fun h x)) := H.
exact: precone_cancel.
Qed.

Lemma linhom_pos (f1 f2 : linhom_car Ar C D) :
  linhom_add f1 f2 = linhom_zero C D ->
  f1 = linhom_zero C D /\ f2 = linhom_zero C D.
Proof.
move=> H; split; apply: linhom_eq => x;
  have /(congr1 (fun h => linhom_fun h x)) /= := H.
- by move/precone_pos => -[].
- by move/precone_pos => -[].
Qed.

End LinhomPrecone.

(** ** Precone HB instance — Paper §5.1 *)

HB.instance Definition _ (R : realType) (Ar : MeasSubcat R)
    (C D : ICone.type Ar) :=
  @isPrecone.Build R (linhom_car Ar C D)
    (@linhom_zero R Ar C D) (@linhom_add R Ar C D) (@linhom_scale R Ar C D)
    (@linhom_addA R Ar C D) (@linhom_addC R Ar C D) (@linhom_add0 R Ar C D)
    (@linhom_scale_DAr R Ar C D) (@linhom_scale_DAl R Ar C D)
    (@linhom_scale_A R Ar C D) (@linhom_scale_1 R Ar C D)
    (@linhom_scale_0r R Ar C D) (@linhom_scale_0l R Ar C D)
    (@linhom_cancel R Ar C D) (@linhom_pos R Ar C D).

(** ** Operator norm on [linhom_car] — Paper §5.1

    Paper §5.1: [‖f‖ = sup {‖f x‖ | ‖x‖ ≤ 1}]. We define this as the
    canonical real-valued [sup] of the image set. The set is bounded
    above by [linmap_norm f] (M1's [cid]-extracted witness from
    Lemma 2.11),
    so it has a sup, and that sup is the *least* upper bound, hence
    fit for proving (Normh)/(Normz)/(Normt)/(Normp)/(Normc) in the
    [isCone] HB instance. *)

Section LinhomNorm.
Variables (R : realType) (Ar : MeasSubcat R).
Variables C D : ICone.type Ar.

(** The image norm-set: [{‖f x‖ | ‖x‖ ≤ 1}]. *)
Definition linhom_normset (f : linhom_car Ar C D) : set R :=
  [set y | exists x : C, cnorm x <= 1 /\ y = cnorm (linhom_fun f x)].

(** Nonempty: contains [cnorm (f 0) = 0] via [x := 0]. *)
Lemma linhom_normset_nonempty (f : linhom_car Ar C D) :
  linhom_normset f !=set0.
Proof.
exists 0; exists precone_zero; split; first by rewrite cone_norm0.
case: (linhom_pre_linear (linhom_pre_of f)) => H0 _ _.
by rewrite /linhom_fun H0 cone_norm0.
Qed.

(** Bounded above: M1's [linmap_norm] (a [cid]-extracted upper
    bound, not itself a supremum) bounds the set. *)
Lemma linhom_normset_has_ubound (f : linhom_car Ar C D) :
  has_ubound (linhom_normset f).
Proof.
exists (@linmap_norm R C D (linhom_fun f)
          (linhom_pre_linear (linhom_pre_of f))).
by move=> _ [x [Hx ->]]; exact: linmap_norm_ub.
Qed.

Lemma linhom_normset_has_sup (f : linhom_car Ar C D) :
  has_sup (linhom_normset f).
Proof.
by split; [exact: linhom_normset_nonempty | exact: linhom_normset_has_ubound].
Qed.

(** Paper §5.1: [‖f‖ = sup {‖f x‖ | ‖x‖ ≤ 1}]. *)
Definition linhom_norm (f : linhom_car Ar C D) : R :=
  sup (linhom_normset f).

(** Pointwise bound: [‖f x‖ ≤ ‖f‖] for [‖x‖ ≤ 1] — the sup is an
    upper bound. *)
Lemma linhom_norm_sup_ub (f : linhom_car Ar C D) (x : C) :
  cnorm x <= 1 -> cnorm (linhom_fun f x) <= linhom_norm f.
Proof.
move=> Hx.
move/ubP : (sup_upper_bound (linhom_normset_has_sup f)); apply.
by exists x.
Qed.

(** Least upper bound: any other upper bound of the image-norm set
    dominates [linhom_norm f]. *)
Lemma linhom_norm_sup_lub (f : linhom_car Ar C D) (M : R) :
  (forall x : C, cnorm x <= 1 -> cnorm (linhom_fun f x) <= M) ->
  linhom_norm f <= M.
Proof.
move=> HM.
apply: ge_sup; first exact: linhom_normset_nonempty.
by move=> _ [x [Hx ->]]; exact: HM.
Qed.

(** Kept for backwards compatibility with downstream callers. *)
Lemma linhom_norm_ub (f : linhom_car Ar C D) (x : C) :
  cnorm x <= 1 -> cnorm (linhom_fun f x) <= linhom_norm f.
Proof. exact: linhom_norm_sup_ub. Qed.

Lemma linhom_norm_ge0 (f : linhom_car Ar C D) : 0 <= linhom_norm f.
Proof.
have Hin : linhom_normset f 0.
  exists precone_zero; split; first by rewrite cone_norm0.
  case: (linhom_pre_linear (linhom_pre_of f)) => H0 _ _.
  by rewrite /linhom_fun H0 cone_norm0.
by move/ubP : (sup_upper_bound (linhom_normset_has_sup f)) => /(_ _ Hin).
Qed.

End LinhomNorm.

Arguments linhom_normset {R Ar C D}.
Arguments linhom_norm {R Ar C D}.
Arguments linhom_normset_nonempty {R Ar C D}.
Arguments linhom_normset_has_ubound {R Ar C D}.
Arguments linhom_normset_has_sup {R Ar C D}.
Arguments linhom_norm_sup_ub {R Ar C D}.
Arguments linhom_norm_sup_lub {R Ar C D}.
Arguments linhom_norm_ub {R Ar C D}.
Arguments linhom_norm_ge0 {R Ar C D}.

(** ** Pointwise order on [linhom_car] mirrors precone_le

    The precone-order on [linhom_car] (inherited via the [isPrecone]
    instance) is [f ≤p g] iff there is a [δ : linhom_car] with
    [g = linhom_add f δ]. Pointwise this gives [linhom_fun g x =
    precone_add (linhom_fun f x) (linhom_fun δ x)], hence
    [linhom_fun f x ≤p linhom_fun g x] in [D]. *)

Section LinhomLePointwise.
Variables (R : realType) (Ar : MeasSubcat R).
Variables C D : ICone.type Ar.

Lemma linhom_le_pointwise (f g : linhom_car Ar C D) :
  precone_le f g ->
  forall x : C, precone_le (linhom_fun f x) (linhom_fun g x).
Proof.
move=> [δ Hδ] x.
exists (linhom_fun δ x).
by have /(congr1 (fun h => linhom_fun h x)) /= := Hδ.
Qed.

End LinhomLePointwise.

(** ** Cone axioms on [linhom_car] — Paper §5.1

    With [linhom_norm] defined as the actual real-valued [sup], the
    five axioms (Normh)/(Normz)/(Normt)/(Normp)/(Normc) become sup
    manipulations (for the first four) plus a pointwise sup-ball
    construction (for the last one). *)

Section LinhomConeAxioms.
Variables (R : realType) (Ar : MeasSubcat R).
Variables C D : ICone.type Ar.
Implicit Types f g : linhom_car Ar C D.

(** (Normh) — Paper §5.1: scalar homogeneity of the operator norm.
    The image norm-set of [r *: f] is [r%:num * (image norm-set of f)]. *)
Lemma linhom_normh (r : {nonneg R}) f :
  linhom_norm (linhom_scale r f) = r%:num * linhom_norm f.
Proof.
have rge0 : 0 <= r%:num by exact: nngnum_ge0.
have [rzero | rpos] := lerP r%:num 0.
  have req0 : r%:num = 0 by apply: le_anti; rewrite rzero rge0.
  rewrite req0 mul0r.
  apply: le_anti; apply/andP; split; last exact: linhom_norm_ge0.
  apply: linhom_norm_sup_lub => x Hx /=.
  rewrite /linhom_fun /= /linhom_scale_fun cone_normh req0.
  by rewrite mul0r.
apply: le_anti; apply/andP; split.
- apply: linhom_norm_sup_lub => x Hx /=.
  rewrite /linhom_fun /= /linhom_scale_fun cone_normh.
  by rewrite ler_pM2l //; exact: linhom_norm_sup_ub.
- rewrite -ler_pdivlMl //.
  apply: linhom_norm_sup_lub => x Hx /=.
  rewrite ler_pdivlMl //.
  have Hin :
    linhom_normset (linhom_scale r f) (r%:num * cnorm (linhom_fun f x)).
    exists x; split=> //=.
    by rewrite /linhom_fun /= /linhom_scale_fun cone_normh.
  by move/ubP : (sup_upper_bound
    (linhom_normset_has_sup (linhom_scale r f))) => /(_ _ Hin).
Qed.

(** (Normz) — Paper §5.1: a linhom of norm zero is the zero linhom.
    From [linhom_norm f = 0] and (Normp)+(Normh) we get [cnorm (f x) = 0]
    for every [x] with [cnorm x ≤ 1]; by (Normz) in D, [f x = 0] for
    such [x]; by linearity, [f x = 0] for every [x]. *)
Lemma linhom_normz f : linhom_norm f = 0 -> f = linhom_zero C D.
Proof.
move=> H; apply: linhom_eq => x.
case: (linhom_pre_linear (linhom_pre_of f)) => H0 _ HZ.
have [x0 | xpos] := lerP (cnorm x) 0.
  have xeq0 : cnorm x = 0 by apply: le_anti; rewrite x0 cone_norm_ge0.
  have x_is_0 : x = precone_zero by exact: cone_normz.
  rewrite x_is_0.
  rewrite /linhom_fun /= H0.
  by rewrite /linhom_zero_fun.
(* cnorm x > 0: scale x to unit ball, use (Normz) on D. *)
have rge0 : 0 <= (cnorm x)^-1 by rewrite invr_ge0 ltW.
pose rinv : {nonneg R} := NngNum rge0.
have rinv_pos : 0 < rinv%:num by rewrite /= invr_gt0.
have scaled_unit : cnorm (precone_scale rinv x) <= 1.
  by rewrite cone_normh /= mulVf// gt_eqF.
have val0 : cnorm (linhom_fun f (precone_scale rinv x)) = 0.
  apply: le_anti; rewrite cone_norm_ge0 andbT.
  by rewrite -H; exact: linhom_norm_sup_ub.
have inner_zero : linhom_fun f (precone_scale rinv x) = precone_zero.
  exact: cone_normz.
(* By linearity, f (rinv *: x) = rinv *: f(x), so rinv *: f(x) = 0,
   then scale by cnorm x to get f(x) = 0. *)
have key : precone_scale rinv (linhom_fun f x) = precone_zero by rewrite -HZ.
(* Multiply by cnorm x: (cnorm x) *: (rinv *: f x) = (cnorm x * rinv) *: f x
   = 1 *: f x = f x. *)
have cnng_ge0 : 0 <= cnorm x by exact: cone_norm_ge0.
pose c : {nonneg R} := NngNum cnng_ge0.
have c_rinv_one : (NngNum (mulr_ge0 cnng_ge0 rge0)) =
                  (NngNum (@ler01 R)).
  by apply/val_inj => /=; rewrite mulfV// gt_eqF.
have := f_equal (precone_scale c) key.
rewrite precone_scale_0r => Hck.
have Hck2 : precone_scale c (precone_scale rinv (linhom_fun f x)) =
            linhom_fun f x.
  rewrite -precone_scale_A.
  have -> : (c%:num * rinv%:num)%:nng = 1%:nng :> {nonneg R}.
    by apply/val_inj => /=; rewrite mulfV// gt_eqF.
  by rewrite precone_scale_1.
by rewrite -Hck2 Hck /linhom_fun /= /linhom_zero_fun.
Qed.

(** (Normt) — Paper §5.1: triangle inequality. *)
Lemma linhom_normt f g :
  linhom_norm (linhom_add f g) <= linhom_norm f + linhom_norm g.
Proof.
apply: linhom_norm_sup_lub => x Hx /=.
apply: le_trans (cone_normt _ _) _.
by rewrite lerD //; exact: linhom_norm_sup_ub.
Qed.

(** (Normp) — Paper §5.1: order monotonicity of the operator norm. *)
Lemma linhom_normp f g :
  precone_le f g -> linhom_norm f <= linhom_norm g.
Proof.
move=> Hle.
apply: linhom_norm_sup_lub => x Hx.
apply: le_trans (cone_normp _ _ (linhom_le_pointwise Hle x)) _.
exact: linhom_norm_sup_ub.
Qed.

End LinhomConeAxioms.

(** ** (Normc) — pointwise sup-ball construction on [linhom_car]

    Given a [≤p]-increasing chain [(f_n)] in the unit ball of
    [linhom_car Ar C D], the pointwise sup [f_sup x := cone_sup_ball
    (n ↦ f_n x) ...] is a [linhom_car] (linear by [cone_sup_ball_addD]
    + [sup_ball_scaler], ω-continuous, bounded by 1, path-preserving,
    integral-preserving), and it is the LUB of the chain. *)

Section LinhomSupBall.
Variables (R : realType) (Ar : MeasSubcat R).
Variables C D : ICone.type Ar.

Variable u : nat -> linhom_car Ar C D.
Hypothesis uch : forall n, precone_le (u n) (u n.+1).
Hypothesis ub1 : forall n, linhom_norm (u n) <= 1.

(** Pointwise chain in [D] is [≤p]-increasing. *)
Lemma linhom_sup_pw_chain (x : C) n :
  precone_le (linhom_fun (u n) x) (linhom_fun (u n.+1) x).
Proof. exact: linhom_le_pointwise. Qed.

(** Pointwise chain at [x] in the unit ball of [C] is in the unit
    ball of [D]. *)
Lemma linhom_sup_pw_ub1 (x : C) (Hx : cnorm x <= 1) n :
  cnorm (linhom_fun (u n) x) <= 1.
Proof.
have := linhom_norm_sup_ub (u n) x Hx.
by move=> /le_trans; apply; exact: ub1.
Qed.

(** Pointwise sup on the unit ball of [C]: the [cone_sup_ball] of the
    pointwise chain in [D]. *)
Definition linhom_sup_unit (x : C) (Hx : cnorm x <= 1) : D :=
  cone_sup_ball (fun n => linhom_fun (u n) x)
                (fun n => linhom_sup_pw_chain x n)
                (linhom_sup_pw_ub1 Hx).

(** Pointwise definition of the sup-ball: for general [x], scale to
    the unit ball using [r := (cnorm x + 1)] (always positive), apply
    [linhom_sup_unit], then scale back. *)

(** [(cnorm x + 1)]-scaled inverse: norm of [x] divided by [cnorm x + 1]
    is at most 1. *)
Lemma cnorm_succ_pos (x : C) : 0 < cnorm x + 1.
Proof.
apply: lt_le_trans ltr01 _; rewrite -[X in X <= _]add0r lerD2r.
exact: cone_norm_ge0.
Qed.

Definition cnorm_succ_nng (x : C) : {nonneg R} :=
  NngNum (ltW (cnorm_succ_pos x)).

Lemma cnorm_succ_inv_ge0 (x : C) : 0 <= (cnorm x + 1)^-1.
Proof. by rewrite invr_ge0 ltW//; exact: cnorm_succ_pos. Qed.

Definition cnorm_succ_inv_nng (x : C) : {nonneg R} :=
  NngNum (cnorm_succ_inv_ge0 x).

Lemma cnorm_succ_mulV (x : C) :
  (cnorm_succ_nng x)%:num * (cnorm_succ_inv_nng x)%:num = 1.
Proof. by rewrite /= mulfV// gt_eqF//; exact: cnorm_succ_pos. Qed.

(** Helper: scaling by [(cnorm x + 1)] cancels with scaling by its
    inverse. *)
Lemma cnorm_succ_scaleK (x : C) (y : D) :
  precone_scale (cnorm_succ_nng x)
    (precone_scale (cnorm_succ_inv_nng x) y) = y.
Proof.
rewrite -precone_scale_A.
have nng_eq : forall (a b : {nonneg R}), a%:num = b%:num -> a = b.
  by move=> a b /val_inj.
rewrite (_ : (_)%:nng = 1%:nng) ?precone_scale_1//.
by apply: nng_eq => /=; exact: cnorm_succ_mulV.
Qed.

Lemma cnorm_inv_unit (x : C) :
  cnorm (precone_scale (cnorm_succ_inv_nng x) x) <= 1.
Proof.
rewrite cone_normh /=.
have hp : 0 < cnorm x + 1 by exact: cnorm_succ_pos.
rewrite mulrC ler_pdivrMr // mul1r.
by rewrite -[X in X <= _]addr0 lerD2l ler01.
Qed.

(** The candidate [f_sup x] for arbitrary [x]. *)
Definition linhom_sup_fun (x : C) : D :=
  precone_scale (cnorm_succ_nng x)
    (linhom_sup_unit (cnorm_inv_unit x)).

(** Helper: [f_sup x] equals [(cnorm x + 1) *: (sup ((f_n) (x/(cnorm x+1))))]. *)
Lemma linhom_sup_funE (x : C) :
  linhom_sup_fun x =
  precone_scale (cnorm_succ_nng x)
    (cone_sup_ball
       (fun n => linhom_fun (u n) (precone_scale (cnorm_succ_inv_nng x) x))
       (fun n => linhom_sup_pw_chain _ n)
       (linhom_sup_pw_ub1 (cnorm_inv_unit x))).
Proof. by []. Qed.

(** ** Algebraic properties of [linhom_sup_fun]

    The pointwise sup interacts cleanly with the linear structure of
    [u_n] via the diagonal-sup identity. *)

(** Helper: [f_sup x = ‖x‖_+ *: sup_n (f_n (rinv *: x))]. To prove
    linearity, we will use a stronger equation: for any positive [r]
    with [‖rinv x‖ ≤ 1], [f_sup x = r *: sup_n (f_n (rinv *: x))]. *)
Lemma linhom_sup_unitE (x : C) (Hx : cnorm x <= 1) :
  linhom_sup_unit Hx =
  cone_sup_ball (fun n => linhom_fun (u n) x)
                (fun n => linhom_sup_pw_chain x n)
                (linhom_sup_pw_ub1 Hx).
Proof. by []. Qed.

(** Auxiliary: the positive-real inverse of an [{nonneg R}] is itself
    [{nonneg R}]. We will use this when scaling by [α⁻¹] for [α > 0]. *)
Lemma nng_inv_ge0 (α : {nonneg R}) : 0 <= α%:num^-1.
Proof. by rewrite invr_ge0; exact: nngnum_ge0. Qed.

Definition nng_inv (α : {nonneg R}) : {nonneg R} := NngNum (nng_inv_ge0 α).

(** When [x] is in the unit ball, [f_sup x] agrees with the unit-ball
    pointwise sup (up to scaling). Concretely, by linearity of
    [f_n] applied to [rinv *: x], the inner sup equals
    [rinv *: (sup_n f_n x)], so [f_sup x = r *: rinv *: (sup_n f_n x)
    = sup_n f_n x]. *)
Lemma linhom_sup_fun_unitE (x : C) (Hx : cnorm x <= 1) :
  linhom_sup_fun x = linhom_sup_unit Hx.
Proof.
rewrite linhom_sup_funE linhom_sup_unitE.
set rinv := cnorm_succ_inv_nng x.
set r := cnorm_succ_nng x.
have linZ : forall n, linhom_fun (u n) (precone_scale rinv x) =
                      precone_scale rinv (linhom_fun (u n) x).
  move=> n; case: (linhom_pre_linear (linhom_pre_of (u n))) => _ _ HZ.
  exact: HZ.
pose ch1 (n : nat) : D := linhom_fun (u n) (precone_scale rinv x).
have ch1_eq : ch1 = (fun n => linhom_fun (u n) (precone_scale rinv x))
  by [].
set ub1' := linhom_sup_pw_ub1 (cnorm_inv_unit x).
set ub2 := linhom_sup_pw_ub1 Hx.
set ch2 := [eta linhom_sup_pw_chain (precone_scale rinv x)].
apply: precone_le_anti.
- (* r *: cone_sup_ball ch1 ≤p cone_sup_ball (n ↦ f_n x). *)
  (* For each n, f_n x = r *: f_n (rinv *: x). So r *: cone_sup_ball ch1
     ≤p r *: f_n (rinv *: x) + ... is structurally cone_sup_ball ub. *)
  have step : forall n,
      linhom_fun (u n) x =
      precone_scale r (linhom_fun (u n) (precone_scale rinv x)).
    by move=> n; rewrite linZ cnorm_succ_scaleK.
  (* r-scaled chain *)
  pose ch_r (n : nat) : D := precone_scale r (ch1 n).
  have ch_r_chain : forall n, precone_le (ch_r n) (ch_r n.+1).
    by move=> n; rewrite /ch_r; apply: precone_scale_le; exact: ch2.
  have ch_r_ub1 : forall n, cnorm (ch_r n) <= 1.
    move=> n; rewrite /ch_r -step.
    by have := linhom_sup_pw_ub1 Hx n.
  have Hsup_eq :=
    @sup_ball_scaler R D r ch1 ch2 ub1' ch_r_chain ch_r_ub1.
  rewrite /ch_r in Hsup_eq.
  rewrite -Hsup_eq.
  apply: cone_sup_ball_lub => n.
  rewrite /ch1 -step.
  exact: cone_sup_ball_ub.
- (* cone_sup_ball (n ↦ f_n x) ≤p r *: cone_sup_ball ch1. *)
  apply: cone_sup_ball_lub => n.
  have step : linhom_fun (u n) x =
              precone_scale r (linhom_fun (u n) (precone_scale rinv x)).
    by rewrite linZ cnorm_succ_scaleK.
  rewrite step.
  apply: precone_scale_le.
  exact: cone_sup_ball_ub.
Qed.

(** ** Linearity equations for [linhom_sup_fun] — Paper §5.1 (key step)

    These three equations witness that the pointwise sup is linear,
    so that we can package it as a [linhom_car]. The hardest is
    [linZ] (scalar multiplication); we use a case-split on [r = 0]
    plus a rescaling argument for [r > 0]. *)

(** [linhom_sup_fun 0 = 0]: by [linhom_sup_fun_unitE] at [precone_zero]
    (in the unit ball) and the fact that each [f_n 0 = 0]. *)
Lemma linhom_sup_fun_lin0 : linhom_sup_fun precone_zero = precone_zero.
Proof.
have Hz : cnorm (precone_zero : C) <= 1 by rewrite cone_norm0.
rewrite (linhom_sup_fun_unitE Hz) /linhom_sup_unit.
have Hfn0 : forall n,
    linhom_fun (u n) (precone_zero : C) = (precone_zero : D).
  by move=> n; case: (linhom_pre_linear (linhom_pre_of (u n))) => H0 _ _.
apply: precone_le_anti.
- apply: cone_sup_ball_lub => n.
  by rewrite /= Hfn0; exact: precone_le_refl.
- exists (cone_sup_ball (fun n => linhom_fun (u n) (precone_zero : C))
                         [eta linhom_sup_pw_chain (precone_zero : C)]
                         (linhom_sup_pw_ub1 Hz)).
  by rewrite precone_add0.
Qed.

(** [linhom_sup_fun (r *: x) = r *: linhom_sup_fun x]: case split on
    [r = 0] vs [r > 0]. The positive case uses the unit-ball point
    [u := (cnorm x + 1)⁻¹ *: x] and writes both sides in terms of
    [linhom_sup_unit] at this [u], reducing the equality to an
    application of [sup_ball_scaler]. *)
Lemma linhom_sup_fun_linZ (r : {nonneg R}) (x : C) :
  linhom_sup_fun (precone_scale r x) =
  precone_scale r (linhom_sup_fun x).
Proof.
have [r0 | rne] := eqVneq r 0%:nng.
- rewrite r0 precone_scale_0l precone_scale_0l.
  exact: linhom_sup_fun_lin0.
- have rpos : 0 < r%:num.
    rewrite lt0r; apply/andP; split; last exact: nngnum_ge0.
    by apply/eqP => Hr0; move/eqP : rne; apply; apply: val_inj.
  (* Notations: u := xc1 *: x is in B_C; β := xs := cnorm x + 1.
     Then x = β *: u (cnorm_succ_scaleK), r *: x = (r * β) *: u. *)
  set xc1 := cnorm_succ_inv_nng x.
  set xs := cnorm_succ_nng x.
  set xrc1 := cnorm_succ_inv_nng (precone_scale r x).
  set xrs := cnorm_succ_nng (precone_scale r x).
  (* By definition: linhom_sup_fun (r *: x) = xrs *: lsu (xrc1 *: r *: x). *)
  rewrite /linhom_sup_fun -/xs -/xrs -/xc1 -/xrc1.
  rewrite -/(linhom_sup_unit (cnorm_inv_unit (precone_scale r x))).
  rewrite -/(linhom_sup_unit (cnorm_inv_unit x)).
  (* The unit-ball point xrc1 *: r *: x is r * xrc1 *: x = δ *: (xc1 *: x).
     Define δ : {nonneg R} as r * xrc1, then we equate the two unit-ball
     points via linhom_sup_unit's value at scaled unit-ball arguments. *)
  pose δ_num : R := r%:num * xrc1%:num.
  have δ_ge0 : 0 <= δ_num.
    by rewrite mulr_ge0 //; exact: nngnum_ge0.
  pose δ : {nonneg R} := NngNum δ_ge0.
  (* δ_num = r/(r*cnorm x + 1) ≤ 1/cnorm x (when cnorm x > 0); but more
     directly, since xrc1 *: (r *: x) has norm ≤ 1, and equals δ *: x. *)
  have eq_δx : precone_scale δ x = precone_scale xrc1 (precone_scale r x).
    rewrite -precone_scale_A.
    by congr precone_scale; apply: val_inj => /=; exact: mulrC.
  have δx_unit : cnorm (precone_scale δ x) <= 1.
    by rewrite eq_δx; exact: cnorm_inv_unit.
  (* Step 1: linhom_sup_unit (cnorm_inv_unit (r *: x)) = lsu at δ *: x.
     Both unit-ball points are equal (eq_δx), so the unit-ball lsu's
     are equal up to Prop_irrelevance of the bound. *)
  have lsu_unit_eq :
    linhom_sup_unit (cnorm_inv_unit (precone_scale r x)) =
    linhom_sup_unit δx_unit.
    rewrite /linhom_sup_unit.
    apply: precone_le_anti.
    + apply: cone_sup_ball_lub => n.
      by rewrite -eq_δx /=; exact: cone_sup_ball_ub.
    + apply: cone_sup_ball_lub => n.
      by rewrite eq_δx /=; exact: cone_sup_ball_ub.
  rewrite lsu_unit_eq.
  (* Step 2: linhom_sup_unit at δ *: x = δ *: linhom_sup_unit at x (xc1 form),
     pushed via linearity and sup_ball_scaler. Actually we use: the chain
     (f_n (δ x))_n equals (δ *: f_n x)_n (by linearity), and the chain
     (f_n (xc1 x))_n is unit-ball, with δ *: (f_n (xc1 x)) being (since
     δ x = ? *: xc1 x, not directly equal — need the right scaling).

     Actually use the unit-ball form: u := xc1 *: x. Then δ *: x =
     (δ%:num * xs%:num) *: u. Let γ := δ * xs. *)
  pose γ_num : R := δ_num * xs%:num.
  have γ_ge0 : 0 <= γ_num.
    by apply: mulr_ge0; rewrite ?nngnum_ge0.
  pose γ : {nonneg R} := NngNum γ_ge0.
  have eq_γu : precone_scale δ x =
               precone_scale γ (precone_scale xc1 x).
    rewrite -precone_scale_A.
    congr precone_scale; apply: val_inj => /=.
    rewrite /γ_num /xs /=.
    by rewrite -mulrA mulfV ?gt_eqF ?cnorm_succ_pos // mulr1.
  pose u_x := precone_scale xc1 x.
  have u_x_unit : cnorm u_x <= 1 by exact: cnorm_inv_unit.
  have γu_unit : cnorm (precone_scale γ u_x) <= 1 by rewrite -eq_γu.
  have linZ_fn : forall n,
      linhom_fun (u n) (precone_scale γ u_x) =
      precone_scale γ (linhom_fun (u n) u_x).
    move=> n; case: (linhom_pre_linear (linhom_pre_of (u n))) => _ _ HZ.
    exact: HZ.
  (* Build the rescaled chain and apply sup_ball_scaler. *)
  have ch_u_chain : forall n,
      precone_le (linhom_fun (u n) u_x) (linhom_fun (u n.+1) u_x).
    by move=> n; exact: linhom_sup_pw_chain.
  have ch_u_ub : forall n, cone_norm (linhom_fun (u n) u_x) <= 1.
    by move=> n; exact: linhom_sup_pw_ub1.
  have ch_γu_chain : forall n,
      precone_le (precone_scale γ (linhom_fun (u n) u_x))
                 (precone_scale γ (linhom_fun (u n.+1) u_x)).
    by move=> n; apply: precone_scale_le; exact: ch_u_chain.
  have ch_γu_ub : forall n,
      cone_norm (precone_scale γ (linhom_fun (u n) u_x)) <= 1.
    move=> n; rewrite -linZ_fn.
    exact: linhom_sup_pw_ub1.
  (* sup_ball_scaler gives us: cone_sup_ball(γ *: f_n u) = γ *: cone_sup_ball(f_n u). *)
  have scaler_eq :
    cone_sup_ball (fun n => precone_scale γ (linhom_fun (u n) u_x))
                  ch_γu_chain ch_γu_ub =
    precone_scale γ
      (cone_sup_ball (fun n => linhom_fun (u n) u_x) ch_u_chain ch_u_ub).
    exact: (@sup_ball_scaler R D γ (fun n => linhom_fun (u n) u_x)
                            ch_u_chain ch_u_ub ch_γu_chain ch_γu_ub).
  (* Bridge through Prop_irrelevance: rewrite δx unit-ball lsu using γ form. *)
  have lsu_δx_eq_γu :
    linhom_sup_unit δx_unit = linhom_sup_unit γu_unit.
    rewrite /linhom_sup_unit.
    apply: precone_le_anti.
    + apply: cone_sup_ball_lub => n.
      by rewrite eq_γu /=; exact: cone_sup_ball_ub.
    + apply: cone_sup_ball_lub => n.
      by rewrite -eq_γu /=; exact: cone_sup_ball_ub.
  rewrite lsu_δx_eq_γu.
  (* The unit-ball cone_sup_ball at u_x in linhom_sup_unit form versus
     in (ch_u_chain, ch_u_ub) form: equal by Prop_irrelevance. *)
  have csb_eq :
    cone_sup_ball (fun n => linhom_fun (u n) u_x)
                  [eta linhom_sup_pw_chain u_x] (linhom_sup_pw_ub1 u_x_unit) =
    cone_sup_ball (fun n => linhom_fun (u n) u_x) ch_u_chain ch_u_ub.
    have e1 : [eta linhom_sup_pw_chain u_x] = ch_u_chain
      by exact: Prop_irrelevance.
    have e2 : linhom_sup_pw_ub1 u_x_unit = ch_u_ub
      by exact: Prop_irrelevance.
    by rewrite e1 e2.
  (* Now: linhom_sup_unit γu_unit = γ *: cone_sup_ball (ch_u). *)
  have lsu_γu_eq :
    linhom_sup_unit γu_unit =
    precone_scale γ (linhom_sup_unit u_x_unit).
    rewrite /linhom_sup_unit.
    apply: precone_le_anti.
    - apply: cone_sup_ball_lub => n.
      rewrite /= linZ_fn.
      apply: precone_scale_le.
      exact: cone_sup_ball_ub.
    - rewrite csb_eq -scaler_eq.
      apply: cone_sup_ball_lub => n.
      rewrite /= -linZ_fn.
      exact: cone_sup_ball_ub.
  rewrite lsu_γu_eq.
  rewrite /linhom_sup_fun -/xs -/xc1 -/(linhom_sup_unit (cnorm_inv_unit x)).
  rewrite -!precone_scale_A.
  (* Algebra: xrs * γ = r * xs and the two linhom_sup_unit's are equal
     by Prop_irrelevance. *)
  have lsu_eq :
    linhom_sup_unit u_x_unit = linhom_sup_unit (cnorm_inv_unit x).
    rewrite /linhom_sup_unit.
    have e2 : linhom_sup_pw_ub1 u_x_unit =
              linhom_sup_pw_ub1 (cnorm_inv_unit x) by exact: Prop_irrelevance.
    by rewrite e2.
  rewrite lsu_eq.
  congr precone_scale.
  apply: val_inj => /=.
  rewrite /γ_num /δ_num.
  rewrite mulrA mulrCA mulrA.
  have crx_simpl : (cnorm (r *: x)%PC + 1) *
                   (cnorm_succ_inv_nng (r *: x)%PC)%:num = 1.
    by rewrite /= mulfV// gt_eqF//; exact: cnorm_succ_pos.
  have crx_inv2 :
    r%:num * (cnorm (r *: x)%PC + 1) *
    (cnorm_succ_inv_nng (r *: x)%PC)%:num = r%:num.
    by rewrite -mulrA crx_simpl mulr1.
  by rewrite crx_inv2 /xs/=.
Qed.

(** Helper: given [s : {nonneg R}] positive with [s⁻¹ *: x] in [B_C],
    we have [linhom_sup_fun x = s *: linhom_sup_unit Hxs]. Used to
    rewrite [linhom_sup_fun] at a common scale across multiple
    points, which is essential for [linD]. *)
Lemma linhom_sup_fun_at_scale (x : C) (s : {nonneg R}) (Hs : 0 < s%:num)
    (Hxs : cnorm (precone_scale (nng_inv s) x) <= 1) :
  linhom_sup_fun x = precone_scale s (linhom_sup_unit Hxs).
Proof.
have eq_x : x = precone_scale s (precone_scale (nng_inv s) x).
  rewrite -precone_scale_A.
  have -> : (s%:num * (nng_inv s)%:num)%:nng = 1%:nng :> {nonneg R}.
    by apply: val_inj => /=; rewrite mulfV// gt_eqF.
  by rewrite precone_scale_1.
rewrite {1}eq_x linhom_sup_fun_linZ.
congr precone_scale.
exact: linhom_sup_fun_unitE.
Qed.

(** [linhom_sup_fun (x + y) = linhom_sup_fun x + linhom_sup_fun y]:
    rescaling trick. With [s := (cnorm x + cnorm y + 1)] we have
    [(s⁻¹ *: x), (s⁻¹ *: y), (s⁻¹ *: (x+y))] all in [B_C]. Apply
    [linhom_sup_fun_at_scale] at [s] for each of the three points, and
    use [cone_sup_ball_addD] to commute the sup with the sum on the
    common-scale unit-ball form. *)
Lemma linhom_sup_fun_linD (x y : C) :
  linhom_sup_fun (precone_add x y) =
  precone_add (linhom_sup_fun x) (linhom_sup_fun y).
Proof.
(* Pick s := cnorm x + cnorm y + 1, definitely positive. *)
have s_pos : 0 < cnorm x + cnorm y + 1.
  apply: lt_le_trans ltr01 _.
  rewrite -[X in X <= _]add0r lerD2r addr_ge0 //; exact: cone_norm_ge0.
have s_ge0 : 0 <= cnorm x + cnorm y + 1 by exact: ltW.
pose s : {nonneg R} := NngNum s_ge0.
have spos : 0 < s%:num := s_pos.
(* Verify the three norm bounds. *)
have Hsx : cnorm (precone_scale (nng_inv s) x) <= 1.
  rewrite cone_normh /=.
  rewrite mulrC ler_pdivrMr // mul1r.
  rewrite -[X in X <= _]addr0 -addrA lerD2l.
  by rewrite addr_ge0 ?cone_norm_ge0 ?ler01.
have Hsy : cnorm (precone_scale (nng_inv s) y) <= 1.
  rewrite cone_normh /=.
  rewrite mulrC ler_pdivrMr // mul1r.
  by rewrite addrAC -[X in X <= _]add0r lerD2r addr_ge0 // cone_norm_ge0.
have Hsxy : cnorm (precone_scale (nng_inv s) (precone_add x y)) <= 1.
  rewrite cone_normh /=.
  apply: le_trans (ler_pM _ _ (lexx _) (cone_normt x y)) _.
  - by rewrite invr_ge0 ltW.
  - exact: cone_norm_ge0.
  rewrite mulrC ler_pdivrMr // mul1r.
  by rewrite -[X in X <= _]addr0 lerD2l ler01.
(* Apply at_scale to each. *)
rewrite (linhom_sup_fun_at_scale spos Hsxy).
rewrite (linhom_sup_fun_at_scale spos Hsx).
rewrite (linhom_sup_fun_at_scale spos Hsy).
(* Goal: s *: lsu(s⁻¹ (x+y)) = s *: lsu(s⁻¹ x) + s *: lsu(s⁻¹ y).
   Use precone_scale_DAr on the RHS, then apply cone_sup_ball_addD. *)
rewrite -precone_scale_DAr.
congr precone_scale.
(* Goal: lsu(s⁻¹ (x+y)) = lsu(s⁻¹ x) + lsu(s⁻¹ y). *)
rewrite /linhom_sup_unit.
(* For each n, f_n(s⁻¹ (x+y)) = f_n(s⁻¹ x) + f_n(s⁻¹ y) by linearity. *)
have linD_fn : forall n,
    linhom_fun (u n) (precone_scale (nng_inv s) (precone_add x y)) =
    precone_add (linhom_fun (u n) (precone_scale (nng_inv s) x))
                (linhom_fun (u n) (precone_scale (nng_inv s) y)).
  move=> n.
  case: (linhom_pre_linear (linhom_pre_of (u n))) => _ HD _.
  rewrite precone_scale_DAr.
  exact: HD.
(* Set up the chains needed by cone_sup_ball_addD. *)
pose a (n : nat) : D := linhom_fun (u n) (precone_scale (nng_inv s) x).
pose b (n : nat) : D := linhom_fun (u n) (precone_scale (nng_inv s) y).
have a_chain : forall n, precone_le (a n) (a n.+1).
  by move=> n; exact: linhom_sup_pw_chain.
have b_chain : forall n, precone_le (b n) (b n.+1).
  by move=> n; exact: linhom_sup_pw_chain.
have a_ub : forall n, cone_norm (a n) <= 1.
  by move=> n; exact: linhom_sup_pw_ub1.
have b_ub : forall n, cone_norm (b n) <= 1.
  by move=> n; exact: linhom_sup_pw_ub1.
have ab_chain : forall n,
    precone_le (precone_add (a n) (b n)) (precone_add (a n.+1) (b n.+1)).
  move=> n.
  rewrite -(linD_fn n) -(linD_fn n.+1).
  exact: linhom_sup_pw_chain.
have ab_ub : forall n, cone_norm (precone_add (a n) (b n)) <= 1.
  move=> n; rewrite -(linD_fn n).
  exact: linhom_sup_pw_ub1.
(* The key: cone_sup_ball_addD. *)
have addD := @cone_sup_ball_addD R D a b
                a_chain a_ub b_chain b_ub ab_chain ab_ub.
(* Now relate the linhom_sup_unit's to the cone_sup_balls. *)
(* lsu(s⁻¹(x+y)) = cone_sup_ball (a + b) = (by linD_fn) cone_sup_ball (f_n(s⁻¹(x+y))). *)
have csb_xy :
  cone_sup_ball (fun n => linhom_fun (u n)
                            (precone_scale (nng_inv s) (precone_add x y)))
                [eta linhom_sup_pw_chain _]
                (linhom_sup_pw_ub1 Hsxy) =
  cone_sup_ball (fun n => precone_add (a n) (b n)) ab_chain ab_ub.
  apply: precone_le_anti.
  - apply: cone_sup_ball_lub => n.
    rewrite /= linD_fn.
    exact: cone_sup_ball_ub.
  - apply: cone_sup_ball_lub => n.
    rewrite /= -linD_fn.
    exact: cone_sup_ball_ub.
have csb_x :
  cone_sup_ball (fun n => linhom_fun (u n) (precone_scale (nng_inv s) x))
                [eta linhom_sup_pw_chain _]
                (linhom_sup_pw_ub1 Hsx) =
  cone_sup_ball a a_chain a_ub.
  have e1 : [eta linhom_sup_pw_chain (precone_scale (nng_inv s) x)] = a_chain
    by exact: Prop_irrelevance.
  have e2 : linhom_sup_pw_ub1 Hsx = a_ub by exact: Prop_irrelevance.
  by rewrite e1 e2.
have csb_y :
  cone_sup_ball (fun n => linhom_fun (u n) (precone_scale (nng_inv s) y))
                [eta linhom_sup_pw_chain _]
                (linhom_sup_pw_ub1 Hsy) =
  cone_sup_ball b b_chain b_ub.
  have e1 : [eta linhom_sup_pw_chain (precone_scale (nng_inv s) y)] = b_chain
    by exact: Prop_irrelevance.
  have e2 : linhom_sup_pw_ub1 Hsy = b_ub by exact: Prop_irrelevance.
  by rewrite e1 e2.
by rewrite csb_xy csb_x csb_y addD.
Qed.

(** Norm bound: [cnorm (linhom_sup_fun x) ≤ cnorm x] (operator-norm
    bound at 1 for chains of unit-ball-bounded morphisms). *)
Lemma linhom_sup_fun_norm_le (x : C) :
  cnorm (linhom_sup_fun x) <= cnorm x.
Proof.
have [x0 | xpos] := lerP (cnorm x) 0.
  have xeq0 : cnorm x = 0 by apply: le_anti; rewrite x0 cone_norm_ge0.
  have xis0 : x = precone_zero by exact: cone_normz.
  rewrite xis0 linhom_sup_fun_lin0 cone_norm0; exact: cone_norm_ge0.
(* cnorm x > 0: scale by 1/cnorm x. *)
have xge0 : 0 <= cnorm x by exact: cone_norm_ge0.
pose cn : {nonneg R} := NngNum xge0.
have cnpos : 0 < cn%:num := xpos.
have Hxcn : cnorm (precone_scale (nng_inv cn) x) <= 1.
  rewrite cone_normh /=.
  by rewrite mulVf// gt_eqF.
rewrite (linhom_sup_fun_at_scale cnpos Hxcn) cone_normh.
rewrite -[X in _ <= X]mulr1.
apply: ler_pM; [exact: nngnum_ge0|exact: cone_norm_ge0|exact: lexx|].
exact: cone_sup_ball_norm.
Qed.

(** Boundedness as required for [linhom_pre]. *)
Lemma linhom_sup_fun_bounded :
  exists M : R, forall x : C, cnorm x <= 1 -> cnorm (linhom_sup_fun x) <= M.
Proof.
exists 1 => x Hx.
apply: le_trans (linhom_sup_fun_norm_le x) Hx.
Qed.

(** ** ω-continuity of [linhom_sup_fun] — Paper §5.1 (Step 2a)

    Strategy. We must show that the pointwise sup [linhom_sup_fun] is
    itself ω-continuous as a function [C -> D]. The argument is the
    commutation of two sups: for an inner chain [(x_k)] in the unit
    ball of [C] with sup [xs],

      [linhom_sup_fun xs = sup_n (linhom_fun u_n xs)
                        = sup_n sup_k (linhom_fun u_n (x_k))    (ω-cont u_n)
                        = sup_k sup_n (linhom_fun u_n (x_k))    (swap)
                        = sup_k (linhom_sup_fun (x_k))]

    The middle equality is the commutation of two sups. Both sides
    are LUBs of the same doubly-indexed family, hence equal by
    anti-symmetry of [≤p]. We package the swap as an auxiliary
    lemma [cone_sup_ball_swap], working in the inner cone [D]. *)

Section LinhomSupCont.
Local Open Scope precone_scope.

(** Commutation of two unit-ball sups in [D]. Given a doubly-indexed
    family [b : nat -> nat -> D] with row and column unit-ball chains
    and entry-wise unit-ball bound, the iterated sup commutes. This
    is the instance at [D] of the consolidated
    [omega_general.cone_sup_ball_swap], which holds in any
    [coneType]; the name is kept here for the blueprint and for the
    use in [linhom_sup_fun_continuous] just below. *)
Lemma cone_sup_ball_swap (b : nat -> nat -> D)
    (b_row_ch : forall k n, b n k <=p b n.+1 k)
    (b_col_ch : forall n k, b n k <=p b n k.+1)
    (b_ub : forall n k, cnorm (b n k) <= 1)
    (b_col_sup_ub : forall n,
       cnorm
         (cone_sup_ball (b n) (b_col_ch n) (fun k => b_ub n k)) <= 1)
    (b_col_sup_ch : forall n,
       cone_sup_ball (b n) (b_col_ch n) (fun k => b_ub n k) <=p
       cone_sup_ball (b n.+1) (b_col_ch n.+1) (fun k => b_ub n.+1 k))
    (b_row_sup_ub : forall k,
       cnorm (cone_sup_ball (b^~ k) (b_row_ch k) (fun n => b_ub n k))
       <= 1)
    (b_row_sup_ch : forall k,
       cone_sup_ball (b^~ k) (b_row_ch k) (fun n => b_ub n k) <=p
       cone_sup_ball (b^~ k.+1) (b_row_ch k.+1) (fun n => b_ub n k.+1)) :
  cone_sup_ball
    (fun n => cone_sup_ball (b n) (b_col_ch n) (fun k => b_ub n k))
    b_col_sup_ch b_col_sup_ub =
  cone_sup_ball
    (fun k => cone_sup_ball (b^~ k) (b_row_ch k) (fun n => b_ub n k))
    b_row_sup_ch b_row_sup_ub.
Proof. exact: omega_general.cone_sup_ball_swap. Qed.

End LinhomSupCont.

(** ω-continuity of [linhom_sup_fun] — Paper §5.1.

    Given an increasing unit-ball chain [(x_k)] in [C] with image
    chain [(linhom_sup_fun (x_k))] also unit-ball and increasing,
    the pointwise sup commutes with [linhom_sup_fun]. *)
Lemma linhom_sup_fun_continuous : is_omega_continuous linhom_sup_fun.
Proof.
move=> x xch xub fxch fxub.
set xs := cone_sup_ball x xch xub.
have Hxs : cnorm xs <= 1 by exact: cone_sup_ball_norm.
have Hxk : forall k, cnorm (x k) <= 1 by exact: xub.
(* The doubly-indexed family. *)
pose b (n k : nat) : D := linhom_fun (u n) (x k).
have b_row_ch : forall k n, precone_le (b n k) (b n.+1 k).
  by move=> k n; exact: (linhom_le_pointwise (uch n) (x k)).
have b_col_ch : forall n k, precone_le (b n k) (b n k.+1).
  move=> n k.
  have Hlin := linhom_pre_linear (linhom_pre_of (u n)).
  exact: (linear_increasing Hlin) _ _ (xch k).
have b_ub : forall n k, cnorm (b n k) <= 1.
  by move=> n k; exact: linhom_sup_pw_ub1.
have b_col_sup_ub : forall n,
    cnorm (cone_sup_ball (b n) (b_col_ch n) (fun k => b_ub n k)) <= 1.
  by move=> n; exact: cone_sup_ball_norm.
have b_row_sup_ub : forall k,
    cnorm (cone_sup_ball (b^~ k) (b_row_ch k) (fun n => b_ub n k)) <= 1.
  by move=> k; exact: cone_sup_ball_norm.
have b_col_sup_ch : forall n,
    precone_le
      (cone_sup_ball (b n) (b_col_ch n) (fun k => b_ub n k))
      (cone_sup_ball (b n.+1) (b_col_ch n.+1) (fun k => b_ub n.+1 k)).
  move=> n; apply: cone_sup_ball_lub => k.
  apply: precone_le_trans (b_row_ch k n) _.
  exact: cone_sup_ball_ub.
have b_row_sup_ch : forall k,
    precone_le
      (cone_sup_ball (b^~ k) (b_row_ch k) (fun n => b_ub n k))
      (cone_sup_ball (b^~ k.+1) (b_row_ch k.+1) (fun n => b_ub n k.+1)).
  move=> k; apply: cone_sup_ball_lub => n.
  apply: precone_le_trans (b_col_ch n k) _.
  exact: cone_sup_ball_ub.
(* Step 1: For each n, by ω-continuity of u_n applied to the
   chain (x k), we have
   linhom_fun u_n xs = cone_sup_ball_k (linhom_fun u_n (x k))
                     = cone_sup_ball_k (b n k). *)
have un_xs_eq : forall n,
    linhom_fun (u n) xs =
    cone_sup_ball (b n) (b_col_ch n) (fun k => b_ub n k).
  move=> n.
  have Hcont_un := linhom_pre_continuous (linhom_pre_of (u n)).
  have := Hcont_un x xch xub (b_col_ch n) (fun k => b_ub n k).
  by rewrite /xs/b/=.
(* Step 2: For each k, linhom_sup_fun (x k) = cone_sup_ball_n (b n k). *)
have sup_xk_eq : forall k,
    linhom_sup_fun (x k) =
    cone_sup_ball (b^~ k) (b_row_ch k) (fun n => b_ub n k).
  move=> k.
  rewrite (linhom_sup_fun_unitE (Hxk k)) /linhom_sup_unit.
  have e1 : [eta linhom_sup_pw_chain (x k)] = b_row_ch k
    by exact: Prop_irrelevance.
  have e2 : linhom_sup_pw_ub1 (Hxk k) = (fun n => b_ub n k)
    by exact: Prop_irrelevance.
  by rewrite e1 e2.
(* Step 3: linhom_sup_fun xs = cone_sup_ball_n (linhom_fun u_n xs)
                              = cone_sup_ball_n (sup_k (b n k))
                              (by un_xs_eq, with Prop_irrelevance). *)
have LHS_eq :
    linhom_sup_fun xs =
    cone_sup_ball
      (fun n => cone_sup_ball (b n) (b_col_ch n) (fun k => b_ub n k))
      b_col_sup_ch b_col_sup_ub.
  rewrite (linhom_sup_fun_unitE Hxs) /linhom_sup_unit.
  (* The two cone_sup_balls have the same underlying function up to
     un_xs_eq, hence are equal by Prop_irrelevance + the equality of
     functions. *)
  apply: precone_le_anti.
  - apply: cone_sup_ball_lub => n /=.
    rewrite un_xs_eq.
    exact: cone_sup_ball_ub.
  - apply: cone_sup_ball_lub => n /=.
    rewrite -un_xs_eq.
    exact: cone_sup_ball_ub.
(* Step 4: cone_sup_ball (linhom_sup_fun \o x) fxch fxub
          = cone_sup_ball (k ↦ sup_n (b n k)) ... (by sup_xk_eq). *)
have RHS_eq :
    cone_sup_ball (linhom_sup_fun \o x) fxch fxub =
    cone_sup_ball
      (fun k => cone_sup_ball (b^~ k) (b_row_ch k) (fun n => b_ub n k))
      b_row_sup_ch b_row_sup_ub.
  apply: precone_le_anti.
  - apply: cone_sup_ball_lub => k /=.
    rewrite sup_xk_eq.
    exact: cone_sup_ball_ub.
  - apply: cone_sup_ball_lub => k /=.
    rewrite -sup_xk_eq.
    exact: cone_sup_ball_ub.
(* Step 5: the LHS-form and RHS-form are equal by sup-commutation. *)
rewrite LHS_eq RHS_eq.
exact: cone_sup_ball_swap.
Qed.

(** ** Path-preservation of [linhom_sup_fun] — Paper §5.1 (Step 2b)

    Given a measurable path [γ : ar_carrier X' -> C] with norm
    bound [M], we show that [r ↦ linhom_sup_fun (γ r)] is a
    measurable path in [D]:
    - Boundedness: [cnorm (linhom_sup_fun (γ r)) ≤ cnorm (γ r) ≤ M]
      via [linhom_sup_fun_norm_le].
    - Test-measurability: for every test [m : test_of Ar Y D] with
      [mcone_M Y m], the map [(s, r) ↦ m s (linhom_sup_fun (γ r))]
      is measurable. The key trick is the *uniform-scale rewrite*:
      with [S := M + 1] (positive), [γ r ∈ S * B_C], so
      [linhom_sup_fun (γ r) = S *: cone_sup_ball_n (linhom_fun u_n
      (S⁻¹ *: γ r))]. The map [(s, r) ↦ m s ...] becomes [S * sup_n
      m s (linhom_fun u_n (S⁻¹ *: γ r))]; each [u_n] preserves
      paths, scaling preserves paths, so each [(s, r) ↦ m s (...)]
      is measurable. The sup is then measurable via
      [measurable_fun_cvg]. *)

(** Auxiliary: scaling preserves measurable paths. *)
Lemma is_measurable_path_scale (X' : ar_obj Ar)
    (γ : ar_carrier Ar X' -> C) (s : {nonneg R}) :
  is_measurable_path γ ->
  is_measurable_path (fun r => precone_scale s (γ r)).
Proof.
move=> [[M HM] Hmeas]; split.
  exists (s%:num * M) => r.
  rewrite cone_normh.
  have sge0 : 0 <= s%:num by exact: nngnum_ge0.
  have [s0 | spos] := eqVneq s%:num 0.
    by rewrite s0 !mul0r.
  by rewrite ler_pM2l ?lt_def ?spos ?sge0 //; exact: HM.
move=> Y m mM.
have -> :
  (fun p : (ar_carrier Ar Y * ar_carrier Ar X')%type =>
    test_fun m p.1 (precone_scale s (γ p.2))) =
  (fun p : (ar_carrier Ar Y * ar_carrier Ar X')%type =>
    s%:num * test_fun m p.1 (γ p.2)).
  by apply: funext => p; rewrite test_linZ.
by apply: measurable_funM; [exact: measurable_cst | exact: Hmeas].
Qed.

(** Path-preservation of [linhom_sup_fun]. *)
Lemma linhom_sup_fun_pres_path (X' : ar_obj Ar)
    (γ : ar_carrier Ar X' -> C) :
  is_measurable_path γ ->
  is_measurable_path (fun r => linhom_sup_fun (γ r)).
Proof.
move=> Hγ.
have [[M HM] Hγ_meas] := Hγ.
have Mge0 : 0 <= M.
  have := HM (point _).
  by apply: le_trans; exact: cone_norm_ge0.
(* Uniform scale: S := M + 1, so S > 0 and ‖γ r‖/S ≤ 1. *)
have Sge0 : 0 <= M + 1.
  by apply: le_trans ler01 _; rewrite -[X in X <= _]add0r lerD2r.
pose S : {nonneg R} := NngNum Sge0.
have Spos : 0 < S%:num.
  by apply: lt_le_trans ltr01 _; rewrite -[X in X <= _]add0r lerD2r.
have S_num : S%:num = M + 1 by [].
have Sinv_ge0 : 0 <= (M + 1)^-1 by rewrite invr_ge0 ltW.
pose Sinv : {nonneg R} := NngNum Sinv_ge0.
have Sinv_num : Sinv%:num = (M + 1)^-1 by [].
have S_Sinv : S%:num * Sinv%:num = 1.
  by rewrite S_num Sinv_num mulfV// gt_eqF.
have Sinv_S : Sinv%:num * S%:num = 1.
  by rewrite S_num Sinv_num mulVf// gt_eqF.
(* The scaled path. *)
pose γs (r : ar_carrier Ar X') : C := precone_scale Sinv (γ r).
have Hγs_unit : forall r, cnorm (γs r) <= 1.
  move=> r; rewrite cone_normh /=.
  rewrite mulrC ler_pdivrMr // mul1r.
  apply: le_trans (HM r) _.
  by rewrite -[X in X <= _]addr0 lerD2l ler01.
have nng_inv_eq : nng_inv S = Sinv.
  by apply: val_inj => /=.
(* Reformulation of linhom_sup_fun on γ r via uniform scale.
   We avoid dependent-rewrite headaches by phrasing the inner sup
   directly at [γs r] (so the proof can use [Hγs_unit r]) and
   reusing [linhom_sup_fun_at_scale] with [Hxs := Hγs_unit r]
   after first rewriting [γ r] as [S *: γs r]. *)
have γ_eq_Sγs : forall r, γ r = precone_scale S (γs r).
  move=> r; rewrite /γs -precone_scale_A.
  have nng1 : (S%:num * Sinv%:num)%:nng = 1%:nng :> {nonneg R}.
    by apply: val_inj => /=.
  by rewrite nng1 precone_scale_1.
have lsfun_eq : forall r, linhom_sup_fun (γ r) =
    precone_scale S (linhom_sup_unit (Hγs_unit r)).
  move=> r.
  rewrite (γ_eq_Sγs r) linhom_sup_fun_linZ.
  congr precone_scale.
  exact: linhom_sup_fun_unitE.
split.
- (* Boundedness: ‖linhom_sup_fun (γ r)‖ ≤ ‖γ r‖ ≤ M. *)
  exists M => r.
  apply: le_trans (linhom_sup_fun_norm_le _) _.
  exact: HM.
- (* Test measurability via uniform-scale + sup-of-meas-fns. *)
  move=> Y m mM.
  have Hγs_path : is_measurable_path γs.
    exact: (is_measurable_path_scale Sinv Hγ).
  (* For each n, by path-preservation of u_n, the function
     (s, r) ↦ m s (u_n (γs r)) is measurable. We extract this
     directly to avoid canonical-structure inference issues. *)
  have un_γs_path : forall n,
      is_measurable_path (Ar:=Ar) (C:=D) (X:=X')
        (fun r => linhom_fun (u n) (γs r)).
    move=> n; exact: (linhom_pre_pres_path (linhom_pre_of (u n))).
  pose h (n : nat) (p : (ar_carrier Ar Y * ar_carrier Ar X')%type) : R :=
    test_fun m p.1 (linhom_fun (u n) (γs p.2)).
  (* Pointwise convergence of (h ^~ p) to test m p.1 of
     linhom_sup_unit (Hγs_unit p.2). *)
  pose b (n : nat) (r : ar_carrier Ar X') : D := linhom_fun (u n) (γs r).
  have b_ch : forall r n, precone_le (b n r) (b n.+1 r).
    by move=> r n; exact: (linhom_le_pointwise (uch n) (γs r)).
  have b_ub : forall r n, cnorm (b n r) <= 1.
    move=> r n; rewrite /b.
    apply: le_trans (linhom_norm_sup_ub (u n) (γs r) (Hγs_unit r)) _.
    exact: ub1.
  have h_ndec : forall p, nondecreasing_seq (h ^~ p).
    move=> p; apply/nondecreasing_seqP => n.
    rewrite /h.
    have Hpw := b_ch p.2 n.
    case: Hpw => [z Hz].
    by rewrite -/(b n p.2) -/(b n.+1 p.2) [in leRHS]Hz test_linD lerDl;
       exact: test_ge0.
  have h_ub : forall p, has_ubound (range (h ^~ p)).
    move=> p; exists 1 => _ [n _ <-].
    rewrite /h; apply: test_le1.
    apply: le_trans
      (linhom_norm_sup_ub (u n) (γs p.2) (Hγs_unit p.2)) _.
    exact: ub1.
  have h_cvg : forall p, (h ^~ p : nat -> R)
      @ \oo --> (sup (range (h ^~ p)) : R).
    by move=> p; apply: nondecreasing_cvgn;
      [exact: h_ndec | exact: h_ub].
  (* The target: test_fun m s (linhom_sup_unit (Hγs_unit r)) =
     sup_n h n (s, r). *)
  have target_eq : forall p,
      test_fun m p.1 (linhom_sup_unit (Hγs_unit p.2)) =
      sup (range (h ^~ p)).
    move=> p; apply: le_anti; apply/andP; split.
    + (* ≤: by test_cont on the chain (b ^~ p.2). *)
      rewrite /linhom_sup_unit.
      have e1 : [eta linhom_sup_pw_chain (γs p.2)] = b_ch p.2.
        exact: Prop_irrelevance.
      have e2 : linhom_sup_pw_ub1 (Hγs_unit p.2) = b_ub p.2.
        exact: Prop_irrelevance.
      rewrite e1 e2.
      apply: (@test_cont _ _ _ _ _ p.1 (b ^~ p.2) (b_ch p.2) (b_ub p.2)
        (sup (range (h ^~ p)))) => n.
      have hsup : has_sup (range (h ^~ p)).
        by split; [by exists (h 0%N p), 0%N | exact: h_ub].
      move/ubP/(_ (h n p)) : (sup_upper_bound hsup); apply.
      by exists n.
    + apply: ge_sup; first by exists (h 0%N p), 0%N.
      move=> _ [n _ <-]; rewrite /h.
      have Hub : precone_le (b n p.2)
                            (linhom_sup_unit (Hγs_unit p.2)).
        rewrite /linhom_sup_unit /b.
        have e1 : [eta linhom_sup_pw_chain (γs p.2)] = b_ch p.2.
          exact: Prop_irrelevance.
        have e2 : linhom_sup_pw_ub1 (Hγs_unit p.2) = b_ub p.2.
          exact: Prop_irrelevance.
        rewrite e1 e2.
        exact: cone_sup_ball_ub.
      case: Hub => [z ->].
      rewrite test_linD lerDl; exact: test_ge0.
  (* Now we put it all together. The test of linhom_sup_fun (γ r) is
     S * test_fun m s (linhom_sup_unit ...) by test_linZ + lsfun_eq. *)
  have target_full : forall p,
      test_fun m p.1 (linhom_sup_fun (γ p.2)) =
      S%:num * sup (range (h ^~ p)).
    move=> p; rewrite (lsfun_eq p.2) test_linZ.
    by rewrite -target_eq.
  have -> : (fun p : ar_carrier Ar Y * ar_carrier Ar X' =>
              test_fun m p.1 (linhom_sup_fun (γ p.2))) =
            (fun p : ar_carrier Ar Y * ar_carrier Ar X' =>
              S%:num * sup [set h i p | i in [set: nat]]).
    by apply: funext => p; exact: target_full.
  apply: measurable_funM; first exact: measurable_cst.
  apply: (measurable_fun_cvg (h := h)).
  - by move=> n; have [_ Hmeas] := un_γs_path n; exact: Hmeas.
  - by move=> p _; exact: h_cvg.
Qed.

(** ** Auxiliary: norm bound on linhom application at arbitrary point.

    For an [f : linhom_car Ar C D] with [linhom_norm f ≤ K] and any
    [x : C], [cnorm (linhom_fun f x) ≤ K * cnorm x]. Derives from
    [linhom_norm_sup_ub] by scaling [x] into the unit ball. *)
Lemma linhom_norm_apply_le
    (f : linhom_car Ar C D) (K : R) (HK : linhom_norm f <= K) (x : C) :
  cnorm (linhom_fun f x) <= K * cnorm x.
Proof.
have x_ge0 : 0 <= cnorm x by exact: cone_norm_ge0.
have Kge0 : 0 <= K.
  apply: le_trans HK; exact: linhom_norm_ge0.
have [x0|xpos] := eqVneq (cnorm x) 0.
  have x_is0 : x = precone_zero by apply: cone_normz.
  rewrite x0 mulr0.
  rewrite x_is0.
  case: (linhom_pre_linear (linhom_pre_of f)) => H0 _ _.
  by rewrite /linhom_fun H0 cone_norm0.
have xpos' : 0 < cnorm x.
  by rewrite lt_def xpos x_ge0.
have cinv_ge0 : 0 <= (cnorm x)^-1 by rewrite invr_ge0 ltW.
pose cinv : {nonneg R} := NngNum cinv_ge0.
have Hxinv : cnorm (precone_scale cinv x) <= 1.
  rewrite cone_normh /=.
  by rewrite mulVf// gt_eqF.
(* cnorm (f x) = cnorm x * cnorm (f (cinv * x)) ≤ cnorm x * K *)
pose c : {nonneg R} := NngNum x_ge0.
have [_ _ HfZ] := linhom_pre_linear (linhom_pre_of f).
have step : cnorm (linhom_fun f x) =
            c%:num * cnorm (linhom_fun f (precone_scale cinv x)).
  have linZ_x_to_cinv :
      linhom_fun f x = precone_scale c (linhom_fun f (precone_scale cinv x)).
    rewrite -[in LHS](_ : precone_scale c (precone_scale cinv x) = x);
      last first.
      rewrite -precone_scale_A.
      have nng_eq : forall (a b : {nonneg R}), a%:num = b%:num -> a = b.
        by move=> a b /val_inj.
      rewrite (_ : (c%:num * cinv%:num)%:nng = 1%:nng); last first.
        by apply: nng_eq => /=; rewrite mulfV// gt_eqF.
      by rewrite precone_scale_1.
    by rewrite /linhom_fun; exact: HfZ.
  by rewrite linZ_x_to_cinv cone_normh.
rewrite step.
have step2 : cnorm (linhom_fun f (precone_scale cinv x)) <= K.
  apply: le_trans HK.
  exact: linhom_norm_sup_ub.
rewrite [K * _]mulrC.
have c_eq : c%:num = cnorm x by [].
rewrite c_eq.
apply: ler_pM.
- exact: cone_norm_ge0.
- exact: cone_norm_ge0.
- exact: lexx.
- exact: step2.
Qed.

(** ** Integral-preservation of [linhom_sup_fun] — Paper §5.1 (Step 2c)

    For [β : ar_carrier X' -> C] measurable and [µ] a finite measure,
    we show [linhom_sup_fun (∫β) = ∫(linhom_sup_fun ∘ β)]. The proof:
    by uniqueness of integral, reduce to verifying the Pettis equation
    for [linhom_sup_fun (∫β)] against the integral of the linhom_sup
    chain. Per-test computation uses [test_cont] + monotone-
    convergence. *)

(** Auxiliary: test of sup equals R-sup of tests, for any [x : C]. *)
Lemma linhom_sup_fun_test_sup
    (Y : ar_obj Ar) (m : test_of Ar Y D) (s : ar_carrier Ar Y) (x : C) :
  test_fun m s (linhom_sup_fun x) =
  sup [set test_fun m s (linhom_fun (u n) x) | n in [set: nat]].
Proof.
have S_pos : 0 < cnorm x + 1 by exact: cnorm_succ_pos.
have S_ge0 : 0 <= cnorm x + 1 by exact: ltW.
pose S : {nonneg R} := NngNum S_ge0.
have Sinv_ge0 : 0 <= (cnorm x + 1)^-1 by rewrite invr_ge0 ltW.
pose Sinv : {nonneg R} := NngNum Sinv_ge0.
have nng_inv_eq : nng_inv S = Sinv.
  by apply: val_inj => /=.
have Hx : cnorm (precone_scale (nng_inv S) x) <= 1.
  rewrite cone_normh /=.
  rewrite mulrC ler_pdivrMr // mul1r.
  by rewrite -[X in X <= _]addr0 lerD2l ler01.
have Spos : 0 < S%:num by exact: S_pos.
(* Step A: linhom_sup_fun x = S *: linhom_sup_unit Hx. *)
rewrite (linhom_sup_fun_at_scale Spos Hx) test_linZ.
(* Step B: chain at scaled point. *)
pose b' (n : nat) : D := linhom_fun (u n) (precone_scale (nng_inv S) x).
have b'_ch : forall n, precone_le (b' n) (b' n.+1).
  by move=> n; exact: linhom_sup_pw_chain.
have b'_ub : forall n, cnorm (b' n) <= 1.
  by move=> n; exact: linhom_sup_pw_ub1.
pose h' (n : nat) : R := test_fun m s (b' n).
have h'_ndec : nondecreasing_seq h'.
  apply/nondecreasing_seqP => n.
  rewrite /h'.
  have := b'_ch n.
  rewrite /b' => -[z Hz].
  by rewrite [in leRHS]Hz test_linD lerDl; exact: test_ge0.
have h'_ub : has_ubound (range h').
  exists 1 => _ [n _ <-]; rewrite /h'.
  by apply: test_le1; exact: b'_ub.
have hsup' : has_sup (range h').
  by split; [exists (h' 0%N), 0%N => // | exact: h'_ub].
have inner_eq :
    test_fun m s (linhom_sup_unit Hx) = sup (range h').
  rewrite /linhom_sup_unit.
  have e1 : [eta linhom_sup_pw_chain (precone_scale (nng_inv S) x)]
            = b'_ch by exact: Prop_irrelevance.
  have e2 : linhom_sup_pw_ub1 Hx = b'_ub by exact: Prop_irrelevance.
  rewrite e1 e2.
  apply: le_anti; apply/andP; split.
  - apply: (@test_cont _ _ _ _ _ s b' b'_ch b'_ub (sup (range h'))) => n.
    move/ubP/(_ (h' n)) : (sup_upper_bound hsup'); apply.
    by exists n.
  - apply: ge_sup; first by exists (h' 0%N), 0%N.
    move=> _ [n _ <-]; rewrite /h' /b'.
    have Hub : precone_le (b' n)
              (cone_sup_ball b' b'_ch b'_ub).
      exact: cone_sup_ball_ub.
    case: Hub => [z ->].
    rewrite test_linD lerDl; exact: test_ge0.
rewrite inner_eq.
(* Step C: relate b' to (linhom_fun u_n x) via Sinv-scaling. *)
have linZ_b' : forall n,
    test_fun m s (b' n) = Sinv%:num * test_fun m s (linhom_fun (u n) x).
  move=> n; rewrite /b'.
  have [_ _ HfZ] := linhom_pre_linear (linhom_pre_of (u n)).
  rewrite /linhom_fun nng_inv_eq /= HfZ.
  by rewrite test_linZ.
(* Step D: sup (range h') = Sinv * sup_n (test_fun m s (u_n x)). *)
pose h'' (n : nat) : R := test_fun m s (linhom_fun (u n) x).
have h''_ndec : nondecreasing_seq h''.
  apply/nondecreasing_seqP => n.
  rewrite /h''.
  have Hpw : precone_le (linhom_fun (u n) x) (linhom_fun (u n.+1) x).
    exact: linhom_le_pointwise.
  case: Hpw => [z Hz].
  by rewrite [in leRHS]Hz test_linD lerDl; exact: test_ge0.
have h''_ub : has_ubound (range h'').
  exists (cnorm x) => _ [n _ <-]; rewrite /h''.
  apply: le_trans (test_norm_le _ _ _) _.
  apply: le_trans (linhom_norm_apply_le _ _) _; first exact: ub1.
  by rewrite mul1r.
have hsup'' : has_sup (range h'').
  by split; [exists (h'' 0%N), 0%N => // | exact: h''_ub].
(* sup (range h') = Sinv%:num * sup (range h''). *)
have h_range_eq :
    sup (range h') = Sinv%:num * sup (range h'').
  apply: le_anti; apply/andP; split.
  - apply: ge_sup; first by case: hsup'.
    move=> y [n _ <-].
    rewrite /h' linZ_b'.
    apply: ler_pM; [exact: nngnum_ge0|exact: test_ge0|exact: lexx|].
    by move/ubP/(_ (h'' n)) : (sup_upper_bound hsup''); apply; exists n.
  - rewrite -ler_pdivlMl /=; last first.
      by rewrite invr_gt0.
    have inv_eq : Sinv%:num^-1 = S%:num.
      by rewrite /= invrK.
    rewrite inv_eq.
    apply: ge_sup; first by case: hsup''.
    move=> y [n _ <-].
    rewrite /h''.
    have heq : test_fun m s (linhom_fun (u n) x)
             = S%:num * (Sinv%:num * test_fun m s (linhom_fun (u n) x)).
      rewrite mulrA mulfV ?mul1r//.
      by rewrite gt_eqF.
    rewrite heq.
    apply: ler_pM; [exact: nngnum_ge0|by rewrite mulr_ge0 ?test_ge0|
                    exact: lexx|].
    rewrite -linZ_b'.
    by move/ubP/(_ (h' n)) : (sup_upper_bound hsup'); apply; exists n.
rewrite h_range_eq.
by rewrite mulrA mulfV ?gt_eqF // mul1r.
Qed.

(** ** Integral-preservation of [linhom_sup_fun] — Paper §5.1.

    Strategy mirrors [integral_omega_cont_path] from
    [icone_integral.v]: by (Mssep), it suffices to check the Pettis
    equation at every test [m] of arity 0. By [linhom_sup_fun_test_sup],
    both sides reduce to the same [sup] over [n], identified via
    monotone convergence on ereal-valued integrals. *)

Local Open Scope ereal_scope.

Lemma linhom_sup_fun_pres_int
    (X' : ar_obj Ar)
    (β : ar_carrier Ar X' -> C) (Hβ : is_measurable_path β)
    (µ : fmeas R (ar_carrier Ar X')) :
  linhom_sup_fun (icone_integral β Hβ µ) =
  icone_integral (fun r => linhom_sup_fun (β r))
    (linhom_sup_fun_pres_path Hβ) µ.
Proof.
apply: icone_integral_eqP => m mM s0.
(* LHS rewrite: m s0 (linhom_sup_fun X) = sup_n m s0 (u_n X). *)
rewrite (linhom_sup_fun_test_sup m s0 (icone_integral β Hβ µ)).
(* Helper: each u_n preserves integrals, so
   m s0 (u_n (∫β)) = fine (∫ m s0 (u_n (β r)) dµ). *)
have un_pet : forall n,
    test_fun m s0 (linhom_fun (u n) (icone_integral β Hβ µ)) =
    fine (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X'])
            (test_fun m s0 (linhom_fun (u n) (β r)))%:E).
  move=> n.
  have Hp := linhom_pres_int (u n) X' β Hβ µ.
  rewrite /linhom_fun Hp.
  exact: (icone_integralP _
    (linhom_pre_pres_path (linhom_pre_of (u n)) X' β Hβ) µ m mM s0).
(* Build the ereal chain un_n and its sup fsup. *)
pose un_e (n : nat) (r : ar_carrier Ar X') : \bar R :=
  (test_fun m s0 (linhom_fun (u n) (β r)))%:E.
pose fsup_e (r : ar_carrier Ar X') : \bar R :=
  (test_fun m s0 (linhom_sup_fun (β r)))%:E.
have un_meas : forall n,
    measurable_fun setT (un_e n).
  move=> n.
  apply/measurable_EFinP.
  have Hun_path :=
    linhom_pre_pres_path (linhom_pre_of (u n)) X' β Hβ.
  exact: (measurable_test_path_section mM Hun_path s0).
have un_ge0 : forall n r, 0 <= un_e n r.
  by move=> n r; rewrite /un_e lee_fin; exact: test_ge0.
have un_homo : forall r,
    {homo (un_e^~ r) : n m0 / (n <= m0)%N >-> (n <= m0)%E}.
  move=> r; apply/nondecreasing_seqP => n.
  rewrite /un_e lee_fin.
  apply: test_fun_le; exact: linhom_le_pointwise.
(* Pointwise limit/sup identity: lim_n un_e n r = fsup_e r. *)
have un_cvg_R : forall r,
  (fun n => test_fun m s0 (linhom_fun (u n) (β r))) x @[x --> \oo] -->
  (test_fun m s0 (linhom_sup_fun (β r)) : R^o).
  move=> r.
  pose v (n : nat) := test_fun m s0 (linhom_fun (u n) (β r)).
  have nd_v : nondecreasing_seq v.
    apply/nondecreasing_seqP => n; rewrite /v.
    apply: test_fun_le; exact: linhom_le_pointwise.
  have ub_v : has_ubound (range v).
    exists (cnorm (β r)) => _ [n _ <-]; rewrite /v.
    apply: le_trans (test_norm_le _ _ _) _.
    apply: le_trans (linhom_norm_apply_le _ _) _; first exact: ub1.
    by rewrite mul1r.
  have sup_eq : sup (range v) = test_fun m s0 (linhom_sup_fun (β r)).
    by rewrite -(linhom_sup_fun_test_sup m s0 (β r)).
  rewrite -sup_eq.
  exact: nondecreasing_cvgn.
have un_cvg : forall r, (un_e^~ r) x @[x --> \oo] --> fsup_e r.
  move=> r; rewrite /un_e /fsup_e.
  apply: cvg_EFin; first by apply: nearW => n; rewrite fin_numE.
  exact: un_cvg_R.
have un_lim : forall r, limn (un_e^~ r) = fsup_e r.
  by move=> r; apply/cvg_lim => //; exact: ereal_hausdorff.
(* MCT: ∫ fsup_e = lim_n ∫ un_e n. *)
have MCT :
    \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X']) fsup_e r =
    limn (fun n => \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X'])
                       un_e n r).
  have HMC :=
    monotone_convergence (fmeas_mu µ) (D := [set: ar_carrier Ar X'])
      measurableT un_meas (fun n r _ => un_ge0 n r)
      (fun r _ => un_homo r).
  rewrite -HMC; apply: eq_integral => r _; by rewrite -un_lim.
(* Finiteness of each ∫ un_e n. *)
have un_bound : forall (n : nat) (r : ar_carrier Ar X'),
    un_e n r <= (cnorm (β r))%:E.
  move=> n r; rewrite /un_e lee_fin.
  apply: le_trans (test_norm_le _ _ _) _.
  apply: le_trans (linhom_norm_apply_le _ _) _; first exact: ub1.
  by rewrite mul1r.
have [[Mβ HMβ] _] := Hβ.
have un_bound_M : forall n r, un_e n r <= Mβ%:E.
  move=> n r.
  apply: le_trans (un_bound n r) _; rewrite lee_fin; exact: HMβ.
have intGe0_un : forall n,
    0 <= \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X']) un_e n r.
  by move=> n; apply: integral_ge0 => r _; exact: un_ge0.
have intGe0_sup :
    0 <= \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X']) fsup_e r.
  apply: integral_ge0 => r _; rewrite /fsup_e lee_fin.
  exact: test_ge0.
have fmeas_setT_fin : fmeas_mu µ [set: ar_carrier Ar X'] \is a fin_num.
  exact: fmeas_setT_fin.
have un_int_fin : forall n,
    \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X']) un_e n r \is a fin_num.
  move=> n.
  rewrite ge0_fin_numE//.
  apply: (@le_lt_trans _ _
    (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X']) Mβ%:E)); last first.
    rewrite (_ : (fun _ => Mβ%:E) = cst Mβ%:E)//.
    rewrite integral_cst//.
    by rewrite ltey_eq fin_numM.
  apply: (@ge0_le_integral _ _ R (fmeas_mu µ) _ measurableT
            (un_e n) (cst Mβ%:E)).
    by move=> r _; exact: un_ge0.
    exact: un_meas.
    by apply: measurable_cst.
  by move=> r _; exact: un_bound_M.
have meas_fsup :
    measurable_fun setT fsup_e.
  apply/measurable_EFinP.
  exact: (measurable_test_path_section mM
            (linhom_sup_fun_pres_path Hβ) s0).
have fsup_bound : forall r, fsup_e r <= Mβ%:E.
  move=> r; rewrite /fsup_e lee_fin.
  apply: le_trans (test_norm_le _ _ _) _.
  apply: le_trans (linhom_sup_fun_norm_le _) _.
  exact: HMβ.
have fsup_int_fin :
    \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X']) fsup_e r \is a fin_num.
  rewrite ge0_fin_numE//.
  apply: (@le_lt_trans _ _
    (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X']) Mβ%:E)); last first.
    rewrite (_ : (fun _ => Mβ%:E) = cst Mβ%:E)//.
    rewrite integral_cst//.
    by rewrite ltey_eq fin_numM.
  apply: (@ge0_le_integral _ _ R (fmeas_mu µ) _ measurableT
            fsup_e (cst Mβ%:E)).
    by move=> r _; rewrite /fsup_e lee_fin; exact: test_ge0.
    exact: meas_fsup.
    by apply: measurable_cst.
  by move=> r _; exact: fsup_bound.
(* Now relate sup_n to fine ∫. *)
pose hint (n : nat) := test_fun m s0 (linhom_fun (u n) (icone_integral β Hβ µ)).
have nd_hint : nondecreasing_seq hint.
  apply/nondecreasing_seqP => n; rewrite /hint.
  apply: test_fun_le.
  exact: linhom_le_pointwise.
have ub_hint : has_ubound (range hint).
  exists (cnorm (icone_integral β Hβ µ)) => _ [n _ <-]; rewrite /hint.
  apply: le_trans (test_norm_le _ _ _) _.
  apply: le_trans (linhom_norm_apply_le _ _) _; first exact: ub1.
  by rewrite mul1r.
have hint_cvg :
    hint x @[x --> \oo] -->
    (fine (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X']) fsup_e r) : R^o).
  have HCMu :=
    cvg_monotone_convergence (D := [set: ar_carrier Ar X'])
      (mu := fmeas_mu µ) measurableT un_meas
      (fun n r _ => un_ge0 n r) (fun r _ => un_homo r).
  have HE :
    \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X'])
        (fun x : ar_carrier Ar X' => limn (un_e^~ x)) r =
    \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X']) fsup_e r.
    by apply: eq_integral => r _; rewrite -un_lim.
  have e_cvg :
    (fun n => \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X']) un_e n r)
      x @[x --> \oo] -->
    (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X']) fsup_e r)%E.
    by rewrite -HE.
  have HEFin :
    \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X']) fsup_e r =
    (fine (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X']) fsup_e r))%:E.
    by rewrite fineK.
  rewrite HEFin in e_cvg.
  have fcvg : (fun n =>
      fine (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X']) un_e n r)) x
    @[x --> \oo] --> (fine (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X'])
                            fsup_e r) : R^o).
    by have := fine_cvg e_cvg; exact.
  have heq : (fun n =>
      fine (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X']) un_e n r))
    = hint.
    by apply: funext => n; rewrite /hint un_pet.
  by rewrite heq in fcvg; exact: fcvg.
have hint_sup_eq :
    sup (range hint) =
    fine (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X']) fsup_e r).
  have nd_cvg := nondecreasing_cvgn nd_hint ub_hint.
  exact: (@cvg_unique R^o (@Rhausdorff R) _ _ _ _ nd_cvg hint_cvg).
by rewrite -hint_sup_eq.
Qed.

End LinhomSupBall.

(** ** Packaging the sup-ball as a [linhom_car] — Paper §5.1

    The constructed [linhom_sup_fun] together with the proofs of
    linearity, ω-continuity, boundedness, path-preservation, and
    integral-preservation packages into a [linhom_car] element.
    Combined with the three sup-ball properties below, this yields
    the [isCone] HB instance on [linhom_car Ar C D]. *)

Section LinhomSupPack.
Variables (R : realType) (Ar : MeasSubcat R).
Variables C D : ICone.type Ar.

Variable u : nat -> linhom_car Ar C D.
Hypothesis uch : forall n, precone_le (u n) (u n.+1).
Hypothesis ub1 : forall n, linhom_norm (u n) <= 1.

(** Pre-carrier: linearity from lin0/linD/linZ, ω-cont from
    [linhom_sup_fun_continuous], boundedness from
    [linhom_sup_fun_bounded], path-preservation from
    [linhom_sup_fun_pres_path]. *)
Definition linhom_sup_ball_pre : linhom_pre Ar C D :=
  MkLinhomPre (@linhom_sup_fun R Ar C D u uch ub1)
    (IsLinear
       (@linhom_sup_fun_lin0 R Ar C D u uch ub1)
       (@linhom_sup_fun_linD R Ar C D u uch ub1)
       (@linhom_sup_fun_linZ R Ar C D u uch ub1))
    (@linhom_sup_fun_continuous R Ar C D u uch ub1)
    (@linhom_sup_fun_bounded R Ar C D u uch ub1)
    (@linhom_sup_fun_pres_path R Ar C D u uch ub1).

(** Full [linhom_car]: adds integral preservation. *)
Definition linhom_sup_ball : linhom_car Ar C D :=
  MkLinhom linhom_sup_ball_pre
    (linhom_sup_fun_pres_int uch ub1).

(** Norm bound: the operator norm of [linhom_sup_ball] is ≤ 1.
    Direct from [linhom_sup_fun_norm_le] (pointwise bound) and the
    [linhom_norm_sup_lub] property of [linhom_norm]. *)
Lemma linhom_sup_ball_norm : linhom_norm linhom_sup_ball <= 1.
Proof.
apply: linhom_norm_sup_lub => x Hx.
apply: le_trans (linhom_sup_fun_norm_le uch ub1 x) Hx.
Qed.

End LinhomSupPack.

Arguments linhom_sup_ball {R Ar C D} u uch ub1.
Arguments linhom_sup_ball_norm {R Ar C D} u uch ub1.

(** ** The difference of two linhoms — Paper §5.1 (Normc) prerequisite

    Given [u v : linhom_car] with a pointwise [precone_le u v]
    witnessed by a per-[x] family [Hle], build the "difference"
    [linhom_diff u v Hle] as a full [linhom_car] satisfying
    [v x = u x + (linhom_diff u v Hle) x]. The construction uses
    classical choice ([cid]) for the per-[x] witness and discharges
    each [linhom_car] field by *cancellation in D* (precone_cancel /
    cone_normp / integral additivity).

    This is the key ingredient for [linhom_sup_ball_ub] /
    [linhom_sup_ball_lub] and, ultimately, the [isCone] HB instance
    on [linhom_car]. *)
Section LinhomDiff.
Variables (R : realType) (Ar : MeasSubcat R).
Variables C D : ICone.type Ar.

Variables u v : linhom_car Ar C D.
Hypothesis Hle : forall x : C,
  exists z : D, linhom_fun v x = precone_add (linhom_fun u x) z.

(** The pointwise witness function. *)
Definition linhom_diff_fun (x : C) : D := projT1 (cid (Hle x)).

(** Defining equation: [v x = u x + (linhom_diff_fun x)]. *)
Lemma linhom_diff_E (x : C) :
  linhom_fun v x =
    precone_add (linhom_fun u x) (linhom_diff_fun x).
Proof. exact: projT2 (cid (Hle x)). Qed.

(** Convenience: [(u, v)] linearity accessors. *)
Let v_lin0 : linhom_fun v precone_zero = precone_zero.
Proof. by have [Hl _ _] := linhom_pre_linear v; exact: Hl. Qed.
Let u_lin0 : linhom_fun u precone_zero = precone_zero.
Proof. by have [Hl _ _] := linhom_pre_linear u; exact: Hl. Qed.
Let v_linD x y :
  linhom_fun v (precone_add x y) =
  precone_add (linhom_fun v x) (linhom_fun v y).
Proof. by have [_ Hl _] := linhom_pre_linear v; exact: Hl. Qed.
Let u_linD x y :
  linhom_fun u (precone_add x y) =
  precone_add (linhom_fun u x) (linhom_fun u y).
Proof. by have [_ Hl _] := linhom_pre_linear u; exact: Hl. Qed.
Let v_linZ r x :
  linhom_fun v (precone_scale r x) = precone_scale r (linhom_fun v x).
Proof. by have [_ _ Hl] := linhom_pre_linear v; exact: Hl. Qed.
Let u_linZ r x :
  linhom_fun u (precone_scale r x) = precone_scale r (linhom_fun u x).
Proof. by have [_ _ Hl] := linhom_pre_linear u; exact: Hl. Qed.

(** Linearity: [linhom_diff_fun 0 = 0]. *)
Lemma linhom_diff_lin0 : linhom_diff_fun precone_zero = precone_zero.
Proof.
have HE := linhom_diff_E precone_zero.
rewrite v_lin0 u_lin0 in HE.
(* HE : 0 = 0 + linhom_diff_fun 0 *)
rewrite precone_add0 in HE.
by rewrite -HE.
Qed.

(** Linearity: [linhom_diff_fun (x + y) = linhom_diff_fun x +
    linhom_diff_fun y]. By cancellation: [u(x+y) + w(x+y) = v(x+y) =
    v(x) + v(y) = u(x) + w(x) + u(y) + w(y) = u(x+y) + (w(x) +
    w(y))]. *)
Lemma linhom_diff_linD x y :
  linhom_diff_fun (precone_add x y) =
  precone_add (linhom_diff_fun x) (linhom_diff_fun y).
Proof.
have HE := linhom_diff_E (precone_add x y).
have HEx := linhom_diff_E x.
have HEy := linhom_diff_E y.
rewrite v_linD HEx HEy u_linD in HE.
(* HE : u(x+y) + (w(x+y)) = (u x + w x) + (u y + w y) *)
(* RHS rearranges to u(x+y) + (w x + w y) via comm/assoc *)
have HRHS : precone_add (precone_add (linhom_fun u x) (linhom_diff_fun x))
              (precone_add (linhom_fun u y) (linhom_diff_fun y)) =
            precone_add (linhom_fun u (precone_add x y))
              (precone_add (linhom_diff_fun x) (linhom_diff_fun y)).
  rewrite u_linD.
  rewrite -2!precone_addA; congr precone_add.
  rewrite precone_addA (precone_addC _ (linhom_fun u y)) -precone_addA.
  by [].
rewrite HRHS in HE.
rewrite -u_linD in HE.
by symmetry; apply: precone_cancel HE.
Qed.

(** Linearity: [linhom_diff_fun (r *: x) = r *: linhom_diff_fun x]. *)
Lemma linhom_diff_linZ (r : {nonneg R}) x :
  linhom_diff_fun (precone_scale r x) =
  precone_scale r (linhom_diff_fun x).
Proof.
have HE := linhom_diff_E (precone_scale r x).
have HEx := linhom_diff_E x.
rewrite v_linZ HEx u_linZ in HE.
(* HE : r *: (u x + w x) = r *: u x + w(r *: x) *)
rewrite precone_scale_DAr in HE.
(* HE : r *: u x + r *: w x = r *: u x + w(r *: x) *)
by symmetry; apply: precone_cancel HE.
Qed.

(** [linhom_diff_fun] is linear (packaged). *)
Lemma linhom_diff_linear : is_linear linhom_diff_fun.
Proof.
exact: (IsLinear linhom_diff_lin0 linhom_diff_linD linhom_diff_linZ).
Qed.

End LinhomDiff.

Arguments linhom_diff_fun {R Ar C D u v} Hle.
Arguments linhom_diff_E {R Ar C D u v} Hle.
Arguments linhom_diff_linear {R Ar C D u v} Hle.

(** ** Remaining [linhom_car] fields for the difference — Paper §5.1

    Building on [linhom_diff_fun] / [linhom_diff_linear] from
    [LinhomDiff], we now discharge the four remaining fields of the
    [linhom_car] record on the difference
    [w x := linhom_diff_fun Hle x]:

    - boundedness ([linhom_diff_bounded]) — via
      [precone_le (w x) (v x)] (witness [u x] from [precone_addC]
      on [linhom_diff_E]) and [cone_normp] + [linhom_norm_sup_ub].
    - ω-continuity ([linhom_diff_continuous]) — by [v_cont],
      [u_cont] applied to the chain [x_n] (whose images stay in
      the unit ball under the auxiliary hypothesis
      [linhom_norm v <= 1]), [cone_sup_ball_addD], and
      [precone_cancel].
    - path-preservation ([linhom_diff_pres_path]) — subtract the
      measurable test of [u ∘ γ] from the measurable test of [v ∘
      γ], rewriting
      [test_fun m s (w (γ r)) = test_fun m s (v (γ r)) -
                                test_fun m s (u (γ r))]
      via [test_linD] + cancellation in [R].
    - integral-preservation ([linhom_diff_pres_int]) — by
      [linhom_pres_int] on [u] and [v], pointwise [linhom_diff_E],
      path-additivity [path_integral_eq_addB], and cancellation
      [precone_cancel] in [D].

    For ω-continuity we require the auxiliary hypothesis
    [linhom_norm v <= 1]; this is automatic at the call sites
    (chain of unit-norm linhoms with [linhom_sup_ball] as [v]).
    [linhom_norm u <= 1] follows from [Hle] and [linhom_norm v <= 1]
    via [linhom_norm_sup_lub] + [cone_normp]. *)

Section LinhomDiffPack.
Variables (R : realType) (Ar : MeasSubcat R).
Variables C D : ICone.type Ar.

Variables u v : linhom_car Ar C D.
Hypothesis Hle : forall x : C,
  exists z : D, linhom_fun v x = precone_add (linhom_fun u x) z.
Hypothesis Hv_le1 : linhom_norm v <= 1.

(** Local notation: [w x := linhom_diff_fun Hle x]. *)
Let w (x : C) : D := linhom_diff_fun Hle x.

Let w_E (x : C) :
  linhom_fun v x = precone_add (linhom_fun u x) (w x).
Proof. exact: linhom_diff_E. Qed.

(** Pointwise [≤p]: [w x ≤p v x] in [D], witnessed by [u x] via
    [precone_addC] on [w_E]. *)
Let w_le_v (x : C) : precone_le (w x) (linhom_fun v x).
Proof.
exists (linhom_fun u x); rewrite precone_addC; exact: w_E.
Qed.

(** Pointwise [≤p]: [u x ≤p v x] in [D], witnessed by [w x]. *)
Let u_le_v (x : C) : precone_le (linhom_fun u x) (linhom_fun v x).
Proof. exists (w x); exact: w_E. Qed.

(** Norm bound: [‖u‖ ≤ ‖v‖ ≤ 1]. *)
Let Hu_le1 : linhom_norm u <= 1.
Proof.
apply: le_trans Hv_le1.
apply: linhom_norm_sup_lub => x Hx.
have H1 := @cone_normp _ _ _ _ (u_le_v x).
exact: le_trans H1 (linhom_norm_sup_ub v x Hx).
Qed.

(** Paper §5.1: boundedness of [w] — Step 1a. *)
Lemma linhom_diff_bounded :
  exists M : R, forall x : C, cnorm x <= 1 ->
    cnorm (w x) <= M.
Proof.
exists (linhom_norm v) => x Hx.
have H1 := @cone_normp _ _ _ _ (w_le_v x).
exact: le_trans H1 (linhom_norm_sup_ub v x Hx).
Qed.

(** Paper §5.1: ω-continuity of [w] — Step 1b.

    Strategy: at the chain [x_n] with unit-ball bounds:
    - [u_cont x_n], [v_cont x_n] both apply since [‖u(x_n)‖ ≤ ‖u‖
      ≤ 1] and similarly for [v].
    - By [cone_sup_ball_addD] on chains [(u(x_n))], [(w(x_n))]
      whose diagonal sum [(v(x_n))] is unit-bounded.
    - Identify [v(sup x_n) = u(sup x_n) + sup w(x_n)]; compare to
      [v(sup x_n) = u(sup x_n) + w(sup x_n)] by [w_E]; cancel. *)
Lemma linhom_diff_continuous : is_omega_continuous w.
Proof.
move=> x xch xub fwch fwub.
set xs := cone_sup_ball x xch xub.
have Hxs : cnorm xs <= 1 by exact: cone_sup_ball_norm.
have v_lin := linhom_pre_linear (linhom_pre_of v).
have u_lin := linhom_pre_linear (linhom_pre_of u).
have w_lin : is_linear w by exact: linhom_diff_linear.
have v_cont := linhom_pre_continuous (linhom_pre_of v).
have u_cont := linhom_pre_continuous (linhom_pre_of u).
(* Image chains: (u ∘ x), (v ∘ x), (w ∘ x). *)
have vx_ch n :
    precone_le (linhom_fun v (x n)) (linhom_fun v (x n.+1)).
  exact: (linear_increasing v_lin) _ _ (xch n).
have ux_ch n :
    precone_le (linhom_fun u (x n)) (linhom_fun u (x n.+1)).
  exact: (linear_increasing u_lin) _ _ (xch n).
have vx_ub n : cnorm (linhom_fun v (x n)) <= 1.
  have H := linhom_norm_apply_le Hv_le1 (x n).
  rewrite mul1r in H; exact: le_trans H (xub n).
have ux_ub n : cnorm (linhom_fun u (x n)) <= 1.
  have H := linhom_norm_apply_le Hu_le1 (x n).
  rewrite mul1r in H; exact: le_trans H (xub n).
(* Apply u_cont and v_cont to chain x: *)
have v_sup : linhom_fun v xs =
    cone_sup_ball (linhom_fun v \o x) vx_ch vx_ub.
  exact: v_cont.
have u_sup : linhom_fun u xs =
    cone_sup_ball (linhom_fun u \o x) ux_ch ux_ub.
  exact: u_cont.
(* The diagonal sum chain (u(x_n) + w(x_n)) equals (v(x_n)) by w_E. *)
have sum_pw n :
    precone_add (linhom_fun u (x n)) (w (x n)) = linhom_fun v (x n).
  by symmetry; exact: w_E.
have sum_ch n :
    precone_le
      (precone_add (linhom_fun u (x n)) (w (x n)))
      (precone_add (linhom_fun u (x n.+1)) (w (x n.+1))).
  by rewrite !sum_pw; exact: vx_ch.
have sum_ub n :
    cnorm (precone_add (linhom_fun u (x n)) (w (x n))) <= 1.
  by rewrite sum_pw; exact: vx_ub.
(* By cone_sup_ball_addD: sup (u + w) = sup u + sup w. *)
have addD := @cone_sup_ball_addD R D
              (linhom_fun u \o x) (w \o x)
              ux_ch ux_ub fwch fwub sum_ch sum_ub.
(* sup (u + w) ∘ x = sup (v ∘ x), via Prop_irrelevance. *)
have sum_eq_v :
    cone_sup_ball
      (fun n => precone_add (linhom_fun u (x n)) (w (x n)))
      sum_ch sum_ub =
    cone_sup_ball (linhom_fun v \o x) vx_ch vx_ub.
  apply: precone_le_anti.
  - apply: cone_sup_ball_lub => n.
    rewrite /= sum_pw.
    exact: cone_sup_ball_ub.
  - apply: cone_sup_ball_lub => n.
    rewrite /= -sum_pw.
    exact: cone_sup_ball_ub.
(* Putting it together: v(xs) = u(xs) + sup w(x_n).  *)
have key :
    linhom_fun v xs =
    precone_add (linhom_fun u xs) (cone_sup_ball (w \o x) fwch fwub).
  by rewrite v_sup u_sup -addD sum_eq_v.
(* And by w_E at xs: v(xs) = u(xs) + w(xs). *)
have key' := w_E xs.
(* Cancel u(xs) from both sides. *)
rewrite key in key'; symmetry.
exact: precone_cancel key'.
Qed.

(** Paper §5.1: path-preservation of [w] — Step 1c.

    Template: [path_sup_ball_ub] / [path_sup_ball_lub] in
    [theories/mcones/path.v] (the [w_meas] step). *)
Lemma linhom_diff_pres_path (X : ar_obj Ar)
    (γ : ar_carrier Ar X -> C) :
  is_measurable_path (Ar:=Ar) (C:=C) γ ->
  is_measurable_path (Ar:=Ar) (C:=D) (fun r => w (γ r)).
Proof.
move=> Hγ.
have Hvγ : is_measurable_path
    (Ar:=Ar) (C:=D) (fun r => linhom_fun v (γ r)).
  exact: (linhom_pre_pres_path (linhom_pre_of v)).
have Huγ : is_measurable_path
    (Ar:=Ar) (C:=D) (fun r => linhom_fun u (γ r)).
  exact: (linhom_pre_pres_path (linhom_pre_of u)).
have [[Mv HMv] Hv_meas] := Hvγ.
have [_ Hu_meas] := Huγ.
split.
  exists Mv => r.
  have H1 := @cone_normp _ _ _ _ (w_le_v (γ r)).
  exact: le_trans H1 (HMv r).
move=> Y m mM.
have -> :
  (fun p : (ar_carrier Ar Y * ar_carrier Ar X)%type =>
    test_fun m p.1 (w (γ p.2))) =
  (fun p : (ar_carrier Ar Y * ar_carrier Ar X)%type =>
    test_fun m p.1 (linhom_fun v (γ p.2)) -
    test_fun m p.1 (linhom_fun u (γ p.2))).
  apply: funext => p.
  have := w_E (γ p.2).
  move/(congr1 (test_fun m p.1)).
  rewrite test_linD => H.
  rewrite H.
  by rewrite addrAC subrr add0r.
by apply: measurable_funB; [exact: Hv_meas | exact: Hu_meas].
Qed.

(** Paper §5.1: integral-preservation of [w] — Step 1d.

    Template: [linhom_add_fun_pres_int] (the additivity +
    cancellation pattern); mirrors the [Path] additivity lemma
    [path_integral_eq_addB]. *)
Lemma linhom_diff_pres_int (X : ar_obj Ar)
    (β : ar_carrier Ar X -> C) (Hβ : is_measurable_path β)
    (µ : fmeas R (ar_carrier Ar X)) :
  w (icone_integral β Hβ µ) =
  icone_integral (fun r => w (β r)) (linhom_diff_pres_path Hβ) µ.
Proof.
have Hvγ := linhom_pre_pres_path (linhom_pre_of v) X β Hβ.
have Huγ := linhom_pre_pres_path (linhom_pre_of u) X β Hβ.
have Hwγ : is_measurable_path (fun r : ar_carrier Ar X => w (β r))
  := linhom_diff_pres_path Hβ.
have at_int :
    linhom_fun v (icone_integral β Hβ µ) =
    precone_add
      (linhom_fun u (icone_integral β Hβ µ))
      (w (icone_integral β Hβ µ)).
  exact: w_E.
(* By Pettis spec on v: v(∫β) satisfies path_integral_eq for (v ∘ β). *)
have Petv : path_integral_eq (fun r => linhom_fun v (β r)) µ
    (linhom_fun v (icone_integral β Hβ µ)).
  move=> m mM s.
  have := linhom_pres_int v X β Hβ µ.
  rewrite /linhom_fun /= => -> .
  exact: (icone_integralP _ _ µ m mM s).
have Petu : path_integral_eq (fun r => linhom_fun u (β r)) µ
    (linhom_fun u (icone_integral β Hβ µ)).
  move=> m mM s.
  have := linhom_pres_int u X β Hβ µ.
  rewrite /linhom_fun /= => -> .
  exact: (icone_integralP _ _ µ m mM s).
(* Sum Pettis spec: v(∫β) = ∫(v ∘ β) = ∫(u ∘ β) + ∫(w ∘ β) via
   path_integral_eq_addB on (u ∘ β) and (w ∘ β). *)
have Petsum : path_integral_eq
    (fun r => precone_add (linhom_fun u (β r)) (w (β r))) µ
    (precone_add
       (icone_integral (fun r => linhom_fun u (β r)) Huγ µ)
       (icone_integral (fun r => w (β r)) Hwγ µ)).
  apply: (@path_integral_eq_addB R Ar D X µ _ _ _ _ Huγ Hwγ).
  - exact: icone_integralP.
  - exact: icone_integralP.
(* Note (fun r => v (β r)) = (fun r => u(β r) + w(β r)) by pw_eq. *)
have Petv' : path_integral_eq
    (fun r => precone_add (linhom_fun u (β r)) (w (β r))) µ
    (linhom_fun v (icone_integral β Hβ µ)).
  move=> m mM s.
  have := Petv m mM s.
  congr (_ = _).
  congr fine.
  by apply: eq_integral => r _; rewrite w_E.
(* By uniqueness of the path-integral (icone_integral_eqP, applied to
   B = D viewed as iconeType): the two witnesses of Petsum and Petv'
   agree. *)
have UE : linhom_fun v (icone_integral β Hβ µ) =
    precone_add
      (icone_integral (fun r => linhom_fun u (β r)) Huγ µ)
      (icone_integral (fun r => w (β r)) Hwγ µ).
  have Hpath : is_measurable_path
      (fun r => precone_add (linhom_fun u (β r)) (w (β r))).
    have -> : (fun r => precone_add (linhom_fun u (β r)) (w (β r)))
            = (fun r : ar_carrier Ar X => linhom_fun v (β r))
      by apply: funext => r; rewrite -w_E.
    exact: Hvγ.
  have H1 := icone_integral_eqP _ Hpath µ _ Petv'.
  have H2 := icone_integral_eqP _ Hpath µ _ Petsum.
  by rewrite H1 H2.
(* Now we have: v(∫β) = u(∫β) + w(∫β) = ∫(u ∘ β) + ∫(w ∘ β).
   Also v(∫β) = ∫(u ∘ β) + ∫(w ∘ β) by UE; and u(∫β) = ∫(u ∘ β)
   via Petu — we'll need this equality too. *)
have u_int_eq : linhom_fun u (icone_integral β Hβ µ) =
    icone_integral (fun r => linhom_fun u (β r)) Huγ µ.
  by apply: icone_integral_eqP.
(* Combine in at_int. *)
rewrite UE u_int_eq in at_int.
(* at_int: ∫(u∘β) + ∫(w∘β) = ∫(u∘β) + w(∫β); cancel to get
   ∫(w∘β) = w(∫β). *)
have key : icone_integral (fun r => w (β r)) Hwγ µ =
    w (icone_integral β Hβ µ).
  exact: precone_cancel at_int.
(* Goal: w(∫β) = icone_integral (...) (linhom_diff_pres_path Hβ) µ;
   the local witness [Hwγ] equals [linhom_diff_pres_path Hβ] by
   Prop_irrelevance. *)
rewrite (_ : linhom_diff_pres_path Hβ = Hwγ);
  last exact: Prop_irrelevance.
by symmetry.
Qed.

(** Packaging: [linhom_pre] form. *)
Definition linhom_diff_pre : linhom_pre Ar C D :=
  MkLinhomPre w
    (linhom_diff_linear Hle)
    linhom_diff_continuous
    linhom_diff_bounded
    linhom_diff_pres_path.

(** Packaging: full [linhom_car] form. *)
Definition linhom_diff_car : linhom_car Ar C D :=
  MkLinhom linhom_diff_pre linhom_diff_pres_int.

End LinhomDiffPack.

Arguments linhom_diff_pre {R Ar C D u v} Hle Hv_le1.
Arguments linhom_diff_car {R Ar C D u v} Hle Hv_le1.

(** ** Sup-ball is an upper bound and least upper bound — Paper §5.1

    With [linhom_diff_car] in hand, we can produce a [linhom_car]
    witness of [precone_le (u n) (linhom_sup_ball u uch ub1)] for
    every [n], and dually a witness of the least-upper-bound
    property. These two lemmas close the (Normc) axiom on
    [linhom_car], yielding the [isCone] HB instance. *)

Section LinhomSupBallOrder.
Variables (R : realType) (Ar : MeasSubcat R).
Variables C D : ICone.type Ar.

Variable u : nat -> linhom_car Ar C D.
Hypothesis uch : forall n, precone_le (u n) (u n.+1).
Hypothesis ub1 : forall n, linhom_norm (u n) <= 1.

Local Notation S := (linhom_sup_ball u uch ub1).

(** Paper §5.1 (Normc) — every chain element is below the sup. *)
Lemma linhom_sup_ball_ub n : precone_le (u n) S.
Proof.
(* Pointwise: for each x, (u_n x) ≤p linhom_sup_fun x.
   Working via linhom_sup_funE (the scaled form at cnorm_succ_nng x). *)
have Hle : forall x : C,
    exists z : D, linhom_fun S x =
      precone_add (linhom_fun (u n) x) z.
  move=> x.
  have S_eq : linhom_fun S x = linhom_sup_fun uch ub1 x by [].
  (* Use linhom_sup_funE: linhom_sup_fun x = cnorm_succ *:
     cone_sup_ball (k ↦ linhom_fun (u k) (cnorm_succ_inv *: x)). *)
  rewrite S_eq linhom_sup_funE.
  pose rinv := cnorm_succ_inv_nng x.
  pose r := cnorm_succ_nng x.
  (* By cone_sup_ball_ub in D applied to the k-indexed chain at n. *)
  have Hub_n := @cone_sup_ball_ub R D
                  (fun k => linhom_fun (u k) (precone_scale rinv x))
                  (fun k => linhom_sup_pw_chain uch _ k)
                  (linhom_sup_pw_ub1 ub1 (cnorm_inv_unit x)) n.
  case: Hub_n => z Hz.
  exists (precone_scale r z).
  rewrite Hz precone_scale_DAr.
  (* Goal: r *: (u_n (rinv *: x) + z) = u_n x + r *: z, i.e.,
     r *: u_n (rinv *: x) = u_n x. By linearity:
     r *: u_n (rinv *: x) = u_n (r *: rinv *: x) = u_n x. *)
  have [_ _ HZ] := linhom_pre_linear (linhom_pre_of (u n)).
  have key : precone_scale r (linhom_fun (u n) (precone_scale rinv x)) =
             linhom_fun (u n) x.
    rewrite -HZ -precone_scale_A.
    have nng_eq : forall (a b : {nonneg R}), a%:num = b%:num -> a = b.
      by move=> a b /val_inj.
    have r_rinv : (r%:num * rinv%:num)%:nng = 1%:nng :> {nonneg R}.
      apply: nng_eq => /=.
      have hp := cnorm_succ_pos x.
      by rewrite mulfV// gt_eqF.
    by rewrite r_rinv precone_scale_1.
  by congr precone_add; rewrite -key.
have Hv1 : linhom_norm S <= 1 by exact: linhom_sup_ball_norm.
exists (linhom_diff_car Hle Hv1).
apply: linhom_eq => x /=.
have := linhom_diff_E Hle x.
rewrite /linhom_diff_car /linhom_diff_pre /linhom_diff_fun /=.
by move=> ->.
Qed.

(** Paper §5.1 (Normc) — the sup is least among all upper bounds. *)
Lemma linhom_sup_ball_lub (y : linhom_car Ar C D) :
  (forall n, precone_le (u n) y) -> precone_le S y.
Proof.
move=> Hy.
(* Pointwise: each (u n x) ≤p y x; by cone_sup_ball_lub in D,
   linhom_sup_fun x ≤p y x. We work via the scaled-form
   [linhom_sup_funE]. *)
have Hle : forall x : C,
    exists z : D, linhom_fun y x =
      precone_add (linhom_fun S x) z.
  move=> x.
  pose rinv := cnorm_succ_inv_nng x.
  pose r := cnorm_succ_nng x.
  (* Pointwise at scaled x: each (u n) (rinv *: x) ≤p y (rinv *: x). *)
  have Hpw : forall n, precone_le (linhom_fun (u n) (precone_scale rinv x))
                                   (linhom_fun y (precone_scale rinv x)).
    move=> n; exact: linhom_le_pointwise (Hy n) _.
  have Hsup := @cone_sup_ball_lub R D
                 (fun k => linhom_fun (u k) (precone_scale rinv x))
                 (fun k => linhom_sup_pw_chain uch _ k)
                 (linhom_sup_pw_ub1 ub1 (cnorm_inv_unit x))
                 (linhom_fun y (precone_scale rinv x)) Hpw.
  case: Hsup => z Hz.
  exists (precone_scale r z).
  (* linhom_fun S x = r *: cone_sup_ball (...) *)
  have S_eq : linhom_fun S x = linhom_sup_fun uch ub1 x by [].
  rewrite S_eq linhom_sup_funE.
  rewrite -precone_scale_DAr -Hz.
  (* Goal: linhom_fun y x = r *: linhom_fun y (rinv *: x). *)
  have [_ _ HZ] := linhom_pre_linear (linhom_pre_of y).
  rewrite -HZ -precone_scale_A.
  have nng_eq : forall (a b : {nonneg R}), a%:num = b%:num -> a = b.
    by move=> a b /val_inj.
  have hp := cnorm_succ_pos x.
  have r_rinv : (r%:num * rinv%:num)%:nng = 1%:nng :> {nonneg R}.
    by apply: nng_eq => /=; rewrite mulfV// gt_eqF.
  by rewrite r_rinv precone_scale_1.
(* Need ‖S‖ ≤ 1 to instantiate linhom_diff_car at the inverted
   inequality. The roles are reversed: here the "v" is y and "u"
   is S. We need ‖y‖ ≤ 1 — but y is a *generic* upper bound, and
   ‖y‖ need not be ≤ 1. We sidestep by NOT using [linhom_diff_car]:
   instead, directly use [linhom_diff_pres_int] without the
   unit-norm Hypothesis. But linhom_diff_continuous needs it!
   We re-prove ω-continuity here using the unit-norm bound from
   linhom_sup_ball_norm. *)
have Hv1 : linhom_norm S <= 1 by exact: linhom_sup_ball_norm.
(* Hle now says y x = S x + z, i.e., S x ≤p y x with witness. We
   build the difference linhom_car using a flipped Hle. The
   difference's continuity depends on the *larger* element being
   unit-norm, which fails for y in general. So we cannot package
   the diff as a linhom_car.

   Workaround: we construct the difference function differently —
   we need a [linhom_car δ] with [y = S + δ]. Since ‖S‖ ≤ 1 ≤ ‖y‖
   (where ‖y‖ may be large), the *difference* y - S has norm at
   most 2 (or arbitrary), still finite. The construction
   [linhom_diff_car] requires ‖larger‖ ≤ 1 for its continuity
   proof; but we can scale.

   Concretely: pose K := ‖y‖ + 1 (positive), then ‖y/K‖ ≤ 1 and
   ‖S/K‖ ≤ ‖S‖/K ≤ 1/K ≤ 1. Apply linhom_diff_car to the *scaled*
   pair (S/K, y/K) with witness (Hle scaled), then scale the
   resulting δ back by K. *)
have K_ge0 : 0 <= linhom_norm y + 1.
  apply: ltW; apply: lt_le_trans ltr01 _.
  by rewrite -[X in X <= _]add0r lerD2r; exact: linhom_norm_ge0.
pose K : {nonneg R} := NngNum K_ge0.
have Kpos : 0 < K%:num.
  by apply: lt_le_trans ltr01 _;
     rewrite -[X in X <= _]add0r lerD2r; exact: linhom_norm_ge0.
have Kinv_ge0 : 0 <= (linhom_norm y + 1)^-1
  by rewrite invr_ge0 ltW.
pose Kinv : {nonneg R} := NngNum Kinv_ge0.
have KKinv : K%:num * Kinv%:num = 1
  by rewrite /= mulfV// gt_eqF.
have KinvK : Kinv%:num * K%:num = 1
  by rewrite /= mulVf// gt_eqF.
have nng_eq : forall (a b : {nonneg R}), a%:num = b%:num -> a = b.
  by move=> a b /val_inj.
have KKinv_nng : (K%:num * Kinv%:num)%:nng = 1%:nng :> {nonneg R}
  by apply: nng_eq.
have KinvK_nng : (Kinv%:num * K%:num)%:nng = 1%:nng :> {nonneg R}
  by apply: nng_eq.
(* Scaled versions. *)
pose yK : linhom_car Ar C D := linhom_scale Kinv y.
pose SK : linhom_car Ar C D := linhom_scale Kinv S.
have HyK_norm : linhom_norm yK <= 1.
  rewrite /yK.
  apply: linhom_norm_sup_lub => x Hx.
  rewrite /linhom_fun /linhom_scale /linhom_scale_pre /linhom_scale_fun /=.
  rewrite cone_normh /=.
  rewrite mulrC -ler_pdivlMr; last by rewrite invr_gt0.
  rewrite invrK.
  have Hub := linhom_norm_sup_ub y x Hx.
  apply: le_trans Hub _.
  rewrite mul1r -[X in X <= _]addr0 lerD2l.
  exact: ler01.
have HSK_le_yK : forall x : C,
    exists z : D, linhom_fun yK x = precone_add (linhom_fun SK x) z.
  move=> x.
  case: (Hle x) => z Hz.
  exists (precone_scale Kinv z).
  rewrite /yK /SK /linhom_fun /linhom_scale /linhom_scale_pre
          /linhom_scale_fun /= Hz precone_scale_DAr //.
pose δK : linhom_car Ar C D := linhom_diff_car HSK_le_yK HyK_norm.
have δK_eq : forall x : C,
    linhom_fun yK x = precone_add (linhom_fun SK x) (linhom_fun δK x).
  move=> x.
  rewrite /δK /linhom_diff_car /linhom_diff_pre /linhom_diff_fun /=.
  exact: (linhom_diff_E HSK_le_yK x).
(* Pointwise: yK x = SK x + δK x, i.e.,
   Kinv *: y(x) = Kinv *: S(x) + δK(x). Scale by K to obtain
   y(x) = S(x) + K *: δK(x). *)
have pw_y : forall x : C,
    linhom_fun y x =
    precone_add (linhom_fun S x) (precone_scale K (linhom_fun δK x)).
  move=> x.
  have HK_eq : precone_scale Kinv (linhom_fun y x) =
               precone_add (precone_scale Kinv (linhom_fun S x))
                           (linhom_fun δK x).
    have := δK_eq x.
    by rewrite /yK /SK /linhom_fun /linhom_scale /linhom_scale_pre
               /linhom_scale_fun /=.
  (* Scale HK_eq by K. *)
  have HK_scaled := congr1 (precone_scale K) HK_eq.
  rewrite precone_scale_DAr in HK_scaled.
  rewrite -[in precone_scale K (precone_scale Kinv (linhom_fun y x))]
           precone_scale_A in HK_scaled.
  rewrite -[in precone_scale K (precone_scale Kinv (linhom_fun S x))]
           precone_scale_A in HK_scaled.
  have nng1 : (K%:num * Kinv%:num)%:nng = 1%:nng :> {nonneg R}
    by apply: nng_eq.
  rewrite nng1 !precone_scale_1 in HK_scaled.
  exact: HK_scaled.
(* Now scale δK back to obtain δ : linhom_car. *)
pose δ : linhom_car Ar C D := linhom_scale K δK.
exists δ.
apply: linhom_eq => x.
rewrite /δ /linhom_fun /linhom_scale /linhom_scale_pre
        /linhom_scale_fun /=.
exact: pw_y.
Qed.

End LinhomSupBallOrder.

Arguments linhom_sup_ball_ub {R Ar C D} u uch ub1 n.
Arguments linhom_sup_ball_lub {R Ar C D} u uch ub1 y.

(** ** [isCone] HB instance on [linhom_car] — Paper §5.1

    With (Normh), (Normz), (Normt), (Normp) already in place earlier
    in this file and (Normc) discharged via [linhom_sup_ball_ub] +
    [linhom_sup_ball_lub] + [linhom_sup_ball_norm], we register
    [linhom_car Ar C D] as a [coneType R]. *)

HB.instance Definition _ (R : realType) (Ar : MeasSubcat R)
    (C D : ICone.type Ar) :=
  @isCone.Build R (linhom_car Ar C D)
    (@linhom_norm R Ar C D)
    (@linhom_normh R Ar C D) (@linhom_normz R Ar C D)
    (@linhom_normt R Ar C D) (@linhom_normp R Ar C D)
    (@linhom_sup_ball R Ar C D)
    (@linhom_sup_ball_ub R Ar C D)
    (@linhom_sup_ball_lub R Ar C D)
    (@linhom_sup_ball_norm R Ar C D).

(** ** Sanity check: [linhom_car Ar C D] is a [coneType R] *)

Section LinhomConeCheck.
Variables (R : realType) (Ar : MeasSubcat R).
Variables C D : ICone.type Ar.

Check (linhom_car Ar C D : coneType R).

End LinhomConeCheck.

(** ** Sanity checks for [linhom_sup_ball] *)
Section LinhomSupBallSanityCheck.
Variables (R : realType) (Ar : MeasSubcat R).
Variables C D : ICone.type Ar.

(** Any chain of integrable linear maps in the unit ball admits a
    packaged [linhom_car] sup, with operator norm ≤ 1. *)
Check (fun (u : nat -> linhom_car Ar C D)
           (uch : forall n, precone_le (u n) (u n.+1))
           (ub1 : forall n, linhom_norm (u n) <= 1) =>
        linhom_sup_ball u uch ub1 : linhom_car Ar C D).
Check (fun (u : nat -> linhom_car Ar C D)
           (uch : forall n, precone_le (u n) (u n.+1))
           (ub1 : forall n, linhom_norm (u n) <= 1) =>
        linhom_sup_ball_norm u uch ub1 :
          linhom_norm (linhom_sup_ball u uch ub1) <= 1).

End LinhomSupBallSanityCheck.

(** ** Pointwise sup-of-chain and difference machinery — Paper §5.1

    The previous section assembles the sup-of-chain construction and
    the pointwise difference machinery used by the [linhom_car] cone
    structure (paper §5.1):

    - [cone_sup_ball_swap] — commutation of two unit-ball sups in a
      cone, used to discharge ω-continuity of [linhom_sup_fun].
    - [linhom_sup_fun_continuous] — ω-continuity of the pointwise sup
      (Step 2 of paper §5.1).  Proved via the swap identity and
      ω-continuity of each [u_n].
    - [is_measurable_path_scale] — scaling preserves measurable paths.
    - [linhom_sup_fun_pres_path] — path-preservation of the pointwise
      sup.  Strategy: uniform-scale rewrite [γ r = S *: γs r] with
      [S := M + 1], then [measurable_fun_cvg] on the chain
      [(s, r) ↦ m s (u_n (γs r))].
    - [linhom_norm_apply_le] — general operator-norm bound for
      arbitrary [x : C] (i.e., [cnorm (f x) ≤ ‖f‖ * cnorm x]).
    - [linhom_sup_fun_test_sup] — the test-of-sup identity:
      [m s (linhom_sup_fun x) = sup_n (m s (u_n x))] for any test [m].
    - [linhom_sup_fun_pres_int] — integral preservation of the
      pointwise sup.  Strategy mirrors [integral_omega_cont_path]:
      each [u_n] preserves integrals via Pettis; combine with MCT
      ([monotone_convergence]) and [fine_cvg] to identify both sides.
    - [linhom_sup_ball] — packaged sup-of-chain as a [linhom_car].
    - [linhom_sup_ball_norm] — the operator-norm bound ≤ 1.
    - [linhom_diff_fun] / [linhom_diff_linear] (linearity of the
      pointwise difference) — Paper §5.1.
    - [LinhomDiffPack] section discharges the four remaining fields
      of [linhom_car] on the difference [w x := linhom_diff_fun Hle
      x], conditional on the auxiliary hypothesis
      [linhom_norm v <= 1]:
        * [linhom_diff_bounded] — via [cone_normp] and the [w ≤p v]
          witness.
        * [linhom_diff_continuous] — by [v_cont], [u_cont] applied
          to the chain [x_n] (image bounds via [linhom_norm_apply_le]
          + the unit-norm hypothesis), [cone_sup_ball_addD], and
          [precone_cancel].
        * [linhom_diff_pres_path] — subtract the two measurable test
          paths of [v ∘ γ] and [u ∘ γ] using [test_linD] +
          [measurable_funB].
        * [linhom_diff_pres_int] — by [linhom_pres_int] on [u] and
          [v], pointwise [linhom_diff_E], path-additivity
          [path_integral_eq_addB], and cancellation [precone_cancel].
    - [linhom_diff_pre] and [linhom_diff_car] — the packaged
      [linhom_pre] and [linhom_car] for the difference.
    - [linhom_sup_ball_ub] (every chain element is below the sup) and
      [linhom_sup_ball_lub] (least upper bound) — both use
      [linhom_diff_car] as the witness, with [linhom_sup_ball_lub]
      introducing a uniform-scale [K := ‖y‖ + 1] to bring [y] into
      the unit ball before instantiating [linhom_diff_car].

    The HB tower [isPrecone] / [isCone] / [isMCone] / [isICone] on
    [linhom_car Ar C D] is registered later in this file. *)

(** ** [isMCone] HB instance on [linhom_car] — Paper Def 5.4 / §5.1

    Per paper §5.1: the measurability test family on [C ⊸ D] at arity
    [Y] is parametrised by a measurable path [γ ∈ Path(Y, C)] (with
    [cone_norm γ ≤ 1] so that the value [(γ ▷ m)(s, f)] lands in
    [[0, 1]] when [‖f‖ ≤ 1]) and a test [m ∈ M^D_Y]. The test body
    is

      [(γ ▷ m)(s, f) := test_fun m s (linhom_fun f (path_fun γ s))]

    and the family is closed under (Mscomp), (Mssep), (Msnorm). The
    unit-ball restriction on [γ] is harmless: (Mscomp) preserves it
    (via [path_normp] / [path_norm_ub]), and (Mssep) / (Msnorm) only
    ever use constant paths [γ_x := λ_. x] with [cone_norm x ≤ 1]. *)

Section LinhomTest.
Variables (R : realType) (Ar : MeasSubcat R).
Variables C D : ICone.type Ar.
Variables (Y : ar_obj Ar) (γ : path_car Ar Y C).
Hypothesis γub : cone_norm γ <= 1.
Variable m : test_of Ar Y D.
Hypothesis mM : mcone_M Y m.

(** Paper §5.1: the test body [(γ ▷ m)(s, f) := m(s, f(γ(s)))]. *)
Definition linhom_test_fun
    (s : ar_carrier Ar Y) (f : linhom_car Ar C D) : R :=
  test_fun m s (linhom_fun f (path_fun γ s)).

(** (Msmeas) — Paper §5.1 paragraph 1. Given a unit-ball [f]
    ([linhom_norm f ≤ 1]), the path [r ↦ linhom_fun f (path_fun γ r)]
    is a measurable path in [D] by [linhom_pre_pres_path]. The joint
    measurability of [(s', r) ↦ m s' ((f ∘ γ) r)] in [Y × Y] specialises
    via the diagonal [s ↦ (s, s)] to give measurability in [s]. *)
Lemma linhom_test_meas (f : linhom_car Ar C D) :
  cone_norm f <= 1 ->
  measurable_fun setT
                 (fun s => linhom_test_fun s f).
Proof.
move=> Hf.
have Hfγ : is_measurable_path
    (fun r : ar_carrier Ar Y => linhom_fun f (path_fun γ r)).
  exact: linhom_pre_pres_path (linhom_pre_of f) Y (path_fun γ) (path_is_path γ).
have [_ Hg] := Hfγ.
have Hbase : measurable_fun
  [set: (ar_carrier Ar Y * ar_carrier Ar Y)%type]
  (fun p => test_fun m p.1 (linhom_fun f (path_fun γ p.2))).
  exact: Hg.
have Hpair : measurable_fun
  [set: ar_carrier Ar Y]
  (fun s => (s, s) : ar_carrier Ar Y * ar_carrier Ar Y).
  by apply: measurable_fun_pair; exact: @measurable_id.
rewrite /linhom_test_fun.
pose F (p : ar_carrier Ar Y * ar_carrier Ar Y) : R :=
  test_fun m p.1 (linhom_fun f (path_fun γ p.2)).
have -> : (fun s => test_fun m s (linhom_fun f (path_fun γ s))) =
          F \o (fun s => (s, s)).
  by apply: funext.
exact: measurableT_comp.
Qed.

Lemma linhom_test_ge0 (s : ar_carrier Ar Y) (f : linhom_car Ar C D) :
  0 <= linhom_test_fun s f.
Proof. exact: test_ge0. Qed.

(** (Msmeas) — [(γ ▷ m)(s, f) ≤ 1] when [linhom_norm f ≤ 1].
    Argument: [‖f(γ s)‖ ≤ ‖f‖ · ‖γ s‖ ≤ 1 · ‖γ‖ ≤ 1]. *)
Lemma linhom_test_le1 (s : ar_carrier Ar Y) (f : linhom_car Ar C D) :
  cone_norm f <= 1 -> linhom_test_fun s f <= 1.
Proof.
move=> Hf; apply: test_le1.
have step1 : cone_norm (linhom_fun f (path_fun γ s))
             <= 1 * cone_norm (path_fun γ s).
  exact: linhom_norm_apply_le Hf _.
apply: le_trans step1 _.
rewrite mul1r.
by apply: le_trans (path_norm_ub _ _) _; exact: γub.
Qed.

Lemma linhom_test_lin0 (s : ar_carrier Ar Y) :
  linhom_test_fun s (linhom_zero C D) = 0.
Proof. by rewrite /linhom_test_fun /= test_lin0. Qed.

Lemma linhom_test_linD (s : ar_carrier Ar Y) (f1 f2 : linhom_car Ar C D) :
  linhom_test_fun s (linhom_add f1 f2) =
  linhom_test_fun s f1 + linhom_test_fun s f2.
Proof. by rewrite /linhom_test_fun /= test_linD. Qed.

Lemma linhom_test_linZ
  (s : ar_carrier Ar Y) (r : {nonneg R}) (f : linhom_car Ar C D) :
  linhom_test_fun s (linhom_scale r f) =
  r%:num * linhom_test_fun s f.
Proof. by rewrite /linhom_test_fun /= test_linZ. Qed.

(** ω-continuity in [f]: directly via [linhom_sup_fun_test_sup],
    which says [m s (linhom_sup_fun u_n x) = sup_n m s (u_n x)]. *)
Lemma linhom_test_cont
    (s : ar_carrier Ar Y)
    (u : nat -> linhom_car Ar C D)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, cone_norm (u n) <= 1)
    (N : R) :
  (forall n, linhom_test_fun s (u n) <= N) ->
  linhom_test_fun s (cone_sup_ball u uch ub1) <= N.
Proof.
move=> HN.
rewrite /linhom_test_fun /=.
rewrite (linhom_sup_fun_test_sup uch ub1 m s (path_fun γ s)).
apply: ge_sup.
  by exists (test_fun m s (linhom_fun (u 0%N) (path_fun γ s))), 0%N.
by move=> _ [n _ <-]; exact: HN.
Qed.

(** Pointwise upper bound: [(γ ▷ m)(s, f) ≤ cnorm f]. *)
Lemma linhom_test_norm_le
    (s : ar_carrier Ar Y) (f : linhom_car Ar C D) :
  linhom_test_fun s f <= cone_norm f.
Proof.
apply: le_trans (test_norm_le _ _ _) _.
(* test_norm_le of m gives ≤ cone_norm (f (γ s)) ≤ ‖f‖ ‖γ s‖ ≤ ‖f‖. *)
apply: le_trans (linhom_norm_apply_le (lexx _) (path_fun γ s)) _.
have Hγs : cone_norm (path_fun γ s) <= 1.
  by apply: le_trans (path_norm_ub _ _) _; exact: γub.
rewrite -[X in _ <= X]mulr1.
by apply: ler_wpM2l;
  [exact: linhom_norm_ge0 | exact: Hγs].
Qed.

(** The packaged test, abbreviated [γ ▷ m]. *)
Definition linhom_test : test_of Ar Y (linhom_car Ar C D) :=
  MkTestOf linhom_test_meas linhom_test_ge0 linhom_test_le1
           linhom_test_lin0 linhom_test_linD linhom_test_linZ
           linhom_test_cont linhom_test_norm_le.

End LinhomTest.

Arguments linhom_test {R Ar C D Y}.

(** ** The measurability structure on [linhom_car] — Paper Def 5.4

    [M_Y(C ⊸ D) = {γ ▷ m | γ ∈ Path(Y, C), ‖γ‖ ≤ 1, m ∈ M^D_Y}]. *)

Section LinhomMCone.
Variables (R : realType) (Ar : MeasSubcat R).
Variables C D : ICone.type Ar.

Definition linhom_mcone_M (Y : ar_obj Ar) :
    set (test_of Ar Y (linhom_car Ar C D)) :=
  [set p | exists (γ : path_car Ar Y C) (γub : cone_norm γ <= 1)
                  (m : test_of Ar Y D) (mM : mcone_M Y m),
    p = linhom_test γ γub m mM].

(** (Mscomp) — Paper §5.1. Reindexing by [ψ : ar_hom Y' Y]: the
    reindexed test is [(s', f) ↦ m(ψ s', f(γ(ψ s')))], which equals
    [(γ ∘ ψ) ▷ (m ∘ (ψ × D))]. *)
Lemma linhom_mcone_M_comp
  (Y' Y : ar_obj Ar) (ψ : ar_hom Ar Y' Y)
  (p : test_of Ar Y (linhom_car Ar C D)) :
  linhom_mcone_M p ->
  linhom_mcone_M (test_reindex ψ p).
Proof.
case=> γ [γub [m [mM ->]]].
(* Build the reindexed path γ ∘ ψ as a path_car Ar Y' C. *)
have Hγψ : is_measurable_path (path_fun γ \o ψ).
  exact: reindex_path_measurable ψ (path_is_path γ).
pose γ' : path_car Ar Y' C := MkPath Hγψ.
(* Unit-ball preserved: ‖γ ∘ ψ‖ ≤ ‖γ‖ ≤ 1, since the image set of
   γ ∘ ψ is a subset of the image of γ. *)
have γ'ub : cone_norm γ' <= 1.
  apply: ge_sup; first exact: path_normset_nonempty.
  move=> _ [r ->].
  apply: le_trans (path_norm_ub γ (ψ r)) _; exact: γub.
have mM' : mcone_M Y' (test_reindex ψ m) by exact: mcone_M_comp.
exists γ', γ'ub, (test_reindex ψ m), mM'.
apply: test_eq => s f /=.
by rewrite /linhom_test_fun /test_reindex_fun /=.
Qed.

(** Helper: constant path [γ_x : ar_carrier Z -> C] at arbitrary
    arity, measurable, with [cone_norm γ_x = cone_norm x]. *)
Section ConstPathAtArity.
Variables (Z : ar_obj Ar) (x : C).

Let const_x_fun : ar_carrier Ar Z -> C := fun _ => x.

Lemma const_x_is_path :
  is_measurable_path (Ar:=Ar) (C:=C) (X:=Z) const_x_fun.
Proof. exact: const_path_measurable. Qed.

Definition const_x_path_arity : path_car Ar Z C :=
  MkPath const_x_is_path.

Lemma const_x_path_arity_normE :
  path_norm const_x_path_arity = cone_norm x.
Proof.
apply: le_anti; apply/andP; split.
- apply: ge_sup; first exact: path_normset_nonempty.
  by move=> _ [r ->] /=; exact: lexx.
- have Hin : path_normset const_x_path_arity (cone_norm x).
    by exists (ar_point Ar Z).
  by move/ubP : (sup_upper_bound (path_normset_has_sup const_x_path_arity));
    apply.
Qed.

End ConstPathAtArity.

(** Specialization at [Z = ar_zero], used in (Mssep)/(Msnorm) below. *)
Definition const_x_path (x : C) : path_car Ar (ar_zero Ar) C :=
  const_x_path_arity (ar_zero Ar) x.

Lemma const_x_path_normE (x : C) :
  path_norm (const_x_path x) = cone_norm x.
Proof. exact: const_x_path_arity_normE. Qed.

(** (Mssep) — Paper §5.1: tests at arity 0 separate linear maps. *)
Lemma linhom_mcone_M_sep (f1 f2 : linhom_car Ar C D) :
  (forall p : test_of Ar (ar_zero Ar) (linhom_car Ar C D),
    linhom_mcone_M (Y:=ar_zero Ar) p ->
    test_fun p (ar_zero_pt Ar) f1 = test_fun p (ar_zero_pt Ar) f2) ->
  f1 = f2.
Proof.
move=> Hsep; apply: linhom_eq => x.
apply: mcone_M_sep => m mM.
(* Use the rescaled-to-unit-ball constant path γ_{x'} where
   x' = (1/(‖x‖+1)) *: x has norm ≤ 1. Then γ_{x'} ▷ m is a test in
   the family, and its value at f_i is m _ (f_i x'). Use linearity of
   f_i to scale back to m _ ((1/‖x‖+1) *: f_i x), and equality gives
   m _ (f_i x) = m _ (f_2 x) by ‖x‖+1 ≠ 0. *)
have S_pos : 0 < cone_norm x + 1 by exact: cnorm_succ_pos.
have Sinv_ge0 : 0 <= (cone_norm x + 1)^-1 by rewrite invr_ge0 ltW.
pose Sinv : {nonneg R} := NngNum Sinv_ge0.
have Sinv_pos : 0 < Sinv%:num by rewrite /= invr_gt0.
have Sinv_neq0 : Sinv%:num != 0 by rewrite gt_eqF.
pose x' : C := precone_scale Sinv x.
have Hx'_unit : cone_norm x' <= 1.
  rewrite /x' cone_normh /=.
  rewrite mulrC ler_pdivrMr // mul1r.
  by rewrite -[X in X <= _]addr0 lerD2l ler01.
have Hγx'_unit : cone_norm (const_x_path x') <= 1.
  by rewrite /cone_norm /= const_x_path_normE.
have HinM : linhom_mcone_M (Y:=ar_zero Ar)
  (linhom_test (const_x_path x') Hγx'_unit m mM).
  by exists (const_x_path x'), Hγx'_unit, m, mM.
have Heq := Hsep _ HinM.
rewrite /linhom_test /linhom_test_fun /= in Heq.
have [_ _ HfZ1] := linhom_pre_linear (linhom_pre_of f1).
have [_ _ HfZ2] := linhom_pre_linear (linhom_pre_of f2).
rewrite /linhom_fun in Heq.
rewrite /x' HfZ1 HfZ2 in Heq.
rewrite test_linZ test_linZ in Heq.
have step : Sinv%:num * test_fun m (ar_zero_pt Ar) (linhom_fun f1 x) =
            Sinv%:num * test_fun m (ar_zero_pt Ar) (linhom_fun f2 x).
  exact: Heq.
have := mulfI Sinv_neq0 step.
by rewrite /linhom_fun.
Qed.

(** (Msnorm) — Paper §5.1. Given [f ≠ 0] and ε > 0:
    1. Choose [x : C] with [cnorm x ≤ 1] and [‖f‖ ≤ cnorm (f x) + ε/2]
       (sup adherence on [linhom_normset f]).
    2. Either [f x = 0] (then ‖f‖ ≤ ε/2, take any witness test) or
       [f x ≠ 0]: apply (Msnorm) in [D] to [f x] with [ε/2] to get
       [m ∈ M^D_0] with [cnorm (f x) ≤ m (f x) + ε/2].
    3. Witness test: [(const_x_path x) ▷ m] applied at the zero point
       gives [m _ (f x)], and [‖f‖ ≤ m (f x) + ε]. *)
Lemma linhom_mcone_M_norm (f : linhom_car Ar C D) (eps : R) :
  f <> linhom_zero C D -> 0 < eps ->
  exists p : test_of Ar (ar_zero Ar) (linhom_car Ar C D),
    linhom_mcone_M (Y:=ar_zero Ar) p /\
    cone_norm f <= test_fun p (ar_zero_pt Ar) f + eps.
Proof.
move=> fne eps_pos.
have eps2_pos : 0 < eps / 2 by rewrite divr_gt0.
have norm_pos : 0 < cone_norm f.
  rewrite lt_def cone_norm_ge0 andbT.
  by apply/eqP => Hn0; apply: fne; exact: linhom_normz Hn0.
have has_sup_f : has_sup (linhom_normset f).
  exact: linhom_normset_has_sup.
have [v Hv1 Hv2] := sup_adherent eps2_pos has_sup_f.
case: Hv1 => x0 [Hx0_le1 Hx0_eq].
have HnormR : cone_norm f <= cone_norm (linhom_fun f x0) + eps / 2.
  rewrite -lerBlDr ltW //.
  by rewrite -/(linhom_norm f) -Hx0_eq.
have [eqz | nez] : linhom_fun f x0 = precone_zero \/
                   linhom_fun f x0 <> precone_zero.
  by case: (pselect (linhom_fun f x0 = precone_zero)); tauto.
- (* [f x0 = 0]: then ‖f‖ ≤ ε/2 ≤ ε. *)
  have norm_le_e2 : cone_norm f <= eps / 2.
    apply: le_trans HnormR _.
    by rewrite eqz cone_norm0 add0r.
  (* Pick any x1 with f x1 ≠ 0. *)
  have [x1 nz1] : exists x1, linhom_fun f x1 <> precone_zero.
    apply: contrapT => Hne; apply: fne.
    apply: linhom_eq => x.
    apply: contrapT => Hr.
    by apply: Hne; exists x.
  (* Need a unit-ball x1' with f x1' ≠ 0; rescale. *)
  have x1n_pos : 0 < cone_norm x1.
    rewrite lt_def cone_norm_ge0 andbT.
    apply/eqP => Hnz; apply: nz1.
    have x1_zero : x1 = precone_zero by exact: cone_normz.
    case: (linhom_pre_linear (linhom_pre_of f)) => H0 _ _.
    by rewrite x1_zero /linhom_fun H0.
  have Tinv_ge0 : 0 <= (cone_norm x1)^-1 by rewrite invr_ge0 ltW.
  pose Tinv : {nonneg R} := NngNum Tinv_ge0.
  have Tinv_pos : 0 < Tinv%:num by rewrite /= invr_gt0.
  pose x1' : C := precone_scale Tinv x1.
  have Hx1'_unit : cone_norm x1' <= 1.
    rewrite /x1' cone_normh /=.
    by rewrite mulVf ?gt_eqF.
  have nz1' : linhom_fun f x1' <> precone_zero.
    have [_ _ HfZ] := linhom_pre_linear (linhom_pre_of f).
    rewrite /x1' /linhom_fun HfZ.
    move=> Hsc; apply: nz1.
    have step : precone_scale (NngNum (ltW x1n_pos))
                  (precone_scale Tinv (linhom_fun f x1)) =
                precone_scale (NngNum (ltW x1n_pos)) precone_zero.
      by rewrite /linhom_fun in Hsc; rewrite Hsc.
    rewrite precone_scale_0r -precone_scale_A in step.
    have one_eq : (NngNum (ltW x1n_pos))%:num * Tinv%:num = 1.
      by rewrite /= mulfV// gt_eqF.
    have nng_eq : forall (a b : {nonneg R}), a%:num = b%:num -> a = b.
      by move=> a b /val_inj.
    have repack : ((NngNum (ltW x1n_pos))%:num * Tinv%:num)%:nng = 1%:nng.
      by apply: nng_eq => /=; rewrite one_eq.
    by rewrite repack precone_scale_1 in step.
  have [m [mM Hm]] :=
    @mcone_M_norm R Ar D (linhom_fun f x1') eps nz1' eps_pos.
  have Hpath_unit : cone_norm (const_x_path x1') <= 1.
    by rewrite /cone_norm /= const_x_path_normE.
  exists (linhom_test (const_x_path x1') Hpath_unit m mM); split.
    by exists (const_x_path x1'), Hpath_unit, m, mM.
  rewrite /linhom_test /= /linhom_test_fun /=.
  apply: le_trans norm_le_e2 _.
  have e2_le_e : eps / 2 <= eps.
    by rewrite ler_pdivrMr // ler_peMr // ?ler1n // ltW.
  apply: le_trans e2_le_e _.
  rewrite -[X in X <= _]add0r lerD //.
  exact: test_ge0.
- (* [f x0 ≠ 0]. *)
  have [m [mM Hm]] :=
    @mcone_M_norm R Ar D (linhom_fun f x0) (eps / 2) nez eps2_pos.
  have Hpath_unit : cone_norm (const_x_path x0) <= 1.
    by rewrite /cone_norm /= const_x_path_normE.
  exists (linhom_test (const_x_path x0) Hpath_unit m mM); split.
    by exists (const_x_path x0), Hpath_unit, m, mM.
  rewrite /linhom_test /= /linhom_test_fun /=.
  apply: le_trans HnormR _.
  apply: le_trans (lerD Hm (lexx (eps / 2))) _.
  rewrite -addrA lerD2l.
  have ->: (eps / 2 + eps / 2 = eps)%R.
    have two_ne0 : (2 : R) != 0 by rewrite pnatr_eq0.
    have step : (eps / 2 + eps / 2) * 2 = eps * 2.
      rewrite mulrDl !mulfVK //.
      by have ->: (2 = 1 + 1 :> R)%R by [];
         rewrite mulrDr mulr1.
    exact: (mulIf two_ne0 step).
  exact: lexx.
Qed.

End LinhomMCone.

(** ** [isMCone] HB instance for [linhom_car Ar C D] — Paper Def 5.4 *)

HB.instance Definition _ (R : realType) (Ar : MeasSubcat R)
    (C D : ICone.type Ar) :=
  @isMCone.Build R Ar (linhom_car Ar C D)
    (@linhom_mcone_M R Ar C D)
    (@linhom_mcone_M_comp R Ar C D)
    (@linhom_mcone_M_sep R Ar C D)
    (@linhom_mcone_M_norm R Ar C D).

(** ** Sanity check: [linhom_car Ar C D] is an [mconeType Ar] *)

Section LinhomMConeCheck.
Variables (R : realType) (Ar : MeasSubcat R).
Variables C D : ICone.type Ar.

Check (linhom_car Ar C D : mconeType Ar).

End LinhomMConeCheck.

(** ** [isICone] HB instance on [linhom_car] — Paper Lemma 5.4

    Given a measurable path [η : ar_carrier Ar Y' -> linhom_car Ar C D]
    and a finite measure [µ : fmeas R (ar_carrier Ar Y')], we build
    the pointwise integral
    [(∫η dµ)(x) := icone_integral (r ↦ linhom_fun (η r) x) ... µ]
    in [D]. We then verify that this map is itself a [linhom_car]
    (linear, ω-continuous, bounded, measurable-path-preserving,
    integral-preserving) and satisfies the Pettis equation w.r.t. the
    [linhom_test] family.

    Template: [theories/icones/examples_icone.v] lines 842–1175
    ([path_int_fun], [path_int_pt_meas], [path_int_fun_is_path],
    [path_int_exists]) for [path_car]; here we replicate it for
    [linhom_car], using Fubini ([fubini_cone_eq]) for the
    integral-preservation field. *)

Section LinhomICone.
Variables (R : realType) (Ar : MeasSubcat R).
Variables C D : ICone.type Ar.

Section LinhomIntFun.
Variable Y' : ar_obj Ar.
Variable η : ar_carrier Ar Y' -> linhom_car Ar C D.
Hypothesis Hη : is_measurable_path η.
Variable µ : fmeas R (ar_carrier Ar Y').

(** Paper Lemma 5.4: at each [x : C], the function
    [r ↦ linhom_fun (η r) x] is a measurable path of [D].
    The cone-norm bound follows from boundedness of each [η r]
    (uniform via [Hη]'s norm bound); the joint test-measurability
    follows from (Msmeas) on [η] applied to the rescaled constant
    test [linhom_test (const_x_path_arity Z x') γub m_D mM_D]. *)
Lemma linhom_int_pt_meas (x : C) :
  is_measurable_path (fun r : ar_carrier Ar Y' => linhom_fun (η r) x).
Proof.
have [[Mη HMη] Hη_meas] := Hη.
split.
  exists (Mη * (cone_norm x)) => r.
  apply: le_trans (linhom_norm_apply_le _ _) _.
  - exact: HMη.
  - exact: lexx.
move=> Z m_D mM_D.
(* Rescale [x] to the unit ball: [x' := (cnorm x + 1)^-1 *: x]. *)
have S_pos : 0 < cone_norm x + 1 by exact: cnorm_succ_pos.
have Sinv_ge0 : 0 <= (cone_norm x + 1)^-1 by rewrite invr_ge0 ltW.
pose Sinv : {nonneg R} := NngNum Sinv_ge0.
have Sinv_pos : 0 < Sinv%:num by rewrite /= invr_gt0.
have Sinv_neq0 : Sinv%:num != 0 by rewrite gt_eqF.
pose x' : C := precone_scale Sinv x.
have Hx'_unit : cone_norm x' <= 1.
  rewrite /x' cone_normh /=.
  rewrite mulrC ler_pdivrMr // mul1r.
  by rewrite -[X in X <= _]addr0 lerD2l ler01.
have Hγx'_unit : cone_norm (const_x_path_arity Z x') <= 1.
  by rewrite /cone_norm /= const_x_path_arity_normE.
(* Apply (Msmeas) on η at the linhom test [γ_{x'} ▷ m_D]. *)
have Hmeas_xprime :
  measurable_fun setT
    (fun p => m_D p.1 (linhom_fun (η p.2) x')).
  have HinM : linhom_mcone_M (Y:=Z)
    (linhom_test (const_x_path_arity Z x') Hγx'_unit m_D mM_D).
    by exists (const_x_path_arity Z x'), Hγx'_unit, m_D, mM_D.
  have Hη' := Hη_meas Z _ HinM.
  apply: (eq_measurable_fun
    (fun p => linhom_test (const_x_path_arity Z x') Hγx'_unit m_D mM_D
                p.1 (η p.2))).
    by move=> p _; rewrite /linhom_test /= /linhom_test_fun /=.
  exact: Hη'.
(* Now use linearity of [linhom_fun (η r)]: x' = Sinv *: x. *)
have Heq : forall (z : ar_carrier Ar Z) (r : ar_carrier Ar Y'),
    m_D z (linhom_fun (η r) x') =
    Sinv%:num * m_D z (linhom_fun (η r) x).
  move=> z r.
  have [_ _ HfZ] := linhom_pre_linear (linhom_pre_of (η r)).
  by rewrite /x' /linhom_fun HfZ test_linZ.
(* Multiply by [(cnorm x + 1) = Sinv⁻¹] to recover the unscaled fn. *)
apply: (eq_measurable_fun
  (fun p : ar_carrier Ar Z * ar_carrier Ar Y' =>
    Sinv%:num^-1 * m_D p.1 (linhom_fun (η p.2) x'))).
  move=> p _ /=.
  by rewrite Heq mulrA mulVf // mul1r.
have Hmul : measurable_fun setT ( *%R Sinv%:num^-1).
  exact: mulrl_measurable.
have step : (fun p : ar_carrier Ar Z * ar_carrier Ar Y' =>
   Sinv%:num^-1 * m_D p.1 (linhom_fun (η p.2) x')) =
  *%R Sinv%:num^-1 \o
  (fun p : ar_carrier Ar Z * ar_carrier Ar Y' =>
    m_D p.1 (linhom_fun (η p.2) x')).
  by apply: funext.
by rewrite step; exact: (measurableT_comp Hmul Hmeas_xprime).
Qed.

(** Paper Lemma 5.4: the pointwise integral as a function [C -> D]. *)
Definition linhom_int_fun (x : C) : D :=
  icone_integral (fun r => linhom_fun (η r) x) (linhom_int_pt_meas x) µ.

(** Paper Lemma 5.4: boundedness — operator-norm bound.
    [cnorm (linhom_int_fun x) ≤ ‖η‖ · ‖µ‖] when [‖x‖ ≤ 1], via
    [path_integral_norm_le]. *)
Lemma linhom_int_fun_bounded :
  exists M : R, forall x : C, cnorm x <= 1 ->
  cnorm (linhom_int_fun x) <= M.
Proof.
have [[Mη HMη] _] := Hη.
have Mη_ge0 : 0 <= Mη.
  by apply: le_trans (HMη (ar_point Ar Y')); exact: cone_norm_ge0.
exists (Mη * fmeas_norm µ) => x Hx.
apply: (path_integral_norm_le (Mβ := Mη)).
- move=> r /=.
  apply: le_trans (linhom_norm_apply_le (HMη r) x) _.
  by rewrite -[X in _ <= X]mulr1 ler_wpM2l // cone_norm_ge0.
- exact: linhom_int_pt_meas.
- exact: icone_integralP.
Qed.

(** Paper Lemma 5.4: linearity of [linhom_int_fun].
    Each [η r] is linear, hence the integrand commutes with [0], [+],
    [*:], and the [Path] bilinearity lemmas
    [path_integral_eq_addB] / [path_integral_eq_scaleB]
    promote this through [icone_integral_eqP]. *)
Lemma linhom_int_fun_linear : is_linear linhom_int_fun.
Proof.
split.
- rewrite /linhom_int_fun.
  symmetry; apply: icone_integral_eqP => m mM s /=.
  rewrite test_lin0.
  under eq_integral => r _ do (
    rewrite (_ : linhom_fun (η r) 0%PC = 0%PC); last
    by have [Hf0 _ _] := linhom_pre_linear (linhom_pre_of (η r));
       rewrite /linhom_fun Hf0).
  under eq_integral => r _ do rewrite test_lin0.
  rewrite (_ : (fun _ : ar_carrier Ar Y' => (0 : R)%:E) =
    cst 0%E :> (_ -> \bar R)); last by apply: funext.
  by rewrite integral0.
- move=> x y.
  rewrite /linhom_int_fun.
  symmetry; apply: icone_integral_eqP => m mM s.
  have HeqAdd := path_integral_eq_addB
    (linhom_int_pt_meas x) (linhom_int_pt_meas y)
    (icone_integralP _ (linhom_int_pt_meas x) µ)
    (icone_integralP _ (linhom_int_pt_meas y) µ).
  rewrite (HeqAdd m mM s).
  congr (fine _); apply: eq_integral => r _.
  congr (_)%:E.
  have [_ HfD _] := linhom_pre_linear (linhom_pre_of (η r)).
  by rewrite /linhom_fun HfD.
- move=> r x.
  rewrite /linhom_int_fun.
  symmetry; apply: icone_integral_eqP => m mM s.
  have HeqZ := path_integral_eq_scaleB r
    (linhom_int_pt_meas x)
    (icone_integralP _ (linhom_int_pt_meas x) µ).
  rewrite (HeqZ m mM s).
  congr (fine _); apply: eq_integral => u _.
  congr (_)%:E.
  have [_ _ HfZ] := linhom_pre_linear (linhom_pre_of (η u)).
  by rewrite /linhom_fun HfZ.
Qed.

(** Paper Lemma 5.4: joint test-measurability for path-preservation.
    For any [γ : ar_carrier X' -> C] measurable path and any
    [Z]-test [m_D] of [D], the function
    [(z, r, r') ↦ m_D z (linhom_fun (η r') (γ r))] is jointly
    measurable on [Z × X' × Y']. Direct analogue of
    [path_int_joint_meas] from [examples_icone.v]. *)
Lemma linhom_int_fun_joint_meas
    (X' : ar_obj Ar)
    (γ : ar_carrier Ar X' -> C) (Hγ : is_measurable_path γ)
    (Z : ar_obj Ar) (m_D : test_of Ar Z D) (mM_D : mcone_M Z m_D) :
  measurable_fun
    [set: (ar_carrier Ar Z *
           (ar_carrier Ar X' * ar_carrier Ar Y'))%type]
    (fun p => m_D p.1 (linhom_fun (η p.2.2) (γ p.2.1))).
Proof.
have [[Mγ HMγ] _] := Hγ.
have [_ Hη_meas] := Hη.
(* Rescale γ to unit-ball via [Sγ := (Mγ + 1)^-1]: γ' := Sγ *: γ. *)
have S_pos : 0 < Mγ + 1.
  rewrite ltr_pwDr // (le_trans _ (HMγ (ar_point Ar X'))) //.
  exact: cone_norm_ge0.
have Sinv_ge0 : 0 <= (Mγ + 1)^-1 by rewrite invr_ge0 ltW.
pose Sinv : {nonneg R} := NngNum Sinv_ge0.
have Sinv_pos : 0 < Sinv%:num by rewrite /= invr_gt0.
have Sinv_neq0 : Sinv%:num != 0 by rewrite gt_eqF.
pose γ' : ar_carrier Ar X' -> C :=
  fun r => precone_scale Sinv (γ r).
have Hγ'_meas : is_measurable_path γ'.
  split.
    exists 1 => r.
    rewrite /γ' cone_normh /=.
    rewrite mulrC ler_pdivrMr // mul1r.
    by apply: le_trans (HMγ _) _; rewrite lerDl ler01.
  move=> Y m mM.
  have Hgm := proj2 Hγ Y m mM.
  apply: (eq_measurable_fun (fun p => Sinv%:num * m p.1 (γ p.2))).
    by move=> p _; rewrite /γ' /= test_linZ.
  pose Fmul : R -> R := *%R Sinv%:num.
  have Hmul : measurable_fun setT Fmul.
    exact: mulrl_measurable.
  have step :
    (fun p : ar_carrier Ar Y * ar_carrier Ar X' =>
       Sinv%:num * m p.1 (γ p.2)) =
    Fmul \o (fun p => m p.1 (γ p.2)).
    by apply: funext.
  by rewrite step; exact: (measurableT_comp Hmul Hgm).
pose γ'_path : path_car Ar X' C := MkPath Hγ'_meas.
have γ'ub : cone_norm γ'_path <= 1.
  rewrite /cone_norm /= /path_norm.
  apply: ge_sup.
    by exists (cnorm (γ' (ar_point Ar X'))); exists (ar_point Ar X').
  move=> _ [r ->]; rewrite /γ' /=.
  rewrite cone_normh /=.
  rewrite mulrC ler_pdivrMr // mul1r.
  by apply: le_trans (HMγ _) _; rewrite lerDl ler01.
(* Build the test on linhom at arity [Z' = ar_prod Z X']. *)
pose ar_fst : ar_hom Ar (ar_prod Ar Z X') Z := ar_prod_fst Z X'.
pose ar_snd : ar_hom Ar (ar_prod Ar Z X') X' := ar_prod_snd Z X'.
pose mZ' : test_of Ar (ar_prod Ar Z X') D := test_reindex ar_fst m_D.
have mZ'M : mcone_M (ar_prod Ar Z X') mZ'.
  exact: mcone_M_comp.
(* Path on Z' obtained by reindexing γ' via ar_snd. *)
pose γZ'_pre : ar_carrier Ar (ar_prod Ar Z X') -> C :=
  fun z' => γ' (ar_snd z').
have γZ'_meas : is_measurable_path γZ'_pre.
  have := Hγ'_meas.
  rewrite /γZ'_pre => -[[Mγ' HMγ'] Hg'].
  split.
    by exists Mγ' => z'; exact: HMγ'.
  move=> Y m mM.
  have HgY := Hg' Y m mM.
  have Hsnd_meas : measurable_fun
    [set: ar_carrier Ar Y * ar_carrier Ar (ar_prod Ar Z X')]
    (fun p : ar_carrier Ar Y * ar_carrier Ar (ar_prod Ar Z X') =>
      (p.1, ar_snd p.2)).
    apply: measurable_fun_pair; first exact: measurable_fst.
    by apply: (measurableT_comp (f := ar_snd));
       [exact: measurable_funP|exact: measurable_snd].
  have step :
    (fun p : ar_carrier Ar Y * ar_carrier Ar (ar_prod Ar Z X') =>
       m p.1 (γ' (ar_snd p.2))) =
    (fun p => m p.1 (γ' p.2)) \o
    (fun p : ar_carrier Ar Y * ar_carrier Ar (ar_prod Ar Z X') =>
       (p.1, ar_snd p.2)).
    by apply: funext.
  by rewrite step; exact: (measurableT_comp HgY Hsnd_meas).
pose γZ'_path : path_car Ar (ar_prod Ar Z X') C := MkPath γZ'_meas.
have γZ'ub : cone_norm γZ'_path <= 1.
  rewrite /cone_norm /= /path_norm.
  apply: ge_sup.
    by exists (cnorm (γZ'_pre (ar_point Ar (ar_prod Ar Z X'))));
       exists (ar_point Ar (ar_prod Ar Z X')).
  move=> _ [z ->]; rewrite /γZ'_pre /γ' /=.
  rewrite cone_normh /=.
  rewrite mulrC ler_pdivrMr // mul1r.
  by apply: le_trans (HMγ _) _; rewrite lerDl ler01.
(* The linhom test at arity Z'. *)
have HinM : linhom_mcone_M
  (linhom_test γZ'_path γZ'ub mZ' mZ'M).
  by exists γZ'_path, γZ'ub, mZ', mZ'M.
(* Apply (Msmeas) on η at this test. *)
have Hη' := Hη_meas (ar_prod Ar Z X') _ HinM.
(* Hη' gives joint measurability on Z' × Y'. *)
(* Cast Z × X' × Y' through ar_prod_cast. *)
pose ψ (p : (ar_carrier Ar Z *
             (ar_carrier Ar X' * ar_carrier Ar Y'))%type) :
    (ar_carrier Ar (ar_prod Ar Z X') * ar_carrier Ar Y')%type :=
  (ar_prod_cast (p.1, p.2.1), p.2.2).
have ψ_meas : measurable_fun
    [set: (ar_carrier Ar Z *
           (ar_carrier Ar X' * ar_carrier Ar Y'))%type] ψ.
  rewrite /ψ.
  apply: measurable_fun_pair.
  - have meas_p12 : measurable_fun setT
        (fun p : ar_carrier Ar Z *
                (ar_carrier Ar X' * ar_carrier Ar Y') => (p.1, p.2.1)).
      apply: measurable_fun_pair.
      + exact: measurable_fst.
      + by apply: (measurableT_comp (f := fst));
          [exact: measurable_fst|exact: measurable_snd].
    exact: (measurableT_comp (ar_prod_cast_meas Ar Z X') meas_p12).
  - by apply: (measurableT_comp (f := snd));
      [exact: measurable_snd|exact: measurable_snd].
(* Show the relation between the integrand and the test composition. *)
have eqψ_unscaled :
    forall p : ar_carrier Ar Z *
               (ar_carrier Ar X' * ar_carrier Ar Y'),
  Sinv%:num * m_D p.1 (linhom_fun (η p.2.2) (γ p.2.1)) =
  (fun q => linhom_test γZ'_path γZ'ub mZ' mZ'M q.1 (η q.2)) (ψ p).
  move=> p.
  rewrite /linhom_test /linhom_test_fun /= /γZ'_pre /γ' /=.
  rewrite /ψ /=.
  rewrite /ar_snd /ar_prod_snd /ar_prod_snd_fun.
  rewrite ar_prod_castK.
  rewrite /mZ' /test_reindex /test_reindex_fun /=.
  rewrite /ar_fst /ar_prod_fst /ar_prod_fst_fun.
  rewrite ar_prod_castK.
  have [_ _ HfZ] := linhom_pre_linear (linhom_pre_of (η p.2.2)).
  by rewrite /linhom_fun HfZ test_linZ.
(* Compose: measurability via ψ. *)
have Hmeas_scaled : measurable_fun
    [set: (ar_carrier Ar Z *
           (ar_carrier Ar X' * ar_carrier Ar Y'))%type]
    (fun p => Sinv%:num *
                m_D p.1 (linhom_fun (η p.2.2) (γ p.2.1))).
  apply: (eq_measurable_fun (fun p =>
    (fun q : ar_carrier Ar (ar_prod Ar Z X') * ar_carrier Ar Y' =>
       linhom_test γZ'_path γZ'ub mZ' mZ'M q.1 (η q.2)) (ψ p))).
    by move=> p _; rewrite -eqψ_unscaled.
  exact: (measurableT_comp Hη' ψ_meas).
(* Unscale by multiplying by Sinv^-1. *)
apply: (eq_measurable_fun (fun p =>
  Sinv%:num^-1 *
    (Sinv%:num * m_D p.1 (linhom_fun (η p.2.2) (γ p.2.1))))).
  move=> p _ /=.
  by rewrite mulrA mulVf // mul1r.
have Hmul : measurable_fun setT ( *%R Sinv%:num^-1).
  exact: mulrl_measurable.
have step :
  (fun p : ar_carrier Ar Z *
           (ar_carrier Ar X' * ar_carrier Ar Y') =>
   Sinv%:num^-1 *
   (Sinv%:num * m_D p.1 (linhom_fun (η p.2.2) (γ p.2.1)))) =
  *%R Sinv%:num^-1 \o
  (fun p => Sinv%:num *
              m_D p.1 (linhom_fun (η p.2.2) (γ p.2.1))).
  by apply: funext.
by rewrite step; exact: (measurableT_comp Hmul Hmeas_scaled).
Qed.

(** Paper Lemma 5.4: path-preservation.
    For every measurable path [γ : ar_carrier X' -> C], the function
    [r ↦ linhom_int_fun (γ r) : ar_carrier X' -> D] is a measurable
    path of [D]. Proof: it equals [fubini_iter_fun_X β' _ µ] for
    [β'(r, r') := linhom_fun (η r') (γ r)], to which we apply
    [fubini_iter_fun_X_is_path]. *)
Lemma linhom_int_fun_pres_path
    (X' : ar_obj Ar) (γ : ar_carrier Ar X' -> C) :
  is_measurable_path γ ->
  is_measurable_path (fun r => linhom_int_fun (γ r)).
Proof.
move=> Hγ.
have [[Mγ HMγ] _] := Hγ.
have [[Mη HMη] _] := Hη.
have Mη_ge0 : 0 <= Mη.
  by apply: le_trans (HMη (ar_point Ar Y')); exact: cone_norm_ge0.
have Mγ_ge0 : 0 <= Mγ.
  by apply: le_trans (HMγ (ar_point Ar X')); exact: cone_norm_ge0.
(* Define the bivariate path [β'(r, r') := linhom_fun (η r') (γ r)]. *)
pose β' : (ar_carrier Ar X' * ar_carrier Ar Y') -> D :=
  fun p => linhom_fun (η p.2) (γ p.1).
have Hβ'x : forall r, is_measurable_path (fun r' => β' (r, r')).
  move=> r; rewrite /β' /=.
  exact: (linhom_int_pt_meas (γ r)).
have HMβ' : forall p, cnorm (β' p) <= Mη * Mγ.
  move=> p.
  apply: le_trans (linhom_norm_apply_le (HMη p.2) (γ p.1)) _.
  by apply: ler_wpM2l => //; exact: HMγ.
have HjointX :
    forall (Z : ar_obj Ar) (m : test_of Ar Z D),
      mcone_M Z m ->
      measurable_fun
        [set: (ar_carrier Ar Z *
               (ar_carrier Ar X' * ar_carrier Ar Y'))%type]
        (fun p => m p.1 (β' (p.2.1, p.2.2))).
  move=> Z m mM.
  exact: linhom_int_fun_joint_meas.
have HrwE : (fun r => linhom_int_fun (γ r)) =
  fubini_iter_fun_X β' Hβ'x µ.
  apply: funext => r.
  rewrite /linhom_int_fun /fubini_iter_fun_X.
  apply: icone_integral_eqP.
  exact: icone_integralP.
rewrite HrwE.
exact: (fubini_iter_fun_X_is_path β' Hβ'x µ (Mη * Mγ) HMβ' HjointX).
Qed.

(** Paper Lemma 5.4: ω-continuity of [linhom_int_fun].
    Direct adaptation of [linhom_sup_fun_pres_int]: use [mcone_M_sep]
    on [D], rewrite both sides via [icone_integralP] and a
    sup-of-tests identity, and conclude by monotone convergence
    (Lebesgue MCT). *)
Lemma linhom_int_fun_continuous : is_omega_continuous linhom_int_fun.
Proof.
move=> u uch ub1 fuch fub1.
have [[Mη HMη] _] := Hη.
have Mη_ge0 : 0 <= Mη.
  by apply: le_trans (HMη (ar_point Ar Y')); exact: cone_norm_ge0.
(* Mssep reduction. *)
apply: mcone_M_sep => m mM.
set s0 := ar_zero_pt Ar.
(* Pointwise test chain in C → D. *)
pose b' (n : nat) (r : ar_carrier Ar Y') : D :=
  linhom_fun (η r) (u n).
have b'_ch : forall n r, (b' n r <=p b' n.+1 r)%PC.
  move=> n r; rewrite /b'.
  have [_ HfD _] := linhom_pre_linear (linhom_pre_of (η r)).
  have [z Hz] := uch n.
  exists (linhom_fun (η r) z).
  by rewrite -HfD -Hz.
have b'_meas : forall n,
  is_measurable_path (b' n) by move=> n; exact: linhom_int_pt_meas.
(* Pointwise test as ereal chain. *)
pose un_e (n : nat) (r : ar_carrier Ar Y') : \bar R :=
  (test_fun m s0 (b' n r))%:E.
pose fsup_e (r : ar_carrier Ar Y') : \bar R :=
  (test_fun m s0 (linhom_fun (η r) (cone_sup_ball u uch ub1)))%:E.
have un_meas : forall n,
    measurable_fun setT (un_e n).
  move=> n; apply/measurable_EFinP.
  exact: (measurable_test_path_section mM (b'_meas n) s0).
have un_ge0 : forall n r, (0 <= un_e n r)%E.
  by move=> n r; rewrite /un_e lee_fin; exact: test_ge0.
have un_homo : forall r,
    {homo (un_e^~ r) : n m0 / (n <= m0)%N >-> (n <= m0)%E}.
  move=> r; apply/nondecreasing_seqP => n.
  rewrite /un_e lee_fin.
  exact: (test_fun_le m s0 (b'_ch n r)).
(* The pointwise function value [linhom_fun (η r) (cone_sup_ball u ...)]
   admits the test_sup identity: m s (cone_sup_ball b ...) = sup_n m s (b_n)
   via [test_cont] + [test_fun_le] + [cone_sup_ball_ub]. *)
have linhom_test_sup_pt :
    forall r,
    test_fun m s0 (linhom_fun (η r) (cone_sup_ball u uch ub1)) =
    sup [set test_fun m s0 (b' n r) | n in [set: nat]].
  move=> r.
  set v : nat -> R := fun n => test_fun m s0 (b' n r).
  have nonempty : (range v) !=set0.
    by exists (v 0%N), 0%N.
  have v_le :
      forall n,
        v n <= test_fun m s0 (linhom_fun (η r) (cone_sup_ball u uch ub1)).
    move=> n; rewrite /v.
    apply: test_fun_le.
    have [z Hz] := cone_sup_ball_ub u uch ub1 n.
    have [_ HfD _] := linhom_pre_linear (linhom_pre_of (η r)).
    exists (linhom_fun (η r) z).
    by rewrite /b' -HfD -Hz.
  have ub_v : has_ubound (range v).
    by exists (test_fun m s0 (linhom_fun (η r) (cone_sup_ball u uch ub1)));
      move=> _ [n _ <-]; exact: v_le.
  (* Rescale η r to the unit ball via Sinv := (Mη + 1)^-1. *)
  have S_pos : 0 < Mη + 1.
    by rewrite ltr_pwDr // ltr01.
  have Sinv_ge0 : 0 <= (Mη + 1)^-1 by rewrite invr_ge0 ltW.
  pose Sinv : {nonneg R} := NngNum Sinv_ge0.
  have Sinv_pos : 0 < Sinv%:num by rewrite /= invr_gt0.
  have Sinv_neq0 : Sinv%:num != 0 by rewrite gt_eqF.
  pose η_resc : linhom_car Ar C D := linhom_scale Sinv (η r).
  have η_resc_norm : linhom_norm η_resc <= 1.
    rewrite linhom_normh /=.
    rewrite mulrC ler_pdivrMr // mul1r.
    by apply: le_trans (HMη r) _; rewrite lerDl ler01.
  pose b_resc (n : nat) : D := linhom_fun η_resc (u n).
  have b_resc_eq : forall n, b_resc n = precone_scale Sinv (b' n r).
    by [].
  have b_resc_ch : forall n, (b_resc n <=p b_resc n.+1)%PC.
    move=> n; rewrite /b_resc.
    have [_ HfD _] := linhom_pre_linear (linhom_pre_of η_resc).
    have [z Hz] := uch n.
    exists (linhom_fun η_resc z).
    by rewrite -HfD -Hz.
  have b_resc_ub : forall n, cnorm (b_resc n) <= 1.
    move=> n; rewrite /b_resc.
    apply: le_trans (linhom_norm_apply_le η_resc_norm (u n)) _.
    by rewrite mul1r; exact: ub1.
  pose w := cone_sup_ball u uch ub1.
  have ω_resc :
    linhom_fun η_resc w = cone_sup_ball b_resc b_resc_ch b_resc_ub.
    exact: (linhom_pre_continuous (linhom_pre_of η_resc) u uch ub1
              b_resc_ch b_resc_ub).
  have lhs_eq :
    linhom_fun η_resc w = precone_scale Sinv (linhom_fun (η r) w).
    by rewrite /η_resc /linhom_scale /linhom_scale_fun /linhom_fun /=.
  have test_resc :
    Sinv%:num * test_fun m s0 (linhom_fun (η r) w) =
    test_fun m s0 (cone_sup_ball b_resc b_resc_ch b_resc_ub).
    by rewrite -test_linZ -lhs_eq ω_resc.
  apply: le_anti; apply/andP; split; last first.
    apply: ge_sup => //.
    by move=> _ [n _ <-]; exact: v_le.
  (* Multiply both sides by Sinv > 0 (preserves order). *)
  rewrite -(@ler_pM2l _ Sinv%:num) // [Sinv%:num * sup _]mulrC.
  rewrite test_resc.
  apply: test_cont => n.
  rewrite (b_resc_eq n) test_linZ -[X in X <= _]mulrC.
  rewrite ler_pM2r //.
  by apply: sup_upper_bound; [split => //|exists n].
have un_cvg_R : forall r,
  (fun n => test_fun m s0 (b' n r)) x @[x --> \oo] -->
  (test_fun m s0 (linhom_fun (η r) (cone_sup_ball u uch ub1)) : R^o).
  move=> r.
  pose v (n : nat) := test_fun m s0 (b' n r).
  have nd_v : nondecreasing_seq v.
    apply/nondecreasing_seqP => n; rewrite /v.
    exact: (test_fun_le m s0 (b'_ch n r)).
  have ub_v : has_ubound (range v).
    exists (cnorm (linhom_fun (η r) (cone_sup_ball u uch ub1))) =>
      _ [n _ <-]; rewrite /v.
    apply: le_trans (test_norm_le _ _ _) _.
    have [_ HfD _] := linhom_pre_linear (linhom_pre_of (η r)).
    have Hpt :
      (linhom_fun (η r) (u n) <=p
       linhom_fun (η r) (cone_sup_ball u uch ub1))%PC.
      have [z Hz] := cone_sup_ball_ub u uch ub1 n.
      exists (linhom_fun (η r) z).
      by rewrite -HfD -Hz.
    exact: cone_normp Hpt.
  have sup_eq :
    sup (range v) =
    test_fun m s0 (linhom_fun (η r) (cone_sup_ball u uch ub1)).
    by rewrite -linhom_test_sup_pt.
  rewrite -sup_eq.
  exact: nondecreasing_cvgn.
have un_cvg : forall r, (un_e^~ r) x @[x --> \oo] --> fsup_e r.
  move=> r; rewrite /un_e /fsup_e.
  apply: cvg_EFin; first by apply: nearW => n; rewrite fin_numE.
  exact: un_cvg_R.
have un_lim : forall r, limn (un_e^~ r) = fsup_e r.
  by move=> r; apply/cvg_lim => //; exact: ereal_hausdorff.
have meas_fsup : measurable_fun setT fsup_e.
  apply/measurable_EFinP.
  have Hpath :
    is_measurable_path (fun r =>
      linhom_fun (η r) (cone_sup_ball u uch ub1)).
    exact: (linhom_int_pt_meas (cone_sup_ball u uch ub1)).
  exact: (measurable_test_path_section mM Hpath s0).
(* Bounds and finiteness. *)
have un_bound_M : forall n r, (un_e n r <= Mη%:E)%E.
  move=> n r; rewrite /un_e /b' lee_fin.
  apply: le_trans (test_norm_le _ _ _) _.
  apply: le_trans (linhom_norm_apply_le (HMη r) (u n)) _.
  by rewrite -[X in _ <= X]mulr1; apply: ler_wpM2l => //; exact: ub1.
have fsup_bound : forall r, (fsup_e r <= Mη%:E)%E.
  move=> r; rewrite /fsup_e lee_fin.
  apply: le_trans (test_norm_le _ _ _) _.
  apply: le_trans
    (linhom_norm_apply_le (HMη r) (cone_sup_ball u uch ub1)) _.
  by rewrite -[X in _ <= X]mulr1; apply: ler_wpM2l => //;
    exact: cone_sup_ball_norm.
have fmeas_setT_fin' : fmeas_mu µ [set: ar_carrier Ar Y'] \is a fin_num.
  exact: fmeas_setT_fin.
have un_int_fin : forall n,
    (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar Y']) un_e n r)%E \is a fin_num.
  move=> n.
  rewrite ge0_fin_numE //; last first.
    by apply: integral_ge0 => r _; exact: un_ge0.
  apply: (@le_lt_trans _ _
    (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar Y']) Mη%:E)%E); last first.
    rewrite (_ : (fun _ => Mη%:E) = cst Mη%:E)//.
    rewrite integral_cst//.
    by rewrite ltey_eq fin_numM.
  apply: (@ge0_le_integral _ _ R (fmeas_mu µ) _ measurableT
            (un_e n) (cst Mη%:E)).
    by move=> r _; exact: un_ge0.
    exact: un_meas.
    by apply: measurable_cst.
  by move=> r _; exact: un_bound_M.
have fsup_int_fin :
    (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar Y']) fsup_e r)%E \is a fin_num.
  rewrite ge0_fin_numE //; last first.
    apply: integral_ge0 => r _; rewrite /fsup_e lee_fin; exact: test_ge0.
  apply: (@le_lt_trans _ _
    (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar Y']) Mη%:E)%E); last first.
    rewrite (_ : (fun _ => Mη%:E) = cst Mη%:E)//.
    rewrite integral_cst//.
    by rewrite ltey_eq fin_numM.
  apply: (@ge0_le_integral _ _ R (fmeas_mu µ) _ measurableT
            fsup_e (cst Mη%:E)).
    by move=> r _; rewrite /fsup_e lee_fin; exact: test_ge0.
    exact: meas_fsup.
    by apply: measurable_cst.
  by move=> r _; exact: fsup_bound.
(* Pettis spec at u_n: m s0 (linhom_int_fun (u n)) = fine ∫ ... *)
have un_pet : forall n,
    test_fun m s0 (linhom_int_fun (u n)) =
    fine (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar Y'])
            (test_fun m s0 (b' n r))%:E).
  move=> n.
  rewrite /linhom_int_fun.
  exact: icone_integralP.
(* Pettis spec at cone_sup_ball u: m s0 (linhom_int_fun (cone_sup_ball u)) = fine ∫ ... *)
have fsup_pet :
    test_fun m s0 (linhom_int_fun (cone_sup_ball u uch ub1)) =
    fine (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar Y']) fsup_e r).
  rewrite /linhom_int_fun.
  exact: icone_integralP.
(* Goal: test_fun m s0 (linhom_int_fun (cone_sup_ball u uch ub1)) =
        test_fun m s0 (cone_sup_ball (linhom_int_fun \o u) fuch fub1).  *)
rewrite fsup_pet.
(* The test of the right sup-ball = sup of tests. *)
have rhs_sup_eq :
    test_fun m s0 (cone_sup_ball (linhom_int_fun \o u) fuch fub1) =
    sup [set test_fun m s0 (linhom_int_fun (u n)) | n in [set: nat]].
  set v : nat -> R := fun n => test_fun m s0 (linhom_int_fun (u n)).
  have ub_v : has_ubound (range v).
    exists 1 => _ [n _ <-]; rewrite /v.
    by apply: test_le1; exact: fub1.
  have nonempty : (range v) !=set0.
    by exists (v 0%N), 0%N.
  apply: le_anti; apply/andP; split.
    apply: test_cont => n.
    apply: sup_upper_bound; first by split.
    by exists n.
  apply: ge_sup => //.
  move=> _ [n _ <-]; rewrite /v.
  apply: test_fun_le.
  exact: cone_sup_ball_ub.
rewrite rhs_sup_eq.
(* MCT-based identity: sup_n fine (∫ un_e n) = fine (∫ fsup_e). *)
have nd_pet : nondecreasing_seq
    (fun n => test_fun m s0 (linhom_int_fun (u n))).
  apply/nondecreasing_seqP => n; rewrite /=.
  apply: test_fun_le.
  exact: fuch.
have ub_pet : has_ubound
    (range (fun n => test_fun m s0 (linhom_int_fun (u n)))).
  by exists 1 => _ [n _ <-]; apply: test_le1; exact: fub1.
have hint_cvg :
    (fun n => test_fun m s0 (linhom_int_fun (u n))) x @[x --> \oo] -->
    (fine (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar Y']) fsup_e r) : R^o).
  have HCMu :=
    cvg_monotone_convergence (D := [set: ar_carrier Ar Y'])
      (mu := fmeas_mu µ) measurableT un_meas
      (fun n r _ => un_ge0 n r) (fun r _ => un_homo r).
  have HE :
    (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar Y'])
        (fun x : ar_carrier Ar Y' => limn (un_e^~ x)) r)%E =
    (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar Y']) fsup_e r)%E.
    by apply: eq_integral => r _; rewrite -un_lim.
  have e_cvg :
    (fun n => (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar Y']) un_e n r)%E)
      x @[x --> \oo] -->
    (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar Y']) fsup_e r)%E.
    by rewrite -HE.
  have HEFin :
    (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar Y']) fsup_e r)%E =
    (fine (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar Y']) fsup_e r))%:E.
    by rewrite fineK.
  rewrite HEFin in e_cvg.
  have fcvg : (fun n =>
      fine ((\int[fmeas_mu µ]_(r in [set: ar_carrier Ar Y']) un_e n r)%E)) x
    @[x --> \oo] --> (fine (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar Y'])
                            fsup_e r) : R^o).
    by have := fine_cvg e_cvg; exact.
  have heq : (fun n =>
      fine ((\int[fmeas_mu µ]_(r in [set: ar_carrier Ar Y']) un_e n r)%E))
    = (fun n => test_fun m s0 (linhom_int_fun (u n))).
    by apply: funext => n; rewrite un_pet.
  by rewrite heq in fcvg; exact: fcvg.
have hint_sup_eq :
    sup [set test_fun m s0 (linhom_int_fun (u n)) | n in [set: nat]] =
    fine (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar Y']) fsup_e r).
  have nd_cvg := nondecreasing_cvgn nd_pet ub_pet.
  exact: (@cvg_unique R^o (@Rhausdorff R) _ _ _ _ nd_cvg hint_cvg).
by rewrite hint_sup_eq.
Qed.

(** Paper Lemma 5.4: integral-preservation, via Fubini.
    Given [β : ar_carrier X' -> C] measurable path and [ν :
    fmeas X'], we have
    [linhom_int_fun η µ (∫ β dν) = ∫ (linhom_int_fun η µ ∘ β) dν]
    by [fubini_cone_eq] applied to the bivariate path
    [(r, r') ↦ linhom_fun (η r') (β r)] with measures [(ν, µ)]. *)
Lemma linhom_int_fun_pres_int
    (X' : ar_obj Ar)
    (β : ar_carrier Ar X' -> C) (Hβ : is_measurable_path β)
    (ν : fmeas R (ar_carrier Ar X')) :
  linhom_int_fun (icone_integral β Hβ ν) =
  icone_integral (fun r => linhom_int_fun (β r))
    (linhom_int_fun_pres_path Hβ) ν.
Proof.
have [[Mβ HMβ] _] := Hβ.
have [[Mη HMη] _] := Hη.
have Mη_ge0 : 0 <= Mη.
  by apply: le_trans (HMη (ar_point Ar Y')); exact: cone_norm_ge0.
have Mβ_ge0 : 0 <= Mβ.
  by apply: le_trans (HMβ (ar_point Ar X')); exact: cone_norm_ge0.
(* Bivariate function with X = X' and Y = Y'. *)
pose β2 : (ar_carrier Ar X' * ar_carrier Ar Y') -> D :=
  fun p => linhom_fun (η p.2) (β p.1).
have HMβ2 : forall p, cnorm (β2 p) <= Mη * Mβ.
  move=> p.
  apply: le_trans (linhom_norm_apply_le (HMη p.2) (β p.1)) _.
  by apply: ler_wpM2l => //; exact: HMβ.
have Hβ2x : forall r, is_measurable_path (fun r' => β2 (r, r')).
  move=> r; rewrite /β2 /=.
  exact: (linhom_int_pt_meas (β r)).
have Hβ2y : forall r', is_measurable_path (fun r => β2 (r, r')).
  move=> r' /=.
  exact: (linhom_pre_pres_path (linhom_pre_of (η r')) X' β Hβ).
have HjointX :
    forall (Z : ar_obj Ar) (m : test_of Ar Z D),
      mcone_M Z m ->
      measurable_fun
        [set: (ar_carrier Ar Z *
               (ar_carrier Ar X' * ar_carrier Ar Y'))%type]
        (fun p => m p.1 (β2 (p.2.1, p.2.2))).
  move=> Z m mM.
  exact: linhom_int_fun_joint_meas.
have HjointY :
    forall (Z : ar_obj Ar) (m : test_of Ar Z D),
      mcone_M Z m ->
      measurable_fun
        [set: (ar_carrier Ar Z *
               (ar_carrier Ar Y' * ar_carrier Ar X'))%type]
        (fun p => m p.1 (β2 (p.2.2, p.2.1))).
  move=> Z m mM.
  pose ψ (p : (ar_carrier Ar Z *
               (ar_carrier Ar Y' * ar_carrier Ar X'))%type) :
       (ar_carrier Ar Z *
        (ar_carrier Ar X' * ar_carrier Ar Y'))%type :=
    (p.1, (p.2.2, p.2.1)).
  have ψ_meas : measurable_fun
    [set: (ar_carrier Ar Z *
           (ar_carrier Ar Y' * ar_carrier Ar X'))%type] ψ.
    rewrite /ψ.
    apply: measurable_fun_pair; first exact: measurable_fst.
    apply: measurable_fun_pair.
    - by apply: (measurableT_comp (f := snd));
        [exact: measurable_snd|exact: measurable_snd].
    - by apply: (measurableT_comp (f := fst));
        [exact: measurable_fst|exact: measurable_snd].
  have HX := linhom_int_fun_joint_meas Hβ mM.
  exact: (measurableT_comp HX ψ_meas).
have HFub := fubini_cone_eq β2 (Mη * Mβ) HMβ2 Hβ2x Hβ2y ν µ HjointX HjointY.
(* HFub: icone_integral (fubini_path_X β2 µ) ... ν
       = icone_integral (fubini_path_Y β2 ν) ... µ. *)
(* fubini_path_X r = icone_integral (r' ↦ β2 (r, r')) ... µ
                   = icone_integral (r' ↦ linhom_fun (η r') (β r)) ... µ
                   = linhom_int_fun (β r). *)
(* fubini_path_Y r' = icone_integral (r ↦ β2 (r, r')) ... ν
                    = icone_integral (r ↦ linhom_fun (η r') (β r)) ... ν
                    = linhom_fun (η r') (icone_integral β Hβ ν)
                      (by linhom_pres_int of (η r')). *)
have LHS_eq : icone_integral (fubini_path_X β2 µ)
    (fubini_path_X_meas β2 (Mη * Mβ) HMβ2 Hβ2x µ HjointX) ν =
  icone_integral (fun r => linhom_int_fun (β r))
    (linhom_int_fun_pres_path Hβ) ν.
  apply: icone_integral_eqP.
  move=> m mM s.
  have HfubP := @icone_integralP R Ar D X' (fubini_path_X β2 µ) _ ν m mM s.
  rewrite HfubP.
  congr (fine _); apply: eq_integral => r _.
  congr (_)%:E.
  rewrite /fubini_path_X /fubini_iter_fun_X /β2 /linhom_int_fun /=.
  congr (test_fun m s _).
  apply: icone_integral_eqP.
  exact: icone_integralP.
have RHS_eq : icone_integral (fubini_path_Y β2 ν)
    (fubini_path_Y_meas β2 (Mη * Mβ) HMβ2 Hβ2y ν HjointY) µ =
  linhom_int_fun (icone_integral β Hβ ν).
  apply: icone_integral_eqP.
  move=> m mM s.
  have HP :=
    icone_integralP (fubini_path_Y β2 ν)
      (fubini_path_Y_meas β2 (Mη * Mβ) HMβ2 Hβ2y ν HjointY) µ m mM s.
  rewrite HP.
  congr (fine _); apply: eq_integral => r' _.
  congr (_)%:E.
  rewrite /fubini_path_Y /fubini_iter_fun_Y /β2 /=.
  have Hηr'_pres :=
    linhom_pres_int (η r') X' β Hβ ν.
  rewrite /linhom_fun.
  rewrite Hηr'_pres.
  congr (test_fun m s _).
  apply: icone_integral_eqP.
  exact: icone_integralP.
by rewrite -RHS_eq -HFub LHS_eq.
Qed.

(** Pre-carrier packaging for the integral [linhom_int_fun]. *)
Definition linhom_int_pre : linhom_pre Ar C D :=
  MkLinhomPre linhom_int_fun
    linhom_int_fun_linear linhom_int_fun_continuous
    linhom_int_fun_bounded linhom_int_fun_pres_path.

(** Full [linhom_car] for the integral. *)
Definition linhom_int_car : linhom_car Ar C D :=
  MkLinhom linhom_int_pre linhom_int_fun_pres_int.

(** Paper Lemma 5.4: the Pettis equation in [linhom_car].

    For every test [p] in the [linhom_test] family at arity 0
    (i.e., [p = γ ▷ m] for some [γ : path_car Ar 0 C], [γub ≤ 1],
    [m : test_of 0 D], [m ∈ M^D_0]), the test value of
    [linhom_int_car] at [s] equals the integral over [µ] of the
    test values of [η r] at [s]. *)
Lemma linhom_int_car_pettis :
  path_integral_eq η µ linhom_int_car.
Proof.
move=> p pM s.
case: pM => γ [γub [m [mM ->]]].
rewrite /linhom_test /= /linhom_test_fun /=.
rewrite (ar_zero_ptE s).
(* The test body is [m _ (linhom_fun linhom_int_car (path_fun γ _))],
   which equals [m _ (linhom_int_fun (path_fun γ _))]. By Pettis on
   D (icone_integralP) at the path [r ↦ linhom_fun (η r) (path_fun γ _)],
   this equals [fine (∫ m _ (linhom_fun (η r) (path_fun γ _)) dµ)]. *)
have HP := icone_integralP
  (fun r => linhom_fun (η r) (path_fun γ (ar_zero_pt Ar)))
  (linhom_int_pt_meas (path_fun γ (ar_zero_pt Ar))) µ m mM (ar_zero_pt Ar).
by rewrite -HP.
Qed.

End LinhomIntFun.

(** Paper Lemma 5.4: existence of the path integral for [linhom_car]. *)
Lemma linhom_int_exists
    (Y' : ar_obj Ar)
    (η : ar_carrier Ar Y' -> linhom_car Ar C D)
    (Hη : is_measurable_path η)
    (µ : fmeas R (ar_carrier Ar Y')) :
  is_path_integrable η µ.
Proof.
exists (linhom_int_car Hη µ).
exact: linhom_int_car_pettis.
Qed.

End LinhomICone.

(** ** [isICone] HB instance for [linhom_car Ar C D] — Paper Lemma 5.4 *)

HB.instance Definition _ (R : realType) (Ar : MeasSubcat R)
    (C D : ICone.type Ar) :=
  @isICone.Build R Ar (linhom_car Ar C D) (@linhom_int_exists R Ar C D).

(** ** Sanity check: [linhom_car Ar C D] is an [iconeType Ar] *)

Section LinhomIConeCheck.
Variables (R : realType) (Ar : MeasSubcat R).
Variables C D : ICone.type Ar.

Check (linhom_car Ar C D : iconeType Ar).

End LinhomIConeCheck.

(** ** Cone-norm construction recap — Paper §5.1

    The previous block assembles [linhom_norm] as the canonical
    real-valued [sup] over the image norm-set, the four cone-norm
    axioms (Normh/Normz/Normt/Normp), and the [linhom_sup_fun]
    sup-of-chain construction together with its linearity / scaling /
    additivity / norm-bound lemmas.  These pieces feed the [isCone]
    HB instance registered earlier in this file. *)

(** ** Paper §5.2 / Def 5.6 — Bilinear maps and the [linhom] bijection

    A *bilinear integrable map* [f : C1 × C2 → D] is the same data
    as a morphism-like map [F : C1 → C2 ⊸ D].  We deliver the
    bijection at the function level. The paper's Def 5.6 elaborates
    that the integrable bilinear maps [C1, C2 ⊸ D] form the
    integrable cone [C1 ⊸ (C2 ⊸ D)]. *)

(** ** A *function-level* bilinear-map predicate — Paper §5.2

    A function [f : C1 -> C2 -> D] is *bilinear, ω-continuous,
    integrable* iff for every [x1 : C1], [f x1] is a [linhom_car],
    and for every [x2 : C2], [(fun x1 => f x1 x2)] is also a
    [linhom_car].  We state this as a predicate that captures the
    paper's three conditions (separate linearity, separate
    continuity / measurability / integrability) by reducing them to
    the [linhom_car] predicate on each section. *)

Section Bilin.
Variables (R : realType) (Ar : MeasSubcat R).
Variables C1 C2 D : ICone.type Ar.

(** A *separately-linhom* bilinear data: for every [x1], the section
    [f x1 : C2 -> D] is a [linhom_car Ar C2 D], and for every [x2],
    the section [(fun x1 => f x1 x2) : C1 -> D] is a [linhom_car Ar C1 D]. *)
Record bilin_data : Type := MkBilin {
  bilin_fun :> C1 -> C2 -> D;
  bilin_left : forall x1 : C1, linhom_car Ar C2 D;
  bilin_left_eq :
    forall (x1 : C1) (x2 : C2),
      linhom_fun (bilin_left x1) x2 = bilin_fun x1 x2;
  bilin_right : forall x2 : C2, linhom_car Ar C1 D;
  bilin_right_eq :
    forall (x1 : C1) (x2 : C2),
      linhom_fun (bilin_right x2) x1 = bilin_fun x1 x2;
}.

End Bilin.

Arguments bilin_data {R} Ar C1 C2 D.
Arguments MkBilin {R Ar C1 C2 D}.
Arguments bilin_fun {R Ar C1 C2 D}.
Arguments bilin_left {R Ar C1 C2 D}.
Arguments bilin_left_eq {R Ar C1 C2 D}.
Arguments bilin_right {R Ar C1 C2 D}.
Arguments bilin_right_eq {R Ar C1 C2 D}.

(** ** A *function-level* curried-bilinear datum — Paper §5.2

    A function [F : C1 -> linhom_car Ar C2 D] (i.e. a function from
    [C1] to the [C2 ⊸ D] carrier) is the "curried" form of a
    bilinear datum.  We require that [F] itself behaves as a
    [linhom_car] (i.e., is linear/continuous/etc. in [C1]) once we
    *forget* the cone structure on [linhom_car Ar C2 D].  At this
    point we register the "underlying-function" form of this datum and
    the round-trip
    lemmas at the function level. *)

Section CurriedBilin.
Variables (R : realType) (Ar : MeasSubcat R).
Variables C1 C2 D : ICone.type Ar.

(** Paper §5.2 / Def 5.6 (uncurry): from a curried bilinear datum
    to a [bilin_data].  We adopt the convention that *every* arg
    section is a [linhom_car].  Given a function
    [F : C1 -> linhom_car Ar C2 D], the uncurried map is
    [(x1, x2) ↦ linhom_fun (F x1) x2]; its left section at [x1] is
    [F x1] itself, and its right section at [x2] must be supplied as
    additional data — namely the [linhom_car] structure of the map
    [(fun x1 => linhom_fun (F x1) x2) : C1 -> D]. *)
Definition curried_to_bilin
  (F : C1 -> linhom_car Ar C2 D)
  (Hright : forall x2 : C2, linhom_car Ar C1 D)
  (Hright_eq :
    forall (x1 : C1) (x2 : C2),
      linhom_fun (Hright x2) x1 = linhom_fun (F x1) x2) :
  bilin_data Ar C1 C2 D :=
  MkBilin (fun x1 x2 => linhom_fun (F x1) x2)
          F
          (fun x1 x2 => erefl _)
          Hright Hright_eq.

(** Paper §5.2 / Def 5.6 (curry): from a [bilin_data] to its left
    sections (which are automatically [linhom_car]s by definition
    of [bilin_data]). *)
Definition bilin_to_curried (f : bilin_data Ar C1 C2 D) :
    C1 -> linhom_car Ar C2 D :=
  fun x1 => bilin_left f x1.

(** Paper §5.2 / Def 5.6 (round-trip 1): currying then evaluating
    recovers the original bilinear function. *)
Lemma bilin_to_curried_fun (f : bilin_data Ar C1 C2 D) (x1 : C1) (x2 : C2) :
  linhom_fun (bilin_to_curried f x1) x2 = bilin_fun f x1 x2.
Proof. by rewrite /bilin_to_curried; apply: bilin_left_eq. Qed.

(** Paper §5.2 / Def 5.6 (round-trip 2): the curried form constructed
    from sections of a [bilin_data] reproduces the same underlying
    function. *)
Lemma curried_to_bilin_fun
  (F : C1 -> linhom_car Ar C2 D)
  (Hright : forall x2 : C2, linhom_car Ar C1 D)
  (Hright_eq :
    forall (x1 : C1) (x2 : C2),
      linhom_fun (Hright x2) x1 = linhom_fun (F x1) x2)
  (x1 : C1) (x2 : C2) :
  bilin_fun (@curried_to_bilin F Hright Hright_eq) x1 x2 =
  linhom_fun (F x1) x2.
Proof. by []. Qed.

End CurriedBilin.

Arguments curried_to_bilin {R Ar C1 C2 D}.
Arguments bilin_to_curried {R Ar C1 C2 D}.

(** ** Paper-aligned aliases for the bilinear ↔ linhom bijection

    Paper §5.2 / Def 5.6 names this bijection in terms of the
    integrable cone [C1, C2 ⊸ D = C1 ⊸ (C2 ⊸ D)]; with the full HB
    tower in place on [linhom_car], the maps [bilin_to_linhom] /
    [linhom_to_bilin] below become morphisms in [ICones], witnessing
    the iso [BilinIntegrable(C1, C2; D) ≃ ICones(C1, linhom_car C2 D)].
    Here we record the function-level content. *)

Section BilinLinhomAlias.
Variables (R : realType) (Ar : MeasSubcat R).
Variables C1 C2 D : ICone.type Ar.

(** Paper Def 5.6 (curry): a [bilin_data] determines a function
    [C1 -> linhom_car Ar C2 D]. *)
Definition bilin_to_linhom : bilin_data Ar C1 C2 D ->
    C1 -> linhom_car Ar C2 D := @bilin_to_curried R Ar C1 C2 D.

(** Paper Def 5.6 (uncurry): a function [C1 -> linhom_car Ar C2 D],
    together with right-section data, determines a [bilin_data]. *)
Definition linhom_to_bilin
  (F : C1 -> linhom_car Ar C2 D)
  (Hright : forall x2 : C2, linhom_car Ar C1 D)
  (Hright_eq :
    forall (x1 : C1) (x2 : C2),
      linhom_fun (Hright x2) x1 = linhom_fun (F x1) x2) :
  bilin_data Ar C1 C2 D :=
  @curried_to_bilin R Ar C1 C2 D F Hright Hright_eq.

(** Paper Def 5.6: the two round-trip equations at the function level. *)
Lemma bilin_to_linhom_E (f : bilin_data Ar C1 C2 D) (x1 : C1) (x2 : C2) :
  linhom_fun (bilin_to_linhom f x1) x2 = bilin_fun f x1 x2.
Proof. exact: bilin_to_curried_fun. Qed.

Lemma linhom_to_bilin_E
  (F : C1 -> linhom_car Ar C2 D)
  (Hright : forall x2 : C2, linhom_car Ar C1 D)
  (Hright_eq :
    forall (x1 : C1) (x2 : C2),
      linhom_fun (Hright x2) x1 = linhom_fun (F x1) x2)
  (x1 : C1) (x2 : C2) :
  bilin_fun (linhom_to_bilin Hright_eq) x1 x2 = linhom_fun (F x1) x2.
Proof.
rewrite /linhom_to_bilin.
exact: curried_to_bilin_fun.
Qed.

End BilinLinhomAlias.

Arguments bilin_to_linhom {R Ar C1 C2 D}.
Arguments linhom_to_bilin {R Ar C1 C2 D F Hright}.

(** ** The functorial action of [⊸] — Paper §5.3, Def 5.7 / Prop 5.8

    Given [h : icones_hom Ar C2 C1] and [g : icones_hom Ar D1 D2], the
    internal hom sends [f ∈ C1 ⊸ D1] to [g ∘ f ∘ h ∈ C2 ⊸ D2].  We
    build this in two reusable halves:

    - [linhom_postc g f := g ∘ f] (postcomposition by [g], an
      [icones_hom]), a [linhom_car Ar C D2] for [f : linhom_car Ar C D1].
    - [linhom_prec h f := f ∘ h] (precomposition by [h], an
      [icones_hom]), a [linhom_car Ar C2 D] for [f : linhom_car Ar C1 D].

    Postcomposition is the harder direction (ω-continuity needs a
    rescaling argument because [f] is only bounded, not unit-norm);
    precomposition is direct because [h] is unit-norm.  We then combine
    them into [linhom_map h g : icones_hom Ar (C1⊸D1) (C2⊸D2)] and prove
    functoriality (Prop 5.8). *)

Section LinhomPostc.
Variables (R : realType) (Ar : MeasSubcat R).
Variables C D1 D2 : ICone.type Ar.
Variable g : icones_hom Ar D1 D2.
Variable f : linhom_car Ar C D1.

Local Notation gf := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones g))).

(** Underlying function [x ↦ g (f x)]. *)
Definition postc_fun : C -> D2 := fun x => gf (linhom_fun f x).

Lemma postc_linear : is_linear postc_fun.
Proof.
have [Hf0 HfD HfZ] := linhom_pre_linear (linhom_pre_of f).
have [Hg0 HgD HgZ] :=
  cones_hom_linear (mcones_hom_cones (icones_hom_mcones g)).
rewrite /postc_fun; split.
- by rewrite /linhom_fun Hf0 Hg0.
- by move=> x y; rewrite /linhom_fun HfD HgD.
- by move=> r x; rewrite /linhom_fun HfZ HgZ.
Qed.

Lemma postc_bounded :
  exists M : R, forall x : C, cnorm x <= 1 -> cnorm (postc_fun x) <= M.
Proof.
have [Mf HMf] := linhom_pre_bounded (linhom_pre_of f).
exists Mf => x Hx; rewrite /postc_fun.
apply: le_trans
  (cones_hom_norm_le1 (mcones_hom_cones (icones_hom_mcones g)) _) _.
exact: HMf.
Qed.

(** ω-continuity of [g ∘ f].  Because [f] is only bounded (by some [Mf]),
    we cannot apply [f]'s or [g]'s ω-continuity directly to a unit-ball
    chain [u].  We rescale by [sinv := 1 / max 1 Mf]: then [f (sinv·u_n)]
    has norm [≤ sinv·Mf ≤ 1], so [f]'s ω-continuity applies; the chain
    [sinv·f(u_n)] is unit-norm so [g]'s ω-continuity applies; finally we
    cancel [sinv] using [s·sinv = 1]. *)
Lemma postc_continuous : is_omega_continuous postc_fun.
Proof.
move=> u uch ub1 wuch wub1.
have Hf_cont := linhom_pre_continuous (linhom_pre_of f).
have Hf_lin := linhom_pre_linear (linhom_pre_of f).
have Hg_cont :
    is_omega_continuous
      (cones_hom_fun (mcones_hom_cones (icones_hom_mcones g))).
  exact: cones_hom_continuous (mcones_hom_cones (icones_hom_mcones g)).
have Hg_lin := cones_hom_linear (mcones_hom_cones (icones_hom_mcones g)).
have [Mf HMf] := linhom_pre_bounded (linhom_pre_of f).
have Mfge0 : 0 <= Mf.
  apply: le_trans (HMf precone_zero _); first exact: cone_norm_ge0.
  by rewrite cone_norm0.
pose s_num : R := Order.max 1 Mf.
have s_pos : 0 < s_num by rewrite /s_num lt_max ltr01.
have s_ge1 : 1 <= s_num by rewrite /s_num le_max lexx.
have s_ge0 : 0 <= s_num by exact: ltW.
pose s : {nonneg R} := NngNum s_ge0.
have sinv_ge0 : 0 <= s_num^-1 by rewrite invr_ge0 ltW.
pose sinv : {nonneg R} := NngNum sinv_ge0.
have nng_eq : forall (a b : {nonneg R}), a%:num = b%:num -> a = b.
  by move=> a b /val_inj.
have s_mul_sinv : s%:num * sinv%:num = 1.
  by rewrite /= mulfV // gt_eqF.
have s_sinv : (s%:num * sinv%:num)%:nng = 1%:nng.
  by apply: nng_eq => /=; rewrite s_mul_sinv.
have sinv_le_1 : sinv%:num <= 1.
  by rewrite /= invf_le1 // s_ge1.
have sinv_Mf_le_1 : sinv%:num * Mf <= 1.
  have e : sinv%:num * Mf <= sinv%:num * s_num.
    by rewrite ler_pM2l ?invr_gt0 // /s_num le_max lexx orbT.
  apply: le_trans e _; rewrite /=.
  by rewrite mulVf // gt_eqF.
have [Hf0 HfD HfZ] := Hf_lin.
have [Hg0 HgD HgZ] := Hg_lin.
(* The rescaled input chain [v_n := sinv · u_n] is unit-norm. *)
have vch : forall n, precone_le (precone_scale sinv (u n))
                                (precone_scale sinv (u n.+1)).
  by move=> n; exact: precone_scale_le (uch n).
have vub : forall n, cnorm (precone_scale sinv (u n)) <= 1.
  move=> n; rewrite cone_normh.
  apply: le_trans (ler_pM sinv_ge0 (cone_norm_ge0 _) sinv_le_1 (ub1 n)) _.
  by rewrite mulr1.
(* [f(sinv·u_n) = sinv·f(u_n)] has norm [≤ sinv·Mf ≤ 1]. *)
have fvch : forall n,
    precone_le (linhom_fun f (precone_scale sinv (u n)))
               (linhom_fun f (precone_scale sinv (u n.+1))).
  by move=> n; exact: (linear_increasing Hf_lin) _ _ (vch n).
have fvub : forall n, cnorm (linhom_fun f (precone_scale sinv (u n))) <= 1.
  move=> n; rewrite /linhom_fun HfZ cone_normh /=.
  apply: le_trans
    (ler_pM sinv_ge0 (cone_norm_ge0 _) (lexx _) (HMf _ (ub1 n))) _.
  exact: sinv_Mf_le_1.
(* [f(sup v) = sup(f∘v)] by [f]'s ω-continuity. *)
have fv_sup : linhom_fun f (cone_sup_ball _ vch vub) =
              cone_sup_ball
                (linhom_fun f \o (fun n => precone_scale sinv (u n)))
                fvch fvub.
  exact: Hf_cont.
(* [sup v = sinv · sup u]. *)
have v_sup : cone_sup_ball _ vch vub =
             precone_scale sinv (cone_sup_ball u uch ub1).
  exact: (@sup_ball_scaler R C sinv u uch ub1 vch vub).
(* The chain [sinv·f(u_n)] is unit-norm. *)
have sinv_fu_ch : forall n,
    precone_le (precone_scale sinv (linhom_fun f (u n)))
               (precone_scale sinv (linhom_fun f (u n.+1))).
  move=> n; apply: precone_scale_le.
  exact: (linear_increasing Hf_lin) _ _ (uch n).
have sinv_fu_ub : forall n,
    cnorm (precone_scale sinv (linhom_fun f (u n))) <= 1.
  move=> n; rewrite cone_normh /=.
  apply: le_trans
    (ler_pM sinv_ge0 (cone_norm_ge0 _) (lexx _) (HMf _ (ub1 n))) _.
  exact: sinv_Mf_le_1.
(* [sinv·f(sup u) = sup_n (sinv·f u_n)]. *)
have main_sinv_eq :
    precone_scale sinv (linhom_fun f (cone_sup_ball u uch ub1)) =
    cone_sup_ball (fun n => precone_scale sinv (linhom_fun f (u n)))
                  sinv_fu_ch sinv_fu_ub.
  have lhs_eq : linhom_fun f (cone_sup_ball _ vch vub) =
                precone_scale sinv (linhom_fun f (cone_sup_ball u uch ub1)).
    by rewrite v_sup /linhom_fun HfZ.
  rewrite -lhs_eq fv_sup.
  apply: precone_le_anti; apply: cone_sup_ball_lub => n.
  - have -> : (linhom_fun f \o (fun n0 => precone_scale sinv (u n0))) n =
              precone_scale sinv (linhom_fun f (u n)).
      by rewrite /= /linhom_fun HfZ.
    exact: cone_sup_ball_ub.
  - have <- : (linhom_fun f \o (fun n0 => precone_scale sinv (u n0))) n =
              precone_scale sinv (linhom_fun f (u n)).
      by rewrite /= /linhom_fun HfZ.
    exact: cone_sup_ball_ub.
(* Apply [g]'s ω-continuity to the unit-norm chain [sinv·f u_n]. *)
have gsfu_ch : forall n,
    precone_le (gf (precone_scale sinv (linhom_fun f (u n))))
               (gf (precone_scale sinv (linhom_fun f (u n.+1)))).
  by move=> n; exact: (linear_increasing Hg_lin) _ _ (sinv_fu_ch n).
have gsfu_ub : forall n,
    cnorm (gf (precone_scale sinv (linhom_fun f (u n)))) <= 1.
  move=> n.
  apply: le_trans
    (cones_hom_norm_le1 (mcones_hom_cones (icones_hom_mcones g)) _) _.
  exact: sinv_fu_ub.
have g_sup : gf (cone_sup_ball
                   (fun n => precone_scale sinv (linhom_fun f (u n)))
                   sinv_fu_ch sinv_fu_ub) =
             cone_sup_ball
               (gf \o (fun n => precone_scale sinv (linhom_fun f (u n))))
               gsfu_ch gsfu_ub.
  exact: Hg_cont.
(* The unit-norm chain [sinv·postc_fun u_n]. *)
have sinv_w_ch : forall n,
    precone_le (precone_scale sinv (postc_fun (u n)))
               (precone_scale sinv (postc_fun (u n.+1))).
  by move=> n; exact: precone_scale_le (wuch n).
have sinv_w_ub : forall n,
    cnorm (precone_scale sinv (postc_fun (u n))) <= 1.
  move=> n; rewrite cone_normh.
  apply: le_trans (ler_pM sinv_ge0 (cone_norm_ge0 _) sinv_le_1 (wub1 n)) _.
  by rewrite mulr1.
(* [g(sinv·f u_n) = sinv·postc_fun(u_n)] pointwise, so the sup-balls agree. *)
have gsfu_sinvw :
  cone_sup_ball (gf \o (fun n => precone_scale sinv (linhom_fun f (u n))))
                gsfu_ch gsfu_ub =
  cone_sup_ball (fun n => precone_scale sinv (postc_fun (u n)))
                sinv_w_ch sinv_w_ub.
  apply: precone_le_anti; apply: cone_sup_ball_lub => n.
  - have -> : (gf \o (fun n0 => precone_scale sinv (linhom_fun f (u n0)))) n =
              precone_scale sinv (postc_fun (u n)).
      by rewrite /= /postc_fun HgZ.
    exact: cone_sup_ball_ub.
  - have <- : (gf \o (fun n0 => precone_scale sinv (linhom_fun f (u n0)))) n =
              precone_scale sinv (postc_fun (u n)).
      by rewrite /= /postc_fun HgZ.
    exact: cone_sup_ball_ub.
(* [sup_n (sinv·postc_fun u_n) = sinv·sup(postc_fun∘u)]. *)
have sinvw_sup :
  cone_sup_ball (fun n => precone_scale sinv (postc_fun (u n)))
                sinv_w_ch sinv_w_ub =
  precone_scale sinv (cone_sup_ball (postc_fun \o u) wuch wub1).
  exact: (@sup_ball_scaler R D2 sinv (postc_fun \o u) wuch wub1
            sinv_w_ch sinv_w_ub).
(* Chain everything: [sinv·postc_fun(sup u) = sinv·sup(postc_fun∘u)]. *)
have core_eq :
    precone_scale sinv (postc_fun (cone_sup_ball u uch ub1)) =
    precone_scale sinv (cone_sup_ball (postc_fun \o u) wuch wub1).
  rewrite -sinvw_sup -gsfu_sinvw -g_sup -main_sinv_eq.
  by rewrite /postc_fun HgZ.
(* Cancel [sinv] by multiplying with [s] (as [s·sinv = 1]). *)
have multiply_s : forall x : D2, precone_scale s (precone_scale sinv x) = x.
  by move=> x; rewrite -precone_scale_A s_sinv precone_scale_1.
rewrite -(multiply_s (postc_fun _))
        -[in RHS](multiply_s (cone_sup_ball _ _ _)).
by congr precone_scale.
Qed.

Lemma postc_pres_path
  (X : ar_obj Ar) (γ : ar_carrier Ar X -> C) :
  is_measurable_path γ ->
  is_measurable_path (fun r => postc_fun (γ r)).
Proof.
move=> Hγ.
have Hfγ : is_measurable_path (fun r => linhom_fun f (γ r)).
  exact: (linhom_pre_pres_path (linhom_pre_of f)).
exact: (mcones_hom_pres_path (icones_hom_mcones g) X _ Hfγ).
Qed.

Definition postc_pre : linhom_pre Ar C D2 :=
  MkLinhomPre postc_fun postc_linear postc_continuous postc_bounded
              postc_pres_path.

Lemma postc_pres_int
  (X : ar_obj Ar) (β : ar_carrier Ar X -> C)
  (Hβ : is_measurable_path β)
  (µ : fmeas R (ar_carrier Ar X)) :
  linhom_pre_fun postc_pre (icone_integral β Hβ µ) =
  icone_integral
    (fun r => linhom_pre_fun postc_pre (β r))
    (linhom_pre_pres_path postc_pre X β Hβ) µ.
Proof.
(* [g (f (∫β µ)) = g (∫(f∘β) µ) = ∫(g∘f∘β) µ], by [f]'s and [g]'s
   integral-preservation, then uniqueness of the path integral. *)
have Hf := linhom_pres_int f X β Hβ µ.
have Hfβ := linhom_pre_pres_path (linhom_pre_of f) X β Hβ.
apply: (path_integral_eq_unique
  (β := fun r => postc_fun (β r)) (µ := µ));
  last by exact: icone_integralP.
rewrite /postc_pre /=.
have -> : postc_fun (icone_integral β Hβ µ) =
          gf (icone_integral (fun r => linhom_fun f (β r)) Hfβ µ).
  rewrite /postc_fun /linhom_fun Hf.
  by congr (gf _); apply: f_equal2; first by apply: Prop_irrelevance.
rewrite (icones_hom_pres_int g X (fun r => linhom_fun f (β r)) Hfβ µ).
exact: icone_integralP.
Qed.

(** The postcomposed map [g ∘ f] as a [linhom_car]. *)
Definition linhom_postc : linhom_car Ar C D2 :=
  MkLinhom postc_pre postc_pres_int.

Lemma linhom_postc_E (x : C) :
  linhom_fun linhom_postc x =
  cones_hom_fun (mcones_hom_cones (icones_hom_mcones g)) (linhom_fun f x).
Proof. by []. Qed.

End LinhomPostc.

Arguments postc_fun {R Ar C D1 D2}.
Arguments linhom_postc {R Ar C D1 D2}.

Section LinhomPrec.
Variables (R : realType) (Ar : MeasSubcat R).
Variables C1 C2 D : ICone.type Ar.
Variable h : icones_hom Ar C2 C1.
Variable f : linhom_car Ar C1 D.

Local Notation hf := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

(** Underlying function [x ↦ f (h x)]. *)
Definition prec_fun : C2 -> D := fun x => linhom_fun f (hf x).

Lemma prec_linear : is_linear prec_fun.
Proof.
have [Hf0 HfD HfZ] := linhom_pre_linear (linhom_pre_of f).
have [Hh0 HhD HhZ] :=
  cones_hom_linear (mcones_hom_cones (icones_hom_mcones h)).
rewrite /prec_fun; split.
- by rewrite /linhom_fun Hh0 Hf0.
- by move=> x y; rewrite /linhom_fun HhD HfD.
- by move=> r x; rewrite /linhom_fun HhZ HfZ.
Qed.

Lemma prec_bounded :
  exists M : R, forall x : C2, cnorm x <= 1 -> cnorm (prec_fun x) <= M.
Proof.
have [Mf HMf] := linhom_pre_bounded (linhom_pre_of f).
exists Mf => x Hx; rewrite /prec_fun.
apply: HMf.
apply: le_trans
  (cones_hom_norm_le1 (mcones_hom_cones (icones_hom_mcones h)) _) _.
exact: Hx.
Qed.

(** ω-continuity of [f ∘ h].  Since [h] is unit-norm, the chain [h∘u]
    stays unit-norm, so we apply [h]'s ω-continuity to [u] and [f]'s
    ω-continuity to [h∘u] — no rescaling needed. *)
Lemma prec_continuous : is_omega_continuous prec_fun.
Proof.
move=> u uch ub1 wuch wub1.
have Hf_cont := linhom_pre_continuous (linhom_pre_of f).
have Hh_cont :
    is_omega_continuous
      (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
  exact: cones_hom_continuous (mcones_hom_cones (icones_hom_mcones h)).
have Hh_lin := cones_hom_linear (mcones_hom_cones (icones_hom_mcones h)).
(* [h∘u] is increasing and unit-norm. *)
have huch : forall n, precone_le (hf (u n)) (hf (u n.+1)).
  by move=> n; exact: (linear_increasing Hh_lin) _ _ (uch n).
have hub1 : forall n, cnorm (hf (u n)) <= 1.
  move=> n; apply: le_trans
    (cones_hom_norm_le1 (mcones_hom_cones (icones_hom_mcones h)) _) _.
  exact: ub1.
(* [h(sup u) = sup(h∘u)] then [f(sup(h∘u)) = sup(f∘h∘u)]. *)
rewrite /prec_fun (Hh_cont u uch ub1 huch hub1).
exact: Hf_cont.
Qed.

Lemma prec_pres_path
  (X : ar_obj Ar) (γ : ar_carrier Ar X -> C2) :
  is_measurable_path γ ->
  is_measurable_path (fun r => prec_fun (γ r)).
Proof.
move=> Hγ.
have Hhγ : is_measurable_path (fun r => hf (γ r)).
  exact: (mcones_hom_pres_path (icones_hom_mcones h) X _ Hγ).
exact: (linhom_pre_pres_path (linhom_pre_of f) X _ Hhγ).
Qed.

Definition prec_pre : linhom_pre Ar C2 D :=
  MkLinhomPre prec_fun prec_linear prec_continuous prec_bounded
              prec_pres_path.

Lemma prec_pres_int
  (X : ar_obj Ar) (β : ar_carrier Ar X -> C2)
  (Hβ : is_measurable_path β)
  (µ : fmeas R (ar_carrier Ar X)) :
  linhom_pre_fun prec_pre (icone_integral β Hβ µ) =
  icone_integral
    (fun r => linhom_pre_fun prec_pre (β r))
    (linhom_pre_pres_path prec_pre X β Hβ) µ.
Proof.
(* [f (h (∫β µ)) = f (∫(h∘β) µ) = ∫(f∘h∘β) µ], by [h]'s and [f]'s
   integral-preservation, then uniqueness of the path integral. *)
have Hh := icones_hom_pres_int h X β Hβ µ.
have Hhβ := mcones_hom_pres_path (icones_hom_mcones h) X β Hβ.
apply: (path_integral_eq_unique
  (β := fun r => prec_fun (β r)) (µ := µ));
  last by exact: icone_integralP.
rewrite /prec_pre /=.
have -> : prec_fun (icone_integral β Hβ µ) =
          linhom_fun f (icone_integral (fun r => hf (β r)) Hhβ µ).
  rewrite /= /prec_fun Hh.
  by congr (linhom_fun f _); apply: f_equal2; first by apply: Prop_irrelevance.
rewrite /linhom_fun (linhom_pres_int f X (fun r => hf (β r)) Hhβ µ).
exact: icone_integralP.
Qed.

(** The precomposed map [f ∘ h] as a [linhom_car]. *)
Definition linhom_prec : linhom_car Ar C2 D :=
  MkLinhom prec_pre prec_pres_int.

End LinhomPrec.

Arguments prec_fun {R Ar C1 C2 D}.
Arguments linhom_prec {R Ar C1 C2 D}.

(** ** The object map of [⊸] — Paper §5.3, Def 5.7

    Combining [linhom_postc] and [linhom_prec] gives the action of the
    internal hom on objects: for [h : icones_hom Ar C2 C1] and
    [g : icones_hom Ar D1 D2],
      [linhom_map_fun h g : linhom_car Ar C1 D1 -> linhom_car Ar C2 D2]
    sends [f] to [g ∘ f ∘ h].

    Packaging this object map as a morphism [icones_hom Ar (C1⊸D1)
    (C2⊸D2)] in [ICones] (Prop 5.8) additionally requires showing the
    map is itself measurable-path- and integral-preserving *in [f]*,
    which needs the pull-back of a [D2]-test along [g] to land back in
    the measurability structure of [D1] — infrastructure not present in
    the current development (it is the dual, test-side, characterisation
    of an [mcones_hom], not formalised here; cf. the analogous deferral
    of the bilinear ↔ linhom bijection to morphisms of [ICones] in
    [BilinLinhomAlias]).  We therefore deliver the object map together
    with its full functoriality at the object level (Prop 5.8 read as
    equalities of the underlying maps, established via [linhom_eq]). *)

Section LinhomMap.
Variables (R : realType) (Ar : MeasSubcat R).

(** [linhom_map_fun h g f := g ∘ f ∘ h]. *)
Definition linhom_map_fun
    (C1 C2 D1 D2 : ICone.type Ar)
    (h : icones_hom Ar C2 C1) (g : icones_hom Ar D1 D2)
    (f : linhom_car Ar C1 D1) : linhom_car Ar C2 D2 :=
  linhom_prec h (linhom_postc g f).

(** Pointwise: [(linhom_map_fun h g f) x = g (f (h x))]. *)
Lemma linhom_map_funE
    (C1 C2 D1 D2 : ICone.type Ar)
    (h : icones_hom Ar C2 C1) (g : icones_hom Ar D1 D2)
    (f : linhom_car Ar C1 D1) (x : C2) :
  linhom_fun (linhom_map_fun h g f) x =
  cones_hom_fun (mcones_hom_cones (icones_hom_mcones g))
    (linhom_fun f
       (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h)) x)).
Proof. by []. Qed.

(** One-sided actions (Paper §5.3): [C ⊸ g := linhom_map_fun id g] and
    [h ⊸ D := linhom_map_fun h id]. *)
Definition linhom_post (C D1 D2 : ICone.type Ar)
    (g : icones_hom Ar D1 D2) : linhom_car Ar C D1 -> linhom_car Ar C D2 :=
  linhom_map_fun (icones_id Ar C) g.

Definition linhom_pre_act (C1 C2 D : ICone.type Ar)
    (h : icones_hom Ar C2 C1) : linhom_car Ar C1 D -> linhom_car Ar C2 D :=
  linhom_map_fun h (icones_id Ar D).

(** Paper Prop 5.8 (identity law): [linhom_map_fun id id = id]. *)
Lemma linhom_map_id (C D : ICone.type Ar) (f : linhom_car Ar C D) :
  linhom_map_fun (icones_id Ar C) (icones_id Ar D) f = f.
Proof. by apply: linhom_eq => x; rewrite linhom_map_funE. Qed.

(** Paper Prop 5.8 (composition law, contravariant in the first slot):
    [linhom_map_fun (h' ∘ h) (g ∘ g') =
       linhom_map_fun h g ∘ linhom_map_fun h' g']. *)
Lemma linhom_map_comp
    (C1 C2 C3 D1 D2 D3 : ICone.type Ar)
    (h : icones_hom Ar C2 C1) (h' : icones_hom Ar C3 C2)
    (g : icones_hom Ar D1 D2) (g' : icones_hom Ar D2 D3)
    (f : linhom_car Ar C1 D1) :
  linhom_map_fun (icones_comp h h') (icones_comp g' g) f =
  linhom_map_fun h' g' (linhom_map_fun h g f).
Proof. by apply: linhom_eq => x; rewrite !linhom_map_funE. Qed.

End LinhomMap.

Arguments linhom_map_fun {R Ar C1 C2 D1 D2}.
Arguments linhom_post {R Ar C D1 D2}.
Arguments linhom_pre_act {R Ar C1 C2 D}.

(** ** Sanity checks — initial [linhom_car] deliverables

    - The [linhom_car Ar C D] type packages: linear, ω-continuous,
      bounded, measurable-path-preserving, and integral-preserving
      maps.  Five fields, the same as the natural integrable-cone-
      morphism record.  (Paper §5.1 + Def 5.4 + Lemma 5.4.)
    - The [linhom_zero] element is fully delivered with no axioms
      beyond [boolp].
    - The [linhom_add_fun] / [linhom_scale_fun] operations are
      packaged as [linhom_car] records, with full proofs of
      linearity, ω-continuity, boundedness, path-preservation, and
      integral-preservation.
    - [cone_sup_ball_addD] — the full diagonal-sup identity in any
      [coneType], delivered above.  This is the key technical lemma
      enabling ω-continuity of pointwise sum.
    - [isPrecone] HB instance on [linhom_car Ar C D] — REGISTERED.
    - [linhom_norm] defined as the canonical [sup] operator norm.
    - Paper §5.2 / Def 5.6 (bilinear ↔ linhom bijection) is
      delivered at the function level via [bilin_data],
      [bilin_to_linhom], [linhom_to_bilin], and their round-trip
      lemmas [bilin_to_linhom_E] / [linhom_to_bilin_E].

    The [isCone] / [isMCone] / [isICone] HB instances are registered
    later in this file. *)

Section LinhomSanityCheck.
Variables (R : realType) (Ar : MeasSubcat R).
Variables C D : ICone.type Ar.

(** The zero morphism is in [linhom_car Ar C D]. *)
Check (linhom_zero C D : linhom_car Ar C D).

(** Pointwise sum and scaling are functions [C -> D]. *)
Check (fun f g : linhom_car Ar C D => linhom_add_fun f g : C -> D).
Check (fun (r : {nonneg R}) (f : linhom_car Ar C D) =>
        linhom_scale_fun r f : C -> D).

(** Pointwise sum and scaling packaged as [linhom_car]. *)
Check (fun f g : linhom_car Ar C D => linhom_add f g : linhom_car Ar C D).
Check (fun (r : {nonneg R}) (f : linhom_car Ar C D) =>
        linhom_scale r f : linhom_car Ar C D).

(** [linhom_car Ar C D] is a [preconeType R] (HB instance registered). *)
Check (linhom_car Ar C D : preconeType R).

End LinhomSanityCheck.

Section BilinSanityCheck.
Variables (R : realType) (Ar : MeasSubcat R).
Variables C1 C2 D : ICone.type Ar.

(** The bijection at the function level: a [bilin_data] gives a
    [C1 -> linhom_car Ar C2 D] map (and conversely, with right-section
    data). *)
Check (fun f : bilin_data Ar C1 C2 D =>
        bilin_to_linhom f : C1 -> linhom_car Ar C2 D).
Check (fun (F : C1 -> linhom_car Ar C2 D)
           (Hright : forall x2 : C2, linhom_car Ar C1 D)
           (Hright_eq :
              forall (x1 : C1) (x2 : C2),
                linhom_fun (Hright x2) x1 = linhom_fun (F x1) x2) =>
         linhom_to_bilin Hright_eq : bilin_data Ar C1 C2 D).

End BilinSanityCheck.
