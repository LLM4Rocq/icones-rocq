(** * The integrable linear-map cone — Paper §5.1 + §5.2

    Given two integrable cones [C, D : iconeType Ar], the paper
    constructs the *integrable cone of linear, ω-continuous,
    integral-preserving maps* [C ⊸ D]. In M4 wave 1 we deliver:

    - [linhom_car C D] — the carrier record bundling a function
      [C -> D] together with proofs of: linearity, ω-continuity,
      *boundedness*, measurable-path preservation, integral
      preservation. (We do **not** require the pointwise unit-norm
      bound that [cones_hom] enforces — paper §5.1 paragraph 1 builds
      [C ⊸ D] as the set of maps [f] such that, for some ε > 0,
      [εf] is in [ICones(C, D)]. Equivalently, [f] is bounded.)
    - [isPrecone] HB instance — pointwise [0], [+], [*:]. Paper §5.1.
    - [isCone] HB instance — operator-norm (M1's [linmap_norm]) plus
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

    The symmetric monoidal closure [⊗ ⊣ ⊸] is **stretch goal S6** and
    is **not in scope** here. *)
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
From mathcomp.analysis Require Import lebesgue_integral_nonneg.
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
Require Import Icones.icones.pettis.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_integral.
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

    We prove this once and for all here, then reuse it for the
    [isPrecone] / [isCone] HB instances on [linhom_car]. *)

Section DiagonalSup.
Variable R : realType.
Variable P : coneType R.
Implicit Types (a b : nat -> P).

Local Open Scope precone_scope.

(** Auxiliary: the diagonal sup is ≤p the pointwise sum of sups.

    Given chains [a, b] in [B] with [‖a_n + b_n‖ ≤ 1] (so the
    diagonal sum chain stays in [B]), we have
    [cone_sup_ball (a + b) ≤p cone_sup_ball a + cone_sup_ball b].

    By [cone_sup_ball_lub] on the diagonal sup, with the witness
    [(z_a, z_b)] from the upper-bound property of [Sa] and [Sb]. *)
Lemma cone_sup_ball_addD_le a b
  (ach : forall n, a n <=p a n.+1)
  (aub : forall n, cnorm (a n) <= 1)
  (bch : forall n, b n <=p b n.+1)
  (bub : forall n, cnorm (b n) <= 1)
  (sch : forall n, precone_add (a n) (b n) <=p precone_add (a n.+1) (b n.+1))
  (sub : forall n, cnorm (precone_add (a n) (b n)) <= 1) :
  cone_sup_ball (fun n => precone_add (a n) (b n)) sch sub
    <=p precone_add (cone_sup_ball a ach aub) (cone_sup_ball b bch bub).
Proof.
apply: cone_sup_ball_lub => n.
have [za Hza] : a n <=p cone_sup_ball a ach aub by exact: cone_sup_ball_ub.
have [zb Hzb] : b n <=p cone_sup_ball b bch bub by exact: cone_sup_ball_ub.
exists (precone_add za zb).
rewrite Hza Hzb.
rewrite -!precone_addA; congr precone_add.
by rewrite precone_addA [za + b n]precone_addC -precone_addA.
Qed.

(** Auxiliary: the reverse direction.

    [cone_sup_ball a + cone_sup_ball b ≤p cone_sup_ball (a + b)].

    Proof. We use [sup_ball_addr] / [sup_ball_addl] in two steps.
    For each fixed [k], the chain [(a_n + b_k)_n] is increasing and
    unit-ball (because [a_n + b_k ≤p a_max(n,k) + b_max(n,k) ≤p Ss],
    hence its norm is ≤ ‖Ss‖ ≤ 1 by Normp). By [sup_ball_addr] on
    the chain [a] with [y := b_k], [sup_n (a_n + b_k) = Sa + b_k];
    by [cone_sup_ball_lub], this sup is ≤p Ss. So [Sa + b_k ≤p Ss]
    for every k. The chain [(Sa + b_k)_k] is then increasing and
    unit-ball (norm ≤ ‖Ss‖). By [sup_ball_addl] applied to [b] with
    [x := Sa], [sup_k (Sa + b_k) = Sa + Sb]; again by
    [cone_sup_ball_lub], this is ≤p Ss. *)
Lemma cone_sup_ball_addD_ge a b
  (ach : forall n, a n <=p a n.+1)
  (aub : forall n, cnorm (a n) <= 1)
  (bch : forall n, b n <=p b n.+1)
  (bub : forall n, cnorm (b n) <= 1)
  (sch : forall n, precone_add (a n) (b n) <=p precone_add (a n.+1) (b n.+1))
  (sub : forall n, cnorm (precone_add (a n) (b n)) <= 1) :
  precone_add (cone_sup_ball a ach aub) (cone_sup_ball b bch bub)
    <=p cone_sup_ball (fun n => precone_add (a n) (b n)) sch sub.
Proof.
set Sa := cone_sup_ball a ach aub.
set Sb := cone_sup_ball b bch bub.
set Ss := cone_sup_ball (fun n => precone_add (a n) (b n)) sch sub.
(* General chain-monotonicity: if [n <= m] then [a n <=p a m]. *)
have chain_mono_a : forall n m : nat, (n <= m)%N -> a n <=p a m.
  move=> n m; elim: m => [|m IHm] nm.
    by rewrite leqn0 in nm; move/eqP: nm => ->; exact: precone_le_refl.
  case: (leqP n m) => Hk.
    apply: precone_le_trans (IHm Hk) _; exact: ach.
  have -> : n = m.+1 by apply/eqP; rewrite eqn_leq nm.
  exact: precone_le_refl.
have chain_mono_b : forall n m : nat, (n <= m)%N -> b n <=p b m.
  move=> n m; elim: m => [|m IHm] nm.
    by rewrite leqn0 in nm; move/eqP: nm => ->; exact: precone_le_refl.
  case: (leqP n m) => Hk.
    apply: precone_le_trans (IHm Hk) _; exact: bch.
  have -> : n = m.+1 by apply/eqP; rewrite eqn_leq nm.
  exact: precone_le_refl.
have ale_max : forall n k : nat, a n <=p a (maxn n k).
  by move=> n k; apply: chain_mono_a; exact: leq_maxl.
have ble_max : forall n k : nat, b k <=p b (maxn n k).
  by move=> n k; apply: chain_mono_b; exact: leq_maxr.
(* Step 1: for every n, k, a_n + b_k ≤p Ss. *)
have ab_le_Ss : forall n k : nat, precone_add (a n) (b k) <=p Ss.
  move=> n k.
  set m := maxn n k.
  have step1 : precone_add (a n) (b k) <=p precone_add (a m) (b m).
    apply: precone_le_trans (precone_add_le_r (b k) (ale_max n k)) _.
    by apply: precone_add_le_l; exact: ble_max.
  apply: precone_le_trans step1 _.
  exact: (cone_sup_ball_ub (fun n => precone_add (a n) (b n)) sch sub m).
(* The chain (a_n + b_k)_n is increasing in n (fixed k), and unit-ball. *)
have ch_ak_bk : forall k n,
    precone_add (a n) (b k) <=p precone_add (a n.+1) (b k).
  by move=> k n; apply: precone_add_le_r; exact: ach.
have ub_ak_bk : forall k n, cnorm (precone_add (a n) (b k)) <= 1.
  move=> k n.
  have hle := ab_le_Ss n k.
  apply: le_trans (cone_normp _ _ hle) _.
  exact: cone_sup_ball_norm.
(* Step 2: for every k, sup_n (a_n + b_k) = Sa + b_k. *)
have step2 : forall k,
  cone_sup_ball (fun n => precone_add (a n) (b k))
                (ch_ak_bk k) (ub_ak_bk k) =
  precone_add Sa (b k).
  by move=> k; rewrite (@sup_ball_addr _ _ a ach aub (b k)).
(* Step 3: Sa + b_k ≤p Ss for every k. *)
have Sa_bk_le_Ss : forall k, precone_add Sa (b k) <=p Ss.
  move=> k; rewrite -step2.
  apply: cone_sup_ball_lub => n; exact: ab_le_Ss.
(* The chain (Sa + b_k)_k is increasing in k, and unit-ball (norm ≤ ‖Ss‖). *)
have ch_Sa_bk : forall k,
    precone_add Sa (b k) <=p precone_add Sa (b k.+1).
  by move=> k; apply: precone_add_le_l; exact: bch.
have ub_Sa_bk : forall k, cnorm (precone_add Sa (b k)) <= 1.
  move=> k.
  apply: le_trans (cone_normp _ _ (Sa_bk_le_Ss k)) _.
  exact: cone_sup_ball_norm.
(* Step 4: sup_k (Sa + b_k) = Sa + Sb (via sup_ball_addr + commutativity). *)
have ch_bk_Sa : forall k, precone_add (b k) Sa <=p precone_add (b k.+1) Sa.
  by move=> k; apply: precone_add_le_r; exact: bch.
have ub_bk_Sa : forall k, cnorm (precone_add (b k) Sa) <= 1.
  by move=> k; rewrite precone_addC; exact: ub_Sa_bk.
have step4_alt :
  cone_sup_ball (fun k => precone_add (b k) Sa) ch_bk_Sa ub_bk_Sa =
  precone_add Sb Sa.
  exact: (@sup_ball_addr _ _ b bch bub Sa).
have swap_eq :
  cone_sup_ball (fun k => precone_add Sa (b k)) ch_Sa_bk ub_Sa_bk =
  cone_sup_ball (fun k => precone_add (b k) Sa) ch_bk_Sa ub_bk_Sa.
  apply: precone_le_anti.
  - apply: cone_sup_ball_lub => k.
    rewrite (_ : precone_add Sa (b k) = precone_add (b k) Sa);
      last exact: precone_addC.
    exact: cone_sup_ball_ub.
  - apply: cone_sup_ball_lub => k.
    rewrite (_ : precone_add (b k) Sa = precone_add Sa (b k));
      last exact: precone_addC.
    exact: cone_sup_ball_ub.
have step4 :
  cone_sup_ball (fun k => precone_add Sa (b k)) ch_Sa_bk ub_Sa_bk =
  precone_add Sa Sb.
  by rewrite swap_eq step4_alt precone_addC.
(* Step 5: Sa + Sb ≤p Ss. *)
rewrite -step4.
apply: cone_sup_ball_lub => k; exact: Sa_bk_le_Ss.
Qed.

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
Proof.
apply: precone_le_anti.
- exact: cone_sup_ball_addD_le.
- exact: cone_sup_ball_addD_ge.
Qed.

End DiagonalSupEq.

(** ** Pointwise sum-of-chain identity (continued)


    The standard one-sided ω-continuity result [sup_ball_addr]
    handles the case where one summand is fixed; the diagonal case
    here can be reduced to two applications of [sup_ball_addr] after
    rescaling, but the bookkeeping is voluminous. Within M4 wave 1
    we adopt the following **strategic scoping**:

    - We deliver the *type* [linhom_car Ar C D] (above) and a [linhom_zero]
      element fully and unconditionally.
    - We deliver the **bilinear ↔ linhom bijection** (paper §5.2 /
      Def 5.6) at the *function level* — this does not require the
      cone structure on [linhom_car] to be in place.
    - We **defer to M4 wave 2** the HB-instance registration of
      [isPrecone] / [isCone] / [isMCone] / [isICone] on
      [linhom_car Ar C D]. These are exactly the four-instance tower
      mirroring [path.v]; the technical block is the diagonal-sup
      identity (above) for [isCone]'s (Normc), and Lemma 5.4 for
      [isICone]. Both are routine but voluminous extensions, and we
      explicitly document the chain of arguments in the comments
      throughout this file.

    The bilinear ↔ linhom bijection (paper §5.2) is delivered below
    without depending on the HB tower; it is the cleanest invariant
    of the [linhom_car] construction. *)

(** ** Pointwise addition and scaling at the function level

    Below we provide the bare-function pointwise [+] and [*:]
    operators on [linhom_car], together with their preservation of
    linearity, ω-continuity (under the auxiliary unit-ball
    hypothesis), and boundedness. We do **not** package them as
    [linhom_car] elements (which would require the full
    diagonal-sup identity); that is M4 wave 2. *)

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

(** Splitting hypothesis for the unit-ball image-chain of [f + g]:
    if [‖f x + g x‖ ≤ 1], then [‖f x‖ ≤ 1] and [‖g x‖ ≤ 1]. *)
Lemma linhom_add_unit_split (f g : linhom_car Ar C D) (x : C) :
  cnorm (linhom_add_fun f g x) <= 1 ->
  cnorm (linhom_fun f x) <= 1 /\ cnorm (linhom_fun g x) <= 1.
Proof.
move=> H; split.
- apply: le_trans H; apply: cone_normp.
  by exists (linhom_fun g x).
- apply: le_trans H; apply: cone_normp.
  by exists (linhom_fun f x); rewrite precone_addC.
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
              cone_sup_ball (linhom_fun f \o (fun n => precone_scale sinv (u n)))
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
have sinv_fu_ch : forall n, precone_le (precone_scale sinv (linhom_fun f (u n)))
                                       (precone_scale sinv (linhom_fun f (u n.+1))).
  move=> n; apply: precone_scale_le.
  by have [_ HfD' HfZ'] := Hf_lin; exact: (linear_increasing Hf_lin) _ _ (uch n).
have sinv_fu_ub : forall n, cnorm (precone_scale sinv (linhom_fun f (u n))) <= 1.
  move=> n; rewrite cone_normh /=.
  apply: le_trans (ler_pM sinv_ge0 (cone_norm_ge0 _)
                          (lexx _) (HMf _ (ub1 n))) _.
  exact: sinv_Mf_le_1.
(* From fv_sup + fv_eq + lhs_eq + Prop_irrelevance:
   sinv · f(sup u) = cone_sup_ball (sinv · f u_n) sinv_fu_ch sinv_fu_ub. *)
have main_sinv_eq : precone_scale sinv (linhom_fun f (cone_sup_ball u uch ub1)) =
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
  cone_sup_ball (fun n => precone_scale r (precone_scale sinv (linhom_fun f (u n))))
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
  cone_sup_ball (fun n => precone_scale r (precone_scale sinv (linhom_fun f (u n))))
                rsinv_fu_ch rsinv_fu_ub =
  precone_scale r (cone_sup_ball (fun n => precone_scale sinv (linhom_fun f (u n)))
                                  sinv_fu_ch sinv_fu_ub).
  exact: (@sup_ball_scaler R D r _ sinv_fu_ch sinv_fu_ub rsinv_fu_ch rsinv_fu_ub).
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
  linhom_add f1 f2 = linhom_zero C D -> f1 = linhom_zero C D /\ f2 = linhom_zero C D.
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
    above by [linmap_norm f] (M1's [xchoose]-witness from Lemma 2.11),
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

(** Bounded above: M1's [linmap_norm] (an [xchoose]-extracted upper
    bound) bounds the set. *)
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

Lemma cnorm_div_succ_le1 (x : C) : cnorm x / (cnorm x + 1) <= 1.
Proof.
have h1 : 0 < cnorm x + 1 by exact: cnorm_succ_pos.
rewrite ler_pdivrMr // mul1r.
by rewrite -[X in X <= _]addr0 lerD2l ler01.
Qed.

Definition cnorm_succ_nng (x : C) : {nonneg R} :=
  NngNum (ltW (cnorm_succ_pos x)).

Lemma cnorm_succ_nng_pos (x : C) : 0 < (cnorm_succ_nng x)%:num.
Proof. exact: cnorm_succ_pos. Qed.

Lemma cnorm_succ_inv_ge0 (x : C) : 0 <= (cnorm x + 1)^-1.
Proof. by rewrite invr_ge0 ltW//; exact: cnorm_succ_pos. Qed.

Definition cnorm_succ_inv_nng (x : C) : {nonneg R} :=
  NngNum (cnorm_succ_inv_ge0 x).

Lemma cnorm_succ_invE (x : C) : (cnorm_succ_inv_nng x)%:num = (cnorm x + 1)^-1.
Proof. by []. Qed.

Lemma cnorm_succ_mulV (x : C) :
  (cnorm_succ_nng x)%:num * (cnorm_succ_inv_nng x)%:num = 1.
Proof. by rewrite /= mulfV// gt_eqF//; exact: cnorm_succ_pos. Qed.

Lemma cnorm_succ_mulVl (x : C) :
  (cnorm_succ_inv_nng x)%:num * (cnorm_succ_nng x)%:num = 1.
Proof. by rewrite /= mulVf// gt_eqF//; exact: cnorm_succ_pos. Qed.

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
    and entry-wise unit-ball bound, the iterated sup commutes. The
    same proof template would apply in any [coneType]. *)
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
Proof.
apply: precone_le_anti.
- apply: cone_sup_ball_lub => n.
  apply: cone_sup_ball_lub => k.
  have step1 : b n k <=p
      cone_sup_ball (b^~ k) (b_row_ch k) (fun n0 => b_ub n0 k).
    exact: cone_sup_ball_ub.
  apply: precone_le_trans step1 _.
  exact: cone_sup_ball_ub.
- apply: cone_sup_ball_lub => k.
  apply: cone_sup_ball_lub => n.
  have step1 : b n k <=p
      cone_sup_ball (b n) (b_col_ch n) (fun k0 => b_ub n k0).
    exact: cone_sup_ball_ub.
  apply: precone_le_trans step1 _.
  exact: cone_sup_ball_ub.
Qed.

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
rewrite mulrA mulfV ?gt_eqF // mul1r.
by [].
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
    measurable_fun [set: ar_carrier Ar X'] (un_e n).
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
    measurable_fun [set: ar_carrier Ar X'] fsup_e.
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

(** ** M4 wave 4 status note

    Delivered in this commit (M4 wave 4):
    - [cone_sup_ball_swap] — commutation of two unit-ball sups in a
      cone, used to discharge ω-continuity of [linhom_sup_fun].
    - [linhom_sup_fun_continuous] — ω-continuity of the pointwise sup
      (Step 2 of paper §5.1). Proved via the swap identity and
      ω-continuity of each [u_n].
    - [is_measurable_path_scale] — scaling preserves measurable paths.
    - [linhom_sup_fun_pres_path] — path-preservation of the pointwise
      sup. Strategy: uniform-scale rewrite [γ r = S *: γs r] with
      [S := M + 1], then [measurable_fun_cvg] on the chain
      [(s, r) ↦ m s (u_n (γs r))].
    - [linhom_norm_apply_le] — general operator-norm bound for arbitrary
      [x : C] (i.e., [cnorm (f x) ≤ ‖f‖ * cnorm x]).
    - [linhom_sup_fun_test_sup] — the test-of-sup identity:
      [m s (linhom_sup_fun x) = sup_n (m s (u_n x))] for any test [m].
    - [linhom_sup_fun_pres_int] — integral preservation of the
      pointwise sup. Strategy mirrors [integral_omega_cont_path] from
      M3: each [u_n] preserves integrals via Pettis; combine with MCT
      ([monotone_convergence]) and [fine_cvg] to identify both sides.
    - [linhom_sup_ball] — packaged sup-of-chain as a [linhom_car].
    - [linhom_sup_ball_norm] — the operator-norm bound ≤ 1.

    Deferred to M4 wave 5 (full isCone HB instance):
    - [linhom_sup_ball_ub] and [linhom_sup_ball_lub] — these state the
      precone-order (Cauchy-difference) upper-bound and least-upper-
      bound properties of [linhom_sup_ball]. The pointwise [≤p]
      relation holds (by [linhom_le_pointwise] in reverse — using the
      [linhom_sup_fun_norm_le] direction); but the precone_le on
      [linhom_car] requires constructing a *linhom_car* witness [δ]
      satisfying [linhom_sup_ball = u n + δ]. Bundling [δ] requires
      proving its own linearity, ω-continuity, boundedness, path-
      preservation, AND integral-preservation — the latter being the
      hard step, since the difference [linhom_sup_fun x - u_n x]
      doesn't directly inherit Pettis-equation from its summands.
    - Final [isCone] HB instance registration on [linhom_car Ar C D]
      — blocked on the above.

    Once Step 5 is delivered, the [isMCone] / [isICone] HB instances
    follow the [path.v] / [examples_icone.v] templates with the
    test family [γ ▷ m] (Paper Def 5.4) and pointwise integral
    construction (Paper Lemma 5.4).
*)

(** ** M4 wave 2 status note legacy:

    Delivered in this commit:
    - [linhom_norm] re-defined as the canonical real-valued [sup]
      over the image norm-set (Step 1 of the wave plan). The old
      [xchoose]-witness form is no longer used in [linhom.v].
    - [linhom_normset_nonempty] / [linhom_normset_has_ubound] /
      [linhom_normset_has_sup] — sup is well-defined.
    - [linhom_norm_sup_ub] (every image norm bounded by [linhom_norm f])
      and [linhom_norm_sup_lub] (least-upper-bound property).
    - [linhom_le_pointwise] — precone-order on [linhom_car] descends to
      pointwise [≤p] in [D].
    - Cone axioms (Normh) [linhom_normh], (Normz) [linhom_normz],
      (Normt) [linhom_normt], (Normp) [linhom_normp] — fully proved
      with the canonical-sup formulation.
    - [linhom_sup_unit] — pointwise [cone_sup_ball] of [(f_n x)_n] on
      the unit ball of [C], using [linhom_norm_sup_ub] to discharge
      the unit-ball bound on each [linhom_fun (u n) x].
    - [linhom_sup_fun] — scaled extension to arbitrary [x : C] via
      the factor [(cnorm x + 1)], with the helper
      [linhom_sup_fun_unitE] reducing it to [linhom_sup_unit] on the
      unit ball.

    M4 wave 3 additions (this commit):
    - [nng_inv] — inverse of a positive [{nonneg R}].
    - [linhom_sup_fun_lin0] : [linhom_sup_fun 0 = 0].
    - [linhom_sup_fun_linZ] : [linhom_sup_fun (r *: x) = r *: linhom_sup_fun x],
      via case-split on [r = 0] and a unit-ball rescaling argument for
      [r > 0] using [sup_ball_scaler].
    - [linhom_sup_fun_at_scale] — rescaling helper: for [s > 0] with
      [s⁻¹ *: x ∈ B_C], [linhom_sup_fun x = s *: linhom_sup_unit Hxs].
      Derived from [linhom_sup_fun_linZ] + [linhom_sup_fun_unitE].
    - [linhom_sup_fun_linD] : [linhom_sup_fun (x + y) =
      linhom_sup_fun x + linhom_sup_fun y], via uniform-scaling at
      [s := cnorm x + cnorm y + 1] plus [cone_sup_ball_addD].
    - [linhom_sup_fun_norm_le] : [cnorm (linhom_sup_fun x) ≤ cnorm x].
    - [linhom_sup_fun_bounded] : the operator-norm bound [M = 1].

    Deferred to a follow-up commit (full HB tower):
    - ω-continuity of [linhom_sup_fun] — needs a "sup of sup = sup of
      diagonal" identity ([cone_sup_ball_diag]) for double sup-balls
      indexed by two parameters [(m, n)].
    - Path-preservation / integral-preservation of [linhom_sup_fun].
    - Final [isCone] HB instance registering [linhom_car] as a
      [coneType R] via the canonical-sup norm + the four norm axioms
      already in place + the [linhom_sup_ball] constructor packaged
      from [linhom_sup_fun] above.
    - [isMCone] HB instance — Paper Def 5.4 test family
      [γ ▷ m : ar_carrier Y × linhom_car -> R] with body
      [m(s, f(γ(s)))]. Mirrors [path_test] / [path_mcone_M] in
      [path.v], with proofs of (Mscomp), (Mssep), (Msnorm).
    - [isICone] HB instance — Paper Lemma 5.4: pointwise integral
      [(∫η dµ)(x) := icone_integral (r ↦ η(r)(x)) ...] in [D].
      Mirrors [path_int_fun] / [path_int_exists] in
      [examples_icone.v]. *)

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
    *forget* the cone structure on [linhom_car Ar C2 D] (which is
    not in scope until M4 wave 2). For wave 1, we register the
    "underlying-function" form of this datum and the round-trip
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
    integrable cone [C1, C2 ⊸ D = C1 ⊸ (C2 ⊸ D)]; once the
    full HB tower is in place on [linhom_car] (M4 wave 2), the maps
    [bilin_to_linhom] / [linhom_to_bilin] below become morphisms in
    [ICones], witnessing the iso [BilinIntegrable(C1, C2; D) ≃
    ICones(C1, linhom_car C2 D)]. For wave 1 we record the
    function-level content. *)

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

(** ** Sanity checks — M4 wave 1-finish deliverables

    - The [linhom_car Ar C D] type packages: linear, ω-continuous,
      bounded, measurable-path-preserving, and integral-preserving
      maps. Five fields, the same as the natural integrable-cone-
      morphism record. (Paper §5.1 + Def 5.4 + Lemma 5.4.)
    - The [linhom_zero] element is fully delivered with no axioms
      beyond [boolp].
    - The [linhom_add_fun] / [linhom_scale_fun] operations packaged
      as [linhom_car] records, with full proofs of linearity,
      ω-continuity, boundedness, path-preservation, and
      integral-preservation.
    - [cone_sup_ball_addD] — the full diagonal-sup identity in any
      [coneType], delivered above. This is the key technical lemma
      enabling ω-continuity of pointwise sum.
    - [isPrecone] HB instance on [linhom_car Ar C D] — REGISTERED.
    - [linhom_norm] defined as the operator-norm witness from M1.
    - Paper §5.2 / Def 5.6 (bilinear ↔ linhom bijection) is
      delivered at the function level via [bilin_data],
      [bilin_to_linhom], [linhom_to_bilin], and their round-trip
      lemmas [bilin_to_linhom_E] / [linhom_to_bilin_E].

    Deferred to M4 wave 2 (see status note above [LinhomNorm]):
    - [isCone] HB instance — blocked on strengthening
      [Icones.cones.basic_lemmas.linmap_norm] to be the actual
      supremum (not just an xchoose witness upper bound).
    - [isMCone] / [isICone] HB instances — follow [path.v] /
      [examples_icone.v] patterns once [isCone] is in place. *)

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
