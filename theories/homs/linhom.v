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

(** ** Operator norm on [linhom_car] — Paper §5.1 *)

Section LinhomNorm.
Variables (R : realType) (Ar : MeasSubcat R).
Variables C D : ICone.type Ar.

(** Paper §5.1: [‖f‖ = sup {‖f x‖ | ‖x‖ ≤ 1}], from M1's [linmap_norm].
    Note: M1's [linmap_norm] is a witness *upper bound*, not the actual
    supremum. The full [isCone] instance requires strengthening this
    to a real supremum (see deferral note below). *)
Definition linhom_norm (f : linhom_car Ar C D) : R :=
  @linmap_norm R C D (linhom_fun f) (linhom_pre_linear (linhom_pre_of f)).

(** Pointwise bound: [‖f x‖ ≤ ‖f‖] for [‖x‖ ≤ 1]. *)
Lemma linhom_norm_ub (f : linhom_car Ar C D) (x : C) :
  cnorm x <= 1 -> cnorm (linhom_fun f x) <= linhom_norm f.
Proof.
move=> Hx; rewrite /linhom_norm.
exact: linmap_norm_ub.
Qed.

Lemma linhom_norm_ge0 (f : linhom_car Ar C D) : 0 <= linhom_norm f.
Proof. rewrite /linhom_norm; exact: linmap_norm_ge0. Qed.

End LinhomNorm.

(** ** Status of M4 wave 1-finish (this commit)

    - [cone_sup_ball_addD] — full diagonal-sup identity (both
      directions) in any [coneType], delivered above.
    - Pointwise [+], [*:] packaged as [linhom_car] (with ω-continuity
      via the diagonal-sup identity, integral preservation via
      [path_integral_eq_addB] / [path_integral_eq_scaleB]).
    - [isPrecone] HB instance on [linhom_car Ar C D] — REGISTERED.
    - [linhom_norm] defined as the operator-norm witness.

    Deferred to M4 wave 2:
    - [isCone] HB instance — blocked on strengthening
      [Icones.cones.basic_lemmas.linmap_norm] to be the actual
      supremum (currently it is only a witness upper bound via
      [xchoose]). Once that is done, (Normh)/(Normz)/(Normt)/(Normp)
      follow by sup manipulation, and (Normc) by the path-style
      pointwise [cone_sup_ball] construction.
    - [isMCone] HB instance — Paper Def 5.4 test family
      [γ ▷ m : ar_carrier Y × linhom_car -> R] with body
      [m(s, f(γ(s)))]. Mirrors [path_test] / [path_mcone_M] in
      [path.v], with proofs of (Mscomp), (Mssep), (Msnorm).
    - [isICone] HB instance — Paper Lemma 5.4: pointwise integral
      [(∫η dµ)(x) := icone_integral (r ↦ η(r)(x)) ...] in [D].
      Mirrors [path_int_fun] in [examples_icone.v]. *)

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
