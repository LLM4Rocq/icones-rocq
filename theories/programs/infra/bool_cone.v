(**md *** PPL CBV chapter infrastructure

    This file is NOT part of the Ehrhard-Geoffroy 2025 formalization
    (paper §2-§9). It provides the 2-point cone [bool_cone_car Ar],
    interpreted as sub-probability measures on bool, as the cones-side
    denotation of the source-language [tbool] type from the CBV PPL of
    [theories/programs/ppl.v]. The cone IS (paper §4.4 / Theorem 4.24)
    the categorical coproduct [cone_one ⊕ cone_one] in ICones; the
    co-pairing [bool_case] is the universal-property eliminator.

    See also: [theories/programs/infra/bool_case_hom.v] (icones_hom packaging),
    [theories/programs/ppl.v] (ne_true, ne_false, ne_if, ne_bernoulli). *)

(** * The boolean cone — the 2-point sub-probability ICone

    This file constructs the **2-dimensional sub-probability cone**
    suitable to serve as [tyD tbool] in the PPL. The carrier is a thin
    record wrapping a pair [(p, q) : {nonneg R} * {nonneg R}], and the
    cone operations are the pointwise ones (componentwise [+],
    componentwise [*:], ω-supremum is the pointwise sup of the
    components). The norm is [p + q] (= the total mass), so the unit
    ball is exactly the set of sub-probability distributions on a
    2-point space.

    Design — **Option A**, the direct [R≥0 × R≥0] construction.
    Rationale: avoids introducing a discrete 2-point measurable space
    inside [Ar] (which would force callers to supply an [ar_obj]
    encoding [bool] before they can speak of [tbool]). Option A is
    self-contained, axiom-free, and yields the same downstream
    interface that the PPL needs:

    - [bool_dirac_true  := (1, 0)] — the Dirac at [true].
    - [bool_dirac_false := (0, 1)] — the Dirac at [false].
    - [bool_case (p, q) a b := p *: a + q *: b] — the "weighted
      decision" eliminator.

    The HB tower is established in four stages, each mirroring the
    [cone_one_car] pattern from [examples_icone.v]:

    - [isPrecone] — algebra of [(+, *:)] componentwise.
    - [isCone]    — norm [‖(p, q)‖ = p + q], ω-completeness on the
                    unit ball via componentwise [sup] in [{nonneg R}].
    - [isMCone]   — the family of selected tests is the two-point
                    family {π_true, π_false} (projection on each
                    coordinate), plus their reindexings; (Mscomp),
                    (Mssep), (Msnorm) are all directly discharged.
    - [isICone]   — Pettis integral against any finite measure on
                    any [ar_obj] returns the componentwise integral.

    *** Categorical content (paper §4.4 / Theorem 4.24)

    [bool_cone_car Ar] is the categorical coproduct
    [cone_one_car Ar ⊕ cone_one_car Ar] in ICones (paper p. 34).
    [bool_dirac_true]/[bool_dirac_false] are the injections
    [in_t(1)]/[in_f(1)]. [bool_case x a b = bc_t x · a + bc_f x · b]
    is the universal co-pairing [a, b] of paper p. 34's universal-
    property formula. The linearity-in-x ([bool_case_linear]) and
    the norm bound ([bool_case_norm_le1]) are the universal-property
    witnesses; ω-continuity ([bool_case_omega_continuous]),
    measurable-path preservation ([bool_case_pres_path]) and
    integral preservation ([bool_case_pres_int]) upgrade the
    co-pairing to a full ICones morphism ([bool_case_icones_hom],
    paper Def 4.10).
*)
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

Require Import Icones.prelude.classical_extra.
Require Import Icones.prelude.nonneg_extra.
Require Import Icones.prelude.omegacpo.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.icones.pettis.
Require Import Icones.icones.icone.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** Stage 0 — the carrier *)

Section BoolConeCar.
Variables (R : realType) (Ar : MeasSubcat R).

(** The carrier is a thin record wrapping two [{nonneg R}] components.
    The dummy [Ar] parameter is the same trick used by
    [cone_one_car]: it forces [Ar] to survive section discharge so
    that the subsequent [isMCone Ar] HB instance can be registered. *)
Record bool_cone_car (dummy : MeasSubcat R) : Type :=
  MkBoolCone { bc_t : {nonneg R}; bc_f : {nonneg R} }.

Lemma bool_cone_eq (x y : bool_cone_car Ar) :
  bc_t x = bc_t y -> bc_f x = bc_f y -> x = y.
Proof. by case: x; case: y => /= ?? ?? -> ->. Qed.

End BoolConeCar.

Arguments bool_cone_car {R}.
Arguments MkBoolCone {R}.
Arguments bc_t {R dummy}.
Arguments bc_f {R dummy}.

(** ** Stage 1 — the [isPrecone] instance *)

Section BoolConePrecone.
Variables (R : realType) (Ar : MeasSubcat R).
Local Notation T := (bool_cone_car Ar).

(** Pointwise zero / addition / scalar multiplication. *)
Definition bc_zero : T := MkBoolCone Ar 0%:nng 0%:nng.
Definition bc_add (x y : T) : T :=
  MkBoolCone Ar (nng_add (bc_t x) (bc_t y)) (nng_add (bc_f x) (bc_f y)).
Definition bc_scale (r : {nonneg R}) (x : T) : T :=
  MkBoolCone Ar (nng_mul r (bc_t x)) (nng_mul r (bc_f x)).

Lemma bc_addA : associative bc_add.
Proof.
move=> x y z; apply: bool_cone_eq; apply: nngnum_inj;
  by rewrite !nng_addE addrA.
Qed.

Lemma bc_addC : commutative bc_add.
Proof.
move=> x y; apply: bool_cone_eq; apply: nngnum_inj;
  by rewrite !nng_addE addrC.
Qed.

Lemma bc_add0 : left_id bc_zero bc_add.
Proof.
move=> x; apply: bool_cone_eq; apply: nngnum_inj;
  by rewrite nng_addE add0r.
Qed.

Lemma bc_scale_DAr (r : {nonneg R}) (x y : T) :
  bc_scale r (bc_add x y) = bc_add (bc_scale r x) (bc_scale r y).
Proof.
apply: bool_cone_eq; apply: nngnum_inj;
  by rewrite !nng_mulE !nng_addE !nng_mulE mulrDr.
Qed.

Lemma bc_scale_DAl (r s : {nonneg R}) (x : T) :
  bc_scale ((r%:num + s%:num))%:nng x =
  bc_add (bc_scale r x) (bc_scale s x).
Proof.
apply: bool_cone_eq; apply: nngnum_inj;
  by rewrite !nng_addE !nng_mulE mulrDl.
Qed.

Lemma bc_scale_A (r s : {nonneg R}) (x : T) :
  bc_scale ((r%:num * s%:num))%:nng x =
  bc_scale r (bc_scale s x).
Proof.
apply: bool_cone_eq; apply: nngnum_inj;
  by rewrite !nng_mulE mulrA.
Qed.

Lemma bc_scale_1 (x : T) : bc_scale 1%:nng x = x.
Proof.
apply: bool_cone_eq; apply: nngnum_inj;
  by rewrite /bc_scale/= mul1r.
Qed.

Lemma bc_scale_0r (r : {nonneg R}) : bc_scale r bc_zero = bc_zero.
Proof.
apply: bool_cone_eq; apply: nngnum_inj;
  by rewrite nng_mulE mulr0.
Qed.

Lemma bc_scale_0l (x : T) : bc_scale 0%:nng x = bc_zero.
Proof.
apply: bool_cone_eq; apply: nngnum_inj;
  by rewrite nng_mulE mul0r.
Qed.

Lemma bc_cancel (x y z : T) :
  bc_add x y = bc_add x z -> y = z.
Proof.
move=> H.
have /(congr1 bc_t)/= Ht := H.
have /(congr1 bc_f)/= Hf := H.
have /(congr1 (@Itv.r _ _ _)) := Ht; rewrite !nng_addE => HtE.
have /(congr1 (@Itv.r _ _ _)) := Hf; rewrite !nng_addE => HfE.
apply: bool_cone_eq.
- by apply: nngnum_inj; apply: (addrI (bc_t x)%:num).
- by apply: nngnum_inj; apply: (addrI (bc_f x)%:num).
Qed.

Lemma bc_pos (x y : T) :
  bc_add x y = bc_zero -> x = bc_zero /\ y = bc_zero.
Proof.
move=> H.
have /(congr1 bc_t)/= Ht := H.
have /(congr1 bc_f)/= Hf := H.
have Ht' : nng_add (bc_t x) (bc_t y) = 0%:nng by exact: Ht.
have Hf' : nng_add (bc_f x) (bc_f y) = 0%:nng by exact: Hf.
case: (nonneg_addr0 Ht') => Hxt Hyt.
case: (nonneg_addr0 Hf') => Hxf Hyf.
split; apply: bool_cone_eq; by rewrite ?Hxt ?Hxf ?Hyt ?Hyf.
Qed.

End BoolConePrecone.

HB.instance Definition _ (R : realType) (Ar : MeasSubcat R) :=
  @isPrecone.Build R (bool_cone_car Ar)
    (@bc_zero R Ar) (@bc_add R Ar) (@bc_scale R Ar)
    (@bc_addA R Ar) (@bc_addC R Ar) (@bc_add0 R Ar)
    (@bc_scale_DAr R Ar) (@bc_scale_DAl R Ar) (@bc_scale_A R Ar)
    (@bc_scale_1 R Ar) (@bc_scale_0r R Ar) (@bc_scale_0l R Ar)
    (@bc_cancel R Ar) (@bc_pos R Ar).

(** ** Stage 2 — the [isCone] instance

    Norm is the total mass [‖(p, q)‖ = p + q]. Order is componentwise.
    ω-supremum on the unit ball is computed componentwise via the
    sup of the underlying-real chains. *)

Section BoolConeCone.
Variables (R : realType) (Ar : MeasSubcat R).
Local Notation T := (bool_cone_car Ar).

Definition bc_norm (x : T) : R := (bc_t x)%:num + (bc_f x)%:num.

Lemma bc_normh (r : {nonneg R}) (x : T) :
  bc_norm (precone_scale r x) = r%:num * bc_norm x.
Proof. by rewrite /precone_scale/= /bc_norm /= !nng_mulE mulrDr. Qed.

(** Norm-zero detection: each coordinate is ≥ 0 and they sum to 0. *)
Lemma bc_normz (x : T) : bc_norm x = 0 -> x = precone_zero.
Proof.
move=> Hxy.
have Ht0 : (bc_t x)%:num = 0.
  apply: le_anti; apply/andP; split; last exact: nngnum_ge0.
  by rewrite -Hxy lerDl nngnum_ge0.
have Hf0 : (bc_f x)%:num = 0.
  apply: le_anti; apply/andP; split; last exact: nngnum_ge0.
  by rewrite -Hxy lerDr nngnum_ge0.
rewrite /precone_zero/=.
apply: bool_cone_eq; [exact: nonneg_eq0 | exact: nonneg_eq0].
Qed.

Lemma bc_normt (x y : T) :
  bc_norm (precone_add x y) <= bc_norm x + bc_norm y.
Proof.
rewrite /precone_add/= /bc_norm/= !nng_addE.
by rewrite addrACA lexx.
Qed.

(** Order on the wrapper is componentwise [{nonneg R}]-order. *)
Lemma bc_leE (x y : T) :
  precone_le x y <->
  (bc_t x)%:num <= (bc_t y)%:num /\ (bc_f x)%:num <= (bc_f y)%:num.
Proof.
split=> [[z Hxy]|[le_t le_f]].
  split; rewrite Hxy/= nng_addE lerDl; exact: nngnum_ge0.
have dt_ge0 : 0 <= (bc_t y)%:num - (bc_t x)%:num by rewrite subr_ge0.
have df_ge0 : 0 <= (bc_f y)%:num - (bc_f x)%:num by rewrite subr_ge0.
exists (MkBoolCone Ar (NngNum dt_ge0) (NngNum df_ge0)).
apply: bool_cone_eq; apply: nngnum_inj;
  by rewrite /= addrC subrK.
Qed.

Lemma bc_normp (x y : T) : precone_le x y -> bc_norm x <= bc_norm y.
Proof.
move=> /bc_leE [le_t le_f]; rewrite /bc_norm.
exact: lerD.
Qed.

(** *** Sup-ball construction *)

(** Each coordinate of the chain is bounded by 1: it is at most the
    norm, which is bounded by 1. *)
Lemma bc_chain_t_ub1 (u : nat -> T) (ub1 : forall n, bc_norm (u n) <= 1) n :
  (bc_t (u n))%:num <= 1.
Proof.
apply: le_trans (ub1 n).
by rewrite /bc_norm lerDl nngnum_ge0.
Qed.

Lemma bc_chain_f_ub1 (u : nat -> T) (ub1 : forall n, bc_norm (u n) <= 1) n :
  (bc_f (u n))%:num <= 1.
Proof.
apply: le_trans (ub1 n).
by rewrite /bc_norm lerDr nngnum_ge0.
Qed.

Lemma bc_sup_t_ge0
    (u : nat -> T) (ub1 : forall n, bc_norm (u n) <= 1) :
  0 <= sup [set (bc_t (u n))%:num | n in [set: nat]].
Proof.
set S : set R := [set _ | _ in _].
have S_has_ubound : has_ubound S
  by exists 1 => x [m _ <-]; exact: bc_chain_t_ub1.
have ub_sup : ubound S (sup S) by exact: ub_le_sup.
apply: le_trans (nngnum_ge0 (bc_t (u 0%N))) _.
by apply: ub_sup; exists 0%N.
Qed.

Lemma bc_sup_f_ge0
    (u : nat -> T) (ub1 : forall n, bc_norm (u n) <= 1) :
  0 <= sup [set (bc_f (u n))%:num | n in [set: nat]].
Proof.
set S : set R := [set _ | _ in _].
have S_has_ubound : has_ubound S
  by exists 1 => x [m _ <-]; exact: bc_chain_f_ub1.
have ub_sup : ubound S (sup S) by exact: ub_le_sup.
apply: le_trans (nngnum_ge0 (bc_f (u 0%N))) _.
by apply: ub_sup; exists 0%N.
Qed.

Definition bc_sup_ball
    (u : nat -> T)
    (_ : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, bc_norm (u n) <= 1) : T :=
  MkBoolCone Ar (NngNum (bc_sup_t_ge0 ub1)) (NngNum (bc_sup_f_ge0 ub1)).

Lemma bc_sup_ball_tE
    (u : nat -> T)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, bc_norm (u n) <= 1) :
  (bc_t (bc_sup_ball uch ub1))%:num =
  sup [set (bc_t (u n))%:num | n in [set: nat]].
Proof. by []. Qed.

Lemma bc_sup_ball_fE
    (u : nat -> T)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, bc_norm (u n) <= 1) :
  (bc_f (bc_sup_ball uch ub1))%:num =
  sup [set (bc_f (u n))%:num | n in [set: nat]].
Proof. by []. Qed.

Lemma bc_sup_ball_ub
    (u : nat -> T)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, bc_norm (u n) <= 1) n :
  precone_le (u n) (bc_sup_ball uch ub1).
Proof.
apply/bc_leE; split.
- rewrite bc_sup_ball_tE.
  set S : set R := [set _ | _ in _].
  have S_has_ubound : has_ubound S
    by exists 1 => x [m _ <-]; exact: bc_chain_t_ub1.
  have ub_sup : ubound S (sup S) by exact: ub_le_sup.
  by apply: ub_sup; exists n.
- rewrite bc_sup_ball_fE.
  set S : set R := [set _ | _ in _].
  have S_has_ubound : has_ubound S
    by exists 1 => x [m _ <-]; exact: bc_chain_f_ub1.
  have ub_sup : ubound S (sup S) by exact: ub_le_sup.
  by apply: ub_sup; exists n.
Qed.

Lemma bc_sup_ball_lub
    (u : nat -> T)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, bc_norm (u n) <= 1) (y : T) :
  (forall n, precone_le (u n) y) ->
  precone_le (bc_sup_ball uch ub1) y.
Proof.
move=> H; apply/bc_leE; split.
- rewrite bc_sup_ball_tE.
  set S : set R := [set _ | _ in _].
  have S_nonempty : S !=set0 by exists (bc_t (u 0))%:num; exists 0%N.
  apply: ge_sup; first exact: S_nonempty.
  by move=> x [n _ <-]; have /bc_leE [Ht _] := H n.
- rewrite bc_sup_ball_fE.
  set S : set R := [set _ | _ in _].
  have S_nonempty : S !=set0 by exists (bc_f (u 0))%:num; exists 0%N.
  apply: ge_sup; first exact: S_nonempty.
  by move=> x [n _ <-]; have /bc_leE [_ Hf] := H n.
Qed.

(** The sup-ball lies in the unit ball.

    Proof: each coordinate sup is bounded by [1 - lim_n (other coord)],
    but it is simpler to bound the *sum* directly. For each [n],
    [t_n + f_n ≤ 1] (the chain is in the ball). The coordinates form
    increasing chains, so their sups are limits. Pass to the limit:
    [sup_t + sup_f ≤ 1]. We avoid limits and use [le_sup] arguments. *)
Lemma bc_sup_ball_norm
    (u : nat -> T)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, bc_norm (u n) <= 1) :
  bc_norm (bc_sup_ball uch ub1) <= 1.
Proof.
rewrite /bc_norm bc_sup_ball_tE bc_sup_ball_fE.
set St : set R := [set _ | _ in _].
set Sf : set R := [set _ | _ in _].
have ch_t : forall n, (bc_t (u n))%:num <= (bc_t (u n.+1))%:num
  by move=> n; have /bc_leE [-> _] := uch n.
have ch_f : forall n, (bc_f (u n))%:num <= (bc_f (u n.+1))%:num
  by move=> n; have /bc_leE [_ ->] := uch n.
have St_bd : has_ubound St
  by exists 1 => x [n _ <-]; exact: bc_chain_t_ub1.
have Sf_bd : has_ubound Sf
  by exists 1 => x [n _ <-]; exact: bc_chain_f_ub1.
have St_ne : St !=set0 by exists (bc_t (u 0%N))%:num; exists 0%N.
have Sf_ne : Sf !=set0 by exists (bc_f (u 0%N))%:num; exists 0%N.
(** Strategy: bound [sup St + sup Sf] by [1] using that the sum
    [t_n + f_n ≤ 1] holds for all [n], and the partial-order
    relationship of sups with sums.

    We use: for all [n m], [t_n + f_m ≤ 1] (by monotonicity, take
    [max n m]). Hence [sup St + sup Sf ≤ 1].

    Concretely we apply: [sup St ≤ 1 - sup Sf] would require
    [t_n ≤ 1 - sup Sf] for all [n], i.e. [t_n + sup Sf ≤ 1].
    By [sup Sf = sup_m f_m] and using monotonicity with [n], this is
    [t_n + sup_{m ≥ n} f_m ≤ 1], which holds by taking the sup of
    [t_n + f_m ≤ 1] over [m ≥ n] (since [t_n] is fixed). *)
have chain_mono : forall n m, (n <= m)%N ->
    (bc_t (u n))%:num <= (bc_t (u m))%:num /\
    (bc_f (u n))%:num <= (bc_f (u m))%:num.
  move=> n m; elim: m => [|m IH]; first by rewrite leqn0=> /eqP ->.
  rewrite leq_eqVlt => /orP[/eqP ->|]; first by [].
  rewrite ltnS => /IH [Ht Hf]; split.
  - exact: le_trans Ht (ch_t m).
  - exact: le_trans Hf (ch_f m).
(** Step 1: for each [n], [t_n + sup Sf ≤ 1]. *)
have step1 : forall n, (bc_t (u n))%:num + sup Sf <= 1.
  move=> n.
  have ineq : forall m, (bc_t (u n))%:num + (bc_f (u m))%:num <= 1.
    move=> m.
    pose k := maxn n m.
    have nk : (n <= k)%N by exact: leq_maxl.
    have mk : (m <= k)%N by exact: leq_maxr.
    have [Ht _] := chain_mono _ _ nk.
    have [_ Hf] := chain_mono _ _ mk.
    apply: le_trans _ (ub1 k).
    by rewrite /bc_norm; apply: lerD.
  rewrite -lerBrDl.
  apply: ge_sup; first exact: Sf_ne.
  move=> x [m _ <-].
  by rewrite lerBrDl; exact: ineq.
(** Step 2: [sup St + sup Sf ≤ 1]. *)
rewrite -lerBrDr.
apply: ge_sup; first exact: St_ne.
move=> x [n _ <-].
by rewrite lerBrDr; exact: step1.
Qed.

End BoolConeCone.

HB.instance Definition _ (R : realType) (Ar : MeasSubcat R) :=
  @isCone.Build R (bool_cone_car Ar)
    (@bc_norm R Ar)
    (@bc_normh R Ar) (@bc_normz R Ar) (@bc_normt R Ar) (@bc_normp R Ar)
    (@bc_sup_ball R Ar)
    (@bc_sup_ball_ub R Ar) (@bc_sup_ball_lub R Ar) (@bc_sup_ball_norm R Ar).

(** ** Stage 3 — the [isMCone] instance

    Tests on [bool_cone_car] at arity [Y] are indexed by an [option
    bool]:

    - [Some true]  — the projection [π_t : (p, q) ↦ p].
    - [Some false] — the projection [π_f : (p, q) ↦ q].
    - [None]       — the *norm* test [‖(p, q)‖ = p + q].

    (Mssep) holds because the two projections separate; (Msnorm) at
    arity 0 holds for the norm test (with [eps] slack from the
    eps>0 condition); reindexing is trivial since all three test
    families are constant in the arity parameter. *)

Module BoolConeMConeAux.
Section BoolConeMConeAux.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation T := (bool_cone_car Ar).

(** Test indexed by [option bool]:
    - [Some b] gives the coordinate projection (true → bc_t, false → bc_f);
    - [None] gives the norm [bc_t + bc_f]. *)
Definition bc_test_val (o : option bool) (x : T) : R :=
  match o with
  | Some true  => (bc_t x)%:num
  | Some false => (bc_f x)%:num
  | None       => (bc_t x)%:num + (bc_f x)%:num
  end.

(** All eight test laws for [bc_test_val o] at any arity [Y]. We
    parameterize the constructions by [(Y, o)] as explicit arguments
    rather than section variables — this avoids opacity of section
    variables that blocks [case: o] from substituting in hypotheses. *)

Definition bool_test_fun (Y : ar_obj Ar) (o : option bool)
    : ar_carrier Ar Y -> T -> R :=
  fun _ x => bc_test_val o x.

Lemma bool_test_meas (Y : ar_obj Ar) (o : option bool) (x : T) :
  cone_norm x <= 1 ->
  measurable_fun setT (fun r => @bool_test_fun Y o r x).
Proof. by move=> _; exact: measurable_cst. Qed.

Lemma bool_test_ge0 (Y : ar_obj Ar) (o : option bool)
    (r : ar_carrier Ar Y) (x : T) :
  0 <= @bool_test_fun Y o r x.
Proof.
rewrite /bool_test_fun /bc_test_val.
by case: o => [[]|]; rewrite ?addr_ge0 ?nngnum_ge0.
Qed.

Lemma bool_test_le1 (Y : ar_obj Ar) (o : option bool)
    (r : ar_carrier Ar Y) (x : T) :
  cone_norm x <= 1 -> @bool_test_fun Y o r x <= 1.
Proof.
move=> Hnorm.
have Hxy : (bc_t x)%:num + (bc_f x)%:num <= 1.
  by have := Hnorm; rewrite /cone_norm/= /bc_norm.
rewrite /bool_test_fun /bc_test_val.
case: o => [[]|]//.
- by rewrite (le_trans _ Hxy)// lerDl nngnum_ge0.
- by rewrite (le_trans _ Hxy)// lerDr nngnum_ge0.
Qed.

Lemma bool_test_lin0 (Y : ar_obj Ar) (o : option bool)
    (r : ar_carrier Ar Y) :
  @bool_test_fun Y o r precone_zero = 0.
Proof.
rewrite /bool_test_fun /bc_test_val.
by case: o => [[]|]//=; rewrite ?addr0.
Qed.

Lemma bool_test_linD (Y : ar_obj Ar) (o : option bool)
    (r : ar_carrier Ar Y) (x y : T) :
  @bool_test_fun Y o r (precone_add x y) =
  @bool_test_fun Y o r x + @bool_test_fun Y o r y.
Proof.
rewrite /bool_test_fun /bc_test_val /precone_add/=.
case: o => [[]|]//=; rewrite !nng_addE//.
by rewrite addrACA.
Qed.

Lemma bool_test_linZ (Y : ar_obj Ar) (o : option bool)
    (r : ar_carrier Ar Y) (s : {nonneg R}) (x : T) :
  @bool_test_fun Y o r (precone_scale s x) =
  s%:num * @bool_test_fun Y o r x.
Proof.
rewrite /bool_test_fun /bc_test_val /precone_scale/=.
case: o => [[]|]//=; rewrite ?nng_mulE//.
by rewrite mulrDr.
Qed.

(** ω-continuity: each test value at the sup-ball equals the sup of
    the test values along the chain. *)
Lemma bool_test_cont (Y : ar_obj Ar) (o : option bool)
    (r : ar_carrier Ar Y) (u : nat -> T)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, cone_norm (u n) <= 1)
    (N : R) :
  (forall n, @bool_test_fun Y o r (u n) <= N) ->
  @bool_test_fun Y o r (cone_sup_ball u uch ub1) <= N.
Proof.
rewrite /bool_test_fun /bc_test_val /cone_sup_ball/=.
case: o => [[]|] HN.
- (* Some true: sup of bc_t. *)
  apply: ge_sup.
  + by exists (bc_t (u 0%N))%:num; exists 0%N.
  + by move=> y [n _ <-]; exact: HN.
- (* Some false: sup of bc_f. *)
  apply: ge_sup.
  + by exists (bc_f (u 0%N))%:num; exists 0%N.
  + by move=> y [n _ <-]; exact: HN.
- (* None: sup of t + f. Reuse the maxn argument from bc_sup_ball_norm. *)
  set St : set R := [set (bc_t (u n))%:num | n in [set: nat]].
  set Sf : set R := [set (bc_f (u n))%:num | n in [set: nat]].
  have ch_t : forall n, (bc_t (u n))%:num <= (bc_t (u n.+1))%:num
    by move=> n; have /bc_leE [-> _] := uch n.
  have ch_f : forall n, (bc_f (u n))%:num <= (bc_f (u n.+1))%:num
    by move=> n; have /bc_leE [_ ->] := uch n.
  have chain_mono : forall n m, (n <= m)%N ->
      (bc_t (u n))%:num <= (bc_t (u m))%:num /\
      (bc_f (u n))%:num <= (bc_f (u m))%:num.
    move=> n m; elim: m => [|m IH]; first by rewrite leqn0=> /eqP ->.
    rewrite leq_eqVlt => /orP[/eqP ->|]; first by [].
    rewrite ltnS => /IH [Ht Hf]; split.
    - exact: le_trans Ht (ch_t m).
    - exact: le_trans Hf (ch_f m).
  have St_ne : St !=set0 by exists (bc_t (u 0%N))%:num; exists 0%N.
  have Sf_ne : Sf !=set0 by exists (bc_f (u 0%N))%:num; exists 0%N.
  have step1 : forall n, (bc_t (u n))%:num + sup Sf <= N.
    move=> n.
    rewrite -lerBrDl.
    apply: ge_sup; first exact: Sf_ne.
    move=> x [m _ <-].
    rewrite lerBrDl.
    pose k := maxn n m.
    have nk : (n <= k)%N by exact: leq_maxl.
    have mk : (m <= k)%N by exact: leq_maxr.
    have [Ht _] := chain_mono _ _ nk.
    have [_ Hf] := chain_mono _ _ mk.
    by apply: le_trans _ (HN k); apply: lerD.
  rewrite -lerBrDr.
  apply: ge_sup; first exact: St_ne.
  move=> x [n _ <-].
  by rewrite lerBrDr; exact: step1.
Qed.

(** Each test is bounded by the norm. *)
Lemma bool_test_norm_le (Y : ar_obj Ar) (o : option bool)
    (r : ar_carrier Ar Y) (x : T) :
  @bool_test_fun Y o r x <= cone_norm x.
Proof.
rewrite /bool_test_fun /bc_test_val /cone_norm/= /bc_norm.
by case: o => [[]|]//; rewrite ?lerDl ?lerDr nngnum_ge0.
Qed.

Definition bool_test (Y : ar_obj Ar) (o : option bool) : test_of Ar Y T :=
  MkTestOf (@bool_test_meas Y o) (@bool_test_ge0 Y o) (@bool_test_le1 Y o)
           (@bool_test_lin0 Y o) (@bool_test_linD Y o) (@bool_test_linZ Y o)
           (@bool_test_cont Y o) (@bool_test_norm_le Y o).

(** The family at arity [Y] is the image of the three tags
    [{bool_test None, bool_test (Some true), bool_test (Some false)}]. *)
Definition mcone_M_bool (Y : ar_obj Ar) : set (test_of Ar Y T) :=
  [set bool_test Y o | o in [set: option bool]].

(** (Mscomp): reindexing of any tagged test is the same tagged test
    at the new arity (test function is constant in the arity). *)
Lemma mcone_M_bool_comp (Y X : ar_obj Ar) (φ : ar_hom Ar Y X)
    (m : test_of Ar X T) :
  mcone_M_bool m -> mcone_M_bool (test_reindex φ m).
Proof.
move=> [o _ <-].
exists o => //.
apply: test_eq => s x.
by rewrite /test_reindex/= /test_reindex_fun /bool_test/= /bool_test_fun.
Qed.

(** (Mssep): two cone elements agreeing on both projections (the
    [Some true] and [Some false] tags) at arity 0 are equal. *)
Lemma mcone_M_bool_sep (x1 x2 : T) :
  (forall m : test_of Ar (ar_zero Ar) T,
    mcone_M_bool m ->
    test_fun m (ar_zero_pt Ar) x1 = test_fun m (ar_zero_pt Ar) x2) ->
  x1 = x2.
Proof.
move=> Hsep.
have Ht : (bc_t x1)%:num = (bc_t x2)%:num.
  by apply: (Hsep (bool_test (ar_zero Ar) (Some true))); exists (Some true).
have Hf : (bc_f x1)%:num = (bc_f x2)%:num.
  by apply: (Hsep (bool_test (ar_zero Ar) (Some false))); exists (Some false).
by apply: bool_cone_eq; apply: nngnum_inj.
Qed.

(** (Msnorm) at arity 0. The [None]-tagged test *is* the norm, so
    [‖x‖ = test_fun m … x ≤ test_fun m … x + eps] (with [eps > 0]). *)
Lemma mcone_M_bool_norm (x : T) (eps : R) :
  x <> precone_zero -> 0 < eps ->
  exists m : test_of Ar (ar_zero Ar) T,
    mcone_M_bool m /\
    cone_norm x <= test_fun m (ar_zero_pt Ar) x + eps.
Proof.
move=> _ eps_pos.
exists (bool_test (ar_zero Ar) None); split; first by exists None.
rewrite /bool_test/= /bool_test_fun /bc_test_val /cone_norm/= /bc_norm.
by rewrite ltW// ltrDl.
Qed.

End BoolConeMConeAux.
End BoolConeMConeAux.

(** Register the [isMCone] instance on [bool_cone_car Ar]. *)
HB.instance Definition _ (R : realType) (Ar : MeasSubcat R) :=
  @isMCone.Build R Ar (bool_cone_car Ar)
    (@BoolConeMConeAux.mcone_M_bool R Ar)
    (@BoolConeMConeAux.mcone_M_bool_comp R Ar)
    (@BoolConeMConeAux.mcone_M_bool_sep R Ar)
    (@BoolConeMConeAux.mcone_M_bool_norm R Ar).

(** ** Stage 4 — the [isICone] instance

    For [β : ar_carrier X → bool_cone_car Ar] (measurable path) and
    [µ : fmeas R (ar_carrier X)], the integral is the
    componentwise integral wrapped as a [bool_cone_car]:

      [(fine ∫ (bc_t (β r))%:num µ(dr), fine ∫ (bc_f (β r))%:num µ(dr))]

    The construction mirrors [cone_one_int] for the [⊥] cone: each
    coordinate's integral is finite (the integrand is bounded by the
    path's uniform [M] and the measure is finite), non-negative, and
    satisfies the Pettis equation against each of the three tests in
    [mcone_M_bool]. *)

Section BoolConeICone.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation T := (bool_cone_car Ar).

Local Open Scope ereal_scope.

(** Helper: each coordinate of [β r] is measurable. The proof
    pattern is identical to [cone_one_int_fin] but specialized to a
    bool-tagged test. *)
Lemma bool_coord_meas
    (X : ar_obj Ar)
    (β : ar_carrier Ar X -> T)
    (Hβ : is_measurable_path β)
    (b : bool) :
  measurable_fun setT
    (fun r => ((if b then (bc_t (β r))%:num
                     else (bc_f (β r))%:num))%:E).
Proof.
case: Hβ => [_ Hmeas].
apply/measurable_EFinP.
pose m := BoolConeMConeAux.bool_test (Ar:=Ar) (ar_zero Ar) (Some b).
have mM : @mcone_M R Ar _ (ar_zero Ar) m by exists (Some b).
pose F (p : ar_carrier Ar (ar_zero Ar) * ar_carrier Ar X) : R :=
  test_fun m p.1 (β p.2).
have HmeasF : measurable_fun
    [set: (ar_carrier Ar (ar_zero Ar) * ar_carrier Ar X)%type] F.
  exact: Hmeas.
have HFeq : forall r,
    (if b then (bc_t (β r))%:num else (bc_f (β r))%:num)
    = F (ar_zero_pt Ar, r).
  move=> r.
  by rewrite /F /m /BoolConeMConeAux.bool_test/=
             /BoolConeMConeAux.bool_test_fun
             /BoolConeMConeAux.bc_test_val.
have -> : (fun r => if b then (bc_t (β r))%:num
                        else (bc_f (β r))%:num) =
          (fun r => F (ar_zero_pt Ar, r)).
  by apply: funext.
apply: (measurableT_comp (f := F)) => //.
Qed.

(** Helper: the componentwise integral is finite. *)
Lemma bool_int_fin
    (X : ar_obj Ar)
    (β : ar_carrier Ar X -> T)
    (Hβ : is_measurable_path β)
    (µ : fmeas R (ar_carrier Ar X))
    (b : bool) :
  \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X])
    ((if b then (bc_t (β r))%:num
            else (bc_f (β r))%:num))%:E \is a fin_num.
Proof.
(** Strategy: show finiteness uniformly in [b]. We isolate the
    coordinate-specific arguments inside a helper that branches on
    [b] *first*, then exposes [bc_t]/[bc_f] without an [if]. *)
suff aux : forall (γ : ar_carrier Ar X -> {nonneg R}),
    (forall r, ((γ r)%:num <= cone_norm (β r))%R) ->
    measurable_fun setT (fun r => ((γ r)%:num)%:E) ->
    \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X]) ((γ r)%:num)%:E
       \is a fin_num.
  have meas_b := bool_coord_meas Hβ b.
  case: b meas_b => meas_b.
  - apply: (aux (fun r => bc_t (β r))).
    + by move=> r; rewrite /cone_norm/= /bc_norm lerDl nngnum_ge0.
    + by [].
  - apply: (aux (fun r => bc_f (β r))).
    + by move=> r; rewrite /cone_norm/= /bc_norm lerDr nngnum_ge0.
    + by [].
move=> γ Hbd meas_γ.
case: Hβ => [[M HM] _].
have HM_b r : ((γ r)%:num)%:E <= M%:E.
  by rewrite lee_fin; apply: le_trans (Hbd r) (HM r).
apply: fin_real.
apply/andP; split.
  apply: (@lt_le_trans _ _ 0); first by rewrite ltNyr.
  by apply: integral_ge0 => r _; rewrite lee_fin nngnum_ge0.
pose Mp : R := Num.max M 0%R.
have HMp : (0 <= Mp)%R by rewrite le_max lexx orbT.
have HMb r : ((γ r)%:num)%:E <= Mp%:E.
  rewrite lee_fin; apply: le_trans (Hbd r) _.
  by apply: le_trans (HM r) _; rewrite le_max lexx.
apply: (@le_lt_trans _ _ (Mp%:E * fmeas_mu µ [set: ar_carrier Ar X])).
  have -> : Mp%:E * fmeas_mu µ [set: ar_carrier Ar X] =
            \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X]) (cst Mp%:E) r.
    by rewrite integral_cst.
  apply: ge0_le_integral.
  - exact: measurableT.
  - by move=> r _; rewrite lee_fin nngnum_ge0.
  - exact: meas_γ.
  - exact: measurable_cst.
  - by move=> r _; exact: HMb.
have HfinT : fmeas_mu µ [set: ar_carrier Ar X] \is a fin_num
  by exact: fmeas_setT_fin.
apply: lte_mul_pinfty => //.
by rewrite ltey_eq HfinT.
Qed.

(** Helper: the value of the integral is non-negative (so the
    componentwise integral can be wrapped as a [{nonneg R}]). *)
Lemma bool_int_ge0
    (X : ar_obj Ar)
    (β : ar_carrier Ar X -> T)
    (µ : fmeas R (ar_carrier Ar X))
    (b : bool) :
  (0 <= fine (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X])
                ((if b then (bc_t (β r))%:num
                        else (bc_f (β r))%:num))%:E))%R.
Proof.
apply: fine_ge0.
by apply: integral_ge0 => r _; rewrite lee_fin; case: b; exact: nngnum_ge0.
Qed.

(** The componentwise integral, wrapped as a [bool_cone_car]. *)
Definition bool_int
    (X : ar_obj Ar)
    (β : ar_carrier Ar X -> T)
    (_ : is_measurable_path β)
    (µ : fmeas R (ar_carrier Ar X)) : T :=
  MkBoolCone Ar
    (NngNum (bool_int_ge0 β µ true))
    (NngNum (bool_int_ge0 β µ false)).

(** Pettis equation: for each test in the family, [test_fun m s
    bool_int = fine ∫ test_fun m s (β r) dµ]. We do this for each
    of the three tag-cases. *)
Lemma bool_int_pettis
    (X : ar_obj Ar)
    (β : ar_carrier Ar X -> T)
    (Hβ : is_measurable_path β)
    (µ : fmeas R (ar_carrier Ar X)) :
  path_integral_eq β µ (bool_int Hβ µ).
Proof.
move=> m mM s.
case: mM => o _ <-.
rewrite /BoolConeMConeAux.bool_test/= /BoolConeMConeAux.bool_test_fun
        /BoolConeMConeAux.bc_test_val.
case: o => [[]|]/=.
- (* Some true: t-coordinate integral. *)
  by rewrite /bool_int.
- (* Some false: f-coordinate integral. *)
  by rewrite /bool_int.
- (* None: total mass = sum of the two integrals. *)
  rewrite /bool_int/=.
  have meas_t := bool_coord_meas Hβ true.
  have meas_f := bool_coord_meas Hβ false.
  have fin_t := bool_int_fin Hβ µ true.
  have fin_f := bool_int_fin Hβ µ false.
  have -> :
    \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X])
      ((bc_t (β r))%:num + (bc_f (β r))%:num)%:E =
    \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X])
      (((bc_t (β r))%:num)%:E + ((bc_f (β r))%:num)%:E).
    by apply: eq_integral => r _; rewrite EFinD.
  rewrite ge0_integralD.
  + by rewrite -fineD.
  + exact: measurableT.
  + by move=> r _; rewrite lee_fin nngnum_ge0.
  + exact: meas_t.
  + by move=> r _; rewrite lee_fin nngnum_ge0.
  + exact: meas_f.
Qed.

(** Existence of the integral for every measurable path. *)
Lemma bool_int_exists
    (X : ar_obj Ar)
    (β : ar_carrier Ar X -> T) :
  is_measurable_path β ->
  forall µ : fmeas R (ar_carrier Ar X),
    is_path_integrable β µ.
Proof.
move=> Hβ µ.
exists (bool_int Hβ µ); exact: bool_int_pettis.
Qed.

End BoolConeICone.

(** Register the [isICone] instance on [bool_cone_car Ar]. *)
HB.instance Definition _ (R : realType) (Ar : MeasSubcat R) :=
  @isICone.Build R Ar (bool_cone_car Ar)
    (@bool_int_exists R Ar).

(** ** Constants and the case-analysis morphism *)

Section BoolConeConstants.
Variables (R : realType) (Ar : MeasSubcat R).
Local Notation T := (bool_cone_car Ar).

(** The Dirac at [true]: the sub-probability that puts all mass on the
    [true] coordinate. *)
Definition bool_dirac_true : T := MkBoolCone Ar 1%:nng 0%:nng.

(** The Dirac at [false]: the sub-probability that puts all mass on
    the [false] coordinate. *)
Definition bool_dirac_false : T := MkBoolCone Ar 0%:nng 1%:nng.

(** Both Diracs have norm 1 (= are total probability measures). *)
Lemma bool_dirac_true_norm : cone_norm bool_dirac_true = 1.
Proof. by rewrite /cone_norm/= /bc_norm/= addr0. Qed.

Lemma bool_dirac_false_norm : cone_norm bool_dirac_false = 1.
Proof. by rewrite /cone_norm/= /bc_norm/= add0r. Qed.

(** *** The case morphism

    [bool_case x a b := (bc_t x) *: a + (bc_f x) *: b] : the
    "weighted decision" eliminator. For a sub-probability
    [(p, q) : bool_cone], picking [a] with probability [p] and
    [b] with probability [q] in any target cone [A].

    Linearity in [x] is direct: scaling and addition on
    [bool_cone] are componentwise, and the formula is bilinear in
    [(bc_t x, bc_f x)]. *)

Section BoolCase.
Variable A : preconeType R.

Definition bool_case (x : T) (a b : A) : A :=
  precone_add
    (precone_scale (bc_t x) a)
    (precone_scale (bc_f x) b).

(** [bool_case bool_dirac_true a b = a]: the Dirac at [true] picks
    [a] with full weight. *)
Lemma bool_case_true (a b : A) : bool_case bool_dirac_true a b = a.
Proof.
rewrite /bool_case /bool_dirac_true/=.
rewrite precone_scale_1 precone_scale_0l.
by rewrite precone_addC precone_add0.
Qed.

(** [bool_case bool_dirac_false a b = b]: the Dirac at [false] picks
    [b] with full weight. *)
Lemma bool_case_false (a b : A) : bool_case bool_dirac_false a b = b.
Proof.
rewrite /bool_case /bool_dirac_false/=.
rewrite precone_scale_0l precone_scale_1.
by rewrite precone_add0.
Qed.

(** [bool_case 0 a b = 0]: the zero sub-probability returns zero. *)
Lemma bool_case_zero (a b : A) :
  bool_case precone_zero a b = precone_zero.
Proof.
rewrite /bool_case /precone_zero/= /bc_zero/=.
rewrite !precone_scale_0l.
by rewrite precone_add0.
Qed.

(** [bool_case] is additive in [x]. *)
(** Helper: a [precone_add]-ACA lemma, the "interchange" /
    "Eckmann-Hilton" identity in commutative monoid notation. *)
Lemma precone_addACA (p q r s : A) :
  precone_add (precone_add p q) (precone_add r s) =
  precone_add (precone_add p r) (precone_add q s).
Proof.
rewrite -precone_addA [precone_add q _]precone_addA.
rewrite [precone_add q r]precone_addC.
by rewrite -precone_addA precone_addA.
Qed.

Lemma bool_case_addD (x y : T) (a b : A) :
  bool_case (precone_add x y) a b =
  precone_add (bool_case x a b) (bool_case y a b).
Proof.
rewrite /bool_case /precone_add/= /bc_add/=.
rewrite !precone_scale_DAl.
(* (t_x + t_y) *: a + (f_x + f_y) *: b
   = (t_x *: a + t_y *: a) + (f_x *: b + f_y *: b) *)
(* Want: (t_x *: a + t_y *: a) + (f_x *: b + f_y *: b)
       = (t_x *: a + f_x *: b) + (t_y *: a + f_y *: b)  [ACA] *)
exact: precone_addACA.
Qed.

(** [bool_case] is homogeneous in [x] (linear under a scalar [r]). *)
Lemma bool_case_scaleZ (r : {nonneg R}) (x : T) (a b : A) :
  bool_case (precone_scale r x) a b =
  precone_scale r (bool_case x a b).
Proof.
rewrite /bool_case /bc_scale/=.
rewrite precone_scale_DAr -!precone_scale_A.
congr (_ + _)%PC; congr (_ *: _)%PC; apply: nngnum_inj;
  by rewrite nng_mulE.
Qed.

(** Linearity of [bool_case x a b] in [x], packaged as a record. *)
Lemma bool_case_linear (a b : A) : is_linear (fun x : T => bool_case x a b).
Proof.
split.
- rewrite /bool_case /precone_zero/= /bc_zero/=.
  by rewrite !precone_scale_0l precone_add0.
- by move=> x y; exact: bool_case_addD.
- by move=> r x; exact: bool_case_scaleZ.
Qed.

End BoolCase.

End BoolConeConstants.

Arguments bool_dirac_true {R Ar}.
Arguments bool_dirac_false {R Ar}.
Arguments bool_case {R Ar A}.

(** ** Norm-boundedness and ω-continuity of [bool_case] on the unit ball *)

Section BoolCaseCone.
Variables (R : realType) (Ar : MeasSubcat R) (A : coneType R).
Local Notation T := (bool_cone_car Ar).

(** When the two "branches" [a, b : A] are in the unit ball,
    [bool_case x a b] is norm-bounded by [‖x‖]. *)
Lemma bool_case_norm_le1
    (a b : A) (Ha : cone_norm a <= 1) (Hb : cone_norm b <= 1) (x : T) :
  cone_norm (bool_case x a b) <= cone_norm x.
Proof.
rewrite /bool_case /cone_norm/= /bc_norm.
apply: (le_trans (cone_normt _ _)).
rewrite !cone_normh.
have Hna : 0 <= cone_norm a by apply: cone_norm_ge0.
have Hnb : 0 <= cone_norm b by apply: cone_norm_ge0.
have Htax : (bc_t x)%:num * cone_norm a <= (bc_t x)%:num.
  by rewrite -[X in _ <= X]mulr1; apply: ler_wpM2l; [exact: nngnum_ge0|].
have Hfbx : (bc_f x)%:num * cone_norm b <= (bc_f x)%:num.
  by rewrite -[X in _ <= X]mulr1; apply: ler_wpM2l; [exact: nngnum_ge0|].
exact: lerD.
Qed.

(** Generalized norm bound: for ARBITRARY [a, b : A] (no unit-ball
    assumption), [‖bool_case x a b‖ ≤ bc_t(x)·‖a‖ + bc_f(x)·‖b‖].  This
    is the load-bearing bound for the env-dependent [case_em] of paper
    §5 (Step 5b): with [a, b] arising as the codomain values of
    coalg_homs that need not be norm-bounded by 1, we still get a
    bilinearity-style decomposition of the norm. *)
Lemma bool_case_norm (a b : A) (x : T) :
  cone_norm (bool_case x a b)
  <= (bc_t x)%:num * cone_norm a + (bc_f x)%:num * cone_norm b.
Proof.
rewrite /bool_case /cone_norm/= /bc_norm.
apply: (le_trans (cone_normt _ _)).
by rewrite !cone_normh.
Qed.

(** Looser global bound used by the ω-continuity argument: when both
    branches are bounded by some common [M ≥ ‖a‖, ‖b‖], we get
    [‖bool_case x a b‖ ≤ ‖x‖ · M].  Follows from [bool_case_norm]. *)
Lemma bool_case_norm_le_max (a b : A) (M : R)
    (HMa : cone_norm a <= M) (HMb : cone_norm b <= M) (HM0 : 0 <= M)
    (x : T) :
  cone_norm (bool_case x a b) <= cone_norm x * M.
Proof.
apply: le_trans (bool_case_norm a b x) _.
rewrite /cone_norm/= /bc_norm mulrDl.
apply: lerD.
- by apply: ler_wpM2l => //; exact: nngnum_ge0.
- by apply: ler_wpM2l => //; exact: nngnum_ge0.
Qed.

End BoolCaseCone.

(** ** Scalar sup-distributivity — substep 2a of ω-continuity

    A small real-analysis lemma needed to lift [bool_case]'s ω-continuity
    through (Mssep).  For two non-negative chains [t, f : nat -> R] in
    [[0,1]] with [t_n + f_n <= 1] and scalars [α, β >= 0]:
    [[
       (sup_n t_n) * α + (sup_n f_n) * β = sup_n (t_n * α + f_n * β).
    ]]
    We prove both inequalities by hand using [ge_sup]/[ub_le_sup]; the
    "max-of-indices" trick from [bc_sup_ball_norm] reappears for the
    [≤] direction. *)

Section BoolCaseScalar.
Variable R : realType.

Lemma bool_case_sup_distrib
    (tn fn : nat -> R) (alpha beta : R)
    (Halpha : 0 <= alpha) (Hbeta : 0 <= beta)
    (Htch : forall n, tn n <= tn n.+1)
    (Hfch : forall n, fn n <= fn n.+1)
    (Htge0 : forall n, 0 <= tn n) (Hfge0 : forall n, 0 <= fn n)
    (Hsum : forall n, tn n + fn n <= 1) :
  sup [set tn n | n in [set: nat]] * alpha
  + sup [set fn n | n in [set: nat]] * beta
  = sup [set tn n * alpha + fn n * beta | n in [set: nat]].
Proof.
set St : set R := [set tn n | n in [set: nat]].
set Sf : set R := [set fn n | n in [set: nat]].
set Sc : set R := [set tn n * alpha + fn n * beta | n in [set: nat]].
have St_ne : St !=set0 by exists (tn 0%N); exists 0%N.
have Sf_ne : Sf !=set0 by exists (fn 0%N); exists 0%N.
have Sc_ne : Sc !=set0 by exists (tn 0%N * alpha + fn 0%N * beta); exists 0%N.
(* Chains are uniformly bounded by 1. *)
have Htub : forall n, tn n <= 1.
  by move=> n; apply: le_trans (Hsum n); rewrite lerDl.
have Hfub : forall n, fn n <= 1.
  by move=> n; apply: le_trans (Hsum n); rewrite lerDr.
have St_bd : has_ubound St by exists 1 => x [n _ <-]; exact: Htub.
have Sf_bd : has_ubound Sf by exists 1 => x [n _ <-]; exact: Hfub.
(* Sc is bounded by α + β. *)
have Sc_bd : has_ubound Sc.
  exists (alpha + beta) => x [n _ <-]; apply: lerD.
  - by rewrite -[X in _ <= X]mul1r; apply: ler_pM; rewrite ?Htge0 ?Htub.
  - by rewrite -[X in _ <= X]mul1r; apply: ler_pM; rewrite ?Hfge0 ?Hfub.
(* Monotonicity of chains: t_n ≤ t_m and f_n ≤ f_m when n ≤ m. *)
have chain_mono : forall n m, (n <= m)%N -> tn n <= tn m /\ fn n <= fn m.
  move=> n m; elim: m => [|m IH]; first by rewrite leqn0=> /eqP ->.
  rewrite leq_eqVlt => /orP[/eqP ->|]; first by [].
  rewrite ltnS => /IH [Ht Hf]; split.
  - exact: le_trans Ht (Htch m).
  - exact: le_trans Hf (Hfch m).
(* Sups are >= the chain values. *)
have St_sup_ge : forall n, tn n <= sup St.
  by move=> n; apply: ub_le_sup => //; exists n.
have Sf_sup_ge : forall n, fn n <= sup Sf.
  by move=> n; apply: ub_le_sup => //; exists n.
have St_sup_ge0 : 0 <= sup St
  by apply: le_trans (St_sup_ge 0%N); exact: Htge0.
have Sf_sup_ge0 : 0 <= sup Sf
  by apply: le_trans (Sf_sup_ge 0%N); exact: Hfge0.
have has_sup_Sc : has_sup Sc by split.
have has_sup_Sf : has_sup Sf by split.
have has_sup_St : has_sup St by split.
apply: le_anti; apply/andP; split.
- (* sup t * α + sup f * β ≤ sup Sc.
     Strategy: split on [alpha = 0]/[alpha > 0] and [beta = 0]/[beta > 0]
     to apply [ge_sup] without the scalar multiplier obstructing the
     [sup E <= _] shape. *)
  have alpha_eq0_or_pos : alpha = 0 \/ 0 < alpha.
    by have := Halpha; rewrite le_eqVlt => /orP[/eqP <-|->]; [left | right].
  have beta_eq0_or_pos : beta = 0 \/ 0 < beta.
    by have := Hbeta; rewrite le_eqVlt => /orP[/eqP <-|->]; [left | right].
  case: alpha_eq0_or_pos => [Halpha0 | Halphap].
    case: beta_eq0_or_pos => [Hbeta0 | Hbetap].
      (* α = 0, β = 0: both sides 0. *)
      have Sc0 : Sc (tn 0%N * alpha + fn 0%N * beta) by exists 0%N.
      have := (ub_le_sup Sc_bd Sc0).
      by rewrite Halpha0 Hbeta0 !mulr0 addr0.
    (* α = 0, β > 0.  Each fn * beta is in Sc; sup Sf * beta ≤ sup Sc. *)
    rewrite Halpha0 mulr0 add0r.
    rewrite -[X in _ <= X](_ : sup Sc / beta * beta = sup Sc); last first.
      by rewrite -mulrA mulVf ?gt_eqF// mulr1.
    rewrite ler_pM2r//.
    apply: ge_sup => //.
    move=> x [n _ <-].
    rewrite ler_pdivlMr//.
    have Hin : Sc (tn n * alpha + fn n * beta) by exists n.
    have := (ub_le_sup Sc_bd Hin).
    by rewrite Halpha0 mulr0 add0r.
  case: beta_eq0_or_pos => [Hbeta0 | Hbetap].
    (* α > 0, β = 0. *)
    rewrite Hbeta0 mulr0 addr0.
    rewrite -[X in _ <= X](_ : sup Sc / alpha * alpha = sup Sc); last first.
      by rewrite -mulrA mulVf ?gt_eqF// mulr1.
    rewrite ler_pM2r//.
    apply: ge_sup => //.
    move=> x [n _ <-].
    rewrite ler_pdivlMr//.
    have Hin : Sc (tn n * alpha + fn n * beta) by exists n.
    have := (ub_le_sup Sc_bd Hin).
    by rewrite Hbeta0 mulr0 addr0.
  (* α > 0 and β > 0: the generic case. *)
  have key : forall n m,
      tn n * alpha + fn m * beta <= sup Sc.
    move=> n m.
    pose k := maxn n m.
    have nk : (n <= k)%N by exact: leq_maxl.
    have mk : (m <= k)%N by exact: leq_maxr.
    have [Ht _] := chain_mono _ _ nk.
    have [_ Hf] := chain_mono _ _ mk.
    apply: le_trans _ (_ : tn k * alpha + fn k * beta <= _).
      by apply: lerD; apply: ler_wpM2r => //; apply: ltW.
    have Hin : Sc (tn k * alpha + fn k * beta) by exists k.
    exact: (ub_le_sup Sc_bd Hin).
  (* For fixed n: tn n * α + sup f * β ≤ sup Sc.  Divide by β. *)
  have step1 : forall n, tn n * alpha + sup Sf * beta <= sup Sc.
    move=> n.
    rewrite -lerBrDl.
    rewrite -[X in _ <= X](_ : (sup Sc - tn n * alpha) / beta * beta =
                                 sup Sc - tn n * alpha); last first.
      by rewrite -mulrA mulVf ?gt_eqF// mulr1.
    rewrite ler_pM2r//.
    apply: ge_sup => //.
    move=> y [m _ <-].
    rewrite ler_pdivlMr// lerBrDl.
    exact: key.
  (* Take sup over n on LHS. Divide by α. *)
  rewrite -lerBrDr.
  rewrite -[X in _ <= X](_ : (sup Sc - sup Sf * beta) / alpha * alpha =
                               sup Sc - sup Sf * beta); last first.
    by rewrite -mulrA mulVf ?gt_eqF// mulr1.
  rewrite ler_pM2r//.
  apply: ge_sup => //.
  move=> y [n _ <-].
  rewrite ler_pdivlMr// lerBrDr.
  exact: step1.
- (* sup Sc ≤ sup t * α + sup f * β.  Each [t_n * α + f_n * β] ≤ the
     RHS via [t_n ≤ sup t], [f_n ≤ sup f], [α, β ≥ 0]. *)
  apply: ge_sup => //.
  move=> x [n _ <-].
  apply: lerD.
  + by apply: ler_wpM2r => //; exact: St_sup_ge.
  + by apply: ler_wpM2r => //; exact: Sf_sup_ge.
Qed.

End BoolCaseScalar.

(** ** ω-continuity of [bool_case] — substep 2b

    On an iconeType target [A : iconeType R Ar] with both branches
    [a, b] in the unit ball, the map [x ↦ bool_case x a b] is
    ω-continuous on the unit ball of [bool_cone_car Ar].  Proof: lift
    via (Mssep) at arity 0, reducing both sides to a scalar equation
    that is exactly [bool_case_sup_distrib]. *)

Section BoolCaseOmegaCont.
Variables (R : realType) (Ar : MeasSubcat R) (A : ICone.type Ar).
Local Notation T := (bool_cone_car Ar).

(** Image-chain unit-ball bound. *)
Lemma bool_case_chain_ub1 (a b : A)
    (Ha : cone_norm a <= 1) (Hb : cone_norm b <= 1)
    (u : nat -> T) (ub1 : forall n, cone_norm (u n) <= 1) (n : nat) :
  cone_norm (bool_case (u n) a b) <= 1.
Proof. exact: le_trans (bool_case_norm_le1 Ha Hb (u n)) (ub1 n). Qed.

(** Generalized image-chain bound: when [u_n] is in the unit ball, the
    test value [test_fun m s0 (bool_case u_n a b)] is bounded by
    [α + β] where [α = test_fun m s0 a], [β = test_fun m s0 b]
    (no unit-ball assumption on [a, b]). *)
Lemma bool_case_test_chain_ub
    (Ar' : MeasSubcat R) (B : ICone.type Ar') (a b : B)
    (u : nat -> bool_cone_car Ar')
    (ub1 : forall n, cone_norm (u n) <= 1)
    (Y : ar_obj Ar') (m : test_of Ar' Y B)
    (s0 : ar_carrier Ar' Y) (n : nat) :
  test_fun m s0 (bool_case (u n) a b)
  <= test_fun m s0 a + test_fun m s0 b.
Proof.
rewrite /bool_case test_linD !test_linZ.
have Htn : (bc_t (u n))%:num <= 1.
  apply: le_trans (ub1 n).
  by rewrite /cone_norm/= /bc_norm lerDl; exact: nngnum_ge0.
have Hfn : (bc_f (u n))%:num <= 1.
  apply: le_trans (ub1 n).
  by rewrite /cone_norm/= /bc_norm lerDr; exact: nngnum_ge0.
apply: lerD.
- rewrite -[X in _ <= X]mul1r.
  apply: ler_wpM2r => //; exact: test_ge0.
- rewrite -[X in _ <= X]mul1r.
  apply: ler_wpM2r => //; exact: test_ge0.
Qed.

(** Generalized ω-continuity (no unit-ball assumption on [a, b]).
    Only the chain [u : nat -> T] needs to live on the unit ball; the
    branches [a, b : A] are arbitrary. *)
Lemma bool_case_omega_continuous_gen (a b : A) :
  is_omega_continuous (fun x : T => bool_case x a b).
Proof.
move=> u uch ub1 fuch fub1.
apply: mcone_M_sep => m mM.
set lhs := bool_case _ a b.
set rhs := cone_sup_ball _ fuch fub1.
set alpha := test_fun m (ar_zero_pt Ar) a.
set beta  := test_fun m (ar_zero_pt Ar) b.
have testLHS :
    test_fun m (ar_zero_pt Ar) lhs =
    (bc_t (cone_sup_ball u uch ub1))%:num * alpha
    + (bc_f (cone_sup_ball u uch ub1))%:num * beta.
  rewrite /lhs /bool_case test_linD !test_linZ.
  by rewrite /alpha /beta.
have testNth : forall n,
    test_fun m (ar_zero_pt Ar) (bool_case (u n) a b) =
    (bc_t (u n))%:num * alpha + (bc_f (u n))%:num * beta.
  by move=> n; rewrite /bool_case test_linD !test_linZ /alpha /beta.
set Sc := [set test_fun m (ar_zero_pt Ar) (bool_case (u n) a b) | n in [set: nat]].
have Sc_ne : Sc !=set0
  by exists (test_fun m (ar_zero_pt Ar) (bool_case (u 0%N) a b)); exists 0%N.
(* Sc is bounded by [α + β] — no unit-ball assumption on a, b needed. *)
have Sc_bd : has_ubound Sc.
  exists (alpha + beta) => x [n _ <-].
  exact: bool_case_test_chain_ub.
have has_sup_Sc : has_sup Sc by split.
have test_mono : forall x y : A, precone_le x y ->
    test_fun m (ar_zero_pt Ar) x <= test_fun m (ar_zero_pt Ar) y.
  move=> x y [z ->].
  rewrite test_linD lerDl.
  exact: test_ge0.
have test_cont_le :
    test_fun m (ar_zero_pt Ar) rhs <= sup Sc.
  apply: test_cont => n.
  exact: (ub_le_sup Sc_bd (ex_intro2 _ _ n I (erefl _))).
have test_rhs_eq : test_fun m (ar_zero_pt Ar) rhs = sup Sc.
  apply: le_anti; apply/andP; split=> //.
  apply: ge_sup => //.
  move=> x [n _ <-].
  apply: test_mono.
  exact: cone_sup_ball_ub.
have ch_t : forall n, (bc_t (u n))%:num <= (bc_t (u n.+1))%:num.
  by move=> n; have /bc_leE [Ht _] := uch n.
have ch_f : forall n, (bc_f (u n))%:num <= (bc_f (u n.+1))%:num.
  by move=> n; have /bc_leE [_ Hf] := uch n.
have Hsum : forall n, (bc_t (u n))%:num + (bc_f (u n))%:num <= 1.
  by move=> n; have := ub1 n; rewrite /cone_norm/= /bc_norm.
have alpha_ge0 : 0 <= alpha by apply: test_ge0.
have beta_ge0 : 0 <= beta by apply: test_ge0.
have Sc_eq : Sc = [set (bc_t (u n))%:num * alpha
                    + (bc_f (u n))%:num * beta | n in [set: nat]].
  apply: funext => x.
  apply: propext; split=> [[n _ <-]|[n _ <-]].
  - by exists n => //; rewrite testNth.
  - by exists n => //; rewrite testNth.
rewrite testLHS test_rhs_eq Sc_eq.
by apply: bool_case_sup_distrib => //; apply: nngnum_ge0.
Qed.

(** ω-continuity of [x ↦ bool_case x a b] on the unit ball. *)
Lemma bool_case_omega_continuous
    (a b : A) (Ha : cone_norm a <= 1) (Hb : cone_norm b <= 1) :
  is_omega_continuous (fun x : T => bool_case x a b).
Proof.
move=> u uch ub1 fuch fub1.
(* Apply (Mssep) on A. *)
apply: mcone_M_sep => m mM.
set lhs := bool_case _ a b.
set rhs := cone_sup_ball _ fuch fub1.
(* Abbreviations for the scalar values. *)
set alpha := test_fun m (ar_zero_pt Ar) a.
set beta  := test_fun m (ar_zero_pt Ar) b.
(* Test of LHS: linear in bool_case, distributes over add/scale. *)
have testLHS :
    test_fun m (ar_zero_pt Ar) lhs =
    (bc_t (cone_sup_ball u uch ub1))%:num * alpha
    + (bc_f (cone_sup_ball u uch ub1))%:num * beta.
  rewrite /lhs /bool_case test_linD !test_linZ.
  by rewrite /alpha /beta.
(* The chain values:
     test_fun m s0 (bool_case (u n) a b)
   = bc_t(u_n) * alpha + bc_f(u_n) * beta. *)
have testNth : forall n,
    test_fun m (ar_zero_pt Ar) (bool_case (u n) a b) =
    (bc_t (u n))%:num * alpha + (bc_f (u n))%:num * beta.
  by move=> n; rewrite /bool_case test_linD !test_linZ /alpha /beta.
(* The sup-set of test values along the chain. *)
set Sc := [set test_fun m (ar_zero_pt Ar) (bool_case (u n) a b) | n in [set: nat]].
have Sc_ne : Sc !=set0
  by exists (test_fun m (ar_zero_pt Ar) (bool_case (u 0%N) a b)); exists 0%N.
have Sc_bd : has_ubound Sc.
  exists 1 => x [n _ <-]; apply: test_le1.
  exact: bool_case_chain_ub1.
have has_sup_Sc : has_sup Sc by split.
(* test_fun is monotone (linear), so test(u_n) ≤ test(sup u_n). *)
have test_mono : forall x y : A, precone_le x y ->
    test_fun m (ar_zero_pt Ar) x <= test_fun m (ar_zero_pt Ar) y.
  move=> x y [z ->].
  rewrite test_linD lerDl.
  exact: test_ge0.
(* test_cont gives upper bound: test(rhs) ≤ sup Sc. *)
have test_cont_le :
    test_fun m (ar_zero_pt Ar) rhs <= sup Sc.
  apply: test_cont => n.
  exact: (ub_le_sup Sc_bd (ex_intro2 _ _ n I (erefl _))).
(* Combine: test(rhs) = sup Sc. *)
have test_rhs_eq : test_fun m (ar_zero_pt Ar) rhs = sup Sc.
  apply: le_anti; apply/andP; split=> //.
  apply: ge_sup => //.
  move=> x [n _ <-].
  apply: test_mono.
  exact: cone_sup_ball_ub.
(* Now apply the scalar lemma: sup Sc = (sup bc_t) * α + (sup bc_f) * β. *)
have ch_t : forall n, (bc_t (u n))%:num <= (bc_t (u n.+1))%:num.
  by move=> n; have /bc_leE [Ht _] := uch n.
have ch_f : forall n, (bc_f (u n))%:num <= (bc_f (u n.+1))%:num.
  by move=> n; have /bc_leE [_ Hf] := uch n.
have Hsum : forall n, (bc_t (u n))%:num + (bc_f (u n))%:num <= 1.
  by move=> n; have := ub1 n; rewrite /cone_norm/= /bc_norm.
have alpha_ge0 : 0 <= alpha by apply: test_ge0.
have beta_ge0 : 0 <= beta by apply: test_ge0.
(* Sc is the image of [bc_t u_n * alpha + bc_f u_n * beta] over n. *)
have Sc_eq : Sc = [set (bc_t (u n))%:num * alpha
                    + (bc_f (u n))%:num * beta | n in [set: nat]].
  apply: funext => x.
  apply: propext; split=> [[n _ <-]|[n _ <-]].
  - by exists n => //; rewrite testNth.
  - by exists n => //; rewrite testNth.
rewrite testLHS test_rhs_eq Sc_eq.
by apply: bool_case_sup_distrib => //; apply: nngnum_ge0.
Qed.

End BoolCaseOmegaCont.

(** ** Path- and integral-preservation — Step 3

    With ω-continuity in hand we can now upgrade [bool_case . a b] to
    a [linhom_car].  Two extra facts are needed:

    - [linhom_pre_pres_path]: [r ↦ bool_case (γ r) a b] is a measurable
      path in [A] whenever [γ] is a measurable path in [bool_cone_car].
    - [linhom_pres_int]: the integral commutes —
      [bool_case (∫ β dµ) a b = ∫ (bool_case (β r) a b) dµ].

    Both follow from the test-level [test_linD]/[test_linZ]
    decomposition plus standard measurability and integral linearity. *)

Section BoolCasePresPath.
Variables (R : realType) (Ar : MeasSubcat R) (A : ICone.type Ar).
Local Notation T := (bool_cone_car Ar).

(** [bool_case . a b] preserves measurable paths. *)
Lemma bool_case_pres_path
    (a b : A) (Ha : cone_norm a <= 1) (Hb : cone_norm b <= 1)
    (X : ar_obj Ar) (γ : ar_carrier Ar X -> T)
    (Hγ : is_measurable_path γ) :
  is_measurable_path (fun r : ar_carrier Ar X => bool_case (γ r) a b).
Proof.
split.
- (* Boundedness: ‖bool_case (γ r) a b‖ ≤ ‖γ r‖ ≤ M. *)
  case: Hγ => [[M HM] _].
  exists M => r.
  apply: le_trans (HM r).
  exact: bool_case_norm_le1.
- (* Test measurability: (s, r) ↦ test m s (bool_case (γ r) a b) is
     measurable. *)
  move=> Y m mM.
  have HmA : measurable_fun setT (fun s => test_fun m s a).
    exact: test_meas.
  have HmB : measurable_fun setT (fun s => test_fun m s b).
    exact: test_meas.
  (* α(s) := test m s a, β(s) := test m s b.  Both are measurable in s. *)
  have meas_t : measurable_fun setT
      (fun r : ar_carrier Ar X => (bc_t (γ r))%:num).
    have meas_t_E := bool_coord_meas Hγ true.
    by have /measurable_EFinP := meas_t_E.
  have meas_f : measurable_fun setT
      (fun r : ar_carrier Ar X => (bc_f (γ r))%:num).
    have meas_f_E := bool_coord_meas Hγ false.
    by have /measurable_EFinP := meas_f_E.
  (* Now express [test m s (bool_case (γ r) a b)] as a polynomial. *)
  have heq : forall p : ar_carrier Ar Y * ar_carrier Ar X,
      test_fun m p.1 (bool_case (γ p.2) a b)
      = (bc_t (γ p.2))%:num * test_fun m p.1 a
      + (bc_f (γ p.2))%:num * test_fun m p.1 b.
    move=> p; rewrite /bool_case test_linD !test_linZ.
    by [].
  have -> : (fun p : ar_carrier Ar Y * ar_carrier Ar X =>
              test_fun m p.1 (bool_case (γ p.2) a b))
          = (fun p => (bc_t (γ p.2))%:num * test_fun m p.1 a
                    + (bc_f (γ p.2))%:num * test_fun m p.1 b).
    by apply: funext.
  apply: measurable_funD.
  + (* (bc_t (γ p.2)) * test m p.1 a *)
    apply: measurable_funM.
    * apply: (measurableT_comp meas_t measurable_snd).
    * exact: (measurableT_comp HmA measurable_fst).
  + (* (bc_f (γ p.2)) * test m p.1 b *)
    apply: measurable_funM.
    * apply: (measurableT_comp meas_f measurable_snd).
    * exact: (measurableT_comp HmB measurable_fst).
Qed.

(** Generalized measurable-path preservation: drop the unit-ball
    assumption on the branches [a, b].  The boundedness uses
    [bool_case_norm_le_max] with [M := Num.max (cone_norm a) (cone_norm b)];
    the test-measurability uses [test_meas_gen] instead of [test_meas]
    so that [λ s. test_fun m s a] (and similarly for [b]) is measurable
    for ARBITRARY [a, b : A]. *)
Lemma bool_case_pres_path_gen
    (a b : A) (X : ar_obj Ar)
    (γ : ar_carrier Ar X -> T)
    (Hγ : is_measurable_path γ) :
  is_measurable_path (fun r : ar_carrier Ar X => bool_case (γ r) a b).
Proof.
split.
- (* Boundedness: ‖bool_case (γ r) a b‖ ≤ ‖γ r‖ · M with
     [M := max (‖a‖, ‖b‖) ∨ 0]. *)
  case: Hγ => [[N HN] _].
  pose M : R := Num.max (Num.max (cone_norm a) (cone_norm b)) 0%R.
  have HM0 : 0 <= M by rewrite le_max lexx orbT.
  have HMa : cone_norm a <= M.
    by apply: le_trans (_ : Num.max (cone_norm a) (cone_norm b) <= _);
       [rewrite le_max lexx|rewrite le_max lexx].
  have HMb : cone_norm b <= M.
    by apply: le_trans (_ : Num.max (cone_norm a) (cone_norm b) <= _);
       [rewrite le_max lexx orbT|rewrite le_max lexx].
  exists (N * M) => r.
  have step1 : cone_norm (bool_case (γ r) a b) <= cone_norm (γ r) * M
    by exact: (bool_case_norm_le_max HMa HMb HM0).
  apply: le_trans step1 _.
  by apply: ler_wpM2r => //; exact: HN.
- (* Test measurability: same polynomial decomposition as the
     unit-ball case, but use [test_meas_gen] to get measurability
     of [λ s. test_fun m s a], [λ s. test_fun m s b] for arbitrary
     [a, b]. *)
  move=> Y m mM.
  have HmA : measurable_fun setT (fun s => test_fun m s a)
    by exact: test_meas_gen.
  have HmB : measurable_fun setT (fun s => test_fun m s b)
    by exact: test_meas_gen.
  have meas_t : measurable_fun setT
      (fun r : ar_carrier Ar X => (bc_t (γ r))%:num).
    have meas_t_E := bool_coord_meas Hγ true.
    by have /measurable_EFinP := meas_t_E.
  have meas_f : measurable_fun setT
      (fun r : ar_carrier Ar X => (bc_f (γ r))%:num).
    have meas_f_E := bool_coord_meas Hγ false.
    by have /measurable_EFinP := meas_f_E.
  have heq : forall p : ar_carrier Ar Y * ar_carrier Ar X,
      test_fun m p.1 (bool_case (γ p.2) a b)
      = (bc_t (γ p.2))%:num * test_fun m p.1 a
      + (bc_f (γ p.2))%:num * test_fun m p.1 b.
    by move=> p; rewrite /bool_case test_linD !test_linZ.
  have -> : (fun p : ar_carrier Ar Y * ar_carrier Ar X =>
              test_fun m p.1 (bool_case (γ p.2) a b))
          = (fun p => (bc_t (γ p.2))%:num * test_fun m p.1 a
                    + (bc_f (γ p.2))%:num * test_fun m p.1 b).
    by apply: funext.
  apply: measurable_funD.
  + apply: measurable_funM.
    * apply: (measurableT_comp meas_t measurable_snd).
    * exact: (measurableT_comp HmA measurable_fst).
  + apply: measurable_funM.
    * apply: (measurableT_comp meas_f measurable_snd).
    * exact: (measurableT_comp HmB measurable_fst).
Qed.

End BoolCasePresPath.

Arguments bool_case_pres_path {R Ar A} a b Ha Hb {X} γ Hγ.
Arguments bool_case_pres_path_gen {R Ar A} a b {X} γ Hγ.

(** ** Integral preservation for [bool_case . a b]

    Substep 3b: the Pettis integral commutes with [bool_case]:
    [bool_case (∫ β dµ) a b = ∫ (bool_case (β r) a b) dµ].
    By [icone_integral_eqP], it suffices to show the LHS satisfies
    [path_integral_eq] for the image path [r ↦ bool_case (β r) a b].
    That reduces, on each test [m] at arity 0, to the scalar
    identity
       [bc_t(I) * α + bc_f(I) * β = ∫ (bc_t(β r) * α + bc_f(β r) * β) dµ]
    where [I = icone_integral β Hβ µ] and [α, β] are the test values
    at [a, b].  Using [test_linD]/[test_linZ] on the LHS, the
    coordinate-Pettis identities of [bool_int_pettis] (applied to the
    [Some true]/[Some false] tag tests) close out. *)

Section BoolCasePresInt.
Variables (R : realType) (Ar : MeasSubcat R) (A : ICone.type Ar).
Local Notation T := (bool_cone_car Ar).

Lemma bool_case_pres_int
    (a b : A) (Ha : (cone_norm a <= 1)%R) (Hb : (cone_norm b <= 1)%R)
    (X : ar_obj Ar) (β : ar_carrier Ar X -> T)
    (Hβ : is_measurable_path β)
    (µ : fmeas R (ar_carrier Ar X)) :
  bool_case (icone_integral β Hβ µ) a b =
  icone_integral (fun r => bool_case (β r) a b)
                 (bool_case_pres_path a b Ha Hb β Hβ) µ.
Proof.
(* Apply uniqueness of integral on the image path. *)
apply: icone_integral_eqP.
move=> m mM s.
(* Decompose test on LHS via linearity. *)
set I := icone_integral β Hβ µ.
rewrite /bool_case test_linD !test_linZ.
(* Right-hand integrand: test(bool_case (β r) a b) = bc_t(β r)*α + bc_f(β r)*β. *)
have integrand_eq :
    forall r, (test_fun m s (bool_case (β r) a b))%:E =
              ((bc_t (β r))%:num * test_fun m s a)%:E
              + ((bc_f (β r))%:num * test_fun m s b)%:E.
  by move=> r; rewrite /bool_case test_linD !test_linZ EFinD.
have meas_t_E := bool_coord_meas Hβ true.
have meas_f_E := bool_coord_meas Hβ false.
have meas_t : measurable_fun setT
    (fun r : ar_carrier Ar X => (bc_t (β r))%:num)
  by have /measurable_EFinP := meas_t_E.
have meas_f : measurable_fun setT
    (fun r : ar_carrier Ar X => (bc_f (β r))%:num)
  by have /measurable_EFinP := meas_f_E.
(* Both sides are finite: cone_norm bounded implies test bounded. *)
have HmA : measurable_fun setT (fun s' => test_fun m s' a)
  by exact: test_meas.
have HmB : measurable_fun setT (fun s' => test_fun m s' b)
  by exact: test_meas.
(* The fine of the sum-integral = sum of the fines. *)
have ge0_t : forall r, (0 <= ((bc_t (β r))%:num)%:E)%E
  by move=> r; rewrite lee_fin nngnum_ge0.
have ge0_f : forall r, (0 <= ((bc_f (β r))%:num)%:E)%E
  by move=> r; rewrite lee_fin nngnum_ge0.
have alpha_ge0 : 0 <= test_fun m s a by exact: test_ge0.
have beta_ge0 : 0 <= test_fun m s b by exact: test_ge0.
(* Step 1: relate icone_integral β to bool_int (both satisfy path_integral_eq). *)
have I_eq : I = bool_int Hβ µ.
  rewrite /I.
  apply/esym/icone_integral_eqP.
  exact: bool_int_pettis.
rewrite I_eq /bool_int /=.
(* Step 2: the two halves of the integral computation. *)
(* By definition of bool_int, bc_t I = fine ∫ bc_t(β r). *)
have eq_t : (NngNum (bool_int_ge0 β µ true))%:num =
            fine (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X])
                    ((bc_t (β r))%:num)%:E).
  rewrite /=.
  apply: congr1.
  by apply: eq_integral.
have eq_f : (NngNum (bool_int_ge0 β µ false))%:num =
            fine (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X])
                    ((bc_f (β r))%:num)%:E).
  rewrite /=.
  apply: congr1.
  by apply: eq_integral.
rewrite eq_t eq_f.
(* Step 3: the RHS integral = sum of the two fine integrals * α, β. *)
have RHS_eq :
    (\int[fmeas_mu µ]_r ((test_fun m s (bool_case (β r) a b))%:E)
    = (test_fun m s a)%:E
      * (\int[fmeas_mu µ]_r ((bc_t (β r))%:num)%:E)
    + (test_fun m s b)%:E
      * (\int[fmeas_mu µ]_r ((bc_f (β r))%:num)%:E))%E.
  rewrite (eq_integral
      (fun r => (((bc_t (β r))%:num * test_fun m s a)%:E
             + ((bc_f (β r))%:num * test_fun m s b)%:E)%E));
    last by move=> r _; rewrite /=; exact: integrand_eq.
  have ge0_t_a : forall r : ar_carrier Ar X, True ->
      (0%R <= ((bc_t (β r))%:num * test_fun m s a)%:E)%E.
    by move=> r _; rewrite lee_fin mulr_ge0 ?nngnum_ge0.
  have ge0_f_b : forall r : ar_carrier Ar X, True ->
      (0%R <= ((bc_f (β r))%:num * test_fun m s b)%:E)%E.
    by move=> r _; rewrite lee_fin mulr_ge0 ?nngnum_ge0.
  have meas_t_a : measurable_fun [set: ar_carrier Ar X]
      (fun r : ar_carrier Ar X => ((bc_t (β r))%:num * test_fun m s a)%:E).
    apply/measurable_EFinP.
    by apply: measurable_funM => //; exact: measurable_cst.
  have meas_f_b : measurable_fun [set: ar_carrier Ar X]
      (fun r : ar_carrier Ar X => ((bc_f (β r))%:num * test_fun m s b)%:E).
    apply/measurable_EFinP.
    by apply: measurable_funM => //; exact: measurable_cst.
  rewrite (ge0_integralD _ measurableT ge0_t_a meas_t_a ge0_f_b meas_f_b).
  congr (_ + _)%E.
  - rewrite (eq_integral
        (fun r => ((test_fun m s a)%:E * ((bc_t (β r))%:num)%:E)%E));
      last by move=> r _; rewrite /= -EFinM mulrC.
    by rewrite ge0_integralZl//; apply/measurable_EFinP.
  - rewrite (eq_integral
        (fun r => ((test_fun m s b)%:E * ((bc_f (β r))%:num)%:E)%E));
      last by move=> r _; rewrite /= -EFinM mulrC.
    by rewrite ge0_integralZl//; apply/measurable_EFinP.
rewrite RHS_eq.
(* Step 4: pull fine through addition + multiplication. *)
have fin_t : (\int[fmeas_mu µ]_r ((bc_t (β r))%:num)%:E)%E \is a fin_num.
  have := bool_int_fin Hβ µ true.
  by rewrite (eq_integral (fun r => ((bc_t (β r))%:num)%:E))//;
    move=> r _; rewrite /=.
have fin_f : (\int[fmeas_mu µ]_r ((bc_f (β r))%:num)%:E)%E \is a fin_num.
  have := bool_int_fin Hβ µ false.
  by rewrite (eq_integral (fun r => ((bc_f (β r))%:num)%:E))//;
    move=> r _; rewrite /=.
have fin_mult_t : ((test_fun m s a)%:E
    * \int[fmeas_mu µ]_r ((bc_t (β r))%:num)%:E)%E \is a fin_num.
  by apply: fin_numM.
have fin_mult_f : ((test_fun m s b)%:E
    * \int[fmeas_mu µ]_r ((bc_f (β r))%:num)%:E)%E \is a fin_num.
  by apply: fin_numM.
have alpha_fin : (test_fun m s a)%:E \is a fin_num by [].
have beta_fin : (test_fun m s b)%:E \is a fin_num by [].
rewrite (fineD fin_mult_t fin_mult_f).
rewrite (fineM alpha_fin fin_t).
rewrite (fineM beta_fin fin_f).
by rewrite [(test_fun _ _ a * _)%R]mulrC [(test_fun _ _ b * _)%R]mulrC.
Qed.

(** Generalized Pettis-integral preservation: drop the unit-ball
    assumption on the branches [a, b].  Proof structure mirrors the
    unit-ball [bool_case_pres_int] with two upgrades:
    - the RHS uses [bool_case_pres_path_gen] for the image path;
    - measurability of [λ s'. test_fun m s' a] (and similarly for [b])
      uses [test_meas_gen] instead of [test_meas].
    All other steps — relating [icone_integral β] to [bool_int] via
    uniqueness, the [ge0_integralD] + [ge0_integralZl] decomposition,
    and the [fineD] + [fineM] finalization — are unchanged. *)
Lemma bool_case_pres_int_gen
    (a b : A)
    (X : ar_obj Ar) (β : ar_carrier Ar X -> T)
    (Hβ : is_measurable_path β)
    (µ : fmeas R (ar_carrier Ar X)) :
  bool_case (icone_integral β Hβ µ) a b =
  icone_integral (fun r => bool_case (β r) a b)
                 (bool_case_pres_path_gen a b β Hβ) µ.
Proof.
apply: icone_integral_eqP.
move=> m mM s.
set I := icone_integral β Hβ µ.
rewrite /bool_case test_linD !test_linZ.
have integrand_eq :
    forall r, (test_fun m s (bool_case (β r) a b))%:E =
              ((bc_t (β r))%:num * test_fun m s a)%:E
              + ((bc_f (β r))%:num * test_fun m s b)%:E.
  by move=> r; rewrite /bool_case test_linD !test_linZ EFinD.
have meas_t_E := bool_coord_meas Hβ true.
have meas_f_E := bool_coord_meas Hβ false.
have meas_t : measurable_fun setT
    (fun r : ar_carrier Ar X => (bc_t (β r))%:num)
  by have /measurable_EFinP := meas_t_E.
have meas_f : measurable_fun setT
    (fun r : ar_carrier Ar X => (bc_f (β r))%:num)
  by have /measurable_EFinP := meas_f_E.
have HmA : measurable_fun setT (fun s' => test_fun m s' a)
  by exact: test_meas_gen.
have HmB : measurable_fun setT (fun s' => test_fun m s' b)
  by exact: test_meas_gen.
have ge0_t : forall r, (0 <= ((bc_t (β r))%:num)%:E)%E
  by move=> r; rewrite lee_fin nngnum_ge0.
have ge0_f : forall r, (0 <= ((bc_f (β r))%:num)%:E)%E
  by move=> r; rewrite lee_fin nngnum_ge0.
have alpha_ge0 : 0 <= test_fun m s a by exact: test_ge0.
have beta_ge0 : 0 <= test_fun m s b by exact: test_ge0.
have I_eq : I = bool_int Hβ µ.
  rewrite /I.
  apply/esym/icone_integral_eqP.
  exact: bool_int_pettis.
rewrite I_eq /bool_int /=.
have eq_t : (NngNum (bool_int_ge0 β µ true))%:num =
            fine (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X])
                    ((bc_t (β r))%:num)%:E).
  rewrite /=.
  apply: congr1.
  by apply: eq_integral.
have eq_f : (NngNum (bool_int_ge0 β µ false))%:num =
            fine (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X])
                    ((bc_f (β r))%:num)%:E).
  rewrite /=.
  apply: congr1.
  by apply: eq_integral.
rewrite eq_t eq_f.
have RHS_eq :
    (\int[fmeas_mu µ]_r ((test_fun m s (bool_case (β r) a b))%:E)
    = (test_fun m s a)%:E
      * (\int[fmeas_mu µ]_r ((bc_t (β r))%:num)%:E)
    + (test_fun m s b)%:E
      * (\int[fmeas_mu µ]_r ((bc_f (β r))%:num)%:E))%E.
  rewrite (eq_integral
      (fun r => (((bc_t (β r))%:num * test_fun m s a)%:E
             + ((bc_f (β r))%:num * test_fun m s b)%:E)%E));
    last by move=> r _; rewrite /=; exact: integrand_eq.
  have ge0_t_a : forall r : ar_carrier Ar X, True ->
      (0%R <= ((bc_t (β r))%:num * test_fun m s a)%:E)%E.
    by move=> r _; rewrite lee_fin mulr_ge0 ?nngnum_ge0.
  have ge0_f_b : forall r : ar_carrier Ar X, True ->
      (0%R <= ((bc_f (β r))%:num * test_fun m s b)%:E)%E.
    by move=> r _; rewrite lee_fin mulr_ge0 ?nngnum_ge0.
  have meas_t_a : measurable_fun [set: ar_carrier Ar X]
      (fun r : ar_carrier Ar X => ((bc_t (β r))%:num * test_fun m s a)%:E).
    apply/measurable_EFinP.
    by apply: measurable_funM => //; exact: measurable_cst.
  have meas_f_b : measurable_fun [set: ar_carrier Ar X]
      (fun r : ar_carrier Ar X => ((bc_f (β r))%:num * test_fun m s b)%:E).
    apply/measurable_EFinP.
    by apply: measurable_funM => //; exact: measurable_cst.
  rewrite (ge0_integralD _ measurableT ge0_t_a meas_t_a ge0_f_b meas_f_b).
  congr (_ + _)%E.
  - rewrite (eq_integral
        (fun r => ((test_fun m s a)%:E * ((bc_t (β r))%:num)%:E)%E));
      last by move=> r _; rewrite /= -EFinM mulrC.
    by rewrite ge0_integralZl//; apply/measurable_EFinP.
  - rewrite (eq_integral
        (fun r => ((test_fun m s b)%:E * ((bc_f (β r))%:num)%:E)%E));
      last by move=> r _; rewrite /= -EFinM mulrC.
    by rewrite ge0_integralZl//; apply/measurable_EFinP.
rewrite RHS_eq.
have fin_t : (\int[fmeas_mu µ]_r ((bc_t (β r))%:num)%:E)%E \is a fin_num.
  have := bool_int_fin Hβ µ true.
  by rewrite (eq_integral (fun r => ((bc_t (β r))%:num)%:E))//;
    move=> r _; rewrite /=.
have fin_f : (\int[fmeas_mu µ]_r ((bc_f (β r))%:num)%:E)%E \is a fin_num.
  have := bool_int_fin Hβ µ false.
  by rewrite (eq_integral (fun r => ((bc_f (β r))%:num)%:E))//;
    move=> r _; rewrite /=.
have fin_mult_t : ((test_fun m s a)%:E
    * \int[fmeas_mu µ]_r ((bc_t (β r))%:num)%:E)%E \is a fin_num.
  by apply: fin_numM.
have fin_mult_f : ((test_fun m s b)%:E
    * \int[fmeas_mu µ]_r ((bc_f (β r))%:num)%:E)%E \is a fin_num.
  by apply: fin_numM.
have alpha_fin : (test_fun m s a)%:E \is a fin_num by [].
have beta_fin : (test_fun m s b)%:E \is a fin_num by [].
rewrite (fineD fin_mult_t fin_mult_f).
rewrite (fineM alpha_fin fin_t).
rewrite (fineM beta_fin fin_f).
by rewrite [(test_fun _ _ a * _)%R]mulrC [(test_fun _ _ b * _)%R]mulrC.
Qed.

End BoolCasePresInt.

Arguments bool_case_pres_int_gen {R Ar A} a b {X} β Hβ µ.
