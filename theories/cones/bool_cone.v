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

Require Import Icones.prelude.classical_extra.
Require Import Icones.prelude.nonneg_extra.
Require Import Icones.prelude.omegacpo.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
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
