(** * Integrable-cone instances for the running examples — Paper §4

    Three [isICone] HB instances fully delivered:

    - [cone_one_car Ar] (paper's ⊥, the 1-dimensional [R≥0] cone wrapped
      in an [Ar]-indexed record) is integrable. The integral of
      [β : X → R≥0] over [µ ∈ FMeas(X)] is [(fine ∫ β(r) µ(dr))%:nng].
      Paper §2.3 / §4. **HB.instance isICone registered.**

    - [fmeas R (ar_carrier Ar X)] for [X ∈ Ar] (paper's FMeas(X)) is
      integrable. The integral of a bounded kernel
      [κ : Y → FMeas(X)] over [ν ∈ FMeas(Y)] is the measure
      [V ↦ ∫_(s ∈ Y) (κ s) V dν(s)]. Paper Theorem 4.5.
      **HB.instance isICone registered.**

    - [path_car Ar X B] for [B : iconeType Ar] (paper's Path(X, B))
      is integrable when [B] is. The integral candidate
      [path_int_fun] is defined, the Pettis equation at arity 0 is
      proved ([path_int_fun_pettis_ar0]), and measurability of
      [path_int_fun] as a path is discharged via paper Lemma 4.6
      ([kernel_integral_measurable] in [icone_integral.v]).
      **HB.instance isICone registered for [path_car]** (see
      [path_int_exists] and the HB.instance below) — cast
      measurability is now part of the [MeasSubcat] record, so the
      registration is unconditional.

    Paper reference: Theorems 4.5 and 4.12 (pages 1:24, 1:28).

    Design notes.

    - [cone_one_car Ar] is a thin [Record] wrapper around
      [{nonneg R}] indexed by [Ar]. It is used in place of the bare
      [{nonneg R}] (which has its [Cone] structure installed without
      an [Ar] parameter in [examples_cone.v]) because the [isMCone]
      mixin is [Ar]-parameterised. The wrapper mirrors the
      [alpha_rescale_car] pattern from [mcone_cat.v].

    - Tests on [cone_one_car Ar] at arity [Y] are the singleton
      family [{ id_test }] where [id_test r x = (c1_val x)%:num] is
      constant in [r]. (Mscomp) closure is trivial; (Mssep) and
      (Msnorm) at arity 0 are direct from the [%:num] projection.

    - Deliverable 2 builds the kernel-integrated measure ν of the
      Pettis witness as a [fmeas R X] record via [isMeasure.Build],
      discharging σ-additivity via [cvg_monotone_convergence]
      applied to partial sums.
*)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals constructive_ereal.
From mathcomp.analysis Require Import ereal.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import measure.
From mathcomp.analysis Require Import lebesgue_integral_definition.
From mathcomp.analysis Require Import lebesgue_integral_monotone_convergence.
From mathcomp.analysis Require Import lebesgue_integral_nonneg.
From mathcomp.analysis Require Import measurable_fun_approximation.

Require Import Icones.prelude.classical_extra.
Require Import Icones.prelude.nonneg_extra.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.examples_cone.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.mcones.path.
Require Import Icones.icones.pettis.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_integral.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** Deliverable 1 — Paper §2.3 / §4: ⊥ is integrable *)

(** The [isMCone] mixin is parameterised by [Ar]; the underlying
    [Cone] instance on [{nonneg R}] (registered in [examples_cone.v])
    is not. We therefore wrap [{nonneg R}] in a thin [Record]
    indexed by [Ar] and re-register [isPrecone], [isCone], [isMCone],
    [isICone] HB instances on the wrapper, mirroring the
    [alpha_rescale_car] pattern from [mcone_cat.v]. The wrapper
    carrier is [cone_one_car Ar = { c1_val : {nonneg R} }]. *)

Section ConeOneCar.
Variables (R : realType) (Ar : MeasSubcat R).

(** Paper §2.3: thin wrapper around [{nonneg R}] indexed by [Ar].
    The dummy parameter [_ : MeasSubcat R] forces [Ar] to survive
    section discharge — the subsequent [isMCone] HB instance must
    depend on [Ar]. *)
Record cone_one_car (dummy : MeasSubcat R) : Type :=
  MkConeOne { c1_val : {nonneg R} }.

(** Extensionality for the wrapper. *)
Lemma cone_one_eq (x y : cone_one_car Ar) :
  c1_val x = c1_val y -> x = y.
Proof. by case: x; case: y => /= ? ? ->. Qed.

End ConeOneCar.

Arguments cone_one_car {R}.
Arguments MkConeOne {R}.
Arguments c1_val {R dummy}.


(** *** Precone instance on [cone_one_car Ar] *)

Section ConeOnePrecone.
Variables (R : realType) (Ar : MeasSubcat R).
Local Notation T := (cone_one_car Ar).

Definition c1_zero : T := MkConeOne Ar 0%:nng.
Definition c1_add (x y : T) : T :=
  MkConeOne Ar (nng_add (c1_val x) (c1_val y)).
Definition c1_scale (r : {nonneg R}) (x : T) : T :=
  MkConeOne Ar (nng_mul r (c1_val x)).

Lemma c1_addA : associative c1_add.
Proof.
move=> x y z; apply: cone_one_eq; apply: nngnum_inj.
by rewrite !nng_addE addrA.
Qed.

Lemma c1_addC : commutative c1_add.
Proof.
move=> x y; apply: cone_one_eq; apply: nngnum_inj.
by rewrite !nng_addE addrC.
Qed.

Lemma c1_add0 : left_id c1_zero c1_add.
Proof.
move=> x; apply: cone_one_eq; apply: nngnum_inj.
by rewrite nng_addE add0r.
Qed.

Lemma c1_scale_DAr (r : {nonneg R}) (x y : T) :
  c1_scale r (c1_add x y) = c1_add (c1_scale r x) (c1_scale r y).
Proof.
apply: cone_one_eq; apply: nngnum_inj.
by rewrite !nng_mulE !nng_addE !nng_mulE mulrDr.
Qed.

Lemma c1_scale_DAl (r s : {nonneg R}) (x : T) :
  c1_scale ((r%:num + s%:num))%:nng x =
  c1_add (c1_scale r x) (c1_scale s x).
Proof.
apply: cone_one_eq; apply: nngnum_inj.
by rewrite !nng_addE !nng_mulE mulrDl.
Qed.

Lemma c1_scale_A (r s : {nonneg R}) (x : T) :
  c1_scale ((r%:num * s%:num))%:nng x =
  c1_scale r (c1_scale s x).
Proof.
apply: cone_one_eq; apply: nngnum_inj.
by rewrite !nng_mulE mulrA.
Qed.

Lemma c1_scale_1 (x : T) : c1_scale 1%:nng x = x.
Proof.
apply: cone_one_eq; apply: nngnum_inj.
by rewrite /c1_scale/= mul1r.
Qed.

Lemma c1_scale_0r (r : {nonneg R}) : c1_scale r c1_zero = c1_zero.
Proof.
apply: cone_one_eq; apply: nngnum_inj.
by rewrite nng_mulE mulr0.
Qed.

Lemma c1_scale_0l (x : T) : c1_scale 0%:nng x = c1_zero.
Proof.
apply: cone_one_eq; apply: nngnum_inj.
by rewrite nng_mulE mul0r.
Qed.

Lemma c1_cancel (x y z : T) :
  c1_add x y = c1_add x z -> y = z.
Proof.
move=> H; apply: cone_one_eq.
have /(congr1 c1_val) /= := H.
move=> /(congr1 (@Itv.r _ _ _)); rewrite !nng_addE => HE.
by apply: nngnum_inj; apply: (addrI (c1_val x)%:num).
Qed.

Lemma c1_pos (x y : T) :
  c1_add x y = c1_zero -> x = c1_zero /\ y = c1_zero.
Proof.
move=> H.
have /(congr1 c1_val) /= := H => Hxy.
have Hxy' : nng_add (c1_val x) (c1_val y) = 0%:nng by exact: Hxy.
case: (nonneg_addr0 Hxy') => Hx0 Hy0.
by split; apply: cone_one_eq; rewrite ?Hx0 ?Hy0.
Qed.

End ConeOnePrecone.

HB.instance Definition _ (R : realType) (Ar : MeasSubcat R) :=
  @isPrecone.Build R (cone_one_car Ar)
    (@c1_zero R Ar) (@c1_add R Ar) (@c1_scale R Ar)
    (@c1_addA R Ar) (@c1_addC R Ar) (@c1_add0 R Ar)
    (@c1_scale_DAr R Ar) (@c1_scale_DAl R Ar) (@c1_scale_A R Ar)
    (@c1_scale_1 R Ar) (@c1_scale_0r R Ar) (@c1_scale_0l R Ar)
    (@c1_cancel R Ar) (@c1_pos R Ar).

(** *** Cone instance on [cone_one_car Ar] *)

Section ConeOneCone.
Variables (R : realType) (Ar : MeasSubcat R).
Local Notation T := (cone_one_car Ar).

Definition c1_norm (x : T) : R := (c1_val x)%:num.

Lemma c1_normh (r : {nonneg R}) (x : T) :
  c1_norm (precone_scale r x) = r%:num * c1_norm x.
Proof. by rewrite /precone_scale/= /c1_norm /= nng_mulE. Qed.

Lemma c1_normz (x : T) : c1_norm x = 0 -> x = precone_zero.
Proof.
move=> x0; rewrite /precone_zero/=; apply: cone_one_eq.
exact: nonneg_eq0.
Qed.

Lemma c1_normt (x y : T) :
  c1_norm (precone_add x y) <= c1_norm x + c1_norm y.
Proof. by rewrite /precone_add/= /c1_norm /= nng_addE lexx. Qed.

(** Order on the wrapper is order on the underlying [{nonneg R}]. *)
Lemma c1_leE (x y : T) : precone_le x y <-> (c1_val x)%:num <= (c1_val y)%:num.
Proof.
split=> [[z Hxy]|le_xy].
  by rewrite Hxy/= nng_addE lerDl nngnum_ge0.
have d_ge0 : 0 <= (c1_val y)%:num - (c1_val x)%:num by rewrite subr_ge0.
exists (MkConeOne Ar (NngNum d_ge0)).
apply: cone_one_eq; apply: nngnum_inj.
by rewrite /= addrC subrK.
Qed.

Lemma c1_normp (x y : T) : precone_le x y -> c1_norm x <= c1_norm y.
Proof. by move/c1_leE. Qed.

(** *** Sup-ball construction *)
Lemma c1_sup_S_ge0
    (u : nat -> T) (ub1 : forall n, c1_norm (u n) <= 1) :
  0 <= sup [set (c1_val (u n))%:num | n in [set: nat]].
Proof.
set S : set R := [set _ | _ in _].
have S_nonempty : S !=set0 by exists (c1_val (u 0))%:num; exists 0%N.
have S_has_ubound : has_ubound S by exists 1 => x [n _ <-]; exact: ub1.
have ub_sup : ubound S (sup S) by exact: ub_le_sup.
apply: le_trans (nngnum_ge0 (c1_val (u 0%N))) _.
by apply: ub_sup; exists 0%N.
Qed.

Definition c1_sup_ball
    (u : nat -> T)
    (_ : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, c1_norm (u n) <= 1) : T :=
  MkConeOne Ar (NngNum (c1_sup_S_ge0 ub1)).

Lemma c1_sup_ball_E
    (u : nat -> T)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, c1_norm (u n) <= 1) :
  (c1_val (c1_sup_ball uch ub1))%:num =
  sup [set (c1_val (u n))%:num | n in [set: nat]].
Proof. by []. Qed.

Lemma c1_sup_ball_ub
    (u : nat -> T)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, c1_norm (u n) <= 1) n :
  precone_le (u n) (c1_sup_ball uch ub1).
Proof.
apply/c1_leE.
rewrite c1_sup_ball_E.
set S : set R := [set _ | _ in _].
have S_has_ubound : has_ubound S by exists 1 => x [m _ <-]; exact: ub1.
have ub_sup : ubound S (sup S) by exact: ub_le_sup.
by apply: ub_sup; exists n.
Qed.

Lemma c1_sup_ball_lub
    (u : nat -> T)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, c1_norm (u n) <= 1) (y : T) :
  (forall n, precone_le (u n) y) ->
  precone_le (c1_sup_ball uch ub1) y.
Proof.
move=> H; apply/c1_leE.
rewrite c1_sup_ball_E.
set S : set R := [set _ | _ in _].
have S_nonempty : S !=set0 by exists (c1_val (u 0))%:num; exists 0%N.
apply: ge_sup; first exact: S_nonempty.
by move=> x [n _ <-]; have /c1_leE := H n.
Qed.

Lemma c1_sup_ball_norm
    (u : nat -> T)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, c1_norm (u n) <= 1) :
  c1_norm (c1_sup_ball uch ub1) <= 1.
Proof.
rewrite /c1_norm c1_sup_ball_E.
apply: ge_sup; first by exists (c1_val (u 0))%:num; exists 0%N.
by move=> x [n _ <-]; exact: ub1.
Qed.

End ConeOneCone.

HB.instance Definition _ (R : realType) (Ar : MeasSubcat R) :=
  @isCone.Build R (cone_one_car Ar)
    (@c1_norm R Ar)
    (@c1_normh R Ar) (@c1_normz R Ar) (@c1_normt R Ar) (@c1_normp R Ar)
    (@c1_sup_ball R Ar)
    (@c1_sup_ball_ub R Ar) (@c1_sup_ball_lub R Ar) (@c1_sup_ball_norm R Ar).

(** *** Measurable-cone instance on [cone_one_car Ar]

    Tests on [R≥0] at arity [Y] are the trivial test [m_id r x = x%:num]
    plus closure under the (Mscomp) operation [test_reindex]. We pick
    the singleton test family [{ m_id }], constant in [r]; reindexing
    sends [m_id] to itself. Separation and (Msnorm) at arity 0 are
    direct from the [%:num] projection. *)

Module ConeOneMConeAux.
Section ConeOneMConeAux.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation T := (cone_one_car Ar).

(** Paper §2.3: the functional underlying the identity test on
    [R≥0] — the [%:num] projection. It is non-negative, linear,
    ω-continuous and norm-preserving, hence gives a test at *every*
    arity through the [test_const] combinator (the test does not
    depend on the arity point [r]). *)

Definition c1_num (x : T) : R := (c1_val x)%:num.

Lemma c1_num_ge0 (x : T) : 0 <= c1_num x.
Proof. exact: nngnum_ge0. Qed.

Lemma c1_num_lin0 : c1_num precone_zero = 0.
Proof. by []. Qed.

Lemma c1_num_linD (x y : T) :
  c1_num (precone_add x y) = c1_num x + c1_num y.
Proof. by rewrite /c1_num /precone_add/= nng_addE. Qed.

Lemma c1_num_linZ (s : {nonneg R}) (x : T) :
  c1_num (precone_scale s x) = s%:num * c1_num x.
Proof. by rewrite /c1_num /precone_scale/= nng_mulE. Qed.

Lemma c1_num_cont
    (u : nat -> T)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, cone_norm (u n) <= 1)
    (N : R) :
  (forall n, c1_num (u n) <= N) -> c1_num (cone_sup_ball u uch ub1) <= N.
Proof.
move=> HN; rewrite /c1_num /cone_sup_ball/=.
apply: ge_sup.
- by exists (c1_val (u 0))%:num; exists 0%N.
- by move=> y [n _ <-]; exact: HN.
Qed.

Lemma c1_num_norm_le (x : T) : c1_num x <= cone_norm x.
Proof. by rewrite /c1_num /cone_norm/= /c1_norm. Qed.

(** Paper §2.3: the identity test on [R≥0] at any arity. Returns
    [x%:num], constant in [r]. *)
Section IdTest.
Variable Y : ar_obj Ar.

Definition id_test_fun : ar_carrier Ar Y -> T -> R :=
  fun _ x => (c1_val x)%:num.

(** Paper §2.3: the packaged identity test, via [test_const]. *)
Definition id_test : test_of Ar Y T :=
  test_const c1_num c1_num_ge0 c1_num_lin0 c1_num_linD c1_num_linZ
             c1_num_cont c1_num_norm_le id_test_fun (fun _ _ => erefl).

End IdTest.

(** Paper §2.3: the singleton family [{ id_test }] at every arity. *)
Definition mcone_M_one (Y : ar_obj Ar) : set (test_of Ar Y T) :=
  [set id_test Y].

Lemma mcone_M_one_comp (Y X : ar_obj Ar) (φ : ar_hom Ar Y X)
    (m : test_of Ar X T) :
  mcone_M_one m -> mcone_M_one (test_reindex φ m).
Proof.
move=> ->.
apply: test_eq => s x.
by rewrite /test_reindex/= /test_reindex_fun /id_test/= /id_test_fun.
Qed.

Lemma mcone_M_one_sep (x1 x2 : T) :
  (forall m : test_of Ar (ar_zero Ar) T,
    mcone_M_one m ->
    test_fun m (ar_zero_pt Ar) x1 = test_fun m (ar_zero_pt Ar) x2) ->
  x1 = x2.
Proof.
move=> Hsep.
have := Hsep _ (erefl _).
rewrite /id_test/= /id_test_fun => Hnum.
apply: cone_one_eq; exact: nngnum_inj.
Qed.

Lemma mcone_M_one_norm (x : T) (eps : R) :
  x <> precone_zero -> 0 < eps ->
  exists m : test_of Ar (ar_zero Ar) T,
    mcone_M_one m /\
    cone_norm x <= test_fun m (ar_zero_pt Ar) x + eps.
Proof.
move=> _ eps_pos.
exists (id_test (ar_zero Ar)); split; first by [].
rewrite /id_test /= /id_test_fun /cone_norm/= /c1_norm.
by rewrite ltW// ltrDl.
Qed.

End ConeOneMConeAux.
End ConeOneMConeAux.

(** Paper §2.3: register the [isMCone] instance on [cone_one_car Ar]. *)
HB.instance Definition _ (R : realType) (Ar : MeasSubcat R) :=
  @isMCone.Build R Ar (cone_one_car Ar)
    (@ConeOneMConeAux.mcone_M_one R Ar)
    (@ConeOneMConeAux.mcone_M_one_comp R Ar)
    (@ConeOneMConeAux.mcone_M_one_sep R Ar)
    (@ConeOneMConeAux.mcone_M_one_norm R Ar).

(** ** Deliverable 1 — Paper §4: [cone_one_car] is integrable

    For [β : ar_carrier X → cone_one_car Ar] (measurable path) and
    [µ : fmeas R (ar_carrier X)], the integral is the wrapped value
    [MkConeOne (fine ∫ (c1_val (β r))%:num µ(dr))%:nng]. *)

Section ConeOneICone.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation T := (cone_one_car Ar).

Local Open Scope ereal_scope.

(** Paper §4: for a measurable path [β : X → R≥0] against a finite
    measure [µ], the [\bar R]-integral of [(c1_val (β r))%:num] is
    finite. *)
Lemma cone_one_int_fin
    (X : ar_obj Ar)
    (β : ar_carrier Ar X -> T)
    (Hβ : is_measurable_path β)
    (µ : fmeas R (ar_carrier Ar X)) :
  \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X])
    ((c1_val (β r))%:num)%:E \is a fin_num.
Proof.
case: Hβ => [[M HM] Hmeas].
have meas_β :
    measurable_fun setT
                   (fun r => ((c1_val (β r))%:num)%:E).
  apply/measurable_EFinP.
  pose m := ConeOneMConeAux.id_test (R:=R) (Ar:=Ar) (ar_zero Ar).
  have mM : @mcone_M R Ar _ (ar_zero Ar) m by [].
  pose F (p : ar_carrier Ar (ar_zero Ar) * ar_carrier Ar X) : R :=
    test_fun m p.1 (β p.2).
  have HmeasF : measurable_fun
      [set: (ar_carrier Ar (ar_zero Ar) * ar_carrier Ar X)%type] F.
    exact: Hmeas.
  have -> : (fun r => (c1_val (β r))%:num) =
            (fun r => F (ar_zero_pt Ar, r)).
    by apply: funext => r.
  apply: (measurableT_comp (f := F)) => //.
apply: fin_real.
apply/andP; split.
  apply: (@lt_le_trans _ _ 0).
    by rewrite ltNyr.
  by apply: integral_ge0 => r _; rewrite lee_fin.
pose Mp : R := Num.max M 0%R.
have HMp : (0 <= Mp)%R by rewrite le_max lexx orbT.
have HMb r : ((c1_val (β r))%:num)%:E <= Mp%:E.
  rewrite lee_fin; apply: le_trans (HM r) _.
  by rewrite le_max lexx.
apply: (@le_lt_trans _ _ (Mp%:E * fmeas_mu µ [set: ar_carrier Ar X])).
  have -> : Mp%:E * fmeas_mu µ [set: ar_carrier Ar X] =
            \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X]) (cst Mp%:E) r.
    by rewrite integral_cst.
  apply: ge0_le_integral.
  - exact: measurableT.
  - by move=> r _; rewrite lee_fin nngnum_ge0.
  - exact: meas_β.
  - exact: measurable_cst.
  - by move=> r _; exact: HMb.
have HfinT : fmeas_mu µ [set: ar_carrier Ar X] \is a fin_num
  by exact: fmeas_setT_fin.
apply: lte_mul_pinfty => //.
by rewrite ltey_eq HfinT.
Qed.

(** Paper §4: the value of the [\bar R]-integral of [β(r)%:num] is
    non-negative — packaged as a separate lemma to keep
    [cone_one_int] transparent. *)
Lemma cone_one_int_ge0
    (X : ar_obj Ar)
    (β : ar_carrier Ar X -> T)
    (µ : fmeas R (ar_carrier Ar X)) :
  (0 <= fine (\int[fmeas_mu µ]_(r in [set: ar_carrier Ar X])
                ((c1_val (β r))%:num)%:E))%R.
Proof.
apply: fine_ge0.
by apply: integral_ge0 => r _; rewrite lee_fin.
Qed.

(** Paper §4: the integral value, wrapped as a [cone_one_car]. *)
Definition cone_one_int
    (X : ar_obj Ar)
    (β : ar_carrier Ar X -> T)
    (_ : is_measurable_path β)
    (µ : fmeas R (ar_carrier Ar X)) : T :=
  MkConeOne Ar (NngNum (cone_one_int_ge0 β µ)).

(** Paper §4 (Def 4.1): the integral satisfies the Pettis defining
    equation. *)
Lemma cone_one_int_pettis
    (X : ar_obj Ar)
    (β : ar_carrier Ar X -> T)
    (Hβ : is_measurable_path β)
    (µ : fmeas R (ar_carrier Ar X)) :
  path_integral_eq β µ (cone_one_int Hβ µ).
Proof.
move=> m mM s.
have Em : m = ConeOneMConeAux.id_test (Ar:=Ar) (ar_zero Ar) := mM.
rewrite Em /ConeOneMConeAux.id_test /= /ConeOneMConeAux.id_test_fun.
by rewrite /cone_one_int /=.
Qed.

(** Paper §4 (Def 4.1): every measurable path on [cone_one_car Ar]
    against every finite measure admits an integral. *)
Lemma cone_one_int_exists
    (X : ar_obj Ar)
    (β : ar_carrier Ar X -> T) :
  is_measurable_path β ->
  forall µ : fmeas R (ar_carrier Ar X),
    is_path_integrable β µ.
Proof.
move=> Hβ µ.
exists (cone_one_int Hβ µ); exact: cone_one_int_pettis.
Qed.

End ConeOneICone.

(** Paper §4: register the [isICone] instance on [cone_one_car Ar]. *)
HB.instance Definition _ (R : realType) (Ar : MeasSubcat R) :=
  @isICone.Build R Ar (cone_one_car Ar)
    (@cone_one_int_exists R Ar).

(** ** Deliverable 2 — Paper Theorem 4.5: [FMeas(X)] is integrable

    For [X ∈ Ar], a bounded kernel
    [β : ar_carrier X' → fmeas R (ar_carrier X)] and a finite measure
    [µ : fmeas R (ar_carrier X')], the integral is the measure
    [V ↦ ∫_(s ∈ X') (β s) V dµ(s)] on [X]. This is paper's
    "integration of a kernel". *)

Section FMeasICone.
Variables (R : realType) (Ar : MeasSubcat R).
Variable X : ar_obj Ar.

Local Notation T := (fmeas R (ar_carrier Ar X)).

Local Open Scope ereal_scope.

Section FMeasIntegralData.
Variable X' : ar_obj Ar.
Variable β : ar_carrier Ar X' -> T.
Hypothesis Hβ : is_measurable_path β.
Variable µ : fmeas R (ar_carrier Ar X').

(** Paper Theorem 4.5: for measurable [U], the [\bar R]-valued
    function [r ↦ (β r) U] is measurable. Derived from
    measurability of the test [e_U] in the kernel direction. *)
Lemma fmeas_int_meas_fun (U : set (ar_carrier Ar X)) :
  measurable U ->
  measurable_fun setT
                 (fun r => fmeas_mu (β r) U).
Proof.
move=> mU.
have := Hβ.
case=> [_ Hmeas].
have mM : mcone_M (ar_zero Ar) (fmeas_eU (Ar:=Ar) (ar_zero Ar) mU).
  by exists U, mU.
have HmeasEU :=
  Hmeas (ar_zero Ar) (fmeas_eU (Ar:=Ar) (ar_zero Ar) mU) mM.
have meas_fine_β_U :
    measurable_fun setT
                   (fun r => fine (fmeas_mu (β r) U)).
  pose F (p : ar_carrier Ar (ar_zero Ar) * ar_carrier Ar X') : R :=
    test_fun (fmeas_eU (Ar:=Ar) (ar_zero Ar) mU) p.1 (β p.2).
  have HF : measurable_fun
      [set: (ar_carrier Ar (ar_zero Ar) * ar_carrier Ar X')%type] F.
    exact: HmeasEU.
  have -> : (fun r => fine (fmeas_mu (β r) U)) =
            (fun r => F (ar_zero_pt Ar, r)).
    by apply: funext.
  apply: (measurableT_comp (f := F)) => //.
have -> : (fun r => fmeas_mu (β r) U) =
          (fun r => (fine (fmeas_mu (β r) U))%:E).
  apply: funext => r; rewrite fineK//; exact: fmeas_fin.
exact/measurable_EFinP.
Qed.

(** Paper Theorem 4.5: the candidate measure
    [ν(U) := ∫_(s ∈ X') (β s) U dµ(s)] on the σ-algebra of [X],
    canonically extended by 0 off it. *)
Definition fmeas_int_fun : set (ar_carrier Ar X) -> \bar R :=
  fun U => if `[< measurable U >] then
             \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X'])
               fmeas_mu (β r) U
           else 0.

Lemma fmeas_int_fun_E (U : set (ar_carrier Ar X)) :
  measurable U ->
  fmeas_int_fun U =
  \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X']) fmeas_mu (β r) U.
Proof. by move=> mU; rewrite /fmeas_int_fun asboolT. Qed.

Lemma fmeas_int_fun_off (U : set (ar_carrier Ar X)) :
  ~ measurable U -> fmeas_int_fun U = 0.
Proof. by move=> nmU; rewrite /fmeas_int_fun asboolF. Qed.

Lemma fmeas_int_set0 : fmeas_int_fun set0 = 0.
Proof.
rewrite fmeas_int_fun_E ?measurable0//.
under eq_integral do rewrite measure0.
exact: integral0.
Qed.

Lemma fmeas_int_ge0 (U : set (ar_carrier Ar X)) :
  0 <= fmeas_int_fun U.
Proof.
rewrite /fmeas_int_fun.
case: asboolP => mU; last exact: lexx.
by apply: integral_ge0 => r _; exact: measure_ge0.
Qed.

(** Paper Theorem 4.5: σ-additivity of [fmeas_int_fun].

    For pairwise disjoint measurable [Fn] with measurable union,
    use σ-additivity of [β r] pointwise, then monotone convergence
    on partial sums of measurable non-negative
    [\bar R]-valued functions to swap [∫_µ] and [Σ]. *)
Lemma fmeas_int_sigma_additive : semi_sigma_additive fmeas_int_fun.
Proof.
move=> F mF tF mUF.
(* The pointwise series [\sum_n (β r)(F n) -> (β r)(\bigcup_n F n)]. *)
have HsigmaR r :
    \sum_(0 <= i < n) fmeas_mu (β r) (F i)
      @[n --> \oo] -->
    fmeas_mu (β r) (\bigcup_n F n).
  exact: measure_semi_sigma_additive.
have lim_partial_sum r :
    limn (fun n => \sum_(0 <= i < n) fmeas_mu (β r) (F i)) =
    fmeas_mu (β r) (\bigcup_n F n).
  exact: cvg_lim (HsigmaR r).
have meas_partial_sum n :
    measurable_fun setT
      (fun r => \sum_(0 <= i < n) fmeas_mu (β r) (F i)).
  elim: n => [|n IH].
    by under eq_fun do rewrite big_nil; exact: measurable_cst.
  under eq_fun do rewrite big_nat_recr//=.
  apply: emeasurable_funD => //.
  exact: fmeas_int_meas_fun.
(* Swap [∫] and [Σ] via [cvg_monotone_convergence]. *)
have cvg_int_partial :
    \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X'])
      \sum_(0 <= i < n) fmeas_mu (β r) (F i)
      @[n --> \oo] -->
    \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X'])
      fmeas_mu (β r) (\bigcup_n F n).
  rewrite [X in _ --> X](_ : _ =
    \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X'])
      (fun r' => limn (fun n =>
         \sum_(0 <= i < n) fmeas_mu (β r') (F i))) r); last first.
    by apply: eq_integral => r _; rewrite lim_partial_sum.
  apply: cvg_monotone_convergence => //.
  - by move=> n r _; apply: sume_ge0 => i _; exact: measure_ge0.
  - move=> r _ n m nm.
    by apply: lee_sum_nneg_natr => // k _ _; exact: measure_ge0.
(* Linearity: [∫ \sum_(i<n) (β r)(F i) dµ = \sum_(i<n) ∫ (β r)(F i) dµ]. *)
have int_partial_eq n :
    \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X'])
      \sum_(0 <= i < n) fmeas_mu (β r) (F i) =
    \sum_(0 <= i < n) \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X'])
                        fmeas_mu (β r) (F i).
  elim: n => [|n IH].
    rewrite big_nil.
    under eq_fun do rewrite big_nil.
    by rewrite integral0.
  rewrite big_nat_recr//= -IH.
  rewrite [LHS](_ : _ =
    \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X'])
      ((\sum_(0 <= i < n) fmeas_mu (β r) (F i)) +
       fmeas_mu (β r) (F n))); last first.
    by apply: eq_integral => r _; rewrite big_nat_recr.
  apply: ge0_integralD; first exact: measurableT.
  - by move=> r _; apply: sume_ge0 => i _; exact: measure_ge0.
  - exact: meas_partial_sum.
  - by move=> r _; exact: measure_ge0.
  - exact: fmeas_int_meas_fun.
(* Conclude: partial sums of [fmeas_int_fun (F i)] converge to
   [fmeas_int_fun (⋃ F)]. *)
have step n :
    \sum_(0 <= i < n) fmeas_int_fun (F i) =
    \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X'])
      \sum_(0 <= i < n) fmeas_mu (β r) (F i).
  rewrite int_partial_eq.
  apply: eq_bigr => i _; rewrite fmeas_int_fun_E//; exact: mF.
rewrite fmeas_int_fun_E//.
under eq_fun do rewrite step.
exact: cvg_int_partial.
Qed.

HB.instance Definition _ :=
  isMeasure.Build _ _ _ fmeas_int_fun
    fmeas_int_set0 fmeas_int_ge0 fmeas_int_sigma_additive.

Lemma fmeas_int_finP : fmeas_finP fmeas_int_fun.
Proof.
move=> U mU; rewrite fmeas_int_fun_E//.
(* For U measurable, [∫ (β r)(U) dµ(r) ≤ ∫ ‖β r‖ dµ(r) ≤ M * µ(X')]
   for some M bounding ‖β r‖. Hence finite. *)
case: Hβ => [[M HM] _].
pose Mp : R := Num.max M 0%R.
have HMp : (0 <= Mp)%R by rewrite le_max lexx orbT.
have HMb r : fmeas_mu (β r) U <= Mp%:E.
  apply: (@le_trans _ _ (fmeas_mu (β r) [set: ar_carrier Ar X])).
    by apply: le_measure => //; rewrite inE.
  have HfinTr : fmeas_mu (β r) [set: ar_carrier Ar X] \is a fin_num
    by exact: fmeas_setT_fin.
  rewrite -(fineK HfinTr) lee_fin.
  apply: le_trans (HM r) _.
  by rewrite le_max lexx.
have meas_int_ge_minfty :
    -oo < \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X'])
            fmeas_mu (β r) U.
  apply: (@lt_le_trans _ _ 0).
    by rewrite ltNyr.
  by apply: integral_ge0 => r _; exact: measure_ge0.
have meas_int_lt_pinfty :
    \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X'])
      fmeas_mu (β r) U < +oo.
  apply: (@le_lt_trans _ _ (Mp%:E * fmeas_mu µ [set: ar_carrier Ar X'])).
    have -> : Mp%:E * fmeas_mu µ [set: ar_carrier Ar X'] =
      \int[fmeas_mu µ]_(r in [set: ar_carrier Ar X']) cst Mp%:E r.
      by rewrite integral_cst.
    apply: ge0_le_integral.
    - exact: measurableT.
    - by move=> r _; exact: measure_ge0.
    - exact: fmeas_int_meas_fun.
    - exact: measurable_cst.
    - by move=> r _; exact: HMb.
  have HfinT : fmeas_mu µ [set: ar_carrier Ar X'] \is a fin_num
    by exact: fmeas_setT_fin.
  apply: lte_mul_pinfty => //.
  by rewrite ltey_eq HfinT.
by rewrite fin_real// meas_int_ge_minfty meas_int_lt_pinfty.
Qed.

Lemma fmeas_int_canon : fmeas_canon fmeas_int_fun.
Proof. exact: fmeas_int_fun_off. Qed.

(** Paper Theorem 4.5: the candidate integral as an [fmeas R Y]
    (with finiteness + canonicality invariants). *)
Definition fmeas_int : T :=
  MkFmeas
    [the {measure set _ -> \bar R} of fmeas_int_fun]
    fmeas_int_finP fmeas_int_canon.

(** Paper Theorem 4.5 (Def 4.1): the candidate measure satisfies
    the Pettis defining equation against every [e_U] test. *)
Lemma fmeas_int_pettis : path_integral_eq β µ fmeas_int.
Proof.
move=> m mM s.
case: mM => U [mU ->].
rewrite /fmeas_eU /= /eU_fun /= fmeas_int_fun_E//.
f_equal.
apply: eq_integral => r _.
by rewrite fineK//; exact: fmeas_fin.
Qed.

End FMeasIntegralData.

(** Paper Theorem 4.5: every measurable path on [fmeas R (ar_carrier Ar X)]
    against every finite measure admits an integral. *)
Lemma fmeas_int_exists
    (X' : ar_obj Ar)
    (β : ar_carrier Ar X' -> T) :
  is_measurable_path β ->
  forall µ : fmeas R (ar_carrier Ar X'),
    is_path_integrable β µ.
Proof.
move=> Hβ µ.
exists (fmeas_int Hβ µ); exact: fmeas_int_pettis.
Qed.

End FMeasICone.

(** Paper Theorem 4.5: register the [isICone] instance on
    [fmeas R (ar_carrier Ar X)] for each [X : ar_obj Ar]. *)
HB.instance Definition _ (R : realType) (Ar : MeasSubcat R)
    (X : ar_obj Ar) :=
  @isICone.Build R Ar (fmeas R (ar_carrier Ar X))
    (@fmeas_int_exists R Ar X).

(** ** Deliverable 3 — Paper Theorem 4.12: [Path(X, B)] is integrable
       when [B] is

    For [B : iconeType Ar], [X : ar_obj Ar], a measurable path
    [η : Y' → path_car Ar X B] and a finite measure
    [ν : fmeas R (ar_carrier Y')], the integral
    [γ : path_car Ar X B] is defined pointwise:
    [γ(s) := icone_integral (fun r => path_fun (η r) s) _ ν : B]. *)

Section PathICone.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (X : ar_obj Ar) (B : iconeType Ar).

Local Notation P := (path_car Ar X B).

Section PathIntegralData.
Variable Y' : ar_obj Ar.
Variable η : ar_carrier Ar Y' -> P.
Hypothesis Hη : is_measurable_path η.
Variable ν : fmeas R (ar_carrier Ar Y').

(** A general "constant at [s]" ar_hom from any [Z ∈ Ar] to [X],
    used to apply [path_test] at arbitrary arities. *)
Section ConstArHomZ.
Variables (Z : ar_obj Ar) (s : ar_carrier Ar X).

Let const_zs_fun : ar_carrier Ar Z -> ar_carrier Ar X := fun _ => s.

Lemma const_zs_measurable :
  measurable_fun setT const_zs_fun.
Proof. exact: measurable_cst. Qed.

HB.instance Definition _ :=
  isMeasurableFun.Build _ _ _ _ const_zs_fun const_zs_measurable.

Definition const_zs : ar_hom Ar Z X := const_zs_fun.
End ConstArHomZ.

(** Paper Theorem 4.12: at each [s ∈ X], the function
    [r ↦ path_fun (η r) s] is a measurable path. *)
Lemma path_int_pt_meas (s : ar_carrier Ar X) :
  is_measurable_path (fun r : ar_carrier Ar Y' => path_fun (η r) s).
Proof.
have [[M HM] Hη_meas] := Hη.
split.
  exists M => r.
  apply: le_trans (path_norm_ub (η r) s) _; exact: HM.
move=> Z m mM.
(* The test [path_test (const_zs Z s) m] on [P] at arity Z is
   [(z, γ) ↦ m z (path_fun γ s)]. Applied to [γ = η r], we get
   [(z, r) ↦ m z (path_fun (η r) s)], which is measurable by
   [is_measurable_path η]. *)
pose pm : test_of Ar Z P := path_test (const_zs Z s) m mM.
have pmM : mcone_M Z pm by exists (const_zs Z s), m, mM.
have := Hη_meas Z pm pmM.
by under [in X in measurable_fun _ X -> _]eq_fun do
  rewrite /path_test/= /path_test_fun/=.
Qed.

(** Paper Theorem 4.12: the candidate integral, defined pointwise
    via [B]'s [icone_integral]. *)
Definition path_int_fun : ar_carrier Ar X -> B :=
  fun s => icone_integral (fun r => path_fun (η r) s) (path_int_pt_meas s) ν.

(** Paper Theorem 4.12: at every arity-0 test [m] on [B] (which
    captures the spec characterising [icone_integral]), the Pettis
    spec applied at the test [test_reindex (const_zs (ar_zero) z) m]
    in [mcone_M (ar_zero Ar)] gives:
    [test_fun m z (path_int_fun s) =
       fine (∫ test_fun m z (path_fun (η r) s) dν(r))]
    when [z = ar_zero_pt Ar]. We package this directly. *)

Lemma path_int_fun_pettis_ar0 (m : test_of Ar (ar_zero Ar) B)
    (mM : mcone_M (ar_zero Ar) m) (s : ar_carrier Ar X) :
  test_fun m (ar_zero_pt Ar) (path_int_fun s) =
  fine (\int[fmeas_mu ν]_(r in [set: ar_carrier Ar Y'])
          (test_fun m (ar_zero_pt Ar) (path_fun (η r) s))%:E).
Proof.
rewrite /path_int_fun.
exact: icone_integralP.
Qed.

(** Paper Theorem 4.12 (continued): the candidate integral
    [path_int_fun] is bounded in cone-norm by [‖η‖ · ‖ν‖]. *)
Lemma path_int_fun_bound :
  exists M : R, forall s : ar_carrier Ar X,
    (cone_norm (path_int_fun s) <= M)%R.
Proof.
have [[Mη HMη] _] := Hη.
exists (Mη * fmeas_norm ν).
move=> s.
apply: (path_integral_norm_le
          (Mβ := Mη)
          (β := fun r => path_fun (η r) s)).
- by move=> r; apply: le_trans (path_norm_ub (η r) s) _; exact: HMη.
- exact: path_int_pt_meas.
- exact: icone_integralP.
Qed.

(** Paper Theorem 4.12 (continued): joint test-measurability of
    [path_int_fun].

    Given joint measurability of [(z, s, r) ↦ test_fun m z (path_fun
    (η r) s)] on [Z × X × Y'] (a hypothesis: see below for the
    natural source via [is_measurable_path η] at the [ar_prod Z X]
    arity, modulo the [ar_prod_carrier_eq] cast), the function
    [path_int_fun] inherits joint measurability against any test [m]
    of [B] at arity [Z]. *)
Lemma path_int_fun_test_meas (Z : ar_obj Ar) (m : test_of Ar Z B)
    (mM : mcone_M Z m)
    (Hjoint : measurable_fun
      [set: (ar_carrier Ar Z *
             (ar_carrier Ar X * ar_carrier Ar Y'))%type]
      (fun p => test_fun m p.1 (path_fun (η p.2.2) p.2.1))) :
  measurable_fun setT
    (fun p => test_fun m p.1 (path_int_fun p.2)).
Proof.
have [[Mη HMη] _] := Hη.
(* Apply icone_integral_joint_measurable with appropriate args *)
pose β' (s : ar_carrier Ar X) (r : ar_carrier Ar Y') : B :=
  path_fun (η r) s.
have Hβ' : forall s, is_measurable_path (β' s) by exact: path_int_pt_meas.
pose κ' (_ : ar_carrier Ar X) : fmeas R (ar_carrier Ar Y') := ν.
have κ'_meas : forall U, measurable U ->
    measurable_fun setT
                   (fun s => fmeas_mu (κ' s) U).
  by move=> U mU; exact: measurable_cst.
have κ'_bound : exists M, forall s, (fmeas_norm (κ' s) <= M)%R.
  by exists (fmeas_norm ν) => s; exact: lexx.
(* Adapt Hjoint to the shape D1c expects: rearrange parens *)
have Hjoint' : measurable_fun
  [set: (ar_carrier Ar Z *
         (ar_carrier Ar X * ar_carrier Ar Y'))%type]
  (fun p => test_fun m p.1 (β' p.2.1 p.2.2)).
  exact: Hjoint.
(* M-bound on test integrand: test_fun ≤ cone_norm ≤ Mη *)
have Mb : exists M : R, forall z s r,
  (test_fun m z (β' s r) <= M)%R.
  exists Mη => z s r.
  apply: le_trans (test_norm_le _ _ _) _.
  apply: le_trans (path_norm_ub (η r) s) _; exact: HMη.
have HmeasI :=
  @icone_integral_joint_measurable R Ar B Y' _ (ar_carrier Ar X)
    β' Hβ' κ' Z m mM κ'_meas κ'_bound Hjoint' Mb.
(* HmeasI gives measurability of
   (z, s) ↦ test_fun m z (icone_integral (β' s) (Hβ' s) (κ' s))
   which equals path_int_fun. *)
apply: (eq_measurable_fun
  (fun p => test_fun m p.1
              (icone_integral (β' p.2) (Hβ' p.2) (κ' p.2)))).
  move=> p _.
  rewrite /path_int_fun /β' /κ'.
  congr (test_fun m _ _).
  apply: icone_integral_eqP.
  exact: icone_integralP.
exact: HmeasI.
Qed.

(** Paper Theorem 4.12 (continued): conditional path measurability of
    [path_int_fun].

    Given the family of joint test-measurability hypotheses (one per
    test of [B]), [path_int_fun] is itself a measurable path in
    [Path(X, B)]. *)
Lemma path_int_fun_is_path
    (Hjoint : forall (Z : ar_obj Ar) (m : test_of Ar Z B)
                     (mM : mcone_M Z m),
       measurable_fun
         [set: (ar_carrier Ar Z *
                (ar_carrier Ar X * ar_carrier Ar Y'))%type]
         (fun p => test_fun m p.1 (path_fun (η p.2.2) p.2.1))) :
  is_measurable_path path_int_fun.
Proof.
split; first exact: path_int_fun_bound.
move=> Z m mM.
exact: (path_int_fun_test_meas mM (Hjoint Z m mM)).
Qed.

End PathIntegralData.

(** Paper Theorem 4.12 (continued): existence of the path integral.

    Given the per-test joint measurability hypotheses, the
    pointwise-defined [path_int_fun] yields a measurable path that
    satisfies the Pettis equation, witnessing path-integrability. *)
Lemma path_int_exists_cond
    (Y' : ar_obj Ar)
    (η : ar_carrier Ar Y' -> path_car Ar X B)
    (Hη : is_measurable_path η)
    (ν : fmeas R (ar_carrier Ar Y'))
    (Hjoint : forall (Z : ar_obj Ar) (m : test_of Ar Z B)
                     (mM : mcone_M Z m),
       measurable_fun
         [set: (ar_carrier Ar Z *
                (ar_carrier Ar X * ar_carrier Ar Y'))%type]
         (fun p => test_fun m p.1 (path_fun (η p.2.2) p.2.1))) :
  is_path_integrable η ν.
Proof.
have Hpif := path_int_fun_is_path Hη ν Hjoint.
pose γ : path_car Ar X B := MkPath Hpif.
exists γ.
move=> p pM s.
(* p ∈ path_mcone_M (ar_zero Ar) iff p = path_test (const_r r0) m mM
   for some r0, m, mM ∈ mcone_M (ar_zero Ar) B. *)
case: pM => φ [m [mM ->]].
rewrite /path_test/= /path_test_fun/=.
rewrite (ar_zero_ptE s).
exact: path_int_fun_pettis_ar0.
Qed.

End PathICone.

(** ** Paper Theorem 4.12 — full unconditional Path-integrability

    Using the [ar.v] product helpers ([ar_prod_uncast], [ar_prod_cast],
    [ar_prod_fst], [ar_prod_snd]), we close the [Hjoint] hypothesis of
    [path_int_exists_cond] by deriving the joint test-measurability
    directly from [is_measurable_path η]. The natural route applies
    [is_measurable_path η] at the test-arity [ar_prod Z X] with the
    reindexed test [path_test ar_prod_snd (test_reindex ar_prod_fst
    m) mM'], and translates the output across the propositional
    carrier equation [ar_prod_carrier_eq Ar Z X].

    Cast measurability is now a record field of [MeasSubcat] (paper §3,
    [ar_prod_uncast_meas] / [ar_prod_cast_meas]), so this section is
    unconditional. *)

Section PathIConeFull.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (X : ar_obj Ar) (B : iconeType Ar).

Local Notation P := (path_car Ar X B).

(** Paper Theorem 4.12: discharge the joint test-measurability
    hypothesis of [path_int_exists_cond] using [is_measurable_path
    η] at arity [ar_prod Z X]. *)
Lemma path_int_joint_meas
    (Y' : ar_obj Ar)
    (η : ar_carrier Ar Y' -> P)
    (Hη : is_measurable_path η)
    (Z : ar_obj Ar) (m : test_of Ar Z B) (mM : mcone_M Z m) :
  measurable_fun
    [set: (ar_carrier Ar Z *
           (ar_carrier Ar X * ar_carrier Ar Y'))%type]
    (fun p => test_fun m p.1 (path_fun (η p.2.2) p.2.1)).
Proof.
have [_ Hη_meas] := Hη.
(* Build the test family on the product arity [ar_prod Z X]:
   [path_test (ar_prod_snd) (test_reindex (ar_prod_fst) m) mM']
   evaluates at [(s', γ)] to
   [test_fun (test_reindex ar_prod_fst m) s' (path_fun γ (ar_prod_snd s'))]
   = [test_fun m (ar_prod_fst s') (path_fun γ (ar_prod_snd s'))]. *)
pose ar_fst : ar_hom Ar (ar_prod Ar Z X) Z := ar_prod_fst Z X.
pose ar_snd : ar_hom Ar (ar_prod Ar Z X) X := ar_prod_snd Z X.
pose m' : test_of Ar (ar_prod Ar Z X) B := test_reindex ar_fst m.
have mM' : mcone_M (ar_prod Ar Z X) m'.
  by apply: mcone_M_comp.
pose pm : test_of Ar (ar_prod Ar Z X) P := path_test ar_snd m' mM'.
have pmM : @path_mcone_M R Ar X B (ar_prod Ar Z X) pm.
  by exists ar_snd, m', mM'.
(* Apply [is_measurable_path η] at this test. *)
have Hη' : measurable_fun
  [set: (ar_carrier Ar (ar_prod Ar Z X) * ar_carrier Ar Y')%type]
  (fun p => test_fun pm p.1 (η p.2)).
  exact: (Hη_meas (ar_prod Ar Z X) pm pmM).
(* Now translate to [Z * (X * Y')] via [ar_prod_cast]. *)
pose ψ (p : (ar_carrier Ar Z * (ar_carrier Ar X * ar_carrier Ar Y'))%type) :
    (ar_carrier Ar (ar_prod Ar Z X) * ar_carrier Ar Y')%type :=
  (ar_prod_cast (p.1, p.2.1), p.2.2).
have ψ_meas : measurable_fun
    [set: (ar_carrier Ar Z *
           (ar_carrier Ar X * ar_carrier Ar Y'))%type] ψ.
  rewrite /ψ.
  apply: measurable_fun_pair.
  - have meas_p12 : measurable_fun setT
        (fun p : ar_carrier Ar Z *
                (ar_carrier Ar X * ar_carrier Ar Y') => (p.1, p.2.1)).
      apply: measurable_fun_pair.
      + exact: measurable_fst.
      + by apply: (measurableT_comp (f := fst));
          [exact: measurable_fst|exact: measurable_snd].
    exact: (measurableT_comp (ar_prod_cast_meas Ar Z X) meas_p12).
  - by apply: (measurableT_comp (f := snd));
      [exact: measurable_snd|exact: measurable_snd].
have eqψ p :
  test_fun m p.1 (path_fun (η p.2.2) p.2.1) =
  (fun q => test_fun pm q.1 (η q.2)) (ψ p).
  rewrite /ψ /pm /= /path_test_fun /m' /= /test_reindex_fun /=.
  rewrite /ar_fst /ar_snd /ar_prod_fst /ar_prod_snd /=.
  rewrite /ar_prod_fst_fun /ar_prod_snd_fun.
  by rewrite ar_prod_castK.
apply: (eq_measurable_fun (fun p =>
  (fun q : ar_carrier Ar (ar_prod Ar Z X) * ar_carrier Ar Y' =>
     test_fun pm q.1 (η q.2)) (ψ p))).
  by move=> p _; rewrite -eqψ.
exact: (measurableT_comp Hη' ψ_meas).
Qed.

(** Paper Theorem 4.12 (full): unconditional path-integrability for
    [path_car Ar X B], given the cast-measurability hypotheses. *)
Lemma path_int_exists
    (Y' : ar_obj Ar)
    (η : ar_carrier Ar Y' -> P)
    (Hη : is_measurable_path η)
    (ν : fmeas R (ar_carrier Ar Y')) :
  is_path_integrable η ν.
Proof.
apply: (path_int_exists_cond Hη ν) => Z m mM.
exact: (path_int_joint_meas Hη mM).
Qed.

(** Paper Theorem 4.12: register the [isICone] instance on
    [path_car Ar X B] for [B : iconeType Ar], conditionally on the
    cast-measurability hypotheses. Within this Section,
    [path_car Ar X B] is an [iconeType Ar]. *)
HB.instance Definition _ : isICone R Ar P :=
  isICone.Build R Ar P (@path_int_exists).

End PathIConeFull.

(** Sanity check: [path_car Ar X B] is recognised as an
    [iconeType Ar] unconditionally — cast measurability is now part
    of the [MeasSubcat] record. *)
Section PathIConeCheck.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (X : ar_obj Ar) (B : iconeType Ar).

(* The [isICone] instance registered above discharges
   into [path_car Ar X B : iconeType Ar] without any extra
   hypothesis. *)
Check (path_car Ar X B : iconeType Ar).

End PathIConeCheck.
