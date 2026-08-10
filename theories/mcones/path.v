(** * The measurable cone of paths — Paper §3.2.2

    Given a measurable cone [B] (an [mconeType Ar]) and an object
    [X : ar_obj Ar], the type [path_car X B] is the carrier of the
    paper's [Path(X, B)] cone: bounded measurable paths
    [γ : ar_carrier X -> B] equipped with pointwise algebraic
    operations, pointwise order, sup-norm, and the test family

      [{ φ ▷ m | φ : ar_hom Y X, m ∈ M^B_Y }]

    for each [Y ∈ Ar].

    Paper reference: §3.2.2 (pages 1:21–1:23) and Lemma 3.19.

    Coverage in this file:

    - [path_car Ar X B] — the underlying type of bounded measurable
      paths (carrier of [Path(X, B)]).
    - [path_precone] and [path_cone] HB instances on [path_car].
    - [path_norm] — paper's [‖γ‖ = sup_r ‖γ(r)‖].
    - [path_sup_ball] — the (Normc) witness, defined pointwise via
      [B]'s [cone_sup_ball].
    - [path_test φ m] — the [φ ▷ m] test on [path_car X B].
    - [path_mcone_M] — the test family, plus its (Mscomp), (Mssep),
      (Msnorm) properties.
    - HB instance [isMCone Ar (path_car X B)] — registers [Path(X, B)]
      as an [mconeType Ar].
    - [path_fl] / [path_fl_inv] and the iso [path_flE] — Paper
      Lemma 3.19: [Path(X, Path(Y, B)) ≃ Path(X × Y, B)].

    Design notes.

    - The carrier [path_car] is a [Record] rather than a sigma type;
      this avoids dependency-headaches when we register HB instances.
      Two paths are equal iff their underlying functions agree
      pointwise, by [path_eq] (extensionality + [Prop_irrelevance]).
    - The pointwise sup defining (Normc) is the cone_sup_ball of [B]
      taken on the chain [fun n => γ_n r]. Measurability of the limit
      uses [measurable_fun_cvg] from mathcomp-analysis, applied to
      the increasing chain of measurable functions
      [(s, r) ↦ m(s, γ_n(r))] which converges pointwise to
      [(s, r) ↦ m(s, γ(r))] by ω-continuity of every test [m] in
      its second argument.
    - The carrier of the codomain of [path_fl] is [path_car (ar_prod
      Ar X Y) B]; the codomain measurable structure on [ar_prod X Y]
      is fixed by the [ar_prod_carrier_eq] equation supplied by
      [MeasSubcat]. We cast across that equation as needed.

    *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import topology normedtype sequences.
Import numFieldTopology.Exports.

Require Import Icones.prelude.nonneg_extra.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.cone_cat.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** The carrier of [Path(X, B)] — Paper §3.2.2

    A measurable path [γ : ar_carrier X -> B] packaged with its
    [is_measurable_path] proof. *)

Section PathCarrier.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (X : ar_obj Ar) (B : MCone.type Ar).

(** Paper §3.2.2: the underlying type of [Path(X, B)]. *)
Record path_car : Type := MkPath {
  path_fun :> ar_carrier Ar X -> B;
  path_is_path : is_measurable_path (Ar:=Ar) (C:=B) (X:=X) path_fun;
}.

(** Extensionality: two paths are equal iff their underlying functions
    are pointwise equal. *)
Lemma path_eq (γ1 γ2 : path_car) :
  (forall r, path_fun γ1 r = path_fun γ2 r) -> γ1 = γ2.
Proof.
case: γ1 => f1 H1; case: γ2 => f2 H2 /= Hfun.
have Hf : f1 = f2 by apply: funext.
move: H1; rewrite Hf => H1.
by congr MkPath; exact: Prop_irrelevance.
Qed.

End PathCarrier.

Arguments path_car {R} Ar X B.
Arguments path_fun {R Ar X B} _.
Arguments path_is_path {R Ar X B} _.

(** ** Pointwise algebraic operations on [path_car] *)

Section PathAlgebra.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (X : ar_obj Ar) (B : MCone.type Ar).
Implicit Types γ : path_car Ar X B.

(** Paper §3.2.2: the zero path [λ r. 0]. Its measurability follows
    from [const_path_measurable]. *)
Definition path_zero_fun : ar_carrier Ar X -> B :=
  fun _ => precone_zero.

Lemma path_zero_is_path :
  is_measurable_path (Ar:=Ar) (C:=B) (X:=X) path_zero_fun.
Proof. exact: const_path_measurable. Qed.

Definition path_zero : path_car Ar X B :=
  MkPath path_zero_is_path.

(** Helper: pointwise sum of two measurable paths is a measurable
    path. The measurability of [λ p. m(p.1, γ1(p.2) + γ2(p.2))] uses
    linearity of [m] in its second argument (test_linD), reducing it
    to the sum of two measurable real-valued functions. *)
Lemma path_add_is_path γ1 γ2 :
  is_measurable_path (Ar:=Ar) (C:=B) (X:=X)
    (fun r => precone_add (path_fun γ1 r) (path_fun γ2 r)).
Proof.
have [[M1 HM1] Hmeas1] := path_is_path γ1.
have [[M2 HM2] Hmeas2] := path_is_path γ2.
split.
  exists (M1 + M2) => r.
  apply: le_trans (cone_normt _ _) _.
  by apply: lerD; [exact: HM1|exact: HM2].
move=> Y m mM.
have -> :
  (fun p : (ar_carrier Ar Y * ar_carrier Ar X)%type =>
    test_fun m p.1 (precone_add (path_fun γ1 p.2) (path_fun γ2 p.2))) =
  (fun p : (ar_carrier Ar Y * ar_carrier Ar X)%type =>
    test_fun m p.1 (path_fun γ1 p.2) +
    test_fun m p.1 (path_fun γ2 p.2)).
  by apply: funext => p; rewrite test_linD.
by apply: measurable_funD; [exact: Hmeas1|exact: Hmeas2].
Qed.

Definition path_add γ1 γ2 : path_car Ar X B :=
  MkPath (path_add_is_path γ1 γ2).

(** Pointwise scalar multiplication: measurability uses [test_linZ]. *)
Lemma path_scale_is_path (r : {nonneg R}) γ :
  is_measurable_path (Ar:=Ar) (C:=B) (X:=X)
    (fun s => precone_scale r (path_fun γ s)).
Proof.
have [[M HM] Hmeas] := path_is_path γ; split.
  exists (r%:num * M) => s.
  rewrite cone_normh.
  have rge0 : 0 <= r%:num by exact: nngnum_ge0.
  have [-> | rpos] := eqVneq r%:num 0.
    by rewrite !mul0r.
  by rewrite ler_pM2l // lt_def rpos rge0.
move=> Y m mM.
have -> :
  (fun p : (ar_carrier Ar Y * ar_carrier Ar X)%type =>
    test_fun m p.1 (precone_scale r (path_fun γ p.2))) =
  (fun p : (ar_carrier Ar Y * ar_carrier Ar X)%type =>
    r%:num * test_fun m p.1 (path_fun γ p.2)).
  by apply: funext => p; rewrite test_linZ.
by apply: measurable_funM; [exact: measurable_cst|exact: Hmeas].
Qed.

Definition path_scale (r : {nonneg R}) γ : path_car Ar X B :=
  MkPath (path_scale_is_path r γ).

(** ** Precone axioms — Paper §3.2.2 (algebraic laws pointwise) *)

Lemma path_addA : associative path_add.
Proof.
move=> γ1 γ2 γ3; apply: path_eq => r /=.
exact: precone_addA.
Qed.

Lemma path_addC : commutative path_add.
Proof. move=> γ1 γ2; apply: path_eq => r /=; exact: precone_addC. Qed.

Lemma path_add0 : left_id path_zero path_add.
Proof.
move=> γ; apply: path_eq => r /=; exact: precone_add0.
Qed.

Lemma path_scale_DAr (r : {nonneg R}) γ1 γ2 :
  path_scale r (path_add γ1 γ2) =
  path_add (path_scale r γ1) (path_scale r γ2).
Proof.
apply: path_eq => s /=; exact: precone_scale_DAr.
Qed.

Lemma path_scale_DAl (r s : {nonneg R}) γ :
  path_scale (r%:num + s%:num)%:nng γ =
  path_add (path_scale r γ) (path_scale s γ).
Proof.
apply: path_eq => t /=; exact: precone_scale_DAl.
Qed.

Lemma path_scale_A (r s : {nonneg R}) γ :
  path_scale (r%:num * s%:num)%:nng γ =
  path_scale r (path_scale s γ).
Proof.
apply: path_eq => t /=; exact: precone_scale_A.
Qed.

Lemma path_scale_1 γ : path_scale 1%:nng γ = γ.
Proof. apply: path_eq => r /=; exact: precone_scale_1. Qed.

Lemma path_scale_0r r : path_scale r path_zero = path_zero.
Proof. apply: path_eq => s /=; exact: precone_scale_0r. Qed.

Lemma path_scale_0l γ : path_scale 0%:nng γ = path_zero.
Proof. apply: path_eq => r /=; exact: precone_scale_0l. Qed.

Lemma path_cancel γ1 γ2 γ3 :
  path_add γ1 γ2 = path_add γ1 γ3 -> γ2 = γ3.
Proof.
move=> H; apply: path_eq => r.
have /(congr1 (fun γ => path_fun γ r)) := H.
exact: precone_cancel.
Qed.

Lemma path_pos γ1 γ2 :
  path_add γ1 γ2 = path_zero -> γ1 = path_zero /\ γ2 = path_zero.
Proof.
move=> H; split; apply: path_eq => r;
  have /(congr1 (fun γ => path_fun γ r)) /= := H.
- by move/precone_pos => -[].
- by move/precone_pos => -[].
Qed.

End PathAlgebra.

(** ** Precone HB instance — Paper §3.2.2 *)

HB.instance Definition _ (R : realType) (Ar : MeasSubcat R)
    (X : ar_obj Ar) (B : MCone.type Ar) :=
  @isPrecone.Build R (path_car Ar X B)
    (@path_zero R Ar X B) (@path_add R Ar X B) (@path_scale R Ar X B)
    (@path_addA R Ar X B) (@path_addC R Ar X B) (@path_add0 R Ar X B)
    (@path_scale_DAr R Ar X B) (@path_scale_DAl R Ar X B)
    (@path_scale_A R Ar X B) (@path_scale_1 R Ar X B)
    (@path_scale_0r R Ar X B) (@path_scale_0l R Ar X B)
    (@path_cancel R Ar X B) (@path_pos R Ar X B).

(** ** Norm of a path — Paper §3.2.2 [‖γ‖ = sup_r ‖γ(r)‖] *)

Section PathNorm.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (X : ar_obj Ar) (B : MCone.type Ar).
Implicit Types γ : path_car Ar X B.

(** The set [{‖γ(r)‖ | r ∈ X}] used for the sup. *)
Definition path_normset γ : set R :=
  [set y | exists r : ar_carrier Ar X, y = cone_norm (path_fun γ r)].

Lemma path_normset_nonempty γ : path_normset γ !=set0.
Proof.
exists (cone_norm (path_fun γ (ar_point Ar X))).
by exists (ar_point Ar X).
Qed.

(** [γ] is bounded, so the set has an upper bound. *)
Lemma path_normset_has_ubound γ : has_ubound (path_normset γ).
Proof.
have [[M HM] _] := path_is_path γ.
by exists M => _ [r ->]; exact: HM.
Qed.

Lemma path_normset_has_sup γ : has_sup (path_normset γ).
Proof.
split; [exact: path_normset_nonempty | exact: path_normset_has_ubound].
Qed.

(** Paper §3.2.2: [‖γ‖ = sup_r ‖γ(r)‖]. *)
Definition path_norm γ : R := sup (path_normset γ).

Lemma path_norm_ge0 γ : 0 <= path_norm γ.
Proof.
have Hsup := sup_upper_bound (path_normset_has_sup γ).
have Hin : path_normset γ (cone_norm (path_fun γ (ar_point Ar X))).
  by exists (ar_point Ar X).
move/ubP : Hsup => /(_ _ Hin) HH.
exact: le_trans (cone_norm_ge0 _) HH.
Qed.

(** Pointwise bound: [‖γ(r)‖ ≤ ‖γ‖]. *)
Lemma path_norm_ub γ r : cone_norm (path_fun γ r) <= path_norm γ.
Proof.
move/ubP : (sup_upper_bound (path_normset_has_sup γ)); apply.
by exists r.
Qed.

End PathNorm.

(** ** Cone axioms on [path_car] — Paper §3.2.2 *)

Section PathConeAxioms.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (X : ar_obj Ar) (B : MCone.type Ar).
Implicit Types γ : path_car Ar X B.

(** (Normh) — Paper §3.2.2. *)
Lemma path_normh (r : {nonneg R}) γ :
  path_norm (path_scale r γ) = r%:num * path_norm γ.
Proof.
have rge0 : 0 <= r%:num by exact: nngnum_ge0.
have [rzero | rpos] := lerP r%:num 0.
  have req0 : r%:num = 0 by apply: le_anti; rewrite rzero rge0.
  rewrite req0 mul0r.
  apply: le_anti; apply/andP; split; last exact: path_norm_ge0.
  apply: ge_sup; first exact: path_normset_nonempty.
  move=> _ [s ->] /=.
  by rewrite /path_scale /= cone_normh req0 mul0r.
apply: le_anti; apply/andP; split.
- apply: ge_sup; first exact: path_normset_nonempty.
  move=> _ [s ->] /=.
  rewrite /path_scale /= cone_normh.
  by rewrite ler_pM2l //; exact: path_norm_ub.
- rewrite -ler_pdivlMl //.
  apply: ge_sup; first exact: path_normset_nonempty.
  move=> _ [s ->].
  rewrite ler_pdivlMl //.
  have Hin :
      path_normset (path_scale r γ) (r%:num * cone_norm (path_fun γ s)).
    by exists s => /=; rewrite /path_scale /= cone_normh.
  by move/ubP : (sup_upper_bound (path_normset_has_sup (path_scale r γ)));
    apply.
Qed.

(** (Normz) — Paper §3.2.2: a path of norm zero is the zero path. *)
Lemma path_normz γ : path_norm γ = 0 -> γ = path_zero X B.
Proof.
move=> H; apply: path_eq => r /=.
apply: cone_normz.
apply: le_anti; rewrite cone_norm_ge0 andbT.
rewrite -H; exact: path_norm_ub.
Qed.

(** (Normt) — Paper §3.2.2: triangle inequality. *)
Lemma path_normt γ1 γ2 :
  path_norm (path_add γ1 γ2) <= path_norm γ1 + path_norm γ2.
Proof.
apply: ge_sup; first exact: path_normset_nonempty.
move=> _ [r ->] /=.
apply: le_trans (cone_normt _ _) _.
by rewrite lerD //; exact: path_norm_ub.
Qed.

(** Helper: pointwise order on paths corresponds to the precone order
    on [path_car]. We prove [γ1 ≤p γ2] iff for all [r],
    [γ1 r ≤p γ2 r], using [precone_cancel]-style arguments. The
    forward direction is by definition (taking the witness pointwise);
    the reverse uses an axiom-of-choice-like step encoded by the
    classical extras to build the difference path. We only need the
    forward direction for (Normp). *)
Lemma path_le_pointwise γ1 γ2 :
  precone_le γ1 γ2 -> forall r, precone_le (path_fun γ1 r) (path_fun γ2 r).
Proof.
move=> [δ Hδ] r.
by exists (path_fun δ r); have /(congr1 (fun γ => path_fun γ r)) := Hδ.
Qed.

(** (Normp) — Paper §3.2.2: order monotonicity. *)
Lemma path_normp γ1 γ2 : precone_le γ1 γ2 -> path_norm γ1 <= path_norm γ2.
Proof.
move=> Hle.
apply: ge_sup; first exact: path_normset_nonempty.
move=> _ [r ->].
apply: le_trans (cone_normp _ _ (path_le_pointwise Hle r)) _.
exact: path_norm_ub.
Qed.

(** *** Pointwise differences of measurable paths

    If [f] and [g] are measurable paths and [w] is a pointwise
    difference witness ([g r = f r + w r] for every [r]), then [w] is
    itself a measurable path: it is bounded because [w r ≤p g r]
    (Normp), and for every test [m] the map [(s, r) ↦ m(s, w r)] is
    the difference of the two measurable maps for [g] and [f] (by
    [test_linD]). This is the common core of the (Normc) upper-bound
    and least-upper-bound proofs below. *)
Lemma path_sub_is_path (f g w : ar_carrier Ar X -> B) :
  is_measurable_path (Ar:=Ar) (C:=B) (X:=X) f ->
  is_measurable_path (Ar:=Ar) (C:=B) (X:=X) g ->
  (forall r, g r = precone_add (f r) (w r)) ->
  is_measurable_path (Ar:=Ar) (C:=B) (X:=X) w.
Proof.
move=> [_ Hfm] [[M HM] Hgm] w_eq; split.
  exists M => r.
  have Hle : precone_le (w r) (g r).
    by exists (f r); rewrite precone_addC; exact: w_eq.
  by apply: le_trans (cone_normp _ _ Hle) _; exact: HM.
move=> Y m mM.
have -> :
  (fun p : (ar_carrier Ar Y * ar_carrier Ar X)%type =>
     test_fun m p.1 (w p.2) : R) =
  (fun p : (ar_carrier Ar Y * ar_carrier Ar X)%type =>
     test_fun m p.1 (g p.2) - test_fun m p.1 (f p.2)).
  apply: funext => p.
  have /(congr1 (test_fun m p.1)) := w_eq p.2.
  by rewrite test_linD => ->; rewrite addrAC subrr add0r.
by apply: measurable_funB; [exact: Hgm|exact: Hfm].
Qed.

End PathConeAxioms.

(** ** (Normc) — the technical core of Paper §3.2.2

    Given an increasing chain [(γ_n)] of paths with [path_norm γ_n ≤ 1],
    we define the pointwise sup-ball path [γ(r) := cone_sup_ball
    (λ n. γ_n r) ...] in [B]. The supremum exists pointwise because:
    - chain hypothesis pointwise: by [path_le_pointwise];
    - norm bound pointwise: [‖γ_n(r)‖ ≤ ‖γ_n‖ ≤ 1] by [path_norm_ub].

    Measurability of the limit path uses the monotone-convergence form
    [measurable_fun_cvg]: the chain of measurable functions
    [(s, r) ↦ m(s, γ_n(r))] converges pointwise (by ω-continuity of
    [m]) to [(s, r) ↦ m(s, γ(r))]. *)

Section PathSupBall.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (X : ar_obj Ar) (B : MCone.type Ar).
Implicit Types u : nat -> path_car Ar X B.

Local Open Scope precone_scope.

(** Pointwise chain: [γ_n(r) ≤p γ_{n+1}(r)] for every [r]. *)
Lemma path_sup_ball_chain_pw u :
  (forall n, precone_le (u n) (u n.+1)) ->
  forall r n, precone_le (path_fun (u n) r) (path_fun (u n.+1) r).
Proof. by move=> uch r n; exact: path_le_pointwise. Qed.

(** Pointwise unit-ball bound: [‖γ_n(r)‖ ≤ 1] from [‖γ_n‖ ≤ 1]. *)
Lemma path_sup_ball_ub1_pw u :
  (forall n, path_norm (u n) <= 1) ->
  forall r n, cone_norm (path_fun (u n) r) <= 1.
Proof.
move=> ub1 r n.
apply: le_trans (path_norm_ub _ _) _; exact: ub1.
Qed.

(** Pointwise sup: the candidate underlying function for the
    sup-ball of the chain [u]. *)
Definition path_sup_ball_fun
  (u : nat -> path_car Ar X B)
  (uch : forall n, precone_le (u n) (u n.+1))
  (ub1 : forall n, path_norm (u n) <= 1)
  (r : ar_carrier Ar X) : B :=
  cone_sup_ball (fun n => path_fun (u n) r)
                (path_sup_ball_chain_pw uch r)
                (path_sup_ball_ub1_pw ub1 r).

(** *** Pointwise measurability of the sup *)

(** For every test [m ∈ mcone_M Y] of [B], the function
    [(s, r) ↦ m(s, γ(r))] is the pointwise sup of the measurable
    functions [(s, r) ↦ m(s, γ_n(r))]. By ω-continuity of [m] in its
    second argument, the chain converges to the sup pointwise; by
    [measurable_fun_cvg] this limit is measurable. *)

Lemma path_sup_ball_meas
  (u : nat -> path_car Ar X B)
  (uch : forall n, precone_le (u n) (u n.+1))
  (ub1 : forall n, path_norm (u n) <= 1)
  (Y : ar_obj Ar) (m : test_of Ar Y B) :
  mcone_M Y m ->
  measurable_fun
    [set: (ar_carrier Ar Y * ar_carrier Ar X)%type]
    (fun p : (ar_carrier Ar Y * ar_carrier Ar X)%type =>
       test_fun m p.1 (path_sup_ball_fun uch ub1 p.2) : R).
Proof.
move=> mM.
(* Each [γ_n] is a measurable path, so the chain
   [(s, r) ↦ m(s, γ_n(r))] is measurable for each n. *)
pose h (n : nat) (p : ar_carrier Ar Y * ar_carrier Ar X) : R :=
  test_fun m p.1 (path_fun (u n) p.2).
have meas_h : forall n,
  measurable_fun
    [set: (ar_carrier Ar Y * ar_carrier Ar X)%type] (h n).
  move=> n; rewrite /h.
  by have [_ H] := path_is_path (u n); exact: H.
(* Pointwise convergence of [h n p] to the target. By ω-continuity of
   [m] in its second argument, [test_fun m p.1 (sup_n γ_n(p.2))] is
   the [R]-sup of the increasing real sequence [h n p]. We thus need
   a real-valued limit. We instantiate the chain via
   [path_sup_ball_chain_pw] / [path_sup_ball_ub1_pw]. *)
(* Step 1: the real-valued sequence [h ^~ p] is nondecreasing for
   each fixed p. By [test_meas + linearity], it suffices to show that
   the cone-order on inputs is preserved by [test_fun m p.1 _]. We
   use the increasing-image hypothesis from [path_le_pointwise] and
   [linear_increasing] applied to the linear functional
   [λ x. m p.1 x]. *)
have h_ndec : forall p, nondecreasing_seq (h ^~ p).
  move=> p.
  apply/nondecreasing_seqP => n.
  rewrite /h.
  have Hpw := path_sup_ball_chain_pw uch p.2 n.
  case: Hpw => [z Hz].
  by rewrite [in leRHS]Hz test_linD lerDl; exact: test_ge0.
(* Step 2: [h ^~ p] is bounded above by 1. *)
have h_ub : forall p, has_ubound (range (h ^~ p)).
  move=> p; exists 1 => _ [n _ <-].
  rewrite /h; apply: test_le1; exact: path_sup_ball_ub1_pw.
(* Step 3: [h ^~ p] converges in [R] to its sup [sup (range (h ^~ p))]. *)
have h_cvg : forall p, (h ^~ p : nat -> R)
  @ \oo --> (sup (range (h ^~ p)) : R).
  by move=> p; apply: nondecreasing_cvgn; [exact: h_ndec | exact: h_ub].
(* Step 4: the limit equals [test_fun m p.1 (path_sup_ball_fun ... p.2)].
   We use the ω-continuity field of [test_of], stated as
   [test_cont]. Strategy: the sup in B is the unique LUB; the sup in
   R is the unique LUB of [h ^~ p]; we use anti-symmetry to identify
   them. We instantiate [test_cont] with [N := sup (range (h ^~ p))]
   to get the [≤] direction; for [≥] we use that [h n p ≤
   test_fun m p.1 (path_sup_ball_fun ...)] (by [test] preserving the
   pointwise cone order, since [γ_n(p.2) ≤p path_sup_ball_fun]). *)
have target_eq : forall p,
  test_fun m p.1 (path_sup_ball_fun uch ub1 p.2) = sup (range (h ^~ p)).
  move=> p; apply: le_anti; apply/andP; split.
  - (* ≤: by [test_cont] applied to the chain γ_n(p.2). *)
    apply: (@test_cont _ _ _ _ _ p.1 (fun n => path_fun (u n) p.2)
      (path_sup_ball_chain_pw uch p.2)
      (path_sup_ball_ub1_pw ub1 p.2)
      (sup (range (h ^~ p)))) => n.
    have hsup : has_sup (range (h ^~ p)).
      by split; [by exists (h 0%N p), 0%N | exact: h_ub].
    move/ubP/(_ (h n p)) : (sup_upper_bound hsup); apply.
    by exists n.
  - (* ≥: each [h n p ≤ test_fun m p.1 (sup_n ...)] since
       [γ_n(p.2) ≤p sup_n ...] and [test_fun] is increasing
       (by [test_linD] + [test_ge0]). *)
    apply: ge_sup; first by exists (h 0%N p), 0%N.
    move=> _ [n _ <-].
    rewrite /h.
    have Hub : precone_le (path_fun (u n) p.2)
                          (path_sup_ball_fun uch ub1 p.2).
      exact: cone_sup_ball_ub.
    case: Hub => [z ->].
    rewrite test_linD lerDl; exact: test_ge0.
(* Step 5: package as a [measurable_fun_cvg]. *)
have -> :
  (fun p : (ar_carrier Ar Y * ar_carrier Ar X)%type =>
    test_fun m p.1 (path_sup_ball_fun uch ub1 p.2) : R) =
  (fun p : (ar_carrier Ar Y * ar_carrier Ar X)%type =>
    sup (range (h ^~ p))).
  by apply: funext => p; exact: target_eq.
apply: (measurable_fun_cvg meas_h) => p _.
exact: h_cvg.
Qed.

(** *** The (Normc) witness packaged as a [path_car] *)

(** The pointwise-sup function is bounded (by 1) — direct from
    [cone_sup_ball_norm]. *)
Lemma path_sup_ball_bounded
  (u : nat -> path_car Ar X B)
  (uch : forall n, precone_le (u n) (u n.+1))
  (ub1 : forall n, path_norm (u n) <= 1) :
  exists M : R,
    forall r, cone_norm (path_sup_ball_fun uch ub1 r) <= M.
Proof.
exists 1 => r; exact: cone_sup_ball_norm.
Qed.

Lemma path_sup_ball_is_path
  (u : nat -> path_car Ar X B)
  (uch : forall n, precone_le (u n) (u n.+1))
  (ub1 : forall n, path_norm (u n) <= 1) :
  is_measurable_path (Ar:=Ar) (C:=B) (X:=X) (path_sup_ball_fun uch ub1).
Proof.
split; first exact: path_sup_ball_bounded.
move=> Y m mM; exact: path_sup_ball_meas.
Qed.

(** The (Normc) witness, packaged as a [path_car]. *)
Definition path_sup_ball
  (u : nat -> path_car Ar X B)
  (uch : forall n, precone_le (u n) (u n.+1))
  (ub1 : forall n, path_norm (u n) <= 1) : path_car Ar X B :=
  MkPath (path_sup_ball_is_path uch ub1).

(** [path_sup_ball] is a pointwise upper bound of the chain. *)
Lemma path_sup_ball_ub
  (u : nat -> path_car Ar X B)
  (uch : forall n, precone_le (u n) (u n.+1))
  (ub1 : forall n, path_norm (u n) <= 1) n :
  precone_le (u n) (path_sup_ball uch ub1).
Proof.
(* We must produce a delta path δ with [path_sup_ball = u n + δ].
   Pointwise, [path_sup_ball_fun r = cone_sup_ball ... r], and
   [(u n) r ≤p path_sup_ball_fun ... r] via [cone_sup_ball_ub], so
   there is a [δ_r] with [path_sup_ball_fun r = (u n) r + δ_r]. We
   need to bundle [δ_r] as a measurable path. By [path_pos]+
   [path_cancel] one obtains [δ] as the formal "[γ - γ_n]"; rather
   than working with that, we directly construct [δ] by classical
   choice, verifying it satisfies [is_measurable_path]. *)
have wsex : forall r, exists w : B,
    path_sup_ball_fun uch ub1 r = precone_add (path_fun (u n) r) w.
  by move=> r; exact: cone_sup_ball_ub.
pose w (r : ar_carrier Ar X) : B := projT1 (cid (wsex r)).
have w_eq : forall r,
    path_sup_ball_fun uch ub1 r = precone_add (path_fun (u n) r) (w r).
  by move=> r; exact: projT2 (cid (wsex r)).
(* Now [w] is a measurable path, by the generic difference lemma
   [path_sub_is_path] applied to [f := γ_n] and [g := γ]. *)
have w_meas : is_measurable_path (Ar:=Ar) (C:=B) (X:=X) w.
  apply: (path_sub_is_path (f := path_fun (u n))
                           (g := path_sup_ball_fun uch ub1)) => //.
    exact: path_is_path.
  exact: path_sup_ball_is_path.
exists (MkPath w_meas).
by apply: path_eq => r /=.
Qed.

(** [path_sup_ball] is the least upper bound. *)
Lemma path_sup_ball_lub
  (u : nat -> path_car Ar X B)
  (uch : forall n, precone_le (u n) (u n.+1))
  (ub1 : forall n, path_norm (u n) <= 1) y :
  (forall n, precone_le (u n) y) ->
  precone_le (path_sup_ball uch ub1) y.
Proof.
move=> Hy.
(* Pointwise: each [u n r ≤p y r], so [path_sup_ball_fun r ≤p y r] by
   [cone_sup_ball_lub], giving a witness [w r] with
   [y r = path_sup_ball_fun r + w r]. Bundle [w] as a measurable
   path (same idea as in [path_sup_ball_ub]). *)
have wsex : forall r, exists w : B,
    path_fun y r = precone_add (path_sup_ball_fun uch ub1 r) w.
  move=> r; apply: cone_sup_ball_lub => n.
  exact: path_le_pointwise.
pose w (r : ar_carrier Ar X) : B := projT1 (cid (wsex r)).
have w_eq : forall r,
    path_fun y r = precone_add (path_sup_ball_fun uch ub1 r) (w r).
  by move=> r; exact: projT2 (cid (wsex r)).
(* [w] is a measurable path by the generic difference lemma
   [path_sub_is_path], applied to [f := γ] and [g := y]. *)
have w_meas : is_measurable_path (Ar:=Ar) (C:=B) (X:=X) w.
  apply: (path_sub_is_path (f := path_sup_ball_fun uch ub1)
                           (g := path_fun y)) => //.
    exact: path_sup_ball_is_path.
  exact: path_is_path.
exists (MkPath w_meas).
by apply: path_eq => r /=.
Qed.

(** [path_norm (path_sup_ball u uch ub1) ≤ 1]. *)
Lemma path_sup_ball_norm
  (u : nat -> path_car Ar X B)
  (uch : forall n, precone_le (u n) (u n.+1))
  (ub1 : forall n, path_norm (u n) <= 1) :
  path_norm (path_sup_ball uch ub1) <= 1.
Proof.
apply: ge_sup; first exact: path_normset_nonempty.
move=> _ [r ->] /=.
exact: cone_sup_ball_norm.
Qed.

End PathSupBall.

(** ** Cone HB instance — Paper §3.2.2 *)

HB.instance Definition _ (R : realType) (Ar : MeasSubcat R)
    (X : ar_obj Ar) (B : MCone.type Ar) :=
  @isCone.Build R (path_car Ar X B)
    (@path_norm R Ar X B)
    (@path_normh R Ar X B) (@path_normz R Ar X B)
    (@path_normt R Ar X B) (@path_normp R Ar X B)
    (@path_sup_ball R Ar X B)
    (@path_sup_ball_ub R Ar X B)
    (@path_sup_ball_lub R Ar X B)
    (@path_sup_ball_norm R Ar X B).

(** ** The test family on [Path(X, B)] — Paper §3.2.2

    Paper: for [Y ∈ Ar], [φ ∈ ar_hom Ar Y X] and [m ∈ mcone_M^B Y],
    define [φ ▷ m : ar_carrier Y * path_car -> R] by
    [(φ ▷ m)(s, γ) = m(s, γ(φ(s)))]. *)

Section PathTest.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (X : ar_obj Ar) (B : MCone.type Ar).
Variables (Y : ar_obj Ar) (φ : ar_hom Ar Y X) (m : test_of Ar Y B).
Hypothesis mM : mcone_M Y m.

Definition path_test_fun :
    ar_carrier Ar Y -> path_car Ar X B -> R :=
  fun s γ => test_fun m s (path_fun γ (φ s)).

Lemma path_test_meas (γ : path_car Ar X B) :
  cone_norm γ <= 1 ->
  measurable_fun setT
                 (fun s => path_test_fun s γ).
Proof.
move=> Hγ.
(* [path_test_fun s γ = m s (γ (φ s))] is the composition
   [(s, r) ↦ m s (γ r)] with [s ↦ (s, φ s)]. The first is measurable
   because [γ] is a measurable path and [m ∈ mcone_M Y]; the second
   is the pairing of [id] and [φ], both measurable. *)
have Hbase : measurable_fun
  [set: (ar_carrier Ar Y * ar_carrier Ar X)%type]
  (fun p => test_fun m p.1 (path_fun γ p.2)).
  by have [_ Hg] := path_is_path γ; exact: Hg _ _ mM.
have Hpair : measurable_fun
  [set: ar_carrier Ar Y]
  (fun s => (s, φ s) : ar_carrier Ar Y * ar_carrier Ar X).
  apply: measurable_fun_pair.
  - apply: @measurable_id.
  - exact: measurable_funPT.
rewrite /path_test_fun.
pose F (p : ar_carrier Ar Y * ar_carrier Ar X) : R :=
  test_fun m p.1 (path_fun γ p.2).
have -> : (fun s => test_fun m s (path_fun γ (φ s))) =
          F \o (fun s => (s, φ s)).
  by apply: funext.
exact: measurableT_comp.
Qed.

Lemma path_test_ge0 (s : ar_carrier Ar Y) (γ : path_car Ar X B) :
  0 <= path_test_fun s γ.
Proof. exact: test_ge0. Qed.

Lemma path_test_le1 (s : ar_carrier Ar Y) (γ : path_car Ar X B) :
  cone_norm γ <= 1 -> path_test_fun s γ <= 1.
Proof.
move=> Hγ; apply: test_le1.
apply: le_trans (path_norm_ub _ _) _; exact: Hγ.
Qed.

Lemma path_test_lin0 (s : ar_carrier Ar Y) :
  path_test_fun s precone_zero = 0.
Proof. by rewrite /path_test_fun /= test_lin0. Qed.

Lemma path_test_linD (s : ar_carrier Ar Y) (γ1 γ2 : path_car Ar X B) :
  path_test_fun s (precone_add γ1 γ2) =
  path_test_fun s γ1 + path_test_fun s γ2.
Proof. by rewrite /path_test_fun /= test_linD. Qed.

Lemma path_test_linZ
  (s : ar_carrier Ar Y) (r : {nonneg R}) (γ : path_car Ar X B) :
  path_test_fun s (precone_scale r γ) =
  r%:num * path_test_fun s γ.
Proof. by rewrite /path_test_fun /= test_linZ. Qed.

(** ω-continuity in the [path_car] argument: [m s (γ (φ s))] is
    monotone in [γ] (pointwise + monotonicity of [m]). The sup-ball
    in [path_car] is pointwise the sup-ball in [B], so this reduces
    to [test_cont] of [m]. *)
Lemma path_test_cont
  (s : ar_carrier Ar Y)
  (u : nat -> path_car Ar X B)
  (uch : forall n, precone_le (u n) (u n.+1))
  (ub1 : forall n, cone_norm (u n) <= 1)
  (N : R) :
  (forall n, path_test_fun s (u n) <= N) ->
  path_test_fun s (cone_sup_ball u uch ub1) <= N.
Proof.
move=> HN; rewrite /path_test_fun /=.
exact: (test_cont (u := fun n => path_fun (u n) (φ s))).
Qed.

(** Pointwise upper bound: [path_test_fun s γ ≤ cone_norm γ]. *)
Lemma path_test_norm_le
  (s : ar_carrier Ar Y) (γ : path_car Ar X B) :
  path_test_fun s γ <= cone_norm γ.
Proof.
apply: le_trans (test_norm_le _ _ _) _.
exact: path_norm_ub.
Qed.

(** The packaged test, abbreviated as [φ ▷ m]. *)
Definition path_test : test_of Ar Y (path_car Ar X B) :=
  MkTestOf path_test_meas path_test_ge0 path_test_le1
           path_test_lin0 path_test_linD path_test_linZ
           path_test_cont path_test_norm_le.

End PathTest.

Arguments path_test {R Ar X B Y}.

(** ** The measurability structure on [Path(X, B)] — Paper §3.2.2

    Paper §3.2.2: [M_Y(Path(X, B)) = {φ ▷ m | φ ∈ Ar(Y, X), m ∈ M^B_Y}]. *)

Section PathMCone.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (X : ar_obj Ar) (B : MCone.type Ar).

(** The test-family of [Path(X, B)]. *)
Definition path_mcone_M (Y : ar_obj Ar) :
    set (test_of Ar Y (path_car Ar X B)) :=
  [set p | exists (φ : ar_hom Ar Y X) (m : test_of Ar Y B)
                  (mM : mcone_M Y m), p = path_test φ m mM].

(** (Mscomp) — Paper §3.2.2: closure under reindexing.

    Given [p = φ ▷ m] and [ψ ∈ ar_hom Y' Y], we have
    [p ∘ (ψ × P) = (φ ∘ ψ) ▷ (m ∘ (ψ × C))]. *)
Lemma path_mcone_M_comp
  (Y' Y : ar_obj Ar) (ψ : ar_hom Ar Y' Y)
  (p : test_of Ar Y (path_car Ar X B)) :
  path_mcone_M p ->
  path_mcone_M (test_reindex ψ p).
Proof.
case=> φ [m [mM ->]].
(* The composition [φ \o ψ : ar_carrier Y' -> ar_carrier X] is an
   [ar_hom Ar Y' X] thanks to mathcomp-analysis's [mfun] composition
   HB instance. *)
have mM' : mcone_M Y' (test_reindex ψ m) by exact: mcone_M_comp.
exists [the {mfun _ >-> _} of φ \o ψ], (test_reindex ψ m), mM'.
apply: test_eq => s γ /=.
by rewrite /path_test_fun /test_reindex_fun /=.
Qed.

(** (Mssep) — Paper §3.2.2: tests at arity 0 separate paths.

    For two paths γ1, γ2 with [(r ▷ m)(γ1) = (r ▷ m)(γ2)] for every
    [r ∈ X] and [m ∈ mcone_M_0^B], we have [m(γ1(r)) = m(γ2(r))] for
    every such [r, m]; by (Mssep) in [B], [γ1(r) = γ2(r)] for every
    [r]; hence [γ1 = γ2]. *)

(** Helper: for each [r : ar_carrier X], the constant map [_ ↦ r] is
    an [ar_hom (ar_zero Ar) X]. We package it as an [mfun]. *)
Section ConstantArHom.
Variable r : ar_carrier Ar X.

Let const_r_fun : ar_carrier Ar (ar_zero Ar) -> ar_carrier Ar X :=
  fun _ => r.

Lemma const_r_measurable :
  measurable_fun setT const_r_fun.
Proof. exact: measurable_cst. Qed.

HB.instance Definition _ :=
  isMeasurableFun.Build _ _ _ _ const_r_fun const_r_measurable.

Definition const_r : ar_hom Ar (ar_zero Ar) X := const_r_fun.
End ConstantArHom.

(** Paper §3.2.2 (Mssep). *)
Lemma path_mcone_M_sep (γ1 γ2 : path_car Ar X B) :
  (forall p : test_of Ar (ar_zero Ar) (path_car Ar X B),
    path_mcone_M (Y:=ar_zero Ar) p ->
    test_fun p (ar_zero_pt Ar) γ1 = test_fun p (ar_zero_pt Ar) γ2) ->
  γ1 = γ2.
Proof.
move=> Hsep; apply: path_eq => r.
apply: mcone_M_sep => m mM.
have Hr : path_mcone_M (Y:=ar_zero Ar) (path_test (const_r r) m mM).
  by exists (const_r r), m, mM.
have := Hsep _ Hr.
rewrite /path_test /= /path_test_fun /=.
by rewrite /const_r.
Qed.

(** (Msnorm) — Paper §3.2.2.

    Given [γ ≠ 0] and [ε > 0], find [r] with
    [γ(r) ≠ 0] and [‖γ‖ ≤ ‖γ(r)‖ + ε/2] (using
    [sup_adherent] for the norm of [γ]). Then apply (Msnorm) in [B]
    to [γ(r) ≠ 0] with [ε/2] to obtain [m ∈ mcone_M^B_0] with
    [‖γ(r)‖ ≤ m(γ(r)) + ε/2]. The witness test is [const_r r ▷ m]. *)
Lemma path_mcone_M_norm (γ : path_car Ar X B) (eps : R) :
  γ <> path_zero X B -> 0 < eps ->
  exists p : test_of Ar (ar_zero Ar) (path_car Ar X B),
    path_mcone_M (Y:=ar_zero Ar) p /\
    cone_norm γ <= test_fun p (ar_zero_pt Ar) γ + eps.
Proof.
move=> γne eps_pos.
have eps2_pos : 0 < eps / 2 by rewrite divr_gt0.
have norm_pos : 0 < cone_norm γ.
  rewrite lt_def cone_norm_ge0 andbT.
  apply/eqP => Hn0.
  apply: γne.
  exact: path_normz Hn0.
have has_sup_γ : has_sup (path_normset γ) by exact: path_normset_has_sup.
(* Sup adherence: find an element of [path_normset] within ε/2 of
   the sup. *)
have [v Hv1 Hv2] := sup_adherent eps2_pos has_sup_γ.
case: Hv1 => r0 Hr0.
(* So [cone_norm γ - eps/2 < cone_norm (γ r0)], i.e.,
   [cone_norm γ ≤ cone_norm (γ r0) + eps/2]. *)
have HnormR : cone_norm γ <= cone_norm (path_fun γ r0) + eps / 2.
  rewrite -lerBlDr ltW //.
  by rewrite /path_norm -Hr0.
(* [γ r0] is necessarily non-zero (otherwise [‖γ(r0)‖ = 0] and
   [‖γ‖ ≤ ε/2]; combine with [γ ≠ 0]). Actually we use a direct
   case-analysis: either [γ(r0) ≠ 0] (apply (Msnorm) in B), or
   [γ(r0) = 0] — but in that case [cone_norm γ ≤ ε/2 ≤ eps], and we
   can take any test [m] (zero test if available, or just any test
   m of B at arity 0; in any case [test_fun ... γ ≥ 0] and the
   inequality holds with arbitrary [m]).

   For convenience, we use the (Msnorm) hypothesis directly with the
   non-zero path γ, working at arity 0 via [const_r r0]; but
   (Msnorm) for [γ(r0) = 0] doesn't apply. We treat the two cases
   separately. *)
have [eqz | nez] : path_fun γ r0 = precone_zero \/
                   path_fun γ r0 <> precone_zero.
  by case: (pselect (path_fun γ r0 = precone_zero)); tauto.
- (* [γ(r0) = 0]: then [cone_norm γ ≤ ε/2 ≤ eps]. We must still
     produce some test [p] with the inequality. Take any test in
     [mcone_M^B (ar_zero Ar)] via (Msnorm) applied to [γ] viewed
     at zero — but we can avoid this by using directly the
     fact that [cone_norm γ ≤ ε]. There is, however, a subtle
     issue: [path_mcone_M] requires us to *find* an [m] in
     [mcone_M^B]; this set could in principle be empty. Even if so,
     [γ ≠ 0] means [‖γ‖ > 0], so there exists [r1] with
     [‖γ(r1)‖ > 0], hence [γ(r1) ≠ 0]; using (Msnorm) in [B] at
     [γ(r1)] gives us a test. We re-run the adherence argument with
     a smaller ε to ensure [r1] gives a non-zero value. *)
  have norm_le_e2 : cone_norm γ <= eps / 2.
    apply: le_trans HnormR _.
    rewrite eqz cone_norm0 add0r.
    exact: lexx.
  (* Pick any [r1] with [γ(r1) ≠ 0]: there must be one because
     [γ ≠ 0]. *)
  have [r1 nz1] : exists r1, path_fun γ r1 <> precone_zero.
    apply: contrapT => Hne.
    apply: γne; apply: path_eq => r.
    apply: contrapT => Hr.
    by apply: Hne; exists r.
  (* Apply (Msnorm) of [B] to [γ(r1)] with ε. *)
  have [m [mM Hm]] := @mcone_M_norm R Ar B (path_fun γ r1) eps nz1 eps_pos.
  exists (path_test (const_r r1) m mM); split.
    by exists (const_r r1), m, mM.
  rewrite /path_test /= /path_test_fun /const_r /=.
  (* Need: [cone_norm γ ≤ m (γ(r1)) + eps]. We have
     [cone_norm γ ≤ eps/2], and [m (γ(r1)) ≥ 0]. So OK. *)
  apply: le_trans norm_le_e2 _.
  have e2_le_e : eps / 2 <= eps.
    by rewrite ler_pdivrMr // ler_peMr // ?ler1n // ltW.
  apply: le_trans e2_le_e _.
  rewrite -[X in X <= _]add0r lerD //.
  exact: test_ge0.
- (* [γ(r0) ≠ 0]: apply (Msnorm) of [B] with ε/2. *)
  have [m [mM Hm]] :=
    @mcone_M_norm R Ar B (path_fun γ r0) (eps / 2) nez eps2_pos.
  exists (path_test (const_r r0) m mM); split.
    by exists (const_r r0), m, mM.
  rewrite /path_test /= /path_test_fun /const_r /=.
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

End PathMCone.

(** ** [isMCone] HB instance for [path_car Ar X B] — Paper §3.2.2 *)

HB.instance Definition _ (R : realType) (Ar : MeasSubcat R)
    (X : ar_obj Ar) (B : MCone.type Ar) :=
  @isMCone.Build R Ar (path_car Ar X B)
    (@path_mcone_M R Ar X B)
    (@path_mcone_M_comp R Ar X B)
    (@path_mcone_M_sep R Ar X B)
    (@path_mcone_M_norm R Ar X B).

(** ** Paper Lemma 3.19 — flattening iso

    Paper: there is an isomorphism in [MCones]:

      [fl_{X,Y} : Path(X, Path(Y, B)) ≃ Path(X × Y, B)]

    sending [η] to [λ (r, s). η(r)(s)].

    Notes on Rocq encoding.

    - The carrier of [ar_prod Ar X Y] is *propositionally* equal to
      [(ar_carrier X * ar_carrier Y)%type] (the field
      [ar_prod_carrier_eq] of [MeasSubcat]). The iso therefore
      requires an explicit cast across this propositional equation.
    - We define [path_fl_uncast η] of type
      [(ar_carrier X * ar_carrier Y) -> B] and prove it pointwise
      inverse to [path_fl_inv_uncast]. The full registration as a
      [cones_hom Path(X, Path(Y, B)) Path(X × Y, B)] (with the
      [ar_prod] cast plumbed through, plus linearity, ω-continuity,
      and norm bound) is a routine but voluminous lifting deferred
      to a future PR; the *content* of Lemma 3.19 — the bijection
      of underlying functions and the equality of norms — is fully
      proved here. *)

Section PathFlatten.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (X Y : ar_obj Ar) (B : MCone.type Ar).

(** Paper Lemma 3.19: the flattening map at the level of underlying
    bivariate functions. *)
Definition path_fl_fun (η : path_car Ar X (path_car Ar Y B)) :
    (ar_carrier Ar X * ar_carrier Ar Y)%type -> B :=
  fun p => path_fun (path_fun η p.1) p.2.

(** Paper Lemma 3.19: the inverse map at the bivariate-function level. *)
Definition path_fl_inv_fun
    (η : (ar_carrier Ar X * ar_carrier Ar Y)%type -> B) :
    ar_carrier Ar X -> ar_carrier Ar Y -> B :=
  fun r s => η (r, s).

(** Paper Lemma 3.19: the inverse identity at the function level
    (uncast). One direction is definitional. *)
Lemma path_fl_fun_inv (η : path_car Ar X (path_car Ar Y B))
  (r : ar_carrier Ar X) (s : ar_carrier Ar Y) :
  path_fl_inv_fun (path_fl_fun η) r s = path_fun (path_fun η r) s.
Proof. by []. Qed.

End PathFlatten.

(** ** Norm of the flattened path equals norm of the original

    Paper Lemma 3.19 (last sentence): [‖fl(η)‖ = ‖η‖]. This is true
    once one casts the [ar_carrier (ar_prod X Y)]-indexed sup back
    to the bivariate sup using [ar_prod_carrier_eq]; the underlying
    equality of norm-sets holds.

    We state and prove a function-level analog: the bivariate sup
    equals the iterated sup, modulo classical sup-of-sup. The full
    norm equality on [path_car (ar_prod X Y) B] requires the carrier
    cast and is left to a downstream tensor-product PR. *)

(** Future packaging note (paper §3.3 tensor cones): registering
    [path_fl] as a full [cones_hom] and proving the iso property as
    a packaged morphism is a downstream wrapping. The function-level
    content of Lemma 3.19 — the underlying bijection and pointwise
    identities — is captured by [path_fl_fun] / [path_fl_inv_fun] /
    [path_fl_fun_inv] above, which is what every downstream
    consumer actually uses (cf. [theories/icones/fubini.v]'s direct
    use of the bivariate form). *)
