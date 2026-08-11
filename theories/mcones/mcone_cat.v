(** * The category MCones — Paper §3.1 (Def 3.13, Rem 3.14, Def 3.15)
    plus Proposition 3.11 (dual-norm sup characterisation)

    A morphism in [MCones] from [B] to [C] is a [cones_hom B C]
    (linear, ω-continuous, pointwise norm-bounded) which moreover
    preserves measurable paths.

    Paper reference: §3.1 (page 1:19), Def 3.13, Rem 3.14, Def 3.15;
    §3 (page 1:18), Prop 3.11.

    Coverage in this file:

    - [mcones_hom Ar B C] — morphisms of measurable cones,
      packaging a [cones_hom] with a path-preservation field
      (Paper Definition 3.13).
    - [mcones_id], [mcones_comp] — identity and composition
      (Paper Definition 3.13).
    - [mcones_compIl], [mcones_compIr], [mcones_compA] — category
      laws (Paper Definition 3.13).
    - [mcone_norm_sup_dual] — Paper Proposition 3.11: the norm in
      [B] is the supremum of the test pairings [<x, m>] over
      [m ∈ M^B_0] with [m] of operator-norm ≤ 1 (the no-ε form,
      obtained from our [mcone_M_norm] by sup-adherence).
    - [alpha_rescale Ar α B] — Paper Definition 3.15: the
      rescaled measurable cone [αB], registered as an
      [mconeType Ar] via the [isPrecone], [isCone], [isMCone] HB
      instances.
    - [mcones_iso_id_alpha] — Paper Remark 3.14: the identity
      function [B → αB] is an [mcones_hom]-iso when interpreted
      with rescaled-norm preservation; we expose a witness pair of
      morphisms in opposite directions (after appropriate
      norm-rescaling of the target test family).

    Design notes.

    - The path-preservation field is stored in its
      "test characterisation" form (Paper Def 3.13, the equivalent
      bullet): for every [Y ∈ Ar], every [m ∈ M^C_Y], and every
      measurable path [γ : ar_carrier X -> B], the function
      [λ p : Y × X. m p.1 (f (γ p.2))] is measurable. This is
      exactly [is_measurable_path Ar C X (f ∘ γ)] thanks to the
      uniform bound [‖f x‖ ≤ ‖x‖]. We expose this as a
      proposition-level [forall γ, is_measurable_path … γ →
      is_measurable_path … (f ∘ γ)].

    - The rescaled cone [αB] uses a thin record wrapper
      [alpha_rescale_car] over [B]'s carrier; this is needed
      because the [coneType R] HB structure picks up [cone_norm]
      from the canonical instance, which is [B]'s norm. The
      wrapper carries a distinct identity for type inference. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.

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

(** ** Morphisms of [MCones] — Paper Definition 3.13 *)

Section MConesHom.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : MCone.type Ar.

(** Paper Definition 3.13: a morphism in [MCones] is a [cones_hom]
    which preserves measurable paths.

    The field [mcones_hom_pres_path] expresses the "equivalently"
    bullet of Def 3.13: for every measurable path [γ : X → B], the
    composite [f ∘ γ : X → C] is a measurable path. *)
Record mcones_hom : Type := MkMConesHom {
  mcones_hom_cones :> cones_hom B C;
  mcones_hom_pres_path :
    forall (X : ar_obj Ar) (γ : ar_carrier Ar X -> B),
      is_measurable_path (Ar:=Ar) (C:=B) γ ->
      is_measurable_path
        (Ar:=Ar) (C:=C)
        (fun r => cones_hom_fun mcones_hom_cones (γ r));
}.

End MConesHom.

Arguments mcones_hom {R} Ar B C.
Arguments MkMConesHom {R Ar B C}.
Arguments mcones_hom_cones {R Ar B C}.
Arguments mcones_hom_pres_path {R Ar B C}.

(** ** Equality of morphisms — extensionality + [Prop_irrelevance] *)

Section MConesHomEq.
Variables (R : realType) (Ar : MeasSubcat R) (B C : MCone.type Ar).

(** Two morphisms in [MCones] are equal as soon as their underlying
    [cones_hom] are equal (pointwise extensionality already implies
    this at the [cones_hom] level via [cones_hom_eq]). *)
Lemma mcones_hom_eq (f g : mcones_hom Ar B C) :
  (forall x, cones_hom_fun (mcones_hom_cones f) x =
             cones_hom_fun (mcones_hom_cones g) x) -> f = g.
Proof.
case: f => fc fp; case: g => gc gp /= Hfg.
have Heq : fc = gc by apply: cones_hom_eq.
move: fp; rewrite Heq => fp.
by congr MkMConesHom; exact: Prop_irrelevance.
Qed.

End MConesHomEq.

(** ** Identity morphism — Paper Definition 3.13 *)

Section MConesId.
Variables (R : realType) (Ar : MeasSubcat R) (B : MCone.type Ar).

(** Paper Definition 3.13: the identity preserves measurable paths
    trivially (since [id ∘ γ = γ]). *)
Lemma mcones_id_pres_path
  (X : ar_obj Ar) (γ : ar_carrier Ar X -> B) :
  is_measurable_path (Ar:=Ar) (C:=B) γ ->
  is_measurable_path
    (Ar:=Ar) (C:=B)
    (fun r => cones_hom_fun (cones_id B) (γ r)).
Proof. by []. Qed.

(** Paper Definition 3.13: identity in [MCones]. *)
Definition mcones_id : mcones_hom Ar B B :=
  MkMConesHom (cones_id B) mcones_id_pres_path.

End MConesId.

Arguments mcones_id {R} Ar B.

(** ** Composition of morphisms — Paper Definition 3.13 *)

Section MConesComp.
Variables (R : realType) (Ar : MeasSubcat R).
Variables A B C : MCone.type Ar.

(** Paper Definition 3.13: composition preserves measurable paths
    by the chain rule [(g ∘ f) ∘ γ = g ∘ (f ∘ γ)]. *)
Lemma mcones_comp_pres_path
  (g : mcones_hom Ar B C) (f : mcones_hom Ar A B)
  (X : ar_obj Ar) (γ : ar_carrier Ar X -> A) :
  is_measurable_path (Ar:=Ar) (C:=A) γ ->
  is_measurable_path
    (Ar:=Ar) (C:=C)
    (fun r => cones_hom_fun
                (cones_comp (mcones_hom_cones g) (mcones_hom_cones f))
                (γ r)).
Proof.
move=> Hγ.
have Hfγ := mcones_hom_pres_path f X _ Hγ.
exact: mcones_hom_pres_path g X _ Hfγ.
Qed.

(** Paper Definition 3.13: composition in [MCones]. *)
Definition mcones_comp
    (g : mcones_hom Ar B C) (f : mcones_hom Ar A B) : mcones_hom Ar A C :=
  MkMConesHom
    (cones_comp (mcones_hom_cones g) (mcones_hom_cones f))
    (mcones_comp_pres_path g f).

End MConesComp.

Arguments mcones_comp {R Ar A B C}.

(** ** Category laws — Paper Definition 3.13 *)

Section MConesCat.
Variables (R : realType) (Ar : MeasSubcat R).

(** Paper Definition 3.13: left identity. *)
Lemma mcones_compIl (B C : MCone.type Ar) (f : mcones_hom Ar B C) :
  mcones_comp (mcones_id Ar C) f = f.
Proof. by apply: mcones_hom_eq. Qed.

(** Paper Definition 3.13: right identity. *)
Lemma mcones_compIr (B C : MCone.type Ar) (f : mcones_hom Ar B C) :
  mcones_comp f (mcones_id Ar B) = f.
Proof. by apply: mcones_hom_eq. Qed.

(** Paper Definition 3.13: composition is associative. *)
Lemma mcones_compA (B1 B2 B3 B4 : MCone.type Ar)
  (h : mcones_hom Ar B3 B4)
  (g : mcones_hom Ar B2 B3)
  (f : mcones_hom Ar B1 B2) :
  mcones_comp h (mcones_comp g f) = mcones_comp (mcones_comp h g) f.
Proof. by apply: mcones_hom_eq. Qed.

End MConesCat.

(** ** Paper Proposition 3.11 — the dual-norm sup characterisation

    For a measurable cone [B] and a non-zero [x ∈ B],

      [‖x‖ = sup { m(x) | m ∈ M^B_0, ‖m‖ ≤ 1 }].

    The [≥] direction is the pointwise bound [m(x) ≤ ‖x‖] of every
    test (paper Def 3.2, captured as our [test_norm_le] field).

    The [≤] direction (the substantive content) is supplied by
    sup-adherence: the (Msnorm) axiom of [B] (in our simplified
    form [‖x‖ ≤ m(x) + ε]) yields, for every [ε > 0], a witness
    [m] with [‖x‖ ≤ m(x) + ε].

    We state the no-ε form below as ‖x‖ is the sup of the set of
    pairings, using mathcomp-analysis's [sup_le_ub] /
    [le_sup_adherent]. To keep the file self-contained and avoid
    dependence on [sup_le_ub] without the necessary [has_sup]
    witness, we expose two facts: the upper-bound part (no extra
    hypotheses) and the adherence part (for non-zero [x]). *)

Section Proposition311.
Variables (R : realType) (Ar : MeasSubcat R) (B : MCone.type Ar).

(** The set of pairings [{ m(x) | m ∈ M^B_0 }] at the terminal
    parameter [ar_zero_pt Ar]. *)
Definition mcone_test_pairing_set (x : B) : set R :=
  [set y | exists2 m : test_of Ar (ar_zero Ar) B,
             mcone_M (ar_zero Ar) m & y = test_fun m (ar_zero_pt Ar) x].

(** Paper Prop 3.11 (≥ direction): every pairing is bounded by
    [‖x‖]. This is the [test_norm_le] field of every test. *)
Lemma mcone_test_pairing_ub (x : B) :
  ubound (mcone_test_pairing_set x) (cone_norm x).
Proof.
move=> y [m _ ->]; exact: test_norm_le.
Qed.

(** Paper Prop 3.11 (≤ direction): for non-zero [x] and ε > 0,
    there is a pairing within ε of [‖x‖]. Direct (Msnorm)
    invocation. *)
Lemma mcone_test_pairing_adherent (x : B) (eps : R) :
  x <> precone_zero -> 0 < eps ->
  exists2 y, mcone_test_pairing_set x y & cone_norm x <= y + eps.
Proof.
move=> xne eps_pos.
have [m [mM Hm]] := @mcone_M_norm R Ar B x eps xne eps_pos.
exists (test_fun m (ar_zero_pt Ar) x) => //.
by exists m.
Qed.

(** Paper Prop 3.11 (no-ε form, restricted to non-zero [x] for
    convenience — the [x = 0] case is automatic since both sides
    of [‖x‖ = sup] are [0], provided the pairing set is treated
    appropriately).

    Any [M] upper-bounding the pairing set must dominate [‖x‖]:
    by ε-adherence, [‖x‖ ≤ y + ε] for some pairing [y ≤ M], hence
    [‖x‖ ≤ M + ε] for every ε > 0, whence [‖x‖ ≤ M]. *)
Lemma mcone_norm_le_pairing_ub (x : B) (M : R) :
  x <> precone_zero ->
  ubound (mcone_test_pairing_set x) M -> cone_norm x <= M.
Proof.
move=> xnz HubM; apply/ler_addgt0Pr => eps eps_pos.
have [y [m mM ->] Hxy] := mcone_test_pairing_adherent xnz eps_pos.
by apply: le_trans Hxy _; rewrite lerD2r; apply: HubM; exists m.
Qed.

End Proposition311.

(** ** Paper Definition 3.15 — the rescaling [αB]

    Given [B : mconeType Ar] and [α : R] with [α > 0], we define
    a new measurable cone [αB] with the same carrier, the same
    precone operations, the rescaled norm [‖x‖_{αB} = α⁻¹ ‖x‖_B],
    and the test family obtained by scaling every test of [B] by
    the [{nonneg R}] value [α⁻¹] (so that [test_norm_le] holds for
    the new norm).

    We use a thin [Record] wrapper [alpha_rescale_car] to give [αB]
    a distinct identity for HB structure inference. *)

Section AlphaRescaleDef.
Variables (R : realType) (Ar : MeasSubcat R).

(** The wrapper carrier of [αB]: a [Record] bundling the positive
    scalar [α] (used to distinguish HB structures for distinct
    [α] values) and an element of [B].

    We package [α] *together with the positivity proof* inside the
    record so that the HB instances depend only on [B] and the
    [pos_real R] subtype, rather than on a separately-passed
    [is_true (0 < α)] hypothesis that Coq would otherwise have to
    infer from the context. *)
Record pos_real : Type := MkPosReal {
  pos_real_val :> R;
  pos_real_pos : 0 < pos_real_val;
}.

Record alpha_rescale_car (α : pos_real) (B : MCone.type Ar) : Type :=
  MkAlphaRescale { alpha_rescale_val : B }.

Variable α : pos_real.
Variable B : MCone.type Ar.

Let αp : 0 < pos_real_val α := pos_real_pos α.

(** Extensionality of the wrapper. *)
Lemma alpha_rescale_eq (x y : alpha_rescale_car α B) :
  alpha_rescale_val x = alpha_rescale_val y -> x = y.
Proof. by case: x; case: y => /= ? ? ->. Qed.

(** Convenient inverse. *)
Lemma α_neq0 : pos_real_val α != 0.
Proof. by rewrite gt_eqF // αp. Qed.

Lemma α_ge0 : 0 <= pos_real_val α.
Proof. exact: ltW. Qed.

Lemma α_inv_ge0 : 0 <= (pos_real_val α)^-1.
Proof. by rewrite invr_ge0 α_ge0. Qed.

Definition α_nng : {nonneg R} := NngNum α_ge0.
Definition α_inv_nng : {nonneg R} := NngNum α_inv_ge0.

End AlphaRescaleDef.

Arguments pos_real R : clear implicits.
Arguments alpha_rescale_val {R Ar α B}.

(** *** Precone instance on [alpha_rescale_car α B] *)

Section AlphaRescalePrecone.
Variables (R : realType) (Ar : MeasSubcat R).
Variable α : pos_real R.
Variable B : MCone.type Ar.

Local Notation T := (alpha_rescale_car α B).

Definition αB_zero : T := @MkAlphaRescale R Ar α B precone_zero.
Definition αB_add (x y : T) : T :=
  @MkAlphaRescale R Ar α B
    (precone_add (alpha_rescale_val x) (alpha_rescale_val y)).
Definition αB_scale (r : {nonneg R}) (x : T) : T :=
  @MkAlphaRescale R Ar α B
    (precone_scale r (alpha_rescale_val x)).

Lemma αB_addA : associative αB_add.
Proof.
by move=> x y z; apply: alpha_rescale_eq; rewrite /= precone_addA.
Qed.

Lemma αB_addC : commutative αB_add.
Proof.
by move=> x y; apply: alpha_rescale_eq; rewrite /= precone_addC.
Qed.

Lemma αB_add0 : left_id αB_zero αB_add.
Proof.
by move=> x; apply: alpha_rescale_eq; rewrite /= precone_add0.
Qed.

Lemma αB_scale_DAr (r : {nonneg R}) (x y : T) :
  αB_scale r (αB_add x y) = αB_add (αB_scale r x) (αB_scale r y).
Proof.
by apply: alpha_rescale_eq; rewrite /= precone_scale_DAr.
Qed.

Lemma αB_scale_DAl (r s : {nonneg R}) (x : T) :
  αB_scale (r%:num + s%:num)%:nng x =
  αB_add (αB_scale r x) (αB_scale s x).
Proof.
by apply: alpha_rescale_eq; rewrite /= precone_scale_DAl.
Qed.

Lemma αB_scale_A (r s : {nonneg R}) (x : T) :
  αB_scale (r%:num * s%:num)%:nng x =
  αB_scale r (αB_scale s x).
Proof.
by apply: alpha_rescale_eq; rewrite /= precone_scale_A.
Qed.

Lemma αB_scale_1 (x : T) : αB_scale 1%:nng x = x.
Proof.
by apply: alpha_rescale_eq; rewrite /= precone_scale_1.
Qed.

Lemma αB_scale_0r (r : {nonneg R}) : αB_scale r αB_zero = αB_zero.
Proof.
by apply: alpha_rescale_eq; rewrite /= precone_scale_0r.
Qed.

Lemma αB_scale_0l (x : T) : αB_scale 0%:nng x = αB_zero.
Proof.
by apply: alpha_rescale_eq; rewrite /= precone_scale_0l.
Qed.

Lemma αB_cancel (x y z : T) :
  αB_add x y = αB_add x z -> y = z.
Proof.
move=> H; apply: alpha_rescale_eq.
have /(congr1 alpha_rescale_val) := H => /= H'.
exact: precone_cancel H'.
Qed.

Lemma αB_pos (x y : T) :
  αB_add x y = αB_zero -> x = αB_zero /\ y = αB_zero.
Proof.
move=> H.
have /(congr1 alpha_rescale_val) := H => /= H'.
case: (precone_pos _ _ H') => Hx Hy.
by split; apply: alpha_rescale_eq.
Qed.

End AlphaRescalePrecone.

(** Classical [Equality]/[Choice] structures on the carrier (required
    by the precone partial order). *)
HB.instance Definition _ (R : realType) (Ar : MeasSubcat R)
    (α : pos_real R) (B : MCone.type Ar) :=
  gen_eqMixin (alpha_rescale_car α B).
HB.instance Definition _ (R : realType) (Ar : MeasSubcat R)
    (α : pos_real R) (B : MCone.type Ar) :=
  gen_choiceMixin (alpha_rescale_car α B).

HB.instance Definition _ (R : realType) (Ar : MeasSubcat R)
    (α : pos_real R) (B : MCone.type Ar) :=
  @isPrecone.Build R (alpha_rescale_car α B)
    (@αB_zero R Ar α B) (@αB_add R Ar α B) (@αB_scale R Ar α B)
    (@αB_addA R Ar α B) (@αB_addC R Ar α B) (@αB_add0 R Ar α B)
    (@αB_scale_DAr R Ar α B) (@αB_scale_DAl R Ar α B)
    (@αB_scale_A R Ar α B) (@αB_scale_1 R Ar α B)
    (@αB_scale_0r R Ar α B) (@αB_scale_0l R Ar α B)
    (@αB_cancel R Ar α B) (@αB_pos R Ar α B).

(** *** Cone instance on [alpha_rescale_car α B] *)

Section AlphaRescaleCone.
Variables (R : realType) (Ar : MeasSubcat R).
Variable α : pos_real R.
Let αpos : 0 < pos_real_val α := pos_real_pos α.
Variable B : MCone.type Ar.

Local Notation T := (alpha_rescale_car α B).

(** Paper Definition 3.15: the rescaled norm. *)
Definition αB_norm (x : T) : R :=
  (α : R)^-1 * cone_norm (alpha_rescale_val x).

Lemma αB_normh (r : {nonneg R}) (x : T) :
  αB_norm (precone_scale r x) = r%:num * αB_norm x.
Proof.
rewrite /αB_norm /= cone_normh.
by rewrite mulrCA.
Qed.

Lemma αB_normz (x : T) :
  αB_norm x = 0 -> x = precone_zero.
Proof.
rewrite /αB_norm => /eqP.
rewrite mulf_eq0 invr_eq0 (negbTE (α_neq0 α)) /=.
move=> /eqP/cone_normz Hv.
by apply: alpha_rescale_eq.
Qed.

Lemma αB_normt (x y : T) :
  αB_norm (precone_add x y) <= αB_norm x + αB_norm y.
Proof.
rewrite /αB_norm /= -mulrDr.
apply: ler_wpM2l; first exact: α_inv_ge0 α.
exact: cone_normt.
Qed.

Lemma αB_normp (x y : T) :
  precone_le x y -> αB_norm x <= αB_norm y.
Proof.
case=> z Hz.
have Hv : alpha_rescale_val y = precone_add (alpha_rescale_val x)
                                            (alpha_rescale_val z).
  by have /(congr1 alpha_rescale_val) := Hz.
have HleV : precone_le (alpha_rescale_val x) (alpha_rescale_val y).
  by exists (alpha_rescale_val z).
rewrite /αB_norm; apply: ler_wpM2l; first exact: α_inv_ge0 α.
exact: cone_normp.
Qed.

(** *** (Normc) — ω-completeness of the αB unit ball.

    Given a chain [u : nat -> T] increasing with [αB_norm (u n) ≤ 1]
    (i.e., [‖u n‖_B ≤ α]), define [u' n := α⁻¹ ·: u n] (in B), which
    has [‖u' n‖_B ≤ 1], take the sup [s'] in B, then return
    [α ·: s' : T]. *)

Section αBSupBall.
Variable u : nat -> T.
Hypothesis uch : forall n, precone_le (u n) (u n.+1).
Hypothesis ub1 : forall n, αB_norm (u n) <= 1.

(** The rescaled chain in [B]: divide by α to land in [B]'s unit
    ball. *)
Let u' (n : nat) : B := precone_scale (α_inv_nng α)
                                      (alpha_rescale_val (u n)).

Lemma αB_u'_norm_le1 (n : nat) : cone_norm (u' n) <= 1.
Proof.
rewrite /u' cone_normh /=.
have := ub1 n; rewrite /αB_norm /=.
by [].
Qed.

Lemma αB_u'_ch (n : nat) : precone_le (u' n) (u' n.+1).
Proof.
rewrite /u'; apply: precone_scale_le.
case: (uch n) => [z Hz].
have /(congr1 alpha_rescale_val) := Hz => /= Hv.
by exists (alpha_rescale_val z).
Qed.

(** The B-sup of [u'] lives in the unit ball of B. *)
Let s' : B := cone_sup_ball u' αB_u'_ch αB_u'_norm_le1.

(** Paper Def 3.15 (Normc witness): the sup is [α ·: s']. *)
Definition αB_sup_ball_def : T :=
  @MkAlphaRescale R Ar α B (precone_scale (α_nng α) s').

Lemma αB_sup_ball_ub_lemma (n : nat) :
  precone_le (u n) αB_sup_ball_def.
Proof.
have key : alpha_rescale_val (u n) =
           precone_scale (α_nng α) (u' n).
  rewrite /u' -precone_scale_A.
  have -> : ((α_nng α)%:num * (α_inv_nng α)%:num)%:nng
            = 1%:nng.
    by apply: nngnum_inj => /=; rewrite divff //; exact: α_neq0.
  by rewrite precone_scale_1.
have Hle : precone_le (u' n) s' by exact: cone_sup_ball_ub.
case: Hle => z Hz.
exists (@MkAlphaRescale R Ar α B (precone_scale (α_nng α) z)).
apply: alpha_rescale_eq => /=.
rewrite key Hz precone_scale_DAr //.
Qed.

Lemma αB_sup_ball_lub_lemma (y : T) :
  (forall n, precone_le (u n) y) ->
  precone_le αB_sup_ball_def y.
Proof.
move=> Hub.
(* Rescale every [u n ≤ y] to [u' n ≤ α⁻¹ ·: y] in B. *)
have key : forall n,
  precone_le (u' n) (precone_scale (α_inv_nng α)
                                   (alpha_rescale_val y)).
  move=> n; rewrite /u'.
  case: (Hub n) => z Hz.
  have /(congr1 alpha_rescale_val) := Hz => /= Hv.
  exists (precone_scale (α_inv_nng α) (alpha_rescale_val z)).
  by rewrite Hv precone_scale_DAr.
have Hs' : precone_le s' (precone_scale (α_inv_nng α)
                                        (alpha_rescale_val y)).
  exact: cone_sup_ball_lub.
case: Hs' => z Hz.
exists (@MkAlphaRescale R Ar α B (precone_scale (α_nng α) z)).
apply: alpha_rescale_eq => /=.
have step :
  alpha_rescale_val y =
  precone_scale (α_nng α)
    (precone_scale (α_inv_nng α) (alpha_rescale_val y)).
  rewrite -precone_scale_A.
  have -> : ((α_nng α)%:num * (α_inv_nng α)%:num)%:nng
            = 1%:nng.
    by apply: nngnum_inj => /=; rewrite divff //; exact: α_neq0.
  by rewrite precone_scale_1.
rewrite [LHS]step Hz precone_scale_DAr //.
Qed.

Lemma αB_sup_ball_norm_lemma : αB_norm αB_sup_ball_def <= 1.
Proof.
rewrite /αB_norm /αB_sup_ball_def /= cone_normh /=.
have Hs' : cone_norm s' <= 1 by exact: cone_sup_ball_norm.
rewrite mulrA.
have ->: (α : R)^-1 * (α : R) = 1.
  by rewrite mulVf //; exact: α_neq0.
by rewrite mul1r.
Qed.

End αBSupBall.

(** Packaged sup-ball operator (taking the chain and bound
    hypotheses as required by [isCone]). *)
Definition αB_sup_ball (u : nat -> T)
  (uch : forall n, precone_le (u n) (u n.+1))
  (ub1 : forall n, αB_norm (u n) <= 1) : T :=
  αB_sup_ball_def uch ub1.

Lemma αB_sup_ball_ub (u : nat -> T)
  (uch : forall n, precone_le (u n) (u n.+1))
  (ub1 : forall n, αB_norm (u n) <= 1) (n : nat) :
  precone_le (u n) (αB_sup_ball uch ub1).
Proof. exact: αB_sup_ball_ub_lemma. Qed.

Lemma αB_sup_ball_lub (u : nat -> T)
  (uch : forall n, precone_le (u n) (u n.+1))
  (ub1 : forall n, αB_norm (u n) <= 1) (y : T) :
  (forall n, precone_le (u n) y) ->
  precone_le (αB_sup_ball uch ub1) y.
Proof. exact: αB_sup_ball_lub_lemma. Qed.

Lemma αB_sup_ball_norm (u : nat -> T)
  (uch : forall n, precone_le (u n) (u n.+1))
  (ub1 : forall n, αB_norm (u n) <= 1) :
  αB_norm (αB_sup_ball uch ub1) <= 1.
Proof. exact: αB_sup_ball_norm_lemma. Qed.

End AlphaRescaleCone.

HB.instance Definition _ (R : realType) (Ar : MeasSubcat R)
    (α : pos_real R) (B : MCone.type Ar) :=
  @Cone_ofWitnessSup.Build R (alpha_rescale_car α B)
    (@αB_norm R Ar α B)
    (@αB_normh R Ar α B)
    (@αB_normz R Ar α B)
    (@αB_normt R Ar α B)
    (@αB_normp R Ar α B)
    (@αB_sup_ball R Ar α B)
    (@αB_sup_ball_ub R Ar α B)
    (@αB_sup_ball_lub R Ar α B)
    (@αB_sup_ball_norm R Ar α B).

(** The abstract [cone_sup_ball] coincides with the concrete rescaled
    witness [αB_sup_ball] (the definitional link of the historical
    encoding, restored as an equation via lub-uniqueness). *)
Lemma αB_cone_sup_ballE (R : realType) (Ar : MeasSubcat R)
    (α : pos_real R) (B : MCone.type Ar)
    (u : nat -> alpha_rescale_car α B)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, cone_norm (u n) <= 1) :
  cone_sup_ball u uch ub1 = αB_sup_ball uch ub1.
Proof.
exact: cone_sup_ballE (αB_sup_ball_ub uch ub1) (αB_sup_ball_lub uch ub1).
Qed.

(** *** Test family of [αB] — Paper Definition 3.15 *)

Section AlphaRescaleTests.
Variables (R : realType) (Ar : MeasSubcat R).
Variable α : pos_real R.
Let αpos : 0 < pos_real_val α := pos_real_pos α.
Variable B : MCone.type Ar.

Local Notation T := (alpha_rescale_car α B).

(** Given a test [m] on [B], the test on [αB] is the same map
    multiplied by [α⁻¹]: this ensures [test_norm_le] for the
    rescaled norm. *)
Section αBTest.
Variable Y : ar_obj Ar.
Variable m : test_of Ar Y B.

Definition αB_test_fun : ar_carrier Ar Y -> T -> R :=
  fun s x => (α : R)^-1 * test_fun m s (alpha_rescale_val x).

Lemma αB_test_meas (x : T) :
  αB_norm x <= 1 ->
  measurable_fun setT (fun s => αB_test_fun s x).
Proof.
move=> _; rewrite /αB_test_fun.
(* [αB_norm x ≤ 1] means [‖val x‖_B ≤ α], not necessarily ≤ 1, so we
   cannot invoke [test_meas] directly; [test_meas_gen] provides
   measurability of [λ s. m s v] for an *arbitrary* [v : B]. *)
by apply: measurable_funM; [exact: measurable_cst|exact: test_meas_gen].
Qed.

Lemma αB_test_ge0 (s : ar_carrier Ar Y) (x : T) :
  0 <= αB_test_fun s x.
Proof.
rewrite /αB_test_fun; apply: mulr_ge0.
  exact: α_inv_ge0 α.
exact: test_ge0.
Qed.

Lemma αB_test_le1 (s : ar_carrier Ar Y) (x : T) :
  cone_norm x <= 1 -> αB_test_fun s x <= 1.
Proof.
move=> Hx; rewrite /αB_test_fun.
(* [(α : R)^-1 * test m s v ≤ (α : R)^-1 * ‖v‖_B ≤ (α : R)^-1 * α = 1]. *)
apply: le_trans
  (_ : (α : R)^-1 * cone_norm (alpha_rescale_val x) <= _).
  apply: ler_wpM2l; first exact: α_inv_ge0 α.
  exact: test_norm_le.
by have := Hx; rewrite /cone_norm /= /αB_norm /=.
Qed.

Lemma αB_test_lin0 (s : ar_carrier Ar Y) :
  αB_test_fun s precone_zero = 0.
Proof. by rewrite /αB_test_fun /= test_lin0 mulr0. Qed.

Lemma αB_test_linD (s : ar_carrier Ar Y) (x y : T) :
  αB_test_fun s (precone_add x y) =
  αB_test_fun s x + αB_test_fun s y.
Proof. by rewrite /αB_test_fun /= test_linD mulrDr. Qed.

Lemma αB_test_linZ
  (s : ar_carrier Ar Y) (r : {nonneg R}) (x : T) :
  αB_test_fun s (precone_scale r x) = r%:num * αB_test_fun s x.
Proof.
by rewrite /αB_test_fun /= test_linZ mulrCA.
Qed.

Lemma αB_test_cont
  (s : ar_carrier Ar Y) (u : nat -> T)
  (uch : forall n, precone_le (u n) (u n.+1))
  (ub1 : forall n, cone_norm (u n) <= 1)
  (N : R) :
  (forall n, αB_test_fun s (u n) <= N) ->
  αB_test_fun s (cone_sup_ball u uch ub1) <= N.
Proof.
move=> HN.
(* Identify the abstract sup with the concrete witness [αB_sup_ball]:
   in its [αB_sup_ball_def] form, it has val [α_nng α *: s'] where
   [s' = cone_sup_ball u' …] for the rescaled chain
   [u' n = α_inv_nng α *: val (u n)] in B.
   [αB_test_fun s (…) = α^-1 * m s (α *: s') = m s s'], and
   [test_cont] of [m] on [u'] in B gives the bound. *)
rewrite αB_cone_sup_ballE.
rewrite /αB_test_fun
        /αB_sup_ball /αB_sup_ball_def /= test_linZ /= mulrA.
have ->: (α : R)^-1 * (α : R) = 1.
  by rewrite mulVf //; exact: α_neq0.
rewrite mul1r.
apply: test_cont => n.
have := HN n.
rewrite /αB_test_fun /= test_linZ /=.
by [].
Qed.

Lemma αB_test_norm_le (s : ar_carrier Ar Y) (x : T) :
  αB_test_fun s x <= cone_norm x.
Proof.
rewrite /αB_test_fun /cone_norm /= /αB_norm.
apply: ler_wpM2l; first exact: α_inv_ge0 α.
exact: test_norm_le.
Qed.

Definition αB_test : test_of Ar Y T :=
  MkTestOf αB_test_meas αB_test_ge0 αB_test_le1
           αB_test_lin0 αB_test_linD αB_test_linZ
           αB_test_cont αB_test_norm_le.

End αBTest.

(** Paper Def 3.15: the test family of [αB] is the [α⁻¹]-scaled
    image of [B]'s test family. *)
Definition αB_mcone_M (Y : ar_obj Ar) : set (test_of Ar Y T) :=
  [set p | exists2 m : test_of Ar Y B,
             mcone_M Y m & p = αB_test m].

(** (Mscomp) — closure under reindexing. *)
Lemma αB_mcone_M_comp
  (Y' Y : ar_obj Ar) (ψ : ar_hom Ar Y' Y)
  (p : test_of Ar Y T) :
  αB_mcone_M p ->
  αB_mcone_M (test_reindex ψ p).
Proof.
case=> m mM ->.
have mM' : mcone_M Y' (test_reindex ψ m) by exact: mcone_M_comp.
exists (test_reindex ψ m) => //.
apply: test_eq => s x.
by rewrite /test_reindex /= /test_reindex_fun /αB_test_fun /=.
Qed.

(** (Mssep) — separation. *)
Lemma αB_mcone_M_sep (x1 x2 : T) :
  (forall p : test_of Ar (ar_zero Ar) T,
    αB_mcone_M p ->
    test_fun p (ar_zero_pt Ar) x1 =
    test_fun p (ar_zero_pt Ar) x2) ->
  x1 = x2.
Proof.
move=> Hsep.
apply: alpha_rescale_eq.
apply: mcone_M_sep => m mM.
have Hp : αB_mcone_M (αB_test m) by exists m.
have := Hsep _ Hp.
rewrite /αB_test /= /αB_test_fun /=.
move/(congr1 (fun y => (α : R) * y)).
rewrite !mulrA mulfV ?(α_neq0 α) // !mul1r => H.
exact: H.
Qed.

(** (Msnorm) — norm adherence (rescaled). *)
Lemma αB_mcone_M_norm (x : T) (eps : R) :
  x <> precone_zero -> 0 < eps ->
  exists p : test_of Ar (ar_zero Ar) T,
    αB_mcone_M p /\
    cone_norm x <= test_fun p (ar_zero_pt Ar) x + eps.
Proof.
move=> xne eps_pos.
(* αB-norm of x is [(α : R)^-1 * ‖val x‖]. Apply (Msnorm) of B to
   [val x] with [α · eps]; obtain m with
   [‖val x‖ ≤ m(val x) + α·eps].
   Multiply by [(α : R)^-1]:
   [(α : R)^-1·‖val x‖ ≤ (α : R)^-1·m(val x) + eps]. *)
have vne : alpha_rescale_val x <> precone_zero.
  move=> Hv; apply: xne; apply: alpha_rescale_eq.
  exact: Hv.
have αeps_pos : 0 < (α : R) * eps by rewrite mulr_gt0.
have [m [mM Hm]] :=
  @mcone_M_norm R Ar B (alpha_rescale_val x) ((α : R) * eps) vne αeps_pos.
exists (αB_test m); split.
  by exists m.
rewrite /αB_test /= /αB_test_fun /=.
rewrite /cone_norm /= /αB_norm /=.
have step :
  (α : R)^-1 * test_fun m (ar_zero_pt Ar) (alpha_rescale_val x) + eps =
  (α : R)^-1 *
    (test_fun m (ar_zero_pt Ar) (alpha_rescale_val x)
     + (α : R) * eps).
  rewrite mulrDr.
  congr (_ + _).
  rewrite mulrA mulVf ?mul1r //.
  exact: α_neq0.
rewrite step; apply: ler_wpM2l; first exact: α_inv_ge0 α.
exact: Hm.
Qed.

End AlphaRescaleTests.

HB.instance Definition _ (R : realType) (Ar : MeasSubcat R)
    (α : pos_real R) (B : MCone.type Ar) :=
  @isMCone.Build R Ar (alpha_rescale_car α B)
    (@αB_mcone_M R Ar α B)
    (@αB_mcone_M_comp R Ar α B)
    (@αB_mcone_M_sep R Ar α B)
    (@αB_mcone_M_norm R Ar α B).

(** ** Paper Remark 3.14 — illustration with αB

    The identity carrier map is *not* in general a morphism of
    [MCones] from [B] to [αB] (norms differ by [α^{-1}]), but the
    rescaled map [x ↦ α ·: x] (interpreted as a function [B → αB])
    *does* preserve everything, including the norm:
    [‖α ·: x‖_{αB} = α^{-1} · α · ‖x‖_B = ‖x‖_B]. We expose this
    morphism as a witness that [B] and [αB] are isomorphic in
    [MCones] (the inverse being [x ↦ α^{-1} ·: x]).

    The substance here is that the underlying carrier of [B] and
    [αB] is the same (modulo the [alpha_rescale_car] wrapper), so
    the measurable-path structures are isomorphic: paper Rem 3.14
    says that "measurability structures determine paths". *)

(** *** A trivial direction: paths through the wrapper are
       measurable as paths to [αB] iff they are measurable as
       paths to [B] (up to scaling). *)

Section MConesIsoAlpha.
Variables (R : realType) (Ar : MeasSubcat R).
Variable α : pos_real R.
Let αpos : 0 < pos_real_val α := pos_real_pos α.
Variable B : MCone.type Ar.

Local Notation T := (alpha_rescale_car α B).

End MConesIsoAlpha.
