(**md**************************************************************************)
(** * [tensor_curry] past [kbind_ext] — categorical reduction, axiom-free

    BEYOND THE PAPER — operational tool for Phase 4 ([ex_loop] / [ex_geom]
    / [ex_almost_loop p]) mass-closure.

    Given a [kbind_ext k m] (resp. [kcomp g f]) whose source coalgebra
    [G_out = EM_prod G_in A] is itself a binary product (so the
    underlying [icones_hom] has tensor source [coalg_obj G_in ⊗ coalg_obj
    A]), the main lemma pushes [tensor_curry] inside the composition:

    [[
      tensor_curry (ch_mor (kbind_ext k m))
      = (C ⊸ bang_fmap (adj_phi k ∘ ⟨id, adj_phi m⟩))
            ∘ tensor_curry (coalg_str (EM_prod G_in A)).
    ]]

    The right-hand side is in [icones_hom B (C ⊸ Bang (coalg_obj B))],
    cleanly exposing [adj_phi k] and [adj_phi m] post-composed by
    [linhom_post_icones] (the [C ⊸ −] functor).

    Two ingredients:
    1. [adj_psiK] / definitional unfolding of [adj_psi]:
       [ch_mor (kbind_ext k m) = bang_fmap (adj_phi (kbind_ext k m))
            ∘ coalg_str (EM_prod G_in A)].
    2. [adj_phi_kbind_ext]: [adj_phi (kbind_ext k m) = adj_phi k ∘
       ⟨id, adj_phi m⟩].
    Then [tensor_curry_natural_post] pushes [tensor_curry] past the
    outer post-composition by [bang_fmap (adj_phi …)].

    Companion: [tensor_curry_ch_mor_kcomp] does the same for [kcomp g f]
    using [adj_phi_kcomp].  This form is directly applicable to
    [eD (ne_app F X) = kcomp app_pair …] downstream.

    Author: Guillaume Baudart <guillaume.baudart@inria.fr>. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals signed.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import measure dirac_measure.

From Stdlib Require Import Strings.String.

Require Import Icones.prelude.nonneg_extra.
Require Import Icones.cones.precone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.cone.
Require Import Icones.cones.omega_general.
Require Import Icones.cones.cone_cat.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_cat.
Require Import Icones.icones.examples_icone.
Require Import Icones.stable.totmono.
Require Import Icones.stable.scones_cat.
Require Import Icones.homs.linhom.
Require Import Icones.homs.linhom_functor.
Require Import Icones.homs.tensor.
Require Import Icones.homs.tensor_iso.
Require Import Icones.homs.smcc.
Require Import Icones.homs.exp_adjunction.
Require Import Icones.homs.bang.
Require Import Icones.homs.seely_defs.
Require Import Icones.homs.seely.
Require Import Icones.homs.coalgebra.
Require Import Icones.homs.em_cat.
Require Import Icones.homs.em_cartesian.
Require Import Icones.homs.em_seely_comonoid.
Require Import Icones.programs.infra.cbv_adjunction.
Require Import Icones.programs.cbv.
Require Import Icones.programs.ppl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** Section setup *)

Section TensorCurryKbindExt.
Variables (R : realType) (Ar : MeasSubcat R).

(** [ch_mor (adj_psi g) = bang_fmap g ∘ coalg_str P] — holds
    definitionally by the very definition of [adj_psi]; recorded as a
    named equation for rewriting. *)
Lemma ch_mor_adj_psi (P : Coalgebra Ar) (B : ICone.type Ar)
    (g : icones_hom Ar (coalg_obj P) B) :
  ch_mor (adj_psi g) = icones_comp (bang_fmap g) (coalg_str P).
Proof. by []. Qed.

(** [ch_mor h = bang_fmap (adj_phi h) ∘ coalg_str P] for any
    [h : coalg_hom P (bang_cofree B)].  Obtained by [adj_psiK]
    ([h = adj_psi (adj_phi h)]), then [ch_mor_adj_psi]. *)
Lemma ch_mor_via_adj_phi (P : Coalgebra Ar) (B : ICone.type Ar)
    (h : coalg_hom P (bang_cofree B)) :
  ch_mor h = icones_comp (bang_fmap (adj_phi h)) (coalg_str P).
Proof. by rewrite -[h in ch_mor h]adj_psiK. Qed.

(** ** [tensor_curry] of [ch_mor (kbind_ext k m)] — main lemma

    For [G_out = EM_prod G_in A], the source of [ch_mor (kbind_ext k m)]
    is [coalg_obj G_in ⊗ coalg_obj A] (definitionally [coalg_obj G_out]).
    Currying that tensor exposes the inner pairing structure of
    [kbind_ext] cleanly. *)
Lemma tensor_curry_ch_mor_kbind_ext (G_in A1 A B : Coalgebra Ar)
    (k : coalg_hom (EM_prod (EM_prod G_in A1) A) (Tobj B))
    (m : coalg_hom (EM_prod G_in A1) (Tobj A)) :
  tensor_curry (B := coalg_obj G_in) (C := coalg_obj A1)
    (ch_mor (kbind_ext k m)) =
  icones_comp
    (linhom_post_icones (C := coalg_obj A1)
       (bang_fmap (icones_comp (adj_phi k)
                    (em_pair_mor
                       (icones_id Ar (coalg_obj (EM_prod G_in A1)))
                       (adj_phi m)))))
    (tensor_curry (B := coalg_obj G_in) (C := coalg_obj A1)
       (coalg_str (EM_prod G_in A1))).
Proof.
rewrite (ch_mor_via_adj_phi (kbind_ext k m)).
rewrite (adj_phi_kbind_ext k m).
exact: tensor_curry_natural_post.
Qed.

(** ** [tensor_curry] of [ch_mor (kcomp g f)] — general companion

    For [f : coalg_hom (EM_prod G_in A1) (Tobj Q)] and [g : coalg_hom Q
    (Tobj S)], [tensor_curry (ch_mor (kcomp g f))] reduces by the same
    chain.  Directly applicable to [eD (ne_app …) = kcomp app_pair …]
    and other [kcomp]-shaped reductions. *)
Lemma tensor_curry_ch_mor_kcomp (G_in A1 Q S : Coalgebra Ar)
    (g : coalg_hom Q (Tobj S))
    (f : coalg_hom (EM_prod G_in A1) (Tobj Q)) :
  tensor_curry (B := coalg_obj G_in) (C := coalg_obj A1)
    (ch_mor (kcomp g f)) =
  icones_comp
    (linhom_post_icones (C := coalg_obj A1)
       (bang_fmap (icones_comp (adj_phi g) (adj_phi f))))
    (tensor_curry (B := coalg_obj G_in) (C := coalg_obj A1)
       (coalg_str (EM_prod G_in A1))).
Proof.
rewrite (ch_mor_via_adj_phi (kcomp g f)).
rewrite (adj_phi_kcomp g f).
exact: tensor_curry_natural_post.
Qed.

End TensorCurryKbindExt.

Arguments ch_mor_adj_psi {R Ar P B} g.
Arguments ch_mor_via_adj_phi {R Ar P B} h.
Arguments tensor_curry_ch_mor_kbind_ext {R Ar G_in A1 A B} k m.
Arguments tensor_curry_ch_mor_kcomp {R Ar G_in A1 Q S} g f.

(** ** Pointwise evaluation forms

    The [Lfun] (= [cones_hom_fun ∘ mcones_hom_cones ∘ icones_hom_mcones])
    pointwise version, obtained by composing the icones-level identity
    with [icones_comp]'s definitional behaviour on points.

    Reading: to evaluate [tensor_curry (ch_mor (kbind_ext k m))] at a
    point [γ : coalg_obj G_in], unfold to [linhom_post (bang_fmap (adj_phi
    k ∘ ⟨id, adj_phi m⟩)) (Lfun (tensor_curry (coalg_str (EM_prod G_in
    A1))) γ)] — i.e. post-compose the inner linhom with [bang_fmap
    (adj_phi k ∘ ⟨id, adj_phi m⟩)]. *)

Section PointwiseEval.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

(** Pointwise: at any [γ : coalg_obj G_in], curry-then-evaluate fires
    through [linhom_post] applied to the [bang_fmap (adj_phi …)]
    post-composition. *)
Lemma tensor_curry_ch_mor_kbind_ext_at (G_in A1 A B : Coalgebra Ar)
    (k : coalg_hom (EM_prod (EM_prod G_in A1) A) (Tobj B))
    (m : coalg_hom (EM_prod G_in A1) (Tobj A))
    (gamma : coalg_obj G_in) :
  Lfun (tensor_curry (B := coalg_obj G_in) (C := coalg_obj A1)
                     (ch_mor (kbind_ext k m)))
       gamma =
  linhom_post (bang_fmap (icones_comp (adj_phi k)
                  (em_pair_mor
                     (icones_id Ar (coalg_obj (EM_prod G_in A1)))
                     (adj_phi m))))
    (Lfun (tensor_curry (B := coalg_obj G_in) (C := coalg_obj A1)
                        (coalg_str (EM_prod G_in A1)))
          gamma).
Proof.
by rewrite (tensor_curry_ch_mor_kbind_ext k m).
Qed.

(** Pointwise version for [kcomp]. *)
Lemma tensor_curry_ch_mor_kcomp_at (G_in A1 Q S : Coalgebra Ar)
    (g : coalg_hom Q (Tobj S))
    (f : coalg_hom (EM_prod G_in A1) (Tobj Q))
    (gamma : coalg_obj G_in) :
  Lfun (tensor_curry (B := coalg_obj G_in) (C := coalg_obj A1)
                     (ch_mor (kcomp g f)))
       gamma =
  linhom_post (bang_fmap (icones_comp (adj_phi g) (adj_phi f)))
    (Lfun (tensor_curry (B := coalg_obj G_in) (C := coalg_obj A1)
                        (coalg_str (EM_prod G_in A1)))
          gamma).
Proof.
by rewrite (tensor_curry_ch_mor_kcomp g f).
Qed.

End PointwiseEval.

Arguments tensor_curry_ch_mor_kbind_ext_at {R Ar G_in A1 A B} k m gamma.
Arguments tensor_curry_ch_mor_kcomp_at {R Ar G_in A1 Q S} g f gamma.

(** ** Class 1 — pointwise [adj_psi] evaluation
    BEYOND THE PAPER — Phase 4 evaluation tier.

    Pointwise reading of [ch_mor (adj_psi g)]:
    [Lfun (ch_mor (adj_psi g)) x = Lfun (bang_fmap g) (Lfun (coalg_str P) x)].
    Definitional from [ch_mor_adj_psi]. *)

Section AdjPsiAt.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

(** Pointwise [ch_mor (adj_psi g)]: [bang_fmap g] applied to [coalg_str]
    of the point.  Direct consequence of [ch_mor_adj_psi]. *)
Lemma Lfun_ch_mor_adj_psi_at (P : Coalgebra Ar) (B : ICone.type Ar)
    (g : icones_hom Ar (coalg_obj P) B) (x : coalg_obj P) :
  Lfun (ch_mor (adj_psi g)) x =
  Lfun (bang_fmap g) (Lfun (coalg_str P) x).
Proof. by rewrite (ch_mor_adj_psi g). Qed.

(** Pointwise [ch_mor h] for [h : coalg_hom P (bang_cofree B)]: via [adj_psiK]. *)
Lemma Lfun_ch_mor_via_adj_phi_at (P : Coalgebra Ar) (B : ICone.type Ar)
    (h : coalg_hom P (bang_cofree B)) (x : coalg_obj P) :
  Lfun (ch_mor h) x =
  Lfun (bang_fmap (adj_phi h)) (Lfun (coalg_str P) x).
Proof. by rewrite (ch_mor_via_adj_phi h). Qed.

End AdjPsiAt.

Arguments Lfun_ch_mor_adj_psi_at {R Ar P B} g x.
Arguments Lfun_ch_mor_via_adj_phi_at {R Ar P B} h x.

(** ** Class 4 — pointwise [const_kleisli] evaluation
    BEYOND THE PAPER — Phase 4 evaluation tier.

    For [c : C] with [‖c‖ ≤ 1] and [x : coalg_obj G],
    [Lfun (ch_mor (const_kleisli G c Hc)) x =
       Lfun (bang_fmap (const_icones G c Hc)) (Lfun (coalg_str G) x)].
    Special case of [Lfun_ch_mor_adj_psi_at] at [g := const_icones G c Hc].

    A more pointwise-friendly form expands [const_icones = lin_pt c ∘ coalg_e G]
    and reduces to [prom (precone_scale (c1_val (coalg_e G ·)) c)] — landing in
    [Bang C] via [bang_fmap_prom] applied to a [lin_pt]-image.  See
    [const_kleisli_at_prom_coalg] below. *)

Section ConstKleisliAt.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

(** Direct pointwise unfolding via [Lfun_ch_mor_adj_psi_at]. *)
Lemma Lfun_ch_mor_const_kleisli_at (G : Coalgebra Ar) (C : ICone.type Ar)
    (c : C) (Hc : (cone_norm c <= 1)%R) (x : coalg_obj G) :
  Lfun (ch_mor (const_kleisli G c Hc)) x =
  Lfun (bang_fmap (const_icones G c Hc)) (Lfun (coalg_str G) x).
Proof. exact: (Lfun_ch_mor_adj_psi_at (const_icones G c Hc) x). Qed.

End ConstKleisliAt.

Arguments Lfun_ch_mor_const_kleisli_at {R Ar G C} c Hc x.

(** ** Class 2 — pointwise [app_kleisli] structural reduction
    BEYOND THE PAPER — Phase 4 evaluation tier.

    [app_kleisli VF VA = coalg_comp (tmul B) (adj_psi (app_under VF VA))]
    by definition.  Its [ch_mor] reads at a point as

      [Lfun (ch_mor (app_kleisli VF VA)) x
         = Lfun (bang_fmap (icones_comp (der (U B)) (app_under VF VA)))
                (Lfun (coalg_str G) x)]

    via [adj_phi_app_kleisli] + [ch_mor_via_adj_phi].  This is the
    structural CBV β reduction at the point level: the result lives in
    [Bang (U B) = coalg_obj (Tobj B)], obtained by [bang_fmap]-promoting
    the icones-level application image of [(der ∘ app_under) ∘ coalg_str G]
    at the point. *)

Section AppKleisliAt.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

(** Pointwise [ch_mor (app_kleisli VF VA)]:
    [bang_fmap (der ∘ app_under VF VA)] applied to [coalg_str G ·]. *)
Lemma Lfun_ch_mor_app_kleisli_at (G A B : Coalgebra Ar)
    (VF : coalg_hom G
            (bang_cofree (linhom_car Ar (coalg_obj A) (coalg_obj (Tobj B)))))
    (VA : coalg_hom G A) (x : coalg_obj G) :
  Lfun (ch_mor (app_kleisli VF VA)) x =
  Lfun (bang_fmap (icones_comp (der (coalg_obj B)) (app_under VF VA)))
       (Lfun (coalg_str G) x).
Proof.
rewrite (ch_mor_via_adj_phi (app_kleisli VF VA)).
by rewrite (adj_phi_app_kleisli VF VA).
Qed.

End AppKleisliAt.

Arguments Lfun_ch_mor_app_kleisli_at {R Ar G A B} VF VA x.

(** ** [linhom_norm] of a [cone_one]-source linhom = pointwise value at [one1]
    BEYOND THE PAPER — Phase 4 evaluation tier.

    For a linhom [phi : cone_one ⊸ C], its operator norm is exactly the
    cone-norm of its value at the unit point [one1].

    Proof: the source [cone_one] is 1-dimensional, [s = (c1_val s) · one1]
    via [cone_one_eq], so by linearity [linhom_fun phi s = (c1_val s) ·
    linhom_fun phi one1].  Apply [cone_normh] and observe [c1_val s =
    cone_norm s].  The sup is then attained at [s = one1]
    (where [c1_val one1 = 1]).

    This is the LINHOM-norm side of the [linhom_one_iso : 1 ⊸ C ≅ C] iso
    of [tensor_iso.v]: the forward map [eval1] is an ISOMETRY. *)

Section LinhomNormOne1.
Variables (R : realType) (Ar : MeasSubcat R).
Variable C : ICone.type Ar.

Lemma cone_norm_one1_E :
  (cone_norm (one1 : cone_one_car Ar) = 1)%R.
Proof. by rewrite /cone_norm /= /c1_norm. Qed.

(** The headline identity: [‖φ‖ = ‖φ(1)‖] for [φ : 1 ⊸ C]. *)
Lemma linhom_norm_one1_E (phi : linhom_car Ar (cone_one_car Ar) C) :
  linhom_norm phi = cone_norm (linhom_fun phi one1).
Proof.
apply: le_anti; apply/andP; split.
- (* Upper bound: every [s] in the ball gives [cone_norm (φ s) ≤
     cone_norm (φ one1)], since [s = (c1_val s) · one1] and
     [c1_val s = cone_norm s ≤ 1]. *)
  apply: linhom_norm_sup_lub => s Hs.
  have Hs_eq : s = precone_scale (c1_val s) (one1 : cone_one_car Ar).
    apply: cone_one_eq; apply: val_inj => /=.
    by rewrite mulr1.
  rewrite [in linhom_fun _ _]Hs_eq.
  have [_ _ HZ] := linhom_pre_linear (linhom_pre_of phi).
  rewrite -[linhom_fun phi (precone_scale _ _)]
            /(linhom_pre_fun (linhom_pre_of phi)
                              (precone_scale (c1_val s)
                                              (one1 : cone_one_car Ar))).
  rewrite HZ /=.
  rewrite cone_normh.
  rewrite -[X in _ <= X]mul1r.
  apply: ler_wpM2r; first exact: cone_norm_ge0.
  by rewrite -[_%:num]/(cone_norm s).
- (* Lower bound: [s := one1] is in the ball and gives [cone_norm
     (φ one1)] in the image set. *)
  have H1 : (cone_norm (one1 : cone_one_car Ar) <= 1)%R
    by rewrite cone_norm_one1_E.
  exact: (linhom_norm_sup_ub phi one1 H1).
Qed.

End LinhomNormOne1.

Arguments cone_norm_one1_E {R Ar}.
Arguments linhom_norm_one1_E {R Ar C} phi.

