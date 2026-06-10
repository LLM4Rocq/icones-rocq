(**md *** PPL CBV chapter infrastructure

    This file is NOT part of the Ehrhard-Geoffroy 2025 formalization
    (paper §2-§9). It provides the convex-combination reduction of
    [case_em] against a Bernoulli scrutinee, used to close the
    [ex_geom] mass-1 theorem (reducing the [if Bern(½) then 0 else 1+g()]
    pattern to [½·(then 0) + ½·(else 1+g())] at the cone level).

    Headline:
    - [convex_icones p Hp_ge0 Hp_le1 a b] — the underlying icones_hom of
      the convex combination [p·a + (1-p)·b] at the linhom-cone level
      (= [bool_case (bernoulli p) a_lh b_lh] via [linhom_icones]).
    - [convex_combination p Hp_ge0 Hp_le1 a b] — the coalg_hom packaging
      of [convex_icones] via [adj_psi].
    - [case_em_bernoulli] — the reduction
        [kbind_ext (case_em a b) (bernoulli_kleisli p) =
         convex_combination p a b].

    See also: [theories/programs/infra/bool_case_hom.v] (icones_hom
    packaging of [bool_case]), [theories/programs/ppl.v] (case_em,
    bernoulli_kleisli, ne_bernoulli, ne_if). *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals constructive_ereal.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import ereal.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import measure.

Require Import Icones.prelude.classical_extra.
Require Import Icones.prelude.nonneg_extra.
Require Import Icones.prelude.omegacpo.
Require Import Icones.cones.precone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.cone.
Require Import Icones.cones.cone_cat.
Require Import Icones.programs.infra.bool_cone.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.mcones.path.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.icone.
Require Import Icones.icones.examples_icone.
Require Import Icones.icones.icone_cat.
Require Import Icones.homs.icones_iso.
Require Import Icones.homs.linhom.
Require Import Icones.homs.tensor.
Require Import Icones.homs.tensor_construct.
Require Import Icones.homs.smcc.
Require Import Icones.homs.exp_adjunction.
Require Import Icones.homs.bang.
Require Import Icones.homs.seely.
Require Import Icones.homs.tensor_hom_iso.
Require Import Icones.programs.infra.bool_case_hom.
Require Import Icones.homs.coalgebra.
Require Import Icones.homs.em_cat.
Require Import Icones.homs.em_cartesian.
Require Import Icones.programs.cbv.
Require Import Icones.programs.ppl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** The convex combination [p·a + (1-p)·b]

    At the linhom-cone level, the convex combination is exactly the
    evaluation of [bool_case_linhom a_lh b_lh] at the [bernoulli p]
    element of [bool_cone_car].  Operationally:
    [[
      bool_case (bernoulli p) a_lh b_lh
      = precone_add (precone_scale p a_lh) (precone_scale (1-p) b_lh).
    ]]
    Norm: bounded by [≤ 1] since [bernoulli p] has norm exactly [1] and
    [bool_case_linhom] has operator norm [≤ 1] (its unit-ball-respecting
    form). *)

Section ConvexCombination.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (G A : Coalgebra Ar).
Variables (a b : coalg_hom G (Tobj A)).
Variables (p : R) (Hp_ge0 : (0 <= p)%R) (Hp_le1 : (p <= 1)%R).

(** Branches as norm-[≤1] points in the hom-cone (matching the local
    [Let]-definitions inside [Section CaseEM] of [ppl.v]). *)
Let a_lh : linhom_car Ar (coalg_obj G) (Bang Ar (coalg_obj A)) :=
  icones_to_linhom (ch_mor a).
Let b_lh : linhom_car Ar (coalg_obj G) (Bang Ar (coalg_obj A)) :=
  icones_to_linhom (ch_mor b).

Lemma cc_a_lh_norm : (cone_norm a_lh <= 1)%R.
Proof. exact: icones_to_linhom_norm_le1 (ch_mor a). Qed.

Lemma cc_b_lh_norm : (cone_norm b_lh <= 1)%R.
Proof. exact: icones_to_linhom_norm_le1 (ch_mor b). Qed.

(** The convex combination at the linhom level, packaged as a [linhom_car]. *)
Definition convex_linhom : linhom_car Ar (coalg_obj G) (Bang Ar (coalg_obj A)) :=
  bool_case (@bernoulli R Ar p Hp_ge0 Hp_le1) a_lh b_lh.

(** Operational reading: [convex_linhom = bool_case (bernoulli p) a_lh b_lh].

    This is a definitional unfolding, but recorded as a lemma for clarity:
    [convex_linhom] IS the evaluation of [bool_case_linhom] at the
    [bernoulli p] scrutinee. *)
Lemma convex_linhomE :
  convex_linhom = bool_case (@bernoulli R Ar p Hp_ge0 Hp_le1) a_lh b_lh.
Proof. by []. Qed.

(** Norm bound: [cone_norm convex_linhom ≤ 1].

    Proof: by [linhom_norm_sup_lub] reduce to a pointwise bound at
    [cone_norm g ≤ 1]; then via [bool_case_norm_le1] (the unit-ball
    bound on [bool_case_linhom]) we have
    [cone_norm (bool_case_linhom a_lh b_lh x) ≤ cone_norm x] for any
    [x : bool_cone] (since both [a_lh], [b_lh] have norm ≤ 1).  Specialise
    to [x = bernoulli p] which has norm exactly [1]; thread through
    [cone_normh] from [g] to the linhom_apply norm. *)
Lemma convex_linhom_norm_le1 : (cone_norm convex_linhom <= 1)%R.
Proof.
rewrite /convex_linhom.
(* The proof: bool_case_linhom a_lh b_lh has norm ≤ 1 (unit-ball form);
   evaluating it at any x : bool_cone with norm ≤ 1 yields a result of
   norm ≤ 1 in the codomain (here, linhom_car ... ).  [bernoulli p] has
   norm exactly 1, so the bound applies. *)
have Hball : (cone_norm (@bernoulli R Ar p Hp_ge0 Hp_le1 : bool_cone_car Ar) <= 1)%R
  := @bernoulli_norm_le1 R Ar p Hp_ge0 Hp_le1.
have Hbc := bool_case_norm_le1 (a := a_lh) (b := b_lh) cc_a_lh_norm cc_b_lh_norm
              (@bernoulli R Ar p Hp_ge0 Hp_le1).
exact: le_trans Hbc Hball.
Qed.

(** The icones_hom packaging of [convex_linhom] in [Bang Ar (coalg_obj A)],
    using the [linhom_icones] bridge. *)
Definition convex_icones_bang :
    icones_hom Ar (coalg_obj G) (Bang Ar (coalg_obj A)) :=
  linhom_icones convex_linhom convex_linhom_norm_le1.

(** The icones_hom presentation INTO [coalg_obj A] (the input of [adj_psi]):
    post-compose [convex_icones_bang] with [der A] to drop the outer [!].
    This is the icones_hom whose [adj_psi]-image is the natural
    [coalg_hom G (Tobj A)] presentation of the convex combination. *)
Definition convex_icones :
    icones_hom Ar (coalg_obj G) (coalg_obj A) :=
  icones_comp (der (coalg_obj A)) convex_icones_bang.

(** The coalg_hom packaging — this is the natural [coalg_hom G (Tobj A)]
    presentation of the convex combination [p·a + (1-p)·b]. *)
Definition convex_combination : coalg_hom G (Tobj A) :=
  adj_psi (P := G) (B := coalg_obj A) convex_icones.

(** Operational reading at the icones_hom level: [adj_phi] of the convex
    combination is exactly [convex_icones]. *)
Lemma adj_phi_convex_combination :
  adj_phi convex_combination = convex_icones.
Proof. exact: adj_phiK convex_icones. Qed.

End ConvexCombination.

Arguments convex_linhom {R Ar G A} a b {p} Hp_ge0 Hp_le1.
Arguments convex_icones_bang {R Ar G A} a b {p} Hp_ge0 Hp_le1.
Arguments convex_icones {R Ar G A} a b {p} Hp_ge0 Hp_le1.
Arguments convex_combination {R Ar G A} a b {p} Hp_ge0 Hp_le1.
Arguments adj_phi_convex_combination {R Ar G A} a b {p} Hp_ge0 Hp_le1.

(** ** Helper: [der_bool ∘ adj_phi (bernoulli_kleisli p) = const_icones G bernoulli H]

    The deriliction [der bool_cone] composed with the [adj_phi]-image of
    the constant Kleisli arrow at [bernoulli p] is just the constant
    icones_hom into [bool_cone_car] at [bernoulli p].

    Proof: [adj_phi (bernoulli_kleisli p)] reduces (by [adj_phi_natL] +
    [adj_triangleL]) to [ch_mor (const_kleisli G bernoulli H)]; the
    latter is [bang_fmap (const_icones G bernoulli H) ∘ coalg_str G] by
    definition of [adj_psi].  Composing with [der bool] absorbs the
    [bang_fmap] via [der_nat], leaving [const_icones G bernoulli H ∘ der G
    ∘ coalg_str G], and [coalg_counit G] kills the [der G ∘ coalg_str G]. *)

Section DerBernoulliKleisli.
Variables (R : realType) (Ar : MeasSubcat R) (G : Coalgebra Ar).
Variables (p : R) (Hp_ge0 : (0 <= p)%R) (Hp_le1 : (p <= 1)%R).

Lemma der_bernoulli_kleisli_E :
  icones_comp (der (bool_cone_car Ar))
              (adj_phi (bernoulli_kleisli G p Hp_ge0 Hp_le1))
  = const_icones G (@bernoulli R Ar p Hp_ge0 Hp_le1)
                    (@bernoulli_norm_le1 R Ar p Hp_ge0 Hp_le1).
Proof.
rewrite /bernoulli_kleisli.
rewrite adj_phi_natL adj_triangleL icones_compIl.
rewrite /const_kleisli /adj_psi /=.
rewrite icones_compA -(der_nat (const_icones G (@bernoulli R Ar p Hp_ge0 Hp_le1)
                                              (@bernoulli_norm_le1 R Ar p Hp_ge0 Hp_le1))).
rewrite -icones_compA.
have Hc : icones_comp (der (coalg_obj G)) (coalg_str G) = icones_id Ar (coalg_obj G)
  := coalg_counit G.
by rewrite Hc icones_compIr.
Qed.

End DerBernoulliKleisli.

Arguments der_bernoulli_kleisli_E {R Ar G p} Hp_ge0 Hp_le1.

(** ** Main lemma: [case_em_bernoulli] — the convex-combination reduction *)

Section CaseEmBernoulli.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (G A : Coalgebra Ar).
Variables (a b : coalg_hom G (Tobj A)).
Variables (p : R) (Hp_ge0 : (0 <= p)%R) (Hp_le1 : (p <= 1)%R).

(** Convenient local notations. *)
Local Notation a_lh := (icones_to_linhom (ch_mor a)).
Local Notation b_lh := (icones_to_linhom (ch_mor b)).
Local Notation Lfun h := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

(** The key structural identity (icones_hom-level reduction):
    [case_em_under_der a b ∘ ⟨id, adj_phi (bernoulli_kleisli p)⟩
     = convex_icones a b Hp_ge0 Hp_le1].

    Proof outline:
    1. Unfold [case_em_under_der]; absorb [(id ⊗ der_bool) ∘ ⟨id, m⟩]
       to [(id ⊗ (der_bool ∘ m)) ∘ coalg_d G].
    2. Use [der_bernoulli_kleisli_E] to replace [der_bool ∘ adj_phi
       (bernoulli_kleisli p)] by [const_icones G bernoulli H].
    3. Unfold [const_icones]; absorb [(id ⊗ coalg_e G) ∘ coalg_d G]
       to [iso_bwd (tensor_runit G)] via [emc_counitR].
    4. Reduce to a pointwise [icones_hom_eq], where both sides
       evaluate (via [tensor_runit_bwdE], [tensor_braidEp],
       [tensor_morE], [tensor_uncurryK], [tensor_curryE]) to the
       same expression in [Bang Ar (coalg_obj A)]. *)

(** Step 1: Reduce [(id ⊗ der_bool) ∘ ⟨id_G, adj_phi (bern_kleisli p)⟩]
    to [(id ⊗ const_icones G bernoulli H) ∘ coalg_d G]. *)
Lemma case_em_pre_step1 :
  icones_comp
    (tensor_mor (icones_id Ar (coalg_obj G)) (der (bool_cone_car Ar)))
    (em_pair_mor (icones_id Ar (coalg_obj G))
                 (adj_phi (bernoulli_kleisli G p Hp_ge0 Hp_le1)))
  = icones_comp
      (tensor_mor (icones_id Ar (coalg_obj G))
                  (const_icones G (@bernoulli R Ar p Hp_ge0 Hp_le1)
                                  (@bernoulli_norm_le1 R Ar p Hp_ge0 Hp_le1)))
      (coalg_d G).
Proof.
rewrite /em_pair_mor.
rewrite icones_compA.
rewrite -(tensor_mor_comp (icones_id Ar (coalg_obj G))
                          (icones_id Ar (coalg_obj G))
                          (der (bool_cone_car Ar))
                          (adj_phi (bernoulli_kleisli G p Hp_ge0 Hp_le1))).
rewrite icones_compIl.
rewrite (der_bernoulli_kleisli_E Hp_ge0 Hp_le1).
by [].
Qed.

(** Step 2: Reduce [(id ⊗ const_icones G c) ∘ coalg_d G]
    to [(id ⊗ linhom_icones (lin_pt c)) ∘ iso_bwd (tensor_runit G)].

    Uses the comonoid right-counit law [emc_counitR]. *)
Lemma case_em_pre_step2 (c : bool_cone_car Ar) (Hc : (cone_norm c <= 1)%R) :
  icones_comp
    (tensor_mor (icones_id Ar (coalg_obj G)) (const_icones G c Hc))
    (coalg_d G)
  = icones_comp
      (tensor_mor (icones_id Ar (coalg_obj G))
                  (linhom_icones (lin_pt c) (lin_pt_norm_le1 c Hc)))
      (iso_bwd (tensor_runit (coalg_obj G))).
Proof.
rewrite /const_icones.
rewrite -[in LHS](icones_compIl (icones_id Ar (coalg_obj G))).
rewrite (tensor_mor_comp (icones_id Ar (coalg_obj G))
                         (icones_id Ar (coalg_obj G))
                         (linhom_icones (lin_pt c) (lin_pt_norm_le1 c Hc))
                         (coalg_e G)).
rewrite -icones_compA.
(* now goal: tensor_mor id (linhom_icones (lin_pt c)) ∘ (tensor_mor id (coalg_e G) ∘ coalg_d G) = ... *)
(* By emc_counitR: iso_fwd (tensor_runit G) ∘ (tensor_mor id (coalg_e G) ∘ coalg_d G) = id.
   So (tensor_mor id (coalg_e G) ∘ coalg_d G) = iso_bwd (tensor_runit G). *)
have HemR : icones_comp (tensor_mor (icones_id Ar (coalg_obj G)) (coalg_e G)) (coalg_d G)
          = iso_bwd (tensor_runit (coalg_obj G)).
  have Hr := emc_counitR (EMComon_all G).
  (* Hr : iso_fwd (tensor_runit (coalg_obj G)) ∘ (tensor_mor id (coalg_e G) ∘ coalg_d G)
          = id_{coalg_obj G}.
     Pre-compose with iso_bwd (tensor_runit) and use iso_fwdK. *)
  rewrite -[in LHS](icones_compIl
                      (icones_comp (tensor_mor (icones_id _ _) (coalg_e G)) (coalg_d G))).
  rewrite -(iso_fwdK (tensor_runit (coalg_obj G))).
  rewrite -icones_compA.
  by rewrite Hr icones_compIr.
by rewrite HemR.
Qed.

(** Pure-tensor evaluation of [case_em_uncurried]: on a [bv ⊗p g] pure
    tensor (where [bv : bool_cone_car Ar] and [g : coalg_obj G]),
    [case_em_uncurried (bv ⊗p g) = bool_case bv (a_lh g) (b_lh g)]. *)
Lemma case_em_uncurried_pure (bv : bool_cone_car Ar) (g : coalg_obj G) :
  Lfun (tensor_uncurry
          (linhom_icones (bool_case_linhom (icones_to_linhom (ch_mor a))
                                            (icones_to_linhom (ch_mor b))
                                            (icones_to_linhom_norm_le1 (ch_mor a))
                                            (icones_to_linhom_norm_le1 (ch_mor b)))
                         (bool_case_linhom_norm_le1
                           (icones_to_linhom (ch_mor a))
                           (icones_to_linhom (ch_mor b))
                           (icones_to_linhom_norm_le1 (ch_mor a))
                           (icones_to_linhom_norm_le1 (ch_mor b)))))
       (ptensor bv g)
  = bool_case bv (icones_to_linhom (ch_mor a) g)
                  (icones_to_linhom (ch_mor b) g).
Proof.
set H_a := icones_to_linhom_norm_le1 (ch_mor a).
set H_b := icones_to_linhom_norm_le1 (ch_mor b).
set case_lh := bool_case_linhom _ _ H_a H_b.
set H_lh := bool_case_linhom_norm_le1 _ _ H_a H_b.
rewrite -(tensor_curryE (tensor_uncurry (linhom_icones case_lh H_lh)) bv g).
rewrite tensor_uncurryK.
by [].
Qed.

(** ** Main lemma — [case_em_bernoulli_under_E] (axiom-free)

    The icones_hom-level identity:
    [case_em_under_der a b ∘ ⟨id_G, adj_phi (bernoulli_kleisli p)⟩
     = convex_icones a b].

    Proof: combine the structural steps [case_em_pre_step1] and
    [case_em_pre_step2] with [der_bernoulli_kleisli_E] to reduce to a
    pointwise [icones_hom_eq] computation.  The pure-tensor case for
    [case_em_uncurried] (= [case_em_uncurried_pure]) finishes off the
    branch evaluation.  [Prop_irrelevance] bridges the [Qed]-opaque
    proof-of-side-condition arguments inside [case_em_uncurried] versus
    [convex_linhom]. *)

Lemma case_em_bernoulli_under_E :
  icones_comp (case_em_under_der a b)
              (em_pair_mor (icones_id Ar (coalg_obj G))
                           (adj_phi (bernoulli_kleisli G p Hp_ge0 Hp_le1)))
  = convex_icones a b Hp_ge0 Hp_le1.
Proof.
rewrite /case_em_under_der /case_em_under.
rewrite -icones_compA -icones_compA -icones_compA.
rewrite case_em_pre_step1.
rewrite (case_em_pre_step2 (@bernoulli_norm_le1 R Ar p Hp_ge0 Hp_le1)).
rewrite /convex_icones.
congr (icones_comp _ _).
apply: icones_hom_eq => g.
have Hinner :
  Lfun (icones_comp
          (tensor_mor (icones_id Ar (coalg_obj G))
                      (linhom_icones (lin_pt (@bernoulli R Ar p Hp_ge0 Hp_le1))
                                     (lin_pt_norm_le1
                                       (@bernoulli R Ar p Hp_ge0 Hp_le1)
                                       (@bernoulli_norm_le1 R Ar p Hp_ge0 Hp_le1))))
          (iso_bwd (tensor_runit (coalg_obj G)))) g
  = ptensor g (@bernoulli R Ar p Hp_ge0 Hp_le1).
  rewrite -[LHS]/(Lfun
                    (tensor_mor (icones_id Ar (coalg_obj G))
                                (linhom_icones (lin_pt (@bernoulli R Ar p Hp_ge0 Hp_le1))
                                               (lin_pt_norm_le1
                                                 (@bernoulli R Ar p Hp_ge0 Hp_le1)
                                                 (@bernoulli_norm_le1 R Ar p Hp_ge0 Hp_le1))))
                    (Lfun (iso_bwd (tensor_runit (coalg_obj G))) g)).
  rewrite tensor_runit_bwdE.
  rewrite tensor_morE.
  rewrite -[Lfun (icones_id _ _) _]/g.
  congr (ptensor g _).
  rewrite -[Lfun (linhom_icones _ _) _]/(linhom_fun (lin_pt (@bernoulli R Ar p Hp_ge0 Hp_le1))
                                                    (c1_one Ar)).
  rewrite -[c1_one Ar]/(MkConeOne Ar 1%:nng).
  exact: lin_pt_unit.
rewrite -[Lfun (icones_comp _ _) _]/(Lfun _ (Lfun _ _)).
rewrite -[Lfun (icones_comp _ _) _]/(Lfun _ (Lfun _ _)).
rewrite Hinner.
rewrite -[Lfun (iso_fwd _) _]/(Lfun (iso_fwd (tensor_braid (coalg_obj G) (bool_cone_car Ar)))
                                    (ptensor g (@bernoulli R Ar p Hp_ge0 Hp_le1))).
rewrite tensor_braidEp.
(* Goal: Lfun case_em_uncurried (bernoulli ⊗p g) = Lfun convex_icones_bang g.
   The case_em_uncurried in the goal involves opaque proofs (Qed lemmas).
   We replace them with their definitional bodies using Prop_irrelevance. *)
have Hpi_a : case_em_a_lh_norm a = icones_to_linhom_norm_le1 (ch_mor a)
  by apply: Prop_irrelevance.
have Hpi_b : case_em_b_lh_norm b = icones_to_linhom_norm_le1 (ch_mor b)
  by apply: Prop_irrelevance.
have Hpi_lh : case_em_lh_norm a b
            = bool_case_linhom_norm_le1 (icones_to_linhom (ch_mor a))
                                         (icones_to_linhom (ch_mor b))
                                         (icones_to_linhom_norm_le1 (ch_mor a))
                                         (icones_to_linhom_norm_le1 (ch_mor b))
  by apply: Prop_irrelevance.
rewrite Hpi_a Hpi_b Hpi_lh.
(* Now the case_em_uncurried in the goal matches the form in case_em_uncurried_pure. *)
rewrite case_em_uncurried_pure.
(* Goal: bool_case bernoulli (a_lh g) (b_lh g) = Lfun convex_icones_bang g *)
rewrite /convex_icones_bang.
rewrite -[Lfun (linhom_icones _ _) g]/(linhom_fun (convex_linhom a b Hp_ge0 Hp_le1) g).
rewrite /convex_linhom.
by [].
Qed.

(** ** The main theorem — [case_em_bernoulli]

    The [coalg_hom]-level reduction:
    [kbind_ext (case_em a b) (bernoulli_kleisli G p ..)
     = convex_combination a b ..].

    Via [adj_phi_inj] and [adj_phi_kbind_ext], reducing to the
    icones_hom identity [case_em_bernoulli_under_E]. *)

Lemma case_em_bernoulli :
  kbind_ext (case_em a b) (bernoulli_kleisli G p Hp_ge0 Hp_le1)
  = convex_combination a b Hp_ge0 Hp_le1.
Proof.
apply: adj_phi_inj.
rewrite (adj_phi_kbind_ext (case_em a b) (bernoulli_kleisli G p Hp_ge0 Hp_le1)).
rewrite /case_em adj_phiK.
rewrite adj_phi_convex_combination.
exact: case_em_bernoulli_under_E.
Qed.

End CaseEmBernoulli.

Arguments case_em_pre_step1 {R Ar G p} Hp_ge0 Hp_le1.
Arguments case_em_pre_step2 {R Ar G c} Hc.
Arguments case_em_uncurried_pure {R Ar G A} a b bv g.
Arguments case_em_bernoulli_under_E {R Ar G A} a b {p} Hp_ge0 Hp_le1.
Arguments case_em_bernoulli {R Ar G A} a b {p} Hp_ge0 Hp_le1.
