(**md *** PPL CBV chapter infrastructure — semantic regression anchors

    BEYOND THE PAPER.  This file is NOT part of the Ehrhard-Geoffroy
    2025 formalization (paper §2-§9).  It pins the OPERATIONAL READING
    of the CBV interpreter [eD] of [theories/programs/ppl_cbv.v] with
    equational anchors, so that a refactor of the §7/§9 cartesian
    machinery ([coalg_d] / [EM_prod_str] / [em_pair_mor]) that silently
    flipped the shared-sample semantics to an independent-product
    semantics would break HERE instead of compiling quietly.

    The anchors:

    - [bool_coalg_d_E] (+ basis corollaries [bool_coalg_d_true] /
      [bool_coalg_d_false]): the Eq-88 comonoid diagonal of the §9.7
      boolean coalgebra [bool_cone_coalg] is the convex combination of
      the DIAGONAL basis tensors,
      [d(x) = bc_t x · (δ_T ⊗ δ_T) + bc_f x · (δ_F ⊗ δ_F)].
    - [coalg_d_FMeas_dirac]: the diagonal of [FMeas_coalgebra X] sends
      a Dirac to its diagonal tensor [δ_r ⊗ δ_r].
    - [let_bernoulli_pair_diag]: the load-bearing SHARED-SAMPLE
      witness — [let x = Bernoulli(p) in (x,x)] denotes
      [p·(δ_T ⊗ δ_T) + (1-p)·(δ_F ⊗ δ_F)], NOT the independent square.
    - [let_sample_pair_diag]: the [FMeas] twin at a Dirac measure —
      [let x = sample δ_{r₀} in (x,x)] denotes [δ_{r₀} ⊗ δ_{r₀}].
      (The general-µ Pettis-integral form [∫ (δ_r ⊗ δ_r) dµ] is the
      let-at-sample integral law, owned by
      [theories/programs/infra/let_sample_law.v]; the Dirac special
      case here is the anchor.)
    - [pair_bernoulli_indep] / [pair_sample_indep]: the CONTRAST —
      [(Bernoulli(p), Bernoulli(p))] (resp. [(sample µ, sample µ)])
      denotes the independent product [bern ⊗ bern] (resp. [µ ⊗ µ]).
      Together with the let-anchors this pins the sharing semantics
      from both sides.
    - [eD_beta]: the β-rule [(λx.M) V = let x := V in M] at the
      [icones_hom] level, via [adj_phiK] + curry/uncurry cancellation.
    - [eD_if_true] / [eD_if_false]: the if-orientation pins
      [if true then M else N = M] (and dually), at the morphism level.

    All anchors are FIX-FREE: no statement involves [ne_fix] (the
    naive zero-seeded iteration is provably the zero linhom —
    [theories/programs/infra/em_fix_value.v::Phi_fun_lfp_eq0] — and
    the same file holds the repaired seeded combinator).

    The supporting kit (setlike-point computations [coalg_d_setlike] /
    [coalg_str_tensor_setlike] / [em_proj1_morE] / [const_iconesE] /
    [em_pair_mor_constE], the pointwise SMC laws [tensor_uncurryE] /
    [tensor_runit_bwdE], and the bool-cone distribution laws) is the
    M4 setlike-point kit of the rejection-sampling plan.  It OWNS the
    four computation laws every CBV rider runs on:

    - [adj_psi_at_setlike] — the [U ⊣ !̃] packaging (the lambda clause)
      PROMOTES at setlike unit-ball points;
    - [if_icones_at] — the if-then-else dispatch computes there;
    - [eD_app_at_setlike] — the application clause computes there
      (Section [ProgramAnchors], generic over the real object);
    - [linhom_fun_sup_ball] — linhom-cone suprema are POINTWISE (on
      [cone_sup_ball_irr] of [theories/cones/omega_general.v]),

    plus the per-branch mass bookkeeping [bool_case_mass].  These used
    to live in [theories/programs/ex_reject_headline.v] §1, which
    inverted the layering (an infra file importing an example file for
    its kit); they are stated here once and instantiated there.

    See also: [theories/programs/ppl_cbv.v] (the interpreter + the
    [eD_*_E] definitional-unfolding pack consumed here),
    [theories/programs/infra/bool_cone_coalg.v] (the §9.7 boolean
    coalgebra), [theories/cbv/em_cartesian.v] (Eq 88 / [EM_prod]). *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals signed constructive_ereal.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import measure dirac_measure numfun.
From mathcomp.analysis Require Import lebesgue_integral_definition.
From mathcomp.analysis Require Import lebesgue_integral_nonneg.

From Stdlib Require Import Strings.String.

Require Import Icones.cones.precone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.cone.
Require Import Icones.cones.cone_cat.
Require Import Icones.cones.omega_general.
Require Import Icones.icones.bool_cone.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.mcones.path.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.icone.
Require Import Icones.icones.examples_icone.
Require Import Icones.icones.icone_cat.
Require Import Icones.stable.scones_cat.
Require Import Icones.stable.scones_ccc.
Require Import Icones.homs.icones_iso.
Require Import Icones.homs.linhom.
Require Import Icones.homs.bilin.
Require Import Icones.homs.tensor.
Require Import Icones.homs.tensor_construct.
Require Import Icones.homs.smcc.
Require Import Icones.exp.exp_adjunction.
Require Import Icones.exp.bang.
Require Import Icones.exp.seely_defs.
Require Import Icones.exp.seely.
Require Import Icones.homs.tensor_hom_iso.
Require Import Icones.exp.bool_case_hom.
Require Import Icones.exp.coalgebra.
Require Import Icones.programs.infra.bool_cone_coalg.
Require Import Icones.cbv.fmeas_lax.
Require Import Icones.cbv.em_cat.
Require Import Icones.cbv.em_seely_comonoid.
Require Import Icones.cbv.em_cartesian.
Require Import Icones.cbv.cbv_adjunction.
Require Import Icones.programs.ppl.
Require Import Icones.programs.infra.em_fix.
Require Import Icones.programs.infra.em_fix_value.
Require Import Icones.programs.ppl_cbv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Opaque tensor_mor tensor_assoc tensor_lunit tensor_runit tensor_braid
       ptensor tau Seely2.
Local Opaque dig der prom bang_fmap d_bang e_bang unit_cofree_str Coalg
       tens_cofree_str m_bang.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** The setlike-point kit

    A point [x] of a coalgebra [(P, str)] is SETLIKE when
    [str x = prom x] — the §9.7 reading "x is a (sub-)Dirac".  On
    setlike unit-ball points the Eq-88 comonoid computes:
    [coalg_d x = x ⊗ x] and [coalg_e x = one1].  The setlike points
    are closed under tensor ([EM_prod]); the unit point [one1], every
    Dirac of [FMeas X], and both boolean Diracs are setlike. *)

Section AnchorKit.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation "B '⊗' C" := (tensor Ar B C)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '!'" := (prom x) (at level 2, format "x '!'").
Local Notation Bg := (@Bang R Ar).

(** The unit point has norm [1]. *)
Lemma one1_norm : cone_norm (one1 : cone_one_car Ar) = 1.
Proof. by rewrite /cone_norm /= /c1_norm. Qed.

(** *** Eq-88 comonoid maps at setlike unit-ball points *)

(** [coalg_d P x = x ⊗ x] when [x] is setlike of norm [≤ 1]. *)
Lemma coalg_d_setlike (P : Coalgebra Ar) (x : coalg_obj P) :
  cone_norm x <= 1 -> Lfun (coalg_str P) x = x! ->
  Lfun (coalg_d P) x = x ⊗p x.
Proof.
move=> Hx Hstr.
rewrite /coalg_d Lfun_comp Lfun_comp Hstr (d_bang_prom x Hx) tensor_morE.
by rewrite (der_prom x Hx).
Qed.

(** [coalg_e P x = one1] when [x] is setlike of norm [≤ 1]. *)
Lemma coalg_e_setlike (P : Coalgebra Ar) (x : coalg_obj P) :
  cone_norm x <= 1 -> Lfun (coalg_str P) x = x! ->
  Lfun (coalg_e P) x = one1.
Proof.
move=> Hx Hstr.
by rewrite /coalg_e Lfun_comp Hstr (e_bang_prom x Hx).
Qed.

(** *** Setlike instances: the unit, Diracs, and tensors *)

(** [one1] is setlike in [EM_term]. *)
Lemma coalg_str_one1 :
  Lfun (coalg_str (EM_term : Coalgebra Ar)) one1 =
  (one1 : cone_one_car Ar)!.
Proof. exact: unit_cofree_str_one1. Qed.

(** Setlike points are closed under the [EM_prod] tensor: the §7.4
    structure map [m ∘ (str ⊗ str)] sends [x ⊗ y] to [(x ⊗ y)!]. *)
Lemma coalg_str_tensor_setlike (P Q : Coalgebra Ar)
    (x : coalg_obj P) (y : coalg_obj Q) :
  cone_norm x <= 1 -> cone_norm y <= 1 ->
  Lfun (coalg_str P) x = x! -> Lfun (coalg_str Q) y = y! ->
  Lfun (coalg_str (EM_prod P Q)) (x ⊗p y) = (x ⊗p y)!.
Proof.
move=> Hx Hy Hsx Hsy.
rewrite EM_prod_str_E /EM_prod_str Lfun_comp tensor_morE Hsx Hsy.
exact: m_bang_prom.
Qed.

(** *** Pointwise SMC computation laws *)

(** Uncurry computes on pure tensors:
    [uncurry(h)(x ⊗ y) = h(x)(y)]. *)
Lemma tensor_uncurryE (B C D : ICone.type Ar)
    (h : icones_hom Ar B (linhom_car Ar C D)) (x : B) (y : C) :
  Lfun (tensor_uncurry h) (x ⊗p y) = linhom_fun (Lfun h x) y.
Proof. by rewrite -(tensor_curryE (tensor_uncurry h) x y) tensor_uncurryK. Qed.

(** The inverse right unitor inserts the unit point:
    [ρ⁻¹(x) = x ⊗ one1]. *)
Lemma tensor_runit_bwdE (A : ICone.type Ar) (x : A) :
  Lfun (iso_bwd (tensor_runit A)) x = x ⊗p one1.
Proof.
apply: (iso_fwd_inj (tensor_runit A)).
by rewrite iso_can'.
Qed.

(** The point evaluator [lin_pt c] at the unit point gives [c]. *)
Lemma lin_pt_one1 (C : ICone.type Ar) (c : C) :
  linhom_fun (lin_pt c) one1 = c.
Proof.
rewrite -[linhom_fun (lin_pt c) one1]/(precone_scale (c1_val one1) c).
by rewrite -[c1_val one1]/(1%:nng) precone_scale_1.
Qed.

(** *** Pure-tensor bilinearity (right-slot additivity) *)

Lemma ptensorDr (B C : ICone.type Ar) (x : B) (y z : C) :
  x ⊗p (precone_add y z) = precone_add (x ⊗p y) (x ⊗p z).
Proof.
rewrite !ptensorE /linhom_fun.
by have [_ -> _] := linhom_pre_linear (linhom_pre_of (tau B C x)).
Qed.

(** *** Projections at pure tensors with a setlike discarded factor *)

Lemma em_proj1_morE (P Q : Coalgebra Ar)
    (x : coalg_obj P) (y : coalg_obj Q) :
  cone_norm y <= 1 -> Lfun (coalg_str Q) y = y! ->
  Lfun (em_proj1_mor P Q) (x ⊗p y) = x.
Proof.
move=> Hy Hsy.
rewrite /em_proj1_mor Lfun_comp tensor_morE (coalg_e_setlike Hy Hsy).
rewrite -[Lfun (icones_id Ar (coalg_obj P)) x]/x tensor_runitEp.
by rewrite -[c1_val one1]/(1%:nng) precone_scale_1.
Qed.

Lemma em_proj2_morE (P Q : Coalgebra Ar)
    (x : coalg_obj P) (y : coalg_obj Q) :
  cone_norm x <= 1 -> Lfun (coalg_str P) x = x! ->
  Lfun (em_proj2_mor P Q) (x ⊗p y) = y.
Proof.
move=> Hx Hsx.
rewrite /em_proj2_mor Lfun_comp tensor_morE (coalg_e_setlike Hx Hsx).
rewrite -[Lfun (icones_id Ar (coalg_obj Q)) y]/y tensor_lunitEp.
by rewrite -[c1_val one1]/(1%:nng) precone_scale_1.
Qed.

(** *** Constants and pairing-with-a-constant *)

(** [const_icones Z c] evaluates to [c] at setlike unit-ball points. *)
Lemma const_iconesE (Z : Coalgebra Ar) (C : ICone.type Ar) (c : C)
    (Hc : cone_norm c <= 1) (g : coalg_obj Z) :
  cone_norm g <= 1 -> Lfun (coalg_str Z) g = g! ->
  Lfun (const_icones Z c Hc) g = c.
Proof.
move=> Hg Hsg.
rewrite /const_icones Lfun_comp (coalg_e_setlike Hg Hsg).
by rewrite linhom_iconesE lin_pt_one1.
Qed.

(** Discarding one comonoid copy collapses the diagonal:
    [(id ⊗ ε) ∘ d = ρ⁻¹] (the [emc_counitR] law re-oriented). *)
Lemma em_pair_mor_id_counit (Z : Coalgebra Ar) :
  icones_comp
    (tensor_mor (icones_id Ar (coalg_obj Z)) (coalg_e Z)) (coalg_d Z) =
  iso_bwd (tensor_runit (coalg_obj Z)).
Proof.
have H2 := congr1 (icones_comp (iso_bwd (tensor_runit (coalg_obj Z))))
  (emc_counitR (EMComon_all Z)).
rewrite icones_compA (iso_fwdK (tensor_runit (coalg_obj Z)))
  icones_compIl icones_compIr in H2.
exact: H2.
Qed.

(** The key computation rule: pairing the identity with a constant computes at
    EVERY point — [⟨id, const c⟩(γ) = γ ⊗ c] — because the discarded
    diagonal copy is erased by the comonoid counit law, with no
    setlike hypothesis on [γ]. *)
Lemma em_pair_mor_constE (Z Q : Coalgebra Ar) (c : coalg_obj Q)
    (Hc : cone_norm c <= 1) (g : coalg_obj Z) :
  Lfun (em_pair_mor (icones_id Ar (coalg_obj Z)) (const_icones Z c Hc)) g =
  g ⊗p c.
Proof.
rewrite /em_pair_mor /const_icones.
rewrite -[X in tensor_mor X _](icones_compIr (icones_id Ar (coalg_obj Z))).
rewrite (tensor_mor_comp (icones_id Ar (coalg_obj Z))
  (icones_id Ar (coalg_obj Z))
  (linhom_icones (lin_pt c) (lin_pt_norm_le1 c Hc)) (coalg_e Z)).
rewrite -icones_compA em_pair_mor_id_counit.
rewrite Lfun_comp tensor_runit_bwdE tensor_morE.
rewrite -[Lfun (icones_id Ar (coalg_obj Z)) g]/g.
by rewrite linhom_iconesE lin_pt_one1.
Qed.

(** *** Bool-cone distribution laws *)

(** The [bool_case_linhom] packaging computes to [bool_case]. *)
Lemma bool_case_linhomE (A : ICone.type Ar) (a b : A)
    (Ha : cone_norm a <= 1) (Hb : cone_norm b <= 1)
    (x : bool_cone_car Ar) :
  linhom_fun (bool_case_linhom a b Ha Hb) x = bool_case x a b.
Proof. by []. Qed.

(** Any [icones_hom] distributes over the boolean co-pairing. *)
Lemma Lfun_bool_case (B C : ICone.type Ar) (h : icones_hom Ar B C)
    (b : bool_cone_car Ar) (u v : B) :
  Lfun h (bool_case b u v) = bool_case b (Lfun h u) (Lfun h v).
Proof.
have [_ HD HZ] : is_linear (Lfun h) := cones_hom_linear _.
rewrite /bool_case HD.
by rewrite !HZ.
Qed.

(** The pure tensor distributes over a boolean right factor. *)
Lemma ptensor_caseR (B : ICone.type Ar) (x : B) (b : bool_cone_car Ar) :
  x ⊗p b =
  bool_case b (x ⊗p bool_dirac_true) (x ⊗p bool_dirac_false).
Proof.
rewrite {1}(bool_cone_basis_expand b) /bool_case ptensorDr.
by rewrite !ptensorZr.
Qed.

(** *** The mass of a boolean dispatch between a Dirac and a measure

    [bool_case b δ_r ν] is the sub-probability mixture
    [(bc_t b)·δ_r + (bc_f b)·ν]; its mass at a measurable [U] is the
    scalar mixture of the indicator [\1_U r] and of [ν U].  Every
    rejection rider's per-branch mass bookkeeping is an instance
    ([bc_t]/[bc_f] of a [bernoulli p] read as [p]/[1-p]). *)
Lemma bool_case_mass (X : ar_obj Ar) (b : bool_cone_car Ar)
    (r : ar_carrier Ar X) (nu : fmeas R (ar_carrier Ar X))
    (U : set (ar_carrier Ar X)) :
  measurable U ->
  fmeas_mu (bool_case b (dirac_fmeas r) nu : fmeas R (ar_carrier Ar X)) U =
  (((bc_t b)%:num * \1_U r +
    (bc_f b)%:num * fine (fmeas_mu nu U))%R)%:E.
Proof.
move=> mU.
have -> : (bool_case b (dirac_fmeas r) nu : fmeas R (ar_carrier Ar X)) =
  fmeas_add (fmeas_scale (bc_t b) (dirac_fmeas r)) (fmeas_scale (bc_f b) nu).
  by [].
rewrite fmeas_addE 2!fmeas_scaleE (dirac_fmeas_E r mU) diracE/=.
rewrite -(fineK (fmeas_fin nu U mU)).
by rewrite -2!EFinM -EFinD indicE.
Qed.

(** *** The [U ⊣ !̃] packaging, the if-dispatch, and pointwise sups

    The three laws every CBV rider runs on: the lambda clause PROMOTES
    at a setlike environment, the if-clause DISPATCHES there, and the
    Kleene supremum of a chain of linear maps is read POINTWISE. *)

(** The [U ⊣ !̃] packaging [adj_psi g] PROMOTES at setlike unit-ball
    points: [adj_psi(g)(γ) = (g γ)!]. *)
Lemma adj_psi_at_setlike (P : Coalgebra Ar) (B : ICone.type Ar)
    (g : icones_hom Ar (coalg_obj P) B) (gam : coalg_obj P) :
  cone_norm gam <= 1 ->
  Lfun (coalg_str P) gam = gam! ->
  Lfun (ch_mor (adj_psi (P := P) g)) gam = (Lfun g gam)!.
Proof.
move=> Hg Hs.
have -> : ch_mor (adj_psi (P := P) g) =
    icones_comp (bang_fmap g) (coalg_str P) by [].
rewrite (Lfun_comp (bang_fmap g) (coalg_str P) gam) Hs.
exact: (bang_fmap_prom g _ Hg).
Qed.

(** The if-then-else dispatch computes at setlike unit-ball points:
    [⟦if b then m else n⟧(γ) = bool_case (b γ) (m γ) (n γ)] — the
    weighted co-pairing of the two branches by the scrutinee's
    sub-probability. *)
Lemma if_icones_at (G A : Coalgebra Ar)
    (m n : icones_hom Ar (coalg_obj G) (coalg_obj A))
    (b : icones_hom Ar (coalg_obj G) (coalg_obj (@bool_cone_coalg R Ar)))
    (gam : coalg_obj G) :
  cone_norm gam <= 1 ->
  Lfun (coalg_str G) gam = gam! ->
  Lfun (if_icones m n b) gam =
  bool_case (Lfun b gam) (Lfun m gam) (Lfun n gam).
Proof.
move=> Hg Hs.
rewrite /if_icones Lfun_comp.
rewrite /em_pair_mor (Lfun_comp
  (tensor_mor (icones_id Ar (coalg_obj G)) b) (coalg_d G) gam).
rewrite (coalg_d_setlike Hg Hs) tensor_morE icones_idE.
rewrite /if_under (Lfun_comp (tensor_uncurry _)
  (iso_fwd (tensor_braid (coalg_obj G) (bool_cone_car Ar)))
  (gam ⊗p Lfun b gam)).
rewrite tensor_braidEp tensor_uncurryE.
by rewrite linhom_iconesE bool_case_linhomE.
Qed.

(** Every Kleene iterate of a unit-ball body endofunction [F : !L ⊸ !L]
    promotes to a unit-ball point of the cofree coalgebra [!L], and is
    setlike there ([dig] computes on promoted points).  Every rider's
    per-iterate environment tower is built from this pair. *)
Lemma kleene_prom_ball (L : ICone.type Ar)
    (F : linhom_car Ar (Bg L) (Bg L)) (HF : cone_norm F <= 1) (n : nat) :
  cone_norm ((fix_chain F n)!) <= 1.
Proof. exact: prom_ball (fix_chain_ball HF n). Qed.

Lemma kleene_prom_setlike (L : ICone.type Ar)
    (F : linhom_car Ar (Bg L) (Bg L)) (HF : cone_norm F <= 1) (n : nat) :
  Lfun (coalg_str (bang_cofree L)) ((fix_chain F n)!) =
  ((fix_chain F n)!)!.
Proof.
by rewrite bang_cofree_str; exact: (dig_prom _ (fix_chain_ball HF n)).
Qed.

(** The same pair for the LIMIT of that chain: the seeded fixpoint
    VALUE of a unit-ball body endofunction promotes to a unit-ball
    point of [!L] and is setlike there.  This is what every [let rec]
    rider's continuation environment [one1 ⊗p (fix_value F)!] is built
    from, exactly as its per-iterate tower is built from
    [kleene_prom_ball] / [kleene_prom_setlike]. *)
Lemma fix_value_prom_ball (L : ICone.type Ar)
    (F : linhom_car Ar (Bg L) (Bg L)) (HF : cone_norm F <= 1) :
  cone_norm ((sc_fun (fix_value L) F)!) <= 1.
Proof. exact: prom_ball (fix_value_ball F HF). Qed.

Lemma fix_value_prom_setlike (L : ICone.type Ar)
    (F : linhom_car Ar (Bg L) (Bg L)) (HF : cone_norm F <= 1) :
  Lfun (coalg_str (bang_cofree L)) ((sc_fun (fix_value L) F)!) =
  ((sc_fun (fix_value L) F)!)!.
Proof.
by rewrite bang_cofree_str; exact: (dig_prom _ (fix_value_ball F HF)).
Qed.

(** Linhom-cone suprema are POINTWISE: evaluating the ball-sup of a
    chain of linear maps at a unit-ball point is the ball-sup of the
    evaluations (for any witnesses of the evaluated chain).  The
    proof-irrelevance it rests on is [cone_sup_ball_irr] of
    [theories/cones/omega_general.v]. *)
Lemma linhom_fun_sup_ball (C D : ICone.type Ar)
    (u : nat -> linhom_car Ar C D)
    (uch : forall n, precone_le (u n) (u n.+1))
    (ub1 : forall n, cone_norm (u n) <= 1)
    (x : C) (Hx : cone_norm x <= 1)
    (pwch : forall n,
        precone_le (linhom_fun (u n) x) (linhom_fun (u n.+1) x))
    (pwub : forall n, cone_norm (linhom_fun (u n) x) <= 1) :
  linhom_fun (cone_sup_ball u uch ub1) x =
  cone_sup_ball (fun n => linhom_fun (u n) x) pwch pwub.
Proof.
have -> : cone_sup_ball u uch ub1 = linhom_sup_ball u uch ub1 by [].
have -> : linhom_fun (linhom_sup_ball u uch ub1) x
          = linhom_sup_fun uch ub1 x by [].
rewrite (linhom_sup_fun_unitE uch ub1 Hx) (linhom_sup_unitE uch ub1 Hx).
exact: cone_sup_ball_irr.
Qed.

(** ** Anchor 1 — the §9.7 boolean comonoid diagonal is DIAGONAL

    [coalg_d bool_cone_coalg] sends a sub-probability [x = (p, q)] to
    the convex combination of the DIAGONAL basis tensors — the
    shared-sample semantics.  (The independent-product reading would
    give [x ⊗ x] instead, with cross terms [p·q · (δ_T ⊗ δ_F)] etc.) *)

(** Basis corollary: [d(δ_T) = δ_T ⊗ δ_T]. *)
Lemma bool_coalg_d_true :
  Lfun (coalg_d (@bool_cone_coalg R Ar)) bool_dirac_true =
  bool_dirac_true ⊗p bool_dirac_true.
Proof.
apply: coalg_d_setlike; first exact: bool_dirac_true_norm_le1.
exact: bool_coalg_str_true.
Qed.

(** Basis corollary: [d(δ_F) = δ_F ⊗ δ_F]. *)
Lemma bool_coalg_d_false :
  Lfun (coalg_d (@bool_cone_coalg R Ar)) bool_dirac_false =
  bool_dirac_false ⊗p bool_dirac_false.
Proof.
apply: coalg_d_setlike; first exact: bool_dirac_false_norm_le1.
exact: bool_coalg_str_false.
Qed.

(** The full diagonal:
    [d(x) = bc_t x · (δ_T ⊗ δ_T) + bc_f x · (δ_F ⊗ δ_F)]
    (stated through the weighted co-pairing [bool_case]). *)
Lemma bool_coalg_d_E (x : bool_cone_car Ar) :
  Lfun (coalg_d (@bool_cone_coalg R Ar)) x =
  bool_case x (bool_dirac_true ⊗p bool_dirac_true)
              (bool_dirac_false ⊗p bool_dirac_false).
Proof.
rewrite {1}(bool_cone_basis_expand x) Lfun_bool_case.
by rewrite bool_coalg_d_true bool_coalg_d_false.
Qed.

(** ** Anchor 2 — the [FMeas] comonoid diagonal on Diracs

    [coalg_d (FMeas_coalgebra X)] sends [δ_r] to [δ_r ⊗ δ_r]: the §9.7
    coalgebra duplicates a SAMPLE, not the measure. *)
Lemma coalg_d_FMeas_dirac (X : ar_obj Ar) (r : ar_carrier Ar X) :
  Lfun (coalg_d (FMeas_coalgebra X)) (dirac_fmeas r) =
  dirac_fmeas r ⊗p dirac_fmeas r.
Proof.
apply: coalg_d_setlike; first exact: dirac_fmeas_norm_le1.
exact: Coalg_dirac.
Qed.

End AnchorKit.

Arguments one1_norm {R Ar}.
Arguments coalg_d_setlike {R Ar P x}.
Arguments coalg_e_setlike {R Ar P x}.
Arguments coalg_str_one1 {R Ar}.
Arguments coalg_str_tensor_setlike {R Ar P Q x y}.
Arguments tensor_uncurryE {R Ar B C D} h x y.
Arguments tensor_runit_bwdE {R Ar A} x.
Arguments lin_pt_one1 {R Ar C} c.
Arguments ptensorDr {R Ar B C} x y z.
Arguments em_proj1_morE {R Ar P Q x y}.
Arguments em_proj2_morE {R Ar P Q x y}.
Arguments const_iconesE {R Ar Z C c Hc g}.
Arguments em_pair_mor_id_counit {R Ar} Z.
Arguments em_pair_mor_constE {R Ar Z Q c} Hc g.
Arguments bool_case_linhomE {R Ar A} a b Ha Hb x.
Arguments Lfun_bool_case {R Ar B C} h b u v.
Arguments ptensor_caseR {R Ar B} x b.
Arguments bool_case_mass {R Ar X} b r nu {U}.
Arguments adj_psi_at_setlike {R Ar P B} g {gam}.
Arguments if_icones_at {R Ar G A} m n b {gam}.
Arguments kleene_prom_ball {R Ar L F} HF n.
Arguments kleene_prom_setlike {R Ar L F} HF n.
Arguments linhom_fun_sup_ball {R Ar C D u} uch ub1 {x} Hx pwch pwub.
Arguments bool_coalg_d_true {R Ar}.
Arguments bool_coalg_d_false {R Ar}.
Arguments bool_coalg_d_E {R Ar} x.
Arguments coalg_d_FMeas_dirac {R Ar X} r.

(** ** Program-level anchors

    The anchors on closed PPL programs, against the public CBV
    interpreter [eD] of [ppl_cbv.v].  Every clause unfolding goes
    through the [eD_*_E] pack of [ppl_cbv.v::Section EDUnfold] — never
    re-derived. *)

Section ProgramAnchors.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation "B '⊗' C" := (tensor Ar B C)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '⊗p' y" := (ptensor x y)
  (at level 40, left associativity) : ring_scope.
Local Notation "x '!'" := (prom x) (at level 2, format "x '!'").

Local Notation eD_cbv' :=
  (@eD_cbv R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation eD' :=
  (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation Lty t1 t2 :=
  (linhom_car Ar (coalg_obj (tyD_cbv t1)) (coalg_obj (tyD_cbv t2))).

(** *** The application clause at a setlike point

    Generic over the real object and its carrier casts, so that every
    example rider — [probObj]-parameterised or not — shares it. *)
Lemma eD_app_at_setlike (G : named_ctx Ar) (t1 t2 : ppl_type Ar)
    (F : @named_expr R Ar R_obj G (tfun t1 t2))
    (X : @named_expr R Ar R_obj G t1)
    (gam : coalg_obj (ctxD_cbv (drop_names G))) :
  cone_norm gam <= 1 ->
  Lfun (coalg_str (ctxD_cbv (drop_names G))) gam = gam! ->
  Lfun (eD_cbv' (ne_app F X)) gam =
  linhom_fun (Lfun (der (Lty t1 t2)) (Lfun (eD_cbv' F) gam))
             (Lfun (eD_cbv' X) gam).
Proof.
move=> Hg Hs.
rewrite eD_app_E.
rewrite (Lfun_comp (tensor_uncurry (icones_id Ar (Lty t1 t2)))
  (icones_comp
    (tensor_mor (der (Lty t1 t2)) (icones_id Ar (coalg_obj (tyD_cbv t1))))
    (em_pair_mor (eD_cbv' F) (eD_cbv' X))) gam).
rewrite (Lfun_comp
  (tensor_mor (der (Lty t1 t2)) (icones_id Ar (coalg_obj (tyD_cbv t1))))
  (em_pair_mor (eD_cbv' F) (eD_cbv' X)) gam).
rewrite /em_pair_mor (Lfun_comp (tensor_mor (eD_cbv' F) (eD_cbv' X))
  (coalg_d (ctxD_cbv (drop_names G))) gam).
rewrite (coalg_d_setlike Hg Hs) tensor_morE tensor_morE icones_idE.
by rewrite tensor_uncurryE icones_idE.
Qed.

(** *** The shared-variable pair [(x, x)] in a one-variable context *)

(** [(#"x", #"x")] over the context [(x, t) :: nil]. *)
Definition anchor_var_pair (x : string) (t : ppl_type Ar) :
    @named_expr R Ar R_obj ((x, t) :: nil) (tprod t t) :=
  ne_pair (ne_var (nv_head x t nil)) (ne_var (nv_head x t nil))%string.

(** At a setlike unit-ball value [y] for the bound variable, the
    shared pair evaluates to the DIAGONAL tensor [y ⊗ y]. *)
Lemma var_pair_diag_at (x : string) (t : ppl_type Ar)
    (y : coalg_obj (tyD_cbv t)) :
  cone_norm y <= 1 ->
  Lfun (coalg_str (tyD_cbv t)) y = y! ->
  Lfun (eD_cbv' (anchor_var_pair x t)) (one1 ⊗p y) = y ⊗p y.
Proof.
move=> Hy Hsy.
have Hone : cone_norm (one1 : cone_one_car Ar) <= 1 by rewrite one1_norm.
rewrite /anchor_var_pair eD_pair_E /em_pair_mor Lfun_comp.
have Hball : cone_norm (one1 ⊗p y) <= 1.
  by rewrite tensor_normME one1_norm mul1r.
have Hstr : Lfun (coalg_str (ctxD_cbv (drop_names ((x, t) :: nil))))
              (one1 ⊗p y) = (one1 ⊗p y)!.
  exact: (coalg_str_tensor_setlike (P:=EM_term) (Q:=tyD_cbv t)
            Hone Hy coalg_str_one1 Hsy).
rewrite (coalg_d_setlike (P:=ctxD_cbv (drop_names ((x, t) :: nil)))
           Hball Hstr) tensor_morE.
have -> : Lfun (eD_cbv' (ne_var (nv_head x t nil))) (one1 ⊗p y) = y.
  rewrite eD_var_E.
  exact: (em_proj2_morE (P:=EM_term) (Q:=tyD_cbv t) Hone coalg_str_one1).
by [].
Qed.

(** *** Anchor 3a — shared Bernoulli sample (THE load-bearing witness)

    [let x := Bernoulli(p) in (x, x)] denotes
    [p · (δ_T ⊗ δ_T) + (1-p) · (δ_F ⊗ δ_F)]
    — the diagonal pushforward, NOT the independent square. *)

Definition anchor_let_bern (p : R)
    (Hp0 : 0 <= p) (Hp1 : p <= 1) :
    @named_expr R Ar R_obj nil (tprod tbool tbool) :=
  ne_let "x"%string (ne_bernoulli (G := nil) p Hp0 Hp1)
    (anchor_var_pair "x" tbool).

Lemma let_bernoulli_pair_diag (p : R) (Hp0 : 0 <= p) (Hp1 : p <= 1) :
  linhom_fun (eD' (anchor_let_bern Hp0 Hp1)) one1 =
  bool_case (bernoulli (Ar:=Ar) p Hp0 Hp1)
    (bool_dirac_true ⊗p bool_dirac_true)
    (bool_dirac_false ⊗p bool_dirac_false).
Proof.
rewrite /eD icones_to_linhomE /anchor_let_bern eD_let_E Lfun_comp.
rewrite eD_bernoulli_E /bernoulli_icones em_pair_mor_constE.
rewrite (ptensor_caseR one1 (bernoulli p Hp0 Hp1)) Lfun_bool_case.
rewrite (var_pair_diag_at "x"%string (t:=tbool)
  bool_dirac_true_norm_le1 bool_coalg_str_true).
rewrite (var_pair_diag_at "x"%string (t:=tbool)
  bool_dirac_false_norm_le1 bool_coalg_str_false).
by [].
Qed.

(** The same identity in explicit weighted-sum form. *)
Lemma let_bernoulli_pair_diag_scale (p : R)
    (Hp0 : 0 <= p) (Hp1 : p <= 1) :
  linhom_fun (eD' (anchor_let_bern Hp0 Hp1)) one1 =
  precone_add
    (precone_scale (NngNum Hp0)
       (bool_dirac_true ⊗p bool_dirac_true))
    (precone_scale (NngNum (subr_ge0_le1 p Hp1))
       (bool_dirac_false ⊗p bool_dirac_false)).
Proof. by rewrite let_bernoulli_pair_diag. Qed.

(** *** Anchor 3b — shared [FMeas] sample at a Dirac measure

    [let x := sample δ_{r₀} in (x, x)] denotes [δ_{r₀} ⊗ δ_{r₀}].
    This is the Dirac special case of the let-at-sample integral law
    [⟦let x = sample µ in (x,x)⟧ = ∫ (δ_r ⊗ δ_r) dµ(r)]; the general-µ
    Pettis form is owned by [infra/let_sample_law.v]. *)

Definition anchor_let_sample_dirac (r0 : ar_carrier Ar R_obj) :
    @named_expr R Ar R_obj nil (tprod (tR R_obj) (tR R_obj)) :=
  ne_let "x"%string
    (ne_sample (G := nil) (dirac_fmeas r0) (dirac_fmeas_norm_le1 r0))
    (anchor_var_pair "x" (tR R_obj)).

Lemma let_sample_pair_diag (r0 : ar_carrier Ar R_obj) :
  linhom_fun (eD' (anchor_let_sample_dirac r0)) one1 =
  dirac_fmeas r0 ⊗p dirac_fmeas r0.
Proof.
rewrite /eD icones_to_linhomE /anchor_let_sample_dirac eD_let_E Lfun_comp.
rewrite eD_sample_E /sample_icones em_pair_mor_constE.
exact: (var_pair_diag_at "x"%string (t:=tR R_obj)
          (dirac_fmeas_norm_le1 r0) (Coalg_dirac R_obj r0)).
Qed.

(** *** Anchor 3c — the independence CONTRAST

    Two SEPARATE samples form the independent product: together with
    3a/3b this pins the sharing semantics from both sides. *)

Lemma pair_bernoulli_indep (p : R) (Hp0 : 0 <= p) (Hp1 : p <= 1) :
  linhom_fun
    (eD' (ne_pair (ne_bernoulli (G := nil) p Hp0 Hp1)
                  (ne_bernoulli (G := nil) p Hp0 Hp1))) one1 =
  bernoulli (Ar:=Ar) p Hp0 Hp1 ⊗p bernoulli (Ar:=Ar) p Hp0 Hp1.
Proof.
rewrite /eD icones_to_linhomE eD_pair_E /em_pair_mor Lfun_comp.
have Hone : cone_norm (one1 : cone_one_car Ar) <= 1 by rewrite one1_norm.
rewrite (coalg_d_setlike (P:=ctxD_cbv (drop_names (nil : named_ctx Ar)))
  Hone coalg_str_one1) tensor_morE.
rewrite eD_bernoulli_E /bernoulli_icones.
by rewrite (const_iconesE (Z:=ctxD_cbv (drop_names (nil : named_ctx Ar)))
  Hone coalg_str_one1).
Qed.

Lemma pair_sample_indep (mu : fmeas R (ar_carrier Ar R_obj))
    (Hmu : cone_norm mu <= 1) :
  linhom_fun
    (eD' (ne_pair (ne_sample (G := nil) mu Hmu)
                  (ne_sample (G := nil) mu Hmu))) one1 =
  mu ⊗p mu.
Proof.
rewrite /eD icones_to_linhomE eD_pair_E /em_pair_mor Lfun_comp.
have Hone : cone_norm (one1 : cone_one_car Ar) <= 1 by rewrite one1_norm.
rewrite (coalg_d_setlike (P:=ctxD_cbv (drop_names (nil : named_ctx Ar)))
  Hone coalg_str_one1) tensor_morE.
rewrite eD_sample_E /sample_icones.
by rewrite (const_iconesE (Z:=ctxD_cbv (drop_names (nil : named_ctx Ar)))
  Hone coalg_str_one1).
Qed.

(** *** Anchor 4 — the β-rule

    [(λx.M) V = let x := V in M] at the [icones_hom] level.  The [!̃]
    round trip [der ∘ !(curry M) ∘ str] collapses by [adj_phiK]; the
    curry/uncurry round trip collapses by [tensor_uncurry_natL] +
    [tensor_curryK]. *)
Lemma eD_beta (G : named_ctx Ar) (x : string) (t1 t2 : ppl_type Ar)
    (M : @named_expr R Ar R_obj ((x, t1) :: G) t2)
    (V : @named_expr R Ar R_obj G t1) :
  eD_cbv' (ne_app (ne_lam x M) V) = eD_cbv' (ne_let x V M).
Proof.
rewrite eD_app_E eD_lam_E eD_let_E /em_pair_mor.
set L := linhom_car Ar (coalg_obj (tyD_cbv t1)) (coalg_obj (tyD_cbv t2)).
(* LHS: eval ∘ ((der ⊗ id) ∘ ((ψ ⊗ V̂) ∘ d)) — fuse (der⊗id)∘(ψ⊗V̂). *)
rewrite (icones_compA (tensor_mor (der L)
  (icones_id Ar (coalg_obj (tyD_cbv t1))))).
rewrite -(tensor_mor_comp (der L)
  (ch_mor (adj_psi (tensor_curry (eD_cbv' M))))
  (icones_id Ar (coalg_obj (tyD_cbv t1))) (eD_cbv' V)).
rewrite icones_compIl.
(* der ∘ ch_mor (adj_psi g) = adj_phi (adj_psi g) = g. *)
rewrite -[icones_comp (der L) (ch_mor (adj_psi (tensor_curry (eD_cbv' M))))]
        /(adj_phi (adj_psi (tensor_curry (eD_cbv' M)))).
rewrite adj_phiK.
(* split curryM ⊗ V̂ = (curryM ⊗ id) ∘ (id ⊗ V̂). *)
rewrite -[X in tensor_mor X _](icones_compIr (tensor_curry (eD_cbv' M))).
rewrite -[X in tensor_mor _ X](icones_compIl (eD_cbv' V)).
rewrite (tensor_mor_comp (tensor_curry (eD_cbv' M))
  (icones_id Ar (coalg_obj (ctxD_cbv (drop_names G))))
  (icones_id Ar (coalg_obj (tyD_cbv t1))) (eD_cbv' V)).
(* regroup so eval ∘ (curryM ⊗ id) is exposed, then collapse. *)
rewrite icones_compA (icones_compA (tensor_uncurry (icones_id Ar L))).
rewrite (tensor_uncurry_natL (tensor_curry (eD_cbv' M)) (icones_id Ar L)).
rewrite icones_compIl tensor_curryK.
by rewrite -icones_compA.
Qed.

(** *** Anchor 5 — if-orientation pins

    [if true then M else N = M] and [if false then M else N = N], at
    the morphism ([icones_hom]) level.  The constant scrutinee erases
    the diagonal copy via [em_pair_mor_constE]; the dispatch computes
    by [bool_case_true]/[bool_case_false]. *)

Lemma eD_if_true (G : named_ctx Ar) (t : ppl_type Ar)
    (M N : @named_expr R Ar R_obj G t) :
  eD_cbv' (ne_if t ne_true M N) = eD_cbv' M.
Proof.
rewrite eD_if_E eD_true_E /if_icones /true_icones.
apply: icones_hom_eq => g.
rewrite Lfun_comp em_pair_mor_constE /if_under Lfun_comp.
rewrite tensor_braidEp tensor_uncurryE linhom_iconesE bool_case_linhomE.
by rewrite bool_case_true icones_to_linhomE.
Qed.

Lemma eD_if_false (G : named_ctx Ar) (t : ppl_type Ar)
    (M N : @named_expr R Ar R_obj G t) :
  eD_cbv' (ne_if t ne_false M N) = eD_cbv' N.
Proof.
rewrite eD_if_E eD_false_E /if_icones /false_icones.
apply: icones_hom_eq => g.
rewrite Lfun_comp em_pair_mor_constE /if_under Lfun_comp.
rewrite tensor_braidEp tensor_uncurryE linhom_iconesE bool_case_linhomE.
by rewrite bool_case_false icones_to_linhomE.
Qed.

End ProgramAnchors.

Arguments eD_app_at_setlike {R Ar R_obj} R_carrier_eq R_carrier_meas
  R_to_carrier_meas {G t1 t2 F X gam}.
Arguments anchor_var_pair {R Ar R_obj} x t.
Arguments var_pair_diag_at
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} x t {y}.
Arguments anchor_let_bern {R Ar R_obj p} Hp0 Hp1.
Arguments let_bernoulli_pair_diag
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas p} Hp0 Hp1.
Arguments let_bernoulli_pair_diag_scale
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas p} Hp0 Hp1.
Arguments anchor_let_sample_dirac {R Ar R_obj} r0.
Arguments let_sample_pair_diag
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} r0.
Arguments pair_bernoulli_indep
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas p} Hp0 Hp1.
Arguments pair_sample_indep
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas} mu Hmu.
Arguments eD_beta
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G} x {t1 t2} M V.
Arguments eD_if_true
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G t} M N.
Arguments eD_if_false
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G t} M N.
