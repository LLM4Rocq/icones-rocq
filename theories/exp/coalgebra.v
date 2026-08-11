(**md**************************************************************************)
(** * The [!]-coalgebra structure of [FMeas(X)] — Paper Theorem 9.7

    Paper §9, "The coalgebra structure of [Cmeas(X)]"
    ([th:meas-cone-coalgebra-stab]).  For each measurable space [X]
    (object of [ARCAT = Ar]), the integrable cone [FMeas(X)] (paper
    [Cmeas(X)]) carries a [!]-coalgebra structure for the exponential
    comonad [(!, der, dig)] of [bang.v], and the assignment
    [X ↦ (FMeas X, Coalg_X)] is a functor [ARCAT → EM(ICones)] into the
    Eilenberg–Moore category of [!].

    This milestone is AXIOM-FREE and independent of the tensor [⊗] /
    Seely: [Bang] is the proved SAFT construction ([bang_construct.v],
    re-exported by [exp_adjunction.v]), and the integration / Dirac-path
    layer of [bilin.v] (Theorem 6.1) is axiom-free.

    Contents:
    - [FMeas X] — the integrable cone [fmeas R (ar_carrier Ar X)].
    - [bang_dirac_path X] — the measurable path [r ↦ (δ_X r)!] in
      [Path(X, !FMeas(X))], the composite [prom ∘ dirac_path].
    - [Coalg X] — the coalgebra map [FMeas(X) ⊸ !FMeas(X)], obtained
      from [bang_dirac_path] by Theorem 6.1 ([int_to_linhom]) and
      packaged as an [icones_hom] via [linhom_icones]; with the
      computation law [Coalg_dirac]: [Coalg_X(δ_X r) = (δ_X r)!].
    - [dirac_dense] — Paper [th:dirac-dense]: two [icones_hom] out of
      [FMeas(X)] agreeing on every [δ_X r] are equal.  The proof engine.
    - [Coalg_counit] / [Coalg_coassoc] — the two coalgebra laws.
    - [Coalgebra] / [coalg_mor] — a minimal [!]-coalgebra record over
      [Bang_comonad] and its Eilenberg–Moore morphisms.
    - [FMeas_coalgebra X] — the coalgebra carried by [FMeas(X)].
    - [FMeas_fmap φ] (pushforward) is a coalgebra morphism, giving the
      functor [FMeas : ARCAT → EM(ICones)] ([FMeas_em_functor]).

    Paper reference: Theorem 9.7 + proof and [th:dirac-dense]. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals constructive_ereal.
From mathcomp.analysis Require Import ereal.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import measure dirac_measure.
From mathcomp.analysis Require Import lebesgue_integral_definition.

Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.cone_cat.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.mcones.path.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_integral.
Require Import Icones.icones.examples_icone.
Require Import Icones.icones.icone_cat.
Require Import Icones.homs.linhom.
Require Import Icones.homs.bilin.
Require Import Icones.homs.tensor_hom_iso.
Require Import Icones.stable.totmono.
Require Import Icones.stable.scones_cat.
Require Import Icones.exp.exp_adjunction.
Require Import Icones.exp.bang.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Import Icones_tensor_hom_iso.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section Coalgebra.
Variables (R : realType) (Ar : MeasSubcat R).

(** ** The integrable cone [FMeas(X)]

    The carrier [fmeas R (ar_carrier Ar X)] (paper [Cmeas(X)]); its
    canonical [ICone] structure (Lemma 4.13) is resolved by unification
    wherever an [ICone.type Ar] is expected, exactly as in [bilin.v]. *)
Definition FMeas (X : ar_obj Ar) : ICone.type Ar :=
  fmeas R (ar_carrier Ar X).

(** Underlying linear function of an [icones_hom] (same chain as
    [bang.v]). *)
Local Notation Lfun h := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

(** Composition computes pointwise: [Lfun (g ∘ f) x = Lfun g (Lfun f x)]
    (definitional, since [icones_comp] is function composition).  Stated
    as a [have]-ready lemma so the reductions below need not rely on the
    aggressive [/=] that would otherwise unfold the [linhom_icones]
    packaging of [Coalg]. *)
Lemma Lfun_comp (A B C : ICone.type Ar)
    (g : icones_hom Ar B C) (f : icones_hom Ar A B) (x : A) :
  Lfun (icones_comp g f) x = Lfun g (Lfun f x).
Proof. by []. Qed.

(** ** The promoted Dirac path [r ↦ (δ_X r)!] *)

(** [(δ_X r)!] is in the unit ball of [!FMeas(X)] since [‖δ_X r‖ = 1]. *)
Lemma prom_dirac_ball (X : ar_obj Ar) (r : ar_carrier Ar X) :
  cone_norm (prom (dirac_fmeas r) : Bang Ar (FMeas X)) <= 1.
Proof. by apply: prom_ball; rewrite dirac_fmeas_norm; exact: lexx. Qed.

(** [r ↦ (δ_X r)!] is a measurable path of [!FMeas(X)].  It is the
    image of the (measurable, unit-ball) Dirac path [dirac_path X]
    under the meas-stable unit [nl (FMeas X)]. *)
Lemma bang_dirac_is_path (X : ar_obj Ar) :
  is_measurable_path (Ar:=Ar) (C:=Bang Ar (FMeas X))
    (X:=X) (fun r => prom (dirac_fmeas r)).
Proof.
have Hball r : cone_norm (dirac_fmeas (X:=X) r : FMeas X) <= 1.
  rewrite dirac_fmeas_norm; exact: lexx.
exact: (sc_meas_stable (nl (FMeas X))).2 _ _ Hball (dirac_fmeas_is_path X).
Qed.

Definition bang_dirac_path (X : ar_obj Ar) :
    path_car Ar X (Bang Ar (FMeas X)) :=
  MkPath (bang_dirac_is_path X).

(** ** The coalgebra map [Coalg_X : FMeas(X) ⊸ !FMeas(X)] *)

(** The integral operator of the promoted Dirac path has operator norm
    [≤ path_norm (bang_dirac_path X) ≤ 1]. *)
Lemma Coalg_norm_le1 (X : ar_obj Ar) :
  cone_norm (int_to_linhom (bang_dirac_path X)) <= 1.
Proof.
apply: le_trans (int_to_linhom_norm_le (bang_dirac_path X)) _.
rewrite -[cone_norm (bang_dirac_path X)]/(path_norm (bang_dirac_path X)).
apply: ge_sup; first exact: path_normset_nonempty.
by move=> _ [r ->] /=; exact: prom_dirac_ball.
Qed.

Definition Coalg (X : ar_obj Ar) : icones_hom Ar (FMeas X) (Bang Ar (FMeas X)) :=
  linhom_icones (int_to_linhom (bang_dirac_path X)) (Coalg_norm_le1 X).

(** Computation law: [Coalg_X(δ_X r) = (δ_X r)!]. *)
Lemma Coalg_dirac (X : ar_obj Ar) (r : ar_carrier Ar X) :
  Lfun (Coalg X) (dirac_fmeas r) = prom (dirac_fmeas r).
Proof.
rewrite /Coalg (linhom_iconesE _ (Coalg_norm_le1 X) (dirac_fmeas r)).
exact: (int_to_linhom_fun_dirac (bang_dirac_path X) r).
Qed.

(** ** Dirac density — Paper [th:dirac-dense]

    Two [icones_hom] out of [FMeas(X)] agreeing on every Dirac [δ_X r]
    are equal. *)
Lemma dirac_dense (X : ar_obj Ar) (B : ICone.type Ar)
    (f g : icones_hom Ar (FMeas X) B) :
  (forall r : ar_carrier Ar X, Lfun f (dirac_fmeas r) = Lfun g (dirac_fmeas r)) ->
  f = g.
Proof.
move=> Hfg.
(* Compare the [linhom_car] views: they integrate the same Dirac path. *)
have Heq : icones_to_linhom f = icones_to_linhom g.
  rewrite -(I_K_int_to_linhom_E (icones_to_linhom f)).
  rewrite -(I_K_int_to_linhom_E (icones_to_linhom g)).
  congr int_to_linhom; apply: path_eq => r.
  rewrite !linhom_to_int_E !icones_to_linhomE.
  exact: Hfg.
apply: icones_hom_eq => x.
have := congr1 (fun h => linhom_fun h x) Heq.
by rewrite !icones_to_linhomE.
Qed.

(** ** Dirac-to-integral lifting — Lemma C

    Any [icones_hom] [h : FMeas X → B] is determined on every [µ] by
    integration against the measurable path [r ↦ h(δ_r)].  Given a
    measurable path [φ : X → B] that agrees pointwise with [h ∘ δ],
    [h(µ) = ∫φ dµ] for every [µ].  This is a direct corollary of the
    round-trip identity [I ∘ K = id] of paper Thm 6.1: viewing [h] as a
    [linhom_car] via [icones_to_linhom], the equality
    [int_to_linhom (linhom_to_int (icones_to_linhom h))
       = icones_to_linhom h] (= [I_K_int_to_linhom_E]) applied to [µ]
    rewrites [h(µ)] as [int_to_linhom_fun] of the Dirac-image path; the
    Dirac-image path is then identified with [φ] via [path_eq] and the
    pointwise hypothesis [Hφ].

    The lemma is the "Diracs determine the integral" half of Thm 6.1
    at the function level; combined with [dirac_dense] (the matching
    "Diracs determine the map" extensionality), it provides the
    Dirac-to-integral lift for any EM-Kleisli arrow
    [K : FMeas_coalgebra X ⇝ B]: pass [ch_mor K] as the [icones_hom]
    [h], and the conclusion reads [K(µ) = ∫φ dµ] for any [φ] matching
    [K ∘ δ] on Diracs. *)
Lemma icones_hom_dirac_to_integral
    (X : ar_obj Ar) (B : ICone.type Ar)
    (h : icones_hom Ar (FMeas X) B)
    (phi : ar_carrier Ar X -> B)
    (Hphi_path : is_measurable_path (Ar:=Ar) (C:=B) (X:=X) phi)
    (Hphi : forall r, Lfun h (dirac_fmeas r) = phi r)
    (mu : fmeas R (ar_carrier Ar X)) :
  Lfun h mu = int_to_linhom_fun (MkPath Hphi_path) mu.
Proof.
have Hrt := I_K_int_to_linhom_E (icones_to_linhom h).
have Heq :
    linhom_fun (int_to_linhom (linhom_to_int (icones_to_linhom h))) mu
    = linhom_fun (icones_to_linhom h) mu.
  by rewrite Hrt.
rewrite icones_to_linhomE in Heq.
rewrite -Heq.
rewrite -[linhom_fun (int_to_linhom _) _]/(int_to_linhom_fun _ _).
congr (int_to_linhom_fun _ mu).
apply: path_eq => r /=.
by rewrite /linhom_to_int_fun icones_to_linhomE Hphi.
Qed.

(** ** The two coalgebra laws *)

(** [‖δ_X r‖ ≤ 1] — used to reduce the comonad laws on promoted
    points. *)
Let dirac_ball (X : ar_obj Ar) (r : ar_carrier Ar X) :
  cone_norm (dirac_fmeas r : FMeas X) <= 1.
Proof. rewrite dirac_fmeas_norm; exact: lexx. Qed.

(** Counit: [der ∘ Coalg_X = id].  On [δ_X r]:
    [der((δ_X r)!) = δ_X r] by [der_prom]. *)
Lemma Coalg_counit (X : ar_obj Ar) :
  icones_comp (der (FMeas X)) (Coalg X) = icones_id Ar (FMeas X).
Proof.
apply: (dirac_dense (X:=X)) => r.
rewrite Lfun_comp (Coalg_dirac (X:=X) r).
by rewrite (der_prom (dirac_fmeas r) (dirac_ball r)).
Qed.

(** Coassociativity: [dig ∘ Coalg_X = (!Coalg_X) ∘ Coalg_X].
    On [δ_X r]: LHS [dig((δ_X r)!) = ((δ_X r)!)!] by [dig_prom];
    RHS [(!Coalg_X)((δ_X r)!) = (Coalg_X(δ_X r))! = ((δ_X r)!)!] by
    [bang_fmap_prom]. *)
Lemma Coalg_coassoc (X : ar_obj Ar) :
  icones_comp (dig (FMeas X)) (Coalg X) =
  icones_comp (bang_fmap (Coalg X)) (Coalg X).
Proof.
apply: (dirac_dense (X:=X)) => r.
rewrite Lfun_comp (Coalg_dirac (X:=X) r).
rewrite (dig_prom (dirac_fmeas r) (dirac_ball r)).
rewrite Lfun_comp (Coalg_dirac (X:=X) r).
by rewrite (bang_fmap_prom (Coalg X) (dirac_fmeas r) (dirac_ball r))
           (Coalg_dirac (X:=X) r).
Qed.

End Coalgebra.

Arguments FMeas {R Ar} X.
Arguments bang_dirac_path {R Ar} X.
Arguments Coalg {R Ar} X.
Arguments Coalg_dirac {R Ar} X r.
Arguments dirac_dense {R Ar X B} f g.
Arguments icones_hom_dirac_to_integral
  {R Ar X B} h phi Hphi_path Hphi mu.
Arguments Coalg_counit {R Ar} X.
Arguments Coalg_coassoc {R Ar} X.

(** ** The minimal [!]-coalgebra record over [Bang_comonad] *)

Section EM.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Bg := (@Bang R Ar).

(** A [!]-coalgebra: a carrier [A], a structure map
    [coalg_str : A ⊸ !A], and the two laws ([der ∘ str = id],
    [dig ∘ str = (!str) ∘ str]). *)
Record Coalgebra : Type := MkCoalgebra {
  coalg_obj : ICone.type Ar;
  coalg_str : icones_hom Ar coalg_obj (Bg coalg_obj);
  coalg_counit :
    icones_comp (der coalg_obj) coalg_str = icones_id Ar coalg_obj;
  coalg_coassoc :
    icones_comp (dig coalg_obj) coalg_str =
    icones_comp (bang_fmap coalg_str) coalg_str;
}.

(** A morphism of [!]-coalgebras [(A,a) → (B,b)] is an [icones_hom]
    [h : A → B] commuting with the structure maps:
    [b ∘ h = (!h) ∘ a]. *)
Definition is_coalg_mor (P Q : Coalgebra) (h : icones_hom Ar (coalg_obj P) (coalg_obj Q)) : Prop :=
  icones_comp (coalg_str Q) h = icones_comp (bang_fmap h) (coalg_str P).

(** The identity is a coalgebra morphism. *)
Lemma coalg_mor_id (P : Coalgebra) :
  is_coalg_mor (P := P) (Q := P) (icones_id Ar (coalg_obj P)).
Proof. by rewrite /is_coalg_mor icones_compIr bang_fmap_id icones_compIl. Qed.

(** Coalgebra morphisms compose. *)
Lemma coalg_mor_comp (P Q S : Coalgebra)
    (g : icones_hom Ar (coalg_obj Q) (coalg_obj S))
    (f : icones_hom Ar (coalg_obj P) (coalg_obj Q)) :
  is_coalg_mor (P := Q) (Q := S) g -> is_coalg_mor (P := P) (Q := Q) f ->
  is_coalg_mor (P := P) (Q := S) (icones_comp g f).
Proof.
rewrite /is_coalg_mor => Hg Hf.
rewrite (bang_fmap_comp g f).
by rewrite icones_compA Hg -icones_compA Hf icones_compA.
Qed.

End EM.

Arguments Coalgebra {R} Ar.
Arguments is_coalg_mor {R Ar} P Q h.
Arguments coalg_mor_id {R Ar} P.
Arguments coalg_mor_comp {R Ar P Q S} g f.

(** ** The functor [FMeas : ARCAT → EM(ICones)] — Paper Theorem 9.7 *)

Section FMeasFunctor.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

(** The [!]-coalgebra carried by [FMeas(X)]. *)
Definition FMeas_coalgebra (X : ar_obj Ar) : Coalgebra Ar :=
  MkCoalgebra (Coalg_counit X) (Coalg_coassoc X).

(** The functorial action [FMeas(φ)]: the pushforward, packaged as an
    [icones_hom].  We realise it via Theorem 6.1 as
    [int_to_linhom (r ↦ δ_Y (φ r))], whose computation law on Diracs is
    [FMeas(φ)(δ_X r) = δ_Y(φ r)]. *)

(** [r ↦ δ_Y(φ r)] is in the unit ball pointwise. *)
Lemma push_dirac_ball (X Y : ar_obj Ar) (φ : ar_hom Ar X Y)
    (r : ar_carrier Ar X) :
  cone_norm (dirac_fmeas (φ r) : FMeas Y) <= 1.
Proof. rewrite dirac_fmeas_norm; exact: lexx. Qed.

(** [r ↦ δ_Y(φ r)] is a measurable path.  It is the Dirac path
    [dirac_fmeas : Y → FMeas Y] ([dirac_fmeas_is_path Y]) precomposed
    with the measurable [φ]: each per-test map [(z,r) ↦ m z (δ_Y(φ r))]
    is [(z,r) ↦ m z (δ_Y r')] reindexed along the measurable
    [(z,r) ↦ (z, φ r)]. *)
Lemma push_dirac_is_path (X Y : ar_obj Ar) (φ : ar_hom Ar X Y) :
  is_measurable_path (Ar:=Ar) (C:=FMeas Y) (X:=X)
    (fun r => dirac_fmeas (φ r)).
Proof.
have measφ : measurable_fun setT φ by exact: measurable_funP.
have [[M HM] Hmeas] := dirac_fmeas_is_path Y.
split.
  by exists M => r; exact: HM.
move=> Z m mM.
have base := Hmeas Z m mM.
(* [(z,r) ↦ m z (δ_Y(φ r))] = [(z,r) ↦ m z (δ_Y r')] ∘ [(z,r) ↦ (z, φ r)]. *)
pose reidx (p : ar_carrier Ar Z * ar_carrier Ar X) :
    ar_carrier Ar Z * ar_carrier Ar Y := (p.1, φ p.2).
have reidx_meas : measurable_fun setT reidx.
  apply: measurable_fun_pair.
    exact: measurable_fst.
  exact: (measurable_comp (F := setT) measurableT _ measφ measurable_snd).
have -> :
    (fun p : ar_carrier Ar Z * ar_carrier Ar X =>
       test_fun m p.1 (dirac_fmeas (φ p.2)))
    = (fun p => test_fun m (reidx p).1 (dirac_fmeas (reidx p).2)).
  by [].
exact: (measurable_comp (F := setT) measurableT _ base reidx_meas).
Qed.

Definition push_dirac_path (X Y : ar_obj Ar) (φ : ar_hom Ar X Y) :
    path_car Ar X (FMeas Y) :=
  MkPath (push_dirac_is_path φ).

Lemma FMeas_fmap_norm_le1 (X Y : ar_obj Ar) (φ : ar_hom Ar X Y) :
  cone_norm (int_to_linhom (push_dirac_path φ)) <= 1.
Proof.
apply: le_trans (int_to_linhom_norm_le (push_dirac_path φ)) _.
rewrite -[cone_norm (push_dirac_path φ)]/(path_norm (push_dirac_path φ)).
apply: ge_sup; first exact: path_normset_nonempty.
by move=> _ [r ->] /=; exact: push_dirac_ball.
Qed.

Definition FMeas_fmap (X Y : ar_obj Ar) (φ : ar_hom Ar X Y) :
    icones_hom Ar (FMeas X) (FMeas Y) :=
  linhom_icones (int_to_linhom (push_dirac_path φ)) (FMeas_fmap_norm_le1 φ).

(** Computation law: [FMeas(φ)(δ_X r) = δ_Y(φ r)]. *)
Lemma FMeas_fmap_dirac (X Y : ar_obj Ar) (φ : ar_hom Ar X Y)
    (r : ar_carrier Ar X) :
  Lfun (FMeas_fmap φ) (dirac_fmeas r) = dirac_fmeas (φ r).
Proof.
rewrite /FMeas_fmap (linhom_iconesE _ (FMeas_fmap_norm_le1 φ) (dirac_fmeas r)).
exact: (int_to_linhom_fun_dirac (push_dirac_path φ) r).
Qed.

(** Paper Theorem 9.7: [FMeas(φ)] is a coalgebra morphism
    [(FMeas X, Coalg_X) → (FMeas Y, Coalg_Y)]. *)
Lemma FMeas_fmap_is_coalg_mor (X Y : ar_obj Ar) (φ : ar_hom Ar X Y) :
  is_coalg_mor (FMeas_coalgebra X) (FMeas_coalgebra Y) (FMeas_fmap φ).
Proof.
rewrite /is_coalg_mor /=.
apply: (dirac_dense (X:=X)) => r.
have Hball : cone_norm (dirac_fmeas r : FMeas X) <= 1.
  rewrite dirac_fmeas_norm; exact: lexx.
(* LHS: [Coalg_Y(FMeas(φ)(δ_X r)) = Coalg_Y(δ_Y(φ r)) = (δ_Y(φ r))!]. *)
rewrite Lfun_comp (FMeas_fmap_dirac φ r) (Coalg_dirac Y (φ r)).
(* RHS: [(!FMeas(φ))(Coalg_X(δ_X r)) = (!FMeas(φ))((δ_X r)!)
   = (FMeas(φ)(δ_X r))! = (δ_Y(φ r))!]. *)
rewrite Lfun_comp (Coalg_dirac X r).
by rewrite (bang_fmap_prom (FMeas_fmap φ) (dirac_fmeas r) Hball)
           (FMeas_fmap_dirac φ r).
Qed.

End FMeasFunctor.

Arguments FMeas_coalgebra {R Ar} X.
Arguments FMeas_fmap {R Ar X Y} φ.
Arguments FMeas_fmap_dirac {R Ar X Y} φ r.
Arguments FMeas_fmap_is_coalg_mor {R Ar X Y} φ.
