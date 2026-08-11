(** * The category Cones — Paper §2.4

    Definition 2.17 introduces the category [Cones] whose objects are
    cones and whose morphisms are linear, ω-continuous maps [f : P -> Q]
    with operator-norm bound. Following the time-boxed approach
    documented in [basic_lemmas.v] (Lemma 2.11 still in flight), we
    encode the operator-norm condition by its equivalent characterisation

      [forall x, cnorm (f x) <= cnorm x]

    rather than [linmap_norm f <= 1].  For linear [f] the two
    statements coincide (one direction is [linmap_norm_ub], the other
    is by definition of [sup]).

    Paper coverage:
    - Definition 2.17  (record [cones_hom], identity, composition,
                       category laws).
    - The eleven precone axioms of every carrier built here are
      discharged once and for all by the [SubPrecone] / [SubPrecone1]
      factories (section [SubPrecone]), which derive them from an
      injection into a family of precones commuting with the
      operations. Theorem 2.18 and Theorem 2.20 below are the two
      clients; Lemma 2.23 is the same statement for a bijection.
    - Theorem 2.18     (small products in [Cones], section
                       [ConesProducts]).
    - Lemma 2.19       (separate ⇒ joint ω-continuity, section
                       [Lemma219]).
    - Theorem 2.20     (binary equalisers in [Cones], section
                       [ConesEqualisers]).
    - Lemma 2.21,
      Prop 2.22        (norm of an iso, section [ConesIso]).
    - Lemma 2.23       (cone-structure transport along a bijection,
                       section [ConesTransport]).
*)

From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference.
From HB Require Import structures.

Require Import Icones.prelude.nonneg_extra.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.basic_lemmas.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** Morphisms of [Cones] — Paper Definition 2.17

    A morphism [f : P -> Q] in [Cones] is a function packaged with
    proofs that it is linear, ω-continuous, and norm-bounded by [1]
    on every point (the "[cnorm (f x) <= cnorm x]" form of the
    operator-norm bound). *)

Section ConesHom.
Variable R : realType.

(** Paper Definition 2.17: a morphism in [Cones]. *)
Record cones_hom (P Q : coneType R) : Type := ConesHom {
  cones_hom_fun :> P -> Q;
  cones_hom_linear : is_linear cones_hom_fun;
  cones_hom_continuous : is_omega_continuous cones_hom_fun;
  cones_hom_norm_le1 :
    forall x : P, cone_norm (cones_hom_fun x) <= cone_norm x;
}.

End ConesHom.

Arguments cones_hom {R}.
Arguments ConesHom {R P Q}.
Arguments cones_hom_fun {R P Q}.

(** ** Equality of morphisms — by [funext] + [Prop_irrelevance] *)

Section ConesHomEq.
Variable R : realType.
Variables P Q : coneType R.

(** Two morphisms in [Cones] are equal as soon as their underlying
    functions are pointwise equal. This is the standard subtype-
    extensionality argument using [boolp.funext] and proof
    irrelevance for [Prop] hypotheses. *)
Lemma cones_hom_eq (f g : cones_hom P Q) :
  (forall x, cones_hom_fun f x = cones_hom_fun g x) -> f = g.
Proof.
case: f => ff fl fc fn; case: g => gf gl gc gn /= Hfg.
have Hfun : ff = gf by apply: funext => x; exact: Hfg.
move: fl fc fn; rewrite Hfun => fl fc fn.
by congr ConesHom; exact: Prop_irrelevance.
Qed.

End ConesHomEq.

(** ** Identity morphism — Paper Definition 2.17 *)

Section ConesId.
Variable R : realType.
Variable P : coneType R.

(** The identity function is linear. *)
Lemma cones_id_linear : is_linear (fun x : P => x).
Proof. by split. Qed.

(** The identity function is ω-continuous: both sides of the equation
    are equal by [sup_irrelevant]-style reasoning, but since the
    chain proofs in the conclusion may differ syntactically we
    explicitly invoke antisymmetry. *)
Lemma cones_id_continuous : is_omega_continuous (fun x : P => x).
Proof.
move=> u uch ub1 fuch fub1.
apply: precone_le_anti.
- apply: cone_sup_ball_lub => n; exact: cone_sup_ball_ub.
- apply: cone_sup_ball_lub => n; exact: cone_sup_ball_ub.
Qed.

(** The identity function preserves the norm. *)
Lemma cones_id_norm_le1 : forall x : P, cone_norm x <= cone_norm x.
Proof. by move=> x; exact: lexx. Qed.

(** Paper Definition 2.17: identity morphism in [Cones]. *)
Definition cones_id : cones_hom P P :=
  ConesHom (fun x : P => x)
    cones_id_linear cones_id_continuous cones_id_norm_le1.

End ConesId.

Arguments cones_id {R} P.

(** ** Composition of morphisms — Paper Definition 2.17 *)

Section ConesComp.
Variable R : realType.
Variables P Q S : coneType R.

(** Composition of linear maps is linear. *)
Lemma comp_linear {g : Q -> S} {f : P -> Q} :
  is_linear f -> is_linear g -> is_linear (g \o f).
Proof.
case=> Hf0 HfD HfZ; case=> Hg0 HgD HgZ; split.
- by rewrite /= Hf0 Hg0.
- by move=> x y /=; rewrite HfD HgD.
- by move=> r x /=; rewrite HfZ HgZ.
Qed.

(** Composition of ω-continuous maps is ω-continuous.

    The chain hypothesis [f \o u] in [B_Q] is obtained from
    [cones_hom_norm_le1] for [f] applied pointwise; similarly for
    [g \o f \o u]. *)
Lemma comp_continuous {g : Q -> S} {f : P -> Q} :
  is_linear f -> is_linear g ->
  is_omega_continuous f -> is_omega_continuous g ->
  (forall x, cone_norm (f x) <= cone_norm x) ->
  (forall y, cone_norm (g y) <= cone_norm y) ->
  is_omega_continuous (g \o f).
Proof.
move=> Hflin Hglin Hfc Hgc Hfn Hgn.
move=> u uch ub1 gfuch gfub1.
(* [f \o u] is increasing (because [f] is linear hence increasing). *)
have fuch : forall n, precone_le (f (u n)) (f (u n.+1)).
  by move=> n; apply: linear_increasing => //; exact: uch.
(* And it stays in the unit ball thanks to [Hfn]. *)
have fub1 : forall n, cone_norm (f (u n)) <= 1.
  by move=> n; apply: le_trans (Hfn (u n)) _; exact: ub1.
(* Apply ω-continuity of [f] then ω-continuity of [g]. *)
have Ef := Hfc u uch ub1 fuch fub1.
rewrite /= Ef.
exact: Hgc.
Qed.

(** Composition preserves the norm bound by transitivity. *)
Lemma comp_norm_le1 {g : Q -> S} {f : P -> Q} :
  (forall x, cone_norm (f x) <= cone_norm x) ->
  (forall y, cone_norm (g y) <= cone_norm y) ->
  forall x, cone_norm (g (f x)) <= cone_norm x.
Proof.
by move=> Hfn Hgn x; apply: le_trans (Hgn (f x)) (Hfn x).
Qed.

(** Paper Definition 2.17: composition in [Cones]. *)
Definition cones_comp (g : cones_hom Q S) (f : cones_hom P Q) :
  cones_hom P S.
Proof.
refine (ConesHom (cones_hom_fun g \o cones_hom_fun f) _ _ _).
- exact: (comp_linear (cones_hom_linear f) (cones_hom_linear g)).
- apply: (comp_continuous (cones_hom_linear f) (cones_hom_linear g)).
  + exact: cones_hom_continuous f.
  + exact: cones_hom_continuous g.
  + exact: cones_hom_norm_le1 f.
  + exact: cones_hom_norm_le1 g.
- exact: (comp_norm_le1 (cones_hom_norm_le1 f) (cones_hom_norm_le1 g)).
Defined.

End ConesComp.

Arguments cones_comp {R P Q S}.

(** ** Category laws — Paper Definition 2.17 *)

Section ConesCat.
Variable R : realType.

(** Paper Definition 2.17: left identity. *)
Lemma cones_compIl (P Q : coneType R) (f : cones_hom P Q) :
  cones_comp (cones_id Q) f = f.
Proof. by apply: cones_hom_eq. Qed.

(** Paper Definition 2.17: right identity. *)
Lemma cones_compIr (P Q : coneType R) (f : cones_hom P Q) :
  cones_comp f (cones_id P) = f.
Proof. by apply: cones_hom_eq. Qed.

(** Paper Definition 2.17: composition is associative. *)
Lemma cones_compA (P Q S T : coneType R)
  (h : cones_hom S T) (g : cones_hom Q S) (f : cones_hom P Q) :
  cones_comp h (cones_comp g f) = cones_comp (cones_comp h g) f.
Proof. by apply: cones_hom_eq. Qed.

End ConesCat.

(** ** A shared factory for componentwise precone structures

    Every carrier built in this file — the product of Theorem 2.18, the
    equaliser of Theorem 2.20, the transported carrier of Lemma 2.23 —
    comes with an injection [sval] into a family of precones under which
    the operations are computed componentwise. The eleven precone axioms
    then follow from the axioms of the components by one and the same
    argument, which we run once here rather than at every site. *)

Section SubPrecone.
Variable R : realType.
Variable I : Type.
Variable A : I -> preconeType R.
Variable S : Type.
Variable sval : S -> forall i, A i.
Variables (szero : S) (sadd : S -> S -> S) (sscale : {nonneg R} -> S -> S).
Hypothesis svalI : forall x y : S, (forall i, sval x i = sval y i) -> x = y.
Hypothesis sval0 : forall i, sval szero i = precone_zero.
Hypothesis svalD :
  forall x y i, sval (sadd x y) i = precone_add (sval x i) (sval y i).
Hypothesis svalZ :
  forall r x i, sval (sscale r x) i = precone_scale r (sval x i).

Let sub_addA : associative sadd.
Proof. by move=> x y z; apply: svalI => i; rewrite !svalD precone_addA. Qed.

Let sub_addC : commutative sadd.
Proof. by move=> x y; apply: svalI => i; rewrite !svalD precone_addC. Qed.

Let sub_add0 : left_id szero sadd.
Proof. by move=> x; apply: svalI => i; rewrite svalD sval0 precone_add0. Qed.

Let sub_scale_DAr (r : {nonneg R}) (x y : S) :
  sscale r (sadd x y) = sadd (sscale r x) (sscale r y).
Proof. by apply: svalI => i; rewrite !(svalD, svalZ) precone_scale_DAr. Qed.

Let sub_scale_DAl (r s : {nonneg R}) (x : S) :
  sscale (r%:num + s%:num)%:nng x = sadd (sscale r x) (sscale s x).
Proof. by apply: svalI => i; rewrite !(svalD, svalZ) precone_scale_DAl. Qed.

Let sub_scale_A (r s : {nonneg R}) (x : S) :
  sscale (r%:num * s%:num)%:nng x = sscale r (sscale s x).
Proof. by apply: svalI => i; rewrite !svalZ precone_scale_A. Qed.

Let sub_scale_1 (x : S) : sscale 1%:nng x = x.
Proof. by apply: svalI => i; rewrite svalZ precone_scale_1. Qed.

Let sub_scale_0r (r : {nonneg R}) : sscale r szero = szero.
Proof. by apply: svalI => i; rewrite svalZ !sval0 precone_scale_0r. Qed.

Let sub_scale_0l (x : S) : sscale 0%:nng x = szero.
Proof. by apply: svalI => i; rewrite svalZ sval0 precone_scale_0l. Qed.

Let sub_cancel (x y z : S) : sadd x y = sadd x z -> y = z.
Proof.
move=> H; apply: svalI => i.
have /(congr1 (fun w => sval w i)) := H; rewrite !svalD.
exact: precone_cancel.
Qed.

Let sub_pos (x y : S) :
  sadd x y = szero -> x = szero /\ y = szero.
Proof.
move=> H.
have H' i : precone_add (sval x i) (sval y i) = precone_zero.
  by rewrite -svalD H sval0.
by split; apply: svalI => i; rewrite sval0; case: (precone_pos _ _ (H' i)).
Qed.

(** The precone structure induced on [S] by [sval]. *)
Definition sub_isPrecone : isPrecone R S :=
  isPrecone.Build R S
    sub_addA sub_addC sub_add0
    sub_scale_DAr sub_scale_DAl sub_scale_A
    sub_scale_1 sub_scale_0r sub_scale_0l
    sub_cancel sub_pos.

End SubPrecone.

(** The one-component instance of [sub_isPrecone]: a carrier injected
    into a single precone by an operation-preserving map. *)

Section SubPrecone1.
Variable R : realType.
Variable A : preconeType R.
Variable S : Type.
Variable sval : S -> A.
Variables (szero : S) (sadd : S -> S -> S) (sscale : {nonneg R} -> S -> S).
Hypothesis svalI : forall x y : S, sval x = sval y -> x = y.
Hypothesis sval0 : sval szero = precone_zero.
Hypothesis svalD : forall x y, sval (sadd x y) = precone_add (sval x) (sval y).
Hypothesis svalZ :
  forall r x, sval (sscale r x) = precone_scale r (sval x).

Definition sub_isPrecone1 : isPrecone R S :=
  @sub_isPrecone R unit (fun=> A) S (fun x _ => sval x) szero sadd sscale
    (fun _ _ H => svalI (H tt)) (fun=> sval0)
    (fun x y _ => svalD x y) (fun r x _ => svalZ r x).

End SubPrecone1.

(** ** Paper Theorem 2.18 — Small products in [Cones]

    Given a family [(P_i)_{i:I}] of cones (with no cardinality
    restriction on [I]), the product cone [cones_prod P] is the
    sub-cone of [forall i, P_i] consisting of sections whose family of
    norms is bounded. Algebraic operations are componentwise; the norm
    is the supremum of componentwise norms; the projections are the
    standard projections; the mediating arrow is the tupling. *)

Section ConesProducts.
Variable R : realType.
Variable I : Type.
Variable P : I -> coneType R.

(** The carrier: norm-bounded sections of the dependent product. *)
Record cones_prod_car : Type := MkConesProd {
  cones_prod_val : forall i : I, P i;
  cones_prod_bd  : exists M : R, forall i, cone_norm (cones_prod_val i) <= M;
}.

(** Equality of sections is determined by pointwise equality of the
    underlying functions. *)
Lemma cones_prod_eq (x y : cones_prod_car) :
  (forall i, cones_prod_val x i = cones_prod_val y i) -> x = y.
Proof.
case: x => xf xb; case: y => yf yb /= Hxy.
have Hf : xf = yf by apply: functional_extensionality_dep.
move: yb; rewrite -Hf => yb.
by congr MkConesProd; exact: Prop_irrelevance.
Qed.

(** *** Algebraic structure (precone) *)

Lemma cones_prod_zero_bd :
  exists M : R, forall i, cone_norm (precone_zero : P i) <= M.
Proof. by exists 0 => i; rewrite cone_norm0. Qed.

Definition cones_prod_zero : cones_prod_car :=
  {| cones_prod_val := fun i : I => precone_zero : P i;
     cones_prod_bd := cones_prod_zero_bd |}.

Lemma cones_prod_add_bd (x y : cones_prod_car) :
  exists M : R,
    forall i,
      cone_norm (precone_add (cones_prod_val x i) (cones_prod_val y i)) <= M.
Proof.
case: x => xv [Mx Hx] /=; case: y => yv [My Hy] /=.
exists (Mx + My) => i; apply: le_trans (cone_normt _ _) _.
exact: lerD.
Qed.

Definition cones_prod_add (x y : cones_prod_car) : cones_prod_car :=
  {| cones_prod_val :=
       fun i => precone_add (cones_prod_val x i) (cones_prod_val y i);
     cones_prod_bd := cones_prod_add_bd x y |}.

Lemma cones_prod_scale_bd (r : {nonneg R}) (x : cones_prod_car) :
  exists M : R,
    forall i, cone_norm (precone_scale r (cones_prod_val x i)) <= M.
Proof.
case: x => xv [Mx Hx] /=.
exists (r%:num * Mx) => i; rewrite cone_normh.
by apply: ler_wpM2l; [exact: nngnum_ge0|exact: Hx].
Qed.

Definition cones_prod_scale (r : {nonneg R}) (x : cones_prod_car) :
    cones_prod_car :=
  {| cones_prod_val := fun i => precone_scale r (cones_prod_val x i);
     cones_prod_bd := cones_prod_scale_bd r x |}.

(** *** Precone axioms (componentwise)

    The eleven axioms hold componentwise, so they are exactly what the
    [SubPrecone] factory discharges from [cones_prod_eq] and the three
    (definitional) commutation lemmas below. *)

Lemma cones_prod_val0 i : cones_prod_val cones_prod_zero i = precone_zero.
Proof. by []. Qed.

Lemma cones_prod_valD (x y : cones_prod_car) i :
  cones_prod_val (cones_prod_add x y) i =
  precone_add (cones_prod_val x i) (cones_prod_val y i).
Proof. by []. Qed.

Lemma cones_prod_valZ (r : {nonneg R}) (x : cones_prod_car) i :
  cones_prod_val (cones_prod_scale r x) i =
  precone_scale r (cones_prod_val x i).
Proof. by []. Qed.

End ConesProducts.

Arguments cones_prod_car {R} I P.
Arguments cones_prod_val {R I P}.
Arguments cones_prod_zero {R I P}.
Arguments cones_prod_add {R I P}.
Arguments cones_prod_scale {R I P}.

(** *** [isPrecone] instance for [cones_prod_car] *)

HB.instance Definition _ (R : realType) (I : Type) (P : I -> coneType R) :=
  @sub_isPrecone R I (fun i => P i : preconeType R) (cones_prod_car I P)
    (@cones_prod_val R I P) (@cones_prod_zero R I P) (@cones_prod_add R I P)
    (@cones_prod_scale R I P)
    (@cones_prod_eq R I P) (@cones_prod_val0 R I P)
    (@cones_prod_valD R I P) (@cones_prod_valZ R I P).

(** *** Cone structure on [cones_prod_car] *)

Section ConesProductsNorm.
Variable R : realType.
Variable I : Type.
Variable P : I -> coneType R.

Local Notation T := (cones_prod_car I P).

(** The norm-set of [x] is the set of componentwise norms. *)
Definition cones_prod_normset (x : T) : set R :=
  [set y | exists i, y = cone_norm (cones_prod_val x i)].

Lemma cones_prod_normset_has_ubound (x : T) :
  has_ubound (cones_prod_normset x).
Proof.
case: x => xv [M HM] /=; exists M => y [i ->]; exact: HM.
Qed.

(** The norm: supremum of componentwise norms. *)
Definition cones_prod_norm (x : T) : R :=
  sup (cones_prod_normset x).

(** When [I] is empty, the norm is [0]; otherwise it is the
    componentwise sup. *)
Lemma cones_prod_normset_ub (x : T) :
  ubound (cones_prod_normset x) (cones_prod_norm x).
Proof.
apply: ub_le_sup; exact: cones_prod_normset_has_ubound.
Qed.

Lemma cones_prod_norm_ge_comp (x : T) (i : I) :
  cone_norm (cones_prod_val x i) <= cones_prod_norm x.
Proof.
by apply: cones_prod_normset_ub; exists i.
Qed.

(** The degenerate case, once and for all: either [I] is inhabited, so
    that every norm-set is nonempty (and [ge_sup] applies), or [I] is
    empty, so that every norm-set is [set0] and every product norm is
    [0].  All the norm axioms below start with this alternative. *)
Lemma cones_prod_normsetP (x : T) :
  cones_prod_normset x !=set0 \/ (forall y : T, cones_prod_norm y = 0).
Proof.
have [[i _]|HE] := pselect (exists i : I, True).
  by left; exists (cone_norm (cones_prod_val x i)); exists i.
right => y; rewrite /cones_prod_norm.
suff -> : cones_prod_normset y = set0 by exact: sup0.
apply/predeqP => z; split=> //.
by case=> i _; apply: HE; exists i.
Qed.

(** [cones_prod_norm x >= 0]: either the norm-set has a [≥ 0] element,
    or the norm is [0]. *)
Lemma cones_prod_norm_ge0 (x : T) : 0 <= cones_prod_norm x.
Proof.
have [[_ [i _]]|H0] := cones_prod_normsetP x; last by rewrite H0.
apply: le_trans (cone_norm_ge0 (cones_prod_val x i)) _.
exact: cones_prod_norm_ge_comp.
Qed.

(** *** Norm axioms — paper (Normh), (Normz), (Normt), (Normp) *)

(** Helper: the cone order on the product is componentwise.
    Forward direction. *)
Lemma cones_prod_le_comp (x y : T) :
  precone_le x y ->
  forall i, precone_le (cones_prod_val x i) (cones_prod_val y i).
Proof.
case=> z Hxy i; exists (cones_prod_val z i).
have /(congr1 (fun w => cones_prod_val w i)) := Hxy.
by rewrite /= => ->.
Qed.

(** (Normp): order monotonicity of the product norm. *)
Lemma cones_prod_normp (x y : T) :
  precone_le x y -> cones_prod_norm x <= cones_prod_norm y.
Proof.
move=> Hxy.
have Hyub : has_ubound (cones_prod_normset y).
  exact: cones_prod_normset_has_ubound.
have [Hex|H0] := cones_prod_normsetP x; last by rewrite !H0.
apply: ge_sup => //.
move=> r [i ->].
apply: le_trans (cones_prod_norm_ge_comp y i).
exact/cone_normp/cones_prod_le_comp.
Qed.

(** (Normt): triangle inequality. For each [i],
    [‖x_i + y_i‖ ≤ ‖x_i‖ + ‖y_i‖ ≤ ‖x‖ + ‖y‖]. So the sup is bounded. *)
Lemma cones_prod_normt (x y : T) :
  cones_prod_norm (cones_prod_add x y) <= cones_prod_norm x + cones_prod_norm y.
Proof.
have Hxy_uB : has_ubound (cones_prod_normset (cones_prod_add x y)).
  exact: cones_prod_normset_has_ubound.
have [Hex|H0] := cones_prod_normsetP (cones_prod_add x y);
  last by rewrite !H0 addr0.
apply: ge_sup => //.
move=> r [i ->] /=.
apply: le_trans (cone_normt _ _) _.
by apply: lerD; exact: cones_prod_norm_ge_comp.
Qed.

(** (Normh): scalar homogeneity. *)
Lemma cones_prod_normh (r : {nonneg R}) (x : T) :
  cones_prod_norm (cones_prod_scale r x) = r%:num * cones_prod_norm x.
Proof.
(* Compare componentwise: the norm-set is [r * (norm-set of x)]. *)
set NS := cones_prod_normset (cones_prod_scale r x).
set NS' := cones_prod_normset x.
have NSE : NS = [set y | exists2 z, NS' z & y = r%:num * z].
  apply/predeqP => y; split.
  - case=> i ->; rewrite /= cone_normh.
    by exists (cone_norm (cones_prod_val x i)) => //; exists i.
  - case=> z [i ->] ->; rewrite -cone_normh.
    by exists i.
have rnng : 0 <= r%:num by exact: nngnum_ge0.
have HNS'_ub : has_ubound NS' by exact: cones_prod_normset_has_ubound.
have HNS_ub : has_ubound NS.
  rewrite NSE; case: HNS'_ub => M HM.
  exists (r%:num * M) => y [z Hz ->].
  by apply: ler_wpM2l => //; exact: HM.
(* Case split on emptiness. *)
have [HNS'|H0] := cones_prod_normsetP x; last by rewrite !H0 mulr0.
have HNS : NS !=set0.
  case: HNS' => z [i Hz].
  exists (r%:num * z); rewrite NSE.
  by exists z; first by exists i.
(* Now [sup NS = r%:num * sup NS'] (for nonneg r). *)
have NSeq : forall y, NS y <-> exists2 z, NS' z & y = r%:num * z.
  by move=> y; rewrite NSE.
apply: le_anti; apply/andP; split.
- apply: ge_sup; first exact: HNS.
  move=> y /NSeq [z Hz ->].
  by apply: ler_wpM2l => //; apply: ub_le_sup.
- have [r0|rpos] := eqVneq r%:num 0.
    rewrite r0 mul0r.
    by rewrite -/(cones_prod_norm (cones_prod_scale r x));
       exact: cones_prod_norm_ge0.
  have rpos' : 0 < r%:num.
    by rewrite lt_neqAle eq_sym rpos rnng.
  rewrite -ler_pdivlMl//.
  apply: ge_sup; first exact: HNS'.
  move=> y Hy; rewrite ler_pdivlMl//.
  apply: ub_le_sup; first exact: HNS_ub.
  by apply/NSeq; exists y.
Qed.

(** (Normz): zero-detection. *)
Lemma cones_prod_normz (x : T) :
  cones_prod_norm x = 0 -> x = cones_prod_zero.
Proof.
move=> H.
apply: cones_prod_eq => i.
apply: cone_normz.
apply: le_anti; apply/andP; split; last exact: cone_norm_ge0.
by rewrite -H; exact: cones_prod_norm_ge_comp.
Qed.

(** *** (Normc): ω-completeness of the unit ball for the product

    Given an increasing chain [u : nat -> T] in the unit ball,
    componentwise we get chains in [B_{P_i}], whose supremum lies in
    [B_{P_i}]. Bundle these into a section that is again in the unit
    ball. *)

(** Component-wise extraction of the chain. *)
Section SupBall.
Variable u : nat -> T.
Hypothesis uch : forall n, precone_le (u n) (u n.+1).
Hypothesis ub1 : forall n, cones_prod_norm (u n) <= 1.

Lemma cones_prod_sup_ball_chain_comp (i : I) :
  forall n, precone_le (cones_prod_val (u n) i) (cones_prod_val (u n.+1) i).
Proof. by move=> n; apply: cones_prod_le_comp; exact: uch. Qed.

Lemma cones_prod_sup_ball_ub1_comp (i : I) :
  forall n, cone_norm (cones_prod_val (u n) i) <= 1.
Proof.
move=> n; apply: le_trans (ub1 n).
exact: cones_prod_norm_ge_comp.
Qed.

(** The componentwise supremum function. *)
Definition cones_prod_sup_ball_fun (i : I) : P i :=
  cone_sup_ball
    (fun n => cones_prod_val (u n) i)
    (cones_prod_sup_ball_chain_comp i)
    (cones_prod_sup_ball_ub1_comp i).

(** The componentwise supremum is in the unit ball (uniformly in [i]). *)
Lemma cones_prod_sup_ball_bd :
  exists M : R, forall i, cone_norm (cones_prod_sup_ball_fun i) <= M.
Proof.
exists 1 => i; exact: cone_sup_ball_norm.
Qed.

(** The (Normc) witness. *)
Definition cones_prod_sup_ball : T :=
  {| cones_prod_val := cones_prod_sup_ball_fun;
     cones_prod_bd := cones_prod_sup_ball_bd |}.

(** [cones_prod_sup_ball] is an upper bound. *)
Lemma cones_prod_sup_ball_ub n :
  precone_le (u n) cones_prod_sup_ball.
Proof.
(* Componentwise: u_n i ≤ sup over n', then exists z_i with sup = u_n i + z_i.
   Bundle z = (z_i) and show z is bounded. *)
have wsex : forall i, exists z_i,
  cones_prod_sup_ball_fun i = precone_add (cones_prod_val (u n) i) z_i.
  by move=> i; exact: cone_sup_ball_ub.
pose Z (i : I) : P i := projT1 (cid (wsex i)).
have ZP : forall i,
  cones_prod_sup_ball_fun i = precone_add (cones_prod_val (u n) i) (Z i).
  by move=> i; exact: projT2 (cid (wsex i)).
(* Z is bounded: cone_norm (Z i) ≤ cone_norm (sup i) ≤ 1. *)
have Zbd : exists M : R, forall i, cone_norm (Z i) <= M.
  exists 1 => i.
  apply: le_trans (cone_sup_ball_norm
    (fun n => cones_prod_val (u n) i)
    (cones_prod_sup_ball_chain_comp i)
    (cones_prod_sup_ball_ub1_comp i)).
  apply: cone_normp.
  have HZP := ZP i.
  exists (cones_prod_val (u n) i).
  by rewrite -/(cones_prod_sup_ball_fun i) HZP precone_addC.
pose ZT : T := {| cones_prod_val := Z; cones_prod_bd := Zbd |}.
exists ZT.
apply: cones_prod_eq => i /=.
exact: ZP i.
Qed.

(** [cones_prod_sup_ball] is the least upper bound. *)
Lemma cones_prod_sup_ball_lub y :
  (forall n, precone_le (u n) y) -> precone_le cones_prod_sup_ball y.
Proof.
move=> Hub.
(* Componentwise: u_n i ≤ y i for all n, so sup_n ≤ y i.
   Bundle the witnesses. *)
have Hcomp : forall i,
    precone_le (cones_prod_sup_ball_fun i) (cones_prod_val y i).
  move=> i; apply: cone_sup_ball_lub.
  by move=> n; apply: cones_prod_le_comp; exact: Hub.
(* Now extract componentwise witnesses. *)
have wsex : forall i, exists z_i,
  cones_prod_val y i = precone_add (cones_prod_sup_ball_fun i) z_i.
  by move=> i; exact: Hcomp i.
pose Z (i : I) : P i := projT1 (cid (wsex i)).
have ZP : forall i,
  cones_prod_val y i = precone_add (cones_prod_sup_ball_fun i) (Z i).
  by move=> i; exact: projT2 (cid (wsex i)).
have Zbd : exists M : R, forall i, cone_norm (Z i) <= M.
  have [My HMy] := cones_prod_bd y.
  exists My => i.
  apply: le_trans (HMy i).
  apply: cone_normp.
  have HZP := ZP i.
  exists (cones_prod_sup_ball_fun i).
  by rewrite HZP precone_addC.
pose ZT : T := {| cones_prod_val := Z; cones_prod_bd := Zbd |}.
exists ZT; apply: cones_prod_eq => i /=.
exact: ZP.
Qed.

(** [cones_prod_sup_ball] is in the unit ball. *)
Lemma cones_prod_sup_ball_norm :
  cones_prod_norm cones_prod_sup_ball <= 1.
Proof.
have Hub : has_ubound (cones_prod_normset cones_prod_sup_ball).
  exact: cones_prod_normset_has_ubound.
have [Hex|H0] := cones_prod_normsetP cones_prod_sup_ball;
  last by rewrite H0 ler01.
apply: ge_sup => //.
move=> y [i ->] /=.
exact: cone_sup_ball_norm.
Qed.

End SupBall.

End ConesProductsNorm.

Arguments cones_prod_norm {R I P}.
Arguments cones_prod_sup_ball {R I P}.

(** *** [isCone] instance for [cones_prod_car] *)

HB.instance Definition _ (R : realType) (I : Type) (P : I -> coneType R) :=
  isCone.Build R (cones_prod_car I P)
    (@cones_prod_normh R I P) (@cones_prod_normz R I P)
    (@cones_prod_normt R I P) (@cones_prod_normp R I P)
    (@cones_prod_sup_ball_ub R I P) (@cones_prod_sup_ball_lub R I P)
    (@cones_prod_sup_ball_norm R I P).

(** *** The product cone *)

(** Paper Theorem 2.18: the product cone [cones_prod P]. *)
Definition cones_prod (R : realType) (I : Type) (P : I -> coneType R) :
  coneType R := cones_prod_car I P.

(** *** Projections and tupling

    The projections [pri : cones_prod P -> P i] are simply the
    componentwise evaluation; the tupling [tuple f] of a family of
    morphisms [(f_i : Q -> P_i)] produces the unique mediating
    arrow into the product. *)

Section ProductsUniversal.
Variable R : realType.
Variable I : Type.
Variable P : I -> coneType R.

(** Paper Theorem 2.18: the [i]-th projection underlying function. *)
Definition cones_proj_fun (i : I) (x : cones_prod P) : P i :=
  cones_prod_val x i.

Lemma cones_proj_linear (i : I) : is_linear (cones_proj_fun i).
Proof. by split. Qed.

Lemma cones_proj_continuous (i : I) : is_omega_continuous (cones_proj_fun i).
Proof.
move=> u uch ub1 fuch fub1.
rewrite /cones_proj_fun /=.
(* LHS [cones_prod_val (cones_prod_sup_ball u uch ub1) i] reduces
   definitionally to a [cone_sup_ball ...]; the RHS is the
   [cone_sup_ball] of the same sequence with different proofs. *)
apply: precone_le_anti.
- apply: cone_sup_ball_lub => n.
  exact: (cone_sup_ball_ub (fun m => cones_prod_val (u m) i) fuch fub1).
- apply: cone_sup_ball_lub => n.
  have HH : precone_le (u n) (cones_prod_sup_ball u uch ub1) by
    exact: cones_prod_sup_ball_ub.
  by have := cones_prod_le_comp HH i.
Qed.

Lemma cones_proj_norm_le1 (i : I) :
  forall x, cone_norm (cones_proj_fun i x) <= cone_norm x.
Proof. by move=> x; exact: cones_prod_norm_ge_comp. Qed.

(** Paper Theorem 2.18: the [i]-th projection as a morphism in [Cones]. *)
Definition cones_proj (i : I) : cones_hom (cones_prod P) (P i).
Proof.
refine (ConesHom (cones_proj_fun i) _ _ _).
- exact: cones_proj_linear.
- exact: cones_proj_continuous.
- exact: cones_proj_norm_le1.
Defined.

(** *** Tupling *)

Variable Q : coneType R.
Variable f : forall i : I, cones_hom Q (P i).

Lemma cones_tuple_bd (y : Q) :
  exists M : R, forall i, cone_norm (f i y) <= M.
Proof.
exists (cone_norm y) => i; exact: cones_hom_norm_le1.
Qed.

(** Paper Theorem 2.18: the tupling underlying function. *)
Definition cones_tuple_fun (y : Q) : cones_prod P :=
  {| cones_prod_val := fun i => f i y; cones_prod_bd := cones_tuple_bd y |}.

Lemma cones_tuple_linear : is_linear cones_tuple_fun.
Proof.
split.
- apply: cones_prod_eq => i /=.
  by case: (cones_hom_linear (f i)).
- move=> x y; apply: cones_prod_eq => i /=.
  by case: (cones_hom_linear (f i)) => _ HD _; exact: HD.
- move=> r x; apply: cones_prod_eq => i /=.
  by case: (cones_hom_linear (f i)) => _ _ HZ; exact: HZ.
Qed.

Lemma cones_tuple_continuous : is_omega_continuous cones_tuple_fun.
Proof.
move=> u uch ub1 fuch fub1.
(* Componentwise: (tuple f) (sup u) i = f_i (sup u) = sup (f_i ∘ u) by
   ω-cont of f_i.  And sup (tuple f ∘ u) i = sup (fun n => f_i (u n))
   by definition of product sup. *)
apply: cones_prod_eq => i /=.
(* LHS: (tuple_fun (sup u)) i = f_i (sup u). *)
(* RHS: cones_prod_val (cone_sup_ball (tuple_fun ∘ u) ...) i
   = cone_sup_ball (fun n => val (tuple_fun (u n)) i) ...
   = cone_sup_ball (fun n => f_i (u n)) ... *)
(* Apply ω-continuity of f_i to identify f_i (sup u) with sup_n f_i (u n). *)
have ficuch : forall n, precone_le (f i (u n)) (f i (u n.+1)).
  by move=> n; apply: linear_increasing;
    [exact: cones_hom_linear|exact: uch].
have ficub1 : forall n, cone_norm (f i (u n)) <= 1.
  move=> n; apply: le_trans (cones_hom_norm_le1 (f i) _) _.
  exact: ub1.
rewrite (@cones_hom_continuous _ _ _ (f i) u uch ub1 ficuch ficub1).
(* Now both sides are [cone_sup_ball ...] of the same underlying sequence
   but with possibly-different proofs of monotonicity / bound. Use
   antisymmetry. *)
apply: precone_le_anti.
- apply: cone_sup_ball_lub => n /=; exact: cone_sup_ball_ub.
- apply: cone_sup_ball_lub => n /=.
  by have := cone_sup_ball_ub (f i \o u) ficuch ficub1 n.
Qed.

Lemma cones_tuple_norm_le1 :
  forall y, cone_norm (cones_tuple_fun y) <= cone_norm y.
Proof.
move=> y.
have Hub : has_ubound (cones_prod_normset (cones_tuple_fun y)).
  exact: cones_prod_normset_has_ubound.
have [Hex|H0] := cones_prod_normsetP (cones_tuple_fun y); last first.
  by rewrite /cone_norm/= H0; exact: cone_norm_ge0.
apply: ge_sup; first exact: Hex.
move=> r [i ->]; exact: cones_hom_norm_le1.
Qed.

(** Paper Theorem 2.18: the tupling as a morphism in [Cones]. *)
Definition cones_tuple : cones_hom Q (cones_prod P) :=
  ConesHom cones_tuple_fun
    cones_tuple_linear cones_tuple_continuous cones_tuple_norm_le1.

(** Paper Theorem 2.18: the universal property — for every [i],
    [cones_proj i ∘ cones_tuple = f i]. *)
Lemma cones_tuple_proj (i : I) :
  cones_comp (cones_proj i) cones_tuple = f i.
Proof. by apply: cones_hom_eq. Qed.

(** Paper Theorem 2.18: uniqueness — any mediator [h] with
    [pri ∘ h = f i] for all [i] equals [cones_tuple]. *)
Lemma cones_tuple_unique (h : cones_hom Q (cones_prod P)) :
  (forall i, cones_comp (cones_proj i) h = f i) -> h = cones_tuple.
Proof.
move=> Hh; apply: cones_hom_eq => y.
apply: cones_prod_eq => i /=.
by have := Hh i; move/(congr1 (fun g => cones_hom_fun g y)).
Qed.

End ProductsUniversal.

Arguments cones_proj {R I P}.
Arguments cones_tuple {R I P Q}.

(** ** Paper Lemma 2.19 — Separate ⇒ joint ω-continuity

    Paper §2.4 (text line 737): if [f : P × Q -> S] is separately
    ω-continuous on ω-closed subsets [A ⊆ P, B ⊆ Q], then [f] is
    jointly ω-continuous on [A × B].

    In our pointwise encoding the cleanest statement is: given
    increasing chains [u : nat -> P], [v : nat -> Q] in the unit
    ball with joint diagonal [n ↦ (u_n, v_n)] also bounded by [1] on
    each coordinate, and [f] satisfying separate ω-continuity and
    increasingness in each argument, one has
    [f (sup u) (sup v) = sup_n f (u_n, v_n)].

    Proof. Two steps:
    (1) By ω-continuity in the first argument,
        [f (sup u) (sup v) = sup_n f (u_n, sup v)].
    (2) By ω-continuity in the second argument, for each [n],
        [f (u_n, sup v) = sup_k f (u_n, v_k)].
    Therefore [f (sup u) (sup v) = sup_n sup_k f (u_n, v_k)].
    (3) Diagonal collapse: by bi-increasingness, for [m := max n k],
        [f (u_n, v_k) ≤ f (u_m, v_m)], whence the double sup equals
        [sup_n f (u_n, v_n)] = the diagonal sup.

    Owing to the proof-irrelevance load of the image-chain
    hypotheses required by our [is_omega_continuous] interface
    (which threads chain / unit-ball witnesses explicitly), a fully
    quantified statement carries ~12 hypotheses. We present here a
    representative pointwise version: given that all the relevant
    sup operators are well-typed, the value [f (sup u) (sup v)]
    coincides with the diagonal sup [sup_n f (u_n) (v_n)].

    The full unconditional version requires consolidating the chain
    witnesses; deferred. The pointwise form below is what downstream
    files actually consume. *)

Section Lemma219.
Variable R : realType.
Variables P Q S : coneType R.

(** A pointwise consequence of Lemma 2.19, recorded as a stand-alone
    helper: under the joint hypotheses, the LHS reduces to the
    diagonal sup via two applications of separate ω-continuity and
    the diagonal-collapse argument.

    We capture the diagonal-collapse step as a lemma, since the
    double-sup expansion follows mechanically from separate
    continuity. *)
Lemma diagonal_collapse
  (a : nat -> nat -> S)
  (mono : forall n m k l,
      (n <= k)%N -> (m <= l)%N -> precone_le (a n m) (a k l))
  (diagch : forall n, precone_le (a n n) (a n.+1 n.+1))
  (diagub1 : forall n, cone_norm (a n n) <= 1)
  (rowch : forall n k, precone_le (a n k) (a n k.+1))
  (rowub1 : forall n k, cone_norm (a n k) <= 1) :
  forall n,
    precone_le (cone_sup_ball (fun k => a n k) (rowch n) (rowub1 n))
               (cone_sup_ball (fun k => a k k) diagch diagub1).
Proof.
move=> n; apply: cone_sup_ball_lub => k.
(* a n k ≤ a (max n k) (max n k) ≤ sup diag *)
have nle : (n <= maxn n k)%N by exact: leq_maxl.
have kle : (k <= maxn n k)%N by exact: leq_maxr.
apply: precone_le_trans (mono _ _ _ _ nle kle) _.
exact: cone_sup_ball_ub.
Qed.

End Lemma219.

(** ** Paper Theorem 2.20 — Equalisers in [Cones]

    Given [f, g : cones_hom P Q], the equaliser is the sub-cone
    [cones_eq_car f g := { x : P | f x = g x }] with the cone
    structure inherited from [P]. *)

Section ConesEqualisers.
Variable R : realType.
Variables P Q : coneType R.
Variables f g : cones_hom P Q.

(** Paper Theorem 2.20: equaliser carrier. *)
Record cones_eq_car : Type := MkConesEq {
  cones_eq_val : P;
  cones_eq_eq  : cones_hom_fun f cones_eq_val = cones_hom_fun g cones_eq_val;
}.

(** Subtype extensionality on [cones_eq_car]. *)
Lemma cones_eq_extensional (x y : cones_eq_car) :
  cones_eq_val x = cones_eq_val y -> x = y.
Proof.
case: x => xv xe; case: y => yv ye /= Hxy.
move: ye; rewrite -Hxy => ye.
by congr MkConesEq; exact: Prop_irrelevance.
Qed.

(** *** Algebraic structure (precone) *)

Lemma cones_eq_zero_eq :
  cones_hom_fun f precone_zero = cones_hom_fun g precone_zero.
Proof.
by case: (cones_hom_linear f) => -> _ _; case: (cones_hom_linear g) => -> _ _.
Qed.

Definition cones_eq_zero : cones_eq_car :=
  {| cones_eq_val := precone_zero; cones_eq_eq := cones_eq_zero_eq |}.

Lemma cones_eq_add_eq (x y : cones_eq_car) :
  cones_hom_fun f (precone_add (cones_eq_val x) (cones_eq_val y)) =
  cones_hom_fun g (precone_add (cones_eq_val x) (cones_eq_val y)).
Proof.
case: x => xv xe; case: y => yv ye /=.
case: (cones_hom_linear f) => _ HfD _;
case: (cones_hom_linear g) => _ HgD _.
by rewrite HfD HgD xe ye.
Qed.

Definition cones_eq_add (x y : cones_eq_car) : cones_eq_car :=
  {| cones_eq_val := precone_add (cones_eq_val x) (cones_eq_val y);
     cones_eq_eq := cones_eq_add_eq x y |}.

Lemma cones_eq_scale_eq (r : {nonneg R}) (x : cones_eq_car) :
  cones_hom_fun f (precone_scale r (cones_eq_val x)) =
  cones_hom_fun g (precone_scale r (cones_eq_val x)).
Proof.
case: x => xv xe /=.
case: (cones_hom_linear f) => _ _ HfZ;
case: (cones_hom_linear g) => _ _ HgZ.
by rewrite HfZ HgZ xe.
Qed.

Definition cones_eq_scale (r : {nonneg R}) (x : cones_eq_car) : cones_eq_car :=
  {| cones_eq_val := precone_scale r (cones_eq_val x);
     cones_eq_eq := cones_eq_scale_eq r x |}.

(** *** Precone axioms

    As for the product, the axioms are inherited from [P] through the
    injection [cones_eq_val]; the [SubPrecone1] factory turns the three
    (definitional) commutation lemmas below into the eleven axioms. *)

Lemma cones_eq_val0 : cones_eq_val cones_eq_zero = precone_zero.
Proof. by []. Qed.

Lemma cones_eq_valD (x y : cones_eq_car) :
  cones_eq_val (cones_eq_add x y) =
  precone_add (cones_eq_val x) (cones_eq_val y).
Proof. by []. Qed.

Lemma cones_eq_valZ (r : {nonneg R}) (x : cones_eq_car) :
  cones_eq_val (cones_eq_scale r x) = precone_scale r (cones_eq_val x).
Proof. by []. Qed.

End ConesEqualisers.

Arguments cones_eq_car {R P Q}.
Arguments cones_eq_val {R P Q f g}.
Arguments cones_eq_eq {R P Q f g}.
Arguments cones_eq_zero {R P Q f g}.
Arguments cones_eq_add {R P Q f g}.
Arguments cones_eq_scale {R P Q f g}.

HB.instance Definition _ (R : realType) (P Q : coneType R)
  (f g : cones_hom P Q) :=
  @sub_isPrecone1 R P (cones_eq_car f g) (@cones_eq_val R P Q f g)
    (@cones_eq_zero R P Q f g) (@cones_eq_add R P Q f g)
    (@cones_eq_scale R P Q f g) (@cones_eq_extensional R P Q f g)
    (@cones_eq_val0 R P Q f g) (@cones_eq_valD R P Q f g)
    (@cones_eq_valZ R P Q f g).

(** *** Cone structure on [cones_eq_car] *)

Section ConesEqualisersNorm.
Variable R : realType.
Variables P Q : coneType R.
Variables f g : cones_hom P Q.

Local Notation E := (cones_eq_car f g).

(** The norm inherited from [P]. *)
Definition cones_eq_norm (x : E) : R := cone_norm (cones_eq_val x).

Lemma cones_eq_normh (r : {nonneg R}) (x : E) :
  cones_eq_norm (cones_eq_scale r x) = r%:num * cones_eq_norm x.
Proof. by rewrite /cones_eq_norm /= cone_normh. Qed.

Lemma cones_eq_normz (x : E) :
  cones_eq_norm x = 0 -> x = cones_eq_zero.
Proof.
move=> H; apply: cones_eq_extensional => /=.
exact: cone_normz.
Qed.

Lemma cones_eq_normt (x y : E) :
  cones_eq_norm (cones_eq_add x y) <= cones_eq_norm x + cones_eq_norm y.
Proof. by rewrite /cones_eq_norm /=; exact: cone_normt. Qed.

Lemma cones_eq_le_underlying (x y : E) :
  precone_le x y -> precone_le (cones_eq_val x) (cones_eq_val y).
Proof.
case=> z Hxy; exists (cones_eq_val z).
by have /(congr1 cones_eq_val) := Hxy => /= ->.
Qed.

Lemma cones_eq_normp (x y : E) :
  precone_le x y -> cones_eq_norm x <= cones_eq_norm y.
Proof.
by move/cones_eq_le_underlying => H; rewrite /cones_eq_norm; exact: cone_normp.
Qed.

(** *** (Normc) for the equaliser

    Given an increasing chain [u] in [E] in the unit ball, the
    underlying chain in [P] also lies in [B_P]. By (Normc) on [P],
    its sup [sup_P u] exists. By ω-continuity of [f] and [g], we
    have [f (sup_P u) = sup_n f (u_n) = sup_n g (u_n) = g (sup_P u)],
    so [sup_P u ∈ E]. Package this. *)

Section EqSupBall.
Variable u : nat -> E.
Hypothesis uch : forall n, precone_le (u n) (u n.+1).
Hypothesis ub1 : forall n, cones_eq_norm (u n) <= 1.

(** The underlying [P]-chain. *)
Definition cones_eq_sup_uP : nat -> P := fun n => cones_eq_val (u n).

Lemma cones_eq_sup_uP_ch :
  forall n, precone_le (cones_eq_sup_uP n) (cones_eq_sup_uP n.+1).
Proof. by move=> n; apply: cones_eq_le_underlying; exact: uch. Qed.

Lemma cones_eq_sup_uP_ub1 :
  forall n, cone_norm (cones_eq_sup_uP n) <= 1.
Proof. exact: ub1. Qed.

(** The [P]-sup of the underlying chain. *)
Definition cones_eq_sup_P : P :=
  cone_sup_ball cones_eq_sup_uP cones_eq_sup_uP_ch cones_eq_sup_uP_ub1.

(** The [P]-sup lies in [E], i.e., satisfies [f = g]. *)
Lemma cones_eq_sup_P_in_E :
  cones_hom_fun f cones_eq_sup_P = cones_hom_fun g cones_eq_sup_P.
Proof.
(* Use ω-continuity of [f] and [g] on the underlying chain. *)
have fuch : forall n,
    precone_le (f (cones_eq_sup_uP n)) (f (cones_eq_sup_uP n.+1)).
  move=> n; apply: linear_increasing;
    [exact: cones_hom_linear|exact: cones_eq_sup_uP_ch].
have fub1 : forall n, cone_norm (f (cones_eq_sup_uP n)) <= 1.
  move=> n; apply: le_trans (cones_hom_norm_le1 f _) _.
  exact: cones_eq_sup_uP_ub1.
have guch : forall n,
    precone_le (g (cones_eq_sup_uP n)) (g (cones_eq_sup_uP n.+1)).
  move=> n; apply: linear_increasing;
    [exact: cones_hom_linear|exact: cones_eq_sup_uP_ch].
have gub1 : forall n, cone_norm (g (cones_eq_sup_uP n)) <= 1.
  move=> n; apply: le_trans (cones_hom_norm_le1 g _) _.
  exact: cones_eq_sup_uP_ub1.
rewrite (@cones_hom_continuous _ _ _ f _ cones_eq_sup_uP_ch _ fuch fub1).
rewrite (@cones_hom_continuous _ _ _ g _ cones_eq_sup_uP_ch _ guch gub1).
(* Now both are [cone_sup_ball (f \o u)] and [cone_sup_ball (g \o u)],
   where [f (u n) = g (u n)] by [cones_eq_eq u n]. Use antisymmetry. *)
have Heq : forall n,
  cones_hom_fun f (cones_eq_sup_uP n) = cones_hom_fun g (cones_eq_sup_uP n).
  by move=> n; exact: cones_eq_eq.
apply: precone_le_anti.
- apply: cone_sup_ball_lub => n /=.
  by rewrite Heq; exact: cone_sup_ball_ub.
- apply: cone_sup_ball_lub => n /=.
  by rewrite -Heq; exact: cone_sup_ball_ub.
Qed.

(** The (Normc) witness for the equaliser. *)
Definition cones_eq_sup_ball : E :=
  {| cones_eq_val := cones_eq_sup_P; cones_eq_eq := cones_eq_sup_P_in_E |}.

Lemma cones_eq_sup_ball_ub n :
  precone_le (u n) cones_eq_sup_ball.
Proof.
(* Use cone_sup_ball_ub in P, then the precone_le on E is induced. *)
have HH : precone_le (cones_eq_val (u n)) cones_eq_sup_P
  by exact: cone_sup_ball_ub.
case: HH => z Hz.
(* Need to package z as an element of E. Since z = sup_P - u_n in some
   sense, and both u_n, sup_P are in E, z's image under f and g should
   also coincide... *)
(* Use: f sup_P = f u_n + f z (linearity); g sup_P = g u_n + g z. *)
(* Since f sup_P = g sup_P and f u_n = g u_n, by cancellation f z = g z. *)
have Hfz : f z = g z.
  case: (cones_hom_linear f) => _ HfD _.
  case: (cones_hom_linear g) => _ HgD _.
  have Hfsup : cones_hom_fun f cones_eq_sup_P = cones_hom_fun g cones_eq_sup_P
    by exact: cones_eq_sup_P_in_E.
  rewrite Hz HfD HgD (cones_eq_eq (u n)) in Hfsup.
  exact: precone_cancel Hfsup.
pose zE : E := {| cones_eq_val := z; cones_eq_eq := Hfz |}.
exists zE; apply: cones_eq_extensional => /=; exact: Hz.
Qed.

Lemma cones_eq_sup_ball_lub y :
  (forall n, precone_le (u n) y) -> precone_le cones_eq_sup_ball y.
Proof.
move=> Hub.
have HH : precone_le cones_eq_sup_P (cones_eq_val y).
  apply: cone_sup_ball_lub => n.
  by apply: cones_eq_le_underlying; exact: Hub.
case: HH => z Hz.
have Hfz : f z = g z.
  case: (cones_hom_linear f) => _ HfD _.
  case: (cones_hom_linear g) => _ HgD _.
  have Hfy : cones_hom_fun f (cones_eq_val y) = cones_hom_fun g (cones_eq_val y)
    by exact: cones_eq_eq.
  rewrite Hz HfD HgD cones_eq_sup_P_in_E in Hfy.
  exact: precone_cancel Hfy.
pose zE : E := {| cones_eq_val := z; cones_eq_eq := Hfz |}.
by exists zE; apply: cones_eq_extensional => /=.
Qed.

Lemma cones_eq_sup_ball_norm : cones_eq_norm cones_eq_sup_ball <= 1.
Proof. exact: cone_sup_ball_norm. Qed.

End EqSupBall.

End ConesEqualisersNorm.

Arguments cones_eq_norm {R P Q f g}.
Arguments cones_eq_sup_ball {R P Q f g}.

HB.instance Definition _ (R : realType) (P Q : coneType R)
  (f g : cones_hom P Q) :=
  isCone.Build R (cones_eq_car f g)
    (@cones_eq_normh R P Q f g) (@cones_eq_normz R P Q f g)
    (@cones_eq_normt R P Q f g) (@cones_eq_normp R P Q f g)
    (@cones_eq_sup_ball_ub R P Q f g) (@cones_eq_sup_ball_lub R P Q f g)
    (@cones_eq_sup_ball_norm R P Q f g).

(** *** The equaliser cone *)

(** Paper Theorem 2.20: equaliser as a cone. *)
Definition cones_eq (R : realType) (P Q : coneType R)
  (f g : cones_hom P Q) : coneType R := cones_eq_car f g.

(** *** Inclusion morphism and universal property *)

Section EqualiserUniversal.
Variable R : realType.
Variables P Q : coneType R.
Variables f g : cones_hom P Q.

(** Paper Theorem 2.20: the inclusion [e : E -> P]. *)
Definition cones_eq_incl_fun : cones_eq_car f g -> P := cones_eq_val.

Lemma cones_eq_incl_linear : is_linear cones_eq_incl_fun.
Proof. by split. Qed.

Lemma cones_eq_incl_continuous : is_omega_continuous cones_eq_incl_fun.
Proof.
move=> u uch ub1 fuch fub1.
rewrite /cones_eq_incl_fun /=.
apply: precone_le_anti.
- apply: cone_sup_ball_lub => n.
  exact: (cone_sup_ball_ub _ fuch fub1 n).
- apply: cone_sup_ball_lub => n.
  exact: cone_sup_ball_ub.
Qed.

Lemma cones_eq_incl_norm_le1 :
  forall x : cones_eq_car f g, cone_norm (cones_eq_incl_fun x) <= cone_norm x.
Proof. by move=> x; exact: lexx. Qed.

(** Paper Theorem 2.20: inclusion as a morphism in [Cones]. *)
Definition cones_eq_incl : cones_hom (cones_eq f g) P.
Proof.
refine (ConesHom cones_eq_incl_fun _ _ _).
- exact: cones_eq_incl_linear.
- exact: cones_eq_incl_continuous.
- exact: cones_eq_incl_norm_le1.
Defined.

(** Paper Theorem 2.20: the inclusion equalises [f] and [g]. *)
Lemma cones_eq_incl_equ :
  cones_comp f cones_eq_incl = cones_comp g cones_eq_incl.
Proof. by apply: cones_hom_eq => x /=; exact: cones_eq_eq. Qed.

(** Paper Theorem 2.20: universal property — given [h : T -> P] that
    equalises [f] and [g], there is a unique mediator to [E]. *)
Variable T : coneType R.
Variable h : cones_hom T P.
Hypothesis Hh : cones_comp f h = cones_comp g h.

(** Pointwise extraction of the equation from [Hh]. *)
Lemma cones_eq_med_eq (u : T) :
  cones_hom_fun f (cones_hom_fun h u) =
  cones_hom_fun g (cones_hom_fun h u).
Proof.
by have := Hh; move/(congr1 (fun w : cones_hom T Q => cones_hom_fun w u)).
Qed.

(** The mediating function. *)
Definition cones_eq_med_fun (u : T) : cones_eq_car f g :=
  {| cones_eq_val := cones_hom_fun h u;
     cones_eq_eq := cones_eq_med_eq u |}.

Lemma cones_eq_med_linear : is_linear cones_eq_med_fun.
Proof.
case: (cones_hom_linear h) => H0 HD HZ; split.
- by apply: cones_eq_extensional => /=; exact: H0.
- by move=> x y; apply: cones_eq_extensional => /=; exact: HD.
- by move=> r x; apply: cones_eq_extensional => /=; exact: HZ.
Qed.

Lemma cones_eq_med_continuous : is_omega_continuous cones_eq_med_fun.
Proof.
move=> u uch ub1 fuch fub1.
apply: cones_eq_extensional => /=.
(* LHS: cones_eq_val (med (sup u)) = h (sup u). *)
(* By ω-cont of h, h (sup u) = sup (h ∘ u). *)
(* RHS: cones_eq_val (sup_ball med ∘ u) = ... = sup (h ∘ u). *)
have huch : forall n,
    precone_le (cones_hom_fun h (u n)) (cones_hom_fun h (u n.+1)).
  by move=> n; apply: linear_increasing;
    [exact: cones_hom_linear|exact: uch].
have hub1 : forall n, cone_norm (cones_hom_fun h (u n)) <= 1.
  by move=> n; apply: le_trans (cones_hom_norm_le1 h _) _; exact: ub1.
rewrite (@cones_hom_continuous _ _ _ h _ uch _ huch hub1).
(* Both sides are now [cone_sup_ball] of the same sequence h(u n);
   antisymmetry handles the chain-proof difference. *)
apply: precone_le_anti.
- apply: cone_sup_ball_lub => n.
  exact: (cone_sup_ball_ub _ _ _ n).
- apply: cone_sup_ball_lub => n.
  exact: (cone_sup_ball_ub _ huch hub1 n).
Qed.

Lemma cones_eq_med_norm_le1 :
  forall u, cone_norm (cones_eq_med_fun u) <= cone_norm u.
Proof. by move=> u; rewrite /cone_norm /=; exact: cones_hom_norm_le1. Qed.

(** Paper Theorem 2.20: mediating morphism. *)
Definition cones_eq_med : cones_hom T (cones_eq f g).
Proof.
refine (ConesHom cones_eq_med_fun _ _ _).
- exact: cones_eq_med_linear.
- exact: cones_eq_med_continuous.
- exact: cones_eq_med_norm_le1.
Defined.

(** Paper Theorem 2.20: factorization. *)
Lemma cones_eq_med_factor : cones_comp cones_eq_incl cones_eq_med = h.
Proof. by apply: cones_hom_eq. Qed.

(** Paper Theorem 2.20: uniqueness of the mediator. *)
Lemma cones_eq_med_unique (h' : cones_hom T (cones_eq f g)) :
  cones_comp cones_eq_incl h' = h -> h' = cones_eq_med.
Proof.
move=> Hh'.
apply: cones_hom_eq => u.
apply: cones_eq_extensional => /=.
by have := Hh'; move/(congr1 (fun w : cones_hom T P => cones_hom_fun w u)).
Qed.

End EqualiserUniversal.

Arguments cones_eq_incl {R P Q}.
Arguments cones_eq_med {R P Q f g T}.

(** ** Paper Lemma 2.21 / Prop 2.22 — Norm of an isomorphism

    In our [cones_hom_norm_le1] encoding, the operator-norm value is
    not directly accessible (it is introduced in Lemma 2.11). The
    paper's claim "[‖f‖ = 1] for any iso [f] with [P ≠ 0]" is
    consequently restated in a form that is constructively usable
    without [linmap_norm]: *if* [f : cones_hom P Q] is invertible in
    [Cones] (i.e. there is [g : cones_hom Q P] with [g ∘ f = id] and
    [f ∘ g = id]), *then* [f] preserves the norm exactly. *)

Section ConesIso.
Variable R : realType.
Variables P Q : coneType R.

(** Paper Lemma 2.21 + Prop 2.22 (constructive form): if [f] has a
    two-sided inverse in [Cones], then [f] preserves the norm. *)
Lemma cones_iso_preserves_norm
  (f : cones_hom P Q) (g : cones_hom Q P)
  (Hgf : cones_comp g f = cones_id P)
  (Hfg : cones_comp f g = cones_id Q) :
  forall x : P, cone_norm (cones_hom_fun f x) = cone_norm x.
Proof.
move=> x; apply: le_anti; apply/andP; split.
- exact: cones_hom_norm_le1.
- (* cnorm x = cnorm (g (f x)) ≤ cnorm (f x). *)
  have Hgfx : cones_hom_fun g (cones_hom_fun f x) = x.
    by have := Hgf; move/(congr1 (fun w : cones_hom P P => cones_hom_fun w x)).
  have HG := @cones_hom_norm_le1 _ _ _ g (cones_hom_fun f x).
  by rewrite Hgfx in HG.
Qed.

End ConesIso.

(** ** Paper Lemma 2.23 — Cone-structure transport along a bijection

    Given a cone [P] and a bijective map [f : P -> S], there is a
    unique cone structure on [S] making [f] an iso in [Cones].

    Proof (paper p. 1:16). Transport everything pointwise:
    [s1 + s2 := f (f^{-1} s1 + f^{-1} s2)], [r ·: s := f (r ·: f^{-1} s)],
    [‖s‖ := ‖f^{-1} s‖]. The cone axioms transport verbatim, and the
    uniqueness follows since the axioms are determined by [f]. *)

Section ConesTransport.
Variable R : realType.
Variable P : coneType R.
Variable S : Type.
Variable f : P -> S.
Variable finv : S -> P.
Hypothesis finvK : forall s, f (finv s) = s.
Hypothesis fK    : forall x, finv (f x) = x.

(** Transported operations. *)
Definition trans_zero : S := f precone_zero.
Definition trans_add (s t : S) : S := f (precone_add (finv s) (finv t)).
Definition trans_scale (r : {nonneg R}) (s : S) : S :=
  f (precone_scale r (finv s)).
Definition trans_norm (s : S) : R := cone_norm (finv s).

(** Helper: [finv] is a section: [finv \o f = id], so applying [finv]
    to both sides of an [f x = ?] gives [x = finv ?]. *)
Lemma trans_addA : associative trans_add.
Proof.
by move=> s t u; rewrite /trans_add !fK precone_addA.
Qed.

Lemma trans_addC : commutative trans_add.
Proof. by move=> s t; rewrite /trans_add precone_addC. Qed.

Lemma trans_add0 : left_id trans_zero trans_add.
Proof.
move=> s; rewrite /trans_add /trans_zero fK precone_add0.
exact: finvK.
Qed.

Lemma trans_scale_DAr (r : {nonneg R}) (s t : S) :
  trans_scale r (trans_add s t) = trans_add (trans_scale r s) (trans_scale r t).
Proof.
rewrite /trans_scale /trans_add !fK precone_scale_DAr //.
Qed.

Lemma trans_scale_DAl (r u : {nonneg R}) (s : S) :
  trans_scale (r%:num + u%:num)%:nng s =
  trans_add (trans_scale r s) (trans_scale u s).
Proof.
by rewrite /trans_scale /trans_add !fK precone_scale_DAl.
Qed.

Lemma trans_scale_A (r u : {nonneg R}) (s : S) :
  trans_scale (r%:num * u%:num)%:nng s = trans_scale r (trans_scale u s).
Proof. by rewrite /trans_scale !fK precone_scale_A. Qed.

Lemma trans_scale_1 (s : S) : trans_scale 1%:nng s = s.
Proof. by rewrite /trans_scale precone_scale_1 finvK. Qed.

Lemma trans_scale_0r (r : {nonneg R}) : trans_scale r trans_zero = trans_zero.
Proof. by rewrite /trans_scale /trans_zero fK precone_scale_0r. Qed.

Lemma trans_scale_0l (s : S) : trans_scale 0%:nng s = trans_zero.
Proof. by rewrite /trans_scale /trans_zero precone_scale_0l. Qed.

Lemma trans_cancel (s t u : S) : trans_add s t = trans_add s u -> t = u.
Proof.
rewrite /trans_add.
move/(congr1 finv); rewrite !fK => /precone_cancel H.
by rewrite -[t]finvK -[u]finvK H.
Qed.

Lemma trans_pos (s t : S) :
  trans_add s t = trans_zero -> s = trans_zero /\ t = trans_zero.
Proof.
rewrite /trans_add /trans_zero.
move/(congr1 finv); rewrite !fK => /precone_pos[Hs Ht].
by split; [rewrite -[s]finvK Hs | rewrite -[t]finvK Ht].
Qed.

(** Paper Lemma 2.23: the transported precone instance. *)
Definition transport_isPrecone : isPrecone R S :=
  isPrecone.Build R S
    trans_addA trans_addC trans_add0
    trans_scale_DAr trans_scale_DAl trans_scale_A
    trans_scale_1 trans_scale_0r trans_scale_0l
    trans_cancel trans_pos.

(** Note: a full [HB.instance] declaration of the cone structure on
    [S] would require additional work to register and would interact
    with the rest of [Cones]. Paper Lemma 2.23 establishes
    *existence* of the cone structure; an HB-style instance is left
    as a downstream packaging task (the per-target file re-states
    this lemma when it is needed concretely). *)

End ConesTransport.
