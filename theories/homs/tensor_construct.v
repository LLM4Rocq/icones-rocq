(**md**************************************************************************)
(* # Tensor discharge T1 — the tensor [B ⊗ C] as the SAFT left adjoint of     *)
(*   [(C ⊸ −)], with the hom-bijection PROVED (Paper §5.4, Thm 5.9 +          *)
(*   [th:Icones-adjoint-functor]).                                            *)
(*                                                                            *)
(* This file DISCHARGES, as genuine theorems about a concrete construction,   *)
(* the first eight [Parameter]s of [theories/axioms/saft_interface.v]:        *)
(*                                                                            *)
(*   tensor, tensor_curry, tensor_uncurry, tensor_curryK, tensor_uncurryK,    *)
(*   tensor_curry_natural_post, tensor_curry_natural_D, tensor_curry_natural_B *)
(*                                                                            *)
(* It is AXIOM-FREE relative to the classical [boolp] base ([pselect]/[cid]/  *)
(* extensionality) — NO [Axiom]/[Parameter]/[Admitted], and it does NOT       *)
(* import [saft_interface]: the proved versions are built from scratch, in    *)
(* their own module [Icones.homs.tensor_construct], so they do not clash with *)
(* the interface's same-named [Parameter]s (consumers still import the        *)
(* interface; this is the parallel proved development that milestone T2 will   *)
(* eventually flip to).                                                        *)
(*                                                                            *)
(* ## The construction (PLAN §13.1/§13.2, Riehl 4.6.11 with [Φ = {1}])         *)
(*                                                                            *)
(* Fix integrable cones [B], [C].  Write [1 := cone_one_car Ar] (the          *)
(* coseparator).                                                              *)
(*                                                                            *)
(*  1. [J := icones_hom Ar B (C ⊸ 1)] — a [Type] (the homset of [C ⊸ 1]).     *)
(*  2. [p := icones_prod (fun _ : J => 1)] — the coseparator power [1^J].      *)
(*  3. The universal map [e_B : B → C ⊸ p], the tuple of all [J]-elements      *)
(*     transported into [C ⊸ p] through [limpl_preserves_prod]:                *)
(*       [e_B := iso_bwd (limpl_preserves_prod C _) ∘ icones_tuple id_J].      *)
(*  4. [tensor B C := wi_obj] (the wide intersection of [representable.v]),     *)
(*     over the family [K] of all subobjects [(A, h)] of [p] through which     *)
(*     [e_B] factors via [C ⊸ h] (i.e. [∃ eA, (C ⊸ h) ∘ eA = e_B]);            *)
(*     the basepoint [k0] is the identity subobject [p ↪ p] (which factors     *)
(*     [e_B] by [eA := e_B]).  In Rocq's predicative [Type] theory the family  *)
(*     is just a [Type], so [wi_obj] applies directly (well-poweredness        *)
(*     [icones_well_powered] is what makes this small set-theoretically; here  *)
(*     it is automatic).                                                        *)
(*  5. [tau' : B → C ⊸ (B ⊗ C)] — co-restrict [e_B] through [C ⊸ wi_incl],     *)
(*     using that [C ⊸ −] preserves the product-then-equaliser limit           *)
(*     [wi_obj] ([limpl_preserves_prod] + [limpl_eq_med] of                    *)
(*     [limpl_continuous.v]).                                                  *)
(*                                                                            *)
(* ## The discharge                                                            *)
(*                                                                            *)
(*  - [tensor_curry f := (C ⊸ f) ∘ tau'] (= [linhom_post_icones f ∘ tau']).    *)
(*  - [tensor_uncurry g] := the SAFT mediator with [(C ⊸ uncurry g) ∘ tau' = g].*)
(*  - [tensor_uncurryK] : DIRECT (the defining equation of [tensor_uncurry]).  *)
(*  - [tensor_curryK]   : by coseparator + the mediator uniqueness.            *)
(*  - the three naturalities : from [linhom_post] functoriality + uniqueness.  *)
(*                                                                            *)
(* APIs used: [representable.v] — [wi_obj]/[wi_incl]/[wi_proj]/[wi_med]/        *)
(* [wi_med_proj]/[wi_med_unique]/[wi_factors_each]; [icones_well_powered].     *)
(* [limpl_continuous.v] — [limpl_preserves_prod] + its [iso_bwd] and the       *)
(* equaliser co-restriction [limpl_eq_med]/[limpl_eq_med_factor]/             *)
(* [limpl_eq_med_unique].                                                      *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals.

Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.cone_cat.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.icone.
Require Import Icones.icones.examples_icone.
Require Import Icones.icones.icone_cat.
Require Import Icones.icones.representable.
Require Import Icones.homs.linhom.
Require Import Icones.homs.linhom_functor.
Require Import Icones.homs.icones_iso.
Require Import Icones.homs.limpl_continuous.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Module Icones_tensor_construct.

(** ** Functoriality of the post-composition action [C ⊸ −]

    [linhom_post_icones] ([C ⊸ g]) is the action of the hom-functor in
    its covariant (codomain) slot.  We need its identity / composition
    laws as one-sided specialisations of the bifunctor laws
    [linhom_map_icones_id] / [linhom_map_icones_comp] from
    [linhom_functor.v]. *)

Section LinhomPostFunctor.
Variables (R : realType) (Ar : MeasSubcat R).
Variable C : ICone.type Ar.

(** [C ⊸ id_D = id_{C ⊸ D}]. *)
Lemma linhom_post_id (D : ICone.type Ar) :
  linhom_post_icones (C := C) (icones_id Ar D) = icones_id Ar (linhom_car Ar C D).
Proof. exact: linhom_map_icones_id. Qed.

(** [C ⊸ (g ∘ f) = (C ⊸ g) ∘ (C ⊸ f)]. *)
Lemma linhom_post_comp (D1 D2 D3 : ICone.type Ar)
    (f : icones_hom Ar D1 D2) (g : icones_hom Ar D2 D3) :
  linhom_post_icones (C := C) (icones_comp g f) =
  icones_comp (linhom_post_icones (C := C) g) (linhom_post_icones (C := C) f).
Proof.
rewrite /linhom_post_icones.
have := linhom_map_icones_comp (icones_id Ar C) (icones_id Ar C) f g.
by rewrite icones_compIl => ->.
Qed.

End LinhomPostFunctor.

(** ** The coseparator power and the universal map [e_B]

    Fix [B], [C].  The coseparator is [1 := cone_one_car Ar].  The
    index type [J := ICones(B, C ⊸ 1)] is the homset of [C ⊸ 1]; the
    power is [p := 1^J = icones_prod (fun _ : J => 1)].

    The universal map [e_B : B → C ⊸ p] is, transported through Thm 5.9
    ([limpl_preserves_prod]), the tuple of all elements of [J]:
      [e_B := iso_bwd (limpl_preserves_prod C _) ∘ ⟨ j ⟩_{j ∈ J}]. *)

Section UniversalMap.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : ICone.type Ar.

Local Notation Cone1 := (cone_one_car Ar).

(** The index type [J = ICones(B, C ⊸ 1)]. *)
Definition tJ : Type := icones_hom Ar B (linhom_car Ar C Cone1).

(** The constant family at [1] and the coseparator power [p = 1^J]. *)
Definition tpfam (_ : tJ) : ICone.type Ar := Cone1.
Definition tp : ICone.type Ar := icones_prod tpfam.

(** Thm 5.9 iso [C ⊸ p ≅ ∏_J (C ⊸ 1)]. *)
Local Notation isoP := (limpl_preserves_prod C tpfam).

(** The tuple of all [J]-elements [⟨ j ⟩_{j ∈ J} : B → ∏_J (C ⊸ 1)]. *)
Definition tJtuple :
    icones_hom Ar B (icones_prod (fun j => linhom_car Ar C (tpfam j))) :=
  icones_tuple (B := fun j => linhom_car Ar C (tpfam j)) (fun j : tJ => j).

(** The universal map [e_B : B → C ⊸ p]. *)
Definition eB : icones_hom Ar B (linhom_car Ar C tp) :=
  icones_comp (iso_bwd isoP) tJtuple.

End UniversalMap.

Arguments tJ {R Ar} B C.
Arguments tp {R Ar} B C.
Arguments eB {R Ar} B C.

(** ** The factoring family and the tensor object [B ⊗ C]

    A member of the family is a subobject-like datum: a domain [fs_dom],
    an embedding [fs_hom : fs_dom → p], and a *factoring witness*
    [fs_eA : B → C ⊸ fs_dom] with [(C ⊸ fs_hom) ∘ fs_eA = e_B].  In
    Rocq's predicative type theory this family is just a [Type]; the
    paper's well-poweredness ([icones_well_powered], [representable.v])
    is what guarantees it is a *set* — automatic here — so the wide
    intersection [wi_obj] applies directly.

    The basepoint [k0] is the identity subobject [(p, id_p, e_B)], which
    factors [e_B] trivially ([(C ⊸ id) ∘ e_B = e_B]).

    [tensor B C := wi_obj] over this family. *)

Section TensorObject.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : ICone.type Ar.

Local Notation p := (tp B C).

(** A member of the factoring family of subobjects of [p = 1^J]: a
    domain, an *injective* embedding into [p] (a subobject, [SA1] of
    [representable.v]), and a *factoring witness* of [e_B] through
    [C ⊸ −] applied to that embedding. *)
Record fsub : Type := MkFsub {
  fs_dom : ICone.type Ar;
  fs_hom : icones_hom Ar fs_dom p;
  fs_inj : is_icones_inj fs_hom;
  fs_eA : icones_hom Ar B (linhom_car Ar C fs_dom);
  fs_fact :
    icones_comp (linhom_post_icones (C := C) fs_hom) fs_eA = eB B C;
}.

(** The underlying subobject of a family member.  Destructured via
    [match] so the [fs_inj] projector's auto-added [injective] arguments
    do not leak into the application. *)
Definition fs_sub (k : fsub) : icones_subobject p :=
  match k with
  | MkFsub A h hinj eA Hf => MkSubobject A h hinj
  end.

(** The basepoint subobject [(p, id_p, e_B)], which factors [e_B]
    trivially ([C ⊸ id = id]) and is a mono ([id] is injective). *)
Lemma fk0_fact :
  icones_comp (linhom_post_icones (C := C) (icones_id Ar p)) (eB B C) = eB B C.
Proof. by rewrite linhom_post_id icones_compIl. Qed.

Lemma fk0_inj : is_icones_inj (icones_id Ar p).
Proof. by move=> x y. Qed.

Definition fbase : fsub :=
  {| fs_dom := p; fs_hom := icones_id Ar p; fs_inj := fk0_inj;
     fs_eA := eB B C; fs_fact := fk0_fact |}.

(** *** The small index — well-poweredness

    The family is indexed by the *small* subobject classifier
    [SubobjClassifier p] ([representable.v], well-poweredness Thm 4.18),
    NOT by the proper-class record [fsub] (which packs an
    [ICone.type Ar] and is therefore too large to index the wide
    intersection [wi_obj], whose index [K : Type] lives below the cone
    universe — a hard universe constraint in the frozen [representable.v]).

    For each classifier value [s] we *choose* (classically,
    [pselect]/[cid]) a factoring subobject whose classifier is [s],
    defaulting to the basepoint [fbase] when none exists.  By
    well-poweredness, two factoring subobjects with the same classifier
    are iso over [p] ([icones_subobject_classP]); so indexing by the
    classifier loses no subobject up to iso — exactly the role
    [icones_well_powered] plays in the SAFT solution-set construction
    (Riehl 4.6.10). *)
Definition fK : Type := SubobjClassifier p.

(** A chosen factoring subobject with classifier value [s] (or [fbase]).
    Every value of [fpick] is a genuine [fsub], hence factors [e_B]. *)
Definition fpick (s : fK) : fsub :=
  match pselect (exists k : fsub, icones_subobject_class (fs_sub k) = s) with
  | left e => proj1_sig (cid e)
  | right _ => fbase
  end.

(** The family data fed to [wi_obj]: domains and embeddings of the
    chosen representatives. *)
Definition fAdom (s : fK) : ICone.type Ar := fs_dom (fpick s).
Definition fhh (s : fK) : icones_hom Ar (fAdom s) p := fs_hom (fpick s).

(** The basepoint index: the classifier value of [fbase].  Its chosen
    representative [fpick fk0] is a factoring subobject (it factors
    [e_B]), the only property the [tau'] co-restriction needs. *)
Definition fk0 : fK := icones_subobject_class (fs_sub fbase).

(** The tensor object [B ⊗ C] as the wide intersection of the family. *)
Definition tensor : ICone.type Ar := wi_obj fhh fk0.

(** The intersection embedding [B ⊗ C ↪ p]. *)
Definition tensor_incl : icones_hom Ar tensor p := wi_incl fAdom fhh fk0.

(** Each chosen representative factors [e_B] through [C ⊸ (its
    embedding)]: [(C ⊸ fhh s) ∘ fs_eA (fpick s) = e_B]. *)
Lemma fpick_fact (s : fK) :
  icones_comp (linhom_post_icones (C := C) (fhh s)) (fs_eA (fpick s)) = eB B C.
Proof. exact: fs_fact. Qed.

(** *** Pointwise value of [e_B] and of the tuple of factoring witnesses

    [e_B b c . j = j b c] (the [j]-th component of [e_B b c ∈ p = 1^J] is
    [j] applied to [b] then evaluated at [c]). *)

(** [tJtuple]'s [j]-component is [j] itself: [tJtuple b . j = j b]. *)
Lemma tJtupleE (b : B) (j : tJ B C) :
  cones_prod_val ((tJtuple B C : icones_hom _ _ _) b) j = (j : icones_hom _ _ _) b.
Proof.
have := icones_tuple_proj (B := fun j0 : tJ B C => linhom_car Ar C (tpfam j0))
          (fun j0 : tJ B C => j0) j.
by move/(congr1 (fun w : icones_hom Ar B (linhom_car Ar C (tpfam j)) =>
                   (w : icones_hom _ _ _) b)).
Qed.

(** Pointwise value of [e_B]: [e_B b c . j = j b c]. *)
Lemma eBE (b : B) (c : C) (j : tJ B C) :
  cones_prod_val (linhom_fun ((eB B C : icones_hom _ _ _) b) c) j =
  linhom_fun ((j : icones_hom _ _ _) b) c.
Proof. by rewrite /eB /=. Qed.

End TensorObject.

Arguments tJtupleE {R Ar B C}.
Arguments eBE {R Ar B C}.
Arguments fsub {R Ar} B C.
Arguments fK {R Ar B C}.
Arguments fAdom {R Ar B C}.
Arguments fhh {R Ar B C}.
Arguments fk0 {R Ar B C}.
Arguments fpick {R Ar B C}.
Arguments fpick_fact {R Ar B C}.
Arguments tensor {R Ar} B C.
Arguments tensor_incl {R Ar} B C.

(** ** The universal element [tau' : B → C ⊸ (B ⊗ C)]

    [B ⊗ C = wi_obj] is, by construction ([representable.v]), the
    equaliser [icones_eq (wi_u fhh) (wi_v fhh fk0)] of two maps
    [wi_prod fAdom → wi_pprod].  Since [C ⊸ −] preserves this equaliser
    ([limpl_eq_med] of [limpl_continuous.v]), we co-restrict the
    universal map [e_prod : B → C ⊸ wi_prod] — the inverse-transported
    tuple of the factoring witnesses — through [C ⊸ (eq inclusion)],
    obtaining [tau'].  Its defining factorisation
    [(C ⊸ wi_incl) ∘ tau' = e_B] then follows from [fpick_fact]. *)

Section Tau.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : ICone.type Ar.

Local Notation p := (tp B C).
Local Notation K := (@fK R Ar B C).
Local Notation Adom := (@fAdom R Ar B C).
Local Notation hh := (@fhh R Ar B C).
Local Notation k0 := (@fk0 R Ar B C).

(** The product of the family domains [wi_prod fAdom = ∏_s fAdom s]. *)
Local Notation Wprod := (wi_prod Adom).

(** The two parallel maps whose equaliser is [B ⊗ C]. *)
Local Notation WU := (wi_u hh).
Local Notation WV := (wi_v hh k0).

(** [B ⊗ C] is the equaliser of [WU], [WV] (definitionally). *)
Lemma tensorE : tensor B C = icones_eq WU WV.
Proof. by []. Qed.

(** The tuple of factoring witnesses [⟨ fs_eA (fpick s) ⟩_s :
    B → ∏_s (C ⊸ fAdom s)]. *)
Definition eAtuple :
    icones_hom Ar B (icones_prod (fun s : K => linhom_car Ar C (Adom s))) :=
  icones_tuple (B := fun s : K => linhom_car Ar C (Adom s))
    (fun s : K => fs_eA (fpick s)).

(** The universal map [e_prod : B → C ⊸ wi_prod], the factoring tuple
    transported back through Thm 5.9 ([limpl_preserves_prod]). *)
Definition eprod : icones_hom Ar B (linhom_car Ar C Wprod) :=
  icones_comp (iso_bwd (limpl_preserves_prod C Adom)) eAtuple.

(** Pointwise component value of [e_prod]:
    [e_prod b c . s = fs_eA (fpick s) b c]. *)
Lemma eprodE (b : B) (c : C) (s : K) :
  cones_prod_val (linhom_fun ((eprod : icones_hom _ _ _) b) c) s =
  linhom_fun ((fs_eA (fpick s) : icones_hom _ _ _) b) c.
Proof. by rewrite /eprod /=. Qed.

(** Pointwise component of [WU] / [WV] (the two product maps).
    [WU x . k = hh k (x . k)] and [WV x . k = hh k0 (x . k0)]. *)
Lemma WUE (x : Wprod) (k : K) :
  cones_prod_val ((WU : icones_hom _ _ _) x) k =
  (hh k : icones_hom _ _ _) (cones_prod_val x k).
Proof.
have := icones_tuple_proj (Q := Wprod)
          (fun k0 => icones_comp (hh k0) (wi_pi Adom k0)) k.
by move/(congr1 (fun w : icones_hom Ar Wprod p => (w : icones_hom _ _ _) x)) => /= ->.
Qed.

Lemma WVE (x : Wprod) (k : K) :
  cones_prod_val ((WV : icones_hom _ _ _) x) k =
  (hh k0 : icones_hom _ _ _) (cones_prod_val x k0).
Proof.
have := icones_tuple_proj (Q := Wprod)
          (fun _ : K => icones_comp (hh k0) (wi_pi Adom k0)) k.
by move/(congr1 (fun w : icones_hom Ar Wprod p => (w : icones_hom _ _ _) x)) => /= ->.
Qed.

(** The factoring witness, evaluated pointwise:
    [hh s (fs_eA (fpick s) b c) = e_B b c]. *)
Lemma fpick_factE (b : B) (c : C) (s : K) :
  (hh s : icones_hom _ _ _) (linhom_fun ((fs_eA (fpick s) : icones_hom _ _ _) b) c) =
  linhom_fun ((eB B C : icones_hom _ _ _) b) c.
Proof.
have := fpick_fact s.
move/(congr1 (fun w : icones_hom Ar B (linhom_car Ar C p) =>
                (w : icones_hom _ _ _) b)).
move/(congr1 (fun f : linhom_car Ar C p => linhom_fun f c)).
by rewrite /= linhom_map_funE /=.
Qed.

(** The equalising condition: [e_prod] equalises [C ⊸ WU] and [C ⊸ WV].
    Pointwise, both [k]-components reduce — via [WUE]/[WVE], [eprodE] and
    the factoring [fpick_factE] — to [e_B b c]. *)
Lemma eprod_equ :
  icones_comp (linhom_post_icones (C := C) WU) eprod =
  icones_comp (linhom_post_icones (C := C) WV) eprod.
Proof.
apply: icones_hom_eq => b.
rewrite /=.
apply: linhom_eq => c.
rewrite !linhom_map_funE /=.
apply: cones_prod_eq => k.
rewrite WUE WVE !eprodE.
by rewrite !fpick_factE.
Qed.

(** *** [tau'] by co-restriction through [C ⊸ (eq inclusion)]

    [B ⊗ C = icones_eq WU WV], and [C ⊸ −] preserves this equaliser, so
    [e_prod] (equalising [C ⊸ WU], [C ⊸ WV]) co-restricts uniquely. *)

Definition tau' : icones_hom Ar B (linhom_car Ar C (tensor B C)) :=
  limpl_eq_med_icones C eprod eprod_equ.

(** Factorisation through the equaliser inclusion:
    [(C ⊸ eq_incl) ∘ tau' = e_prod]. *)
Lemma tau'_eq_incl :
  icones_comp (linhom_post_icones (C := C) (icones_eq_incl WU WV)) tau' = eprod.
Proof. exact: (limpl_eq_med_factor C eprod eprod_equ). Qed.

(** The DEFINING factorisation of the universal element:
    [(C ⊸ wi_incl) ∘ tau' = e_B].  This is Paper Eq 5.1's universal
    property of [tau'].  Both sides are maps [B → C ⊸ p]; pointwise the
    [j]-th [p]-component reduces, via [tau'_eq_incl]/[eprodE]/[fpick_factE]
    and [eBE], to [j b c]. *)
Lemma tau'_def :
  icones_comp (linhom_post_icones (C := C) (tensor_incl B C)) tau' = eB B C.
Proof.
rewrite /tensor_incl /wi_incl -/WU -/WV.
rewrite linhom_post_comp -icones_compA tau'_eq_incl.
apply: icones_hom_eq => b.
rewrite /=.
apply: linhom_eq => c.
rewrite linhom_map_funE /=.
apply: cones_prod_eq => j.
rewrite eBE (fpick_factE b c k0) eBE.
by [].
Qed.

End Tau.

Arguments tau' {R Ar} B C.
Arguments tau'_def {R Ar B C}.

(** ** [tensor_curry] and the naturalities not needing [tensor_uncurry]

    [tensor_curry f := (C ⊸ f) ∘ tau'] is the forward hom-map
    [ICones(B ⊗ C, D) → ICones(B, C ⊸ D)] (Paper Thm 5.9 / Eq 5.1).
    Two of its naturalities follow from the functoriality of [C ⊸ −]
    ([linhom_post_comp]) alone, without the inverse [tensor_uncurry]. *)

Section TensorCurry.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : ICone.type Ar.

(** Paper Eq 5.1: the forward currying map. *)
Definition tensor_curry (D : ICone.type Ar) (f : icones_hom Ar (tensor B C) D) :
    icones_hom Ar B (linhom_car Ar C D) :=
  icones_comp (linhom_post_icones (C := C) f) (tau' B C).

(** Naturality of [Φ] in [D] (concrete form, Paper Thm 5.9):
    [Φ (h ∘ f) = (C ⊸ h) ∘ Φ f].  By [linhom_post_comp]
    ([C ⊸ (h ∘ f) = (C ⊸ h) ∘ (C ⊸ f)]) composed with [tau']. *)
Lemma tensor_curry_natural_post (D D' : ICone.type Ar)
    (h : icones_hom Ar D D') (f : icones_hom Ar (tensor B C) D) :
  tensor_curry (icones_comp h f) =
  icones_comp (linhom_post_icones (C := C) h) (tensor_curry f).
Proof.
by rewrite /tensor_curry linhom_post_comp -icones_compA.
Qed.

(** Paper Eq 5.1, pointwise: [Φ(f)(x)(y) = f(τ'(x)(y))].  Direct from
    the definition [tensor_curry f = (C ⊸ f) ∘ tau']. *)
Lemma tensor_curryE (D : ICone.type Ar) (f : icones_hom Ar (tensor B C) D)
    (x : B) (y : C) :
  linhom_fun ((tensor_curry f : icones_hom _ _ _) x) y =
  (f : icones_hom _ _ _) (linhom_fun ((tau' B C : icones_hom _ _ _) x) y).
Proof. by rewrite /tensor_curry /= linhom_map_funE /=. Qed.

(** Naturality of [Φ] in [D] (existential form, the [saft_interface]
    signature): the witness is [C ⊸ h = linhom_post_icones h]. *)
Lemma tensor_curry_natural_D (D D' : ICone.type Ar)
    (h : icones_hom Ar D D') :
  exists hstar : icones_hom Ar (linhom_car Ar C D) (linhom_car Ar C D'),
    forall f : icones_hom Ar (tensor B C) D,
      tensor_curry (icones_comp h f) = icones_comp hstar (tensor_curry f).
Proof.
exists (linhom_post_icones (C := C) h) => f.
exact: tensor_curry_natural_post.
Qed.

End TensorCurry.

Arguments tensor_curry {R Ar B C D}.
Arguments tensor_curry_natural_post {R Ar B C D D'}.
Arguments tensor_curry_natural_D {R Ar B C D D'}.

End Icones_tensor_construct.
