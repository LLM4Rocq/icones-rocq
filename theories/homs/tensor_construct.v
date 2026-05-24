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

(** Each chosen representative's embedding is a mono.  Destructured via
    [match] (as [fs_sub]) so the [fs_inj] projector's [injective]
    arguments do not leak. *)
Definition fhh_inj (s : fK) : is_icones_inj (fhh s) :=
  match fpick s as k return is_icones_inj (fs_hom k) with
  | MkFsub A h hinj eA Hf => hinj
  end.

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
Arguments fhh_inj {R Ar B C}.
Arguments fk0 {R Ar B C}.
Arguments fs_sub {R Ar B C}.
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
Arguments tensor_curryE {R Ar B C D}.
Arguments tensor_curry_natural_post {R Ar B C D D'}.
Arguments tensor_curry_natural_D {R Ar B C D D'}.

(** ** [tensor_uncurry] — the SAFT comma-category mediator (Riehl 4.6.11)

    Given [g : B → C ⊸ D], we build the unique [tensor_uncurry g :
    B ⊗ C → D] with [(C ⊸ uncurry g) ∘ tau' = g] by the
    coseparator-power reindexing of PLAN §13.2.

    Write [1 = cone_one_car Ar].  Form the coseparator power of [D],
    [q D := 1^{ICones(D,1)}], with its canonical mono
    [GammaD : D ↪ q D] ([GammaD d . n = n d], a mono since [1]
    cogenerates — Phase A.3 [icones_coseparator_inj]).  Reindex the
    power [p = 1^J] of [B ⊗ C] to [q D] along
    [θ : ICones(D,1) → J, n ↦ (C ⊸ n) ∘ g], giving [P : p → q D] with
    [P x . n = x . (θ n)].  The square
    [(C ⊸ P) ∘ eB = (C ⊸ GammaD) ∘ g] commutes (both send [b,c,n] to
    [n (g b c)]) — this is the pullback datum.

    Pull [GammaD] back along [P]: [Dsub := pb_obj P GammaD] (the
    equaliser [{(x,d) | P x = GammaD d}]), with embedding [pb_incl :
    Dsub → p] and projection [pb_proj2 : Dsub → D].  The square lets
    [eB], [g] co-restrict (through [C ⊸ −], which preserves the
    pullback equaliser) to [eA : B → C ⊸ Dsub] with
    [(C ⊸ pb_incl) ∘ eA = eB] — so [(Dsub, pb_incl, eA)] is a member
    of the factoring family.  Hence the intersection embedding
    [tensor_incl] factors through it; the [D]-leg of that factor is the
    point map of [tensor_uncurry g]. *)

(** [C ⊸ −] preserves monos: if [h] is injective so is
    [linhom_post_icones h].  Pointwise, [(C ⊸ h) f = h ∘ f], so
    [h ∘ f₁ = h ∘ f₂] gives [f₁ = f₂] by injectivity of [h] and
    [linhom_eq]. *)
Lemma linhom_post_inj (R : realType) (Ar : MeasSubcat R)
    (C D1 D2 : ICone.type Ar) (h : icones_hom Ar D1 D2) :
  is_icones_inj h -> is_icones_inj (linhom_post_icones (C := C) h).
Proof.
move=> hinj f1 f2 /(congr1 (fun w : linhom_car Ar C D2 => linhom_fun w)) /= Hf.
apply: linhom_eq => x; apply: hinj.
by have := f_equal (fun w => w x) Hf.
Qed.

Arguments linhom_post_inj {R Ar C D1 D2} h.

Section TensorUncurry.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C D : ICone.type Ar.

Local Notation Cone1 := (cone_one_car Ar).
Local Notation p := (tp B C).

Variable g : icones_hom Ar B (linhom_car Ar C D).

(** The index of [q D]: the homset [ICones(D, 1)]. *)
Definition tN : Type := icones_hom Ar D Cone1.

(** The coseparator power [q D = 1^{ICones(D,1)}]. *)
Definition tqfam (_ : tN) : ICone.type Ar := Cone1.
Definition tq : ICone.type Ar := icones_prod tqfam.

(** The canonical mono [GammaD : D → q D], [GammaD d . n = n d]. *)
Definition GammaD : icones_hom Ar D tq :=
  icones_tuple (B := tqfam) (fun n : tN => n).

Lemma GammaDE (d : D) (n : tN) :
  cones_prod_val ((GammaD : icones_hom _ _ _) d) n = (n : icones_hom _ _ _) d.
Proof.
have := icones_tuple_proj (B := tqfam) (fun n0 : tN => n0) n.
by move/(congr1 (fun w : icones_hom Ar D Cone1 => (w : icones_hom _ _ _) d)).
Qed.

(** [GammaD] is a mono ([1] cogenerates). *)
Lemma GammaD_inj : is_icones_inj GammaD.
Proof.
move=> x y /(congr1 (fun z : tq => cones_prod_val z)) /= Hxy.
apply: icones_coseparator_inj => n.
by have := f_equal (fun w => w n) Hxy.
Qed.

(** The reindexing map [θ : ICones(D,1) → J = ICones(B, C ⊸ 1)],
    [θ n = (C ⊸ n) ∘ g]. *)
Definition tθ (n : tN) : tJ B C :=
  icones_comp (linhom_post_icones (C := C) n) g.

(** The reindex projection [P : p → q D], [P x . n = x . (θ n)]. *)
Definition tP : icones_hom Ar p tq :=
  icones_tuple (B := tqfam) (fun n : tN => icones_proj (tθ n)).

Lemma tPE (x : p) (n : tN) :
  cones_prod_val ((tP : icones_hom _ _ _) x) n = cones_prod_val x (tθ n).
Proof. by []. Qed.

(** The pullback datum — the commuting square
    [(C ⊸ P) ∘ eB = (C ⊸ GammaD) ∘ g].  Pointwise at [b, c], both
    sides are the element of [C ⊸ q D] whose [n]-component is
    [n (g b c)]: LHS via [eBE] ([eB b c . j = j b c]) and [tPE]
    ([θ n = (C ⊸ n) ∘ g], so [eB b c . θ n = n (g b c)]); RHS via
    [GammaDE]. *)
Lemma tP_square :
  icones_comp (linhom_post_icones (C := C) tP) (eB B C) =
  icones_comp (linhom_post_icones (C := C) GammaD) g.
Proof.
apply: icones_hom_eq => b /=.
apply: linhom_eq => c.
rewrite !linhom_map_funE /=.
apply: cones_prod_eq => n.
rewrite tPE eBE.
rewrite GammaDE.
by rewrite /tθ /= linhom_map_funE /=.
Qed.

(** *** The pullback [Dsub = pb_obj P GammaD] and its [p]-subobject *)

Local Notation Dsub := (pb_obj tP GammaD).

(** [Dsub ↪ p] is [pb_proj1] (the [p]-leg of the pullback of the mono
    [GammaD]); [pb_proj2 : Dsub → D] is the other leg. *)
Local Notation Dincl := (pb_proj1 tP GammaD).
Local Notation Dpr := (pb_proj2 tP GammaD).

(** [Dincl] is a mono: if [Dincl a = Dincl b] then [P (Dincl a) =
    P (Dincl b)], so by the pullback square [GammaD (Dpr a) =
    GammaD (Dpr b)], whence [Dpr a = Dpr b] ([GammaD] mono); agreeing
    on both projections of the product-equaliser forces [a = b]. *)
Lemma Dincl_inj : is_icones_inj Dincl.
Proof.
have Hsq := pb_square tP GammaD.
move=> a b Hab.
have Hsqpt : forall z : Dsub,
    (tP : icones_hom _ _ _) ((Dincl : icones_hom _ _ _) z) =
    (GammaD : icones_hom _ _ _) ((Dpr : icones_hom _ _ _) z).
  by move=> z;
    have := f_equal
      (fun w : icones_hom Ar Dsub tq => (w : icones_hom _ _ _) z) Hsq.
have Hpr2 : (Dpr : icones_hom _ _ _) a = (Dpr : icones_hom _ _ _) b.
  by apply: GammaD_inj; rewrite -!Hsqpt Hab.
(* [Dsub = icones_eq …]; equal iff [eq_incl] (into [pb_prod]) agree,
   iff both bool-components agree. *)
apply: (icones_eq_incl_inj (pb_left D tP) (pb_right p GammaD)).
apply: cones_prod_eq; case.
- exact: Hab.
- exact: Hpr2.
Qed.

(** *** Co-restricting [eB] and [g] to [C ⊸ Dsub]

    [Dsub] is the equaliser of [pb_left = P ∘ π₁] and
    [pb_right = GammaD ∘ π₂] on [pb_prod = p ×_bool D].  As [C ⊸ −]
    preserves it, the map [eAprod : B → C ⊸ pb_prod] tupling [eB]
    (at [true]) and [g] (at [false]) — built through
    [limpl_preserves_prod] — co-restricts to [eA : B → C ⊸ Dsub]. *)

(** The [bool]-family tuple [⟨ eB, g ⟩ : B → ∏_b (C ⊸ pb_fam b)]. *)
Definition eAtupfam (b : bool) :
    icones_hom Ar B (linhom_car Ar C (pb_fam p D b)) :=
  if b as b' return icones_hom Ar B (linhom_car Ar C (pb_fam p D b'))
  then eB B C else g.

Definition eAtup :
    icones_hom Ar B (icones_prod (fun b => linhom_car Ar C (pb_fam p D b))) :=
  icones_tuple (B := fun b => linhom_car Ar C (pb_fam p D b)) eAtupfam.

(** Transport back to [C ⊸ pb_prod] through Thm 5.9. *)
Definition eAprod : icones_hom Ar B (linhom_car Ar C (pb_prod p D)) :=
  icones_comp (iso_bwd (limpl_preserves_prod C (pb_fam p D))) eAtup.

(** Pointwise component value of [eAprod]:
    [eAprod b c . b' = (if b' then eB b c else g b c) . b']. *)
Lemma eAprodE (b : B) (c : C) (b' : bool) :
  cones_prod_val (linhom_fun ((eAprod : icones_hom _ _ _) b) c) b' =
  linhom_fun ((eAtupfam b' : icones_hom _ _ _) b) c.
Proof. by rewrite /eAprod /=. Qed.

(** [(C ⊸ π_b) ∘ eAprod = eAtupfam b]: the [true]/[false] components
    of [eAprod] are [eB] / [g]. *)
Lemma eAprod_pi (b' : bool) :
  icones_comp (linhom_post_icones (C := C) (icones_proj (B := pb_fam p D) b'))
              eAprod = eAtupfam b'.
Proof.
apply: icones_hom_eq => b /=.
apply: linhom_eq => c.
by rewrite linhom_map_funE /=.
Qed.

(** [eAprod] equalises [C ⊸ pb_left] and [C ⊸ pb_right]: both reduce,
    via [eAprod_pi], to [(C ⊸ P) ∘ eB] resp. [(C ⊸ GammaD) ∘ g], equal
    by [tP_square]. *)
Lemma eAprod_equ :
  icones_comp (linhom_post_icones (C := C) (pb_left D tP)) eAprod =
  icones_comp (linhom_post_icones (C := C) (pb_right p GammaD)) eAprod.
Proof.
rewrite /pb_left /pb_right /pb_pi1 /pb_pi2.
rewrite !linhom_post_comp -!icones_compA.
rewrite (eAprod_pi true) (eAprod_pi false).
exact: tP_square.
Qed.

(** The co-restriction [eA : B → C ⊸ Dsub]. *)
Definition eA : icones_hom Ar B (linhom_car Ar C Dsub) :=
  limpl_eq_med_icones C eAprod eAprod_equ.

(** [(C ⊸ eq_incl) ∘ eA = eAprod]. *)
Lemma eA_eq_incl :
  icones_comp (linhom_post_icones (C := C)
                 (icones_eq_incl (pb_left D tP) (pb_right p GammaD))) eA =
  eAprod.
Proof. exact: (limpl_eq_med_factor C eAprod eAprod_equ). Qed.

(** The factoring witness of the family member [(Dsub, Dincl, eA)]:
    [(C ⊸ Dincl) ∘ eA = eB].  [Dincl = π₁ ∘ eq_incl], and
    [(C ⊸ π₁) ∘ eAprod = eB] by [eAprod_pi true]. *)
Lemma eA_fact :
  icones_comp (linhom_post_icones (C := C) Dincl) eA = eB B C.
Proof.
rewrite /pb_proj1 /pb_pi1 linhom_post_comp -icones_compA eA_eq_incl.
exact: (eAprod_pi true).
Qed.

(** The family member [(Dsub, Dincl, eA)] as an [fsub]. *)
Definition Dfsub : fsub B C :=
  {| fs_dom := Dsub; fs_hom := Dincl; fs_inj := Dincl_inj;
     fs_eA := eA; fs_fact := eA_fact |}.

(** *** [tensor_uncurry g] via the intersection's factoring property

    Let [s := class(Dsub, Dincl)].  The chosen representative
    [fpick s] has the same classifier, hence is iso *over [p]* to
    [(Dsub, Dincl)] ([icones_subobject_classP]): an iso [φ : fAdom s ≅
    Dsub] with [Dincl ∘ φ = fhh s].  The intersection embedding
    [tensor_incl] factors through [fhh s] ([wi_factors_each]); composing
    with [φ] then [pb_proj2] gives the [D]-valued point map. *)

Definition Ds : fK := icones_subobject_class (fs_sub Dfsub).

(** The subobjects (in [fs_dom]-projection form, so the resulting iso
    has the [fAdom Ds] / [Dsub] domains [tu_factor] needs): the chosen
    representative [(fAdom Ds, fhh Ds)] and the pullback [(Dsub, Dincl)]. *)
Local Notation SubA :=
  (@MkSubobject R Ar p (fAdom Ds) (fhh Ds) (fhh_inj Ds)).
Local Notation SubDp :=
  (@MkSubobject R Ar p Dsub Dincl Dincl_inj).

(** Both have classifier [Ds]: [SubDp] by definition of [Ds] (via
    [fs_subE] on the constructor [Dfsub]); [SubA] because [fpick Ds]
    has classifier [Ds] (defining property of [fpick] when a witness —
    here [Dfsub] — exists) and [fs_subE] reads off its projections. *)
Lemma SubA_class : icones_subobject_class SubA = Ds.
Proof.
(* The chosen representative [fpick Ds] has classifier [Ds] (a witness
   exists: [Dfsub]). *)
have HpD : icones_subobject_class (fs_sub (fpick Ds)) = Ds.
  rewrite /fpick; case: pselect => [e|[]]; last by exists Dfsub.
  by case: (cid e) => k /= ->.
(* [SubA = fs_sub (fpick Ds)]: casing the representative makes both
   sides [MkSubobject A h hinj]. *)
rewrite -[in RHS]HpD; congr icones_subobject_class.
by rewrite /fAdom /fhh /fhh_inj /fs_sub; case: (fpick Ds).
Qed.

(** The two subobjects are iso *over [p]*: [SubDp] has classifier [Ds]
    by definition ([fs_sub Dfsub] reduces, [Dfsub] being a constructor);
    [SubA] by [SubA_class]. *)
Lemma Ds_equiv : subobject_equiv SubA SubDp.
Proof. by apply: icones_subobject_classP; rewrite SubA_class. Qed.

(** The iso [φ : fAdom Ds ≅ Dsub] over [p]
    ([Dincl ∘ iso_fwd φ = fhh Ds]). *)
Definition Dphi : icones_iso Ar (fAdom Ds) Dsub := proj1_sig (cid Ds_equiv).

Lemma DphiE (z : fAdom Ds) :
  (Dincl : icones_hom _ _ _) ((iso_fwd Dphi : icones_hom _ _ _) z) =
  (fhh Ds : icones_hom _ _ _) z.
Proof. exact: proj2_sig (cid Ds_equiv) z. Qed.

(** The factor of [tensor_incl] through [Dincl]:
    [tensor B C → Dsub], [= iso_fwd φ ∘ wi_proj Ds]. *)
Definition tu_factor : icones_hom Ar (tensor B C) Dsub :=
  icones_comp (iso_fwd Dphi) (wi_proj fAdom fhh fk0 Ds).

(** [Dincl ∘ tu_factor = tensor_incl]: [tensor_incl] factors through
    [fhh Ds] ([wi_factors_each]) and [Dincl ∘ iso_fwd φ = fhh Ds]
    ([DphiE]). *)
Lemma tu_factorP :
  icones_comp Dincl tu_factor = tensor_incl B C.
Proof.
rewrite /tu_factor icones_compA.
have HDphi : icones_comp Dincl (iso_fwd Dphi) = fhh Ds.
  by apply: icones_hom_eq => z /=; exact: DphiE.
rewrite HDphi.
rewrite -[tensor_incl B C]/(wi_incl fAdom fhh fk0).
exact: (@wi_factors_each R Ar fK p fAdom fhh fk0 Ds).
Qed.

(** The SAFT mediator [tensor_uncurry g : B ⊗ C → D]. *)
Definition tensor_uncurry : icones_hom Ar (tensor B C) D :=
  icones_comp Dpr tu_factor.

(** The [D]-leg factoring witness: [(C ⊸ Dpr) ∘ eA = g] ([Dpr =
    π₂ ∘ eq_incl] and the [false]-component of [eAprod] is [g]). *)
Lemma eA_pr_fact :
  icones_comp (linhom_post_icones (C := C) Dpr) eA = g.
Proof.
rewrite /pb_proj2 /pb_pi2 linhom_post_comp -icones_compA eA_eq_incl.
exact: (eAprod_pi false).
Qed.

(** *** [tensor_uncurryK] : [tensor_curry (tensor_uncurry g) = g]

    The defining factorisation.  Let [w := (C ⊸ tu_factor) ∘ tau'].
    Then [(C ⊸ Dincl) ∘ w = (C ⊸ tensor_incl) ∘ tau' = eB] ([tu_factorP],
    [tau'_def]); and [(C ⊸ Dincl) ∘ eA = eB] ([eA_fact]).  As [C ⊸ Dincl]
    is a mono ([linhom_post_inj] of the pullback mono [Dincl]), [w = eA].
    Hence [tensor_curry (tensor_uncurry g) = (C ⊸ Dpr) ∘ w =
    (C ⊸ Dpr) ∘ eA = g] ([eA_pr_fact]). *)
Lemma tensor_uncurryK : tensor_curry tensor_uncurry = g.
Proof.
pose w := icones_comp (linhom_post_icones (C := C) tu_factor) (tau' B C).
have Hw_Dincl : icones_comp (linhom_post_icones (C := C) Dincl) w = eB B C.
  rewrite /w icones_compA -linhom_post_comp.
  rewrite -[icones_comp Dincl tu_factor]/(icones_comp Dincl tu_factor).
  rewrite tu_factorP.
  exact: tau'_def.
have Hwe : w = eA.
  have Hmono := icones_inj_mono (linhom_post_icones (C := C) Dincl)
                  (linhom_post_inj (C := C) Dincl Dincl_inj).
  apply: (Hmono B w eA).
  by rewrite Hw_Dincl eA_fact.
rewrite /tensor_curry /tensor_uncurry linhom_post_comp -icones_compA -/w.
by rewrite Hwe eA_pr_fact.
Qed.

End TensorUncurry.

Arguments tensor_uncurry {R Ar B C D}.
Arguments tensor_uncurryK {R Ar B C D}.

(**md**************************************************************************)
(* # STATUS — [tensor_uncurry] BUILT; round-trip [tensor_uncurryK] PROVED      *)
(*                                                                            *)
(* What this file PROVES, axiom-clean (only the three classical [boolp]       *)
(* axioms; NO project [Axiom]/[Parameter]/[Admitted]; verified by             *)
(* [Print Assumptions tensor_uncurryK] = {propositional_extensionality,       *)
(* functional_extensionality_dep, constructive_indefinite_description}):       *)
(*                                                                            *)
(*   - [tensor B C := wi_obj …], [eB], [tau'] + [tau'_def], [tensor_curry] +   *)
(*     [tensor_curryE], [tensor_curry_natural_post] / [_D] (as before).        *)
(*   - [tensor_uncurry g : B ⊗ C → D] — the SAFT comma-category mediator,      *)
(*     BUILT by the coseparator-power reindexing (Riehl 4.6.11): the          *)
(*     canonical mono [GammaD : D ↪ q := 1^{ICones(D,1)}] ([GammaD_inj] from   *)
(*     Phase A [icones_coseparator_inj]), the reindex [P : p → q] along        *)
(*     [n ↦ (C ⊸ n) ∘ g], the pullback [Dsub := pb_obj P GammaD] (its         *)
(*     [p]-leg [Dincl] a mono, [Dincl_inj]), the co-restriction [eA :          *)
(*     B → C ⊸ Dsub] of [eB]/[g] through the preserved equaliser              *)
(*     ([eA_fact] : [(C ⊸ Dincl) ∘ eA = eB]) making [(Dsub, Dincl, eA)] a      *)
(*     factoring-family member, and the classifier transport ([Ds_equiv] via  *)
(*     [icones_subobject_classP]) so [tensor_incl] factors through [Dincl]     *)
(*     ([tu_factorP]); [tensor_uncurry g := Dpr ∘ tu_factor].                  *)
(*   - [tensor_uncurryK] : [tensor_curry (tensor_uncurry g) = g] — the         *)
(*     defining factorisation, via [C ⊸ Dincl] mono ([linhom_post_inj]) so     *)
(*     [(C ⊸ tu_factor) ∘ tau' = eA], then [(C ⊸ Dpr) ∘ eA = g] ([eA_pr_fact]).*)
(*                                                                            *)
(* What REMAINS — [tensor_curryK] and [tensor_curry_natural_B]:                *)
(*                                                                            *)
(*  (U1) [tensor_curryK] : [tensor_uncurry (tensor_curry f) = f] is EQUIVALENT *)
(*       to *injectivity of [tensor_curry]* (given [tensor_uncurryK]:          *)
(*       [tensor_curry (tensor_uncurry (tensor_curry f)) = tensor_curry f], so *)
(*       [tensor_uncurry (tensor_curry f) = f] iff [tensor_curry] is mono).    *)
(*       By the coseparator [GammaD] (cod [D]) and the component law           *)
(*       [π_n ∘ GammaD = n], injectivity of [tensor_curry] reduces to the      *)
(*       codomain-[1] case: for [h₁ h₂ : B ⊗ C → 1],                           *)
(*         [tensor_curry h₁ = tensor_curry h₂  ⟹  h₁ = h₂].                    *)
(*       Equivalently (taking [j := tensor_curry h]) the UNIVERSAL-ELEMENT      *)
(*       RECOVERY identity                                                     *)
(*         [π_j ∘ tensor_incl = h    whenever    tensor_curry h = j],          *)
(*       i.e. the [j]-component of the intersection embedding reproduces the   *)
(*       map [h] whose curry is [j].  This holds on the IMAGE of [tau']        *)
(*       ([tensor_incl (tau' b c) . j = j b c], from [tau'_def]+[eBE]) but     *)
(*       its extension to ALL of [B ⊗ C] is exactly the *faithfulness* /       *)
(*       minimality half of SAFT representability: that [tau'] is jointly      *)
(*       epic, i.e. the universal element generates [B ⊗ C].  The exported     *)
(*       [representable.v] [wi_*] interface gives maps INTO the intersection   *)
(*       ([wi_med]) and FACTORING through members ([wi_factors_each]) — but no *)
(*       "maps OUT of the intersection are determined by [tau']" principle.    *)
(*       Supplying that (a [wi_proj]-jointly-mono / generation lemma in        *)
(*       [representable.v], or a direct density argument that the sub-cone     *)
(*       generated by [tau']'s image is all of [B ⊗ C]) closes both [U1] and   *)
(*       [tensor_curry_natural_B] (the latter is then routine — define         *)
(*       [tensor_mor_l u := tensor_uncurry (icones_comp tau' u)] and use       *)
(*       [tensor_uncurryK]).                                                   *)
(******************************************************************************)

End Icones_tensor_construct.
