(**md**************************************************************************)
(* # SAFT skeleton — the shared left-adjoint construction underlying both     *)
(*   [tensor_construct.v] (the tensor [B ⊗ C] as SAFT left adjoint of         *)
(*   [(C ⊸ −)]) and [bang_construct.v] (the exponential [E = Bang] as SAFT    *)
(*   left adjoint of [Der]).                                                  *)
(*                                                                            *)
(* The two constructions are the SAME Riehl-4.6.11 argument run against two   *)
(* different limit-preserving right functors [R : ICones → D]:                *)
(*                                                                            *)
(*   - tensor : [D := ICones],  [R X := (C ⊸ X)]  ([linhom_post_icones]);     *)
(*   - bang   : [D := SCones],  [R X := X]        ([ders], the [Der] functor).*)
(*                                                                            *)
(* This file abstracts what both instantiations use into a single signature   *)
(* [saft_sig]: the generalised-element functor [sg_ehom X := D(B, R X)]       *)
(* (with the fixed source [B] folded in), its functorial action [sg_emap]     *)
(* (post-composition with [R h]) with identity/composition/mono laws, the     *)
(* product-preservation data [sg_etuple]/[sg_etuple_proj]/[sg_eprod_ext]      *)
(* (tupling into [R (∏ X_k)] plus joint monicity of the [R π_k]), and the     *)
(* equaliser-preservation data [sg_eq_med]/[sg_eq_med_factor] (co-restriction *)
(* through [R] of an equalising element).                                     *)
(*                                                                            *)
(* Against this signature the file builds, once, the whole SAFT engine:       *)
(*                                                                            *)
(*   - [saft_J := sg_ehom 1], the coseparator power [saft_p := 1^J] and the   *)
(*     universal element [saft_eB := ⟨ j ⟩_{j ∈ J}];                          *)
(*   - the factoring family [fsub] of subobjects of [saft_p] through which    *)
(*     [saft_eB] factors, its small classifier reindexing [fK]/[fpick]        *)
(*     (well-poweredness, [SubobjClassifier]), and the wide intersection      *)
(*     [saft_obj := wi_obj fhh fk0] with embedding [saft_incl];               *)
(*   - intersection minimality [ff_factor]/[ff_factorP] (classifier           *)
(*     transport, [icones_subobject_classP]);                                 *)
(*   - the universal element [saft_tau] (co-restriction of [saft_eB]) with    *)
(*     [saft_tau_def], and [saft_incl_inj] (all-components mono argument);    *)
(*   - the mediator [saft_uncurry g] (coseparator-power reindexing +          *)
(*     pullback [pb_obj] + classifier transport) with the round-trip          *)
(*     [saft_uncurryK], and SAFT-uniqueness [saft_curry_inj]/[saft_curryK]    *)
(*     (equaliser of candidates + intersection minimality).                   *)
(*                                                                            *)
(* [tensor_construct.v] instantiates the signature ([tensor_sig]) and         *)
(* re-exports the results under its historical names (keeping its             *)
(* instantiation-specific pointwise lemmas locally).  The [Der]/[bang]        *)
(* instantiation TYPECHECKS against this signature as well (universe-clean),  *)
(* but is NOT wired in: routing [Bang]/[nl]/[lin] through the signature       *)
(* record multiplies the conversion cost of [bang.v]'s nested-[Bang]          *)
(* comonad proofs (measured: [comonad_coassoc]'s                              *)
(* [rewrite (dig_prom (prom_ball _))] goes from 632 s concrete to >2400 s),   *)
(* so [bang_construct.v] keeps its concrete twin of this argument.  This      *)
(* file is AXIOM-FREE relative to the classical [boolp] base — NO [Axiom]/    *)
(* [Parameter]/[Admitted].                                                    *)
(*                                                                            *)
(* APIs used: [representable.v] — [wi_obj]/[wi_incl]/[wi_proj]/               *)
(* [wi_factors_each]/[icones_subobject_classP]/[icones_coseparator_inj]/      *)
(* [pb_obj]/[pb_*]; [icone_cat.v] — products/equalisers.                      *)
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
Require Import Icones.homs.icones_iso.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Module Icones_saft_construct.

(** ** The signature: a concrete limit-preserving right functor

    [sg_ehom X] packages the hom-set [D(B, R X)] of the target category
    [D] out of a fixed source [B] into the image of a limit-preserving
    functor [R : ICones → D]; [sg_emap h := (R h ∘ −)] is the covariant
    hom-action.  The laws are exactly what the SAFT argument consumes:

    - [sg_emap_id]/[sg_emap_comp] : functoriality of [R] + associativity
      of composition in [D];
    - [sg_emap_mono] : [R] preserves monos, as left-cancellability on the
      generalised elements ([linhom_post_inj]+[icones_inj_mono] resp.
      [ders_mono]);
    - [sg_etuple]/[sg_etuple_proj]/[sg_eprod_ext] : [R] preserves small
      products — tupling into [R (∏ X_k)] with the projection law and
      joint monicity of the [R π_k] ([limpl_preserves_prod] resp. the
      on-the-nose product preservation of [Der]);
    - [sg_eq_med]/[sg_eq_med_factor] : [R] preserves equalisers — an
      equalising element co-restricts through [R (eq inclusion)]
      ([limpl_eq_med_icones] resp. [der_eq_med]). *)

Record saft_sig (R : realType) (Ar : MeasSubcat R) : Type := MkSaftSig {
  sg_ehom : ICone.type Ar -> Type;
  sg_emap : forall X Y : ICone.type Ar,
      icones_hom Ar X Y -> sg_ehom X -> sg_ehom Y;
  sg_emap_id : forall (X : ICone.type Ar) (g : sg_ehom X),
      sg_emap (icones_id Ar X) g = g;
  sg_emap_comp : forall (X Y Z : ICone.type Ar)
      (h1 : icones_hom Ar X Y) (h2 : icones_hom Ar Y Z) (g : sg_ehom X),
      sg_emap (icones_comp h2 h1) g = sg_emap h2 (sg_emap h1 g);
  sg_emap_mono : forall (X Y : ICone.type Ar) (h : icones_hom Ar X Y),
      is_icones_inj h ->
      forall u v : sg_ehom X, sg_emap h u = sg_emap h v -> u = v;
  sg_etuple : forall (K : Type) (X : K -> ICone.type Ar),
      (forall k, sg_ehom (X k)) -> sg_ehom (icones_prod X);
  sg_etuple_proj : forall (K : Type) (X : K -> ICone.type Ar)
      (g : forall k, sg_ehom (X k)) (k : K),
      sg_emap (icones_proj k) (sg_etuple g) = g k;
  sg_eprod_ext : forall (K : Type) (X : K -> ICone.type Ar)
      (a b : sg_ehom (icones_prod X)),
      (forall k, sg_emap (icones_proj k) a = sg_emap (icones_proj k) b) ->
      a = b;
  sg_eq_med : forall (X Y : ICone.type Ar) (u v : icones_hom Ar X Y)
      (g : sg_ehom X),
      sg_emap u g = sg_emap v g -> sg_ehom (icones_eq u v);
  sg_eq_med_factor : forall (X Y : ICone.type Ar) (u v : icones_hom Ar X Y)
      (g : sg_ehom X) (E : sg_emap u g = sg_emap v g),
      sg_emap (icones_eq_incl u v) (sg_eq_med E) = g;
}.

Arguments sg_ehom {R Ar} s X.
Arguments sg_emap {R Ar} s {X Y} h g.
Arguments sg_emap_id {R Ar} s {X} g.
Arguments sg_emap_comp {R Ar} s {X Y Z} h1 h2 g.
Arguments sg_emap_mono {R Ar} s {X Y h} hinj {u v}.
Arguments sg_etuple {R Ar} s {K X} g.
Arguments sg_etuple_proj {R Ar} s {K X} g k.
Arguments sg_eprod_ext {R Ar} s {K X a b}.
Arguments sg_eq_med {R Ar} s {X Y u v g} E.
Arguments sg_eq_med_factor {R Ar} s {X Y u v g} E.

Section Skeleton.
Variables (R : realType) (Ar : MeasSubcat R).
Variable S : saft_sig Ar.

Local Notation Cone1 := (cone_one_car Ar).
Local Notation EHom := (sg_ehom S).
Local Notation emap := (sg_emap S).
Local Notation etuple := (sg_etuple S).

(** ** The coseparator power and the universal element [saft_eB]

    The index type [saft_J := sg_ehom 1] is the generalised hom-set of
    the coseparator [1]; the power is [saft_p := 1^J].  The universal
    element [saft_eB : sg_ehom saft_p] is the tuple of all elements of
    [saft_J]. *)

Definition saft_J : Type := EHom Cone1.
Definition saft_pfam (_ : saft_J) : ICone.type Ar := Cone1.
Definition saft_p : ICone.type Ar := icones_prod saft_pfam.

Definition saft_eB : EHom saft_p :=
  etuple (fun j : saft_J => j).

(** ** The factoring family and the SAFT object

    A member is a subobject-like datum: a domain, an [ICones]-mono
    embedding into [saft_p], and a factoring witness of [saft_eB]
    through the embedding's [sg_emap]-image. *)

Record fsub : Type := MkFsub {
  fs_dom : ICone.type Ar;
  fs_hom : icones_hom Ar fs_dom saft_p;
  fs_inj : is_icones_inj fs_hom;
  fs_eA : EHom fs_dom;
  fs_fact : emap fs_hom fs_eA = saft_eB;
}.

(** The underlying subobject of a family member.  Destructured via
    [match] so the [fs_inj] projector's auto-added [injective] arguments
    do not leak into the application. *)
Definition fs_sub (k : fsub) : icones_subobject saft_p :=
  match k with
  | MkFsub A h hinj eA Hf => MkSubobject A h hinj
  end.

(** A family member's embedding is a mono (same destructuring). *)
Definition fs_hom_inj (k : fsub) : is_icones_inj (fs_hom k) :=
  match k as k' return is_icones_inj (fs_hom k') with
  | MkFsub A h hinj eA Hf => hinj
  end.

Arguments fs_hom_inj : clear implicits.

(** The basepoint subobject [(saft_p, id, saft_eB)]. *)
Lemma fk0_fact : emap (icones_id Ar saft_p) saft_eB = saft_eB.
Proof. exact: (sg_emap_id S). Qed.

Lemma fk0_inj : is_icones_inj (icones_id Ar saft_p).
Proof. by move=> x y. Qed.

Definition fbase : fsub :=
  {| fs_dom := saft_p; fs_hom := icones_id Ar saft_p; fs_inj := fk0_inj;
     fs_eA := saft_eB; fs_fact := fk0_fact |}.

(** *** The small index — well-poweredness

    The family is indexed by the *small* subobject classifier
    [SubobjClassifier saft_p] ([representable.v], well-poweredness
    Thm 4.18), NOT by the proper-class record [fsub].  For each
    classifier value [s] we *choose* (classically, [pselect]/[cid]) a
    factoring subobject whose classifier is [s], defaulting to the
    basepoint [fbase] when none exists.  By well-poweredness, two
    factoring subobjects with the same classifier are iso over [saft_p]
    ([icones_subobject_classP]); so indexing by the classifier loses no
    subobject up to iso — exactly the role [icones_well_powered] plays
    in the SAFT solution-set construction (Riehl 4.6.10). *)
Definition fK : Type := SubobjClassifier saft_p.

Definition fpick (s : fK) : fsub :=
  match pselect (exists k : fsub, icones_subobject_class (fs_sub k) = s) with
  | left e => proj1_sig (cid e)
  | right _ => fbase
  end.

Definition fAdom (s : fK) : ICone.type Ar := fs_dom (fpick s).
Definition fhh (s : fK) : icones_hom Ar (fAdom s) saft_p := fs_hom (fpick s).

Definition fhh_inj (s : fK) : is_icones_inj (fhh s) :=
  match fpick s as k return is_icones_inj (fs_hom k) with
  | MkFsub A h hinj eA Hf => hinj
  end.

Arguments fhh_inj : clear implicits.

Definition fk0 : fK := icones_subobject_class (fs_sub fbase).

(** The SAFT object as the wide intersection of the family, with its
    embedding into the coseparator power. *)
Definition saft_obj : ICone.type Ar := wi_obj fhh fk0.
Definition saft_incl : icones_hom Ar saft_obj saft_p := wi_incl fAdom fhh fk0.

Lemma fpick_fact (s : fK) : emap (fhh s) (fs_eA (fpick s)) = saft_eB.
Proof. exact: fs_fact. Qed.

(** ** Intersection minimality: [saft_incl] factors through every member

    The SAFT "initial object of the comma category" content (Riehl
    4.6.11): for any factoring-family member [k : fsub], the
    intersection embedding factors through its embedding via the
    classifier transport [icones_subobject_classP]. *)

Section FsubFactors.
Variable k : fsub.

Definition ff_class : fK := icones_subobject_class (fs_sub k).

Local Notation SubA :=
  (@MkSubobject R Ar saft_p (fAdom ff_class) (fhh ff_class) (fhh_inj ff_class)).
Local Notation SubK :=
  (@MkSubobject R Ar saft_p (fs_dom k) (fs_hom k) (fs_hom_inj k)).

(** [SubA] has classifier [ff_class]: a witness ([k]) exists, so [fpick
    ff_class] picks a subobject with classifier [ff_class]. *)
Lemma ff_SubA_class : icones_subobject_class SubA = ff_class.
Proof.
have HpD : icones_subobject_class (fs_sub (fpick ff_class)) = ff_class.
  rewrite /fpick; case: pselect => [e|[]]; last by exists k.
  by case: (cid e) => k1 /= ->.
rewrite -[in RHS]HpD; congr icones_subobject_class.
by rewrite /fAdom /fhh /fhh_inj /fs_sub; case: (fpick ff_class).
Qed.

Lemma ff_equiv : subobject_equiv SubA SubK.
Proof.
apply: icones_subobject_classP.
rewrite ff_SubA_class /ff_class.
by congr icones_subobject_class; case: k.
Qed.

(** The iso [φ : fAdom ff_class ≅ fs_dom k] over [saft_p]. *)
Definition ff_phi : icones_iso Ar (fAdom ff_class) (fs_dom k) :=
  proj1_sig (cid ff_equiv).

Lemma ff_phiE (z : fAdom ff_class) :
  (fs_hom k : icones_hom _ _ _) ((iso_fwd ff_phi : icones_hom _ _ _) z) =
  (fhh ff_class : icones_hom _ _ _) z.
Proof. exact: proj2_sig (cid ff_equiv) z. Qed.

Definition ff_factor : icones_hom Ar saft_obj (fs_dom k) :=
  icones_comp (iso_fwd ff_phi) (wi_proj fAdom fhh fk0 ff_class).

Lemma ff_factorP :
  icones_comp (fs_hom k) ff_factor = saft_incl.
Proof.
rewrite /ff_factor icones_compA.
have Hphi : icones_comp (fs_hom k) (iso_fwd ff_phi) = fhh ff_class.
  by apply: icones_hom_eq => z /=; exact: ff_phiE.
rewrite Hphi.
rewrite -[saft_incl]/(wi_incl fAdom fhh fk0).
exact: (@wi_factors_each R Ar fK saft_p fAdom fhh fk0 ff_class).
Qed.

End FsubFactors.

(** ** The universal element [saft_tau] by co-restriction

    [saft_obj = wi_obj] is, by construction, the equaliser of [wi_u]
    and [wi_v] on [wi_prod fAdom].  The tuple [saft_eprod] of factoring
    witnesses equalises their [sg_emap]-images (categorically, via
    [sg_etuple_proj] + [fpick_fact] + joint monicity), so [sg_eq_med]
    co-restricts it to [saft_tau]. *)

Local Notation WU := (wi_u fhh).
Local Notation WV := (wi_v fhh fk0).

Definition saft_eprod : EHom (wi_prod fAdom) :=
  etuple (fun s : fK => fs_eA (fpick s)).

Lemma saft_eprod_equ : emap WU saft_eprod = emap WV saft_eprod.
Proof.
apply: (sg_eprod_ext S) => k.
rewrite -!(sg_emap_comp S) /wi_u /wi_v !icones_tuple_proj.
rewrite !(sg_emap_comp S) /wi_pi /saft_eprod !(sg_etuple_proj S).
by rewrite !fpick_fact.
Qed.

Definition saft_tau : EHom saft_obj := sg_eq_med S saft_eprod_equ.

Lemma saft_tau_eq_incl :
  emap (icones_eq_incl WU WV) saft_tau = saft_eprod.
Proof. exact: (sg_eq_med_factor S). Qed.

(** The DEFINING factorisation of the universal element:
    [sg_emap saft_incl saft_tau = saft_eB]. *)
Lemma saft_tau_def : emap saft_incl saft_tau = saft_eB.
Proof.
rewrite /saft_incl /wi_incl (sg_emap_comp S).
rewrite /saft_tau saft_tau_eq_incl.
rewrite (sg_emap_comp S) /wi_pi /saft_eprod (sg_etuple_proj S).
exact: fpick_fact.
Qed.

(** ** The hom-map [saft_curry] and its naturality in the codomain *)

Definition saft_curry (D : ICone.type Ar) (f : icones_hom Ar saft_obj D) :
    EHom D :=
  emap f saft_tau.

Lemma saft_curry_post (D D' : ICone.type Ar)
    (h : icones_hom Ar D D') (f : icones_hom Ar saft_obj D) :
  saft_curry (icones_comp h f) = emap h (saft_curry f).
Proof. exact: (sg_emap_comp S). Qed.

(** ** The intersection embedding [saft_incl] is a monomorphism

    The all-components argument: every family member [fhh k] is a mono
    ([fhh_inj]); two equaliser points with the same [saft_incl]-image
    agree componentwise.  (The generic [wi_incl_inj] would need the
    single projection [wi_proj k0] injective — false here.) *)

Lemma WUE' (x : wi_prod fAdom) (k : fK) :
  cones_prod_val ((WU : icones_hom _ _ _) x) k =
  (fhh k : icones_hom _ _ _) (cones_prod_val x k).
Proof.
have := icones_tuple_proj (Q := wi_prod fAdom)
          (fun k1 => icones_comp (fhh k1) (wi_pi fAdom k1)) k.
by move/(congr1 (fun w : icones_hom Ar (wi_prod fAdom) saft_p =>
                   (w : icones_hom _ _ _) x)) => /= ->.
Qed.

Lemma WVE' (x : wi_prod fAdom) (k : fK) :
  cones_prod_val ((WV : icones_hom _ _ _) x) k =
  (fhh fk0 : icones_hom _ _ _) (cones_prod_val x fk0).
Proof.
have := icones_tuple_proj (Q := wi_prod fAdom)
          (fun _ : fK => icones_comp (fhh fk0) (wi_pi fAdom fk0)) k.
by move/(congr1 (fun w : icones_hom Ar (wi_prod fAdom) saft_p =>
                   (w : icones_hom _ _ _) x)) => /= ->.
Qed.

Lemma saft_incl_inj : is_icones_inj saft_incl.
Proof.
rewrite /is_icones_inj => x y Hxy.
have Hk0 : (fhh fk0 : icones_hom _ _ _)
             (cones_prod_val (cones_eq_val x) fk0) =
           (fhh fk0 : icones_hom _ _ _)
             (cones_prod_val (cones_eq_val y) fk0).
  exact: Hxy.
have Hcx := cones_eq_eq x.
have Hcy := cones_eq_eq y.
apply: (icones_eq_incl_inj WU WV).
apply: cones_prod_eq => k.
apply: (fhh_inj k).
have Ex : (fhh k : icones_hom _ _ _) (cones_prod_val (cones_eq_val x) k) =
          (fhh fk0 : icones_hom _ _ _) (cones_prod_val (cones_eq_val x) fk0).
  have := f_equal (fun z => cones_prod_val z k) Hcx.
  by rewrite WUE' WVE'.
have Ey : (fhh k : icones_hom _ _ _) (cones_prod_val (cones_eq_val y) k) =
          (fhh fk0 : icones_hom _ _ _) (cones_prod_val (cones_eq_val y) fk0).
  have := f_equal (fun z => cones_prod_val z k) Hcy.
  by rewrite WUE' WVE'.
by rewrite Ex Hk0 -Ey.
Qed.

(** ** The SAFT comma-category mediator [saft_uncurry] (Riehl 4.6.11)

    Given a generalised element [g : sg_ehom D], build the unique
    [saft_uncurry g : saft_obj → D] with
    [sg_emap (saft_uncurry g) saft_tau = g] by the coseparator-power
    reindexing: the canonical mono [saft_Gamma : D ↪ 1^{ICones(D,1)}],
    the reindex projection [saft_P], the pullback
    [pb_obj saft_P saft_Gamma], the co-restriction [saft_gA] of
    [saft_eB]/[g], and the classifier transport [ff_factor]. *)

Section Mediator.
Variables (D : ICone.type Ar) (g : EHom D).

(** The index of [q D]: the homset [ICones(D, 1)]. *)
Definition saft_N : Type := icones_hom Ar D Cone1.

Definition saft_qfam (_ : saft_N) : ICone.type Ar := Cone1.
Definition saft_q : ICone.type Ar := icones_prod saft_qfam.

(** The canonical mono [saft_Gamma : D → q D], [saft_Gamma d . n = n d]. *)
Definition saft_Gamma : icones_hom Ar D saft_q :=
  icones_tuple (B := saft_qfam) (fun n : saft_N => n).

(** [saft_Gamma] is a mono ([1] cogenerates). *)
Lemma saft_Gamma_inj : is_icones_inj saft_Gamma.
Proof.
move=> x y /(congr1 (fun z : saft_q => cones_prod_val z)) /= Hxy.
apply: icones_coseparator_inj => n.
by have := f_equal (fun w => w n) Hxy.
Qed.

(** The reindexing map [θ : ICones(D,1) → saft_J], [θ n := sg_emap n g]. *)
Definition saft_theta (n : saft_N) : saft_J := emap n g.

(** The reindex projection [P : saft_p → q D], [P x . n = x . (θ n)]. *)
Definition saft_P : icones_hom Ar saft_p saft_q :=
  icones_tuple (B := saft_qfam) (fun n : saft_N => icones_proj (saft_theta n)).

(** The pullback datum — the commuting square
    [sg_emap saft_P saft_eB = sg_emap saft_Gamma g], proved
    categorically via [sg_eprod_ext] + the tuple-projection laws. *)
Lemma saft_P_square : emap saft_P saft_eB = emap saft_Gamma g.
Proof.
apply: (sg_eprod_ext S) => n.
rewrite -!(sg_emap_comp S) /saft_P /saft_Gamma !icones_tuple_proj.
by rewrite /saft_eB (sg_etuple_proj S).
Qed.

(** *** The pullback and its [saft_p]-subobject *)

Local Notation Gsub := (pb_obj saft_P saft_Gamma).
Local Notation Gincl := (pb_proj1 saft_P saft_Gamma).
Local Notation Gpr := (pb_proj2 saft_P saft_Gamma).

(** [Gincl] is a mono (via the pullback square and [saft_Gamma_inj]). *)
Lemma saft_Gincl_inj : is_icones_inj Gincl.
Proof.
have Hsq := pb_square saft_P saft_Gamma.
move=> a b Hab.
have Hsqpt : forall z : Gsub,
    (saft_P : icones_hom _ _ _) ((Gincl : icones_hom _ _ _) z) =
    (saft_Gamma : icones_hom _ _ _) ((Gpr : icones_hom _ _ _) z).
  by move=> z;
    have := f_equal
      (fun w : icones_hom Ar Gsub saft_q => (w : icones_hom _ _ _) z) Hsq.
have Hpr2 : (Gpr : icones_hom _ _ _) a = (Gpr : icones_hom _ _ _) b.
  by apply: saft_Gamma_inj; rewrite -!Hsqpt Hab.
apply: (icones_eq_incl_inj (pb_left D saft_P) (pb_right saft_p saft_Gamma)).
apply: cones_prod_eq; case.
- exact: Hab.
- exact: Hpr2.
Qed.

(** *** Co-restricting [saft_eB] and [g] to the pullback *)

Definition saft_tupfam (b : bool) : EHom (pb_fam saft_p D b) :=
  if b as b' return EHom (pb_fam saft_p D b') then saft_eB else g.

Definition saft_gprod : EHom (pb_prod saft_p D) :=
  etuple saft_tupfam.

Lemma saft_gprod_pi (b : bool) :
  emap (icones_proj (B := pb_fam saft_p D) b) saft_gprod = saft_tupfam b.
Proof. exact: (sg_etuple_proj S). Qed.

Lemma saft_gprod_equ :
  emap (pb_left D saft_P) saft_gprod =
  emap (pb_right saft_p saft_Gamma) saft_gprod.
Proof.
rewrite /pb_left /pb_right /pb_pi1 /pb_pi2 !(sg_emap_comp S).
rewrite (saft_gprod_pi true) (saft_gprod_pi false).
exact: saft_P_square.
Qed.

Definition saft_gA : EHom Gsub := sg_eq_med S saft_gprod_equ.

Lemma saft_gA_eq_incl :
  emap (icones_eq_incl (pb_left D saft_P) (pb_right saft_p saft_Gamma))
       saft_gA = saft_gprod.
Proof. exact: (sg_eq_med_factor S). Qed.

Lemma saft_gA_fact : emap Gincl saft_gA = saft_eB.
Proof.
rewrite /pb_proj1 (sg_emap_comp S) /saft_gA saft_gA_eq_incl /pb_pi1.
exact: (saft_gprod_pi true).
Qed.

(** The family member [(Gsub, Gincl, saft_gA)]. *)
Definition saft_gfsub : fsub :=
  {| fs_dom := Gsub; fs_hom := Gincl; fs_inj := saft_Gincl_inj;
     fs_eA := saft_gA; fs_fact := saft_gA_fact |}.

(** The SAFT mediator, through the intersection's factoring property. *)
Definition saft_uncurry : icones_hom Ar saft_obj D :=
  icones_comp Gpr (ff_factor saft_gfsub).

Lemma saft_uncurry_factorP :
  icones_comp Gincl (ff_factor saft_gfsub) = saft_incl.
Proof. exact: (ff_factorP saft_gfsub). Qed.

Lemma saft_gA_pr_fact : emap Gpr saft_gA = g.
Proof.
rewrite /pb_proj2 (sg_emap_comp S) /saft_gA saft_gA_eq_incl /pb_pi2.
exact: (saft_gprod_pi false).
Qed.

(** The round trip: [saft_curry (saft_uncurry g) = g] — the defining
    factorisation, via [sg_emap Gincl] mono ([sg_emap_mono]). *)
Lemma saft_uncurryK : saft_curry saft_uncurry = g.
Proof.
pose w := emap (ff_factor saft_gfsub) saft_tau.
have Hw : emap Gincl w = saft_eB.
  rewrite /w -(sg_emap_comp S) saft_uncurry_factorP.
  exact: saft_tau_def.
have Hwe : w = saft_gA.
  apply: (sg_emap_mono S saft_Gincl_inj).
  by rewrite Hw saft_gA_fact.
rewrite /saft_curry /saft_uncurry (sg_emap_comp S) -/w Hwe.
exact: saft_gA_pr_fact.
Qed.

End Mediator.

(** ** SAFT-uniqueness: [saft_curry] is injective

    The equaliser-of-candidates + intersection-minimality argument. *)

Section SaftCurryInj.
Variables (D : ICone.type Ar) (f1 f2 : icones_hom Ar saft_obj D).
Hypothesis Hcurry : saft_curry f1 = saft_curry f2.

Local Notation E := (icones_eq f1 f2).
Local Notation e := (icones_eq_incl f1 f2).

(** [saft_tau] equalises the [sg_emap]-images — exactly [Hcurry]. *)
Definition sci_equ : emap f1 saft_tau = emap f2 saft_tau := Hcurry.

(** The co-restriction [sci_tauE : sg_ehom E]. *)
Definition sci_tauE : EHom E := sg_eq_med S sci_equ.

Lemma sci_tauE_factor : emap e sci_tauE = saft_tau.
Proof. exact: (sg_eq_med_factor S). Qed.

(** The composite embedding [m_E := saft_incl ∘ e : E ↪ saft_p]. *)
Definition sci_mE : icones_hom Ar E saft_p := icones_comp saft_incl e.

Lemma sci_mE_inj : is_icones_inj sci_mE.
Proof.
move=> a b /= /saft_incl_inj; exact: (icones_eq_incl_inj f1 f2).
Qed.

Lemma sci_fact : emap sci_mE sci_tauE = saft_eB.
Proof.
rewrite /sci_mE (sg_emap_comp S) sci_tauE_factor.
exact: saft_tau_def.
Qed.

Definition sci_fsub : fsub :=
  {| fs_dom := E; fs_hom := sci_mE; fs_inj := sci_mE_inj;
     fs_eA := sci_tauE; fs_fact := sci_fact |}.

Definition sci_r : icones_hom Ar saft_obj E := ff_factor sci_fsub.

Lemma sci_rP : icones_comp sci_mE sci_r = saft_incl.
Proof. exact: (ff_factorP sci_fsub). Qed.

(** [e] is a split epi: [e ∘ r = id]. *)
Lemma sci_split : icones_comp e sci_r = icones_id Ar saft_obj.
Proof.
have Hmono := icones_inj_mono saft_incl saft_incl_inj.
apply: (Hmono _ (icones_comp e sci_r) (icones_id Ar saft_obj)).
rewrite icones_compA -/sci_mE sci_rP.
by rewrite icones_compIr.
Qed.

Lemma sci_eq : f1 = f2.
Proof.
transitivity (icones_comp f1 (icones_comp e sci_r)).
  by rewrite sci_split icones_compIr.
transitivity (icones_comp f2 (icones_comp e sci_r)); last first.
  by rewrite sci_split icones_compIr.
by rewrite !icones_compA (icones_eq_incl_equ f1 f2).
Qed.

End SaftCurryInj.

(** Injectivity of the forward hom-map, and the other round trip. *)
Lemma saft_curry_inj (D : ICone.type Ar)
    (f1 f2 : icones_hom Ar saft_obj D) :
  saft_curry f1 = saft_curry f2 -> f1 = f2.
Proof. exact: sci_eq. Qed.

Lemma saft_curryK (D : ICone.type Ar) (f : icones_hom Ar saft_obj D) :
  saft_uncurry (saft_curry f) = f.
Proof.
apply: saft_curry_inj.
exact: saft_uncurryK.
Qed.

End Skeleton.

End Icones_saft_construct.
