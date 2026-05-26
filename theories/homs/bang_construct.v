(**md**************************************************************************)
(* # Exponential discharge — the left adjoint [E] of [Der] as the SAFT        *)
(*   construction, with the universal-arrow data PROVED (Paper §9 +           *)
(*   [th:Icones-adjoint-functor], the [E ⊣ Der] adjunction).                  *)
(*                                                                            *)
(* This file DISCHARGES, as genuine theorems about a concrete construction,   *)
(* the five [Parameter]/[Axiom]s of [theories/homs/exp_adjunction.v]:         *)
(*                                                                            *)
(*   Bang, nl, lin, lin_beta, lin_unique                                      *)
(*                                                                            *)
(* It is AXIOM-FREE relative to the classical [boolp] base — NO               *)
(* [Axiom]/[Parameter]/[Admitted], and it does NOT import [exp_interface]:    *)
(* the proved versions are built from scratch, in their own module            *)
(* [Icones.homs.bang_construct], so they do not clash with the interface's    *)
(* same-named [Parameter]s.                                                   *)
(*                                                                            *)
(* This is the EXACT exponential analog of [theories/homs/tensor_construct.v] *)
(* (the tensor discharge T1), with the limit-preserving functor [R := Der]    *)
(* in place of [(C ⊸ −)].  The correspondences:                               *)
(*                                                                            *)
(*   - the functor on objects [(C ⊸ X)] ↦ [Der X = X] (id-on-objects), so     *)
(*     the hom-set [ICones(B, C ⊸ X)] becomes [SCones(B, X) = scones_hom B X];*)
(*   - the functor on morphisms [linhom_post_icones h = (C ⊸ h)] ↦ [ders h];  *)
(*     [linhom_post_comp]/[_id] ↦ [ders_comp]/[ders_id];                       *)
(*   - product preservation [limpl_preserves_prod] ↦ Der's (on the nose,      *)
(*     [der_continuous.v]: [scones_proj i = ders (icones_proj i)] and the     *)
(*     comparison is the identity — no iso needed);                            *)
(*   - equaliser co-restriction [limpl_eq_med_icones] ↦ [der_eq_med]          *)
(*     ([der_continuous.v]);                                                   *)
(*   - the universal map [eB : B → C ⊸ p] ↦ [neB : B → p] in [SCones], the    *)
(*     tuple of all [J = SCones(B, 1)]-elements (via [scones_tuple]);          *)
(*   - [tau'] (the co-restriction of [eB]) ↦ [nl] (the unit / universal       *)
(*     nonlinear map);                                                         *)
(*   - [tensor_curry f = (C ⊸ f) ∘ tau'] ↦ [Theta h = ders h ∘ nl] (built     *)
(*     in [bang.v]); [tensor_uncurry g] ↦ [lin f].                            *)
(*                                                                            *)
(* APIs used: [representable.v] — [wi_obj]/[wi_incl]/[wi_proj]/                *)
(* [wi_factors_each]/[icones_subobject_classP]/[icones_coseparator_inj]/      *)
(* [pb_obj]/[pb_*]; [der_continuous.v] — [der_eq_med]/[_factor]/[_unique];     *)
(* [scones_cat.v] — [ders]/[scones_comp]/[scones_tuple]/[scones_proj] + laws. *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import measurable_structure measurable_function.

Require Import Icones.prelude.classical_extra.
Require Import Icones.prelude.nonneg_extra.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.omega_general.
Require Import Icones.cones.cone_cat.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.path.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.icone.
Require Import Icones.icones.examples_icone.
Require Import Icones.icones.icone_cat.
Require Import Icones.icones.representable.
Require Import Icones.homs.icones_iso.
Require Import Icones.stable.totmono.
Require Import Icones.stable.findiff.
Require Import Icones.stable.compose.
Require Import Icones.stable.scones_cat.
Require Import Icones.stable.der_continuous.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Module Icones_bang_construct.

(** ** A [scones_comp] evaluates by composition on the unit ball

    On the unit ball every clamp of [scones_comp gg ff] is transparent:
    [(gg ∘ ff) x = gg (ff x)] (both [ff x] and the composite are in the
    ball). *)
Lemma scones_comp_ball (R : realType) (Ar : MeasSubcat R)
    (X Y Z : ICone.type Ar) (gg : scones_hom Y Z) (ff : scones_hom X Y)
    (x : X) :
  cone_norm x <= 1 -> sc_fun (scones_comp gg ff) x = sc_fun gg (sc_fun ff x).
Proof. by move=> Hx; rewrite /= (sc_clamp_ball Hx). Qed.

Arguments scones_comp_ball {R Ar X Y Z} gg ff {x}.

(** ** [Der] of an injective map is left-cancellable in [SCones]

    If [h : A1 → A2] is an [ICones]-mono (injective) then [Der h] is a
    [SCones]-mono: on the ball both clamps are transparent, so
    [Der h ∘ u = Der h ∘ v] gives [h (u x) = h (v x)] hence [u x = v x]
    by injectivity; off the ball both are [0]. *)
Lemma ders_mono (R : realType) (Ar : MeasSubcat R)
    (A1 A2 Z : ICone.type Ar) (h : icones_hom Ar A1 A2) :
  is_icones_inj h ->
  forall u v : scones_hom Z A1,
    scones_comp (ders h) u = scones_comp (ders h) v -> u = v.
Proof.
move=> hinj u v Huv; apply: scones_hom_eq => x.
have [Hx|Hx] := boolP (cone_norm x <= 1); last first.
  by rewrite (sc_offball u x Hx) (sc_offball v x Hx).
apply: hinj.
have := congr1 (fun k : scones_hom Z A2 => sc_fun k x) Huv.
rewrite !(scones_comp_ball _ _ Hx).
have Hu : cone_norm (sc_fun u x) <= 1 := sc_image_ball u Hx.
have Hv : cone_norm (sc_fun v x) <= 1 := sc_image_ball v Hx.
by rewrite /ders /= (sc_clamp_ball Hu) (sc_clamp_ball Hv).
Qed.

Arguments ders_mono {R Ar A1 A2 Z} h.

(** ** Functoriality of [Der] (re-exported one-sided laws)

    [ders] is the action of the functor [Der] on morphisms; its identity
    and composition laws are [ders_id] / [ders_comp] of [scones_cat.v].
    We use them directly. *)

(** ** The coseparator power and the universal map [neB]

    Fix [B].  The coseparator is [1 := cone_one_car Ar].  The index type
    [J := SCones(B, Der 1) = SCones(B, 1)] is the homset of stable maps
    [B → 1]; the power is [p := 1^J = icones_prod (fun _ : J => 1)].

    The universal map [neB : B → p] in [SCones] is the tuple of all
    elements of [J]:
      [neB := ⟨ j ⟩_{j ∈ J} = scones_tuple (fun j => j)]. *)

Section UniversalMap.
Variables (R : realType) (Ar : MeasSubcat R).
Variable B : ICone.type Ar.

Local Notation Cone1 := (cone_one_car Ar).

(** The index type [J = SCones(B, 1)]. *)
Definition nJ : Type := scones_hom B Cone1.

(** The constant family at [1] and the coseparator power [p = 1^J]. *)
Definition npfam (_ : nJ) : ICone.type Ar := Cone1.
Definition np : ICone.type Ar := icones_prod npfam.

(** The universal map [neB : B → p], the tuple of all [J]-elements. *)
Definition neB : scones_hom B np := scones_tuple (B := npfam) (fun j : nJ => j).

(** Pointwise value of [neB] on the unit ball: [neB b . j = j b]. *)
Lemma neBE (b : B) (j : nJ) :
  cone_norm b <= 1 -> cones_prod_val (sc_fun neB b) j = sc_fun j b.
Proof.
move=> Hb.
rewrite /neB /= (sc_clamp_ball Hb).
exact: (scones_tuple_val (B := npfam) (fun j0 : nJ => j0) Hb j).
Qed.

End UniversalMap.

Arguments nJ {R Ar} B.
Arguments np {R Ar} B.
Arguments neB {R Ar} B.
Arguments neBE {R Ar B b j}.

(** ** The factoring family and the object [Bang B = E B]

    A member of the family is a subobject-like datum: a domain [fs_dom],
    an ICones-mono embedding [fs_hom : fs_dom → p], and a *factoring
    witness* [fs_eA : B → fs_dom] in [SCones] with
    [Der fs_hom ∘ fs_eA = neB].  As in [tensor_construct.v], in Rocq's
    predicative type theory this family is just a [Type]; the paper's
    well-poweredness ([icones_well_powered]) guarantees it is a *set* —
    automatic here — so the wide intersection [wi_obj] applies directly.

    The basepoint is the identity subobject [(p, id_p, neB)], which
    factors [neB] trivially ([Der id = id]).

    [Bang B := wi_obj] over this family. *)

Section BangObject.
Variables (R : realType) (Ar : MeasSubcat R).
Variable B : ICone.type Ar.

Local Notation p := (np B).

(** A member of the factoring family of subobjects of [p = 1^J]. *)
Record fsub : Type := MkFsub {
  fs_dom : ICone.type Ar;
  fs_hom : icones_hom Ar fs_dom p;
  fs_inj : is_icones_inj fs_hom;
  fs_eA : scones_hom B fs_dom;
  fs_fact : scones_comp (ders fs_hom) fs_eA = neB B;
}.

(** The underlying subobject of a family member. *)
Definition fs_sub (k : fsub) : icones_subobject p :=
  match k with
  | MkFsub A h hinj eA Hf => MkSubobject A h hinj
  end.

(** A family member's embedding is a mono. *)
Definition fs_hom_inj (k : fsub) : is_icones_inj (fs_hom k) :=
  match k as k' return is_icones_inj (fs_hom k') with
  | MkFsub A h hinj eA Hf => hinj
  end.

(** The basepoint subobject [(p, id_p, neB)]. *)
Lemma fk0_fact :
  scones_comp (ders (icones_id Ar p)) (neB B) = neB B.
Proof. by rewrite ders_id scones_compIl. Qed.

Lemma fk0_inj : is_icones_inj (icones_id Ar p).
Proof. by move=> x y. Qed.

Definition fbase : fsub :=
  {| fs_dom := p; fs_hom := icones_id Ar p; fs_inj := fk0_inj;
     fs_eA := neB B; fs_fact := fk0_fact |}.

(** *** The small index — well-poweredness

    As in [tensor_construct.v], the family is indexed by the *small*
    subobject classifier [SubobjClassifier p], not by the proper-class
    record [fsub].  For each classifier value [s] we *choose* (classically)
    a factoring subobject whose classifier is [s], defaulting to [fbase]. *)
Definition fK : Type := SubobjClassifier p.

Definition fpick (s : fK) : fsub :=
  match pselect (exists k : fsub, icones_subobject_class (fs_sub k) = s) with
  | left e => proj1_sig (cid e)
  | right _ => fbase
  end.

Definition fAdom (s : fK) : ICone.type Ar := fs_dom (fpick s).
Definition fhh (s : fK) : icones_hom Ar (fAdom s) p := fs_hom (fpick s).

Definition fhh_inj (s : fK) : is_icones_inj (fhh s) :=
  match fpick s as k return is_icones_inj (fs_hom k) with
  | MkFsub A h hinj eA Hf => hinj
  end.

Definition fk0 : fK := icones_subobject_class (fs_sub fbase).

(** The exponential object [Bang B = E B] as the wide intersection. *)
Definition Bang : ICone.type Ar := wi_obj fhh fk0.

(** The intersection embedding [Bang B ↪ p]. *)
Definition Bang_incl : icones_hom Ar Bang p := wi_incl fAdom fhh fk0.

(** Each chosen representative factors [neB] through [Der (its embedding)]. *)
Lemma fpick_fact (s : fK) :
  scones_comp (ders (fhh s)) (fs_eA (fpick s)) = neB B.
Proof. exact: fs_fact. Qed.

End BangObject.

Arguments fsub {R Ar} B.
Arguments fK {R Ar B}.
Arguments fAdom {R Ar B}.
Arguments fhh {R Ar B}.
Arguments fhh_inj {R Ar B}.
Arguments fk0 {R Ar B}.
Arguments fs_sub {R Ar B}.
Arguments fs_hom_inj {R Ar B}.
Arguments fpick {R Ar B}.
Arguments fpick_fact {R Ar B}.
Arguments Bang {R Ar} B.
Arguments Bang_incl {R Ar} B.

(** ** Intersection minimality: [Bang_incl] factors through every member

    For any factoring-family member [k : fsub B] the intersection
    embedding [Bang_incl] factors through its embedding: [fs_hom k ∘ r =
    Bang_incl] for some [r : Bang B → fs_dom k].  Exactly the
    [ff_factor]/[ff_factorP] of [tensor_construct.v]. *)

Section FsubFactors.
Variables (R : realType) (Ar : MeasSubcat R).
Variable B : ICone.type Ar.

Local Notation p := (np B).

Variable k : fsub B.

Definition ff_class : @fK R Ar B := icones_subobject_class (fs_sub k).

Local Notation SubA :=
  (@MkSubobject R Ar p (fAdom ff_class) (fhh ff_class) (fhh_inj ff_class)).
Local Notation SubK :=
  (@MkSubobject R Ar p (fs_dom k) (fs_hom k) (fs_hom_inj k)).

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

Definition ff_phi : icones_iso Ar (fAdom ff_class) (fs_dom k) :=
  proj1_sig (cid ff_equiv).

Lemma ff_phiE (z : fAdom ff_class) :
  (fs_hom k : icones_hom _ _ _) ((iso_fwd ff_phi : icones_hom _ _ _) z) =
  (fhh ff_class : icones_hom _ _ _) z.
Proof. exact: proj2_sig (cid ff_equiv) z. Qed.

Definition ff_factor : icones_hom Ar (Bang B) (fs_dom k) :=
  icones_comp (iso_fwd ff_phi) (wi_proj fAdom fhh fk0 ff_class).

Lemma ff_factorP :
  icones_comp (fs_hom k) ff_factor = Bang_incl B.
Proof.
rewrite /ff_factor icones_compA.
have Hphi : icones_comp (fs_hom k) (iso_fwd ff_phi) = fhh ff_class.
  by apply: icones_hom_eq => z /=; exact: ff_phiE.
rewrite Hphi.
rewrite -[Bang_incl B]/(wi_incl fAdom fhh fk0).
exact: (@wi_factors_each R Ar (@fK R Ar B) p fAdom fhh fk0 ff_class).
Qed.

End FsubFactors.

Arguments ff_factor {R Ar B} k.
Arguments ff_factorP {R Ar B} k.

(** ** The unit / universal nonlinear map [nl B : B → Bang B]

    [Bang B = wi_obj] is, by construction, the equaliser
    [icones_eq (wi_u fhh) (wi_v fhh fk0)] of two maps [wi_prod → wi_pprod].
    Since [Der] preserves this equaliser ([der_eq_med] of
    [der_continuous.v]), we co-restrict the universal map
    [neprod : B → wi_prod] — the tuple of the factoring witnesses — through
    [Der (eq inclusion)], obtaining [nl B].  Its defining factorisation
    [Der Bang_incl ∘ nl B = neB] then follows from [fpick_fact]. *)

Section Nl.
Variables (R : realType) (Ar : MeasSubcat R).
Variable B : ICone.type Ar.

Local Notation p := (np B).
Local Notation K := (@fK R Ar B).
Local Notation Adom := (@fAdom R Ar B).
Local Notation hh := (@fhh R Ar B).
Local Notation k0 := (@fk0 R Ar B).
Local Notation Wprod := (wi_prod Adom).
Local Notation WU := (wi_u hh).
Local Notation WV := (wi_v hh k0).

(** The tuple of factoring witnesses [neprod : B → wi_prod] (in [SCones]):
    [⟨ fs_eA (fpick s) ⟩_s]. *)
Definition neprod : scones_hom B Wprod :=
  scones_tuple (B := Adom) (fun s : K => fs_eA (fpick s)).

(** Pointwise component of [neprod] on the ball:
    [neprod b . s = fs_eA (fpick s) b]. *)
Lemma neprodE (b : B) (s : K) :
  cone_norm b <= 1 ->
  cones_prod_val (sc_fun neprod b) s = sc_fun (fs_eA (fpick s)) b.
Proof.
move=> Hb.
rewrite /neprod /= (sc_clamp_ball Hb).
exact: (scones_tuple_val (B := Adom) (fun s0 : K => fs_eA (fpick s0)) Hb s).
Qed.

(** Pointwise component of [Der WU] / [Der WV] on the ball. *)
Lemma WUE (x : Wprod) (k : K) :
  cone_norm x <= 1 ->
  cones_prod_val (sc_fun (ders WU) x) k =
  (hh k : icones_hom _ _ _) (cones_prod_val x k).
Proof.
move=> Hx; rewrite /ders /= (sc_clamp_ball Hx).
have := icones_tuple_proj (Q := Wprod)
          (fun k0 => icones_comp (hh k0) (wi_pi Adom k0)) k.
by move/(congr1 (fun w : icones_hom Ar Wprod p => (w : icones_hom _ _ _) x)) => /= ->.
Qed.

Lemma WVE (x : Wprod) (k : K) :
  cone_norm x <= 1 ->
  cones_prod_val (sc_fun (ders WV) x) k =
  (hh k0 : icones_hom _ _ _) (cones_prod_val x k0).
Proof.
move=> Hx; rewrite /ders /= (sc_clamp_ball Hx).
have := icones_tuple_proj (Q := Wprod)
          (fun _ : K => icones_comp (hh k0) (wi_pi Adom k0)) k.
by move/(congr1 (fun w : icones_hom Ar Wprod p => (w : icones_hom _ _ _) x)) => /= ->.
Qed.

(** The factoring witness, evaluated pointwise on the ball:
    [hh s (fs_eA (fpick s) b) = neB b . s] = [neB b . s] ... actually
    [Der (hh s) ∘ fs_eA (fpick s) = neB] gives, componentwise,
    [hh s (fs_eA (fpick s) b) = neB b]. *)
Lemma fpick_factE (b : B) (s : K) :
  cone_norm b <= 1 ->
  (hh s : icones_hom _ _ _) (sc_fun (fs_eA (fpick s)) b) =
  sc_fun (neB B) b.
Proof.
move=> Hb.
have := fpick_fact s.
move/(congr1 (fun w : scones_hom B p => sc_fun w b)).
rewrite /= (sc_clamp_ball Hb) /ders /=.
have Hball : cone_norm (sc_fun (fs_eA (fpick s)) b) <= 1
  := sc_image_ball (fs_eA (fpick s)) Hb.
by rewrite (sc_clamp_ball Hball).
Qed.

(** [neprod] equalises [Der WU] and [Der WV].  Pointwise on the ball,
    both [k]-components reduce — via [WUE]/[WVE], [neprodE] and the
    factoring [fpick_factE] — to [neB b . k] (and the off-ball case is the
    [scones_comp] 0-extension). *)
Lemma neprod_equ :
  scones_comp (ders WU) neprod = scones_comp (ders WV) neprod.
Proof.
apply: scones_hom_eq => b.
have [Hb|Hb] := boolP (cone_norm b <= 1); last by rewrite /= !(sc_clamp_offball Hb).
rewrite !(scones_comp_ball _ _ Hb).
have Hbp : cone_norm (sc_fun neprod b) <= 1 := sc_image_ball neprod Hb.
apply: cones_prod_eq => k.
rewrite (WUE k Hbp) (WVE k Hbp) !(neprodE _ Hb).
by rewrite !(fpick_factE _ Hb).
Qed.

(** [nl B] by co-restriction through [Der (eq inclusion)]. *)
Definition nl : scones_hom B (Bang B) :=
  der_eq_med neprod neprod_equ.

(** Factorisation through the equaliser inclusion:
    [Der eq_incl ∘ nl = neprod]. *)
Lemma nl_eq_incl :
  scones_comp (ders (icones_eq_incl WU WV)) nl = neprod.
Proof. exact: (der_eq_med_factor neprod neprod_equ). Qed.

(** The DEFINING factorisation of the unit:
    [Der Bang_incl ∘ nl = neB].  Pointwise on the ball the [j]-th
    [p]-component reduces, via [nl_eq_incl]/[neprodE]/[fpick_factE], to
    [j b] = [neB b . j]. *)
Lemma nl_def :
  scones_comp (ders (Bang_incl B)) nl = neB B.
Proof.
rewrite /Bang_incl /wi_incl.
rewrite ders_comp -scones_compA nl_eq_incl.
apply: scones_hom_eq => b; rewrite /=.
have [Hb|Hb] := boolP (cone_norm b <= 1); last first.
  rewrite (sc_clamp_offball Hb).
  by rewrite /neB /= (sc_clamp_offball Hb).
rewrite (sc_clamp_ball Hb).
have Hbp : cone_norm (sc_fun neprod b) <= 1 := sc_image_ball neprod Hb.
rewrite /ders /= (sc_clamp_ball Hbp).
(* [wi_incl (nl b) = (hh k0 ∘ wi_pi k0) (neprod b) = hh k0 (fs_eA (fpick k0) b)
   = neB b] ([neprodE] then [fpick_factE] at [k0]). *)
rewrite /comp /cones_proj_fun (neprodE _ Hb).
exact: (fpick_factE k0 Hb).
Qed.

End Nl.

Arguments neprod {R Ar} B.
Arguments nl {R Ar} B.
Arguments nl_def {R Ar} B.

(** ** The intersection embedding [Bang_incl] is a monomorphism

    Exactly [tensor_incl_inj] of [tensor_construct.v]: [Bang B =
    icones_eq WU WV] and [Bang_incl = (hh k0 ∘ π_{k0}) ∘ eq_incl].  Two
    points agree iff their underlying tuples agree componentwise; the
    equaliser constraint plus [Bang_incl x = Bang_incl y] force
    [hh k (val x . k) = hh k (val y . k)] for every [k], whence
    [val x . k = val y . k] by [fhh_inj k] (every family member is a
    mono). *)

Section BangInclInj.
Variables (R : realType) (Ar : MeasSubcat R).
Variable B : ICone.type Ar.

Local Notation p := (np B).
Local Notation K := (@fK R Ar B).
Local Notation hh := (@fhh R Ar B).
Local Notation k0 := (@fk0 R Ar B).
Local Notation WU := (wi_u hh).
Local Notation WV := (wi_v hh k0).

Lemma WUE' (x : wi_prod (@fAdom R Ar B)) (k : K) :
  cones_prod_val ((WU : icones_hom _ _ _) x) k =
  (hh k : icones_hom _ _ _) (cones_prod_val x k).
Proof.
have := icones_tuple_proj (Q := wi_prod (@fAdom R Ar B))
          (fun k1 => icones_comp (hh k1) (wi_pi (@fAdom R Ar B) k1)) k.
by move/(congr1 (fun w : icones_hom Ar (wi_prod (@fAdom R Ar B)) p =>
                   (w : icones_hom _ _ _) x)) => /= ->.
Qed.

Lemma WVE' (x : wi_prod (@fAdom R Ar B)) (k : K) :
  cones_prod_val ((WV : icones_hom _ _ _) x) k =
  (hh k0 : icones_hom _ _ _) (cones_prod_val x k0).
Proof.
have := icones_tuple_proj (Q := wi_prod (@fAdom R Ar B))
          (fun _ : K => icones_comp (hh k0) (wi_pi (@fAdom R Ar B) k0)) k.
by move/(congr1 (fun w : icones_hom Ar (wi_prod (@fAdom R Ar B)) p =>
                   (w : icones_hom _ _ _) x)) => /= ->.
Qed.

Lemma Bang_incl_inj : is_icones_inj (Bang_incl B).
Proof.
rewrite /is_icones_inj => x y Hxy.
have Hk0 : (hh k0 : icones_hom _ _ _) (cones_prod_val (cones_eq_val x) k0) =
           (hh k0 : icones_hom _ _ _) (cones_prod_val (cones_eq_val y) k0).
  exact: Hxy.
have Hcx := cones_eq_eq x.
have Hcy := cones_eq_eq y.
apply: (icones_eq_incl_inj WU WV).
apply: cones_prod_eq => k.
apply: (@fhh_inj R Ar B k).
have Ex : (hh k : icones_hom _ _ _) (cones_prod_val (cones_eq_val x) k) =
          (hh k0 : icones_hom _ _ _) (cones_prod_val (cones_eq_val x) k0).
  have := f_equal (fun z => cones_prod_val z k) Hcx.
  by rewrite WUE' WVE'.
have Ey : (hh k : icones_hom _ _ _) (cones_prod_val (cones_eq_val y) k) =
          (hh k0 : icones_hom _ _ _) (cones_prod_val (cones_eq_val y) k0).
  have := f_equal (fun z => cones_prod_val z k) Hcy.
  by rewrite WUE' WVE'.
by rewrite Ex Hk0 -Ey.
Qed.

End BangInclInj.

Arguments Bang_incl_inj {R Ar} B.

(** ** The linear factoriser [lin f : Bang B → C] — the SAFT comma-category
       mediator (Riehl 4.6.11), the exponential analog of [tensor_uncurry]

    Given a stable map [f : SCones(B, C)], we build the unique LINEAR
    [lin f : Bang B → C] in [ICones] with [Der (lin f) ∘ nl = f]
    ([lin_beta]) by the coseparator-power reindexing of PLAN §13.2 / the
    tensor [tensor_uncurry]:

    Write [1 = cone_one_car Ar].  Form the coseparator power of [C],
    [q C := 1^{ICones(C,1)}], with its canonical mono [GammaC : C ↪ q C]
    (a mono since [1] cogenerates, [icones_coseparator_inj]).  Reindex the
    power [p = 1^J] of [Bang B] to [q C] along
    [θ : ICones(C,1) → J = SCones(B,1), n ↦ Der n ∘ f], giving [P : p → q C]
    with [P x . n = x . (θ n)].  The square
    [Der P ∘ neB = Der GammaC ∘ f] commutes in [SCones] (both send [b,n]
    to [n (f b)] on the ball) — the pullback datum.

    Pull [GammaC] back along [P]: [Csub := pb_obj P GammaC] (the equaliser
    [{(x,c) | P x = GammaC c}]), with embedding [pb_proj1 : Csub → p] and
    projection [pb_proj2 : Csub → C].  The square lets [neB], [f]
    co-restrict (through [Der], which preserves the pullback equaliser,
    [der_eq_med]) to [eA : B → Csub] with [Der pb_proj1 ∘ eA = neB] — so
    [(Csub, pb_proj1, eA)] is a member of the factoring family.  Hence the
    intersection embedding [Bang_incl] factors through it; the [C]-leg of
    that factor is [lin f]. *)

Section Lin.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : ICone.type Ar.

Local Notation Cone1 := (cone_one_car Ar).
Local Notation p := (np B).

Variable f : scones_hom B C.

(** The index of [q C]: the homset [ICones(C, 1)]. *)
Definition tN : Type := icones_hom Ar C Cone1.

(** The coseparator power [q C = 1^{ICones(C,1)}]. *)
Definition tqfam (_ : tN) : ICone.type Ar := Cone1.
Definition tq : ICone.type Ar := icones_prod tqfam.

(** The canonical mono [GammaC : C → q C], [GammaC c . n = n c]. *)
Definition GammaC : icones_hom Ar C tq :=
  icones_tuple (B := tqfam) (fun n : tN => n).

Lemma GammaCE (c : C) (n : tN) :
  cones_prod_val ((GammaC : icones_hom _ _ _) c) n = (n : icones_hom _ _ _) c.
Proof.
have := icones_tuple_proj (B := tqfam) (fun n0 : tN => n0) n.
by move/(congr1 (fun w : icones_hom Ar C Cone1 => (w : icones_hom _ _ _) c)).
Qed.

(** [GammaC] is a mono ([1] cogenerates). *)
Lemma GammaC_inj : is_icones_inj GammaC.
Proof.
move=> x y /(congr1 (fun z : tq => cones_prod_val z)) /= Hxy.
apply: icones_coseparator_inj => n.
by have := f_equal (fun w => w n) Hxy.
Qed.

(** The reindexing map [θ : ICones(C,1) → J = SCones(B, 1)],
    [θ n = Der n ∘ f]. *)
Definition tθ (n : tN) : nJ B := scones_comp (ders n) f.

(** The reindex projection [P : p → q C], [P x . n = x . (θ n)]. *)
Definition tP : icones_hom Ar p tq :=
  icones_tuple (B := tqfam) (fun n : tN => icones_proj (tθ n)).

Lemma tPE (x : p) (n : tN) :
  cones_prod_val ((tP : icones_hom _ _ _) x) n = cones_prod_val x (tθ n).
Proof. by []. Qed.

(** The pullback datum — the commuting square [Der P ∘ neB = Der GammaC ∘ f]
    in [SCones].  Pointwise on the ball, both sides are the element of
    [q C] whose [n]-component is [n (f b)]: LHS via [neBE]
    ([neB b . j = j b]) and [tPE] ([θ n = Der n ∘ f], so [neB b . θ n =
    (θ n) b = n (f b)]); RHS via [GammaCE]. *)
Lemma tP_square :
  scones_comp (ders tP) (neB B) = scones_comp (ders GammaC) f.
Proof.
apply: scones_hom_eq => b.
have [Hb|Hb] := boolP (cone_norm b <= 1); last by rewrite /= !(sc_clamp_offball Hb).
rewrite !(scones_comp_ball _ _ Hb).
have HnB : cone_norm (sc_fun (neB B) b) <= 1 := sc_image_ball (neB B) Hb.
have Hf : cone_norm (sc_fun f b) <= 1 := sc_image_ball f Hb.
rewrite /ders /= (sc_clamp_ball HnB) (sc_clamp_ball Hf).
apply: cones_prod_eq => n.
(* LHS: [tP (neB b) . n = neB b . (θ n) = (θ n) b = n (f b)]. *)
rewrite tPE (neBE Hb).
rewrite GammaCE.
(* [θ n b = (Der n ∘ f) b = n (f b)] on the ball. *)
rewrite /tθ (scones_comp_ball _ _ Hb).
by rewrite /ders /= (sc_clamp_ball Hf).
Qed.

(** *** The pullback [Csub = pb_obj P GammaC] and its [p]-subobject *)

Local Notation Csub := (pb_obj tP GammaC).
Local Notation Cincl := (pb_proj1 tP GammaC).
Local Notation Cpr := (pb_proj2 tP GammaC).

(** [Cincl] is a mono: agreeing under [Cincl] forces agreement under [P],
    hence (via the square) under [GammaC] of the [C]-projection, whence
    the [C]-projections agree ([GammaC] mono); agreeing on both
    projections of the product-equaliser forces equality. *)
Lemma Cincl_inj : is_icones_inj Cincl.
Proof.
have Hsq := pb_square tP GammaC.
move=> a b Hab.
have Hsqpt : forall z : Csub,
    (tP : icones_hom _ _ _) ((Cincl : icones_hom _ _ _) z) =
    (GammaC : icones_hom _ _ _) ((Cpr : icones_hom _ _ _) z).
  by move=> z; have := f_equal
      (fun w : icones_hom Ar Csub tq => (w : icones_hom _ _ _) z) Hsq.
have Hpr2 : (Cpr : icones_hom _ _ _) a = (Cpr : icones_hom _ _ _) b.
  by apply: GammaC_inj; rewrite -!Hsqpt Hab.
apply: (icones_eq_incl_inj (pb_left C tP) (pb_right p GammaC)).
apply: cones_prod_eq; case.
- exact: Hab.
- exact: Hpr2.
Qed.

(** *** Co-restricting [neB] and [f] to [Csub]

    [Csub] is the equaliser of [pb_left = P ∘ π₁] and
    [pb_right = GammaC ∘ π₂] on [pb_prod = p ×_bool C].  As [Der]
    preserves it ([der_eq_med]), the bool-tuple [eAprod : B → pb_prod]
    of [neB] (at [true]) and [f] (at [false]) co-restricts to
    [eA : B → Csub]. *)

(** The [bool]-family tuple [⟨ neB, f ⟩ : B → pb_prod]. *)
Definition eAtupfam (bb : bool) : scones_hom B (pb_fam p C bb) :=
  if bb as bb' return scones_hom B (pb_fam p C bb')
  then neB B else f.

Definition eAprod : scones_hom B (pb_prod p C) :=
  scones_tuple (B := pb_fam p C) eAtupfam.

(** [(Der π_bb) ∘ eAprod = eAtupfam bb] (the [true]/[false] components of
    [eAprod] are [neB]/[f]). *)
Lemma eAprod_pi (bb : bool) :
  scones_comp (ders (icones_proj (B := pb_fam p C) bb)) eAprod = eAtupfam bb.
Proof.
rewrite -[ders (icones_proj (B := pb_fam p C) bb)]/(scones_proj (pb_fam p C) bb).
exact: (scones_tuple_proj (B := pb_fam p C) eAtupfam bb).
Qed.

(** [eAprod] equalises [Der pb_left] and [Der pb_right]: both reduce, via
    [eAprod_pi], to [Der P ∘ neB] resp. [Der GammaC ∘ f], equal by
    [tP_square]. *)
Lemma eAprod_equ :
  scones_comp (ders (pb_left C tP)) eAprod =
  scones_comp (ders (pb_right p GammaC)) eAprod.
Proof.
rewrite /pb_left /pb_right /pb_pi1 /pb_pi2.
rewrite !ders_comp -!scones_compA.
rewrite (eAprod_pi true) (eAprod_pi false).
exact: tP_square.
Qed.

(** The co-restriction [eA : B → Csub]. *)
Definition eA : scones_hom B Csub :=
  der_eq_med eAprod eAprod_equ.

(** [Der eq_incl ∘ eA = eAprod]. *)
Lemma eA_eq_incl :
  scones_comp (ders (icones_eq_incl (pb_left C tP) (pb_right p GammaC))) eA =
  eAprod.
Proof. exact: (der_eq_med_factor eAprod eAprod_equ). Qed.

(** The factoring witness of the family member [(Csub, Cincl, eA)]:
    [Der Cincl ∘ eA = neB].  [Cincl = π₁ ∘ eq_incl], and
    [Der π₁ ∘ eAprod = neB] by [eAprod_pi true]. *)
Lemma eA_fact :
  scones_comp (ders Cincl) eA = neB B.
Proof.
rewrite /pb_proj1 /pb_pi1 ders_comp -scones_compA eA_eq_incl.
exact: (eAprod_pi true).
Qed.

(** The family member [(Csub, Cincl, eA)] as an [fsub]. *)
Definition Cfsub : fsub B :=
  {| fs_dom := Csub; fs_hom := Cincl; fs_inj := Cincl_inj;
     fs_eA := eA; fs_fact := eA_fact |}.

(** *** [lin f] via the intersection's factoring property

    Intersection minimality ([ff_factor]/[ff_factorP]): [Bang_incl]
    factors through [Cincl]; composing that factor with [Cpr] gives the
    [C]-valued LINEAR map [lin f : Bang B → C]. *)
Definition lin : icones_hom Ar (Bang B) C :=
  icones_comp Cpr (ff_factor Cfsub).

(** [Cincl ∘ (factor) = Bang_incl] ([ff_factorP] on [Cfsub]). *)
Lemma lin_factorP :
  icones_comp Cincl (ff_factor Cfsub) = Bang_incl B.
Proof. exact: (ff_factorP Cfsub). Qed.

(** The [C]-leg factoring witness: [Der Cpr ∘ eA = f] ([Cpr = π₂ ∘
    eq_incl] and the [false]-component of [eAprod] is [f]). *)
Lemma eA_pr_fact :
  scones_comp (ders Cpr) eA = f.
Proof.
rewrite /pb_proj2 /pb_pi2 ders_comp -scones_compA eA_eq_incl.
exact: (eAprod_pi false).
Qed.

(** *** [lin_beta] : [Der (lin f) ∘ nl = f]

    The defining factorisation, the exponential analog of
    [tensor_uncurryK].  Let [w := Der (factor) ∘ nl].  Then
    [Der Cincl ∘ w = Der Bang_incl ∘ nl = neB] ([lin_factorP], [nl_def]);
    and [Der Cincl ∘ eA = neB] ([eA_fact]).  As [Der Cincl] is a [SCones]
    mono ([ders_mono] of the pullback mono [Cincl]), [w = eA].  Hence
    [Der (lin f) ∘ nl = Der Cpr ∘ w = Der Cpr ∘ eA = f] ([eA_pr_fact]). *)
Lemma lin_beta_construct :
  scones_comp (ders lin) (nl B) = f.
Proof.
pose w := scones_comp (ders (ff_factor Cfsub)) (nl B).
have Hw_Cincl : scones_comp (ders Cincl) w = neB B.
  rewrite /w scones_compA -ders_comp.
  rewrite -[icones_comp Cincl (ff_factor Cfsub)]/(icones_comp Cincl (ff_factor Cfsub)).
  rewrite lin_factorP.
  exact: nl_def.
have Hwe : w = eA.
  apply: (ders_mono Cincl Cincl_inj).
  by rewrite Hw_Cincl eA_fact.
rewrite /lin ders_comp -scones_compA -/w.
by rewrite Hwe eA_pr_fact.
Qed.

End Lin.

Arguments tN {R Ar} C.
Arguments tq {R Ar} C.
Arguments GammaC {R Ar} C.
Arguments lin {R Ar B C} f.
Arguments lin_beta_construct {R Ar B C} f.
Arguments lin_factorP {R Ar B C} f.
Arguments eA {R Ar B C} f.
Arguments eA_fact {R Ar B C} f.
Arguments eA_pr_fact {R Ar B C} f.
Arguments Cfsub {R Ar B C} f.

(** ** Injectivity of [Θ] — the uniqueness half [lin_unique]

    The SAFT-uniqueness argument (equaliser of the two candidates +
    intersection minimality), the exponential analog of
    [tensor_curry_inj].

    Let [h1, h2 : Bang B → C] with [Der h1 ∘ nl = Der h2 ∘ nl].  Form the
    equaliser [Eq := icones_eq h1 h2] with inclusion [eqe] ([h1 ∘ eqe =
    h2 ∘ eqe], [eqe] a mono).  Since [Der] preserves equalisers, [nl]
    (equalising [Der h1], [Der h2]) co-restricts to [nlE : B → Eq] with
    [Der eqe ∘ nlE = nl] ([der_eq_med]).

    The composite [m_E := Bang_incl ∘ eqe : Eq ↪ p] is a mono, and [neB]
    factors through [Der m_E]:
      [neB = Der Bang_incl ∘ nl = Der Bang_incl ∘ Der eqe ∘ nlE
           = Der m_E ∘ nlE].
    So [(Eq, m_E, nlE)] is a factoring-family member [fsub].  By
    intersection minimality ([ff_factorP]) [Bang_incl] factors through
    [m_E]: [r : Bang B → Eq] with [m_E ∘ r = Bang_incl], i.e.
    [Bang_incl ∘ (eqe ∘ r) = Bang_incl].  As [Bang_incl] is a mono
    ([Bang_incl_inj]), [eqe ∘ r = id]; so [eqe] is a split epi.  An epi
    from [h1 ∘ eqe = h2 ∘ eqe] then gives [h1 = h2]. *)

Section ThetaInj.
Variables (R : realType) (Ar : MeasSubcat R).
Variables B C : ICone.type Ar.

Variables h1 h2 : icones_hom Ar (Bang B) C.
Hypothesis Hth : scones_comp (ders h1) (nl B) = scones_comp (ders h2) (nl B).

Local Notation Eq := (icones_eq h1 h2).
Local Notation eqe := (icones_eq_incl h1 h2).

(** [nl] equalises [Der h1] and [Der h2] — that is exactly [Hth]. *)
Lemma ti_equ :
  scones_comp (ders h1) (nl B) = scones_comp (ders h2) (nl B).
Proof. exact: Hth. Qed.

(** The co-restriction [nlE : B → Eq] ([der_eq_med]). *)
Definition nlE : scones_hom B Eq := der_eq_med (nl B) ti_equ.

Lemma nlE_factor :
  scones_comp (ders eqe) nlE = nl B.
Proof. exact: (der_eq_med_factor (nl B) ti_equ). Qed.

(** The composite embedding [m_E := Bang_incl ∘ eqe : Eq ↪ p]. *)
Definition ti_mE : icones_hom Ar Eq (np B) :=
  icones_comp (Bang_incl B) eqe.

Lemma ti_mE_inj : is_icones_inj ti_mE.
Proof.
move=> a b /= /(Bang_incl_inj B); exact: (icones_eq_incl_inj h1 h2).
Qed.

(** [neB] factors through [Der m_E] via [nlE]: [Der m_E ∘ nlE = neB]. *)
Lemma ti_fact :
  scones_comp (ders ti_mE) nlE = neB B.
Proof.
rewrite /ti_mE ders_comp -scones_compA nlE_factor.
exact: nl_def.
Qed.

(** The factoring-family member [(Eq, m_E, nlE)]. *)
Definition ti_fsub : fsub B :=
  {| fs_dom := Eq; fs_hom := ti_mE; fs_inj := ti_mE_inj;
     fs_eA := nlE; fs_fact := ti_fact |}.

(** Intersection minimality: [Bang_incl] factors through [m_E]. *)
Definition ti_r : icones_hom Ar (Bang B) Eq := ff_factor ti_fsub.

Lemma ti_rP : icones_comp ti_mE ti_r = Bang_incl B.
Proof. exact: (ff_factorP ti_fsub). Qed.

(** [eqe] is a split epi: [eqe ∘ r = id_{Bang B}].  From
    [Bang_incl ∘ (eqe ∘ r) = m_E ∘ r = Bang_incl = Bang_incl ∘ id] and
    [Bang_incl] mono. *)
Lemma ti_split : icones_comp eqe ti_r = icones_id Ar (Bang B).
Proof.
have Hmono := icones_inj_mono (Bang_incl B) (Bang_incl_inj B).
apply: (Hmono _ (icones_comp eqe ti_r) (icones_id Ar (Bang B))).
rewrite icones_compA -/ti_mE ti_rP.
by rewrite icones_compIr.
Qed.

(** Hence [h1 = h2]: [h1 = h1 ∘ eqe ∘ r = h2 ∘ eqe ∘ r = h2]
    ([icones_eq_incl_equ] : [h1 ∘ eqe = h2 ∘ eqe]). *)
Lemma ti_eq : h1 = h2.
Proof.
transitivity (icones_comp h1 (icones_comp eqe ti_r)).
  by rewrite ti_split icones_compIr.
transitivity (icones_comp h2 (icones_comp eqe ti_r)); last first.
  by rewrite ti_split icones_compIr.
by rewrite !icones_compA (icones_eq_incl_equ h1 h2).
Qed.

End ThetaInj.

(** Injectivity of [Θ] (the bijection [Θ] is mono): if [Der h1 ∘ nl =
    Der h2 ∘ nl] then [h1 = h2]. *)
Lemma Theta_inj (R : realType) (Ar : MeasSubcat R)
    (B C : ICone.type Ar) (h1 h2 : icones_hom Ar (Bang B) C) :
  scones_comp (ders h1) (nl B) = scones_comp (ders h2) (nl B) -> h1 = h2.
Proof. exact: ti_eq. Qed.

Arguments Theta_inj {R Ar B C} h1 h2.

(** [lin_unique] : any linear [h] with [Der h ∘ nl = f] equals [lin f].
    By [lin_beta_construct], [Der (lin f) ∘ nl = f = Der h ∘ nl];
    [Theta_inj] then gives [h = lin f]. *)
Lemma lin_unique_construct (R : realType) (Ar : MeasSubcat R)
    (B C : ICone.type Ar) (f : scones_hom B C) (h : icones_hom Ar (Bang B) C) :
  scones_comp (ders h) (nl B) = f -> h = lin f.
Proof.
move=> Hh; apply: Theta_inj.
by rewrite Hh (lin_beta_construct f).
Qed.

Arguments lin_unique_construct {R Ar B C} f h.

End Icones_bang_construct.
