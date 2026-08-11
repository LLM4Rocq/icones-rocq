(**md**************************************************************************)
(* # Exponential construction — the left adjoint [E] of [Der] as the SAFT     *)
(*   construction, instantiated on the SHARED parametric engine of            *)
(*   [saft_construct.v] and SEALED, with the universal-arrow data PROVED      *)
(*   (Paper §9 + [th:Icones-adjoint-functor], the [E ⊣ Der] adjunction).      *)
(*                                                                            *)
(* This file builds the five universal-arrow primitives consumed by           *)
(* [exp_adjunction.v]:                                                        *)
(*                                                                            *)
(*   Bang, nl, lin, lin_beta_construct, lin_unique_construct                  *)
(*                                                                            *)
(* It is AXIOM-FREE relative to the classical [boolp] base — NO               *)
(* [Axiom]/[Parameter]/[Admitted] ([Qed] bodies are traversed by              *)
(* [Print Assumptions]; [verify.sh] checks [Bang_comonad]).  The              *)
(* definitions live in their own module [Icones.exp.bang_construct].          *)
(*                                                                            *)
(* ## The shared SAFT engine ([saft_construct.v])                             *)
(*                                                                            *)
(* The SAFT argument — the factoring family, the classifier reindexing, the   *)
(* wide intersection, intersection minimality, the universal element and its  *)
(* round-trips — is proved ONCE in [Icones.homs.saft_construct] (module       *)
(* [Icones_saft_construct], alias [SC] below) against the signature           *)
(* [SC.saft_sig].  This file instantiates that signature with the right       *)
(* functor [Der] ([bang_sig]: [bang_ehom X := SCones(B, X)],                  *)
(* [bang_emap h := Der h ∘ −] via [ders], products on the nose via            *)
(* [scones_tuple]/[scones_tuple_proj]/[scones_tuple_unique] of                *)
(* [scones_cat.v], equalisers via [der_eq_med]/[der_eq_med_factor] of         *)
(* [der_continuous.v] — paper Thm 7.34).  The correspondences with the        *)
(* tensor instantiation ([tensor_sig] of [tensor_construct.v]):               *)
(*                                                                            *)
(*   - hom-set [ICones(B, C ⊸ X)] ↦ [SCones(B, X)]        ([bang_ehom]);      *)
(*   - action [(C ⊸ h) ∘ −] ↦ [Der h ∘ −]                 ([bang_emap],       *)
(*     laws [ders_id]/[ders_comp], monos [ders_mono]);                        *)
(*   - products [limpl_preserves_prod] ↦ on the nose      ([bang_etuple]);    *)
(*   - equalisers [limpl_eq_med_icones] ↦ [der_eq_med]    ([bang_eq_med]).    *)
(*                                                                            *)
(* ## The sealing ([bang_pack], [Qed])                                        *)
(*                                                                            *)
(* Unlike [tensor_construct.v] (which re-exports the engine's definitions     *)
(* transparently), the instantiation here is SEALED: the engine output —      *)
(* the object [SC.saft_obj], the unit [SC.saft_tau], the mediator             *)
(* [SC.saft_uncurry] and the two halves of the universal property             *)
(* ([SC.saft_uncurryK]/[SC.saft_curry_inj]) — is packed into the Σ-type       *)
(* [bang_pack_t], and the witness [bang_pack] is closed with [Qed].  The      *)
(* consumer-visible constants                                                 *)
(*                                                                            *)
(*   [Bang B := projT1 (bang_pack B)],  [nl B],  [lin f]                      *)
(*                                                                            *)
(* are thin projections of that opaque pack, so their normal forms are        *)
(* ATOMIC — strictly smaller than the previous concrete [wi_obj] twin's —     *)
(* and the conversion-heavy nested-[Bang] comonad proofs of [bang.v] can      *)
(* never pay the parametric engine's normal-form cost (the measured >3.9x     *)
(* slowdown of an unsealed instantiation that motivated this design; see      *)
(* the history note in [saft_construct.v]).  [Qed]-sealing is KERNEL-level:   *)
(* neither tactics nor the final typechecking can unfold [bang_pack], so     *)
(* the [Strategy opaque]/[simpl never] calibration of [exp_adjunction.v] is   *)
(* subsumed rather than merely respected.                                     *)
(*                                                                            *)
(* APIs used: [saft_construct.v] — the SAFT engine; [der_continuous.v] —      *)
(* [der_eq_med]/[_factor]; [scones_cat.v] — [ders]/[scones_comp]/             *)
(* [scones_tuple]/[scones_proj] + laws.                                       *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import measurable_structure measurable_function.

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
Require Import Icones.homs.representable.
Require Import Icones.homs.icones_iso.
Require Import Icones.homs.saft_construct.
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

Module SC := Icones_saft_construct.

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

(** ** The SAFT signature of the right functor [Der]

    The generalised-element functor of the exponential instantiation:
    [bang_ehom X := SCones(B, X)] (the fixed source [B] folded in) with
    hom-action [bang_emap h := Der h ∘ −].  Products are preserved on
    the nose ([scones_proj i = ders (icones_proj i)], [scones_cat.v]),
    so tupling is [scones_tuple] and joint monicity of the projections
    is [scones_tuple_unique]; equalisers through the co-restriction
    [der_eq_med] ([der_continuous.v], paper Thm 7.34).  [bang_sig]
    packages these as an [SC.saft_sig], against which the shared SAFT
    engine of [saft_construct.v] delivers the construction. *)

Section BangSig.
Variables (R : realType) (Ar : MeasSubcat R).
Variable B : ICone.type Ar.

Definition bang_ehom (X : ICone.type Ar) : Type := scones_hom B X.

Definition bang_emap (X Y : ICone.type Ar) (h : icones_hom Ar X Y)
    (g : bang_ehom X) : bang_ehom Y :=
  scones_comp (ders h) g.

Lemma bang_emap_id (X : ICone.type Ar) (g : bang_ehom X) :
  bang_emap (icones_id Ar X) g = g.
Proof. by rewrite /bang_emap ders_id scones_compIl. Qed.

Lemma bang_emap_comp (X Y Z : ICone.type Ar)
    (h1 : icones_hom Ar X Y) (h2 : icones_hom Ar Y Z) (g : bang_ehom X) :
  bang_emap (icones_comp h2 h1) g = bang_emap h2 (bang_emap h1 g).
Proof. by rewrite /bang_emap ders_comp -scones_compA. Qed.

Lemma bang_emap_mono (X Y : ICone.type Ar) (h : icones_hom Ar X Y) :
  is_icones_inj h ->
  forall u v : bang_ehom X, bang_emap h u = bang_emap h v -> u = v.
Proof. by move=> hinj u v; exact: (ders_mono h hinj u v). Qed.

Definition bang_etuple (K : Type) (X : K -> ICone.type Ar)
    (g : forall k, bang_ehom (X k)) : bang_ehom (icones_prod X) :=
  scones_tuple g.

Lemma bang_etuple_proj (K : Type) (X : K -> ICone.type Ar)
    (g : forall k, bang_ehom (X k)) (k : K) :
  bang_emap (icones_proj k) (bang_etuple g) = g k.
Proof. exact: (scones_tuple_proj g k). Qed.

(** Joint monicity of the [Der π_k]: two elements of [SCones(B, ∏ X_k)]
    with equal projections are equal — both are the [scones_tuple] of
    their common projections ([scones_tuple_unique]). *)
Lemma bang_eprod_ext (K : Type) (X : K -> ICone.type Ar)
    (a b : bang_ehom (icones_prod X)) :
  (forall k, bang_emap (icones_proj k) a = bang_emap (icones_proj k) b) ->
  a = b.
Proof.
move=> Hab.
have Ha : a = scones_tuple (fun k => bang_emap (icones_proj k) a).
  by apply: scones_tuple_unique => k.
have Hb : b = scones_tuple (fun k => bang_emap (icones_proj k) a).
  by apply: scones_tuple_unique => k; rewrite (Hab k).
by rewrite Ha Hb.
Qed.

Definition bang_eq_med (X Y : ICone.type Ar) (u v : icones_hom Ar X Y)
    (g : bang_ehom X) (E : bang_emap u g = bang_emap v g) :
    bang_ehom (icones_eq u v) :=
  der_eq_med g E.

Lemma bang_eq_med_factor (X Y : ICone.type Ar) (u v : icones_hom Ar X Y)
    (g : bang_ehom X) (E : bang_emap u g = bang_emap v g) :
  bang_emap (icones_eq_incl u v) (bang_eq_med E) = g.
Proof. exact: (der_eq_med_factor g E). Qed.

(** The packaged signature. *)
Definition bang_sig : SC.saft_sig Ar :=
  @SC.MkSaftSig R Ar bang_ehom bang_emap bang_emap_id bang_emap_comp
    bang_emap_mono bang_etuple bang_etuple_proj bang_eprod_ext
    bang_eq_med bang_eq_med_factor.

(** ** The sealed pack

    The Σ-type [bang_pack_t] packages the whole universal-arrow content
    of the [E ⊣ Der] adjunction at [B]: the object, the unit, the linear
    factoriser and the two halves of the universal property.  The
    witness [bang_pack] instantiates the shared engine at [bang_sig] —
    [Bang B := SC.saft_obj] (the wide intersection over the coseparator
    power [1^{SCones(B,1)}]), [nl B := SC.saft_tau] (the co-restricted
    universal tuple), [lin := SC.saft_uncurry] (the comma-category
    mediator), with [lin_beta = SC.saft_uncurryK] and [lin_unique] from
    [SC.saft_curry_inj] — and is closed with [Qed], so the projections
    below are conversion-ATOMIC. *)

Definition bang_pack_t : Type :=
  {E : ICone.type Ar &
  {nlB : scones_hom B E &
  {linf : forall C : ICone.type Ar, scones_hom B C -> icones_hom Ar E C |
    (forall (C : ICone.type Ar) (f : scones_hom B C),
        scones_comp (ders (linf C f)) nlB = f) /\
    (forall (C : ICone.type Ar) (f : scones_hom B C)
            (h : icones_hom Ar E C),
        scones_comp (ders h) nlB = f -> h = linf C f)}}}.

Lemma bang_pack : bang_pack_t.
Proof.
exists (@SC.saft_obj R Ar bang_sig).
exists (@SC.saft_tau R Ar bang_sig).
exists (fun C f => @SC.saft_uncurry R Ar bang_sig C f).
split.
- move=> C f; exact: (@SC.saft_uncurryK R Ar bang_sig C f).
- move=> C f h Hh.
  apply: (@SC.saft_curry_inj R Ar bang_sig C).
  rewrite (@SC.saft_uncurryK R Ar bang_sig C f).
  exact: Hh.
Qed.

(** ** The five sealed primitives

    Thin projections of the opaque [bang_pack]; their normal forms are
    atomic ([projT1 (bang_pack B)], …).  [exp_adjunction.v] re-exports
    them (with [Strategy opaque]/[simpl never]) as the facade the
    comonad ([bang.v]) and Seely ([seely.v]) milestones consume. *)

(** The exponential object [Bang B = E B] (Paper §9, [\Excls]). *)
Definition Bang : ICone.type Ar := projT1 bang_pack.

(** The unit / universal nonlinear map [nl B : B → !B] (Paper §9,
    [\Unistab_B]). *)
Definition nl : scones_hom B Bang := projT1 (projT2 bang_pack).

(** The linear factoriser [lin f : !B → C] (Paper §9, [Θ⁻¹]). *)
Definition lin (C : ICone.type Ar) (f : scones_hom B C) :
    icones_hom Ar Bang C :=
  proj1_sig (projT2 (projT2 bang_pack)) C f.

(** Existence half of the universal property: [Der (lin f) ∘ nl = f]. *)
Lemma lin_beta_construct (C : ICone.type Ar) (f : scones_hom B C) :
  scones_comp (ders (lin f)) nl = f.
Proof. exact: (proj1 (proj2_sig (projT2 (projT2 bang_pack))) C f). Qed.

(** Uniqueness half: any linear [h] with [Der h ∘ nl = f] equals
    [lin f]. *)
Lemma lin_unique_construct (C : ICone.type Ar) (f : scones_hom B C)
    (h : icones_hom Ar Bang C) :
  scones_comp (ders h) nl = f -> h = lin f.
Proof. exact: (proj2 (proj2_sig (projT2 (projT2 bang_pack))) C f h). Qed.

End BangSig.

Arguments Bang {R Ar} B.
Arguments nl {R Ar} B.
Arguments lin {R Ar B C} f.
Arguments lin_beta_construct {R Ar B C} f.
Arguments lin_unique_construct {R Ar B C} f h.

End Icones_bang_construct.
