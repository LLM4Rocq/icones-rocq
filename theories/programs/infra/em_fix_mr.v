(**md**************************************************************************)
(** * [em_fix_mr] — the Seely-transported value-fixpoint for mutual recursion

    *** BEYOND THE PAPER — PPL CBV chapter infrastructure

    This file is NOT part of the Ehrhard-Geoffroy 2025 formalization
    (it builds on the CBV value-fixpoint combinator of
    [em_fix_value.v], itself paper-level folklore).

    *** Why this file exists: [ne_fix_mr] at products of free types

    The surface mutual-recursion constructor [ne_fix_mr]
    ([theories/programs/ppl.v]) binds a recursive name at any body type
    [t] with [is_free_coalg_type t] — function types AND products of
    free types (a pair of mutually recursive functions is a recursive
    name at [tprod (tfun A1 B1) (tfun A2 B2)]).  The genuine seeded
    value-fixpoint combinator

      [fix_comb Z : EM( !̃(!Z ⊸ !Z), !̃Z )]

    of [em_fix_value.v] lives on COFREE coalgebras only.  The CBV
    interpretation of a product of free types is NOT literally cofree:
    [tyD_cbv (tprod s t) = EM_prod (tyD s) (tyD t)].  But for free
    [s], [t] it is ISOMORPHIC to a cofree coalgebra via the Seely
    structure:

      [EM_prod (!̃X) (!̃Y)  ≅  !̃(X & Y)]

    — the EM-cartesian product of cofrees is the cofree on the [&]
    (cone) product, the [Seely2 : !X ⊗ !Y ≅ !(X & Y)] story of
    [theories/homs/seely.v]: the carrier of [EM_prod (!̃X) (!̃Y)] is
    [!X ⊗ !Y], its structure map is [tens_cofree_str X Y]
    ([em_cartesian.v::tens_cofree_str_m_bang]), and [tens_cofree_str]
    is BY DEFINITION the transport of [dig_{X&Y}] along [Seely2].

    *** What this file delivers (all axiom-free modulo the 3 boolp axioms)

    - [coalg_iso P Q] — isomorphisms of [!]-coalgebras (both directions
      as [coalg_hom]s + the two round-trips at the [icones_hom] level),
      with [coalg_iso_id] / [coalg_iso_sym] / [coalg_iso_trans] /
      [coalg_iso_prod] (the [EM_prod] congruence, via [EM_prod_mor]).
    - [seely2_em_iso X Y : coalg_iso (EM_prod (!̃X) (!̃Y)) (!̃(X & Y))]
      — the Seely-2 iso packaged at the EM level; the coalgebra-morphism
      squares are pure transport algebra (no point computation).
    - [fix_comb_iso iso : EM( !̃(U P ⊸ U P), P )] for any coalgebra [P]
      with [iso : coalg_iso P (!̃Z)] — the conjugation of [fix_comb Z]
      by the iso: bodies [F : U P ⊸ U P] transport to [!Z ⊸ !Z] by
      pre/post-composition with the iso's underlying linear maps
      ([linhom_map_icones]), and the resulting fixpoint is carried back
      by the iso's backward map.
    - [fix_comb_iso_prom_E] — the prom-point computation law (the
      analogue of [em_fix_value.v::fix_prom_E]); [fix_comb_iso_norm] —
      the norm bound.

    The consumer is [theories/programs/ppl_cbv.v]: [free_decomp] there
    decomposes every [is_free_coalg_type] type into a cofree coalgebra
    by structural induction (the [tprod] step is [coalg_iso_prod]
    composed with [seely2_em_iso]), and [fix_mr_clause] dispatches
    [ne_fix_mr] at product types through [fix_comb_iso] — making the
    mutual-recursion fixpoint GENUINE at products of free types.

    Author: Guillaume Baudart <guillaume.baudart@inria.fr>. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import measurable_structure measurable_function.

Require Import Icones.prelude.nonneg_extra.
Require Import Icones.cones.precone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.cone.
Require Import Icones.cones.omega_general.
Require Import Icones.cones.cone_cat.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.fmeas.
Require Import Icones.mcones.path.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_cat.
Require Import Icones.icones.examples_icone.
Require Import Icones.stable.totmono.
Require Import Icones.stable.stablehom.
Require Import Icones.stable.scones_cat.
Require Import Icones.stable.scones_ccc.
Require Import Icones.stable.fixpoint.
Require Import Icones.stable.stab_lin_swap.
Require Import Icones.stable.diag_bilinear_tensor.
Require Import Icones.homs.icones_iso.
Require Import Icones.homs.linhom.
Require Import Icones.homs.linhom_functor.
Require Import Icones.homs.bilin.
Require Import Icones.homs.exp_adjunction.
Require Import Icones.homs.bang_construct.
Require Import Icones.homs.bang.
Require Import Icones.homs.seely_defs.
Require Import Icones.homs.seely.
Require Import Icones.homs.coalgebra.
Require Import Icones.homs.em_cat.
Require Import Icones.homs.em_seely_comonoid.
Require Import Icones.homs.em_cartesian.
(* NOTE: the tensor stack comes AFTER the Seely/EM stack on purpose:
   [seely.v] and [tensor_hom_iso.v] both export a [linhom_icones]
   constant; downstream files must see [tensor_hom_iso]'s. *)
Require Import Icones.homs.tensor.
Require Import Icones.homs.tensor_construct.
Require Import Icones.homs.smcc.
Require Import Icones.homs.tensor_iso.
Require Import Icones.homs.tensor_hom_iso.
Require Import Icones.programs.infra.em_fix.
Require Import Icones.programs.infra.em_fix_value.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** §1 — Isomorphisms of [!]-coalgebras *)

Section CoalgIso.
Variables (R : realType) (Ar : MeasSubcat R).

(** An isomorphism in [EM(!)]: both directions are bundled coalgebra
    morphisms and the two round-trips are the identity at the
    underlying-[icones_hom] level (whence also at the [coalg_hom]
    level, by [coalg_hom_eqP]). *)
Record coalg_iso (P Q : Coalgebra Ar) : Type := MkCoalgIso {
  ci_fwd : coalg_hom P Q;
  ci_bwd : coalg_hom Q P;
  ci_fwdK : icones_comp (ch_mor ci_bwd) (ch_mor ci_fwd) =
            icones_id Ar (coalg_obj P);
  ci_bwdK : icones_comp (ch_mor ci_fwd) (ch_mor ci_bwd) =
            icones_id Ar (coalg_obj Q);
}.

(** The identity iso. *)
Lemma coalg_iso_idK (P : Coalgebra Ar) :
  icones_comp (ch_mor (coalg_id P)) (ch_mor (coalg_id P)) =
  icones_id Ar (coalg_obj P).
Proof. exact: icones_compIl. Qed.

Definition coalg_iso_id (P : Coalgebra Ar) : coalg_iso P P :=
  MkCoalgIso (coalg_iso_idK P) (coalg_iso_idK P).

(** Symmetry: swap the two directions. *)
Definition coalg_iso_sym (P Q : Coalgebra Ar) (i : coalg_iso P Q) :
    coalg_iso Q P :=
  MkCoalgIso (ci_bwdK i) (ci_fwdK i).

(** Transitivity (composition of isos). *)
Lemma coalg_iso_transK (P Q S : Coalgebra Ar)
    (i : coalg_iso P Q) (j : coalg_iso Q S) :
  icones_comp (ch_mor (coalg_comp (ci_bwd i) (ci_bwd j)))
              (ch_mor (coalg_comp (ci_fwd j) (ci_fwd i))) =
  icones_id Ar (coalg_obj P).
Proof.
rewrite !coalg_comp_mor -icones_compA.
rewrite (icones_compA (ch_mor (ci_bwd j))) (ci_fwdK j) icones_compIl.
exact: (ci_fwdK i).
Qed.

Definition coalg_iso_trans (P Q S : Coalgebra Ar)
    (i : coalg_iso P Q) (j : coalg_iso Q S) : coalg_iso P S :=
  MkCoalgIso (coalg_iso_transK i j)
             (coalg_iso_transK (coalg_iso_sym j) (coalg_iso_sym i)).

(** [EM_prod] congruence: the tensor of two coalg isos is a coalg iso
    between the [EM(!)] products ([EM_prod_mor] for the squares,
    [tensor_mor] functoriality for the round-trips). *)
Lemma coalg_iso_prodK (P P' Q Q' : Coalgebra Ar)
    (i : coalg_iso P P') (j : coalg_iso Q Q') :
  icones_comp (tensor_mor (ch_mor (ci_bwd i)) (ch_mor (ci_bwd j)))
              (tensor_mor (ch_mor (ci_fwd i)) (ch_mor (ci_fwd j))) =
  icones_id Ar (coalg_obj (EM_prod P Q)).
Proof.
rewrite -tensor_mor_comp (ci_fwdK i) (ci_fwdK j).
by rewrite tensor_mor_id.
Qed.

(** The tensor of two bundled coalg morphisms as a [coalg_hom] between
    the [EM_prod]s. *)
Definition coalg_hom_prod (P P' Q Q' : Coalgebra Ar)
    (f : coalg_hom P P') (g : coalg_hom Q Q') :
    coalg_hom (EM_prod P Q) (EM_prod P' Q') :=
  MkCoalgHom (EM_prod_mor (ch_mor f) (ch_mor g)
                (ch_is_mor f) (ch_is_mor g)).

Definition coalg_iso_prod (P P' Q Q' : Coalgebra Ar)
    (i : coalg_iso P P') (j : coalg_iso Q Q') :
    coalg_iso (EM_prod P Q) (EM_prod P' Q') :=
  MkCoalgIso (ci_fwd := coalg_hom_prod (ci_fwd i) (ci_fwd j))
    (ci_bwd := coalg_hom_prod (ci_bwd i) (ci_bwd j))
    (coalg_iso_prodK i j)
    (coalg_iso_prodK (coalg_iso_sym i) (coalg_iso_sym j)).

End CoalgIso.

Arguments coalg_iso {R Ar} P Q.
Arguments ci_fwd {R Ar P Q}.
Arguments ci_bwd {R Ar P Q}.
Arguments ci_fwdK {R Ar P Q}.
Arguments ci_bwdK {R Ar P Q}.
Arguments coalg_iso_id {R Ar} P.
Arguments coalg_iso_sym {R Ar P Q} i.
Arguments coalg_iso_trans {R Ar P Q S} i j.
Arguments coalg_iso_prod {R Ar P P' Q Q'} i j.

(** ** §2 — The Seely-2 iso at the EM level

    [EM_prod (!̃X) (!̃Y) ≅ !̃(X & Y)]: same carrier [!X ⊗ !Y] vs
    [!(X & Y)] related by [Seely2]; the structure map of the product of
    cofrees IS the [Seely2]-transported [tens_cofree_str]
    ([tens_cofree_str_m_bang]), so the coalgebra-morphism squares for
    [Seely2]'s two directions are pure transport algebra. *)

Section Seely2EM.
Variables (R : realType) (Ar : MeasSubcat R).

(** The structure map of a product of two cofree coalgebras is the
    transported [tens_cofree_str] — the two-cone generalisation of
    [em_cartesian.v::EM_prod_str_cofree]. *)
Lemma EM_prod_str_cofree2 (X Y : ICone.type Ar) :
  coalg_str (EM_prod (bang_cofree X) (bang_cofree Y)) =
  tens_cofree_str X Y.
Proof. by rewrite EM_prod_str_E /EM_prod_str /= -(tens_cofree_str_m_bang X Y). Qed.

(** Re-open the transported structure map for the two squares below:
    they unfold [tens_cofree_str] ONCE (top level, no [/=]) and then
    work entirely in [icones_comp]/[bang_fmap] algebra. *)
Local Transparent tens_cofree_str.

(** [Seely2] forward is a coalgebra morphism
    [EM_prod (!̃X) (!̃Y) → !̃(X & Y)]:
    [!S2f ∘ (!S2b ∘ dig ∘ S2f) = !(S2f ∘ S2b) ∘ dig ∘ S2f
     = dig ∘ S2f]. *)
Lemma seely2_fwd_is_coalg_mor (X Y : ICone.type Ar) :
  is_coalg_mor (EM_prod (bang_cofree X) (bang_cofree Y))
               (bang_cofree (sprod X Y)) (iso_fwd (Seely2 X Y)).
Proof.
rewrite /is_coalg_mor EM_prod_str_cofree2 bang_cofree_str /tens_cofree_str.
(* NB: every [icones_compA] below is instantiated EXPLICITLY — an
   unscoped rewrite may unify [iso_fwd (Seely2 X Y)] itself against
   [icones_comp ?g ?f] (unfolding the SAFT internals) and mangle the
   goal. *)
rewrite (icones_compA (bang_fmap (iso_bwd (Seely2 X Y)))
                      (dig (sprod X Y)) (iso_fwd (Seely2 X Y))).
rewrite (icones_compA (bang_fmap (iso_fwd (Seely2 X Y)))
                      (icones_comp (bang_fmap (iso_bwd (Seely2 X Y)))
                                   (dig (sprod X Y)))
                      (iso_fwd (Seely2 X Y))).
rewrite (icones_compA (bang_fmap (iso_fwd (Seely2 X Y)))
                      (bang_fmap (iso_bwd (Seely2 X Y)))
                      (dig (sprod X Y))).
rewrite -(bang_fmap_comp (iso_fwd (Seely2 X Y)) (iso_bwd (Seely2 X Y))).
by rewrite (iso_bwdK (Seely2 X Y)) bang_fmap_id icones_compIl.
Qed.

(** [Seely2] backward is a coalgebra morphism
    [!̃(X & Y) → EM_prod (!̃X) (!̃Y)]:
    [(!S2b ∘ dig ∘ S2f) ∘ S2b = !S2b ∘ dig ∘ (S2f ∘ S2b)
     = !S2b ∘ dig]. *)
Lemma seely2_bwd_is_coalg_mor (X Y : ICone.type Ar) :
  is_coalg_mor (bang_cofree (sprod X Y))
               (EM_prod (bang_cofree X) (bang_cofree Y))
               (iso_bwd (Seely2 X Y)).
Proof.
rewrite /is_coalg_mor EM_prod_str_cofree2 bang_cofree_str /tens_cofree_str.
rewrite -(icones_compA (bang_fmap (iso_bwd (Seely2 X Y)))
                       (icones_comp (dig (sprod X Y)) (iso_fwd (Seely2 X Y)))
                       (iso_bwd (Seely2 X Y))).
rewrite -(icones_compA (dig (sprod X Y)) (iso_fwd (Seely2 X Y))
                       (iso_bwd (Seely2 X Y))).
by rewrite (iso_bwdK (Seely2 X Y)) icones_compIr.
Qed.

(** Re-seal (matching [em_cartesian.v]'s global sealing). *)
Local Opaque tens_cofree_str.

(** The packaged EM-level Seely-2 iso. *)
Definition seely2_em_iso (X Y : ICone.type Ar) :
    coalg_iso (EM_prod (bang_cofree X) (bang_cofree Y))
              (bang_cofree (sprod X Y)) :=
  MkCoalgIso (ci_fwd := MkCoalgHom (seely2_fwd_is_coalg_mor X Y))
    (ci_bwd := MkCoalgHom (seely2_bwd_is_coalg_mor X Y))
    (iso_fwdK (Seely2 X Y)) (iso_bwdK (Seely2 X Y)).

End Seely2EM.

Arguments EM_prod_str_cofree2 {R Ar} X Y.
Arguments seely2_em_iso {R Ar} X Y.

(** ** §3 — The transported value-fixpoint combinator

    For [P] a coalgebra isomorphic to a cofree [!̃Z], the combinator
    [fix_comb Z] conjugates to an EM-morphism

      [fix_comb_iso : EM( !̃(U P ⊸ U P), P )]

    by: (1) transporting the BODY along the iso's underlying linear
    maps ([F : U P ⊸ U P] becomes [fwd ∘ F ∘ bwd : !Z ⊸ !Z], the
    hom-functor action [linhom_map_icones bwd fwd]); (2) running
    [fix_comb Z]; (3) carrying the fixpoint back along [bwd]. *)

Section FixCombIso.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (P : Coalgebra Ar) (Z : ICone.type Ar).
Variable (iso : coalg_iso P (bang_cofree Z)).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).
Local Notation UP := (coalg_obj P).

(** Body transport [U P ⊸ U P → !Z ⊸ !Z] (pre-compose [bwd],
    post-compose [fwd]). *)
Definition fix_iso_body_conj :
    icones_hom Ar (linhom_car Ar UP UP)
                  (linhom_car Ar (Bang Ar Z) (Bang Ar Z)) :=
  linhom_map_icones (ch_mor (ci_bwd iso)) (ch_mor (ci_fwd iso)).

(** The transported combinator — a coalgebra morphism BY CONSTRUCTION
    (a composite of [coalg_hom]s). *)
Definition fix_comb_iso :
    coalg_hom (bang_cofree (linhom_car Ar UP UP)) P :=
  coalg_comp (ci_bwd iso)
    (coalg_comp (fix_comb Z) (bang_cofree_hom fix_iso_body_conj)).

Lemma fix_comb_iso_mor :
  ch_mor fix_comb_iso =
  icones_comp (ch_mor (ci_bwd iso))
    (icones_comp (ch_mor (fix_comb Z)) (bang_fmap fix_iso_body_conj)).
Proof. by []. Qed.

(** The prom-point computation law — the analogue of [fix_prom_E]:
    on a promoted body [F!] the combinator returns the iso-transport
    of the genuine value-fixpoint of the conjugated body. *)
Lemma fix_comb_iso_prom_E (F : linhom_car Ar UP UP)
    (HF : cone_norm F <= 1) :
  Lfun (ch_mor fix_comb_iso) (prom F) =
  Lfun (ch_mor (ci_bwd iso))
    (prom (sc_fun (fix_value Z)
       (linhom_map_fun (ch_mor (ci_bwd iso)) (ch_mor (ci_fwd iso)) F))).
Proof.
have Hconj : cone_norm
    (linhom_map_fun (ch_mor (ci_bwd iso)) (ch_mor (ci_fwd iso)) F) <= 1.
  exact: le_trans (linhom_map_norm_le1 _ _ F) HF.
rewrite fix_comb_iso_mor.
rewrite [in LHS]Lfun_comp [in LHS]Lfun_comp.
rewrite (bang_fmap_prom fix_iso_body_conj F HF).
rewrite -[Lfun fix_iso_body_conj F]
        /(linhom_map_fun (ch_mor (ci_bwd iso)) (ch_mor (ci_fwd iso)) F).
by rewrite (fix_prom_E Hconj).
Qed.

(** Norm bound (the underlying [icones_hom] is norm-decreasing). *)
Lemma fix_comb_iso_norm (v : Bang Ar (linhom_car Ar UP UP)) :
  cone_norm (Lfun (ch_mor fix_comb_iso) v) <= cone_norm v.
Proof. exact: cones_hom_norm_le1. Qed.

End FixCombIso.

Arguments fix_iso_body_conj {R Ar P Z} iso.
Arguments fix_comb_iso {R Ar P Z} iso.
Arguments fix_comb_iso_mor {R Ar P Z} iso.
Arguments fix_comb_iso_prom_E {R Ar P Z} iso {F} HF.
Arguments fix_comb_iso_norm {R Ar P Z} iso v.
