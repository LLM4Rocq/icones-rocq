(**md*** CBV per-iterate outer-point scaffolding

    Shared structural infrastructure for the Bang-level CBV-Y cascade
    examples [ex_loop_arr], [ex_geom_step], and [ex_almost_loop_step].

    These three files all instantiate a per-iterate operator of the form
    [[
       Step γ v := Lfun (bang_fmap (der L)) (Lfun (ch_mor M) (ptensor γ v))
    ]]
    on a function-coalgebra [funT := bang_cofree L] for a linhom-carrier
    [L : ICone.type Ar].  The per-iterate Kleene chain starts at
    [prom (precone_zero : L)] and reduces structurally via the
    "outer point"
    [[
       at_outer_pt_u u := ((one1 : cone_one_car) ⊗p prom u) ⊗p one1
                       : coalg_obj G_L
    ]]
    where [G_L := EM_prod (EM_prod EM_term funT) EM_term].

    The structural reductions of this outer point — [coalg_str_G], the
    [coalg_e_G] cascade, and the [lam_coalg] outer-collapse at
    [ptensor one1 (prom u)] — depend ONLY on [L : ICone.type Ar], not on
    the specific return cone (FMeas / cone_one_car) of the example.  We
    factor them into this module.  The per-example body cascades
    (THEN/ELSE branch evaluations, recursion-variable reads,
    convex-combination decompositions) remain in the per-file
    developments because they depend on the actual body syntax and
    return type.

    What we ship here, AXIOM-FREE (modulo the three [boolp] axioms):

    1. [cone_norm_one1] / [cone_norm_one1_le1]: the unit-cone unit has
       norm exactly 1.

    2. [linhom_fun_precone_add_E] / [linhom_fun_precone_scale_E]: pointwise
       decomposition of [linhom_fun] over [precone_add] / [precone_scale].

    3. Section [OuterPt] parameterised by [L : ICone.type Ar]:
       - [at_outer_pt_u u : coalg_obj G_L];
       - [cone_norm_at_outer_pt_u_le1] / [cone_norm_inner_pt_u_le1] /
         [cone_norm_one_prom_le1];
       - [coalg_str_G_on_outer_pt_u_E] : the [coalg_str (EM_prod (EM_prod
         EM_term funT) EM_term)] cascade at the outer point reduces to
         [prom (at_outer_pt_u u)];
       - [coalg_e_G_on_outer_pt_u_E] : the unit-cone counit at the outer
         point evaluates to [one1].

    4. Section [LamCoalgPromCascade] parameterised by [L : ICone.type Ar]
       and [Y : Coalgebra Ar]:
       - [lam_coalg_at_one_prom] : the outer-prom collapse
         [[
           Lfun (ch_mor (lam_coalg N)) (ptensor one1 (prom u))
           = prom (Lfun (tensor_curry (ch_mor N)) (ptensor one1 (prom u)))
         ]]
         for any [N : coalg_hom (EM_prod (EM_prod EM_term (bang_cofree L))
         EM_term) (Tobj Y)] and any [u : L] with [cone_norm u ≤ 1].

    ** Author

    Guillaume Baudart <guillaume.baudart@inria.fr>. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals signed constructive_ereal.
From mathcomp.algebra Require Import interval_inference.

Require Import Icones.cones.precone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.cone.
Require Import Icones.cones.cone_cat.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.path.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_cat.
Require Import Icones.icones.examples_icone.
Require Import Icones.homs.linhom.
Require Import Icones.homs.tensor.
Require Import Icones.homs.bilin.
Require Import Icones.homs.tensor_iso.
Require Import Icones.homs.smcc.
Require Import Icones.homs.exp_adjunction.
Require Import Icones.homs.bang.
Require Import Icones.homs.seely_defs.
Require Import Icones.homs.seely.
Require Import Icones.homs.coalgebra.
Require Import Icones.homs.em_cat.
Require Import Icones.homs.em_cartesian.
Require Import Icones.homs.em_seely_comonoid.
Require Import Icones.programs.cbv.
Require Import Icones.programs.ppl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** §1 — Pointwise [linhom_fun] decompositions and [cone_norm one1] *)

Section Utility.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

Lemma cone_norm_one1 :
  (cone_norm (one1 : cone_one_car Ar) = 1)%R.
Proof. by rewrite /cone_norm /= /c1_norm. Qed.

Lemma cone_norm_one1_le1 :
  (cone_norm (one1 : cone_one_car Ar) <= 1)%R.
Proof. by rewrite cone_norm_one1. Qed.

Lemma linhom_fun_precone_add_E (C D : ICone.type Ar)
    (f g : linhom_car Ar C D) (x : C) :
  linhom_fun (precone_add f g) x =
  precone_add (linhom_fun f x) (linhom_fun g x).
Proof. by []. Qed.

Lemma linhom_fun_precone_scale_E (C D : ICone.type Ar)
    (r : {nonneg R}) (f : linhom_car Ar C D) (x : C) :
  linhom_fun (precone_scale r f) x =
  precone_scale r (linhom_fun f x).
Proof. by []. Qed.

End Utility.

Arguments cone_norm_one1 {R Ar}.
Arguments cone_norm_one1_le1 {R Ar}.
Arguments linhom_fun_precone_add_E {R Ar C D} f g x.
Arguments linhom_fun_precone_scale_E {R Ar C D} r f x.

(** ** §2 — Outer-point scaffolding parameterised by [L : ICone.type Ar]

    [funT_L = bang_cofree L]; [G_L = EM_prod (EM_prod EM_term funT_L)
    EM_term]; the outer point is [(one1 ⊗ prom u) ⊗ one1]. *)

Section OuterPt.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (L : ICone.type Ar).

Let funT_L : Coalgebra Ar := bang_cofree L.

Local Notation G_L :=
  (EM_prod (EM_prod (EM_term : Coalgebra Ar) funT_L)
           (EM_term : Coalgebra Ar)).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

Definition at_outer_pt_u (u : L) : coalg_obj G_L :=
  ptensor (ptensor (one1 : cone_one_car Ar) (prom u))
          (one1 : cone_one_car Ar).

Lemma cone_norm_one_prom_le1 (u : L) (Hu : cone_norm u <= 1) :
  cone_norm (ptensor (one1 : cone_one_car Ar) (prom u)) <= 1.
Proof.
apply: le_trans (tensor_norm_le _ _) _.
rewrite -[1]mulr1; apply: ler_pM.
- exact: cone_norm_ge0.
- exact: cone_norm_ge0.
- by rewrite cone_norm_one1.
- exact: prom_ball Hu.
Qed.

Lemma cone_norm_inner_pt_u_le1 (u : L) (Hu : cone_norm u <= 1) :
  cone_norm (ptensor (one1 : cone_one_car Ar) (prom u)) <= 1.
Proof. exact: cone_norm_one_prom_le1 Hu. Qed.

Lemma cone_norm_at_outer_pt_u_le1 (u : L) (Hu : cone_norm u <= 1) :
  cone_norm (at_outer_pt_u u) <= 1.
Proof.
rewrite /at_outer_pt_u.
apply: le_trans (tensor_norm_le _ _) _.
rewrite -[1]mulr1; apply: ler_pM.
- exact: cone_norm_ge0.
- exact: cone_norm_ge0.
- exact: cone_norm_one_prom_le1 Hu.
- by rewrite cone_norm_one1.
Qed.

Lemma coalg_str_G_on_outer_pt_u_E (u : L) (Hu : cone_norm u <= 1) :
  Lfun (coalg_str G_L) (at_outer_pt_u u) = prom (at_outer_pt_u u).
Proof.
rewrite (EM_prod_str_E (EM_prod (EM_term : Coalgebra Ar) funT_L)
                       (EM_term : Coalgebra Ar)) /EM_prod_str.
rewrite -[Lfun (icones_comp _ _) _]
        /(Lfun (m_bang (coalg_obj _) (coalg_obj _))
               (Lfun (tensor_mor _ _) _)).
rewrite tensor_morE.
have Hinner :
  Lfun (coalg_str (EM_prod (EM_term : Coalgebra Ar) funT_L))
       (ptensor (one1 : cone_one_car Ar) (prom u))
  = prom (ptensor (one1 : cone_one_car Ar) (prom u)).
  rewrite (EM_prod_str_E (EM_term : Coalgebra Ar) funT_L) /EM_prod_str.
  rewrite -[Lfun (icones_comp _ _) _]
          /(Lfun (m_bang (coalg_obj _) (coalg_obj _))
                 (Lfun (tensor_mor _ _) _)).
  rewrite tensor_morE.
  rewrite -[coalg_str EM_term]/(unit_cofree_str (Ar:=Ar))
          unit_cofree_str_one1.
  rewrite (bang_cofree_str L) (dig_prom (B:=L) u Hu).
  by rewrite (m_bang_prom (x:=one1) (y:=prom u)
                          cone_norm_one1_le1 (prom_ball Hu)).
rewrite Hinner.
rewrite -[coalg_str EM_term]/(unit_cofree_str (Ar:=Ar))
        unit_cofree_str_one1.
by rewrite (m_bang_prom (x:=ptensor (one1 : cone_one_car Ar) (prom u))
                        (y:=one1)
                        (cone_norm_inner_pt_u_le1 Hu)
                        cone_norm_one1_le1).
Qed.

Lemma coalg_e_G_on_outer_pt_u_E (u : L) (Hu : cone_norm u <= 1) :
  Lfun (coalg_e G_L) (at_outer_pt_u u) = one1.
Proof.
have Hz_le1 : cone_norm (at_outer_pt_u u) <= 1
  by exact: cone_norm_at_outer_pt_u_le1.
have Hcs : Lfun (coalg_str G_L) (at_outer_pt_u u) = prom (at_outer_pt_u u)
  by exact: coalg_str_G_on_outer_pt_u_E.
transitivity (Lfun (e_bang (coalg_obj G_L))
                   (Lfun (coalg_str G_L) (at_outer_pt_u u)));
  first by [].
rewrite Hcs.
exact: (@e_bang_prom R Ar (coalg_obj G_L) (at_outer_pt_u u) Hz_le1).
Qed.

End OuterPt.

Arguments at_outer_pt_u {R Ar L} u.
Arguments cone_norm_one_prom_le1 {R Ar L u} Hu.
Arguments cone_norm_inner_pt_u_le1 {R Ar L u} Hu.
Arguments cone_norm_at_outer_pt_u_le1 {R Ar L u} Hu.
Arguments coalg_str_G_on_outer_pt_u_E {R Ar L u} Hu.
Arguments coalg_e_G_on_outer_pt_u_E {R Ar L u} Hu.

(** ** §3 — [lam_coalg] outer-prom collapse cascade

    Parameterised by [L : ICone.type Ar] and the target coalgebra
    [Y : Coalgebra Ar].  This is the generic version of
    [lam_coalg_at_one_prom] / [lam_coalg_at_one_prom_loop]. *)

Section LamCoalgPromCascade.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (L : ICone.type Ar).
Variable (Y : Coalgebra Ar).

Let funT_L : Coalgebra Ar := bang_cofree L.

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

Lemma lam_coalg_at_one_prom
    (N : coalg_hom (EM_prod (EM_prod (EM_term : Coalgebra Ar) funT_L)
                            (EM_term : Coalgebra Ar))
                   (Tobj Y))
    (u : L) (Hu : cone_norm u <= 1) :
  Lfun (ch_mor (lam_coalg N)) (ptensor one1 (prom u)) =
  prom (Lfun (tensor_curry (ch_mor N)) (ptensor one1 (prom u))).
Proof.
rewrite /lam_coalg /lam_under.
rewrite -[ch_mor (adj_psi _)]
        /(icones_comp (bang_fmap (tensor_curry (ch_mor N)))
                      (coalg_str (EM_prod (EM_term : Coalgebra Ar) funT_L))).
rewrite -[Lfun (icones_comp _ _) (ptensor _ _)]
        /(Lfun (bang_fmap (tensor_curry (ch_mor N)))
               (Lfun (coalg_str (EM_prod (EM_term : Coalgebra Ar) funT_L))
                     (ptensor one1 (prom u)))).
rewrite (EM_prod_str_E (EM_term : Coalgebra Ar) funT_L) /EM_prod_str.
rewrite -[Lfun (icones_comp _ _) (ptensor _ _)]
        /(Lfun (m_bang (coalg_obj EM_term) (coalg_obj funT_L))
               (Lfun (tensor_mor (coalg_str EM_term) (coalg_str funT_L))
                     (ptensor one1 (prom u)))).
rewrite tensor_morE.
rewrite -[coalg_str EM_term]/(unit_cofree_str (Ar:=Ar))
        unit_cofree_str_one1.
rewrite (bang_cofree_str L) (dig_prom (B:=L) u Hu).
rewrite (m_bang_prom (x:=one1) (y:=prom u)
                     cone_norm_one1_le1 (prom_ball Hu)).
have Hone_prom : cone_norm (ptensor one1 (prom u)) <= 1
  by exact: (cone_norm_one_prom_le1 (L:=L) Hu).
by rewrite (bang_fmap_prom (tensor_curry (ch_mor N))
                           (ptensor one1 (prom u)) Hone_prom).
Qed.

End LamCoalgPromCascade.

Arguments lam_coalg_at_one_prom {R Ar L Y} N {u} Hu.
