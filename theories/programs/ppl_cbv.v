(**md**************************************************************************)
(** * Clean CBV interpreter for the named-PPL — linhom-valued, comonoid-primitive

    A presentation of the call-by-value denotational semantics for the
    higher-order probabilistic calculus of [ppl.v] in which every
    expression denotes a LINEAR morphism in [ICone]: an element of
    [linhom_car Ar (coalg_obj (ctxD_cbv Γ)) (coalg_obj (tyD_cbv τ))].
    Programs are linear maps in [ICone], not coalgebra morphisms; the
    coalgebra structure of the context is used ONLY through the
    transported commutative-comonoid pair [(δ, ε) = (coalg_d, coalg_e)]
    of every coalgebra (Melliès Prop 28 / Cor 20, [em_cartesian.v]).

    The type interpretation drops the Kleisli-exponential wrapping on
    the codomain of [tfun]: it is simply [!̃(U⟦A⟧ ⊸ U⟦B⟧)], reflecting
    the linear-map view of programs.  Contexts are interpreted by
    [ctxD_cbv] as a tensor of coalgebras, head of the list on the
    RIGHT.

    The clause-by-clause shape of [eD]:
    [[
      ⟦x⟧             = projection from the tensor (ε on every other
                        slot, id on the chosen one)
      ⟦let x = e₁ in e₂⟧ = δ_Γ ; (id_Γ ⊗ e₁) ; e₂
      ⟦(e₁, e₂)⟧      = δ_Γ ; (e₁ ⊗ e₂)
      ⟦fst p⟧         = p ; (id ⊗ ε)
      ⟦snd p⟧         = p ; (ε ⊗ id)
      ⟦λx.M⟧          = curry M ; promote to !̃(U A ⊸ U B)
      ⟦f e⟧           = δ_Γ ; (f ⊗ e) ; (der ⊗ id) ; eval
      ⟦()⟧            = ε_Γ
      ⟦sample µ⟧      = ε_Γ ; const µ
      ⟦score f e⟧     = ε on the unused slots, scale by density
      ⟦r⟧             = ε_Γ ; const δ_r
      ⟦e₁ + e₂⟧       = δ_Γ ; (e₁ ⊗ e₂) ; add_lift
      ⟦e₁ × e₂⟧       = δ_Γ ; (e₁ ⊗ e₂) ; mul_lift
      ⟦true⟧/⟦false⟧  = ε_Γ ; const δ_T/δ_F
      ⟦Bernoulli p⟧   = ε_Γ ; const Bern(p)
      ⟦if b then M else N⟧ = δ_Γ ; (id_Γ ⊗ b) ; braid
                             ; uncurry (bool_case M N)
      ⟦fix s.M⟧       = Yfix_fun_lin (Kleene on the unit-ball CPO)
    ]]

    DESIGN INTENT.  No [Tobj] anywhere on the codomain of [tfun]; no
    [kbind_ext] / [kcomp] / [Tmap] in the interpretation; the only
    cofree wrapping is the OUTER [!̃] of [tfun A B], realising the
    duplicability of function values.  Every clause is built from the
    SMC primitives ([linhom_comp], the tensor/braid/unitors) and the
    coalgebra-comonoid pair ([coalg_d], [coalg_e]) only.

    The file compiles cleanly with no [Admitted] stubs; every
    clause is built from the SMC primitives, the coalgebra-comonoid
    pair, and the existing arithmetic / score / boolean helpers of
    [ppl.v].  Recursion ([ne_fix], [ne_fix_mr]) routes through the
    clean-cone [Yfix_fun_lin] of
    [theories/programs/infra/em_fix.v]. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals signed constructive_ereal.
From mathcomp.algebra Require Import interval_inference.
From mathcomp.analysis Require Import measurable_structure measurable_function.
From mathcomp.analysis Require Import measurable_realfun.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import measure dirac_measure.
From mathcomp.analysis Require Import lebesgue_integral_definition.
From mathcomp.analysis Require Import lebesgue_integral_nonneg.

From Stdlib Require Import Strings.String.

Require Import Icones.cones.precone.
Require Import Icones.cones.basic_lemmas.
Require Import Icones.cones.cone.
Require Import Icones.cones.cone_cat.
Require Import Icones.programs.infra.bool_cone.
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
Require Import Icones.homs.exp_adjunction.
Require Import Icones.homs.bang.
Require Import Icones.homs.seely_defs.
Require Import Icones.homs.seely.
Require Import Icones.homs.tensor_hom_iso.
Require Import Icones.programs.infra.bool_case_hom.
Require Import Icones.homs.coalgebra.
Require Import Icones.programs.infra.bool_cone_coalg.
Require Import Icones.homs.fmeas_lax.
Require Import Icones.homs.em_cat.
Require Import Icones.homs.em_seely_comonoid.
Require Import Icones.homs.em_cartesian.
Require Import Icones.programs.infra.cbv_adjunction.
Require Import Icones.programs.ppl.
Require Import Icones.programs.infra.em_fix.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Opaque tensor_mor tensor_assoc tensor_lunit tensor_runit tensor_braid
       ptensor tau Seely2.
Opaque dig der prom bang_fmap d_bang e_bang unit_cofree_str Coalg
       tens_cofree_str m_bang.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** Type and context interpretation — direct-style, no [Tobj] on [tfun] *)

Section TypeInterpCBV.
Variables (R : realType) (Ar : MeasSubcat R).

(** [tyD_cbv t] — every type denotes a coalgebra of [EM(!)].

    The load-bearing clause:
    - [tfun A B] is interpreted as [!̃(U⟦A⟧ ⊸ U⟦B⟧)], WITHOUT the [Tobj]
      wrap on the codomain.  Function VALUES are linear maps
      [U⟦A⟧ ⊸ U⟦B⟧]; duplicability comes from the OUTER [!̃] only. *)
Fixpoint tyD_cbv (t : ppl_type Ar) : Coalgebra Ar :=
  match t with
  | tunit => EM_term
  (* [tbool] uses the §9.7-style coalgebra on the 2-point sub-
     probability cone of [bool_cone.v], hand-rolled in
     [bool_cone_coalg.v] (the [bool] type is not an [ar_obj Ar] in this
     codebase, so [FMeas_coalgebra bool_meas_space] is unavailable; we
     specialise the §9.7 integral [∫ prom(δ_x) dµ(x)] to the finite
     sum [p · prom(δ_T) + q · prom(δ_F)] on the 2-point cone).  This
     gives the SHARED-SAMPLE semantics for [let x = Bernoulli(p) in (x,x)]
     (= [p · (T,T) + (1-p) · (F,F)], the diagonal pushforward) instead of
     the independent-product semantics [bang_cofree] would give. *)
  | tbool => bool_cone_coalg
  | tbase X => FMeas_coalgebra X
  | tprod s1 s2 => EM_prod (tyD_cbv s1) (tyD_cbv s2)
  (* Clean CBV function type — no [Tobj] on the codomain. *)
  | tfun A B => bang_cofree (linhom_car Ar (coalg_obj (tyD_cbv A))
                                          (coalg_obj (tyD_cbv B)))
  end.

(** Contexts: head of the list on the RIGHT, so [hv_zero] = second
    component and [hv_succ] strips the head — the orientation
    [var_lookup_cbv] (below) projects against. *)
Fixpoint ctxD_cbv (G : ppl_ctx Ar) : Coalgebra Ar :=
  match G with
  | nil => EM_term
  | t :: G' => EM_prod (ctxD_cbv G') (tyD_cbv t)
  end.

End TypeInterpCBV.

Arguments tyD_cbv {R Ar} t.
Arguments ctxD_cbv {R Ar} G.

(** ** Variable lookup — projection chains over a coalgebra context

    [var_lookup_cbv v] takes a De Bruijn witness [v : has_var G t] over
    the CBV-skeletal context and returns a [coalg_hom (ctxD_cbv G)
    (tyD_cbv t)].  Structure: [hv_zero] reads the second component of
    the head tensor; [hv_succ] reads the first and recurses.

    Pure projection: [em_proj2] / [em_proj1] chains, no [δ], no [str]
    (contract C4: [ne_var] uses only the comonoid counit/projections). *)
Section VarLookupCBV.
Variables (R : realType) (Ar : MeasSubcat R).

Fixpoint var_lookup_cbv (G : ppl_ctx Ar) (t : ppl_type Ar)
    (v : has_var G t) {struct v} :
    coalg_hom (ctxD_cbv G) (tyD_cbv t) :=
  match v in has_var G0 t0 return coalg_hom (ctxD_cbv G0) (tyD_cbv t0) with
  | hv_zero G' t' => em_proj2 (ctxD_cbv G') (tyD_cbv t')
  | hv_succ G' t' s v' =>
      coalg_comp (var_lookup_cbv v') (em_proj1 (ctxD_cbv G') (tyD_cbv s))
  end.

End VarLookupCBV.

Arguments var_lookup_cbv {R Ar G t} v.

(** ** Real / sample / boolean / Bernoulli constant helpers — CBV-clean

    Direct-style: a sample / real / boolean / Bernoulli constructor
    denotes a CONSTANT [icones_hom] out of the context into the value
    coalgebra's carrier, with NO outer [Tobj] wrap (the old
    [Tobj]-wrapped Kleisli variants are deleted).  Every constructor's
    denotation lives in [coalg_obj (tyD_cbv t)] directly.

    All four reuse [const_icones] of [ppl.v::Section ConstIcones]:
    given a unit-ball value [c : C], [const_icones G c Hc] is the
    constant icones_hom out of [coalg_obj G] taking the value [c]. *)

Section ConstHelpersCBV.
Variables (R : realType) (Ar : MeasSubcat R).

(** Constant [icones_hom] at a unit-ball measure [µ : FMeas X]. *)
Definition sample_icones (G : Coalgebra Ar) (X : ar_obj Ar)
    (mu : fmeas R (ar_carrier Ar X)) (Hmu : (cone_norm mu <= 1)%R) :
    icones_hom Ar (coalg_obj G) (coalg_obj (FMeas_coalgebra X)) :=
  const_icones G mu Hmu.

(** Constant [icones_hom] at a Dirac on a real literal. *)
Definition real_icones (R_obj : ar_obj Ar)
    (R_carrier_eq : ar_carrier Ar R_obj = R :> Type)
    (G : Coalgebra Ar) (r : R) :
    icones_hom Ar (coalg_obj G) (coalg_obj (FMeas_coalgebra R_obj)) :=
  const_icones G (dirac_fmeas (R_to_carrier R_carrier_eq r))
                 (dirac_fmeas_norm_le1 _).

(** Constant [icones_hom] at the [true]-Dirac of [bool_cone].
    With the §9.7-style [bool_cone_coalg], the carrier of [tyD_cbv tbool]
    is [bool_cone_car Ar] directly (no [Bang] wrap), so the value is
    the basis point [bool_dirac_true] itself. *)
Definition true_icones (G : Coalgebra Ar) :
    icones_hom Ar (coalg_obj G) (bool_cone_car Ar) :=
  const_icones G (bool_dirac_true : bool_cone_car Ar)
                 bool_dirac_true_norm_le1.

(** Constant [icones_hom] at the [false]-Dirac of [bool_cone]. *)
Definition false_icones (G : Coalgebra Ar) :
    icones_hom Ar (coalg_obj G) (bool_cone_car Ar) :=
  const_icones G (bool_dirac_false : bool_cone_car Ar)
                 bool_dirac_false_norm_le1.

(** Constant [icones_hom] at the Bernoulli sub-probability [(p, 1-p)]. *)
Definition bernoulli_icones (G : Coalgebra Ar) (p : R)
    (Hp_ge0 : (0 <= p)%R) (Hp_le1 : (p <= 1)%R) :
    icones_hom Ar (coalg_obj G) (bool_cone_car Ar) :=
  const_icones G (bernoulli p Hp_ge0 Hp_le1)
                 (bernoulli_norm_le1 p Hp_ge0 Hp_le1).

End ConstHelpersCBV.

Arguments sample_icones {R Ar} G {X} mu Hmu.
Arguments real_icones {R Ar} R_obj R_carrier_eq G r.
Arguments true_icones {R Ar} G.
Arguments false_icones {R Ar} G.
Arguments bernoulli_icones {R Ar} G p Hp_ge0 Hp_le1.

(** ** [if-then-else] at the icones level — CBV, no [Tobj]

    The [if_icones] combinator takes two branch icones_homs from a
    shared context [G] into a common target coalgebra [A], plus a
    boolean scrutinee icones_hom from [G] into [Bang bool_cone], and
    produces the dispatch icones_hom [G → A].

    Recipe (no [Tobj] wrap on the codomain; with the §9.7 coalgebra
    on [bool_cone_car], the scrutinee lives in [bool_cone_car Ar]
    directly, so no [der] dance is needed):
    1. Branches as norm-[≤1] linhoms [aM, bN : G ⊸ A].
    2. [bool_case_linhom aM bN : bool_cone ⊸ (G ⊸ A)] of the
       universal co-pairing of [bool_case_hom.v].
    3. [linhom_icones] back to [icones_hom bool_cone (G ⊸ A)].
    4. [tensor_uncurry] to [bool_cone ⊗ G → A].
    5. Pre-compose with [braid : G ⊗ bool_cone → bool_cone ⊗ G].
    6. Pre-compose with [em_pair_mor id_G (eD b)] : [G → G ⊗ bool_cone]
       (the pair is taken in [EM(!)] using [bool_cone_coalg] as the
       second factor's coalgebra structure). *)

Section IfICones.
Variables (R : realType) (Ar : MeasSubcat R).
Variables (G : Coalgebra Ar) (A : Coalgebra Ar).
Variables (m : icones_hom Ar (coalg_obj G) (coalg_obj A))
          (n : icones_hom Ar (coalg_obj G) (coalg_obj A)).

(** Branches as norm-[≤1] linhoms [G ⊸ A]. *)
Let m_lh : linhom_car Ar (coalg_obj G) (coalg_obj A) :=
  icones_to_linhom m.
Let n_lh : linhom_car Ar (coalg_obj G) (coalg_obj A) :=
  icones_to_linhom n.

Lemma if_m_lh_norm : (cone_norm m_lh <= 1)%R.
Proof. exact: icones_to_linhom_norm_le1. Qed.

Lemma if_n_lh_norm : (cone_norm n_lh <= 1)%R.
Proof. exact: icones_to_linhom_norm_le1. Qed.

(** Step 2: [bool_case_linhom] at the linhom-cone level. *)
Let if_lh : linhom_car Ar (bool_cone_car Ar)
    (linhom_car Ar (coalg_obj G) (coalg_obj A)) :=
  bool_case_linhom m_lh n_lh if_m_lh_norm if_n_lh_norm.

Lemma if_lh_norm : (cone_norm if_lh <= 1)%R.
Proof. exact: bool_case_linhom_norm_le1. Qed.

(** Step 3: bridge to an [icones_hom]. *)
Let if_hom : icones_hom Ar (bool_cone_car Ar)
    (linhom_car Ar (coalg_obj G) (coalg_obj A)) :=
  linhom_icones if_lh if_lh_norm.

(** Step 4: SAFT uncurry to [bool_cone ⊗ G → A]. *)
Let if_uncurried : icones_hom Ar
    (tensor Ar (bool_cone_car Ar) (coalg_obj G)) (coalg_obj A) :=
  tensor_uncurry if_hom.

(** Step 5: pre-compose with the braid [G ⊗ bool_cone → bool_cone ⊗ G].
    No [der] is needed: with the §9.7-style [bool_cone_coalg], the
    scrutinee directly produces [bool_cone_car Ar] (not [Bang _]). *)
Definition if_under :
    icones_hom Ar
      (tensor Ar (coalg_obj G) (bool_cone_car Ar))
      (coalg_obj A) :=
  icones_comp if_uncurried
    (iso_fwd (tensor_braid (coalg_obj G) (bool_cone_car Ar))).

(** Step 6: pre-compose with the pairing of [id_G] and the scrutinee.
    Final icones_hom: [G → A].  The pair uses [em_pair_mor] which
    elaborates [Q] from the second argument's codomain; passing [b]
    as an icones_hom into [bool_cone_car Ar = coalg_obj bool_cone_coalg]
    makes [Q := bool_cone_coalg]. *)
Definition if_icones (b : icones_hom Ar (coalg_obj G)
                            (coalg_obj (@bool_cone_coalg R Ar))) :
    icones_hom Ar (coalg_obj G) (coalg_obj A) :=
  icones_comp if_under
    (@em_pair_mor R Ar G G (@bool_cone_coalg R Ar)
       (icones_id Ar (coalg_obj G)) b).

End IfICones.

Arguments if_under {R Ar G A} m n.
Arguments if_icones {R Ar G A} m n b.

(** ** Term interpretation [eD_cbv] — icones_hom-valued

    Internally [eD_cbv] returns an [icones_hom] (a norm-[≤1] linear
    morphism); the public-facing linhom is [icones_to_linhom
    (eD_cbv M)] = [eD M] of [Section PublicED].  The
    icones_hom output is the cleanest way to compose with the SMC and
    coalgebra-comonoid primitives:
    - tensor product of two morphisms is [tensor_mor] (icones_hom);
    - the comonoid diagonal / counit are [coalg_d] / [coalg_e]
      (icones_hom);
    - currying / evaluation are [tensor_curry] / [tensor_uncurry]
      (icones_hom).

    Both recursion clauses [ne_fix] and [ne_fix_mr] use the
    [Yfix_fun_lin] of [theories/programs/infra/em_fix.v] — the CBV
    value-fixpoint operator at the linhom level, ported to the clean
    cone (no [Tobj] / [!̃U] wrap on the codomain).  Parametric in [Γ]
    and [B], so the same operator handles both [tfun] and
    free-coalgebra-product return types. *)
Section TermInterpCBV.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Local Notation T := (@ppl_type R Ar).
Local Notation EXi G t :=
    (icones_hom Ar (coalg_obj (ctxD_cbv (drop_names G)))
                   (coalg_obj (tyD_cbv t))).

(** The denotation of a named expression as a norm-[≤1] linear
    morphism in [ICones]: an [icones_hom] from the context's underlying
    cone to the type's underlying cone, both AS [!]-COALGEBRAS — but
    [eD_cbv M] itself is a plain [icones_hom], NOT a coalgebra
    morphism.  Programs are linear maps in [ICones], not coalgebra
    morphisms; the coalgebra structure of [⟦Γ⟧] is used only through
    the transported comonoid pair [(coalg_d, coalg_e)]. *)
Fixpoint eD_cbv (G : named_ctx Ar) (t : T)
    (M : @named_expr R Ar R_obj G t) {struct M} : EXi G t.
Proof.
refine (
  match M in named_expr G0 t0 return EXi G0 t0 with
  (* [ne_var v]: lookup via projection from the context tensor. *)
  | ne_var _ _ v => ch_mor (var_lookup_cbv (named_var_to_has_var v))
  (* [ne_tt]: ε_Γ — the comonoid counit. *)
  | ne_tt G0 => ch_mor (em_term_mor (ctxD_cbv (drop_names G0)))
  (* [ne_pair M N]: δ_Γ ; (eD M ⊗ eD N) — pair via the comonoid
     diagonal of [Γ] (= [coalg_d]) followed by the bifunctor tensor. *)
  | ne_pair G0 t1 t2 M1 M2 =>
      em_pair_mor (eD_cbv G0 t1 M1) (eD_cbv G0 t2 M2)
  (* [ne_fst M]: π₁ ∘ eD M — the comonoid counit on the second slot. *)
  | ne_fst G0 t1 t2 M0 =>
      icones_comp (em_proj1_mor (tyD_cbv t1) (tyD_cbv t2)) (eD_cbv G0 _ M0)
  (* [ne_snd M]: π₂ ∘ eD M. *)
  | ne_snd G0 t1 t2 M0 =>
      icones_comp (em_proj2_mor (tyD_cbv t1) (tyD_cbv t2)) (eD_cbv G0 _ M0)
  (* [ne_lam x M]: curry the body, then promote via the [U⊣!̃]
     adjunction [adj_psi].  The result is in [coalg_obj (tyD_cbv (tfun
     t1 t2))] = [Bang (U⟦t1⟧ ⊸ U⟦t2⟧)]; no [Tobj] wrap on [⟦t2⟧]. *)
  | ne_lam G0 _ t1 t2 body =>
      ch_mor (adj_psi (P := ctxD_cbv (drop_names G0))
                      (B := linhom_car Ar (coalg_obj (tyD_cbv t1))
                                          (coalg_obj (tyD_cbv t2)))
              (tensor_curry (eD_cbv ((_, t1) :: G0) t2 body)))
  (* [ne_app f e]:
       δ_Γ ; (eD f ⊗ eD e) ; (der ⊗ id) ; eval
     where [eval = tensor_uncurry (id : linhom A B → linhom A B)] is
     the SMCC evaluation [linhom A B ⊗ A → B]. *)
  | ne_app G0 t1 t2 Vf Va =>
      icones_comp
        (tensor_uncurry (icones_id Ar
           (linhom_car Ar (coalg_obj (tyD_cbv t1)) (coalg_obj (tyD_cbv t2)))))
        (icones_comp
          (tensor_mor (der (linhom_car Ar (coalg_obj (tyD_cbv t1))
                                          (coalg_obj (tyD_cbv t2))))
                      (icones_id Ar (coalg_obj (tyD_cbv t1))))
          (em_pair_mor (eD_cbv G0 (tfun t1 t2) Vf) (eD_cbv G0 t1 Va)))
  (* [ne_let x M K]:
       δ_Γ ; (id_Γ ⊗ eD M) ; eD K
     The diagonal of [Γ] feeds one copy through [eD M] to build the
     bound variable, and keeps the other copy as the outer context for
     [K] (whose context is [(x, t1) :: G0], interpreted as [Γ ⊗ ⟦t1⟧]). *)
  | ne_let G0 _ t1 t2 M0 K =>
      icones_comp (eD_cbv ((_, t1) :: G0) t2 K)
        (em_pair_mor (icones_id Ar (coalg_obj (ctxD_cbv (drop_names G0))))
                     (eD_cbv G0 t1 M0))
  (* [ne_sample µ]: constant icones_hom at the unit-ball measure. *)
  | ne_sample G0 mu Hmu =>
      sample_icones (ctxD_cbv (drop_names G0)) mu Hmu
  (* [ne_real r]: constant icones_hom at [δ_r] (a Dirac on the
     R-carrier of [R_obj]). *)
  | ne_real G0 r =>
      real_icones R_obj R_carrier_eq (ctxD_cbv (drop_names G0)) r
  (* [ne_score f e]: post-compose [eD e] with [score_lift f] (the
     density lift of [ppl.v]'s [score_lift]). *)
  | ne_score G0 f Hf_meas Hf_ge0 Hf_le1 e0 =>
      icones_comp
        (@score_lift R Ar R_obj R_carrier_eq R_carrier_meas
                     f Hf_meas Hf_ge0 Hf_le1)
        (eD_cbv G0 _ e0)
  (* [ne_add M N]:
       δ_Γ ; (eD M ⊗ eD N) ; add_lift
     where [add_lift : FMeas R_obj ⊗ FMeas R_obj → FMeas R_obj] is the
     §5 lax-monoidal arithmetic lift. *)
  | ne_add G0 M0 N0 =>
      icones_comp
        (@add_lift R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas)
        (em_pair_mor (eD_cbv G0 _ M0) (eD_cbv G0 _ N0))
  | ne_mul G0 M0 N0 =>
      icones_comp
        (@mul_lift R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas)
        (em_pair_mor (eD_cbv G0 _ M0) (eD_cbv G0 _ N0))
  | ne_true G0 => true_icones (ctxD_cbv (drop_names G0))
  | ne_false G0 => false_icones (ctxD_cbv (drop_names G0))
  | ne_bernoulli G0 p Hp_ge0 Hp_le1 =>
      bernoulli_icones (ctxD_cbv (drop_names G0)) p Hp_ge0 Hp_le1
  (* [ne_bernoulli_f f e]: post-compose [eD e] with [bern_lift f] (the
     value-dependent Bernoulli lift of [ppl.v::Section BernTmLift]) —
     the exact mirror of the [ne_score]/[score_lift] clause, landing
     in [bool_cone_car] instead of [cone_one_car]. *)
  | ne_bernoulli_f G0 f Hf_meas Hf_ge0 Hf_le1 e0 =>
      icones_comp
        (@bern_lift R Ar R_obj R_carrier_eq R_carrier_meas
                    f Hf_meas Hf_ge0 Hf_le1)
        (eD_cbv G0 _ e0)
  (* [ne_if b M N]:
       δ_Γ ; (id_Γ ⊗ eD b) ; braid ; uncurry (bool_case eD M eD N)
     where [bool_case] is the universal co-pairing of [bool_cone] of
     [bool_cone.v].  No [der]: the §9.7 [bool_cone_coalg] scrutinee
     lives in [bool_cone_car] directly.  See [if_icones] above. *)
  | ne_if G0 ty e M0 N0 =>
      if_icones (eD_cbv G0 ty M0) (eD_cbv G0 ty N0) (eD_cbv G0 _ e)
  (* [ne_fix s M]: the OCaml-style value-fixpoint at function types.
     Iterate [Phi_fun (coalg_d Γ) (eD_cbv body)] from [precone_zero]
     on the unit-ball ω-CPO of [linhom Γ ⟦tfun t1 t2⟧]; the supremum
     is the linhom-level recursive value.  Package as [icones_hom]
     via [linhom_icones] using [Yfix_fun_lin_norm_le1]. *)
  | ne_fix G0 _ t1 t2 body =>
      linhom_icones
        (Yfix_fun_lin (coalg_d (ctxD_cbv (drop_names G0)))
                      (eD_cbv ((_, tfun t1 t2) :: G0) (tfun t1 t2) body))
        (Yfix_fun_lin_norm_le1 _ _)
  (* [ne_fix_mr s t Hfree M]: mutual-recursion / free-coalg-type
     fixpoint.  Same Kleene operator, now with the body's denotation
     at the (possibly product) free coalgebra type [t].  Parametric
     in [Γ] and [B], so identical recipe. *)
  | ne_fix_mr G0 _ ty _ body =>
      linhom_icones
        (Yfix_fun_lin (coalg_d (ctxD_cbv (drop_names G0)))
                      (eD_cbv ((_, ty) :: G0) ty body))
        (Yfix_fun_lin_norm_le1 _ _)
  end).
Defined.

End TermInterpCBV.

Arguments eD_cbv
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G t} M.

(** ** Public-facing linhom-valued interpretation [eD]

    The clean CBV interpretation as a linear morphism in [ICones]:
    [[
       eD M : linhom_car Ar (coalg_obj (ctxD_cbv (drop_names Γ)))
                            (coalg_obj (tyD_cbv τ))
    ]]
    Built from the internal icones_hom-valued [eD_cbv] by
    [icones_to_linhom].  [eD M] is a norm-[≤1] linear, ω-continuous,
    integral-preserving map; the unit ball recovers [icones_hom]. *)

Section PublicED.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Definition eD (G : named_ctx Ar) (t : ppl_type Ar)
    (M : @named_expr R Ar R_obj G t) :
    linhom_car Ar (coalg_obj (ctxD_cbv (drop_names G)))
                  (coalg_obj (tyD_cbv t)) :=
  icones_to_linhom (@eD_cbv R Ar R_obj R_carrier_eq R_carrier_meas
                            R_to_carrier_meas G t M).

End PublicED.

Arguments eD
  {R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas G t} M.

(** ** Definitional-unfolding pack — one lemma per [eD_cbv] clause

    Regression anchors for the interpreter: each [eD_<clause>_E] lemma
    pins the EXACT clause body of [eD_cbv], so any refactor of the
    interpreter (or of the combinators it is built from) breaks loudly
    here instead of silently changing the semantics.  Because [eD_cbv]
    is a structural [Fixpoint], every clause reduces definitionally on
    its constructor and every proof is [by []].

    The pack closes with the SEMANTIC recursion-unfolding equation
    [eD_cbv_fix_unfold] / [eD_fix_unfold]: the denotation of
    [ne_fix s body] equals the body run with the fixpoint itself bound
    to the recursive variable — derived from [Yfix_fun_lin_fixpoint]
    ([theories/programs/infra/em_fix.v]). *)

Section EDUnfold.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Local Notation eD_cbv' :=
  (@eD_cbv R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).
Local Notation eD' :=
  (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _).

(** [ne_var]: pure projection from the context tensor. *)
Lemma eD_var_E (G : named_ctx Ar) (t : ppl_type Ar) (v : named_var G t) :
  eD_cbv' (ne_var v) = ch_mor (var_lookup_cbv (named_var_to_has_var v)).
Proof. by []. Qed.

(** [ne_tt]: the comonoid counit [ε_Γ]. *)
Lemma eD_tt_E (G : named_ctx Ar) :
  eD_cbv' (@ne_tt R Ar R_obj G) =
  ch_mor (em_term_mor (ctxD_cbv (drop_names G))).
Proof. by []. Qed.

(** [ne_pair]: [δ_Γ ; (⟦M⟧ ⊗ ⟦N⟧)] via [em_pair_mor]. *)
Lemma eD_pair_E (G : named_ctx Ar) (t1 t2 : ppl_type Ar)
    (M : @named_expr R Ar R_obj G t1) (N : @named_expr R Ar R_obj G t2) :
  eD_cbv' (ne_pair M N) = em_pair_mor (eD_cbv' M) (eD_cbv' N).
Proof. by []. Qed.

(** [ne_fst]: [π₁ ∘ ⟦M⟧]. *)
Lemma eD_fst_E (G : named_ctx Ar) (t1 t2 : ppl_type Ar)
    (M : @named_expr R Ar R_obj G (tprod t1 t2)) :
  eD_cbv' (ne_fst M) =
  icones_comp (em_proj1_mor (tyD_cbv t1) (tyD_cbv t2)) (eD_cbv' M).
Proof. by []. Qed.

(** [ne_snd]: [π₂ ∘ ⟦M⟧]. *)
Lemma eD_snd_E (G : named_ctx Ar) (t1 t2 : ppl_type Ar)
    (M : @named_expr R Ar R_obj G (tprod t1 t2)) :
  eD_cbv' (ne_snd M) =
  icones_comp (em_proj2_mor (tyD_cbv t1) (tyD_cbv t2)) (eD_cbv' M).
Proof. by []. Qed.

(** [ne_lam]: curry the body, promote via [adj_psi]. *)
Lemma eD_lam_E (G : named_ctx Ar) (x : string) (t1 t2 : ppl_type Ar)
    (M : @named_expr R Ar R_obj ((x, t1) :: G) t2) :
  eD_cbv' (ne_lam x M) =
  ch_mor (adj_psi (P := ctxD_cbv (drop_names G))
                  (B := linhom_car Ar (coalg_obj (tyD_cbv t1))
                                      (coalg_obj (tyD_cbv t2)))
            (tensor_curry (eD_cbv' M))).
Proof. by []. Qed.

(** [ne_app]: [δ_Γ ; (⟦F⟧ ⊗ ⟦X⟧) ; (der ⊗ id) ; eval]. *)
Lemma eD_app_E (G : named_ctx Ar) (t1 t2 : ppl_type Ar)
    (F : @named_expr R Ar R_obj G (tfun t1 t2))
    (X : @named_expr R Ar R_obj G t1) :
  eD_cbv' (ne_app F X) =
  icones_comp
    (tensor_uncurry (icones_id Ar
       (linhom_car Ar (coalg_obj (tyD_cbv t1)) (coalg_obj (tyD_cbv t2)))))
    (icones_comp
      (tensor_mor (der (linhom_car Ar (coalg_obj (tyD_cbv t1))
                                      (coalg_obj (tyD_cbv t2))))
                  (icones_id Ar (coalg_obj (tyD_cbv t1))))
      (em_pair_mor (eD_cbv' F) (eD_cbv' X))).
Proof. by []. Qed.

(** [ne_let]: [δ_Γ ; (id_Γ ⊗ ⟦M⟧) ; ⟦K⟧]. *)
Lemma eD_let_E (G : named_ctx Ar) (x : string) (t1 t2 : ppl_type Ar)
    (M : @named_expr R Ar R_obj G t1)
    (K : @named_expr R Ar R_obj ((x, t1) :: G) t2) :
  eD_cbv' (ne_let x M K) =
  icones_comp (eD_cbv' K)
    (em_pair_mor (icones_id Ar (coalg_obj (ctxD_cbv (drop_names G))))
                 (eD_cbv' M)).
Proof. by []. Qed.

(** [ne_sample]: constant [icones_hom] at the unit-ball measure. *)
Lemma eD_sample_E (G : named_ctx Ar)
    (mu : fmeas R (ar_carrier Ar R_obj))
    (Hmu : (cone_norm mu <= 1)%R) :
  eD_cbv' (@ne_sample R Ar R_obj G mu Hmu) =
  sample_icones (ctxD_cbv (drop_names G)) mu Hmu.
Proof. by []. Qed.

(** [ne_real]: constant [icones_hom] at the Dirac [δ_r]. *)
Lemma eD_real_E (G : named_ctx Ar) (r : R) :
  eD_cbv' (@ne_real R Ar R_obj G r) =
  real_icones R_obj R_carrier_eq (ctxD_cbv (drop_names G)) r.
Proof. by []. Qed.

(** [ne_score]: post-compose with the density lift [score_lift]. *)
Lemma eD_score_E (G : named_ctx Ar) (f : R -> R)
    (Hf_meas : measurable_fun [set: R] f)
    (Hf_ge0 : forall r : R, (0 <= f r)%R)
    (Hf_le1 : forall r : R, (f r <= 1)%R)
    (e : @named_expr R Ar R_obj G (tR R_obj)) :
  eD_cbv' (ne_score f Hf_meas Hf_ge0 Hf_le1 e) =
  icones_comp
    (@score_lift R Ar R_obj R_carrier_eq R_carrier_meas
                 f Hf_meas Hf_ge0 Hf_le1)
    (eD_cbv' e).
Proof. by []. Qed.

(** [ne_add]: [δ_Γ ; (⟦M⟧ ⊗ ⟦N⟧) ; add_lift]. *)
Lemma eD_add_E (G : named_ctx Ar)
    (M N : @named_expr R Ar R_obj G (tR R_obj)) :
  eD_cbv' (ne_add M N) =
  icones_comp
    (@add_lift R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas)
    (em_pair_mor (eD_cbv' M) (eD_cbv' N)).
Proof. by []. Qed.

(** [ne_mul]: [δ_Γ ; (⟦M⟧ ⊗ ⟦N⟧) ; mul_lift]. *)
Lemma eD_mul_E (G : named_ctx Ar)
    (M N : @named_expr R Ar R_obj G (tR R_obj)) :
  eD_cbv' (ne_mul M N) =
  icones_comp
    (@mul_lift R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas)
    (em_pair_mor (eD_cbv' M) (eD_cbv' N)).
Proof. by []. Qed.

(** [ne_true]: constant at [bool_dirac_true]. *)
Lemma eD_true_E (G : named_ctx Ar) :
  eD_cbv' (@ne_true R Ar R_obj G) =
  true_icones (ctxD_cbv (drop_names G)).
Proof. by []. Qed.

(** [ne_false]: constant at [bool_dirac_false]. *)
Lemma eD_false_E (G : named_ctx Ar) :
  eD_cbv' (@ne_false R Ar R_obj G) =
  false_icones (ctxD_cbv (drop_names G)).
Proof. by []. Qed.

(** [ne_bernoulli]: constant at the sub-probability [(p, 1-p)]. *)
Lemma eD_bernoulli_E (G : named_ctx Ar) (p : R)
    (Hp_ge0 : (0 <= p)%R) (Hp_le1 : (p <= 1)%R) :
  eD_cbv' (@ne_bernoulli R Ar R_obj G p Hp_ge0 Hp_le1) =
  bernoulli_icones (ctxD_cbv (drop_names G)) p Hp_ge0 Hp_le1.
Proof. by []. Qed.

(** [ne_bernoulli_f]: post-compose with the value-dependent Bernoulli
    lift [bern_lift] — the [tbool]-valued mirror of [eD_score_E]. *)
Lemma eD_bernoulli_f_E (G : named_ctx Ar) (f : R -> R)
    (Hf_meas : measurable_fun [set: R] f)
    (Hf_ge0 : forall r : R, (0 <= f r)%R)
    (Hf_le1 : forall r : R, (f r <= 1)%R)
    (e : @named_expr R Ar R_obj G (tR R_obj)) :
  eD_cbv' (ne_bernoulli_f f Hf_meas Hf_ge0 Hf_le1 e) =
  icones_comp
    (@bern_lift R Ar R_obj R_carrier_eq R_carrier_meas
                f Hf_meas Hf_ge0 Hf_le1)
    (eD_cbv' e).
Proof. by []. Qed.

(** [ne_if]: dispatch via [if_icones] (the [bool_case] co-pairing). *)
Lemma eD_if_E (G : named_ctx Ar) (t : ppl_type Ar)
    (e : @named_expr R Ar R_obj G tbool)
    (M N : @named_expr R Ar R_obj G t) :
  eD_cbv' (ne_if t e M N) =
  if_icones (eD_cbv' M) (eD_cbv' N) (eD_cbv' e).
Proof. by []. Qed.

(** [ne_fix]: the Kleene value-fixpoint [Yfix_fun_lin], packaged as an
    [icones_hom] via [linhom_icones]. *)
Lemma eD_fix_E (G : named_ctx Ar) (s : string) (t1 t2 : ppl_type Ar)
    (M : @named_expr R Ar R_obj ((s, tfun t1 t2) :: G) (tfun t1 t2)) :
  eD_cbv' (ne_fix s M) =
  linhom_icones
    (Yfix_fun_lin (coalg_d (ctxD_cbv (drop_names G))) (eD_cbv' M))
    (Yfix_fun_lin_norm_le1 _ _).
Proof. by []. Qed.

(** [ne_fix_mr]: the same operator at a free-coalgebra body type. *)
Lemma eD_fix_mr_E (G : named_ctx Ar) (s : string) (t : ppl_type Ar)
    (Hfree : is_free_coalg_type t)
    (M : @named_expr R Ar R_obj ((s, t) :: G) t) :
  eD_cbv' (ne_fix_mr s t Hfree M) =
  linhom_icones
    (Yfix_fun_lin (coalg_d (ctxD_cbv (drop_names G))) (eD_cbv' M))
    (Yfix_fun_lin_norm_le1 _ _).
Proof. by []. Qed.

(** ** The recursion-unfolding equation

    [⟦fix s. body⟧ = ⟦body⟧ ∘ ⟨id_Γ, ⟦fix s. body⟧⟩]: the fixpoint
    denotation equals the body run with the fixpoint itself bound to
    the recursive variable.  Strong (icones_hom-level) form first;
    derived from [Yfix_fun_lin_fixpoint], whose Kleene step
    [Phi_fun diag M prev = M ∘ (id_Γ ⊗ prev) ∘ δ_Γ] is exactly the
    [em_pair_mor]-composite on the right-hand side. *)
Lemma eD_cbv_fix_unfold (G : named_ctx Ar) (s : string)
    (t1 t2 : ppl_type Ar)
    (body : @named_expr R Ar R_obj ((s, tfun t1 t2) :: G) (tfun t1 t2)) :
  eD_cbv' (ne_fix s body) =
  icones_comp (eD_cbv' body)
    (em_pair_mor (icones_id Ar (coalg_obj (ctxD_cbv (drop_names G))))
                 (eD_cbv' (ne_fix s body))).
Proof.
pose diag := coalg_d (ctxD_cbv (drop_names G)).
pose M : icones_hom Ar
    (tensor Ar (coalg_obj (ctxD_cbv (drop_names G)))
               (coalg_obj (tyD_cbv (tfun t1 t2))))
    (coalg_obj (tyD_cbv (tfun t1 t2))) := eD_cbv' body.
(* Bridge the two (pointwise-identical) [linhom_icones] packagings:
   [em_fix.v]'s [Phi_fun_safe] uses [tensor_hom_iso.v]'s, the [ne_fix]
   clause uses [seely.v]'s; their integral-preservation proofs are
   distinct [Qed] constants, so the records are only propositionally
   equal — via [icones_hom_eq]. *)
have liE (Hb : cone_norm (Yfix_fun_lin diag M) <= 1) :
    Icones_tensor_hom_iso.linhom_icones (Yfix_fun_lin diag M) Hb =
    linhom_icones (Yfix_fun_lin diag M) (Yfix_fun_lin_norm_le1 diag M).
  by apply: icones_hom_eq.
apply: icones_hom_eq => gam.
rewrite -[X in X = _]/(linhom_fun (Yfix_fun_lin diag M) gam).
rewrite -(Yfix_fun_lin_fixpoint diag M).
rewrite (Phi_fun_unit diag M _ (Yfix_fun_lin_norm_le1 diag M)).
by rewrite /Phi_fun_safe liE.
Qed.

(** The same equation at the public linhom level. *)
Lemma eD_fix_unfold (G : named_ctx Ar) (s : string) (t1 t2 : ppl_type Ar)
    (body : @named_expr R Ar R_obj ((s, tfun t1 t2) :: G) (tfun t1 t2)) :
  eD' (ne_fix s body) =
  icones_to_linhom
    (icones_comp (eD_cbv' body)
       (em_pair_mor (icones_id Ar (coalg_obj (ctxD_cbv (drop_names G))))
                    (eD_cbv' (ne_fix s body)))).
Proof.
by rewrite /eD; congr icones_to_linhom; exact: eD_cbv_fix_unfold.
Qed.

End EDUnfold.
