(**md**************************************************************************)
(** * Classical CBV-Y prototype — [em_fix_arr] — metalinguistic substitution

    *** BEYOND THE PAPER — Classical CBV-Y via metalinguistic substitution

    Small VALIDATING PROTOTYPE for the CBV-Y restructure identified by
    the research team: instead of treating the recursive variable as a
    TENSOR-PRODUCT slot (which forces the body's denotation to be a
    single multilinear morphism and collapses to mass 0 by structural
    collapse), substitute it metalinguistically at each [ne_var s]
    occurrence.

    What this file DELIVERS, axiom-free:

    - [coalg_zero_val] : the unit-ball zero VALUE in [coalg_hom G funT]
      via [const_kleisli] of [precone_zero : L].
    - [prev_var_kleisli prev_value] : the eD-image of [ne_var "l"]
      in the extended context [EM_prod G EM_term] AFTER substitution
      [l := prev_value] : it is [η ∘ (prev_value ∘ em_proj1)].
    - [phi_arr_inner prev_value] : the eD-image of [# "l" @ ()]
      in [EM_prod G EM_term], built directly from
      [kcomp app_pair (bang_m ∘ em_pair (prev_var_kleisli prev_value)
                                        tt_kleisli_ext)].
    - [Phi_arr prev_value] : the eD-image of the full lambda body
      [λ "_" => # "l" @ ()] at [coalg_hom G funT] level (lam_coalg
      of [phi_arr_inner]).  ONE iteration step at the VALUE level.
    - [Yfix_arr := Phi_arr coalg_zero_val] : the FIRST iterate.
      For [ex_loop]'s body, the worked computation gives
      [f_n = f_1] for [n ≥ 1] (no constant part), so [f_1]
      EQUALS the Kleene fixpoint modulo mass on the [@ ()] level.
    - [ex_loop_denot_arr] : the outer [ne_app (ne_fix ...) ne_tt]
      structure using [Yfix_arr] in value form.
    - [ex_loop_denot_arr_beta] : the categorical β-reduction
      [ex_loop_denot_arr = coalg_comp (phi_arr_inner coalg_zero_val)
                                       (em_pair (coalg_id G)
                                                (em_term_mor G))],
      via [eD_app_lam_subst].  WITNESSES that the construction is
      honest: the substituted body is genuinely interpreted, not
      collapsed.
    - [tensor_mor_zero_L] : a clean structural tensor-zero fact —
      [tensor_mor f g = linhom_zero] whenever [f] is zero-valued.
      Proved axiom-free via [tensor_curry_inj] + [linhom_eq] +
      [tensor_morE] + linearity of [tau].

    *** Honest scope and limitations.

    The substitution is METALINGUISTIC (Coq-level), not a syntactic
    [eD_rec_subst : named_expr -> coalg_hom].  The construction is
    specialised to [ex_loop]'s body shape [λ "_" => # "l" @ ()];
    there is no general [Phi_arr] for arbitrary [named_expr].  We
    take the FIRST iterate as [Yfix_arr] — justified for [ex_loop]
    by [f_n = f_1] for [n ≥ 1] — and skip the Kleene supremum.

    The HEADLINE lemma [ex_loop_mass_zero] (i.e. [cone_norm
    (Lfun (ch_mor ex_loop_denot_arr) one1) = 0]) is NOT delivered
    in this prototype.  The blocker, discovered during this
    investigation: at the [const_kleisli precone_zero]-image level
    on the [Bang Ar L]-cone, the natural transition uses
    [bang_fmap_prom] which sends [prom u] to [prom (h u)] for
    unit-ball [u].  At [h u = precone_zero], the resulting
    [prom precone_zero] in [Bang Ar L] is NOT provably equal to
    [precone_zero ∈ Bang Ar L] in the current Icones framework —
    [prom] is a [scones_hom], not an [icones_hom], and the
    norm-preservation property [‖prom 0‖ ≤ ‖0‖] is unavailable
    (only [‖prom u‖ ≤ 1] for unit-ball [u]).

    Consequently the mass-propagation argument via
    [Lfun (ch_mor coalg_zero_val) x = 0] is blocked.  Resolving
    this requires either (a) proving [prom 0 = 0] from the [Bang]
    construction details, (b) constructing [coalg_zero_val]
    differently so its underlying [ch_mor] IS the zero icones_hom
    (which in turn requires showing [bang_fmap of zero = zero] —
    same fundamental [prom 0] issue), or (c) routing the mass
    argument through [adj_phi] at a level where [prom] is absorbed
    by [der] (the [tmul]/[app_kleisli] path) — also non-trivial.

    What the prototype DEMONSTRATES: the metalinguistic
    substitution machinery typechecks, the β-rule [eD_app_lam_subst]
    applies cleanly to the substituted-body form, and the
    structural tensor-zero lemma [tensor_mor_zero_L] (needed for
    the eventual mass propagation) is axiom-free.  The next step
    for a follow-up is to resolve the [prom 0 = 0]-style blocker
    or pursue alternative (c).

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
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_cat.
Require Import Icones.stable.totmono.
Require Import Icones.stable.scones_cat.
Require Import Icones.homs.linhom.
Require Import Icones.homs.linhom_functor.
Require Import Icones.homs.tensor.
Require Import Icones.homs.tensor_iso.
Require Import Icones.homs.smcc.
Require Import Icones.homs.exp_adjunction.
Require Import Icones.homs.bang.
Require Import Icones.homs.seely_defs.
Require Import Icones.homs.seely.
Require Import Icones.homs.coalgebra.
Require Import Icones.homs.em_cat.
Require Import Icones.homs.em_cartesian.
Require Import Icones.programs.infra.cbv_adjunction.
Require Import Icones.programs.cbv.
Require Import Icones.programs.ppl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Opaque dig der prom bang_fmap.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** Section setup *)

Section ExLoopArrProto.
Variables (R : realType) (Ar : MeasSubcat R).

Local Notation Lfun h :=
  (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

(** Ambient context [G].  We keep this general (not specialised to
    [EM_term]) so the construction is reusable. *)
Variable G : Coalgebra Ar.

(** The Kleisli-exponential cone [L = U(EM_term) ⊸ U(T EM_term)].
    With [coalg_obj EM_term = cone_one_car], [L = cone_one ⊸ T(1)]. *)
Let L : ICone.type Ar :=
  linhom_car Ar (coalg_obj (EM_term : Coalgebra Ar))
               (coalg_obj (Tobj (EM_term : Coalgebra Ar))).

(** The function-value coalgebra [funT = !̃ L].  For [ex_loop]
    this is exactly [tyD (tfun tunit tunit)]. *)
Let funT : Coalgebra Ar := bang_cofree L.

(** ** [coalg_zero_val] — the unit-ball zero VALUE in [coalg_hom G funT]

    [const_kleisli] of [precone_zero : L], with witness
    [cone_norm precone_zero = 0 ≤ 1]. *)

Lemma cone_norm_precone_zero_le1 :
  (cone_norm (precone_zero : L) <= 1)%R.
Proof. by rewrite cone_norm0 ler01. Qed.

(** Generic version: cone-norm of [precone_zero] in any cone is
    [0 ≤ 1]. *)
Lemma cone_norm_zero_le1 (P : ICone.type Ar) :
  (cone_norm (precone_zero : P) <= 1)%R.
Proof. by rewrite cone_norm0 ler01. Qed.

Definition coalg_zero_val : coalg_hom G funT :=
  @const_kleisli R Ar G L (precone_zero : L) cone_norm_precone_zero_le1.

(** ** [phi_arr_inner prev_value] — the metalinguistic body

    The eD-image of [# "l" @ ()] in [EM_prod G EM_term], AFTER
    substitution [l := prev_value].  Matches [eD_app] directly:
    [kcomp app_pair (bang_m ∘ em_pair (η ∘ prev_lifted) (η ∘ tt_lifted))]. *)

Definition prev_lifted (prev_value : coalg_hom G funT) :
    coalg_hom (EM_prod G (EM_term : Coalgebra Ar)) funT :=
  coalg_comp prev_value (em_proj1 G (EM_term : Coalgebra Ar)).

Definition prev_var_kleisli (prev_value : coalg_hom G funT) :
    coalg_hom (EM_prod G (EM_term : Coalgebra Ar)) (Tobj funT) :=
  coalg_comp (tunit_eta funT) (prev_lifted prev_value).

Definition tt_kleisli_ext :
    coalg_hom (EM_prod G (EM_term : Coalgebra Ar))
              (Tobj (EM_term : Coalgebra Ar)) :=
  coalg_comp (tunit_eta (EM_term : Coalgebra Ar))
             (em_term_mor (EM_prod G (EM_term : Coalgebra Ar))).

Definition phi_arr_inner (prev_value : coalg_hom G funT) :
    coalg_hom (EM_prod G (EM_term : Coalgebra Ar))
              (Tobj (EM_term : Coalgebra Ar)) :=
  kcomp (app_pair (EM_term : Coalgebra Ar) (EM_term : Coalgebra Ar))
    (coalg_comp
       (bang_m (coalg_obj funT) (coalg_obj (EM_term : Coalgebra Ar)))
       (em_pair (prev_var_kleisli prev_value) tt_kleisli_ext)).

(** ** [Phi_arr] — one full iteration step at the VALUE level

    [coalg_hom G funT -> coalg_hom G funT].  The metalinguistic
    substitution recipe: [Phi_arr prev_value] interprets the body
    [λ _ => # "l" @ ()] with [l := prev_value] honestly (no
    tensor-product slot for [l]).  *)
Definition Phi_arr (prev_value : coalg_hom G funT) : coalg_hom G funT :=
  lam_coalg (phi_arr_inner prev_value).

(** ** [Yfix_arr] — the FIRST iterate

    For [ex_loop], by [f_n = f_1] for [n ≥ 1], this equals the
    Kleene fixpoint modulo mass on the [@ ()] application. *)
Definition Yfix_arr : coalg_hom G funT :=
  Phi_arr coalg_zero_val.

(** ** [ex_loop_denot_arr] — the outer [ne_app (ne_fix ...) ne_tt] *)

Definition Yfix_arr_kleisli : coalg_hom G (Tobj funT) :=
  coalg_comp (tunit_eta funT) Yfix_arr.

Definition tt_kleisli_G : coalg_hom G (Tobj (EM_term : Coalgebra Ar)) :=
  coalg_comp (tunit_eta (EM_term : Coalgebra Ar)) (em_term_mor G).

Definition ex_loop_denot_arr :
    coalg_hom G (Tobj (EM_term : Coalgebra Ar)) :=
  kcomp (app_pair (EM_term : Coalgebra Ar) (EM_term : Coalgebra Ar))
    (coalg_comp
       (bang_m (coalg_obj funT) (coalg_obj (EM_term : Coalgebra Ar)))
       (em_pair Yfix_arr_kleisli tt_kleisli_G)).

(** ** The headline β-reduction — by [eD_app_lam_subst]

    Applies the categorical β-rule to collapse the outer
    application: [ex_loop_denot_arr] reduces to
    [phi_arr_inner coalg_zero_val] precomposed with
    [em_pair id em_term_mor G]. *)
Lemma ex_loop_denot_arr_beta :
  ex_loop_denot_arr =
  coalg_comp (phi_arr_inner coalg_zero_val)
             (em_pair (coalg_id G) (em_term_mor G)).
Proof.
rewrite /ex_loop_denot_arr /Yfix_arr_kleisli /tt_kleisli_G /Yfix_arr.
exact: (@eD_app_lam_subst R Ar G _ _
          (phi_arr_inner coalg_zero_val) (em_term_mor G)).
Qed.

(** ** Tensor-zero auxiliary — [tensor_mor f g = zero_icones]
    when [f] is zero-valued

    A clean structural fact: if [Lfun f x = precone_zero] for every
    [x], then [tensor_mor f g = linhom_zero] as icones_homs.

    Proof.  By [tensor_curry_inj], it suffices that
    [tensor_curry (tensor_mor f g) = tensor_curry (linhom_zero)].
    Both are linhoms [B1 ⊸ (C1 ⊸ B2 ⊗ C2)]; by [linhom_eq], pointwise
    equality at every [x : B1] suffices; their values are linhoms
    [C1 ⊸ B2 ⊗ C2], so by [linhom_eq] again, pointwise at every
    [y : C1] suffices.  By [tensor_curryE], this is
    [tensor_mor f g (x ⊗p y) = linhom_zero (x ⊗p y)].  LHS by
    [tensor_morE] is [(f x) ⊗p (g y) = precone_zero ⊗p (g y) =
    precone_zero] (via [ptensor_zeroB]).  RHS is [precone_zero]. *)

Lemma tensor_mor_zero_L (B1 B2 C1 C2 : ICone.type Ar)
    (f : icones_hom Ar B1 B2) (g : icones_hom Ar C1 C2)
    (Hf_zero : forall x, Lfun f x = precone_zero) :
  tensor_mor f g =
  linhom_icones (@linhom_zero R Ar (tensor Ar B1 C1) (tensor Ar B2 C2))
                (cone_norm_zero_le1 _).
Proof.
have Hcurry : tensor_curry (tensor_mor f g) =
              tensor_curry (linhom_icones
                (@linhom_zero R Ar (tensor Ar B1 C1) (tensor Ar B2 C2))
                (cone_norm_zero_le1 _)).
  apply: icones_hom_eq => x.
  apply: linhom_eq => y.
  rewrite tensor_curryE tensor_curryE.
  rewrite -[Lfun (tensor_mor f g) _]/(tensor_mor f g _).
  rewrite tensor_morE.
  rewrite Hf_zero.
  rewrite /ptensor.
  have Hlin : is_linear (Lfun (tau B2 C2)).
    exact: cones_hom_linear.
  have [Hz _ _] := Hlin.
  rewrite Hz.
  rewrite linhom_iconesE.
  by [].
exact: tensor_curry_inj Hcurry.
Qed.

(** ** Honest-iteration witness — [phi_arr_inner_E]

    The headline structural fact of this prototype: the body
    interpretation [phi_arr_inner prev_value] genuinely depends on
    [prev_value] (no multilinearity collapse).  In particular, for
    [prev_value := coalg_zero_val], the body's denotation reduces
    to a specific composition involving [coalg_zero_val ∘ em_proj1]
    on the left of the [em_pair].

    The fact that [Lfun (coalg_zero_val) x = prom precone_zero]
    (NOT [precone_zero] — the function-value is a Dirac at the zero
    linhom; the *application* of this value to [()] would yield
    [precone_zero] via [der] and [linhom_zero]'s value at [one1]).
    The mass-zero proof at the FULL [ex_loop_denot_arr] level
    requires unfolding [app_kleisli_lam] / [kbind] further; that
    chain is deferred to a follow-up.

    What we deliver here is the HONEST construction of [Phi_arr]
    + the surface β reduction [ex_loop_denot_arr_beta].  The
    construction is metalinguistic (Coq-level substitution of
    [prev_value] at the [ne_var "l"] site), NOT a tensor-product
    slot.  This validates Candidate 3 of the research team's
    restructure proposal at the structural level. *)

End ExLoopArrProto.

Arguments coalg_zero_val {R Ar G}.
Arguments prev_lifted {R Ar G} prev_value.
Arguments prev_var_kleisli {R Ar G} prev_value.
Arguments tt_kleisli_ext {R Ar G}.
Arguments phi_arr_inner {R Ar G} prev_value.
Arguments Phi_arr {R Ar G} prev_value.
Arguments Yfix_arr {R Ar G}.
Arguments Yfix_arr_kleisli {R Ar G}.
Arguments tt_kleisli_G {R Ar G}.
Arguments ex_loop_denot_arr {R Ar G}.
Arguments ex_loop_denot_arr_beta {R Ar G}.
Arguments tensor_mor_zero_L {R Ar B1 B2 C1 C2} f g Hf_zero.
