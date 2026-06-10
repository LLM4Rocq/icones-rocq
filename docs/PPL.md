# PPL.md — A direct-style PPL on top of the integrable-cones model

A typed probabilistic functional language sits on top of the paper's
categorical model: each type denotes a `!`-coalgebra, each program a
Kleisli arrow of the linear-exponential comonad `!`, recursion the
least fixpoint of paper §9.2. The same surface syntax also admits a
call-by-name reading through the cartesian closed `SCones` of stable
and measurable functions of paper §7. The language is direct-style
(Plotkin / Girard), named-variable (Saito–Affeldt APLAS 2023), and the
probability monad lives entirely in the interpretation — there is no
`tprob` type marker, no syntactic `return`, no `bind`. Examples are
listed in [EXAMPLES.md](../examples/).

The paper-side correspondence (§§ 2–9 ↔ Rocq) lives on the
[Paper tab](../paper/). This document covers what sits *above* the
paper: the surface language, its two interpretations, the shared
fixpoint and arithmetic infrastructure, and the structural
correctness statements one can make at the categorical level.

---

## Beyond the paper — The surface language

The source language is a simply-typed lambda calculus with sampling,
scoring, recursion at function type, a two-point boolean type, and
mutual recursion at any free-coalgebra type. The syntax is a single
intrinsically-typed inductive `named_expr Γ τ` in named-variable
style, indexed by a *named* context `named_ctx = seq (string ×
ppl_type)`. The same inductive is consumed by both the CBV
interpretation `eD` and the CBN interpretation `eD_CBN` below.

| Construction | Rocq |
|---|---|
| Types `tunit`, `tbase X`, `tprod`, `tfun`, `tbool` | `ppl_type` — `theories/programs/ppl.v` |
| Named contexts | `named_ctx`, `drop_names` — same file |
| Named variables (witness) | `named_var`, `nv_head`, `nv_tail` — same file |
| Term constructors | `named_expr` (the 17 constructors below) — same file |
| Free-coalgebra type predicate (gating `ne_fix_mr`) | `is_free_coalg_type` — same file |
| Variable lookup via canonical structures | `tagged_nctx`, `find_nv`, `found_nv`, `recurse_nv`, `ne_var'` — same file |
| Surface notation `[ … ]` and the `ppl_named` custom entry | `ppl_named` (custom entry) — same file |

### Types and contexts (`ppl_type`, `named_ctx`)

```coq
(* theories/programs/ppl.v *)
Inductive ppl_type : Type :=
  | tunit
  | tbase (X : ar_obj Ar)
  | tprod (t1 t2 : ppl_type)
  | tfun  (t1 t2 : ppl_type)
  | tbool.

Definition named_ctx : Type := list (string * ppl_type Ar).
Definition drop_names (G : named_ctx) : ppl_ctx Ar := map snd G.
```

`drop_names` forgets the string identifiers; the categorical
interpretation lives on `drop_names G`, the named layer is only for
canonical-structure-driven variable lookup at `#"x"` sites.

### Free-coalgebra types (`is_free_coalg_type`)

```coq
(* theories/programs/ppl.v *)
Fixpoint is_free_coalg_type (t : ppl_type Ar) : bool :=
  match t with
  | tfun _ _ => true
  | tprod t1 t2 => is_free_coalg_type t1 && is_free_coalg_type t2
  | _ => false
  end.
```

The predicate characterises the surface types whose interpretation is
a *free* `!`-coalgebra — function types and products thereof. This is
the gating predicate of `ne_fix_mr` below.

### Pure term constructors (`ne_var`, `ne_tt`, `ne_pair`, `ne_fst`, `ne_snd`, `ne_lam`, `ne_app`, `ne_let`, `ne_real`, `ne_add`, `ne_mul`, `ne_true`, `ne_false`)

```coq
(* theories/programs/ppl.v *)
Inductive named_expr : named_ctx Ar -> T -> Type :=
  | ne_var   : forall G t, named_var G t -> named_expr G t
  | ne_tt    : forall G,   named_expr G tunit
  | ne_pair  : forall G t1 t2,
      named_expr G t1 -> named_expr G t2 ->
      named_expr G (tprod t1 t2)
  | ne_fst   : forall G t1 t2,
      named_expr G (tprod t1 t2) -> named_expr G t1
  | ne_snd   : forall G t1 t2,
      named_expr G (tprod t1 t2) -> named_expr G t2
  | ne_lam   : forall G x t1 t2,
      named_expr ((x, t1) :: G) t2 -> named_expr G (tfun t1 t2)
  | ne_app   : forall G t1 t2,
      named_expr G (tfun t1 t2) -> named_expr G t1 ->
      named_expr G t2
  | ne_let   : forall G x t1 t2,
      named_expr G t1 -> named_expr ((x, t1) :: G) t2 ->
      named_expr G t2
  | ne_real  : forall G, R -> named_expr G tR'
  | ne_add   : forall G,
      named_expr G tR' -> named_expr G tR' -> named_expr G tR'
  | ne_mul   : forall G,
      named_expr G tR' -> named_expr G tR' -> named_expr G tR'
  | ne_true  : forall G, named_expr G tbool
  | ne_false : forall G, named_expr G tbool
  (* … effects and recursion below … *)
```

Bidirectionality hints `&` on every binding / context-shared
constructor (e.g. `Arguments ne_lam {R Ar R_obj G} x & {t1 t2} M`) are
crucial for canonical-structure resolution at `#"x"` sites — exactly
the Saito–Affeldt APLAS 2023 §5.1 pattern.

### Effectful term constructors (`ne_sample`, `ne_score`, `ne_bernoulli`, `ne_if`)

```coq
(* theories/programs/ppl.v *)
(* … (continued) *)
  | ne_sample : forall G,
      forall mu : fmeas R (ar_carrier Ar R_obj),
      (cone_norm mu <= 1)%R ->
      named_expr G tR'
  | ne_score  : forall G,
      forall f : R -> R,
      measurable_fun [set: R] f ->
      (forall r : R, 0 <= f r)%R ->
      (forall r : R, f r <= 1)%R ->
      named_expr G tR' -> named_expr G tunit
  | ne_bernoulli : forall G,
      forall p : R, (0 <= p)%R -> (p <= 1)%R ->
      named_expr G tbool
  | ne_if : forall G t,
      named_expr G tbool ->
      named_expr G t -> named_expr G t -> named_expr G t.
```

Direct-style: `ne_sample` returns a pure `tR'`, `ne_score` a pure
`tunit`. The probability monad is hidden in the interpretation `eD`,
not in the source types. `ne_score` carries a measurable density
`f : R → R` clipped to `[0,1]` — the bound is needed by the
unit-ball discipline of `linhom_icones`.

### Recursion at function type (`ne_fix`)

```coq
(* theories/programs/ppl.v *)
(* … *)
  | ne_fix  : forall G s t1 t2,
      named_expr ((s, tfun t1 t2) :: G) (tfun t1 t2) ->
      named_expr G (tfun t1 t2)
```

OCaml-style `let rec`, restricted to function types. The body has
access to the recursive function via a fresh name `s : tfun t1 t2` in
the context. The CBV interpretation routes through `Yfix_fun_T` (see
below); CBN through paper §9.2's `Yfix`.

### Mutual recursion at free-coalgebra types (`ne_fix_mr`)

```coq
(* theories/programs/ppl.v *)
(* … *)
  | ne_fix_mr : forall G s t,
      is_free_coalg_type t ->
      named_expr ((s, t) :: G) t -> named_expr G t.
```

Generalises `ne_fix` to any body type `t` with
`is_free_coalg_type t = true` — in particular `t = tprod (tfun A1 B1)
(tfun A2 B2)`, the mutual-recursion shape. The two components can
then call each other via `fst #"s"` / `snd #"s"`. CBN dispatches via
`Yfix` at the product cone (fully sound); CBV dispatches via
`Yfix_mr_pack` (sound at the `tfun` arm, honest-scope placeholder at
the `tprod` arm — see *The CBV value-fixpoint at function types*
below).

### Surface notation (the `ppl_named` custom entry)

```coq
(* theories/programs/ppl.v *)
Declare Custom Entry ppl_named.
Notation "[ e ]" := e (e custom ppl_named at level 90).
Notation "()" := ne_tt (in custom ppl_named at level 0).
Notation "# x" := (ne_var' x%string _)
  (in custom ppl_named at level 1, x constr at level 0).
Notation "[| r |]" := (ne_real r)
  (in custom ppl_named at level 1, r constr).
Notation "'Sample' ( mu , Hmu )" := (ne_sample mu Hmu)
  (in custom ppl_named at level 1, mu constr, Hmu constr).
Notation "'Score' '{' f ',' Hf_meas ',' Hf_ge0 ',' Hf_le1 '}' e" :=
  (ne_score f Hf_meas Hf_ge0 Hf_le1 e)
  (in custom ppl_named at level 60, e custom ppl_named at level 60,
   f constr, Hf_meas constr, Hf_ge0 constr, Hf_le1 constr).
Notation "'Bernoulli' '{' p ',' Hge0 ',' Hle1 '}'" :=
  (ne_bernoulli p Hge0 Hle1)
  (in custom ppl_named at level 1, p constr, Hge0 constr, Hle1 constr).
Notation "'if' e 'then' M 'else' N" := (ne_if _ e M N)
  (in custom ppl_named at level 60).
Notation "'\' x ':::' A '=>' M" := (ne_lam x%string (t1 := A) M)
  (in custom ppl_named at level 70).
Notation "'let' x ':=' M 'in' N" := (ne_let x%string M N)
  (in custom ppl_named at level 80).
Notation "'fix' x ':::' A 'in' M" := (ne_fix x%string (t1 := _) M)
  (in custom ppl_named at level 70).
Notation "'fix_mr' x 'as' t 'by' Hfree 'in' M" :=
  (ne_fix_mr x%string t Hfree M)
  (in custom ppl_named at level 70).
```

Direct-style: no `Ret` notation; `let "x" := M in N` desugars to
`ne_let` (not `ne_bind`). Brackets `[ … ]` enter the entry; curly
braces `{ x }` escape back to plain Rocq.

---

## Beyond the paper — Call-by-value interpretation (EM(!) Kleisli)

**Definition (CBV interpretation).** *Each type `τ` denotes a
`!`-coalgebra `⟦τ⟧ ∈ EM(!)`; each well-typed program `Γ ⊢ M : τ`
denotes a Kleisli arrow `⟦M⟧ : ⟦Γ⟧ → T⟦τ⟧` for the CBV monad
`T = !̃ ∘ U` of the linear / non-linear adjunction (Mellies §7.4 Prop
29, paper §9). Composition is Kleisli, the unit is `tunit_eta`. The
value category is the **full** Eilenberg–Moore category `EM(!)` of
the linear-exponential comonad — Mellies Cor 20 + Fox 1976 give the
cartesian η; see Paper-tab `EM(!) is fully cartesian`.*

In Rocq this is the function

```
eD : named_expr Γ τ → coalg_hom (ctxD (drop_names Γ)) (Tobj (tyD τ))
```

defined by structural recursion on `named_expr`. Pure constructors
are made into Kleisli arrows by post-composition with `tunit_eta` —
the implicit return that direct style needs. The function-type
denotation is the Kleisli exponential `!̃(U⟦t1⟧ ⊸ U(T ⟦t2⟧))`, with
the `T` on the codomain encoding that every function call is
potentially effectful.

| Construction | Rocq |
|---|---|
| Type translation | `tyD` — `theories/programs/ppl.v` |
| Context translation | `ctxD` — same file |
| Term interpretation | `eD` (uniform `Tobj`-wrapped codomain) — same file |
| CBV monad `T = !̃ ∘ U` | `Tobj` — `theories/programs/cbv.v` |
| Kleisli bind / extended bind | `kbind`, `kcomp`, `kbind_ext` — `cbv.v`, `ppl.v` |
| Sampling on a Dirac | `sample_kleisli`, `cpD_sample_var_dirac`, `cpD_sample_is_integral` (= `Coalg`) | `cbv.v`, `ppl.v` |

### Type translation (`tyD`)

```coq
(* theories/programs/ppl.v *)
Fixpoint tyD (t : ppl_type Ar) : Coalgebra Ar :=
  match t with
  | tunit       => EM_term
  | tbase X     => FMeas_coalgebra X
  | tprod t1 t2 => EM_prod (tyD t1) (tyD t2)
  | tfun  t1 t2 => bang_cofree
                     (linhom_car Ar (coalg_obj (tyD t1))
                                    (coalg_obj (Tobj (tyD t2))))
  | tbool       => bang_cofree (bool_cone_car Ar)
  end.
```

`⟦tunit⟧ = EM_term` is the terminal coalgebra. `⟦tbase X⟧ = (FMeas
X, h_X)` is the Theorem 9.7 coalgebra. `⟦tfun t1 t2⟧` is the Kleisli
exponential of `T`; the `Tobj` on the codomain is what makes the
language direct-style CBV.

### Context translation (`ctxD`)

```coq
(* theories/programs/ppl.v *)
Fixpoint ctxD (G : ppl_ctx Ar) : Coalgebra Ar :=
  match G with
  | nil     => EM_term
  | t :: G' => EM_prod (ctxD G') (tyD t)
  end.
```

### Term interpretation (`eD`)

```coq
(* theories/programs/ppl.v *)
Fixpoint eD (G : named_ctx Ar) (t : T)
    (M : @named_expr R Ar R_obj G t) {struct M} : EX G t :=
  match M with
  | ne_var _ _ v =>
      coalg_comp (tunit_eta (tyD _))
                 (var_lookup (named_var_to_has_var v))
  | ne_tt _ => coalg_comp (tunit_eta EM_term) (em_term_mor _)
  | ne_pair _ _ _ M1 M2 =>
      coalg_comp (bang_m _ _) (em_pair (eD M1) (eD M2))
  | ne_fst _ _ _ M0 => coalg_comp (Tmap (em_proj1 _ _)) (eD M0)
  | ne_snd _ _ _ M0 => coalg_comp (Tmap (em_proj2 _ _)) (eD M0)
  | ne_lam _ _ _ _ body =>
      coalg_comp (tunit_eta _) (lam_coalg (eD body))
  | ne_fix _ _ _ _ body => Yfix_fun_T (eD body)
  | ne_fix_mr _ _ _ Hfree body => Yfix_mr_pack Hfree (eD body)
  | ne_app _ _ _ Vf Va =>
      kcomp (app_pair _ _)
        (coalg_comp (bang_m _ _) (em_pair (eD Vf) (eD Va)))
  | ne_let _ _ _ _ M0 K => kbind_ext (eD K) (eD M0)
  | ne_sample _ mu Hmu  => sample_kleisli _ mu Hmu
  | ne_real _ r         => real_kleisli _ r
  | ne_score _ f Hfm Hg0 Hl1 e0 =>
      coalg_comp (bang_cofree_hom (score_lift Hfm Hg0 Hl1)) (eD e0)
  | ne_add _ M0 N0 =>
      coalg_comp (bang_cofree_hom add_lift)
                 (coalg_comp (bang_m _ _) (em_pair (eD M0) (eD N0)))
  | ne_mul _ M0 N0 =>
      coalg_comp (bang_cofree_hom mul_lift)
                 (coalg_comp (bang_m _ _) (em_pair (eD M0) (eD N0)))
  | ne_true _  => coalg_comp (tunit_eta _) (bool_value bool_dirac_true)
  | ne_false _ => coalg_comp (tunit_eta _) (bool_value bool_dirac_false)
  | ne_bernoulli _ p Hp0 Hp1 =>
      coalg_comp (tunit_eta _) (bernoulli_value p Hp0 Hp1)
  | ne_if _ _ e M0 N0 => kbind_ext (case_em (eD M0) (eD N0)) (eD e)
  end.
```

### The `kbind_ext` direct-style sequencer

```coq
(* theories/programs/ppl.v *)
Definition kbind_ext (G A B : Coalgebra Ar)
    (K : coalg_hom (EM_prod G A) (Tobj B))
    (M : coalg_hom G (Tobj A)) :
    coalg_hom G (Tobj B) :=
  kcomp K (coalg_comp (T_str_l G A) (em_pair (coalg_id G) M)).

Lemma eD_let (G : named_ctx Ar) (x : string) (t1 t2 : ppl_type Ar)
    (M : named_expr G t1) (K : named_expr ((x, t1) :: G) t2) :
  eD (ne_let x M K) = kbind_ext (eD K) (eD M).
Proof. by []. Qed.
```

The extended-context Kleisli bind is the load-bearing reduction
lemma for `ne_let` and the inner clause of `ne_app`; in direct style
there is no syntactic `return`, so every expression already denotes
a Kleisli arrow.

### Sampling (`sample_kleisli`, `cpD_sample_is_integral`)

```coq
(* theories/programs/cbv.v *)
Lemma cpD_sample_is_integral (X : ar_obj Ar) :
  ch_mor (tunit_eta (FMeas_coalgebra X)) = Coalg X.
Proof. by []. Qed.
```

Following paper Remark 9.8: for `f : FMeas X → B`, the sampler
returns the linearisation of `f` along the Dirac path, which is
exactly the §9.7 coalgebra map `Coalg X`. The Rocq translation is
*definitional*.

---

## Beyond the paper — Call-by-name interpretation (SCones)

**Definition (CBN interpretation).** *Each type `τ` denotes an
integrable cone `⟦τ⟧_n` in `SCones`; each well-typed program
`Γ ⊢ M : τ` denotes a stable and measurable function
`⟦M⟧_n : ⟦Γ⟧_n → ⟦τ⟧_n`. Recursion at any free-coalgebra type is
the fixpoint operator `Yfix` of paper §9.2.*

The base type `tbase X` denotes the cone `FMeas X` *directly* — no
`Bang` lift — the pragmatic QBS reading of Heunen–Kammar–Staton–Yang.
Function types denote the internal hom `stablehom` of paper §7.32,
products the SCones `sprod`, the unit `Stop = ⊤`, and `tbool` the
2-point cone of `bool_cone.v`. Effects live inside the type
interpretation; there is no `Tobj` wrap on the codomain.

| Construction | Rocq |
|---|---|
| Type translation | `tyD_CBN` — `theories/programs/ppl_cbn.v` |
| Context translation | `ctxD_CBN` — same file |
| Term interpretation (pure fragment) | `eD_CBN`, `var_lookup_CBN` — same file |
| Recursion clause | `eD_CBN_fix_E` (the `Yfix`-as-free-recursion identity) — same file |
| Mutual recursion clause | `eD_CBN_fix_mr_E` — same file |
| Effect clauses (hypothesised) | `cbn_sample_clause` … `cbn_if_clause` — same file |

### Type translation (`tyD_CBN`)

```coq
(* theories/programs/ppl_cbn.v *)
Fixpoint tyD_CBN (t : ppl_type Ar) : ICone.type Ar :=
  match t with
  | tunit       => Stop Ar
  | tbool       => bool_cone_car Ar
  | tbase X     => FMeas X
  | tprod s1 s2 => sprod (tyD_CBN s1) (tyD_CBN s2)
  | tfun A B    => stablehom (tyD_CBN A) (tyD_CBN B)
  end.
```

### Term interpretation (`eD_CBN`)

```coq
(* theories/programs/ppl_cbn.v *)
Fixpoint eD_CBN (G : named_ctx Ar) (t : ppl_type Ar)
    (M : @named_expr R Ar R_obj G t) {struct M}
    : scones_hom (ctxD_CBN (drop_names G)) (tyD_CBN t) :=
  match M with
  | ne_var _ _ v => var_lookup_CBN (named_var_to_has_var v)
  | ne_tt _      => ders (Stop_mor _)
  | ne_pair _ _ _ M1 M2 => spair (eD_CBN M1) (eD_CBN M2)
  | ne_fst _ _ _ M0 => scones_comp sfst (eD_CBN M0)
  | ne_snd _ _ _ M0 => scones_comp ssnd (eD_CBN M0)
  | ne_lam _ _ _ _ body => curry (eD_CBN body)
  | ne_app _ _ _ F X => scones_comp Ev (spair (eD_CBN F) (eD_CBN X))
  | ne_let _ _ _ _ M0 K => scones_comp (eD_CBN K)
                                       (spair (scones_id _) (eD_CBN M0))
  | ne_fix _ _ _ _ body =>
      scones_comp (Yfix (tyD_CBN (tfun _ _))) (curry (eD_CBN body))
  | ne_fix_mr _ _ t Hfree body =>
      scones_comp (Yfix (tyD_CBN t)) (curry (eD_CBN body))
  (* effect clauses dispatched through the hypothesised cbn_*_clause *)
  | ne_sample _ mu Hmu  => cbn_sample_clause _ mu Hmu
  | ne_real _ r         => cbn_real_clause _ r
  | ne_score _ f Hfm Hg0 Hl1 e0 =>
      cbn_score_clause _ f Hfm Hg0 Hl1 (eD_CBN e0)
  | ne_add _ M0 N0 => cbn_add_clause _ (eD_CBN M0) (eD_CBN N0)
  | ne_mul _ M0 N0 => cbn_mul_clause _ (eD_CBN M0) (eD_CBN N0)
  | ne_true _      => cbn_true_clause _
  | ne_false _     => cbn_false_clause _
  | ne_bernoulli _ p Hp0 Hp1 => cbn_bernoulli_clause _ p Hp0 Hp1
  | ne_if _ _ e M0 N0 =>
      cbn_if_clause _ _ (eD_CBN e) (eD_CBN M0) (eD_CBN N0)
  end.
```

The effect clauses are *section parameters* — the CBN interpretation
is parametric over them. Concrete instances are
`cbn_sample_clause_def` / `cbn_const_clause` (option-γ baseline, in
`ppl_cbn_eff.v`) and `cbn_add_clause_arith` / `cbn_mul_clause_arith`
(option-β honest bilinear, in `ppl_cbn_arith_eff.v` — see *The CBN
arithmetic refinement* below).

### Recursion clause (`eD_CBN_fix_E`, `Yfix`)

```coq
(* theories/programs/ppl_cbn.v *)
Lemma eD_CBN_fix_E
    (G : named_ctx Ar) (s : string) (t1 t2 : ppl_type Ar)
    (body : named_expr ((s, tfun t1 t2) :: G) (tfun t1 t2))
    (g : ctxD_CBN (drop_names G))
    (Hg : (cone_norm g <= 1)%R) :
  sh_fun (sc_fun (curry (eD_CBN body)) g)
         (sc_fun (eD_CBN (ne_fix s body)) g) =
  sc_fun (eD_CBN (ne_fix s body)) g.
Proof.
rewrite eD_CBN_fix scomp_ball//.
exact: Yfix_fix (sc_image_ball (curry (eD_CBN body)) Hg).
Qed.
```

A single line via paper §9.2's `Yfix`. The CBN win: no bilinear
bridge obligation, free recursion at *every* function type.

### Mutual-recursion clause (`eD_CBN_fix_mr_E`)

```coq
(* theories/programs/ppl_cbn.v *)
Lemma eD_CBN_fix_mr_E
    (G : named_ctx Ar) (s : string) (t : ppl_type Ar)
    (Hfree : is_free_coalg_type t)
    (body : named_expr ((s, t) :: G) t)
    (g : ctxD_CBN (drop_names G)) (Hg : (cone_norm g <= 1)%R) :
  sh_fun (sc_fun (curry (eD_CBN body)) g)
         (sc_fun (eD_CBN (ne_fix_mr s t Hfree body)) g) =
  sc_fun (eD_CBN (ne_fix_mr s t Hfree body)) g.
Proof.
rewrite eD_CBN_fix_mr scomp_ball//.
exact: Yfix_fix (sc_image_ball (curry (eD_CBN body)) Hg).
Qed.
```

Same statement as `eD_CBN_fix_E` modulo replacing `tfun t1 t2` by an
arbitrary `t`. The CBN side has no honest-scope limitation at
`ne_fix_mr`: `Yfix` of paper §9.2 works at *any* integrable cone,
including `tprod (tfun A1 B1) (tfun A2 B2)` (the mutually-recursive
function pair).

---

## Beyond the paper — The Bernoulli-cascade framework

The shared mathematical core of `ppl_cbn_geom.v` and
`ppl_cbn_almost_loop.v`: a single SCones endomorphism scheme that
realises the body of a `if Bernoulli(p) then halt else cont_op µ`
recursion, with the closed-form Kleene cascade `mass(k^n) = 1 −
(1−p)^n` and its `sfix` headlines. Both `ex_geom` and
`ex_almost_loop p` are *instances* of this framework.

| Construction | Rocq |
|---|---|
| The cascade operator `µ ↦ p·halt + (1−p)·cont_op µ` | `phi_bcascade`, `phi_bcascade_E` — `theories/programs/infra/cbn_bernoulli_cascade.v` |
| Kleene chain at `precone_zero` | `kleene_bcascade`, `kleene_bcascade_S_E`, `kleene_bcascade_ball` — same file |
| Per-iterate mass recurrence | `kleene_bcascade_S_mass` — same file |
| Closed form `mass(k^n) = 1 − (1−p)^n` | `kleene_bcascade_mass_closed` — same file |
| Convergence: `mass → 1` when `p > 0` | `kleene_bcascade_mass_cvg_if_pos` — same file |
| Vanishing: `mass = 0` when `p = 0` | `kleene_bcascade_mass_eq_zero_if_zero` — same file |
| `sfix`-level headline `mass = 1` | `sfix_bcascade_mass_one_if_pos` — same file |
| `sfix`-level headline `mass = 0` | `sfix_bcascade_mass_zero_if_zero` — same file |

### The cascade operator (`phi_bcascade`, `phi_bcascade_E`)

```coq
(* theories/programs/infra/cbn_bernoulli_cascade.v *)
Definition phi_bcascade : scones_hom Gc A := (* … *).

Lemma phi_bcascade_E (mu : FMeas R_obj) :
  (cone_norm mu <= 1)%R ->
  sc_fun phi_bcascade mu =
  bool_case (bernoulli p Hp_ge0 Hp_le1)
            halt
            (sc_fun cont_op mu).
```

Built as `Ev ∘ spair (bool_case_linhom of (halt, cont_op) over
Bernoulli(p)) id` (the boolean cascade of *The boolean cascade*
below, composed with the chosen continuation operator).

### Closed form and headlines (`kleene_bcascade_mass_closed`, `sfix_bcascade_mass_one_if_pos`)

```coq
(* theories/programs/infra/cbn_bernoulli_cascade.v *)
Lemma kleene_bcascade_mass_closed (n : nat) :
  fmeas_mu (kleene_bcascade n) [set: ar_carrier Ar R_obj]
  = (1 - (1 - p)^+n : R)%R%:E.

Theorem sfix_bcascade_mass_one_if_pos :
  fmeas_mu halt [set: ar_carrier Ar R_obj] = 1%:E ->
  (forall mu, (cone_norm mu <= 1)%R ->
              fmeas_mu (sc_fun cont_op mu) [set: ar_carrier Ar R_obj]
                = fmeas_mu mu [set: ar_carrier Ar R_obj]) ->
  (0 < p)%R ->
  fmeas_mu sfix_bcascade [set: ar_carrier Ar R_obj] = 1%:E.

Theorem sfix_bcascade_mass_zero_if_zero :
  fmeas_mu halt [set: ar_carrier Ar R_obj] = 1%:E ->
  (forall mu, (cone_norm mu <= 1)%R ->
              fmeas_mu (sc_fun cont_op mu) [set: ar_carrier Ar R_obj]
                = fmeas_mu mu [set: ar_carrier Ar R_obj]) ->
  p = 0%R ->
  fmeas_mu sfix_bcascade [set: ar_carrier Ar R_obj] = 0%E.
```

Instantiate at `p := 1/2`, `halt := δ_0`, `cont_op := shift_scones 1`
for `ex_geom`'s `mass = 1`. Instantiate at `p := p`, `halt := δ_0`,
`cont_op := scones_id` for `ex_almost_loop p`'s two headlines.

---

## Beyond the paper — The CBV outer-point cascade

The CBV counterpart of the CBN Bernoulli-cascade. The CBV
Kleene-style argument runs at the `Bang`-level: each iterate of the
Kleene chain (a linear arrow `linhom_car G (!̃funT)`) is fed against
a *promoted outer point* `prom u`, and the inner application
reduction lemmas (the so-called *outer-point E lemmas*) cascade the
Bang-level evaluation down to a `FMeas R_obj`-valued scalar. Shared
between `ex_loop_arr.v`, `em_fix_arr.v`, `ex_almost_loop_step.v`.

| Construction | Rocq |
|---|---|
| The outer-point coalgebra (`Ctx-side` arg = `one1`, `lin-side` arg = `prom u`) | `at_outer_pt_u` — `theories/programs/infra/cbv_outer_pt.v` |
| `coalg_str` evaluates at the outer point | `coalg_str_G_on_outer_pt_u_E` — same file |
| `coalg_e` evaluates at the outer point | `coalg_e_G_on_outer_pt_u_E` — same file |
| `lam_coalg` evaluates at the outer point (the body's λ closure) | `lam_coalg_at_one_prom` — same file |
| Promotion identity: `linhom_fun u (one1) = …` | `linhom_fun_precone_add_E`, `linhom_fun_precone_scale_E` — same file |

### The outer-point pair (`at_outer_pt_u`)

```coq
(* theories/programs/infra/cbv_outer_pt.v *)
Definition at_outer_pt_u (u : L) : coalg_obj G_L :=
  ptensor one1 (prom u).

Lemma cone_norm_at_outer_pt_u_le1 (u : L) (Hu : cone_norm u <= 1) :
  cone_norm (at_outer_pt_u u) <= 1.
```

The `G_L = EM_term ⊗ !̃ L` carrier with `one1 : EM_term` in the
context slot and `prom u : !̃ L` in the recursive-self slot.

### Evaluation at the outer point (`coalg_str_G_on_outer_pt_u_E`, `lam_coalg_at_one_prom`)

```coq
(* theories/programs/infra/cbv_outer_pt.v *)
Lemma coalg_str_G_on_outer_pt_u_E (u : L) (Hu : cone_norm u <= 1) :
  Lfun (coalg_str G_L) (at_outer_pt_u u) =
  prom (at_outer_pt_u u).

Lemma lam_coalg_at_one_prom
    (body_E : coalg_hom (EM_prod G EM_term) (Tobj funT))
    (u : L) (Hu : cone_norm u <= 1) :
  Lfun (ch_mor (lam_coalg body_E)) (at_outer_pt_u u) =
  (* the body's denotation evaluated at (one1, prom u) *).
```

The lemmas package the per-iterate reduction of a Kleene chain at the
`Bang` level. `ex_loop_arr_mass_zero` (via `Step_loop_E`) and
`ex_geom_arr_mass_one` (via `Phi_arr` / `F_arr`) both consume this
framework.

---

## Beyond the paper — The SCones↔ICones-tensor bilinear stability bridge

The structural unblocker that ties the two interpretations together
at the level of bilinear-into-tensor arithmetic. Given a
measurable-stable `K : G → A` and a bilinear
`Φ : G ⊗ A → B` in `ICones`, the diagonal evaluation
`g ↦ Φ(g ⊗ K(g)) : G → B` is measurable-stable. Built by pure
structural composition through paper Theorem 5.12's
tensor↔internal-hom adjunction (`tensor_curryE`) — no §7.3
finite-difference replay required. Lifted to the internal-hom level
this is paper Lemma 7.31; instantiated at the `Bang` level
(`A := !A`, `B := !B`) it unblocks generic CBV recursion at
`ne_fix`, the honest CBN bilinear arithmetic on `FMeas`, and a CBV /
CBN soundness comparison.

| Construction | Rocq |
|---|---|
| Lifting `linhom → stablehom` is meas-stable (Lem 7.31 at internal-hom) | `linhom_to_stablehom`, `linhom_to_stablehom_meas_stable` — `theories/stable/diag_bilinear_tensor.v` |
| Composition with an `icones_hom` preserves meas-stability | `meas_stable_comp_post`, `meas_stable_comp_pre` — same file |
| The diagonal stable pairing | `id_spair_meas_stable`, `spair_meas_stable` — same file |
| **The deliverable** — diagonal bilinear stability bridge | `meas_stable_diag_bilinear_tensor` — same file |
| Binary variant on `sprod A B` | `meas_stable_bin_bilinear_tensor` — `theories/programs/ppl_cbn_arith_scones.v` |

### Lift `linhom → stablehom` (`linhom_to_stablehom`)

```coq
(* theories/stable/diag_bilinear_tensor.v *)
Definition linhom_to_stablehom
    (h : linhom_car Ar B C) : stablehom B C :=
  MkStablehom (sc_clamp (linhom_fun h))
              (sc_clamp_meas_stable (linhom_meas_stable h))
              (sc_clamp_offball_field _).

Lemma linhom_to_stablehom_meas_stable :
  is_meas_stable
    (linhom_to_stablehom : linhom_car Ar B C -> stablehom B C).
```

The internal-hom version of paper Lemma 7.31: a `linhom_car Ar B C`
is measurable-stable as a *map of cones* (a fact about the
inhabitants of the internal hom). The 0-extension off the unit ball
is the standard `sc_clamp`.

### The deliverable (`meas_stable_diag_bilinear_tensor`)

```coq
(* theories/stable/diag_bilinear_tensor.v *)
Lemma meas_stable_diag_bilinear_tensor
    (K : G -> EA)
    (Phi : icones_hom Ar (tensor Ar G EA) EB) :
  is_meas_stable K ->
  is_meas_stable (fun g : G => Phi (ptensor g (K g))).
```

The proof unfolds the diagonal as

```
g ↦ Φ(g ⊗p K g)
  = linhom_fun ((tensor_curry Φ) g) (K g)           -- Thm 5.12
  = ev_fun ⟨ (linhom_to_stablehom ∘ ders) (tensor_curry Φ) g,
              K g ⟩
```

then assembles the lift (the inner `linhom_to_stablehom` is
meas-stable), the post-composition with `Φ_curry` (meas-stable), the
diagonal pair (meas-stable), and paper Lemma 7.27 (`ev_meas_stable`)
— finally rescaling by linearity of `ev_fun` in its first slot.

### Binary variant (`meas_stable_bin_bilinear_tensor`)

```coq
(* theories/programs/ppl_cbn_arith_scones.v *)
Lemma meas_stable_bin_bilinear_tensor
    (Phi : icones_hom Ar (tensor Ar A B) C) :
  is_meas_stable
    (fun p : sprod A B => Phi (ptensor (sprod_fst p) (sprod_snd p))).
```

The diagonal bridge applied to `Phi_lift := Phi ∘ (icones_proj true ⊗
id_B)` over the projection-then-second-component pairing. Consumed by
the honest CBN arithmetic install of `ppl_cbn_arith_scones.v`.

---

## Beyond the paper — The CBV value-fixpoint at function types

The fixpoint operator of paper §9.2 (`Y`) lives on `SCones` and
operates on stable maps. The CBV value-fixpoint at function type —
recursion as in OCaml's `let rec` — is its EM(!)-Kleisli counterpart;
it generalises paper §9.2's `Yfix` from `SCones` (stable maps)
to its EM(!)-Kleisli counterpart. The construction is a Kleene
iteration on the unit-ball
CPO of the `linhom` cone, packaged as a `coalg_hom` via the cofree
adjunction `U ⊣ !̃` of the LNL structure.

| Construction | Rocq |
|---|---|
| ω-continuity infrastructure on `linhom` | `linhom_pre_icones_sup`, `linhom_post_icones_sup`, `bang_fmap_lin_omega_cont`, `prom_omega_cont`, `tensor_mor_omega_cont_R`, `tensor_mor_R_lin_incr` — `theories/programs/infra/em_continuity.v` |
| The Kleene operator on the `linhom` cone | `Phi_fun`, `Phi_fun_ball`, `Phi_fun_incr`, `Phi_fun_cont` — `theories/programs/infra/em_fix.v` |
| The Kleene supremum (linhom level) | `Yfix_fun_lin`, `Yfix_fun_lin_norm_le1`, `Yfix_fun_lin_fixpoint` — same file |
| The `coalg_hom` packaging — the CBV value-fixpoint | `Yfix_fun_T`, `Yfix_fun_T_unfolding` — same file |
| Dispatcher for `ne_fix_mr` (sound at `tfun`, honest-scope at `tprod`) | `Yfix_mr_pack`, `Yfix_mr_pack_fun`, `Yfix_mr_pack_prod` — `theories/programs/ppl.v` |
| Bang-level Kleene-cascade headlines (`ex_geom`) | `Phi_arr`, `Yfix_arr`, `Yfix_arr_fixpoint`, `F_arr`, `kleene_arr_chain` — `theories/programs/infra/em_fix_arr.v` |

### The linhom-level Kleene operator (`Phi_fun`)

```coq
(* theories/programs/infra/em_fix.v *)
Definition Phi_fun
    (prev : linhom_car Ar (coalg_obj G) (coalg_obj funT)) :
    linhom_car Ar (coalg_obj G) (coalg_obj funT) :=
  (* bang_fmap (der L) ∘ ch_mor M ∘ tensor_mor (id_G, prev) ∘ coalg_d G *).
```

The body's natural reading: starting from the `coalg_d`
comultiplication on the context, tensor in the previous recursive
approximation `prev`, run the body `M` (as an `icones_hom`), then
dereliction back. The composite is linear, norm-≤ 1 on the unit
ball, monotone, and ω-continuous.

### The Kleene supremum (`Yfix_fun_lin`, `Yfix_fun_lin_fixpoint`)

```coq
(* theories/programs/infra/em_fix.v *)
Definition Yfix_fun_lin :
    linhom_car Ar (coalg_obj G) (coalg_obj funT) :=
  cone_sup_ball Phi_fun_iter Phi_fun_iter_chain Phi_fun_iter_ball.

Lemma Yfix_fun_lin_norm_le1 :
  cone_norm Yfix_fun_lin <= 1.

Lemma Yfix_fun_lin_fixpoint :
  Phi_fun Yfix_fun_lin = Yfix_fun_lin.
```

### The `coalg_hom` packaging (`Yfix_fun_T`)

```coq
(* theories/programs/infra/em_fix.v *)
Definition Yfix_fun_T : coalg_hom G (Tobj funT) :=
  adj_psi (linhom_icones Yfix_fun_lin Yfix_fun_lin_norm_le1).
```

`adj_psi` of the cofree adjunction `U ⊣ !̃` is unconditionally
available on any norm-≤ 1 `icones_hom`, so no separate
`is_coalg_mor` obligation arises. This is the CBV value-fixpoint
consumed by the `ne_fix` clause of `eD`.

### Dispatcher for `ne_fix_mr` (`Yfix_mr_pack`)

```coq
(* theories/programs/ppl.v *)
Fixpoint Yfix_mr_pack (Ctx : Coalgebra Ar) (t : T)
    (Hfree : is_free_coalg_type t) {struct t} :
    coalg_hom (EM_prod Ctx (tyD t)) (Tobj (tyD t)) ->
    coalg_hom Ctx (Tobj (tyD t)) := ...

Lemma Yfix_mr_pack_fun (Ctx : Coalgebra Ar) (A B : T)
    (Hfree : is_free_coalg_type (tfun A B))
    (body : coalg_hom (EM_prod Ctx (tyD (tfun A B)))
                      (Tobj (tyD (tfun A B)))) :
  Yfix_mr_pack Hfree body = Yfix_fun_T body.
Proof. by []. Qed.

Lemma Yfix_mr_pack_prod (Ctx : Coalgebra Ar) (t1 t2 : T)
    (Hfree : is_free_coalg_type (tprod t1 t2))
    (body : coalg_hom (EM_prod Ctx (tyD (tprod t1 t2)))
                      (Tobj (tyD (tprod t1 t2)))) :
  Yfix_mr_pack Hfree body =
  @const_kleisli R Ar Ctx _ precone_zero (precone_zero_norm_le1 _).
Proof. by []. Qed.
```

At `tfun A B` this is definitionally `Yfix_fun_T`. At `tprod t1 t2`
it is the honest-scope constant-zero placeholder (CBV mutual
recursion at product types is documented-deferred, see *What is not
formalised* below). The CBN side has no such limitation.

### Bang-level Kleene cascade (`Phi_arr`, `Yfix_arr`, `F_arr`)

```coq
(* theories/programs/infra/em_fix_arr.v *)
Definition Phi_arr (v : coalg_obj funT_geom) : coalg_obj funT_geom :=
  (* … the Kleene operator at the Bang level for ex_geom *).

Definition Yfix_arr : coalg_obj funT_geom :=
  cone_sup_ball kleene_arr kleene_arr_chain kleene_arr_ball.

Lemma Yfix_arr_fixpoint : Phi_arr Yfix_arr = Yfix_arr.

Definition F_arr (n : nat) : FMeas R_obj :=
  Lfun (der (FMeas R_obj))
       (linhom_fun (Lfun (der L_geom) (kleene_arr n))
                   (one1 : cone_one_car Ar)).
```

`F_arr n` is the FMeas-element extracted from `kleene_arr n` by
applying `der L_geom`, evaluating at `one1`, then `der (FMeas R_obj)`
— the recipe that powers `ex_geom_arr_mass_one` and
`ex_geom_arr_is_geometric_distribution` (see EXAMPLES.md).

---

## Beyond the paper — The boolean cascade

The 2-point cone of paper §4.4 / Theorem 4.24 — the coproduct
`1 ⊕ 1` — is built concretely as `bool_cone_car Ar : {nonneg R} ×
{nonneg R}` with norm `‖(p, q)‖ = p + q`, with its full HB tower, its
universal co-pairing as an `icones_hom`, an EM(!)-Kleisli case
combinator for the `if-then-else` of `named_expr`, and a CBN-side
`scones_hom` packaging via `ders`. The key insight that avoids a
`Bang`-level bilinearity obstruction: a `coalg_hom` from
`EM_prod G A` to `Tobj B` is automatically norm-≤ 1 *as an arrow*, so
the co-pairing `bool_case_linhom` consumes it verbatim.

| Construction | Rocq |
|---|---|
| The 2-point ICone with full HB tower | `bool_cone_car`, `bool_dirac_true`, `bool_dirac_false` — `theories/programs/infra/bool_cone.v` |
| The universal co-pairing | `bool_case`, `bool_case_true`, `bool_case_false`, `bool_case_linear`, `bool_case_omega_continuous`, `bool_case_norm_le1`, `bool_case_pres_path`, `bool_case_pres_int` — same file |
| Unit-ball-free variants | `bool_case_omega_continuous_gen`, `bool_case_norm_le_max`, `bool_case_pres_path_gen`, `bool_case_pres_int_gen` — same file |
| Test measurability, generalised | `test_meas_gen` — `theories/mcones/mcone.v` |
| Icones-hom packaging | `bool_case_linhom`, `bool_case_linhom_gen`, `bool_case_icones_hom` — `theories/programs/infra/bool_case_hom.v` |
| α / β decomposition | `alpha_linhom`, `beta_linhom`, `bool_case_linhom_gen_alpha_beta` — same file |
| SCones-side packaging (via paper Lem 7.31) | `bool_case_scones` — `theories/programs/infra/bool_case_scones.v` |
| EM-Kleisli `case_em` combinator | `case_em` — `theories/programs/ppl.v` |
| Bernoulli value (Kleisli return at `tbool`) | `bernoulli_value`, `case_em_bernoulli` — same file |

### The 2-point cone (`bool_cone_car`)

```coq
(* theories/programs/infra/bool_cone.v *)
Record bool_cone_car (dummy : MeasSubcat R) : Type :=
  MkBoolCone { bc_t : {nonneg R}; bc_f : {nonneg R} }.

Definition bool_dirac_true  : bool_cone_car Ar := MkBoolCone Ar 1%:nng 0%:nng.
Definition bool_dirac_false : bool_cone_car Ar := MkBoolCone Ar 0%:nng 1%:nng.
```

The cone norm is `‖(p, q)‖ = p + q`, recognised as the paper §4.4 /
Thm 4.24 coproduct `cone_one_car ⊕ cone_one_car`.

### The universal co-pairing (`bool_case`)

```coq
(* theories/programs/infra/bool_cone.v *)
Definition bool_case (x : bool_cone_car Ar) (a b : A) : A :=
  precone_add (precone_scale (bc_t x) a) (precone_scale (bc_f x) b).

Lemma bool_case_true  (a b : A) : bool_case bool_dirac_true  a b = a.
Lemma bool_case_false (a b : A) : bool_case bool_dirac_false a b = b.

Lemma bool_case_linear (a b : A) : is_linear (fun x => bool_case x a b).
Lemma bool_case_omega_continuous
    (Ha : cone_norm a <= 1) (Hb : cone_norm b <= 1) :
  is_omega_continuous (fun x : bool_cone_car Ar => bool_case x a b).
Lemma bool_case_norm_le1
    (Ha : cone_norm a <= 1) (Hb : cone_norm b <= 1) (x : bool_cone_car Ar) :
  cone_norm (bool_case x a b) <= cone_norm x.
```

Paper §4.4 / Thm 4.24 universal-property formula
`[a, b](x) = bc_t(x)·a + bc_f(x)·b`. Linear in `x`, ω-continuous on
the unit ball, norm ≤ 1 when `‖a‖, ‖b‖ ≤ 1`, and preserves
measurable paths and integrals.

### Icones-hom packaging (`bool_case_linhom`, `case_em`)

```coq
(* theories/programs/infra/bool_case_hom.v *)
Definition bool_case_linhom
    (a b : A) (Ha : cone_norm a <= 1) (Hb : cone_norm b <= 1) :
    linhom_car Ar (bool_cone_car Ar) A.

Definition bool_case_icones_hom
    (a b : A) (Ha : cone_norm a <= 1) (Hb : cone_norm b <= 1) :
    icones_hom Ar (bool_cone_car Ar) A.

(** Unit-ball-free variant; uses [bool_case_norm_le_max]. *)
Definition bool_case_linhom_gen (a b : A) :
    linhom_car Ar (bool_cone_car Ar) A.
```

```coq
(* theories/programs/ppl.v *)
Definition case_em (G : Coalgebra Ar) (A : ppl_type Ar)
    (a b : coalg_hom (EM_prod G (tyD A)) (Tobj (tyD A))) :
    coalg_hom (EM_prod G (bang_cofree (bool_cone_car Ar)))
              (Tobj (tyD A)).
```

The EM(!) value-level `if-then-else` combinator. Branches `a`, `b`
are auto-unit-ball *as coalg homs* — the hom-cone insight that lets
`bool_case_linhom` consume them with no ad-hoc bound. Build via
`bool_case_linhom` of `a_lh := adj_phi a` / `b_lh := adj_phi b` on
the Kleisli-bool source, then tensor-uncurry to consume the
`bool_cone_car` source, then `adj_psi` back into the `Tobj A`
codomain.

---

## Beyond the paper — The CBN arithmetic refinement (option-β)

The CBN denotation `eD_CBN` is parameterised over the effect clauses
(`cbn_sample_clause`, …, `cbn_if_clause`). The pragmatic *option-γ*
baseline (`cbn_const_clause`) makes `cbn_add_clause_def` /
`cbn_mul_clause_def` constant at `precone_zero` — the honest reading
given that under option-γ the unit type denotes the terminal cone
`Stop`. The *option-β* refinement replaces those clauses with
genuine bilinear arithmetic on `FMeas R_obj`, lifted from the FMeas
lax-monoidal map of paper §5 via the diagonal bilinear stability
bridge above.

| Construction | Rocq |
|---|---|
| `add_FMeas` / `mul_FMeas` measure-theoretic foundation | `add_FMeas`, `add_FMeas_setT`, `add_FMeas_norm`, `add_FMeas_dirac`, `mul_FMeas`, `mul_FMeas_setT`, `mul_FMeas_norm`, `mul_FMeas_dirac` — `theories/programs/ppl_cbn_arith.v` |
| `linhom`-level bilinear `add_FMeas_lax_icones` / `mul_FMeas_lax_icones` | `add_FMeas_lax_icones`, `add_FMeas_lax_icones_pt`, `mul_FMeas_lax_icones`, `mul_FMeas_lax_icones_pt` — `theories/programs/ppl_cbn_arith_scones.v` |
| Lifting to a `scones_hom` via the binary bridge | `add_FMeas_pair_fun`, `add_FMeas_pair_fun_meas_stable`, `add_FMeas_scones`, `add_FMeas_scones_E`, `add_FMeas_scones_dirac` — same file |
| Replacement effect clauses (option-β) | `cbn_add_clause_arith`, `cbn_mul_clause_arith`, `cbn_add_clause_arith_E`, `cbn_mul_clause_arith_E` — `theories/programs/ppl_cbn_arith_eff.v` |
| Refined CBN denotation `eD_CBN_full_arith` | `eD_CBN_full_arith`, `eD_CBN_full_arith_add_E`, `eD_CBN_full_arith_mul_E` — same file |

### Measure-theoretic foundation (`add_FMeas`, `add_FMeas_dirac`)

```coq
(* theories/programs/ppl_cbn_arith.v *)
Definition add_FMeas (mu nu : fmeas R (ar_carrier Ar R_obj)) :
    fmeas R (ar_carrier Ar R_obj) :=
  (* Pushforward of fmeas_lax_pre mu nu under add_meas. *)

Lemma add_FMeas_setT (mu nu : fmeas R (ar_carrier Ar R_obj)) :
  fmeas_mu (add_FMeas mu nu) [set: ar_carrier Ar R_obj] =
  fmeas_mu mu [set: ar_carrier Ar R_obj]
  * fmeas_mu nu [set: ar_carrier Ar R_obj].

Lemma add_FMeas_dirac (a b : R) :
  add_FMeas (dirac_fmeas (R_to_carrier R_carrier_eq a))
            (dirac_fmeas (R_to_carrier R_carrier_eq b)) =
  dirac_fmeas (R_to_carrier R_carrier_eq (a + b)).
```

Bilinear in `(µ, ν)` measure-theoretically; the Dirac identity is
load-bearing for any QBS-paper-flagship Dirac reduction.

### SCones packaging (`add_FMeas_scones`)

```coq
(* theories/programs/ppl_cbn_arith_scones.v *)
Definition add_FMeas_lax_icones :
    icones_hom Ar
      (tensor Ar (FMeas R_obj) (FMeas R_obj))
      (FMeas R_obj) :=
  icones_comp (FMeas_fmap add_meas') (fmeas_lax R_obj R_obj).

Definition add_FMeas_scones :
    scones_hom (sprod (FMeas R_obj) (FMeas R_obj)) (FMeas R_obj) :=
  MkStablehom (sc_clamp add_FMeas_pair_fun)
              add_FMeas_pair_fun_meas_stable_clamp
              (add_FMeas_clamp_norm_le1 _).
```

The `linhom`-level construction is the SAFT-style composite of
paper §5's `fmeas_lax` and the FMeas-functorial action of the
measurable `+`; the SCones lift uses
`meas_stable_bin_bilinear_tensor` of *The bilinear stability bridge*
above to package the bilinear-on-tensor map as a stable arrow on the
SCones product.

### Option-β replacement clauses (`cbn_add_clause_arith`, `eD_CBN_full_arith`)

```coq
(* theories/programs/ppl_cbn_arith_eff.v *)
Definition cbn_add_clause_arith
    (G : ppl_ctx Ar)
    (M N : scones_hom (ctxD_CBN G) (FMeas R_obj)) :
    scones_hom (ctxD_CBN G) (FMeas R_obj) :=
  scones_comp add_FMeas_scones (spair M N).

Lemma cbn_add_clause_arith_E (G : ppl_ctx Ar)
    (M N : scones_hom (ctxD_CBN G) (FMeas R_obj))
    (g : ctxD_CBN G) (Hg : (cone_norm g <= 1)%R) :
  sc_fun (cbn_add_clause_arith M N) g =
  add_FMeas (sc_fun M g) (sc_fun N g).

Definition eD_CBN_full_arith (G : named_ctx Ar) (t : ppl_type Ar)
    (M : @named_expr R Ar R_obj G t) :
    scones_hom (ctxD_CBN (drop_names G)) (tyD_CBN t) := (* … *).
```

`eD_CBN_full_arith` instantiates `eD_CBN` with the option-β
arithmetic clauses (and the option-γ baseline elsewhere). It supports
the CBN-side honest QBS-flagship marginal identity
`ex_random_linear_arith_marginal_at` of EXAMPLES.md.

---

## What is **not** formalised

A handful of PPL-side items are intentionally left open.

| Item | What it is | Why not yet |
|---|---|---|
| Law-2 (`kbind_ext_A`) | Bridge from the `kcomp`-of-`sample` shape to the `Lfun .. one1` integration-side shape for the Bayes posterior headline. | Requires cartesian uniqueness in `EM(!)` exposed at the `icones_hom` level; the current cones library packages the η-rule only at the coalg-hom level via `em_pair_mor_proj_id`. |
| Option-α refinement | Replace `tyD_CBN tunit := Stop` (terminal) by `Bang(FMeas *)` so `score` and the arithmetic constructors do not collapse to constants. | Needs a parallel `eD_CBN_full_alpha` interpretation and the corresponding `cbn_*_clause_alpha`; not yet packaged. |
| CBV value-fixpoint at product types | `Yfix_mr_pack` at `tprod` is currently a constant-zero placeholder. | Requires a `Bang`-level Kleene cascade at `tprod` (the natural product of two `Yfix_fun_T`s plus a Seely-2-iso untangling); CBN side via `Yfix` at the product cone is unaffected and is fully sound. |
| CBV / CBN soundness theorem | No proof that `⟦M⟧_CBV` and `⟦M⟧_CBN` agree in any sense. | Requires commuting `Bang` with the effect-bearing types, which has no closed-form realisation in the SAFT-built `Bang`. |
| External semantic equivalence | A QBS / ProbProg / Pyro / Stan correspondence. | The correctness statements in this development are denotational identities at the categorical level. |

---

## How to verify

```sh
make -j

echo "Print Assumptions Skern_to_ICones_fully_faithful." | \
  rocq top -Q theories Icones -l theories/kernels/kernel_embedding.v
echo "Print Assumptions eD_CBN_fix_E."            | \
  rocq top -Q theories Icones -l theories/programs/ppl_cbn.v
echo "Print Assumptions eD_CBN_fix_mr_E."         | \
  rocq top -Q theories Icones -l theories/programs/ppl_cbn.v
echo "Print Assumptions Yfix_fun_T."              | \
  rocq top -Q theories Icones -l theories/programs/infra/em_fix.v
echo "Print Assumptions case_em."                 | \
  rocq top -Q theories Icones -l theories/programs/ppl.v
echo "Print Assumptions meas_stable_diag_bilinear_tensor." | \
  rocq top -Q theories Icones -l theories/stable/diag_bilinear_tensor.v
echo "Print Assumptions sfix_bcascade_mass_one_if_pos." | \
  rocq top -Q theories Icones -l theories/programs/infra/cbn_bernoulli_cascade.v
```

Each command reports only `propositional_extensionality`,
`functional_extensionality_dep` and
`constructive_indefinite_description` (the classical-logic axioms of
`mathcomp-analysis`). Per-entry pages embed the precise identifier
name, file, and a GitHub link to the Rocq source.

For the example programs and their mass / marginal / PMF identities,
see the [Examples tab](../examples/) — `docs/EXAMPLES.md`.
