# PPL.md — A direct-style PPL on top of the integrable-cones model

A typed probabilistic functional language sits on top of the paper's
categorical model. Each type denotes a `!`-coalgebra, each program a
*linear* morphism in `ICone` between the underlying carriers of the
context and result coalgebras, and recursion at function type is
realised as a Kleene fixpoint on the unit-ball cpo of the relevant
internal hom. The same surface syntax also admits a call-by-name
reading through the cartesian closed `SCones` of stable and
measurable functions of paper §7. The language is direct-style
(Plotkin / Girard), named-variable (Saito–Affeldt APLAS 2023), and
probabilistic effects live entirely in the interpretation — there is
no `tprob` type marker, no syntactic `return`, no `bind`. Examples
are listed in [EXAMPLES.md](../examples/).

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
the context. The CBN interpretation routes through paper §9.2's
`Yfix`. The CBV interpretation in `theories/programs/ppl_cbv.v`
resolves both `ne_fix` and `ne_fix_mr` to the Kleene iteration
`Yfix_fun_lin` of `theories/programs/infra/em_fix.v` on the
unit-ball CPO of the clean `linhom`-cone — see *The CBV
value-fixpoint at function types* below.

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
`Yfix` at the product cone (fully sound). CBV in
`theories/programs/ppl_cbv.v` routes `ne_fix_mr` through the same
`Yfix_fun_lin` of `theories/programs/infra/em_fix.v` as `ne_fix` —
the operator is parametric in the codomain coalgebra, so the same
recipe handles both function types and any free-coalgebra type.

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

## Beyond the paper — Call-by-value interpretation (linhom + comonoid)

**Definition (CBV interpretation).** *Each type `τ` denotes a
`!`-coalgebra `⟦τ⟧ ∈ EM(!)`; each well-typed program `Γ ⊢ M : τ`
denotes a linear morphism `⟦M⟧ : U⟦Γ⟧ ⊸ U⟦τ⟧` in `ICone` — an
element of `linhom_car Ar (coalg_obj ⟦Γ⟧) (coalg_obj ⟦τ⟧)`. Programs
are not coalgebra morphisms (the sampling clause is not a coalgebra
morphism: it doesn't commute with the §9.7 duplicability structure
on `FMeas`); the coalgebra structure of the context is used only
through the comonoid pair `(δ, ε) = (coalg_d, coalg_e)` that every
EM(!) object carries by Mellies' Proposition 28 — see Paper-tab
`EM(!) is fully cartesian`.*

In Rocq this is the function

```
eD : named_expr Γ τ →
       linhom_car Ar (coalg_obj (ctxD_cbv (drop_names Γ)))
                     (coalg_obj (tyD_cbv τ))
```

of `theories/programs/ppl_cbv.v`, defined by structural recursion on
`named_expr`. Internally it is built from an `icones_hom`-valued
helper `eD_cbv` (an inhabitant of the unit ball of the same
`linhom`) and forwarded to a linhom by `icones_to_linhom`; the two
views are interchangeable. There is no Kleisli wrapping on the
codomain of `tfun`: function VALUES are linear maps `U⟦t1⟧ ⊸ U⟦t2⟧`,
and duplicability comes from the outer cofree `!̃` only.

| Construction | Rocq |
|---|---|
| Type translation (no `Tobj` on `tfun`) | `tyD_cbv` — `theories/programs/ppl_cbv.v` |
| Context translation | `ctxD_cbv` — same file |
| Variable lookup (projection chain) | `var_lookup_cbv` — same file |
| Constant `icones_hom` helpers (`sample`, `real`, `true`/`false`, `bernoulli`) | `sample_icones`, `real_icones`, `true_icones`, `false_icones`, `bernoulli_icones` — same file |
| If-then-else combinator at the icones level | `if_icones`, `if_under` — same file |
| Internal icones-valued term interpretation | `eD_cbv` — same file |
| Public linhom-valued term interpretation | `eD` — same file |
| EM cartesian primitives (`δ`, `ε`, projections, pairing) | `coalg_d`, `coalg_e`, `em_proj1_mor`, `em_proj2_mor`, `em_pair_mor`, `em_term_mor` — `theories/programs/infra/cbv_adjunction.v` |

### Type translation (`tyD_cbv`)

```coq
(* theories/programs/ppl_cbv.v *)
Fixpoint tyD_cbv (t : ppl_type Ar) : Coalgebra Ar :=
  match t with
  | tunit       => EM_term
  | tbool       => bool_cone_coalg
  | tbase X     => FMeas_coalgebra X
  | tprod t1 t2 => EM_prod (tyD_cbv t1) (tyD_cbv t2)
  | tfun  t1 t2 => bang_cofree
                     (linhom_car Ar (coalg_obj (tyD_cbv t1))
                                    (coalg_obj (tyD_cbv t2)))
  end.
```

`⟦tunit⟧ = EM_term` is the terminal coalgebra; `⟦tbase X⟧ = (FMeas
X, h_X)` is the Theorem 9.7 coalgebra; `⟦tprod t1 t2⟧` is the EM
cartesian product. `⟦tfun t1 t2⟧` is the outer-cofree of the *clean*
internal hom `U⟦t1⟧ ⊸ U⟦t2⟧` — no `Tobj` on the codomain. The
`tbool` clause uses `bool_cone_coalg` of
`theories/programs/infra/bool_cone_coalg.v` — the §9.7-style
hand-rolled coalgebra structure on the 2-point sub-probability cone
of `bool_cone.v`, whose structure map is
`p·δ_T + q·δ_F ↦ p·prom(δ_T) + q·prom(δ_F)`. The §9.7 structure
gives the *shared-sample* semantics expected of a PPL: `let x =
Bernoulli(p) in (x, x)` denotes the diagonal pushforward `p·(T, T) +
(1-p)·(F, F)`, not the independent product `µ ⊗ µ` that the cofree
`bang_cofree (bool_cone_car Ar)` would give.

### Context translation (`ctxD_cbv`)

```coq
(* theories/programs/ppl_cbv.v *)
Fixpoint ctxD_cbv (G : ppl_ctx Ar) : Coalgebra Ar :=
  match G with
  | nil     => EM_term
  | t :: G' => EM_prod (ctxD_cbv G') (tyD_cbv t)
  end.
```

### Term interpretation (`eD_cbv`, `eD`)

The clean CBV interpretation is uniformly comonoid-primitive: every
branching node (let, pair, app, if, arithmetic, boolean) uses the
`δ_Γ` diagonal of the context to give each sub-term its own copy of
`Γ`; multi-use of a free variable is then free in the cone. The
cofree exponential `!̃` appears only at two boundaries — `ne_lam`,
where the body is curried and promoted via the strength `str_Γ` of
the `U⊣!̃` adjunction, and `ne_app`, where the function value is
dereferenced via `der` before evaluation.

```coq
(* theories/programs/ppl_cbv.v *)
Fixpoint eD_cbv (G : named_ctx Ar) (t : T)
    (M : @named_expr R Ar R_obj G t) {struct M} : EXi G t :=
  match M with
  | ne_var _ _ v          => ch_mor (var_lookup_cbv (named_var_to_has_var v))
  | ne_tt G0              => ch_mor (em_term_mor (ctxD_cbv (drop_names G0)))
  | ne_pair _ _ _ M1 M2   => em_pair_mor (eD_cbv M1) (eD_cbv M2)
  | ne_fst _ _ _ M0       => icones_comp (em_proj1_mor _ _) (eD_cbv M0)
  | ne_snd _ _ _ M0       => icones_comp (em_proj2_mor _ _) (eD_cbv M0)
  | ne_lam _ _ _ _ body   => ch_mor (adj_psi (tensor_curry (eD_cbv body)))
  | ne_app _ _ _ Vf Va    =>
      icones_comp
        (tensor_uncurry (icones_id Ar _))
        (icones_comp
          (tensor_mor (der _) (icones_id Ar _))
          (em_pair_mor (eD_cbv Vf) (eD_cbv Va)))
  | ne_let _ _ _ _ M0 K   =>
      icones_comp (eD_cbv K)
        (em_pair_mor (icones_id Ar _) (eD_cbv M0))
  | ne_sample G0 mu Hmu   => sample_icones (ctxD_cbv (drop_names G0)) mu Hmu
  | ne_real G0 r          => real_icones R_obj R_carrier_eq _ r
  | ne_score _ f Hfm Hg0 Hl1 e0 =>
      icones_comp (score_lift Hfm Hg0 Hl1) (eD_cbv e0)
  | ne_add _ M0 N0        => icones_comp add_lift
                               (em_pair_mor (eD_cbv M0) (eD_cbv N0))
  | ne_mul _ M0 N0        => icones_comp mul_lift
                               (em_pair_mor (eD_cbv M0) (eD_cbv N0))
  | ne_true G0            => true_icones (ctxD_cbv (drop_names G0))
  | ne_false G0           => false_icones (ctxD_cbv (drop_names G0))
  | ne_bernoulli G0 p H0 H1 =>
      bernoulli_icones (ctxD_cbv (drop_names G0)) p H0 H1
  | ne_if _ _ e M0 N0     => if_icones (eD_cbv M0) (eD_cbv N0) (eD_cbv e)
  | ne_fix G0 _ t1 t2 body =>
      linhom_icones
        (Yfix_fun_lin (coalg_d (ctxD_cbv (drop_names G0)))
                      (eD_cbv body))
        (Yfix_fun_lin_norm_le1 _ _)
  | ne_fix_mr G0 _ ty _ body =>
      linhom_icones
        (Yfix_fun_lin (coalg_d (ctxD_cbv (drop_names G0)))
                      (eD_cbv body))
        (Yfix_fun_lin_norm_le1 _ _)
  end.

Definition eD M : linhom_car Ar (coalg_obj (ctxD_cbv (drop_names G)))
                                (coalg_obj (tyD_cbv t)) :=
  icones_to_linhom (eD_cbv M).
```

The `ne_fix` and `ne_fix_mr` clauses resolve to the Kleene fixpoint
`Yfix_fun_lin` on the unit-ball CPO of the clean `linhom`-cone (see
*The CBV value-fixpoint at function types* below); the diagonal
`coalg_d (ctxD_cbv (drop_names G0))` supplies the context-coalgebra
comonoid `δ_Γ` used inside the Kleene step. Every other clause is
built from the SMC primitives (`linhom_comp`, `tensor_mor`,
`tensor_braid`, `tensor_curry` / `tensor_uncurry`) and the
coalgebra-comonoid pair (`coalg_d`, `coalg_e`) only.

### Constant icones helpers (`sample_icones`, `real_icones`, `bernoulli_icones`)

Each effect / value constructor (`ne_sample`, `ne_real`,
`ne_bernoulli`, `ne_true`, `ne_false`) denotes a *constant*
`icones_hom` out of the context: the context's `ε_Γ` discards the
context, then the constant value (a unit-ball measure, Dirac, or
two-point distribution) is injected through `const_icones` of
`theories/programs/ppl.v`.

```coq
(* theories/programs/ppl_cbv.v *)
Definition sample_icones (G : Coalgebra Ar) (X : ar_obj Ar)
    (mu : fmeas R (ar_carrier Ar X)) (Hmu : (cone_norm mu <= 1)%R) :
    icones_hom Ar (coalg_obj G) (coalg_obj (FMeas_coalgebra X)) :=
  const_icones G mu Hmu.

Definition true_icones (G : Coalgebra Ar) :
    icones_hom Ar (coalg_obj G) (bool_cone_car Ar) :=
  const_icones G (bool_dirac_true : bool_cone_car Ar)
                 bool_dirac_true_norm_le1.
```

With `tyD_cbv tbool = bool_cone_coalg`, the carrier of `⟦tbool⟧` is
`bool_cone_car Ar` directly (not `Bang _`), so the value is the basis
point `bool_dirac_true` itself — no `prom` wrap is needed.

### If-then-else at the icones level (`if_icones`)

The Boolean cascade is rebuilt around the universal co-pairing
`bool_case_linhom` of `bool_case_hom.v`: the two branches `M`, `N`
are taken as `icones_hom G → A` and converted to linhoms `m_lh`,
`n_lh`; `bool_case_linhom m_lh n_lh` gives a linhom `bool_cone ⊸ (G
⊸ A)`; SMCC uncurry then yields `bool_cone ⊗ G → A`; the scrutinee
is composed in via the braid and `der_bool`, then paired with `id_G`
via `em_pair_mor`. The result is a clean `icones_hom G → A` — no
Kleisli wrapping anywhere.

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

## Beyond the paper — The SCones↔ICones-tensor bilinear stability bridge

The structural unblocker behind the honest CBN bilinear arithmetic
on `FMeas`. Given a measurable-stable `K : G → A` and a bilinear
`Φ : G ⊗ A → B` in `ICones`, the diagonal evaluation
`g ↦ Φ(g ⊗ K(g)) : G → B` is measurable-stable. Built by pure
structural composition through paper Theorem 5.12's
tensor↔internal-hom adjunction (`tensor_curryE`) — no §7.3
finite-difference replay required. Lifted to the internal-hom level
this is paper Lemma 7.31; the SCones-product variant is consumed by
the CBN `add_FMeas` / `mul_FMeas` lift of `ppl_cbn_arith_scones.v`.

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

The CBV-side `let rec` (the `ne_fix` and `ne_fix_mr` clauses of
`ppl_cbv.v`) is the Kleene iteration on the unit-ball ω-CPO of the
clean `linhom`-cone `linhom_car Ar Γ B` — no `Tobj` / `!̃U` wrap on
the codomain `B`. Lives in `theories/programs/infra/em_fix.v`,
parameterised by an arbitrary diagonal `diag : Γ → Γ ⊗ Γ` and the
body's icones-hom `M : Γ ⊗ B → B`; specialised in `ppl_cbv.v` at
`diag := coalg_d (ctxD_cbv (drop_names G))` (the context coalgebra's
comonoid diagonal) and `M := eD_cbv body`.

| Construction | Rocq |
|---|---|
| The Kleene step `M ∘ (id ⊗ prev) ∘ diag` (safe, on unit-ball `prev`) | `Phi_fun_safe` — `theories/programs/infra/em_fix.v` |
| The total Kleene step (with `precone_zero` off the unit ball) | `Phi_fun` — same file |
| Ball preservation / monotonicity / ω-continuity | `Phi_fun_ball`, `Phi_fun_incr`, `Phi_fun_cont` — same file |
| The CBV value-fixpoint as `sup_n (Phi_fun)^n precone_zero` | `Yfix_fun_lin` — same file |
| Fixpoint equation `Phi_fun (Yfix_fun_lin) = Yfix_fun_lin` | `Yfix_fun_lin_fixpoint` — same file |
| Unit-ball preservation `cone_norm Yfix_fun_lin ≤ 1` | `Yfix_fun_lin_norm_le1` — same file |
| Consumed by the CBV recursion clauses `ne_fix` / `ne_fix_mr` | the two `linhom_icones (Yfix_fun_lin _ _) (Yfix_fun_lin_norm_le1 _ _)` branches at the end of `eD_cbv` — `theories/programs/ppl_cbv.v` |

### The Kleene step (`Phi_fun`, `Phi_fun_safe`)

```coq
(* theories/programs/infra/em_fix.v *)
Definition Phi_fun_safe
    (diag : icones_hom Ar Gamma (tensor Ar Gamma Gamma))
    (M : icones_hom Ar (tensor Ar Gamma B) B)
    (prev : linhom_car Ar Gamma B) (Hprev : cone_norm prev <= 1) :
    linhom_car Ar Gamma B :=
  linhom_post M
    (linhom_pre_act diag
      (tensor_mor_R_lin Gamma (linhom_icones prev Hprev))).

Definition Phi_fun diag M (prev : linhom_car Ar Gamma B) :
    linhom_car Ar Gamma B :=
  match pselect (cone_norm prev <= 1) with
  | left H  => Phi_fun_safe diag M prev H
  | right _ => precone_zero
  end.
```

The "safe" version is the categorical Kleene step `M ∘ (id_Γ ⊗ prev)
∘ diag` packaged at the linhom level; the total version extends it
trivially off the unit ball so `Phi_fun` is total in `prev` (the
Kleene chain stays inside the unit ball, so the off-ball behaviour
never matters for `Yfix_fun_lin`). The three layers are
`tensor_mor_R_lin Γ` (the `id ⊗ prev` tensor), `linhom_pre_act diag`
(pre-composition by the diagonal), and `linhom_post M`
(post-composition by the body).

### The fixpoint (`Yfix_fun_lin`, `Yfix_fun_lin_fixpoint`)

```coq
(* theories/programs/infra/em_fix.v *)
Definition Yfix_fun_lin : linhom_car Ar Gamma B :=
  linhom_lfp Phi_fun Phi_fun_incr Phi_fun_ball.

Lemma Yfix_fun_lin_norm_le1 : cone_norm Yfix_fun_lin <= 1.
Lemma Yfix_fun_lin_fixpoint : Phi_fun Yfix_fun_lin = Yfix_fun_lin.
```

`linhom_lfp` is the unit-ball Kleene-cascade supremum
`sup_n (Phi_fun)^n precone_zero` over the ω-CPO of `linhom_car Ar Γ
B`; the fixpoint identity then follows from `Phi_fun_cont` (the
ω-continuity of the Kleene step in all three layers).

### Parametricity in the codomain coalgebra

`Yfix_fun_lin` is parametric in any `B : ICone.type Ar` — the
construction does not depend on a `!`-coalgebra structure on `B`. In
particular `ppl_cbv.v` instantiates it at three different `B`:
- `B = bang_cofree (linhom A1 A2)` for the `ne_fix` clause (the
  cofree coalgebra on the clean internal hom of the function-type
  case — an OCaml-style `let rec` at function types);
- `B = coalg_obj (tyD_cbv t)` for any `t` with `is_free_coalg_type
  t` true, for `ne_fix_mr` (the §9.7 base-type coalgebra
  `FMeas_coalgebra X`, the §9.7 boolean coalgebra `bool_cone_coalg`,
  or any `EM_prod` thereof);
- non-cofree `B` (e.g. `FMeas_coalgebra X` directly, or
  `bool_cone_coalg`) when a recursive function returns a base or
  boolean value.

This uniform-in-`B` shape is what makes the design work across all
CBV types — the unit ball ω-CPO of `linhom_car Ar Γ B` exists for
every integrable cone `B`, no coalgebra structure required.

### Cross-reference to the SCones side (`Yfix` of paper §9.2)

The CBN counterpart is `Yfix : scones_hom BB B` of
`theories/stable/fixpoint.v` (= paper §9.2): the Kleene fixpoint at
the corresponding `SCones` internal hom `stablehom B B → B`. Same
arithmetic — a unit-ball Kleene chain from `precone_zero`, taken as
a supremum — at the stable-and-measurable categorical level. The CBV
side runs the same recipe at the `linhom` level instead.

---

## Beyond the paper — The boolean cascade

The 2-point cone of paper §4.4 / Theorem 4.24 — the coproduct
`1 ⊕ 1` — is built concretely as `bool_cone_car Ar : {nonneg R} ×
{nonneg R}` with norm `‖(p, q)‖ = p + q`, with its full HB tower, its
universal co-pairing as a linhom and an icones_hom, and a CBN-side
`scones_hom` packaging via `ders`. Consumed by the CBV `if_icones`
combinator of `ppl_cbv.v` and by the CBN `cbn_if_clause` of
`ppl_cbn.v`.

| Construction | Rocq |
|---|---|
| The 2-point ICone with full HB tower | `bool_cone_car`, `bool_dirac_true`, `bool_dirac_false` — `theories/programs/infra/bool_cone.v` |
| The universal co-pairing | `bool_case`, `bool_case_true`, `bool_case_false`, `bool_case_linear`, `bool_case_omega_continuous`, `bool_case_norm_le1`, `bool_case_pres_path`, `bool_case_pres_int` — same file |
| Unit-ball-free variants | `bool_case_omega_continuous_gen`, `bool_case_norm_le_max`, `bool_case_pres_path_gen`, `bool_case_pres_int_gen` — same file |
| Test measurability, generalised | `test_meas_gen` — `theories/mcones/mcone.v` |
| Icones-hom packaging | `bool_case_linhom`, `bool_case_linhom_gen`, `bool_case_icones_hom` — `theories/programs/infra/bool_case_hom.v` |
| α / β decomposition | `alpha_linhom`, `beta_linhom`, `bool_case_linhom_gen_alpha_beta` — same file |
| SCones-side packaging (via paper Lem 7.31) | `bool_case_scones` — `theories/programs/infra/bool_case_scones.v` |
| CBV `if_icones` consumer (from the new interpreter) | `if_icones`, `if_under` — `theories/programs/ppl_cbv.v` |

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

### Icones-hom packaging (`bool_case_linhom`, `if_icones`)

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
(* theories/programs/ppl_cbv.v *)
Definition if_icones
    (G A : Coalgebra Ar)
    (m n : icones_hom Ar (coalg_obj G) (coalg_obj A))
    (b : icones_hom Ar (coalg_obj G)
                     (coalg_obj (@bool_cone_coalg R Ar))) :
    icones_hom Ar (coalg_obj G) (coalg_obj A).
```

The CBV value-level `if-then-else` combinator. Both branches `m`,
`n` are taken as `icones_hom G → A`, converted to linhoms, paired by
`bool_case_linhom`, uncurried over `bool_cone ⊗ G`, then composed
with the scrutinee via `em_pair_mor` and the braid. With the §9.7
`bool_cone_coalg` on the scrutinee side, no `der` dance is needed —
the scrutinee directly produces `bool_cone_car Ar`. Every step stays
at the `icones_hom` level — no Kleisli wrapping.

---

## Beyond the paper — The CBN arithmetic refinement (option-β)

The CBN denotation `eD_CBN` is parameterised over the effect clauses
(`cbn_sample_clause`, …, `cbn_if_clause`). The pragmatic *option-γ*
baseline (`cbn_const_clause`) makes `cbn_add_clause_def` /
`cbn_mul_clause_def` constant at `precone_zero` — the honest reading
given that under option-γ the unit type denotes the terminal cone
`Stop`. The *option-β* refinement replaces those clauses with
genuine bilinear arithmetic on `FMeas R_obj`, lifted from the FMeas
lax-monoidal map of paper §5 via the SCones-side bilinear bridge
above.

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
| CBV-side mass identities for the recursive example programs | The CBV analogues of `ex_geom_CBN_mass_one`, `ex_loop_CBN_headline`, `ex_almost_loop_p_CBN_mass_one_if_pos` / `_mass_zero_if_zero` against the `Yfix_fun_lin`-resolved `eD` of `ppl_cbv.v`. | The recursion infrastructure (`Yfix_fun_lin`, `Yfix_fun_lin_fixpoint`, `Yfix_fun_lin_norm_le1`) is in place, but the example-specific identities (mirroring the CBN-side `phi_bcascade` cascade replay) have not yet been written. Not blocked — follow-up work. |
| CBV mass / marginal identities for the QBS examples | The CBV-side analogues of `ex_random_constant_CBN_headline`, `ex_random_linear_arith_marginal_at`, `ex_bayes_linear_CBN_headline` against the linhom-valued `eD` of `ppl_cbv.v`. | The surface terms compile through `eD`; the structural reduction lemmas and measure-level identities have not yet been re-derived in the new comonoid-primitive setting. |
| Option-α refinement | Replace `tyD_CBN tunit := Stop` (terminal) by `Bang(FMeas *)` so `score` and the arithmetic constructors do not collapse to constants. | Needs a parallel `eD_CBN_full_alpha` interpretation and the corresponding `cbn_*_clause_alpha`; not yet packaged. |
| CBV / CBN soundness theorem | No proof that `⟦M⟧_CBV` and `⟦M⟧_CBN` agree in any sense. | The two interpretations target different categorical objects (CBV: linear morphisms between coalgebras; CBN: stable measurable functions between integrable cones); a soundness comparison is outside the current scope. |
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
echo "Print Assumptions eD."                      | \
  rocq top -Q theories Icones -l theories/programs/ppl_cbv.v
echo "Print Assumptions if_icones."               | \
  rocq top -Q theories Icones -l theories/programs/ppl_cbv.v
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
