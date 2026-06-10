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

The sections of this chapter: the type grammar and named contexts;
the free-coalgebra gating predicate; the pure, effectful and
recursive constructor groups of `named_expr`; the
canonical-structure variable-lookup machinery behind `#"x"`; and the
`ppl_named` surface notation.

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

The surface types are a five-constructor grammar — unit, an arbitrary
measurable base object `tbase X`, binary products, function types,
and a two-point boolean type — and a context is a list of
string-named typed bindings, defined in `theories/programs/ppl.v`.

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

The predicate characterises the surface types whose CBV
interpretation is a *free* `!`-coalgebra — function types and
products thereof. It is the gating predicate of the mutual-recursion
constructor `ne_fix_mr` below.

```coq
(* theories/programs/ppl.v *)
Fixpoint is_free_coalg_type (t : ppl_type Ar) : bool :=
  match t with
  | tfun _ _ => true
  | tprod t1 t2 => is_free_coalg_type t1 && is_free_coalg_type t2
  | _ => false
  end.
```

### Pure term constructors (`ne_var`, `ne_tt`, `ne_pair`, `ne_fst`, `ne_snd`, `ne_lam`, `ne_app`, `ne_let`, `ne_real`, `ne_add`, `ne_mul`, `ne_true`, `ne_false`)

The pure fragment of `named_expr` is a standard intrinsically-typed
simply-typed lambda calculus with products, let, real constants,
arithmetic, and the two boolean values — thirteen constructors of
the single inductive in `theories/programs/ppl.v` (Section Syntax).

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

The effectful constructors are direct-style: `ne_sample` returns a
pure `tR'`, `ne_score` a pure `tunit`, `ne_bernoulli` a pure
`tbool`; the probability monad is hidden in the interpretation `eD`,
not in the source types.

```coq
(* theories/programs/ppl.v *)
Inductive named_expr : named_ctx Ar -> T -> Type :=
  (* … pure constructors above … *)
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

`ne_score` carries a measurable density `f : R → R` clipped to
`[0,1]` — the bound is needed by the unit-ball discipline of
`linhom_icones`.

### Recursion at function type (`ne_fix`)

OCaml-style `let rec`, restricted to function types: the body has
access to the recursive function via a fresh name `s : tfun t1 t2`
pushed onto the context, and the whole construct is again a value of
type `tfun t1 t2`.

```coq
(* theories/programs/ppl.v *)
Inductive named_expr : named_ctx Ar -> T -> Type :=
  (* … *)
  | ne_fix  : forall G s t1 t2,
      named_expr ((s, tfun t1 t2) :: G) (tfun t1 t2) ->
      named_expr G (tfun t1 t2)
```

The CBN interpretation routes through paper §9.2's `Yfix`. The CBV
interpretation in `theories/programs/ppl_cbv.v` resolves both
`ne_fix` and `ne_fix_mr` to the Kleene iteration `Yfix_fun_lin` of
`theories/programs/infra/em_fix.v` on the unit-ball CPO of the clean
`linhom`-cone — see
[The fixpoint](../../ppl/sections/ppl-sec-the-fixpoint.html).

### Mutual recursion at free-coalgebra types (`ne_fix_mr`)

`ne_fix_mr` generalises `ne_fix` to any body type `t` with
`is_free_coalg_type t = true` — in particular `t = tprod (tfun A1
B1) (tfun A2 B2)`, the mutual-recursion shape, where the two
components call each other via `fst #"s"` / `snd #"s"`.

```coq
(* theories/programs/ppl.v *)
Inductive named_expr : named_ctx Ar -> T -> Type :=
  (* … *)
  | ne_fix_mr : forall G s t,
      is_free_coalg_type t ->
      named_expr ((s, t) :: G) t -> named_expr G t.
```

CBN dispatches via `Yfix` at the product cone. CBV in
`theories/programs/ppl_cbv.v` routes `ne_fix_mr` through the same
`Yfix_fun_lin` of `theories/programs/infra/em_fix.v` as `ne_fix` —
the operator is parametric in the codomain cone, so the same recipe
handles both function types and any free-coalgebra type.

### Variable lookup by canonical structures (`tagged_nctx`, `find_nv`, `found_nv`, `recurse_nv`, `ne_var'`)

Writing `#"x"` makes Rocq's canonical-structure search find the
named context, the type, and the `named_var` witness of the binding
`"x"` all at once — the Saito–Affeldt APLAS 2023 §5.2 `find`
structure, transplanted to `named_ctx` in `theories/programs/ppl.v`.

The search is driven by two canonical instances over a tagged
context: `found_nv` (head case — the sought string is the head
binding) is tried first; otherwise the tag unfolds to `recurse_nctx`
and `recurse_nv` recurses on the tail, with the "different string"
side-condition discharged by `infer (String.eqb s y = false)` — a
`vm_compute`-reducible boolean disequality witness for the concrete
strings occurring in programs.

```coq
(* theories/programs/ppl.v *)
Structure tagged_nctx (R : realType) (Ar : MeasSubcat R) :=
  Tag_nctx { untag_nctx : named_ctx Ar }.

(** The [find_nv s t] structure: a tagged context together with a proof
    that the string [s] is bound to type [t] in that context. *)
Structure find_nv (R : realType) (Ar : MeasSubcat R)
    (s : string) (t : ppl_type Ar) : Type := Find_nv {
  fn_ctx  : tagged_nctx Ar;
  fn_proof : named_var (untag_nctx fn_ctx) t
}.

(** Canonical instance 1 (head case). *)
Canonical found_nv (R : realType) (Ar : MeasSubcat R)
    (s : string) (t : ppl_type Ar) (G : named_ctx Ar) :
    find_nv s t :=
  @Find_nv R Ar s t (found_nctx ((s, t) :: G)) (nv_head s t G).

(** Canonical instance 2 (tail case): driven by
    [infer (String.eqb s y = false)]. *)
Canonical recurse_nv (R : realType) (Ar : MeasSubcat R)
    (s : string) (t : ppl_type Ar) (y : string)
    (sty : ppl_type Ar) (Hneq : infer (String.eqb s y = false))
    (g : find_nv s t) : find_nv s t :=
  @Find_nv R Ar s t
    (recurse_nctx ((y, sty) :: untag_nctx (fn_ctx g)))
    (nv_tail y sty (untag_nctx (fn_ctx g)) (fn_proof g)).

(** [ne_var'] — the canonical-structure-driven [ne_var]; the [# x]
    notation elaborates to [ne_var' x _]. *)
Definition ne_var' (R : realType) (Ar : MeasSubcat R) (R_obj : ar_obj Ar)
    (s : string) (t : ppl_type Ar) (g : find_nv s t) :
    @named_expr R Ar R_obj (untag_nctx (fn_ctx g)) t :=
  ne_var (fn_proof g).
```

### Surface notation (the `ppl_named` custom entry)

A custom grammar entry `ppl_named` (opened by `Declare Custom Entry
ppl_named` in the source) gives the examples an OCaml-flavoured
direct-style surface syntax: `[ … ]` enters the entry, `# x` is
variable lookup, and `Sample` / `Score` / `Bernoulli` / `if` / `\` /
`let` / `fix` / `fix_mr` map one-to-one onto the constructors.

```coq
(* theories/programs/ppl.v — after [Declare Custom Entry ppl_named] *)
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
EM(!) object carries by Mellies' Proposition 28.*

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

The sections of this chapter: the type and context translations; the
EM cartesian primitives the interpreter is assembled from; the
clause-by-clause interpreter `eD_cbv` / `eD`; the constant-effect
helpers; the value-level `if_icones`; the definitional-unfolding
regression pack; and the semantic recursion-unfolding equation.

| Construction | Rocq |
|---|---|
| Type translation (no `Tobj` on `tfun`) | `tyD_cbv` — `theories/programs/ppl_cbv.v` |
| Context translation | `ctxD_cbv` — same file |
| Variable lookup (projection chain) | `var_lookup_cbv` — same file |
| Constant `icones_hom` helpers (`sample`, `real`, `true`/`false`, `bernoulli`) | `sample_icones`, `real_icones`, `true_icones`, `false_icones`, `bernoulli_icones` — same file |
| If-then-else combinator at the icones level | `if_icones`, `if_under` — same file |
| Internal icones-valued term interpretation | `eD_cbv` — same file |
| Public linhom-valued term interpretation | `eD` — same file |
| EM cartesian primitives (`δ`, `ε`, projections, pairing) | `coalg_d`, `coalg_e`, `em_proj1_mor`, `em_proj2_mor`, `em_pair_mor`, `em_term_mor` — `theories/homs/em_cartesian.v`; cartesian-η `em_pair_mor_proj_id` — `theories/programs/infra/cbv_adjunction.v` |
| Definitional-unfolding pack (one lemma per clause) | `eD_var_E` … `eD_fix_mr_E` (19 lemmas) — `theories/programs/ppl_cbv.v` (Section EDUnfold) |
| Recursion-unfolding equation | `eD_cbv_fix_unfold`, `eD_fix_unfold` — same file |

### Type translation (`tyD_cbv`)

Each surface type is sent to a `!`-coalgebra: `tunit` to the
terminal coalgebra, `tbase X` to the Theorem 9.7 coalgebra on `FMeas
X`, `tbool` to the §9.7-style coalgebra on the 2-point cone, `tprod`
to the EM cartesian product, and `tfun t1 t2` to the cofree
coalgebra on the *clean* internal hom `U⟦t1⟧ ⊸ U⟦t2⟧`.

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

The `tbase` clause is the
[Thm 9.7 coalgebra](../../paper/entries/thm-9-7.html) of
`theories/homs/coalgebra.v`; the `tbool` clause uses
`bool_cone_coalg` of `theories/programs/infra/bool_cone_coalg.v` —
see [the §9.7 coalgebra on the 2-point
cone](../../ppl/sections/ppl-sec-the-sec-9-7-coalgebra-on-the-2-point-cone.html).
Both choices give the *shared-sample* semantics expected of a PPL:
`let x = Bernoulli(p) in (x, x)` denotes the diagonal pushforward
`p·(T, T) + (1-p)·(F, F)`, not the independent product `µ ⊗ µ` that
a cofree `bang_cofree (bool_cone_car Ar)` would give. There is no
`Tobj` wrap anywhere: function values are clean linear maps.

### Context translation (`ctxD_cbv`)

A context denotes the right-nested iterated EM product of its types'
coalgebras, with the terminal coalgebra `EM_term` at the nil case;
variable lookup is then the evident chain of `em_proj1` /
`em_proj2` projections (`var_lookup_cbv`, same file), using only the
comonoid counits — no diagonal, no strength.

```coq
(* theories/programs/ppl_cbv.v *)
Fixpoint ctxD_cbv (G : ppl_ctx Ar) : Coalgebra Ar :=
  match G with
  | nil     => EM_term
  | t :: G' => EM_prod (ctxD_cbv G') (tyD_cbv t)
  end.

Fixpoint var_lookup_cbv (G : ppl_ctx Ar) (t : ppl_type Ar)
    (v : has_var G t) {struct v} :
    coalg_hom (ctxD_cbv G) (tyD_cbv t) :=
  match v in has_var G0 t0 return coalg_hom (ctxD_cbv G0) (tyD_cbv t0) with
  | hv_zero G' t' => em_proj2 (ctxD_cbv G') (tyD_cbv t')
  | hv_succ G' t' s v' =>
      coalg_comp (var_lookup_cbv v') (em_proj1 (ctxD_cbv G') (tyD_cbv s))
  end.
```

### EM cartesian primitives (`coalg_d`, `coalg_e`, `em_pair_mor`, `em_proj1_mor`, `em_proj2_mor`, `em_term_mor`)

Every `!`-coalgebra carries a commutative comonoid `(δ, ε) =
(coalg_d, coalg_e)` transported from the Seely comonoid on its
cofree resolution, and these comonoids make `(EM(!), ⊗, 1)`
cartesian — pairing, projections and the terminal morphism are all
definable from `(δ, ε)` alone. This is the entire toolbox the CBV
interpreter branches on.

The constructions live in `theories/homs/em_cartesian.v` (Melliès
§7.4 Prop 28 / Cor 20 — see the Paper-tab pages [EM(!) is fully
cartesian](../../paper/beyond/beyond-em.html) and [Cartesian-η of
EM(!)](../../paper/beyond/beyond-cartesian-of-em.html)); the
unbundled cartesian-η identity `em_pair_mor_proj_id` is exposed in
`theories/programs/infra/cbv_adjunction.v` (Section EmPairProjId)
and proved by promoted-point extensionality on the cofree pair, then
transported along the `coalg_str` retract.

```coq
(* theories/homs/em_cartesian.v *)

(** Eq 88 (diagonal): [coalg_d = (ε⊗ε) ∘ d_{!A} ∘ a : A ⊸ A⊗A]. *)
Definition coalg_d (P : Coalgebra Ar) :
    icones_hom Ar (coalg_obj P) (coalg_obj P ⊗ coalg_obj P) :=
  icones_comp (tensor_mor (der (coalg_obj P)) (der (coalg_obj P)))
    (icones_comp (d_bang (coalg_obj P)) (coalg_str P)).

(** Eq 88 (counit): [coalg_e = e_{!A} ∘ a : A ⊸ 1]. *)
Definition coalg_e (P : Coalgebra Ar) :
    icones_hom Ar (coalg_obj P) (cone_one_car Ar) :=
  icones_comp (e_bang (coalg_obj P)) (coalg_str P).

(** The pairing [⟨f,g⟩ = (f⊗g) ∘ d_Z]. *)
Definition em_pair_mor (Z P Q : Coalgebra Ar)
    (f : icones_hom Ar (coalg_obj Z) (coalg_obj P))
    (g : icones_hom Ar (coalg_obj Z) (coalg_obj Q)) :
    icones_hom Ar (coalg_obj Z) (coalg_obj P ⊗ coalg_obj Q) :=
  icones_comp (tensor_mor f g) (coalg_d Z).

(** The projections [π₁ = ρ_P ∘ (id_P ⊗ coalg_e Q)] (and dually π₂). *)
Definition em_proj1_mor (P Q : Coalgebra Ar) :
    icones_hom Ar (coalg_obj P ⊗ coalg_obj Q) (coalg_obj P) :=
  icones_comp (iso_fwd (tensor_runit (coalg_obj P)))
    (tensor_mor (icones_id Ar (coalg_obj P)) (coalg_e Q)).

(** [coalg_e P] is the canonical morphism [P → EM_term]. *)
Definition em_term_mor (P : Coalgebra Ar) :
    coalg_hom P EM_term :=
  MkCoalgHom (emc_e_mor (EMComon_all P)).
```

```coq
(* theories/programs/infra/cbv_adjunction.v (Section EmPairProjId) *)
(** Cartesian-η: pairing the two projections is the identity. *)
Lemma em_pair_mor_proj_id (P Q : Coalgebra Ar) :
  @em_pair_mor R Ar (EM_prod P Q) P Q (em_proj1_mor P Q) (em_proj2_mor P Q)
  = icones_id Ar (coalg_obj (EM_prod P Q)).
```

### Term interpretation (`eD_cbv`, `eD`)

The interpreter is uniformly comonoid-primitive: every branching
node (let, pair, app, if, arithmetic, boolean) uses the `δ_Γ`
diagonal of the context to give each sub-term its own copy of `Γ`;
multi-use of a free variable is then free in the cone. The cofree
exponential `!̃` appears only at two boundaries — `ne_lam`, where the
body is curried and promoted via `adj_psi` of the `U⊣!̃` adjunction,
and `ne_app`, where the function value is dereferenced via `der`
before evaluation.

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
[The fixpoint](../../ppl/sections/ppl-sec-the-fixpoint.html)); the
diagonal `coalg_d (ctxD_cbv (drop_names G0))` supplies the
context-coalgebra comonoid `δ_Γ` used inside the Kleene step. Every
other clause is built from the SMC primitives (`linhom_comp`,
`tensor_mor`, `tensor_braid`, `tensor_curry` / `tensor_uncurry`) and
the coalgebra-comonoid pair (`coalg_d`, `coalg_e`) only.

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

### If-then-else at the icones level (`if_icones`, `if_under`)

The CBV value-level if-then-else takes two branches `m, n :
icones_hom G → A` and a scrutinee `b : G → bool_cone` and returns a
clean `icones_hom G → A`, with no Kleisli wrapping at any step. It
is the *single* consumer-side packaging of the boolean cascade: the
branches are co-paired by `bool_case_linhom`, SMCC-uncurried over
`bool_cone ⊗ G`, braided, and finally pre-composed with the EM
pairing `⟨id_G, b⟩`.

```coq
(* theories/programs/ppl_cbv.v (Section IfICones) *)
Definition if_under :
    icones_hom Ar
      (tensor Ar (coalg_obj G) (bool_cone_car Ar))
      (coalg_obj A) :=
  icones_comp if_uncurried
    (iso_fwd (tensor_braid (coalg_obj G) (bool_cone_car Ar))).

Definition if_icones (b : icones_hom Ar (coalg_obj G)
                            (coalg_obj (@bool_cone_coalg R Ar))) :
    icones_hom Ar (coalg_obj G) (coalg_obj A) :=
  icones_comp if_under
    (@em_pair_mor R Ar G G (@bool_cone_coalg R Ar)
       (icones_id Ar (coalg_obj G)) b).
```

With the §9.7 `bool_cone_coalg` on the scrutinee side, no `der`
dance is needed — the scrutinee directly produces `bool_cone_car
Ar`. The building blocks (`bool_case_linhom`, the 2-point cone, the
§9.7 coalgebra) are documented in [the boolean-cascade
chapter](../../ppl/chapters/ppl-ch-the-boolean-cascade.html).

### The definitional-unfolding pack (`eD_var_E` … `eD_fix_mr_E`)

One lemma per `eD_cbv` clause — 19 in total, one for each
`named_expr` constructor — pins the exact clause body of the
interpreter, so any refactor of `eD_cbv` (or of the combinators it
is built from) breaks loudly in a named lemma instead of silently
changing the semantics.

Because `eD_cbv` is a structural `Fixpoint`, every clause reduces
definitionally on its constructor and every proof is `by []`. The
pack lives at the end of `theories/programs/ppl_cbv.v` (Section
EDUnfold); three representative members:

```coq
(* theories/programs/ppl_cbv.v (Section EDUnfold) *)
(** [ne_var]: pure projection from the context tensor. *)
Lemma eD_var_E (G : named_ctx Ar) (t : ppl_type Ar) (v : named_var G t) :
  eD_cbv' (ne_var v) = ch_mor (var_lookup_cbv (named_var_to_has_var v)).
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

(** [ne_fix]: the Kleene value-fixpoint [Yfix_fun_lin]. *)
Lemma eD_fix_E (G : named_ctx Ar) (s : string) (t1 t2 : ppl_type Ar)
    (M : @named_expr R Ar R_obj ((s, tfun t1 t2) :: G) (tfun t1 t2)) :
  eD_cbv' (ne_fix s M) =
  linhom_icones
    (Yfix_fun_lin (coalg_d (ctxD_cbv (drop_names G))) (eD_cbv' M))
    (Yfix_fun_lin_norm_le1 _ _).
Proof. by []. Qed.

(* … 16 more: eD_tt_E, eD_pair_E, eD_fst_E, eD_snd_E, eD_lam_E,
   eD_app_E, eD_sample_E, eD_real_E, eD_score_E, eD_add_E, eD_mul_E,
   eD_true_E, eD_false_E, eD_bernoulli_E, eD_if_E, eD_fix_mr_E. *)
```

### The recursion-unfolding equation (`eD_cbv_fix_unfold`, `eD_fix_unfold`)

The denotation of `fix s. body` equals the denotation of the body
run with the fixpoint itself bound to the recursive variable —
`⟦fix s. body⟧ = ⟦body⟧ ∘ ⟨id_Γ, ⟦fix s. body⟧⟩` — first at the
`icones_hom` level, then re-exported at the public linhom level.

The proof is the semantic payoff of the Kleene construction: by
`Yfix_fun_lin_fixpoint` the fixpoint is invariant under the Kleene
step `Phi_fun diag M prev = M ∘ (id_Γ ⊗ prev) ∘ δ_Γ`, and that step
is *exactly* the `em_pair_mor`-composite on the right-hand side
(unfolded via `Phi_fun_unit` on the unit ball). One bookkeeping
subtlety: `em_fix.v` and the `ne_fix` clause package the same
unit-ball linhom through two *propositionally* equal `linhom_icones`
records (their integral-preservation proofs are distinct opaque
constants), bridged by `icones_hom_eq`.

```coq
(* theories/programs/ppl_cbv.v (Section EDUnfold) *)
Lemma eD_cbv_fix_unfold (G : named_ctx Ar) (s : string)
    (t1 t2 : ppl_type Ar)
    (body : @named_expr R Ar R_obj ((s, tfun t1 t2) :: G) (tfun t1 t2)) :
  eD_cbv' (ne_fix s body) =
  icones_comp (eD_cbv' body)
    (em_pair_mor (icones_id Ar (coalg_obj (ctxD_cbv (drop_names G))))
                 (eD_cbv' (ne_fix s body))).

(** The same equation at the public linhom level. *)
Lemma eD_fix_unfold (G : named_ctx Ar) (s : string) (t1 t2 : ppl_type Ar)
    (body : @named_expr R Ar R_obj ((s, tfun t1 t2) :: G) (tfun t1 t2)) :
  eD' (ne_fix s body) =
  icones_to_linhom
    (icones_comp (eD_cbv' body)
       (em_pair_mor (icones_id Ar (coalg_obj (ctxD_cbv (drop_names G))))
                    (eD_cbv' (ne_fix s body)))).
```

---

## Beyond the paper — Call-by-name interpretation (SCones)

**Definition (CBN interpretation).** *Each type `τ` denotes an
integrable cone `⟦τ⟧_n` in `SCones`; each well-typed program
`Γ ⊢ M : τ` denotes a stable and measurable function
`⟦M⟧_n : ⟦Γ⟧_n → ⟦τ⟧_n`. Recursion at any free-coalgebra type is
the fixpoint operator `Yfix` of paper §9.2.*

The sections of this chapter: the type translation and its QBS
reading; the clause-parametric interpreter `eD_CBN`; the two
recursion clauses; and the concrete instantiations `eD_CBN_full` /
`eD_CBN_complete` / `eD_CBN_full_arith` used by every headline.

| Construction | Rocq |
|---|---|
| Type translation | `tyD_CBN` — `theories/programs/ppl_cbn.v` |
| CBN context translation | `ctxD_CBN` — same file |
| Term interpretation (pure fragment) | `eD_CBN`, `var_lookup_CBN` — same file |
| Recursion clause | `eD_CBN_fix_E` (the `Yfix`-as-free-recursion identity) — same file |
| Mutual recursion clause | `eD_CBN_fix_mr_E` — same file |
| Effect clauses (hypothesised) | `cbn_sample_clause` … `cbn_if_clause` — same file |
| Instantiated denotations (γ / M4 / β) | `eD_CBN_full` — `theories/programs/ppl_cbn_eff.v`; `eD_CBN_complete` — `theories/programs/ppl_cbn_headlines.v`; `eD_CBN_full_arith` — `theories/programs/ppl_cbn_arith_eff.v` |

### CBN type translation (`tyD_CBN`)

The base type `tbase X` denotes the cone `FMeas X` *directly* — no
`Bang` lift — the pragmatic QBS reading of
Heunen–Kammar–Staton–Yang, where a probabilistic program of base
type *is* a sub-probability measure. Function types denote the
internal hom `stablehom` of paper §7.32, products the SCones
`sprod`, the unit the terminal `Stop`, and `tbool` the 2-point cone
of `bool_cone.v`. Effects live inside the type interpretation; there
is no `Tobj` wrap on the codomain.

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

Contexts follow by iterated `sprod` (`ctxD_CBN`, same file), with
variable lookup `var_lookup_CBN` the corresponding projection chain.

### CBN term interpretation (`eD_CBN`)

The interpreter maps the pure fragment to the cartesian-closed
structure of `SCones` (paper §7.32: `spair` / `sfst` / `ssnd` /
`curry` / `Ev`), recursion to `Yfix` of paper §9.2, and dispatches
every effect constructor through a *hypothesised* clause — the CBN
interpretation is parametric over its effect clauses.

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

Concrete clause instances are wired in by the instantiated
denotations below.

### Recursion clause (`eD_CBN_fix_E`, `Yfix`)

The denotation of `fix s. body` is a genuine fixpoint of the body:
applying `⟦body⟧` (curried, at the current environment `g`) to
`⟦fix s. body⟧ g` gives back `⟦fix s. body⟧ g`, for every unit-ball
environment.

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

A single line via [paper §9.2's
`Yfix`](../../paper/entries/sect-9-2.html). The CBN win: no bilinear
bridge obligation, free recursion at *every* function type.

### Mutual-recursion clause (`eD_CBN_fix_mr_E`)

Same fixpoint identity as `eD_CBN_fix_E`, with the function type
`tfun t1 t2` replaced by an arbitrary body type `t` — the CBN side
has no scope restriction at `ne_fix_mr`, because `Yfix` of paper
§9.2 works at *any* integrable cone, including `tprod (tfun A1 B1)
(tfun A2 B2)` (the mutually-recursive function pair).

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

### The instantiated CBN denotations (`eD_CBN_full`, `eD_CBN_complete`, `eD_CBN_full_arith`)

Three concrete instantiations of the clause-parametric `eD_CBN`,
forming the actual interpreters that every CBN headline of
[EXAMPLES.md](../../examples/index.html) is stated against:
`eD_CBN_full` fixes the five effect clauses (sample / real / score /
add / mul, option-γ constants), `eD_CBN_complete` additionally fixes
the four boolean clauses, and `eD_CBN_full_arith` swaps the add/mul
clauses for the honest option-β bilinear arithmetic.

The layering mirrors the delivery waves: `eD_CBN_full`
(`theories/programs/ppl_cbn_eff.v`, Section EDCBNFull) leaves the
boolean clauses as section variables; `eD_CBN_complete`
(`theories/programs/ppl_cbn_headlines.v`, Section EDCBNComplete)
closes them with the `cbn_*_clause_def` of `ppl_cbn_bool.v`;
`eD_CBN_full_arith` (`theories/programs/ppl_cbn_arith_eff.v`,
Section EDCBNFullArith) is identical except for
`cbn_add_clause_arith` / `cbn_mul_clause_arith` — see [the CBN
arithmetic
chapter](../../ppl/chapters/ppl-ch-the-cbn-arithmetic-refinement-option.html).
Each comes with `by []` reduction lemmas (`eD_CBN_full_sample_E`,
`eD_CBN_full_arith_add_E`, …) unfolding the instantiated clauses.

```coq
(* theories/programs/ppl_cbn_eff.v (Section EDCBNFull) *)
Definition eD_CBN_full (G : named_ctx Ar) (t : ppl_type Ar)
    (M : @named_expr R Ar R_obj G t) :
    scones_hom (ctxD_CBN (drop_names G)) (tyD_CBN t) :=
  @eD_CBN R Ar R_obj
    (@cbn_sample_clause_def R Ar R_obj)
    (@cbn_real_clause_def R Ar R_obj R_carrier_eq)
    (@cbn_score_clause_def R Ar R_obj)
    (@cbn_add_clause_def R Ar R_obj)
    (@cbn_mul_clause_def R Ar R_obj)
    cbn_true_clause cbn_false_clause cbn_bernoulli_clause cbn_if_clause
    G t M.
```

```coq
(* theories/programs/ppl_cbn_headlines.v (Section EDCBNComplete) *)
Definition eD_CBN_complete (G : named_ctx Ar) (t : ppl_type Ar)
    (M : @named_expr R Ar R_obj G t) :
    scones_hom (ctxD_CBN (drop_names G)) (tyD_CBN t) :=
  @eD_CBN_full R Ar R_obj R_carrier_eq
    (@cbn_true_clause_def R Ar)
    (@cbn_false_clause_def R Ar)
    (@cbn_bernoulli_clause_def R Ar)
    (@cbn_if_clause_def R Ar)
    G t M.
```

---

## Beyond the paper — The Bernoulli-cascade framework

The shared mathematical core of `ppl_cbn_geom.v` and
`ppl_cbn_almost_loop.v`: a single SCones endomorphism scheme that
realises the body of a `if Bernoulli(p) then halt else cont_op µ`
recursion, with the closed-form Kleene cascade `mass(k^n) = 1 −
(1−p)^n` and its `sfix` headlines. Both `ex_geom` and
`ex_almost_loop p` are *instances* of this framework.

The sections of this chapter: the cascade operator itself; the
Kleene chain and its per-iterate mass recurrence; and the closed
form with the two `sfix`-level mass headlines.

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

The cascade operator is the SCones endomorphism on `FMeas R_obj`
that, on the unit ball, computes `µ ↦ p·halt + (1−p)·cont_op(µ)` —
the one-step body of a Bernoulli-guarded recursion, parametric in
the halting measure `halt` and the continuation operator `cont_op`.

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

It is built as `Ev ∘ spair (bool_case_linhom of (halt, cont_op) over
Bernoulli(p)) id` — the universal co-pairing of [the boolean
cascade](../../ppl/chapters/ppl-ch-the-boolean-cascade.html)
composed with the chosen continuation operator; the reduction rule
`phi_bcascade_E` mirrors `phi_CBN_geom_E` / `phi_almost_loop_p_E`.

### The Kleene chain and the mass recurrence (`kleene_bcascade`, `kleene_bcascade_S_E`, `kleene_bcascade_ball`, `kleene_bcascade_S_mass`, `kleene_bcascade_mass_cvg_if_pos`, `kleene_bcascade_mass_eq_zero_if_zero`)

The Kleene iterates `k(n) = phi_bcascade^n(0)` stay in the unit
ball, decompose per-iterate as `k(n+1) = p·halt + (1−p)·cont_op(k(n))`,
and their total masses obey the affine recurrence `mass(k(n+1)) =
p + (1−p)·mass(k(n))` whenever `halt` has mass 1 and `cont_op`
preserves mass on the unit ball.

```coq
(* theories/programs/infra/cbn_bernoulli_cascade.v (Section KleeneBCascade) *)
Definition kleene_bcascade (n : nat) : FMeas R_obj :=
  kleene (sc_fun phi_bc') n.

Lemma kleene_bcascade_ball (n : nat) :
  (cone_norm (kleene_bcascade n) <= 1)%R.

(** Per-iterate decomposition on the unit ball. *)
Lemma kleene_bcascade_S_E (n : nat) :
  kleene_bcascade n.+1 =
  (precone_add
    (precone_scale (NngNum Hp_ge0) (halt : FMeas R_obj))
    (precone_scale (NngNum (onem_ge0 p Hp_le1))
       (sc_fun cont_op (kleene_bcascade n) : FMeas R_obj))
   : FMeas R_obj).
```

```coq
(* theories/programs/infra/cbn_bernoulli_cascade.v *)
Lemma kleene_bcascade_S_mass (n : nat) :
  fmeas_mu (kleene_bcascade n.+1) [set: ar_carrier Ar R_obj]
  = (p%:E + (1 - p)%R%:E *
       fmeas_mu (kleene_bcascade n) [set: ar_carrier Ar R_obj])%E.

Lemma kleene_bcascade_mass_cvg_if_pos :
  (0 < p)%R ->
  fmeas_mu (kleene_bcascade n) [set: ar_carrier Ar R_obj]
    @[n --> \oo] --> (1 : \bar R).

Lemma kleene_bcascade_mass_eq_zero_if_zero (n : nat) :
  p = 0%R ->
  fmeas_mu (kleene_bcascade n) [set: ar_carrier Ar R_obj] = 0%E.
```

Proof shape of the closed form `kleene_bcascade_mass_closed` below:
induction on `n`; the base case is `fmeas_zeroE` at `precone_zero`;
the step rewrites by `kleene_bcascade_S_mass` (itself obtained from
`kleene_bcascade_S_E` via `fmeas_addE` / `fmeas_scaleE` and the two
mass hypotheses on `halt` / `cont_op`), then closes the algebra
`p + (1−p)(1 − (1−p)^n) = 1 − (1−p)^{n+1}` with `exprSr`. The
convergence lemma is then `cvg_expr` on `|1−p| < 1`; the vanishing
lemma is immediate from the closed form at `p = 0`.

### Closed form and headlines (`kleene_bcascade_mass_closed`, `sfix_bcascade_mass_one_if_pos`, `sfix_bcascade_mass_zero_if_zero`)

The mass of the `n`-th Kleene iterate is exactly `1 − (1−p)^n`, and
therefore the `sfix`-level fixpoint `sfix_bcascade` has total mass 1
whenever `p > 0` (and mass 0 when `p = 0`) — partial termination
with probability one, resp. honest divergence.

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

The bridge from per-iterate masses to the `sfix` mass is
`sfix_bcascade_mass_E` + `sfix_bcascade_sup_cvg` (monotone
convergence of `fmeas_mu` along the Kleene chain at `setT`), closed
by uniqueness of limits. Instantiate at `p := 1/2`, `halt := δ_0`,
`cont_op := shift_scones 1` for `ex_geom`'s `mass = 1`; at `p := p`,
`halt := δ_0`, `cont_op := scones_id` for `ex_almost_loop p`'s two
headlines — see the [Examples tab](../../examples/index.html).

---

## Beyond the paper — The SCones↔ICones-tensor bilinear stability bridge

The structural unblocker behind the honest CBN bilinear arithmetic
on `FMeas`. Given a measurable-stable `K : G → A` and a bilinear
`Φ : G ⊗ A → B` in `ICones`, the diagonal evaluation
`g ↦ Φ(g ⊗ K(g)) : G → B` is measurable-stable. Built by pure
structural composition through paper Theorem 5.12's
tensor↔internal-hom adjunction — no §7.3 finite-difference replay
required.

The sections of this chapter: the `linhom → stablehom` lift (paper
Lemma 7.31 at the internal hom); the diagonal bridge itself; and the
binary variant on the SCones product consumed by the CBN arithmetic.

| Construction | Rocq |
|---|---|
| Lifting `linhom → stablehom` is meas-stable (Lem 7.31 at internal-hom) | `linhom_to_stablehom`, `linhom_to_stablehom_meas_stable` — `theories/stable/diag_bilinear_tensor.v` |
| Composition with an `icones_hom` preserves meas-stability | `meas_stable_comp_post`, `meas_stable_comp_pre` — same file |
| The diagonal stable pairing | `id_spair_meas_stable`, `spair_meas_stable` — same file |
| **The deliverable** — diagonal bilinear stability bridge | `meas_stable_diag_bilinear_tensor` — same file |
| Binary variant on `sprod A B` | `meas_stable_bin_bilinear_tensor` — `theories/programs/ppl_cbn_arith_scones.v` |

### Lift `linhom → stablehom` (`linhom_to_stablehom`)

Every inhabitant of the internal hom `linhom_car Ar B C` is a stable
and measurable map of cones, and the packaging function
`linhom_to_stablehom : linhom_car Ar B C → stablehom B C` is *itself*
measurable-stable — the internal-hom version of paper Lemma 7.31.

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

The 0-extension off the unit ball is the standard `sc_clamp`.

### The deliverable (`meas_stable_diag_bilinear_tensor`)

For any measurable-stable `K : G → EA` and any bilinear
`Φ : G ⊗ EA → EB` (an `icones_hom` out of the tensor), the diagonal
evaluation `g ↦ Φ(g ⊗ K g)` is measurable-stable — the bridge that
lets a bilinear ICones map be applied along a stable argument
without leaving `SCones`.

The proof is pure structural composition through [paper Thm
5.12](../../paper/entries/thm-5-12.html): it rewrites the diagonal
through the tensor↔internal-hom adjunction, then assembles the lift
(the inner `linhom_to_stablehom` is meas-stable by Lemma 7.31
above), the post-composition with `tensor_curry Φ`
(`meas_stable_comp_post`), the diagonal pair
(`id_spair_meas_stable`), and paper Lemma 7.27 (`ev` is
meas-stable) — finally rescaling by linearity of `ev_fun` in its
first slot.

```coq
(* theories/stable/diag_bilinear_tensor.v *)
Lemma meas_stable_diag_bilinear_tensor
    (K : G -> EA)
    (Phi : icones_hom Ar (tensor Ar G EA) EB) :
  is_meas_stable K ->
  is_meas_stable (fun g : G => Phi (ptensor g (K g))).
(* Proof shape:
     g ↦ Φ(g ⊗p K g)
       = linhom_fun ((tensor_curry Φ) g) (K g)            -- Thm 5.12
       = ev_fun ⟨ (linhom_to_stablehom ∘ ders) (tensor_curry Φ) g,
                  K g ⟩
   then close by Lem 7.27 (ev) + the meas-stable closure lemmas. *)
```

### Binary variant (`meas_stable_bin_bilinear_tensor`)

For a bilinear `Φ : A ⊗ B → C`, the induced map on the SCones
product `sprod A B`, `p ↦ Φ(fst p ⊗ snd p)`, is measurable-stable —
the form consumed directly by the honest CBN arithmetic install.

```coq
(* theories/programs/ppl_cbn_arith_scones.v *)
Lemma meas_stable_bin_bilinear_tensor
    (Phi : icones_hom Ar (tensor Ar A B) C) :
  is_meas_stable
    (fun p : sprod A B => Phi (ptensor (sprod_fst p) (sprod_snd p))).
```

It is the diagonal bridge applied to `Phi_lift := Phi ∘ (icones_proj
true ⊗ id_B)` over the projection-then-second-component pairing.
Consumed by `add_FMeas_scones` / `mul_FMeas_scones` of
`ppl_cbn_arith_scones.v`.

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

The sections of this chapter: the Kleene step `Phi_fun`; the
fixpoint `Yfix_fun_lin` with its proved properties (and their
limits); and the cross-reference to the SCones-side `Yfix`.

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

The Kleene step sends a candidate denotation `prev : Γ ⊸ B` to
`M ∘ (id_Γ ⊗ prev) ∘ diag` — "run the body with `prev` bound to the
recursive variable" — packaged at the linhom level, and extended
trivially off the unit ball so the operator is total.

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

The three layers are `tensor_mor_R_lin Γ` (the `id ⊗ prev` tensor),
`linhom_pre_act diag` (pre-composition by the diagonal), and
`linhom_post M` (post-composition by the body). The Kleene chain
stays inside the unit ball, so the off-ball default `precone_zero`
never matters for `Yfix_fun_lin`.

### The fixpoint (`Yfix_fun_lin`, `Yfix_fun_lin_fixpoint`, `Yfix_fun_lin_norm_le1`)

`Yfix_fun_lin` is the supremum of the Kleene chain `(Phi_fun)^n
precone_zero` over the unit-ball ω-CPO of `linhom_car Ar Γ B`; it is
proved to stay in the unit ball (`Yfix_fun_lin_norm_le1`) and to
satisfy the fixpoint equation `Phi_fun (Yfix_fun_lin) =
Yfix_fun_lin` (`Yfix_fun_lin_fixpoint`).

```coq
(* theories/programs/infra/em_fix.v (Section PhiFun) *)
Definition Yfix_fun_lin : linhom_car Ar Gamma B :=
  linhom_lfp Phi_fun Phi_fun_incr Phi_fun_ball.

Lemma Yfix_fun_lin_norm_le1 : cone_norm Yfix_fun_lin <= 1.

(** The fixpoint equation: [Phi_fun (Yfix_fun_lin) = Yfix_fun_lin]. *)
Lemma Yfix_fun_lin_fixpoint : Phi_fun Yfix_fun_lin = Yfix_fun_lin.
```

The proof is organised as three obligations feeding the generic
`linhom_lfp` engine (same file, Section LinhomLFP): `Phi_fun_ball`
(the step preserves the unit ball — operator-norm bookkeeping
through the three layers), `Phi_fun_incr` (monotonicity on the unit
ball, by linearity of post-composition), and `Phi_fun_cont`
(ω-continuity, proved layer by layer: `tensor_mor_omega_cont_R` for
the tensor layer, then continuity of `linhom_pre_act` /
`linhom_post`). `linhom_lfp` then forms the chain `kleene_lin n =
iter n Phi_fun precone_zero` and takes `linhom_sup_ball`; the
fixpoint equation follows from `Phi_fun_cont` by the standard
exchange of `Phi_fun` with the supremum.

These three lemmas — construction, ball, fixpoint equation — are
what is proven about the operator. They do not by themselves yield
the mass identities of recursive example programs on the CBV side;
see *What is not formalised* below.

`Yfix_fun_lin` is parametric in any `B : ICone.type Ar` — the
construction does not depend on a `!`-coalgebra structure on `B`
(the unit-ball ω-CPO of `linhom_car Ar Γ B` exists for every
integrable cone `B`). `ppl_cbv.v` instantiates it at `B =
bang_cofree (linhom …)` for `ne_fix` and at `B = coalg_obj (tyD_cbv
t)` for any free-coalgebra `t` at `ne_fix_mr`; the same uniformity
is what lets one operator serve both recursion constructors.

### Cross-reference to the SCones side (`Yfix`)

The CBN counterpart is `Yfix : scones_hom BB B` of
`theories/stable/fixpoint.v` — [paper
§9.2](../../paper/entries/sect-9-2.html), in the [§9 paper
chapter](../../paper/sections/sec-9.html) orbit: the Kleene fixpoint
at the `SCones` internal hom `stablehom B B → B`, again a unit-ball
Kleene chain from `precone_zero` taken as a supremum.

```coq
(* theories/stable/fixpoint.v *)
(** Paper §9.2: the least-fixpoint combinator [Y], as a morphism of
    [SCones]. *)
Definition Yfix : scones_hom BB B :=
  MkSconesHom (sh_fun Yfix_elt) (sh_meas_stable Yfix_elt) Yfix_norm_le1
    (sh_offball Yfix_elt).
```

Same arithmetic at the stable-and-measurable categorical level; the
CBV side runs the recipe at the `linhom` level instead.

---

## Beyond the paper — The boolean cascade

The 2-point cone of [paper §4.4 / Theorem
4.24](../../paper/sections/sec-4.html) — the coproduct `1 ⊕ 1` — is
built concretely as `bool_cone_car Ar : {nonneg R} × {nonneg R}`
with norm `‖(p, q)‖ = p + q`, with its full HB tower, its universal
co-pairing as a linhom and an icones_hom, a CBN-side `scones_hom`
packaging via `ders`, and a hand-rolled §9.7-style `!`-coalgebra
structure giving the shared-sample semantics.

The sections of this chapter: the carrier; the universal co-pairing
`bool_case`; its linhom / icones / SCones packagings (with the α/β
decomposition); and the §9.7 coalgebra `bool_cone_coalg`.

| Construction | Rocq |
|---|---|
| The 2-point ICone with full HB tower | `bool_cone_car`, `bool_dirac_true`, `bool_dirac_false` — `theories/programs/infra/bool_cone.v` |
| The universal co-pairing | `bool_case`, `bool_case_true`, `bool_case_false`, `bool_case_linear`, `bool_case_omega_continuous`, `bool_case_norm_le1`, `bool_case_pres_path`, `bool_case_pres_int` — same file |
| Unit-ball-free variants | `bool_case_omega_continuous_gen`, `bool_case_norm_le_max`, `bool_case_pres_path_gen`, `bool_case_pres_int_gen` — same file |
| Test measurability, generalised | `test_meas_gen` — `theories/mcones/mcone.v` |
| Icones-hom packaging | `bool_case_linhom`, `bool_case_linhom_gen`, `bool_case_icones_hom` — `theories/programs/infra/bool_case_hom.v` |
| α / β decomposition | `alpha_linhom`, `beta_linhom`, `bool_case_linhom_gen_alpha_beta` — same file |
| SCones-side packaging (via paper Lem 7.31) | `bool_case_scones` — `theories/programs/infra/bool_case_scones.v` |
| The §9.7 coalgebra on `bool_cone_car` | `bool_coalg_str`, `bool_cone_coalg`, `bool_cone_dispatch` — `theories/programs/infra/bool_cone_coalg.v` |
| CBV `if_icones` consumer (from the interpreter) | `if_icones`, `if_under` — `theories/programs/ppl_cbv.v` |

### The 2-point cone (`bool_cone_car`)

The boolean value cone is the pair `(p, q)` of non-negative weights
on true and false, with norm `‖(p, q)‖ = p + q` — concretely the
paper §4.4 / Thm 4.24 coproduct `cone_one_car ⊕ cone_one_car`, with
the two Dirac basis points as the boolean values.

```coq
(* theories/programs/infra/bool_cone.v *)
Record bool_cone_car (dummy : MeasSubcat R) : Type :=
  MkBoolCone { bc_t : {nonneg R}; bc_f : {nonneg R} }.

Definition bool_dirac_true  : bool_cone_car Ar := MkBoolCone Ar 1%:nng 0%:nng.
Definition bool_dirac_false : bool_cone_car Ar := MkBoolCone Ar 0%:nng 1%:nng.
```

### The universal co-pairing (`bool_case`)

The co-pairing `[a, b](x) = bc_t(x)·a + bc_f(x)·b` realises the
coproduct universal property of [paper §4.4 / Thm
4.24](../../paper/sections/sec-4.html): it restores the branch
values on the two basis points, is linear in `x`, ω-continuous on
the unit ball, norm-bounded, and preserves measurable paths and
integrals.

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

The `_gen` variants drop the unit-ball hypotheses (with
`bool_case_norm_le_max` as the norm bound); the generalised test
measurability `test_meas_gen` of `theories/mcones/mcone.v` is what
lets the path-preservation proofs drop the unit ball on test
scrutinees.

### Icones-hom packaging (`bool_case_linhom`, `bool_case_icones_hom`, `alpha_linhom`, `beta_linhom`, `bool_case_scones`)

The co-pairing is packaged once at each categorical level in
`theories/programs/infra/bool_case_hom.v`: as a linhom
`bool_case_linhom : bool_cone ⊸ A` (with the unit-ball-free
`bool_case_linhom_gen`), as an icones_hom `bool_case_icones_hom`,
and — via paper Lemma 7.31 — as a CBN-side `scones_hom`
`bool_case_scones` in
`theories/programs/infra/bool_case_scones.v`.

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

The general variant decomposes as `bool_case_linhom_gen a b =
alpha_linhom a + beta_linhom b` (`bool_case_linhom_gen_alpha_beta`,
same file) — the α/β decomposition that reduces its integral- and
path-preservation obligations to the two scaled-projection linhoms
`alpha_linhom` / `beta_linhom`. The CBV consumer of this packaging
is `if_icones` — see [if-then-else at the icones
level](../../ppl/sections/ppl-sec-if-then-else-at-the-icones-level.html).

### The §9.7 coalgebra on the 2-point cone (`bool_coalg_str`, `bool_cone_coalg`, `bool_cone_dispatch`)

The 2-point cone carries a hand-rolled `!`-coalgebra structure
`bool_coalg_str : bool_cone ⊸ !bool_cone` mirroring [Theorem
9.7](../../paper/entries/thm-9-7.html)'s `FMeas_coalgebra`: the §9.7
integral `Coalg_X(µ) = ∫ prom(δ_x) dµ(x)` degenerates on the
two-point carrier to the finite sum `p·δ_T + q·δ_F ↦ p·prom(δ_T) +
q·prom(δ_F)`.

This is the structure that makes `tyD_cbv tbool` give *shared-sample*
semantics: the comonoid induced on `⟦tbool⟧` is the diagonal
pushforward, so `let x = Bernoulli(p) in (x, x)` denotes `p·(T,T) +
(1−p)·(F,F)` rather than the four-point independent product. The
two coalgebra laws (`bool_coalg_counit`, `bool_coalg_coassoc`)
reduce on the basis points to the comonad identities `der ∘ prom =
id` and `dig ∘ prom = prom ∘ prom`, dispatched by the
universal-property extensionality lemma `bool_cone_dispatch` (any
two linear morphisms out of the 2-point cone agreeing on `δ_T` and
`δ_F` are equal).

```coq
(* theories/programs/infra/bool_cone_coalg.v (Section BoolConeCoalg) *)
Definition bool_coalg_str : icones_hom Ar T (Bang Ar T) :=
  bool_case_icones_hom
    (prom (bool_dirac_true : T))
    (prom (bool_dirac_false : T))
    prom_bool_dirac_true_ball
    prom_bool_dirac_false_ball.

(** On the true basis: [bool_coalg_str(δ_T) = prom(δ_T)]. *)
Lemma bool_coalg_str_true :
  Lfun bool_coalg_str bool_dirac_true = prom (bool_dirac_true : T).

(** Universal-property dispatch: an [icones_hom] out of [T] is
    determined by its two basis values. *)
Lemma bool_cone_dispatch (B : ICone.type Ar)
    (f g : icones_hom Ar T B) :
  Lfun f bool_dirac_true = Lfun g bool_dirac_true ->
  Lfun f bool_dirac_false = Lfun g bool_dirac_false ->
  f = g.

(** Package as a [Coalgebra Ar]. *)
Definition bool_cone_coalg : Coalgebra Ar :=
  MkCoalgebra bool_coalg_counit bool_coalg_coassoc.
```

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

The sections of this chapter: the measure-theoretic `add_FMeas` /
`mul_FMeas`; their SCones packaging through the binary bridge; and
the option-β replacement clauses with `eD_CBN_full_arith`.

| Construction | Rocq |
|---|---|
| `add_FMeas` / `mul_FMeas` measure-theoretic foundation | `add_FMeas`, `add_FMeas_setT`, `add_FMeas_norm`, `add_FMeas_dirac`, `mul_FMeas`, `mul_FMeas_setT`, `mul_FMeas_norm`, `mul_FMeas_dirac` — `theories/programs/ppl_cbn_arith.v` |
| `linhom`-level bilinear `add_FMeas_lax_icones` / `mul_FMeas_lax_icones` | `add_FMeas_lax_icones`, `add_FMeas_lax_icones_pt`, `mul_FMeas_lax_icones`, `mul_FMeas_lax_icones_pt` — `theories/programs/ppl_cbn_arith_scones.v` |
| Lifting to a `scones_hom` via the binary bridge | `add_FMeas_pair_fun`, `add_FMeas_pair_fun_meas_stable`, `add_FMeas_scones`, `add_FMeas_scones_E`, `add_FMeas_scones_dirac` — same file |
| Replacement effect clauses (option-β) | `cbn_add_clause_arith`, `cbn_mul_clause_arith`, `cbn_add_clause_arith_E`, `cbn_mul_clause_arith_E` — `theories/programs/ppl_cbn_arith_eff.v` |
| Refined CBN denotation `eD_CBN_full_arith` | `eD_CBN_full_arith`, `eD_CBN_full_arith_add_E`, `eD_CBN_full_arith_mul_E` — same file |

### Measure-theoretic foundation (`add_FMeas`, `add_FMeas_dirac`)

`add_FMeas µ ν` is the pushforward of the pre-Fubini pairing
`fmeas_lax_pre µ ν` under measurable addition: bilinear in `(µ, ν)`,
with total mass the *product* of the masses, and sending a pair of
Diracs to the Dirac of the sum — the identity load-bearing for the
QBS-flagship Dirac reductions.

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

`mul_FMeas` is verbatim analogous with multiplication in place of
addition.

### SCones packaging (`add_FMeas_scones`, `add_FMeas_lax_icones`)

The bilinear arithmetic enters the categorical pipeline in two
steps: at the ICones level, `add_FMeas_lax_icones` is the composite
of paper §5's lax-monoidal `fmeas_lax` with the FMeas-functorial
action of the measurable `+`; at the SCones level, the binary
bilinear bridge packages it as a stable arrow on the SCones product.

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

The meas-stability obligation `add_FMeas_pair_fun_meas_stable` is
exactly `meas_stable_bin_bilinear_tensor` of [the bilinear
bridge](../../ppl/chapters/ppl-ch-the-sconesicones-tensor-bilinear-stability-bridge.html)
applied at `Phi := add_FMeas_lax_icones`.

### Option-β replacement clauses (`cbn_add_clause_arith`, `eD_CBN_full_arith`)

The option-β clauses interpret `ne_add` / `ne_mul` by composing
`add_FMeas_scones` / `mul_FMeas_scones` with the stable pairing of
the two sub-denotations, and `eD_CBN_full_arith` is `eD_CBN`
instantiated with them (and the option-γ baseline elsewhere) — the
interpreter behind the CBN-side honest QBS-flagship marginal
identity `ex_random_linear_arith_marginal_at` of EXAMPLES.md.

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

`eD_CBN_full_arith` sits alongside `eD_CBN_full` /
`eD_CBN_complete` — see [the instantiated CBN
denotations](../../ppl/sections/ppl-sec-the-instantiated-cbn-denotations.html).

---

## What is **not** formalised

A handful of PPL-side items are intentionally left open.

| Item | What it is | Why not yet |
|---|---|---|
| CBV-side mass identities for the recursive example programs | The CBV analogues of `ex_geom_CBN_mass_one`, `ex_loop_CBN_headline`, `ex_almost_loop_p_CBN_mass_one_if_pos` / `_mass_zero_if_zero` against the `Yfix_fun_lin`-resolved `eD` of `ppl_cbv.v`. | What is proven about `Yfix_fun_lin` is the Kleene construction, unit-ball preservation, and the fixpoint equation (plus the definitional/semantic unfolding lemmas of `ppl_cbv.v`). The recursive mass identities additionally need a refinement of the fixpoint seeding at function types — iterating *inside* the cofree wrap `!̃` rather than from the zero seed of the wrapped hom — which is not yet in place. |
| CBV mass / marginal identities for the QBS examples | The CBV-side analogues of `ex_random_constant_CBN_headline`, `ex_random_linear_arith_marginal_at`, `ex_bayes_linear_CBN_headline` against the linhom-valued `eD` of `ppl_cbv.v`. | The surface terms compile through `eD`; the structural reduction lemmas and measure-level identities have not yet been re-derived in the comonoid-primitive setting. |
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
echo "Print Assumptions eD_fix_unfold."           | \
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
