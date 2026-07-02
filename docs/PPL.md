# A direct-style PPL on top of the integrable-cones model

A typed probabilistic functional language sits on top of the paper's
categorical model. Each type denotes a `!`-coalgebra. Each program
denotes a *linear* morphism in `ICone`, between the underlying carriers
of the context and result coalgebras. Recursion at function type is
realised by a value-fixpoint *combinator* in the Eilenberg–Moore
category of `!`: the supremum of an interleaved Kleene chain, seeded at
the diverging function value and computed pointwise through a
`der`/`prom` sandwich.

The language is direct-style (Plotkin / Girard) and named-variable
(Saito–Affeldt APLAS 2023). Probabilistic effects live entirely in the
interpretation: there is no `tprob` type marker, no syntactic `return`,
no `bind`. A call-by-name interpretation of the same surface syntax
(through the cartesian closed `SCones` of paper §7) is preserved on the
`cbn-track` branch; main is CBV-only. Examples are listed in the
[Examples tab](../examples/).

The paper-side correspondence (§§ 2–9 ↔ Rocq) lives on the
[Paper tab](../paper/). This document covers what sits *above* the
paper: the surface language, its CBV interpretation, the fixpoint
and integral-law infrastructure, and the semantic correctness
statements one can make at the categorical level.

---

**Chapter map.** This tab has six chapters:

- [The surface language](../../ppl/chapters/ppl-ch-the-surface-language.html) — the intrinsically-typed syntax, the `tProb` probability type, and the witness-free surface forms.
- [Call-by-value interpretation](../../ppl/chapters/ppl-ch-call-by-value-interpretation-linhom-comonoid.html) — `eD`, the linhom + comonoid interpreter, clause by clause.
- [The SCones↔ICones-tensor bilinear stability bridge](../../ppl/chapters/ppl-ch-the-sconesicones-tensor-bilinear-stability-bridge.html) — the `stable/` infrastructure the value-fixpoint consumes.
- [The CBV value-fixpoint at function types](../../ppl/chapters/ppl-ch-the-cbv-value-fixpoint-at-function-types.html) — `fix_comb`, its seeded Kleene core, and the mutual-recursion transport.
- [CBV semantic laws and regression anchors](../../ppl/chapters/ppl-ch-cbv-semantic-laws-and-regression-anchors.html) — the equational layer and the marginal / conditioning results.
- [The boolean cascade](../../ppl/chapters/ppl-ch-the-boolean-cascade.html) — the 2-point cone and its §9.7 coalgebra.

## The surface language

**In this chapter:** [Def 1.1](../../ppl/sections/ppl-sec-def-1-1-types-and-contexts.html) · [Def 1.2](../../ppl/sections/ppl-sec-def-1-2-free-coalgebra-types.html) · [Def 1.3](../../ppl/sections/ppl-sec-def-1-3-pure-term-constructors.html) · [Def 1.4](../../ppl/sections/ppl-sec-def-1-4-effectful-term-constructors.html) · [Def 1.5](../../ppl/sections/ppl-sec-def-1-5-measurable-function-application.html) · [Def 1.6](../../ppl/sections/ppl-sec-def-1-6-runtime-parameter-distributions.html) · [Def 1.7](../../ppl/sections/ppl-sec-def-1-7-recursion-at-function-type.html) · [Def 1.8](../../ppl/sections/ppl-sec-def-1-8-mutual-recursion-at-free-coalgebra-types.html) · [Def 1.9](../../ppl/sections/ppl-sec-def-1-9-variable-lookup-by-canonical-structures.html) · [Def 1.10](../../ppl/sections/ppl-sec-def-1-10-surface-notation.html) · [Def 1.11](../../ppl/sections/ppl-sec-def-1-11-probability-type-and-bundle.html) · [Def 1.12](../../ppl/sections/ppl-sec-def-1-12-bernoulli-coins.html) · [Def 1.13](../../ppl/sections/ppl-sec-def-1-13-score-reweighting.html) · [Def 1.14](../../ppl/sections/ppl-sec-def-1-14-sigmoid-gausslik-and-gt0-primitives.html) · [Def 1.15](../../ppl/sections/ppl-sec-def-1-15-the-test-function-coin.html) · [Def 1.16](../../ppl/sections/ppl-sec-def-1-16-const-and-inclp.html) · [Def 1.17](../../ppl/sections/ppl-sec-def-1-17-the-observe-operator.html) · [Def 1.18](../../ppl/sections/ppl-sec-def-1-18-sampling-the-comparison-coin-and-let-rec.html) · [Def 1.19](../../ppl/sections/ppl-sec-def-1-19-reject-condition-combinators.html) · [Law 1.20](../../ppl/sections/ppl-sec-law-1-20-scores-densities-and-the-sub-probability-boundary.html).

The source language is a simply-typed lambda calculus with sampling,
scoring, recursion at function type, a two-point boolean type, and
mutual recursion at any free-coalgebra type. Its syntax is one
intrinsically-typed inductive `named_expr` $\Gamma\ \tau$ in
named-variable style, indexed by a *named* context
`named_ctx` $=$ `seq (string × ppl_type)`, and consumed by the CBV
interpretation `eD` of the next chapter. This chapter covers the
constructor groups of the inductive, the canonical-structure machinery
behind variable lookup, and the two notation layers: the kernel
`ppl_named` grammar and the readable forms derived on top of it.

| Construction | Rocq |
|---|---|
| Types `tunit`, `tbase X`, `tprod`, `tfun`, `tbool` | `ppl_type` — `theories/programs/ppl.v` |
| Named contexts | `named_ctx`, `drop_names` — same file |
| Named variables (witness) | `named_var`, `nv_head`, `nv_tail` — same file |
| Term constructors | `named_expr` (the 23 constructors below) — same file |
| Free-coalgebra type predicate (gating `ne_fix_mr`) | `is_free_coalg_type` — same file |
| Measurable function application (pushforward) | `ne_meas`, `meas_lift`, `meas_lift_dirac`, `meas_lift_mass` — same file |
| Runtime-parameter distributions $\mathrm{Gaussian}(e_1,e_2)$ / $\mathrm{Uniform}(e_1,e_2)$ | `ne_gaussian`, `ne_uniform` — same file; `pkernel`, `kernel_lift`, `kernel_lift2`, `gaussian_kernel`, `uniform_kernel` — `theories/programs/distributions.v` |
| Variable lookup via canonical structures | `tagged_nctx`, `find_nv`, `found_nv`, `recurse_nv`, `ne_var'` — same file |
| Surface notation `[ … ]` and the `ppl_named` custom entry | `ppl_named` (custom entry) — same file |
| The probability type and its bundle (`tProb`, `probObj`, `tProb_robj`) | `probObj`, `po_obj`, `po_incl`, `po_into`, `tProb`, `po_density` — same file |
| Probability surface forms (`Bernoulli`, `Bernoulli [\|p\|]`, `Score`, `Sigmoid`, `Gausslik`, `Gt0`, `test`, `Const`, `InclP`, `observe`, `Meas`, `sample`, `>`, `let rec`) | `pbern`, `pscore`, `psigmoid`, `pgausslik`, `pgt0`, `ptest`, `testfn`, `test_fun`, `pconst`, `pincl`, `bern_lift_P`, `score_lift_P`, `sigmoid`, `gauss_obs_density`, `gt0_ind`, `negr`, `prob`, `pmeas`, `prob_pmeas` — same file; `gaussian`, `uniform`, `ex_surface_demo`, `ex_surface_walk` — `theories/programs/examples.v` |
| The `observe` operator and its distribution bundle | `pobserve`, `obsDist`, `obsGaussian`, `od_arg`, `od_dens`, `pobserve_obsGaussian`, `test`, `ptest` — same file |
| The reject/condition combinators over a program predicate `f :` `b` $\to$ `tbool` (`ne_reject`, `ne_condition`) | `ne_fail`, `ne_assert`, `ne_reject`, `ne_condition` — `theories/programs/reject_condition.v` |

### Def 1.1 — Types and contexts (`ppl_type`, `named_ctx`)

The surface types are a five-constructor grammar — unit, an arbitrary
measurable base object `tbase X`, binary products, function types, and
a two-point boolean type — and a context is a list of string-named
typed bindings (`theories/programs/ppl.v`).

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

`drop_names` forgets the string identifiers: the categorical
interpretation lives on `drop_names G`, and the named layer serves only
canonical-structure-driven variable lookup at `#"x"` sites.

### Def 1.2 — Free-coalgebra types (`is_free_coalg_type`)

This predicate characterises the surface types whose CBV
interpretation is a *free* $!$-coalgebra — function types and products
thereof. It gates the mutual-recursion constructor `ne_fix_mr` below.

```coq
(* theories/programs/ppl.v *)
Fixpoint is_free_coalg_type (t : ppl_type Ar) : bool :=
  match t with
  | tfun _ _ => true
  | tprod t1 t2 => is_free_coalg_type t1 && is_free_coalg_type t2
  | _ => false
  end.
```

### Def 1.3 — Pure term constructors (`ne_var`, `ne_lam`, `ne_app`, `ne_let`)

The pure fragment of `named_expr` is a standard intrinsically-typed
simply-typed lambda calculus with products, let, real constants,
arithmetic, and the two boolean values — thirteen constructors of the
single inductive in `theories/programs/ppl.v` (Section Syntax).

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
crucial for canonical-structure resolution at `#"x"` sites — the
Saito–Affeldt APLAS 2023 §5.1 pattern.

### Def 1.4 — Effectful term constructors (`ne_sample`, `ne_score`, `ne_bernoulli`, `ne_if`)

The effectful constructors are direct-style — the probability monad
lives in the interpretation `eD`, not in the source types — and divide
by what they produce. `ne_sample` is one real draw from a fixed
sub-probability measure ($\to$ `tR'`). `ne_bernoulli` /
`ne_bernoulli_f` are the **boolean coin** ($\to$ `tbool`), the sole
source of boolean randomness, consumed by `ne_if` for probabilistic
branching. `ne_score` is soft conditioning ($\to$ `tunit`). The
real-valued *named* and *runtime-parameter* distributions (`gaussian` /
`uniform`, `Gaussian` / `Uniform`) are not primitives: they build on
`ne_sample` and the probability-kernel layer (the
[Runtime-parameter distributions](#) section below). So the only
randomness baked into the syntax is one fixed-measure sample, one
boolean coin, and one score; everything else is derived.

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
  | ne_bernoulli_f : forall G,
      forall f : R -> R,
      measurable_fun [set: R] f ->
      (forall r : R, 0 <= f r)%R ->
      (forall r : R, f r <= 1)%R ->
      named_expr G tR' -> named_expr G tbool
  | ne_if : forall G t,
      named_expr G tbool ->
      named_expr G t -> named_expr G t -> named_expr G t.
```

`ne_score` carries a density $f : \mathbb{R} \to \mathbb{R}$ valued in
$[0,1]$; the bound is the unit-ball discipline of `linhom_icones` (see
[Scores, densities, and the sub-probability
boundary](../../ppl/sections/ppl-sec-law-1-20-scores-densities-and-the-sub-probability-boundary.html)
for what it rules out — genuinely unbounded densities — and how a
bounded density is conditioned via its intrinsic peak). The boolean
coin shares that discipline: `ne_bernoulli p` is the constant coin
$(p, 1 - p)$, and `ne_bernoulli_f f e` is value-dependent — the coin
$(f\,r,\ 1 - f\,r)$ at the value $r$ of the `tR'`-valued sub-expression
`e` — with CBV engine the path lift `bern_lift` (the boolean twin of
`score_lift`; see [the value-dependent Bernoulli
section](../../ppl/sections/ppl-sec-law-2-6-the-value-dependent-bernoulli-lift.html)).

The $[0,1]$ discipline is carried by a **type**, not by loose
witnesses: the probability type `tProb P` (a `tbase` over the $[0,1]$
object of a bundle `P : probObj`) is the surface home of every coin and
score — a value of type `tProb P` is a $[0,1]$-supported measure, and a
coin or score over it integrates the bundle's inclusion $\iota$. The
witness-free surface forms (`Bernoulli`, `Score`, `Sigmoid`,
`Gausslik`, `Gt0`, `test`, `observe`, the comparison coin `>`) are
covered in full by [the probability type and the `tProb`
surface](../../ppl/sections/ppl-sec-def-1-11-probability-type-and-bundle.html)
below.

### Def 1.5 — Measurable function application (`ne_meas`)

`ne_meas f Hf e` pushes the value of the `tR'`-valued sub-expression
`e` through a measurable meta-level function $f : \mathbb{R} \to
\mathbb{R}$ — surface form `Meas { f , Hf } e`. Unlike `ne_score` /
`ne_bernoulli_f`, no $[0,1]$ bounds are needed: the semantics is the
`FMeas` functorial action (pushforward), whose operator norm is already
$\leq 1$.

```coq
(* theories/programs/ppl.v *)
Inductive named_expr : named_ctx Ar -> T -> Type :=
  (* … *)
  | ne_meas  : forall G,
      forall f : R -> R,
      measurable_fun [set: R] f ->
      named_expr G tR' -> named_expr G tR'.
```

The semantic engine is `meas_lift := FMeas_fmap meas_hom` (the
Dirac-path pushforward at the carrier transport $\hat f =
\mathtt{R\_to\_carrier} \circ f \circ \mathtt{carrier\_to\_R}$), with
two load-bearing laws: `meas_lift_dirac` (`Meas f` on a point mass is
application, $\delta_r \mapsto \delta_{f\,r}$) and `meas_lift_mass`
(pushforward preserves total mass). The CBV clause is `eD_meas_E`
(`theories/programs/ppl_cbv.v`): $\llbracket \mathtt{Meas}\ f\ e
\rrbracket = \mathtt{meas\_lift} \circ \llbracket e \rrbracket$ — the
`FMeas`-functorial mirror of the `ne_score` clause.

### Def 1.6 — Runtime-parameter distributions (`ne_gaussian`, `ne_uniform`)

$\mathrm{Gaussian}(e_1, e_2)$ / $\mathrm{Uniform}(e_1, e_2)$ draw from
the normal/uniform family whose parameters are the **values** of the
two `tR'`-valued sub-expressions — so a sampled value can itself
parameterise the next draw (hierarchical models, e.g.
`examples.v::ex_gaussian_walk`). No witness braces: the kernel families
are *total*.

```coq
(* theories/programs/ppl.v *)
Inductive named_expr : named_ctx Ar -> T -> Type :=
  (* … *)
  | ne_gaussian : forall G,
      named_expr G tR' -> named_expr G tR' -> named_expr G tR'
  | ne_uniform : forall G,
      named_expr G tR' -> named_expr G tR' -> named_expr G tR'.
```

**The kernel layer** (`theories/programs/distributions.v`) turns a
measurable family of sub-probability measures into a linear lift on
measures, in four beats.

- *Bundle.* A `pkernel X Y` packages a family `pk_ker` $: X \to$ `FMeas`
  $Y$ with the mathcomp-analysis kernel condition (`pk_meas`: $x \mapsto
  k(x)(U)$ measurable for every measurable $U$) and the unit-ball bound
  (`pk_ball`). Such a family *is* a measurable path (`pkernel_is_path`,
  paper Def 3.7).
- *Lift.* The Thm 6.1 machinery promotes that path to the semantic lift
  `kernel_lift k` $:$ `FMeas` $X \multimap$ `FMeas` $Y$, $\nu \mapsto
  \int k(x)\,\nu(dx)$ (Pettis integral), with computation laws
  `kernel_lift_E` ($(\mathtt{kernel\_lift}\ k\ \nu)(U) = \int
  k(x)(U)\,\nu(dx)$), `kernel_lift_mass` (pointwise-mass-1 kernels
  preserve total mass) and `kernel_lift_dirac`
  ($\mathtt{kernel\_lift}\ k\ \delta_x = k(x)$).
- *Two arguments.* `kernel_lift2 k := kernel_lift k ∘ fmeas_lax` makes
  the tensored argument pair a joint measure on the product object —
  exactly the `add_lift` / `mul_lift` route — with `kernel_lift2_dirac`
  and the product-mass law `kernel_lift2_mass`.
- *Instances.* `dirac_kernel` (`kernel_lift dirac_kernel = id`,
  `dirac_kernel_lift_id`); `gaussian_kernel` ($(m,s) \mapsto$
  `normal_prob m s` transported along the carrier cast); and
  `uniform_kernel` ($(a,b) \mapsto$ `uniform_prob` for $a < b$, else
  $\delta_a$). (The value-dependent $[0,1]$ coin is *not* a `pkernel`
  instance: it is realised by `bern_lift`, a linhom in
  `theories/programs/ppl.v`, with the branch-mass laws `bern_lift_t_E`
  / `bern_lift_f_E`.)

**The $s = 0$ convention**: `gaussian_kernel` overrides the $s = 0$
fibre to the Dirac $\delta_m$ — the degenerate weak limit of $N(m,s)$
as $s \to 0$ — because mathcomp-analysis' own `normal_prob m 0` is a
junk uniform-$[0,1]$ *placeholder* (its `normal_pdf` falls back to
`uniform_pdf 0 1` at $s = 0$), not a meaningful distribution; $s \neq
0$ (including $s < 0$) keeps mathcomp's genuine normal with deviation
$\lvert s \rvert$. Family measurability *in the parameters*
(`measurable_normal_prob_pair`, `measurable_uniform_int_pair`) is proved
by Fubini–Tonelli against Lebesgue measure.

The CBV clause (`eD_gaussian_E` / `eD_uniform_E`,
`theories/programs/ppl_cbv.v`) is the `ne_add` shape with the kernel
lift in place of the pushforward:
$$\llbracket \mathrm{Gaussian}(e_1,e_2) \rrbracket = \delta_\Gamma \mathbin{;} (\llbracket e_1 \rrbracket \otimes \llbracket e_2 \rrbracket) \mathbin{;} \mathtt{kernel\_lift2}\ \mathtt{gaussian\_kernel}.$$
Three anchors pin it (`theories/programs/infra/kernel_anchors.v`):

- *Point masses.* `eD_gaussian_at` / `eD_gaussian_dirac_E` — on
  point-mass arguments the draw *is* the transported `normal_prob`, with
  the $s = 0$ Dirac fibre.
- *Mass.* `eD_gaussian_mass` — the result's mass is the product of the
  argument masses, the kernel being a pointwise probability
  (`gaussian_kernel_norm1`).
- *Constant-parameter agreement.* `eD_gaussian_sample_agree` —
  $\llbracket \mathrm{Gaussian}([\lvert m \rvert],[\lvert s \rvert]) \rrbracket\gamma = \llbracket \mathtt{sample}\ (\mathtt{gaussian}\ m\ s) \rrbracket\gamma$
  for $s \neq 0$: the old bundled-`sample` surface is the kernel surface
  at real literals (the two transports are identified by
  `pmeas_of_prob_fmeas`).

The `Uniform` mirror is `eD_uniform_at` / `eD_uniform_dirac_E` /
`eD_uniform_mass` / `eD_uniform_sample_agree`.

### Def 1.7 — Recursion at function type (`ne_fix`)

OCaml-style `let rec`, restricted to function types: the body accesses
the recursive function via a fresh name `s : tfun t1 t2` pushed onto the
context, and the whole construct is again a value of type `tfun t1 t2`.

```coq
(* theories/programs/ppl.v *)
Inductive named_expr : named_ctx Ar -> T -> Type :=
  (* … *)
  | ne_fix  : forall G s t1 t2,
      named_expr ((s, tfun t1 t2) :: G) (tfun t1 t2) ->
      named_expr G (tfun t1 t2)
```

The CBV interpretation in `theories/programs/ppl_cbv.v` resolves
`ne_fix` (and `ne_fix_mr` at function body types) to the composite
$\mathtt{fix\_comb} \circ \llbracket \lambda s.\,\mathrm{body}
\rrbracket$, where `fix_comb` is the seeded value-fixpoint combinator of
`theories/programs/infra/em_fix_value.v` — see [the CBV value-fixpoint
chapter](../../ppl/chapters/ppl-ch-the-cbv-value-fixpoint-at-function-types.html).

### Def 1.8 — Mutual recursion at free-coalgebra types (`ne_fix_mr`)

`ne_fix_mr` generalises `ne_fix` to any body type `t` with
`is_free_coalg_type t = true` — in particular `t = tprod (tfun A1 B1)
(tfun A2 B2)`, the mutual-recursion shape, where the two components call
each other via `fst #"s"` / `snd #"s"`.

```coq
(* theories/programs/ppl.v *)
Inductive named_expr : named_ctx Ar -> T -> Type :=
  (* … *)
  | ne_fix_mr : forall G s t,
      is_free_coalg_type t ->
      named_expr ((s, t) :: G) t -> named_expr G t.
```

The CBV interpretation in `theories/programs/ppl_cbv.v` dispatches
`ne_fix_mr` on the body type (`fix_mr_clause`): at `tfun t1 t2` it is
the *same* genuine seeded combinator `fix_comb` as `ne_fix`; at products
of free types it is the *same combinator transported along the Seely
decomposition* — `fix_mr_comb`, i.e. `fix_comb (free_base t)` conjugated
by the coalgebra iso `free_decomp` $: \mathtt{tyD\_cbv}\ t \cong
\widetilde{!}(\mathtt{free\_base}\ t)$, whose `tprod` step is the
EM-level Seely-2 iso $\mathtt{EM\_prod}\ (\widetilde{!}X)\
(\widetilde{!}Y) \cong \widetilde{!}(X \mathbin{\&} Y)$ of
`theories/programs/infra/em_fix_mr.v`. The mutual-recursion fixpoint is
genuine at *every* free body type; the surface witness is
`ex_even_odd_pair` (see the [Examples tab](../examples/)).

### Def 1.9 — Variable lookup by canonical structures (`find_nv`, `ne_var'`)

Writing `#"x"` makes Rocq's canonical-structure search find the named
context, the type, and the `named_var` witness of the binding `"x"` all
at once — the Saito–Affeldt APLAS 2023 §5.2 `find` structure,
transplanted to `named_ctx` in `theories/programs/ppl.v`.

Two canonical instances over a tagged context drive the search:
`found_nv` (head case — the sought string is the head binding) is tried
first; otherwise the tag unfolds to `recurse_nctx` and `recurse_nv`
recurses on the tail, with the "different string" side-condition
discharged by `infer (String.eqb s y = false)` — a
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

### Def 1.10 — Surface notation (the `ppl_named` custom entry)

A custom grammar entry `ppl_named` (opened by `Declare Custom Entry
ppl_named`) gives the examples an OCaml-flavoured direct-style surface
syntax: `[ … ]` enters the entry, `# x` is variable lookup, and
`Sample` / `Sc` / `Bernoulli` / `if` / `\` / `let` / `fix` / `fix_mr`
map one-to-one onto the constructors.

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
Notation "'Bernoulli' '{' p ',' Hp_ge0 ',' Hp_le1 '}'" :=
  (ne_bernoulli p Hp_ge0 Hp_le1)
  (in custom ppl_named at level 1,
   p constr, Hp_ge0 constr, Hp_le1 constr).
Notation "'if' e 'then' M 'else' N" := (ne_if _ e M N)
  (in custom ppl_named at level 80).
Notation "'\' x ':::' A '=>' M" := (ne_lam x%string (t1 := A) M)
  (in custom ppl_named at level 70).
Notation "'let' x ':=' M 'in' N" := (ne_let x%string M N)
  (in custom ppl_named at level 80).
Notation "'fix' s ':::' 'tfun' A B 'in' M" :=
  (ne_fix s%string (t1 := A) (t2 := B) M)
  (in custom ppl_named at level 80).
Notation "'fix_mr' s 'as' T 'by' Hfree 'in' M" :=
  (ne_fix_mr s%string T Hfree M)
  (in custom ppl_named at level 80).
```

Direct-style: no `Ret` notation, and `let "x" := M in N` desugars to
`ne_let` (not `ne_bind`). Brackets `[ … ]` enter the entry; curly braces
`{ x }` escape back to plain Rocq.

### Def 1.11 — Probability type and bundle (`probObj`, `tProb`)

The $[0,1]$ discipline of coins and scores is carried by a **type**, not
by loose witnesses. A single bundle `probObj` packages the $[0,1]$
sub-object the surface needs — a distinguished object `po_obj` with its
inclusion `po_incl` $:$ `po_obj` $\to$ `R_obj`, the two $[0,1]$ bounds,
and the universal factoring `po_into` of any measurable $[0,1]$ map
through the inclusion ($h = \iota \circ \mathtt{po\_into}\ h$, the
computation law `po_into_E`). The probability type is `tProb P := tbase
(po_obj P)`: a value of type `tProb P` is a $[0,1]$-supported measure,
and a coin or score over it integrates the inclusion $\iota$ — the mean
of the supported measure. The bundle also exposes the carrier density
`po_density P` (the inclusion read into $\mathbb{R}$). Every surface form
below is witness-free; the bounds travel with the type, never as proof
obligations.

| Result | Statement | Rocq |
|---|---|---|
| Def 1.11a — the `probObj` bundle | the canonical $[0,1]$ sub-object interface: object, inclusion $\iota$, the two bounds, and the factoring `po_into` | `probObj`, `po_incl`, `po_into`, `po_into_E` — `theories/programs/ppl.v` |
| Def 1.11b — the `tProb P` type | a value is a $[0,1]$-supported measure a coin or score integrates via `po_density` | `tProb`, `po_density` — `theories/programs/ppl.v` |

```coq
(* theories/programs/ppl.v — the [[0,1]] bundle and the probability type *)
Record probObj (R : realType) (Ar : MeasSubcat R) := MkProbObj {
  po_robj : ar_obj Ar ;
  po_obj  : ar_obj Ar ;
  po_incl : ar_hom Ar po_obj po_robj ;
  po_ge0  : forall x, (0 <= carrier_to_R _ (po_incl x))%R ;
  po_le1  : forall x, (carrier_to_R _ (po_incl x) <= 1)%R ;
  po_into : forall h, measurable_fun [set: R] h ->
              (forall r, 0 <= h r) -> (forall r, h r <= 1) ->
              ar_hom Ar po_robj po_obj ;
  (* … the computation law [po_into_E] … *) }.
Definition tProb (P : probObj Ar) : ppl_type Ar := tbase (po_obj P).
```

A coin or score gets its $[0,1]$ number three ways: as a bare literal
(`Bernoulli [| p |]`), read off a `tProb`-typed value (`Bernoulli e`,
`Score e`), or produced by pushing a real through a named $[0,1]$ map
(`Sigmoid e`, `Gausslik e { s , y }`, `Gt0 e`, `test f e`). Each is
built once, in `ppl.v`, by feeding its $[0,1]$ map into `po_into`; the
use site never sees `po_into`.

### Def 1.12 — Bernoulli coins (`pbern`, `bern_lift_P`)

> **Prerequisite:** the two lifts `bern_lift_P` / `score_lift_P` at an
> arbitrary base object, from
> [Law 2.6 — the value-dependent Bernoulli lift](../../ppl/sections/ppl-sec-law-2-6-the-value-dependent-bernoulli-lift.html).

The value coin `Bernoulli e` reads its success probability off the
`tProb P`-typed sub-expression `e` through `po_density P` and flips with
that probability; the bundle `P` is inferred from `e`'s type
(e.g. `Bernoulli (Sigmoid #"x")`). The constant coin `Bernoulli [| p |]`
takes a bare real literal — the fair coin is `Bernoulli [| (1/2 : R) |]`
— with its $[0,1]$ bounds discharged automatically by `lra`.

| Result | Statement | Rocq |
|---|---|---|
| Def 1.12a — value coin `Bernoulli e` | flips with the probability read off a `tProb P`-typed `e` via `po_density P` | `pbern`, `bern_lift_P` — `theories/programs/ppl.v` |
| Def 1.12b — literal coin `Bernoulli [\| p \|]` | fair/biased coin from a bare $[0,1]$ literal, bounds discharged by `lra` | `ne_bernoulli` — `theories/programs/ppl.v` |

```coq
(* theories/programs/ppl.v — the two Bernoulli surface forms *)
Notation "'Bernoulli' '[|' p '|]'" :=
  (ne_bernoulli p (* [0 <= p] and [p <= 1] discharged by lra *)) (* … *).
Notation "'Bernoulli' e" := (pbern e)   (* … value-dependent coin *).
```

### Def 1.13 — Score reweighting (`pscore`, `score_lift_P`)

The score `Score e` weighs the current trace by the weight read off the
`tProb P`-typed sub-expression `e` through `po_density P`, e.g.
`Score (Gausslik e { 1 / 2 , y })`. Its engine at an arbitrary base
object is `score_lift_P`, the score twin of `bern_lift_P`.

| Result | Statement | Rocq |
|---|---|---|
| Def 1.13a — the score `Score e` | weighs the trace by the weight read off a `tProb P`-typed `e` | `pscore`, `score_lift_P` — `theories/programs/ppl.v` |

```coq
(* theories/programs/ppl.v — the score surface form *)
Notation "'Score' e" := (pscore e)  (* … *).
```

### Def 1.14 — Sigmoid, Gausslik, and Gt0 primitives (`psigmoid`, `pgausslik`, `pgt0`)

Each of `Sigmoid e` / `Gausslik e { s , y }` / `Gt0 e` pushes a real
value through a named $\mathbb{R} \to [0,1]$ map and returns `tProb P` —
the logistic map, the peak-normalised Gaussian likelihood (mean
expression first, then the meta-level `{ stddev , datum }` braces), and
the strict-positivity indicator, respectively. Each is built by feeding
its $[0,1]$ map into the bundle factoring `po_into`.

| Result | Statement | Rocq |
|---|---|---|
| Def 1.14a — `Sigmoid e` | pushes a real through the logistic map `sigmoid` $: \mathbb{R} \to [0,1]$ into `tProb` | `psigmoid`, `sigmoid` — `theories/programs/ppl.v` |
| Def 1.14b — `Gausslik e { s , y }` | pushes the mean `e` through the peak-normalised Gaussian likelihood | `pgausslik`, `gauss_obs_density` — `theories/programs/ppl.v` |
| Def 1.14c — `Gt0 e` | pushes a real through the strict-positivity indicator $\mathtt{gt0\_ind} = \mathbf{1}_{(0,\infty)}$ | `pgt0`, `gt0_ind` — `theories/programs/ppl.v` |

```coq
(* theories/programs/ppl.v — the tProb-producing primitives *)
Notation "'Sigmoid' e" := (psigmoid e) (* … *).
Notation "'Gausslik' e '{' s ',' y '}'" := (pgausslik s y e) (* mean-first *).
Notation "'Gt0' e"    := (pgt0 e)    (* … *).
```

### Def 1.15 — The test-function coin (`ptest`, `testfn`)

A *test function* `f : testfn` is a measurable $[0,1]$-valued map you
integrate measures *against*: $\int f\,d\mu$ is the test pairing at the
heart of the conditioning/rejection headline theorems. The `testfn`
record bundles the carrier map `test_fun` with its measurability and
$0 \leq f \leq 1$ witnesses and coerces to its function, so `f r` and
$\int f\,d\mu$ read directly. `test f e` evaluates `f` at the runtime
value `e`, landing in `tProb` — the `testfn`-parameterised sibling of
`Sigmoid` / `Gausslik` — so a use site reads `Bernoulli (test f #"x")`
/ `Score (test f #"m")`.

| Result | Statement | Rocq |
|---|---|---|
| Def 1.15a — the test coin `test f e` | evaluates a test function `f : testfn` ($0 \leq f \leq 1$) at the runtime value `e`, landing in `tProb` | `ptest`, `testfn`, `test_fun` — `theories/programs/ppl.v` |

```coq
(* theories/programs/ppl.v — the abstract test-function coin *)
Notation "'test' f e" := (ptest f e) (* abstract test-function coin *).
```

### Def 1.16 — Const and InclP (`pconst`, `pincl`)

`Const pr e` is the constant-literal `tProb`-map at the bundled
probability `pr : prob` (used by the parameterised `ex_almost_loop`).
`InclP e` is the forgetful read of a `tProb P` value back to `tR` along
the inclusion $\iota$.

| Result | Statement | Rocq |
|---|---|---|
| Def 1.16a — `Const pr e` | the constant-literal `tProb` map at a bundled probability `pr : prob` | `pconst`, `prob` — `theories/programs/ppl.v` |
| Def 1.16b — `InclP e` | forgetful read of a `tProb P` value back to `tR` along the inclusion $\iota$ | `pincl` — `theories/programs/ppl.v` |

```coq
(* theories/programs/ppl.v — constant map and inclusion read *)
Notation "'Const' pr e" := (pconst pr e) (* … *).
Notation "'InclP' e"  := (pincl e)   (* … *).
```

### Def 1.17 — The observe operator (`pobserve`, `obsGaussian`)

`observe` is a general conditioning operator, not Gaussian-specific:
`observe Gaussian e { s } y` $\equiv$ `Score (Gausslik e { s , y })`. It
is `pobserve (D : obsDist) (y : R)` over a distribution-with-density
record `obsDist { od_arg ; od_dens ; … }`, where `od_arg` is the runtime
parameter (the predicted mean) and `od_dens` the family of
$[0,1]$-valued densities. `obsGaussian e s` is the first instance, so
`pobserve (obsGaussian e s) y = pscore (pgausslik s y e)` definitionally
(`pobserve_obsGaussian`); adding another observable distribution is a new
`obsDist` instance plus a one-line sugar. The denotation lemma
`observe_gauss_E` (`theories/programs/ppl_cbv.v`) weighs the trace by
$\mathtt{normal\_pdf}\ \mu\ s\ y\,/\,\mathtt{normal\_peak}\ s$ — the
Gaussian likelihood normalised by the intrinsic peak (see [Law 1.20 —
scores, densities, and the sub-probability
boundary](../../ppl/sections/ppl-sec-law-1-20-scores-densities-and-the-sub-probability-boundary.html)).

| Result | Statement | Rocq |
|---|---|---|
| Def 1.17a — `observe Gaussian e { s } y` | $\equiv$ `Score (Gausslik e { s , y })` — condition the mean `e` on datum `y` | `pobserve`, `obsGaussian`, `pobserve_obsGaussian` — `theories/programs/ppl.v` |
| Def 1.17b — the `obsDist` record | distribution-with-density interface; a new observable is a new instance | `obsDist`, `od_arg`, `od_dens` — `theories/programs/ppl.v` |

```coq
(* theories/programs/ppl.v — the observe operator *)
Notation "'observe' 'Gaussian' e '{' s '}' y" :=
  (pobserve (obsGaussian e s) y) (* … *).
```

### Def 1.18 — Sampling, the comparison coin, and let rec (`ne_sample`, `pmeas`)

Bundled sampling: `pmeas` packages a sub-probability with its unit-ball
witness, and `prob_pmeas` transports any mathcomp-analysis probability on
$\mathbb{R}$ to a `pmeas`, giving the named distributions `gaussian m s`
/ `uniform a b` (`theories/programs/examples.v`). The comparison coin
`e1 > e2` is `Bernoulli (Gt0 (e1 + Meas{negr} e2))` at the
strict-positivity indicator of the difference — the deterministic test
$a > b$ on point masses. And `let rec f x := M in K` is OCaml-style
recursive binding, `ne_let f (ne_fix f (ne_lam x M)) K`. The end-to-end
demos are `ex_surface_demo` and `ex_surface_walk` (see the
[Examples tab](../examples/)).

| Result | Statement | Rocq |
|---|---|---|
| Def 1.18a — bundled draw `sample m` | `pmeas` packages a sub-probability with its unit-ball witness; `prob_pmeas` transports a probability | `sample`, `pmeas`, `prob_pmeas` — `theories/programs/ppl.v` |
| Def 1.18b — comparison coin `e1 > e2` | `Bernoulli (Gt0 (e1 + Meas{negr} e2))` — deterministic $a > b$ on point masses | `negr` — `theories/programs/ppl.v` |
| Def 1.18c — `let rec f x := M in K` | OCaml-style recursive binding `ne_let f (ne_fix f (ne_lam x M)) K` | `ne_fix`, `ne_let` — `theories/programs/ppl.v` |

```coq
(* theories/programs/ppl.v — bundled sampling, the comparison coin, let rec *)
Notation "'sample' m" := (ne_sample (pm_meas m) (pm_ball m)) (* … *).
Notation "M > N"      := (Bernoulli (Gt0 (ne_add M (ne_meas negr negr_meas N)))) (* … *).
Notation "'let' 'rec' f x ':=' M 'in' K" :=
  (ne_let f%string (ne_fix f%string (ne_lam x%string M)) K) (* … *).
```

### Def 1.19 — Reject/condition combinators (`ne_reject`, `ne_condition`)

Rejection sampling and conditioning are two closed combinators whose
**acceptance test is itself a program** — a predicate `f :` `b` $\to$
`tbool` on the model's output value, supplied as an argument exactly
like the model `m :` `a` $\to$ `b`. Applying the test is then ordinary
object-language application `# "f" @ # "x"`: no lift node and no
`ne_test` (both deleted — the constructor, its `eD_cbv` clause, the
`TestTmLiftG` section, and the `Test{…}` notation are all gone).

The one fact that makes this work is that **`tbool` is not `bool`**: it
denotes a point of the 2-point sub-probability cone
(`tyD_cbv tbool = bool_cone_car`), a sub-distribution over $\{\mathtt{true},
\mathtt{false}\}$. So $\llbracket f\,x \rrbracket$ is the *acceptance
distribution* at $x$, and its true-mass $t(x) := (\mathtt{bc\_t}\
\llbracket f\,x \rrbracket)\%\mathtt{:num} \in [0,1]$ is the acceptance
probability — the only quantity the combinators read. Two regimes, one
mechanism: when `f` is **deterministic** ($\llbracket f\,x \rrbracket$
a Dirac) $t = \mathbf{1}_A$ is the indicator of the accept set $A := \{
x \mid f\,x = \mathtt{true} \}$ (hard conditioning); when `f` is a
**coin** ($\llbracket f\,x \rrbracket$ non-Dirac) $t$ is a density (soft
conditioning).

`Bernoulli` still names a genuine coin and `Score` a genuine density
reweight — both remain primitives for *building* models and predicates
(a soft predicate is $f := \lambda x.\,\mathtt{Bernoulli}\
(\mathtt{density}\ x)$) — but neither appears inside `reject` /
`condition`. `reject` retries a rejected draw; `condition` gives up on
it — the same program modulo the else-branch. `ne_fail` is the diverging
give-up term $(\mathtt{fix}\ \mathit{fail}.\,\lambda().\,\mathit{fail}\
())\,()$, denoting the zero sub-distribution, and `ne_assert b = if b
then () else fail`.

```coq
(* theories/programs/reject_condition.v *)
Definition ne_reject :
    nexpr nil (tfun (tfun tb tbool) (tfun (tfun ta tb) (tfun ta tb))) :=
  [ \ "f" ::: tfun tb tbool =>
      ( fix "rx" ::: tfun (tfun ta tb) (tfun ta tb) in
          \ "m" ::: (tfun ta tb) =>
            \ "a" ::: ta =>
              (let "x" := # "m" @ # "a" in
               if (# "f" @ # "x") then # "x" else # "rx" @ # "m" @ # "a") ) ].

Definition ne_condition :
    nexpr nil (tfun (tfun tb tbool) (tfun (tfun ta tb) (tfun ta tb))) :=
  [ \ "f" ::: tfun tb tbool =>
      \ "m" ::: (tfun ta tb) =>
        \ "a" ::: ta =>
          (let "x" := # "m" @ # "a" in
           let "_" := (if (# "f" @ # "x") then () else { ne_fail }) in
           # "x") ].
```

### Law 1.20 — Scores, densities, and the sub-probability boundary (`ne_score`, `score_lift`)

This is a sub-probability model, and that fixes exactly which scores it
can express. Every morphism of $\mathbf{ICone}$ is non-expansive: the
`cones_hom` record carries a norm-bound field, so a map never increases
mass.

```coq
(* theories/cones/cone_cat.v *)
Record cones_hom (P Q : coneType R) : Type := ConesHom {
  cones_hom_fun :> P -> Q;
  cones_hom_linear : is_linear cones_hom_fun;
  cones_hom_continuous : is_omega_continuous cones_hom_fun;
  cones_hom_norm_le1 :
    forall x : P, cone_norm (cones_hom_fun x) <= cone_norm x;
}.
```

Scoring weights a measure by a density: `score_lift f` sends a measure
$\mu$ to $f \cdot \mu$, of mass $\int f\,d\mu$. As a morphism its
operator norm is $\sup f$, so `score_lift f` is a map of the category —
and `ne_score f` is well-typed — exactly when $f$ is bounded by $1$.
That is the source of the `forall r, f r <= 1` witness on `ne_score` and
`ne_bernoulli_f`: not a modelling convenience but the condition for the
score to be a morphism at all.

The distinction that matters in practice is between *sampling* and
*observing*. Sampling is always fine: `sample (gaussian m s)` denotes a
probability measure of mass $1$, a good morphism for every $m$ and $s$.
Observing — scoring by a density, `observe Gaussian e {s} y` weighing
the trace by the Gaussian likelihood of `y` — is the constrained
operation, a morphism only while the weight stays in $[0,1]$. The line
that matters is **bounded vs unbounded**.

A **bounded** likelihood is always conditionable, and `observe` does
exactly this. $N(\mu, \sigma)$ peaks at its intrinsic peak
$\mathtt{normal\_peak}\ \sigma = 1/(\sigma\sqrt{2\pi})$; the
*unnormalised* pdf crosses $1$ as soon as $\sigma < 1/\sqrt{2\pi}
\approx 0.399$, so it is not directly a $[0,1]$ weight. But the peak is
a finite bound, and dividing by it gives the legal weight
$\mathtt{gauss\_obs\_density}\ \sigma\ y = \mathtt{normal\_pdf}\ \mu\
\sigma\ y\,/\,\mathtt{normal\_peak}\ \sigma \in [0,1]$ — a map into the
$[0,1]$ object `po_obj P`, factored through the bundle inclusion by
`po_into`. This is exactly what `Gausslik e { σ , y }` (hence `observe`)
scores by — no user-supplied envelope, the peak is intrinsic to the
distribution. The normaliser cancels in the posterior: the conditioned
distribution $\int_U f\,d\nu \,/ \int f\,d\nu$ is independent of any
positive scaling of $f$, so dividing by $\mathtt{normal\_peak}\ \sigma$
changes the total evidence but never the posterior. The same holds for
the conditioning/rejection pair, where dividing by the peak is classical
rejection sampling with that envelope.

Only a **genuinely unbounded** family is out of scope. When a density
has no finite peak — a Gaussian with $\sigma$ free to approach $0$, a
likelihood that can be arbitrarily sharp — no normalisation brings it
inside the unit ball, so the observation is not a morphism of
$\mathbf{ICone}$ and has no denotation here. This is a property of every
sub-probability model, integrable cones and probabilistic coherence
spaces alike, not of the encoding.

The semantics designed to score by arbitrary unbounded weights is the
*s-finite kernel* model (Staton and collaborators): it drops the norm
bound and lets $\mathtt{score}\ w$ denote a measure of any finite mass.
The cone model makes the opposite trade — it keeps the sub-probability
discipline and, in return, carries the higher-order and analytic
structure (the $!$ comonad, the Seely and Eilenberg–Moore development)
that the kernel model does not. An `observe` with an unbounded density
is the price of that structure.

---

## Call-by-value interpretation (linhom + comonoid)

**In this chapter:** [Def 2.1](../../ppl/sections/ppl-sec-def-2-1-type-translation.html) · [Def 2.2](../../ppl/sections/ppl-sec-def-2-2-context-translation.html) · [Def 2.3](../../ppl/sections/ppl-sec-def-2-3-em-cartesian-primitives.html) · [Def 2.4](../../ppl/sections/ppl-sec-def-2-4-term-interpretation.html) · [Def 2.5](../../ppl/sections/ppl-sec-def-2-5-constant-icones-helpers.html) · [Law 2.6](../../ppl/sections/ppl-sec-law-2-6-the-value-dependent-bernoulli-lift.html) · [Def 2.7](../../ppl/sections/ppl-sec-def-2-7-if-then-else-at-the-icones-level.html) · [Law 2.8](../../ppl/sections/ppl-sec-law-2-8-the-definitional-unfolding-pack.html).

**Definition (CBV interpretation).** *Each type $\tau$ denotes a
$!$-coalgebra $\llbracket\tau\rrbracket \in \mathrm{EM}(!)$; each
well-typed program $\Gamma \vdash M : \tau$ denotes a linear morphism
$\llbracket M\rrbracket : U\llbracket\Gamma\rrbracket \multimap
U\llbracket\tau\rrbracket$ in $\mathbf{ICone}$ — an element of
`linhom_car Ar (coalg_obj (ctxD_cbv (drop_names Γ))) (coalg_obj (tyD_cbv τ))`.
Programs are not coalgebra morphisms (the sampling clause does not commute with the §9.7
duplicability structure on `FMeas`); the context's coalgebra structure
is used only through the comonoid pair $(\delta, \varepsilon) =
(\mathtt{coalg\_d}, \mathtt{coalg\_e})$ that every $\mathrm{EM}(!)$
object carries by Melliès' Proposition 28.*

In Rocq this is `eD` (`theories/programs/ppl_cbv.v`), sending a term
`M : named_expr Γ τ` to an element of `linhom_car Ar (coalg_obj (ctxD_cbv
(drop_names Γ))) (coalg_obj (tyD_cbv τ))` by structural recursion on
`named_expr`. It is built from an `icones_hom`-valued helper `eD_cbv` (in
the unit ball of the same `linhom`) and forwarded by `icones_to_linhom`;
the two views are interchangeable. Nothing wraps the codomain of `tfun`:
function *values* are linear maps $U\llbracket t_1\rrbracket \multimap
U\llbracket t_2\rrbracket$, and duplicability comes from the outer cofree
$\widetilde{!}$ only.

This chapter covers the type and context translations, the EM cartesian
primitives the interpreter is assembled from, the interpreter clause by
clause, and the regression pack pinning each clause. The semantic laws
*about* the interpreter — recursion-unfolding, the let-at-sample integral
law, the sharing anchors — live in
[the CBV value-fixpoint
chapter](../../ppl/chapters/ppl-ch-the-cbv-value-fixpoint-at-function-types.html)
and
[the CBV semantic-laws chapter](../../ppl/chapters/ppl-ch-cbv-semantic-laws-and-regression-anchors.html).

| Construction | Rocq |
|---|---|
| Type translation (no `Tobj` on `tfun`) | `tyD_cbv` — `theories/programs/ppl_cbv.v` |
| Context translation | `ctxD_cbv` — same file |
| Variable lookup (projection chain) | `var_lookup_cbv` — same file |
| Constant `icones_hom` helpers (`sample`, `real`, `true`/`false`, `bernoulli`) | `sample_icones`, `real_icones`, `true_icones`, `false_icones`, `bernoulli_icones` — same file |
| The value-dependent Bernoulli lift (semantics of `ne_bernoulli_f`) | `bern_lift`, `bern_lift_dirac`, `bern_lift_E`, `bern_lift_t_E`, `bern_lift_f_E`, `bern_lift_mass` — `theories/programs/ppl.v` (Section BernTmLift) |
| Runtime-parameter kernel lifts (semantics of `ne_gaussian` / `ne_uniform`) | `kernel_lift2`, `gaussian_kernel`, `uniform_kernel` — `theories/programs/distributions.v`; anchors `eD_gaussian_at`, `eD_gaussian_dirac_E`, `eD_gaussian_mass`, `eD_gaussian_sample_agree` (+ `Uniform` mirrors) — `theories/programs/infra/kernel_anchors.v` |
| If-then-else combinator at the icones level | `if_icones`, `if_under` — `theories/programs/ppl_cbv.v` |
| Internal icones-valued term interpretation | `eD_cbv`, `fix_mr_clause` — same file |
| Public linhom-valued term interpretation | `eD` — same file |
| EM cartesian primitives ($\delta$, $\varepsilon$, projections, pairing) | `coalg_d`, `coalg_e`, `em_proj1_mor`, `em_proj2_mor`, `em_pair_mor`, `em_term_mor` — `theories/homs/em_cartesian.v`; cartesian-η `em_pair_mor_proj_id` — `theories/programs/infra/cbv_adjunction.v` |
| Definitional-unfolding pack (one lemma per clause) | `eD_var_E` … `eD_fix_mr_prod_E` (25 lemmas) — `theories/programs/ppl_cbv.v` (Section EDUnfold) |
| Recursion-unfolding equations (semantic; setlike points) | `eD_fix_at_setlike`, `eD_fix_unfold`, `eD_fix_unfold_closed` — `theories/programs/infra/cbv_fix_unfold.v` |

### Def 2.1 — Type translation (`tyD_cbv`)

> **Key result:** each surface type denotes a $!$-coalgebra — the whole interpretation runs in $\mathrm{EM}(!)$.

Each surface type maps to a $!$-coalgebra: `tunit` to the terminal
coalgebra, `tbase X` to the Theorem 9.7 coalgebra on `FMeas X`, `tbool`
to the §9.7-style coalgebra on the 2-point cone, `tprod` to the EM
cartesian product, and `tfun t1 t2` to the cofree
coalgebra on the *clean* internal hom $U\llbracket t_1\rrbracket
\multimap U\llbracket t_2\rrbracket$.

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
`theories/homs/coalgebra.v`; the `tbool` clause uses `bool_cone_coalg` of
`theories/programs/infra/bool_cone_coalg.v` — see [the §9.7 coalgebra on
the 2-point
cone](../../ppl/sections/ppl-sec-def-6-4-the-sec-9-7-coalgebra-on-the-2-point-cone.html).
Both give the *shared-sample* semantics expected of a PPL: `let x =
Bernoulli(p) in (x, x)` denotes the diagonal pushforward $p\cdot(T, T) +
(1-p)\cdot(F, F)$, not the independent product $\mu \otimes \mu$ a cofree
`bang_cofree (bool_cone_car Ar)` would give. No `Tobj` wrap anywhere:
function values are clean linear maps.

### Def 2.2 — Context translation (`ctxD_cbv`)

> **Prerequisite:** the type translation [Def 2.1](../../ppl/sections/ppl-sec-def-2-1-type-translation.html); variable lookup uses only the comonoid counits.

A context denotes the right-nested iterated EM product of its types'
coalgebras, with `EM_term` at nil; variable lookup is then the evident
chain of `em_proj1` / `em_proj2` projections (`var_lookup_cbv`, same
file), using only the comonoid counits — no diagonal, no strength.

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

### Def 2.3 — EM cartesian primitives (`coalg_d`, `coalg_e`, `em_pair_mor`)

Every $!$-coalgebra carries a commutative comonoid $(\delta,
\varepsilon) = (\mathtt{coalg\_d}, \mathtt{coalg\_e})$ transported from
the Seely comonoid on its cofree resolution, and these comonoids make
$(\mathrm{EM}(!), \otimes, 1)$ cartesian — pairing, projections and the
terminal morphism are all definable from $(\delta, \varepsilon)$ alone.
This is the whole toolbox the CBV interpreter branches on.

The constructions live in `theories/homs/em_cartesian.v` (Melliès §7.4
Prop 28 / Cor 20 — see the Paper-tab pages [EM(!) is fully
cartesian](../../paper/beyond/beyond-em.html) and [Cartesian-η of
EM(!)](../../paper/beyond/beyond-cartesian-of-em.html)). The unbundled
cartesian-η identity `em_pair_mor_proj_id` is exposed in
`theories/programs/infra/cbv_adjunction.v` (Section EmPairProjId), proved
by promoted-point extensionality on the cofree pair then transported
along the `coalg_str` retract.

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

### Def 2.4 — Term interpretation (`eD_cbv`, `eD`)

The interpreter is uniformly comonoid-primitive: every branching node
(let, pair, app, if, arithmetic, boolean) uses the context diagonal
$\delta_\Gamma$ to give each sub-term its own copy of $\Gamma$, so
multi-use of a free variable is free in the cone. The cofree exponential
$\widetilde{!}$ appears only at two boundaries — `ne_lam`, where the body
is curried and promoted via `adj_psi` of the $U \dashv \widetilde{!}$
adjunction, and `ne_app`, where the function value is dereferenced via
`der` before evaluation.

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
  | ne_meas _ f Hfm e0    => icones_comp (meas_lift Hfm) (eD_cbv e0)
  | ne_gaussian _ M0 N0   =>
      icones_comp (kernel_lift2 (gaussian_kernel _ _))
                  (em_pair_mor (eD_cbv M0) (eD_cbv N0))
  | ne_uniform _ M0 N0    =>
      icones_comp (kernel_lift2 (uniform_kernel _ _))
                  (em_pair_mor (eD_cbv M0) (eD_cbv N0))
  | ne_true G0            => true_icones (ctxD_cbv (drop_names G0))
  | ne_false G0           => false_icones (ctxD_cbv (drop_names G0))
  | ne_bernoulli G0 p H0 H1 =>
      bernoulli_icones (ctxD_cbv (drop_names G0)) p H0 H1
  | ne_bernoulli_f G0 f Hfm Hg0 Hl1 e0 =>
      icones_comp (bern_lift Hfm Hg0 Hl1) (eD_cbv e0)
  | ne_if _ _ e M0 N0     => if_icones (eD_cbv M0) (eD_cbv N0) (eD_cbv e)
  | ne_fix G0 _ t1 t2 body =>
      icones_comp
        (ch_mor (fix_comb (linhom_car Ar (coalg_obj (tyD_cbv t1))
                                         (coalg_obj (tyD_cbv t2)))))
        (ch_mor (adj_psi (tensor_curry (eD_cbv body))))
  | ne_fix_mr G0 _ ty _ body =>
      fix_mr_clause (ctxD_cbv (drop_names G0)) ty (eD_cbv body)
  end.

Definition eD M : linhom_car Ar (coalg_obj (ctxD_cbv (drop_names G)))
                                (coalg_obj (tyD_cbv t)) :=
  icones_to_linhom (eD_cbv M).
```

The `ne_fix` clause is the composite $\mathtt{fix\_comb} \circ
\llbracket\lambda s.\mathrm{body}\rrbracket$: the self-abstraction is
interpreted as an *ordinary* lambda (the `ne_lam` clause, inlined because
`ne_lam s body` is not a subterm of `ne_fix s body`), then post-composed
with the seeded value-fixpoint combinator $\mathtt{fix\_comb} :
\mathrm{EM}(\widetilde{!}(!L \multimap {!L}), \widetilde{!}L)$ of
`theories/programs/infra/em_fix_value.v`, at $L := U\llbracket
t_1\rrbracket \multimap U\llbracket t_2\rrbracket$ — see
[the CBV value-fixpoint
chapter](../../ppl/chapters/ppl-ch-the-cbv-value-fixpoint-at-function-types.html).
The `ne_fix_mr` clause dispatches on the body type (`fix_mr_clause`): the
same `fix_comb` composite at `tfun`, the Seely-transported `fix_mr_comb`
at products of frees. Every other clause is built only from the SMC
primitives (`linhom_comp`, `tensor_mor`, `tensor_braid`, `tensor_curry` /
`tensor_uncurry`) and the coalgebra-comonoid pair (`coalg_d`,
`coalg_e`).

### Def 2.5 — Constant icones helpers (`sample_icones`, `real_icones`, `bernoulli_icones`)

Each effect / value constructor (`ne_sample`, `ne_real`, `ne_bernoulli`,
`ne_true`, `ne_false`) denotes a *constant* `icones_hom` out of the
context: the counit $\varepsilon_\Gamma$ discards the context, then the
constant value (a unit-ball measure, Dirac, or two-point distribution) is
injected through `const_icones` of `theories/programs/ppl.v`.

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

With `tyD_cbv tbool = bool_cone_coalg`, the carrier of
$\llbracket\mathtt{tbool}\rrbracket$ is `bool_cone_car Ar` directly (not
`Bang _`), so the value is the basis point `bool_dirac_true` itself — no
`prom` wrap needed.

### Law 2.6 — The value-dependent Bernoulli lift (`bern_lift`, `bern_lift_P`, `score_lift_P`)

> **Key result:** the total-mass law `bern_lift_mass` is what makes the rejection-sampling per-iterate mass recurrence affine.

The semantic engine of `ne_bernoulli_f`: an `icones_hom (FMeas R_obj)
(bool_cone_car Ar)` sending a measure $\mu$ on the reals to the 2-point
sub-probability $(\int f\,d\mu,\ \int (1 - f)\,d\mu)$ — sample $r \sim
\mu$, then flip a coin with success probability $f\,r$. It lives in
`theories/programs/ppl.v` (Section BernTmLift), and the `ne_bernoulli_f`
clause of `eD_cbv` post-composes it with the scrutinee's denotation,
exactly as `ne_score` post-composes `score_lift`.

The construction is the *path route*, a verbatim clone of the score lift:
package $r \mapsto \mathtt{bernoulli}\,(f\,(\mathtt{cR}\,r))$ as a
measurable path into `bool_cone_car Ar` (the three bool-cone tests
evaluate along the path to $f \circ \mathtt{cR}$, $1 - f \circ
\mathtt{cR}$ and the constant $1$), then promote with `int_to_linhom`.
The integral semantics follows automatically by Pettis uniqueness against
the componentwise integral `bool_int` of
`theories/programs/infra/bool_cone.v`.

```coq
(* theories/programs/ppl.v (Section BernTmLift) *)
(** The lift as an [icones_hom]. *)
Definition bern_lift :
    icones_hom Ar (FMeas R_obj) (bool_cone_car Ar) :=
  linhom_icones (int_to_linhom bern_path) bern_int_norm_le1.

(** On a Dirac at [R_to_carrier r], the lift evaluates to the
    Bernoulli element [(f r, 1 - f r)]. *)
Lemma bern_lift_dirac (r : R) :
  Lfun bern_lift (dirac_fmeas (R_to_carrier R_carrier_eq r)) =
  bernoulli (f r) (Hf_ge0 r) (Hf_le1 r).

(** Coordinate readings: the [true]-coordinate is [∫ f dµ] … *)
Lemma bern_lift_t_E (mu : fmeas R (ar_carrier Ar R_obj)) :
  ((bc_t (Lfun bern_lift mu))%:num)%R =
  fine (\int[fmeas_mu mu]_(r in [set: ar_carrier Ar R_obj])
          (f (cR r))%:E).

(** … and the [false]-coordinate is [∫ (1 - f) dµ]. *)
Lemma bern_lift_f_E (mu : fmeas R (ar_carrier Ar R_obj)) :
  ((bc_f (Lfun bern_lift mu))%:num)%R =
  fine (\int[fmeas_mu mu]_(r in [set: ar_carrier Ar R_obj])
          ((1 - f (cR r))%R)%:E).
```

The load-bearing law for the rejection-sampling headline is the
total-mass identity: the coin is norm-1 *pointwise* (it always lands), so
the lift preserves total mass — with $\lVert\mu\rVert = 1$ the reject
weight is exactly $1 - \int f\,d\mu$, which makes the headline's
per-iterate mass recurrence affine.

```coq
(* theories/programs/ppl.v (Section BernTmLift) *)
Lemma bern_lift_mass (mu : fmeas R (ar_carrier Ar R_obj)) :
  cone_norm (Lfun bern_lift mu) =
  fine (fmeas_mu mu [set: ar_carrier Ar R_obj]).
```

The `tProb` surface needs the same two lifts at an *arbitrary* base
object — the $[0,1]$ object `po_obj P` of a bundle `P : probObj` — not
just at `R_obj`. `bern_lift_P P` and `score_lift_P P` instantiate the
path route at $X := \mathtt{po\_obj}\ P$ with the carrier density
`po_density P` and the bundle's $[0,1]$ witnesses (`po_ge0` / `po_le1`),
with no `R_to_carrier` round trip: `bern_lift_P` is the engine behind
`Bernoulli e`, `score_lift_P` behind `Score e`. The Dirac and mass laws
transport verbatim (`bern_lift_P_dirac`, `score_lift_P_dirac`).

```coq
(* theories/programs/ppl.v *)
Definition bern_lift_P (P : probObj Ar) :
    icones_hom Ar (FMeas (po_obj P)) (bool_cone_car Ar) := (* … *).
Definition score_lift_P (P : probObj Ar) :
    icones_hom Ar (FMeas (po_obj P)) (cone_one_car Ar) := (* … *).
```

### Def 2.7 — If-then-else at the icones level (`if_icones`, `if_under`)

The CBV value-level if-then-else takes two branches $m, n :
\mathtt{icones\_hom}\ G \to A$ and a scrutinee $b : G \to
\mathtt{bool\_cone}$ and returns a clean $\mathtt{icones\_hom}\ G \to A$,
with no Kleisli wrapping at any step. It is the *single* consumer-side
packaging of the boolean cascade: the branches are co-paired by
`bool_case_linhom`, SMCC-uncurried over $\mathtt{bool\_cone} \otimes G$,
braided, and finally pre-composed with the EM pairing $\langle
\mathrm{id}_G, b\rangle$.

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

With the §9.7 `bool_cone_coalg` on the scrutinee side, no `der` dance is
needed — the scrutinee directly produces `bool_cone_car Ar`. The building
blocks (`bool_case_linhom`, the 2-point cone, the §9.7 coalgebra) are
documented in [the boolean-cascade
chapter](../../ppl/chapters/ppl-ch-the-boolean-cascade.html).

### Law 2.8 — The definitional-unfolding pack (`eD_var_E`, `eD_fix_mr_prod_E`)

One lemma per `eD_cbv` clause — 25 in total: one for each of the 23
`named_expr` constructors, plus the two per-body-type refinements
`eD_fix_mr_fun_E` / `eD_fix_mr_prod_E` of the dispatched `ne_fix_mr`
clause. Each pins the exact clause body, so any refactor of `eD_cbv` (or
its combinators) breaks loudly in a named lemma instead of silently
changing the semantics.

Because `eD_cbv` is a structural `Fixpoint`, every clause reduces
definitionally on its constructor and every proof is `by []`. The pack
lives at the end of `theories/programs/ppl_cbv.v` (Section EDUnfold);
three representative members:

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

(** [ne_fix]: the genuine value-fixpoint —
    [⟦fix s.M⟧ = fix_comb ∘ ⟦λs.M⟧] ([fix_comb] of [em_fix_value.v]
    post-composed with the inlined [ne_lam] packaging of the body). *)
Lemma eD_fix_E (G : named_ctx Ar) (s : string) (t1 t2 : ppl_type Ar)
    (M : @named_expr R Ar R_obj ((s, tfun t1 t2) :: G) (tfun t1 t2)) :
  eD_cbv' (ne_fix s M) =
  icones_comp
    (ch_mor (fix_comb (linhom_car Ar (coalg_obj (tyD_cbv t1))
                                     (coalg_obj (tyD_cbv t2)))))
    (ch_mor (adj_psi (P := ctxD_cbv (drop_names G))
                     (B := linhom_car Ar
                             (coalg_obj (tyD_cbv (tfun t1 t2)))
                             (coalg_obj (tyD_cbv (tfun t1 t2))))
             (tensor_curry (eD_cbv' M)))).
Proof. by []. Qed.

(* … 22 more: eD_tt_E, eD_pair_E, eD_fst_E, eD_snd_E, eD_lam_E,
   eD_app_E, eD_sample_E, eD_real_E, eD_score_E, eD_add_E, eD_mul_E,
   eD_meas_E, eD_gaussian_E, eD_uniform_E,
   eD_true_E, eD_false_E, eD_bernoulli_E, eD_bernoulli_f_E, eD_if_E,
   eD_fix_mr_E, eD_fix_mr_fun_E, eD_fix_mr_prod_E. *)
```

The *semantic* recursion-unfolding equations — the prom-point
computation law `eD_fix_at_setlike` and the honest recursion equation
`eD_fix_unfold` — live in `theories/programs/infra/cbv_fix_unfold.v`
(they need the setlike-point kit of `infra/cbv_anchors.v`, which imports
this file); they are documented with the fixpoint combinator in [the CBV
value-fixpoint
chapter](../../ppl/chapters/ppl-ch-the-cbv-value-fixpoint-at-function-types.html).

---

## The SCones↔ICones-tensor bilinear stability bridge

**In this chapter:** [Law 3.1](../../ppl/sections/ppl-sec-law-3-1-lift-linhom-stablehom.html) · [Law 3.2](../../ppl/sections/ppl-sec-law-3-2-the-diagonal-bilinear-stability-bridge.html).

This chapter records the `stable/`-side infrastructure (paper-§7
material) consumed by the CBV value-fixpoint. The lift
`linhom_to_stablehom` is what lets the fixpoint chapter's
`fix_value` assemble a *stable* map out of linear data; it is the
first ingredient of `fix_lts` in
`theories/programs/infra/em_fix_value.v`. The main statement is the
diagonal bridge: given a measurable-stable `K : G → A` and a
bilinear `Φ : G ⊗ A → B` in `ICones`, the diagonal evaluation
`g ↦ Φ(g ⊗ K(g)) : G → B` is measurable-stable. The proof is pure
structural composition through paper Theorem 5.12's
tensor↔internal-hom adjunction; no §7.3 finite-difference replay is
required.

| Construction | Rocq |
|---|---|
| Lifting `linhom → stablehom` is meas-stable (Lem 7.31 at internal-hom) | `linhom_to_stablehom`, `linhom_to_stablehom_meas_stable` — `theories/stable/diag_bilinear_tensor.v` |
| Composition with an `icones_hom` preserves meas-stability | `meas_stable_comp_post`, `meas_stable_comp_pre` — same file |
| The diagonal stable pairing | `id_spair_meas_stable`, `spair_meas_stable` — same file |
| **The deliverable** — diagonal bilinear stability bridge | `meas_stable_diag_bilinear_tensor` — same file |

### Law 3.1 — Lift `linhom → stablehom` (`linhom_to_stablehom`)

Every inhabitant of the internal hom `linhom_car Ar B C` is a stable
and measurable map of cones, and the packaging function
`linhom_to_stablehom : linhom_car Ar B C → stablehom B C` is *itself*
measurable-stable — the internal-hom version of paper Lemma 7.31.
This is the lift the CBV value-fixpoint consumes: `fix_lts` of
`theories/programs/infra/em_fix_value.v` applies it to the
post-action `F ↦ der ∘ F`, feeding `fix_value` — see
[the CBV value-fixpoint
chapter](../../ppl/chapters/ppl-ch-the-cbv-value-fixpoint-at-function-types.html).

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

### Law 3.2 — The diagonal bilinear stability bridge (`meas_stable_diag_bilinear_tensor`)

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

---

## The CBV value-fixpoint at function types

**In this chapter:** [Thm 4.1](../../ppl/sections/ppl-sec-thm-4-1-the-degeneracy-theorem.html) · [Def 4.2](../../ppl/sections/ppl-sec-def-4-2-the-naive-linear-kleene-step.html) · [Def 4.3](../../ppl/sections/ppl-sec-def-4-3-the-seeded-kleene-core.html) · [Def 4.4](../../ppl/sections/ppl-sec-def-4-4-the-interleaved-chain-and-the-value-map.html) · [Def 4.5](../../ppl/sections/ppl-sec-def-4-5-the-combinator.html) · [Law 4.6](../../ppl/sections/ppl-sec-law-4-6-coalgebraic-bodies-the-literal-chain.html) · [Law 4.7](../../ppl/sections/ppl-sec-law-4-7-non-degeneracy.html) · [Def 4.8](../../ppl/sections/ppl-sec-def-4-8-the-mutual-recursion-transport.html) · [Law 4.9](../../ppl/sections/ppl-sec-law-4-9-the-interpreter-wiring.html) · [Law 4.10](../../ppl/sections/ppl-sec-law-4-10-the-recursion-unfolding-equations.html) · [Def 4.11](../../ppl/sections/ppl-sec-def-4-11-the-scones-fixpoint-core.html).

The CBV-side `let rec` is the value-fixpoint *combinator*
`fix_comb : EM( !̃(!A ⊸ !A), !̃A )` — a morphism of `!`-coalgebras
between the cofree coalgebras, determined on promoted bodies `F!`
(for `F` in the unit ball of `!A ⊸ !A`) by
`fix_comb (F!) = (sup_n x_n)!`, where `x_0 = 0 : A` and
`x_{n+1} = der (F (x_n !))` is the *interleaved* Kleene chain. It
lives in `theories/programs/infra/em_fix_value.v` and is what the
`ne_fix` clause (and `ne_fix_mr` at every free body type) of
`ppl_cbv.v` post-composes onto the body's lambda packaging:
`⟦fix s.body⟧ = fix_comb ∘ ⟦λs.body⟧` — directly at function body
types, and through the Seely transport of
`theories/programs/infra/em_fix_mr.v` at products of free types.

The chapter tells the story in three beats.

- *Degeneracy.* The zero-seeded iteration — the Kleene iteration of
  `theories/programs/infra/em_fix.v`'s linear step
  `prev ↦ M ∘ (id ⊗ prev) ∘ δ` from the linhom cone-zero, which used to
  be `em_fix.v`'s CBV value-fixpoint operator before its removal — is
  *provably the zero linhom*, always (`Phi_fun_lfp_eq0`): a linear step
  preserves the zero seed, and the bottom of a CBV function-value type is
  not the cone-zero of `!L` but the promoted zero `(0)!`, the
  diverging-function value of `e_bang`-mass one.
- *Repair.* Seed the iteration at the genuine bottom `0 : A` *under* the
  promotion, interleaving `der` and `prom` so each iterate re-enters the
  body as a promoted value. The `prom ∘ der` sandwich makes the chain
  productive for *any* unit-ball body, linear or not (the step
  `x ↦ der (F (x!))` is monotone because `prom` is totally monotone and
  `F`, `der` are linear). Coalgebra-morphism-ness comes for free: the
  value map `F ↦ sup_n x_n` is built from existing `SCones` morphisms,
  converted to a linear map `!(!A ⊸ !A) ⊸ A` by the SAFT hom-bijection
  `lin`, and packaged by `adj_psi` of the `U ⊣ !̃` adjunction.
- *Transport.* A product of free types is not literally cofree, but it is
  *isomorphic* to a cofree coalgebra through the EM-level Seely-2 iso;
  conjugating `fix_comb` by that iso makes `ne_fix_mr` genuine at every
  free body type.

| Construction | Rocq |
|---|---|
| The degeneracy theorem: the naive zero-seeded iteration is the zero linhom | `Phi_fun_lfp_eq0`, `Phi_fun_zero`, `kleene_lin_Phi_fun_eq0` — `theories/programs/infra/em_fix_value.v`; the generic collapse `lfp_eq0` — `theories/stable/fixpoint.v` |
| The naive linear Kleene step and the linhom LFP core (the operator itself was removed after the degeneracy proof) | `Phi_fun`, `kleene_lin`, `linhom_lfp`, `linhom_lfp_fixpoint` — `theories/programs/infra/em_fix.v` |
| Seeded Kleene core on any cone (`b0 ≤ f b0` replaces the zero seed) | `kleene_from`, `lfp_from`, `lfp_from_fixpoint` — `theories/programs/infra/em_fix_value.v` |
| The interleaved chain `x_{n+1} = der (F (x_n!))` | `fix_chain`, `fix_chain_S`, `fix_chain_ball`, `fix_chain_chain` — same file |
| The stable value map `F ↦ sup_n x_n` in `SCones` | `fix_value`, `fix_value_E`, `fix_value_unfold` — same file |
| The combinator as an EM morphism, and its computation law | `fix_comb`, `fix_comb_mor`, `fix_prom_E` — same file |
| Obligation (b): coalgebraic bodies give the literal chain | `fix_setlike_prom`, `fix_coalg_simpl`, `fix_unfold_coalg` — same file |
| Non-degeneracy witnesses | `fix_prom_neq0`, `fix_id_E`, `fix_id_nontrivial` — same file |
| Isomorphisms of `!`-coalgebras (id / sym / trans / `EM_prod` congruence) | `coalg_iso`, `coalg_iso_id`, `coalg_iso_sym`, `coalg_iso_trans`, `coalg_iso_prod`, `coalg_hom_prod` — `theories/programs/infra/em_fix_mr.v` |
| The EM-level Seely-2 iso `EM_prod (!̃X) (!̃Y) ≅ !̃(X & Y)` | `seely2_em_iso`, `EM_prod_str_cofree2`, `seely2_fwd_is_coalg_mor`, `seely2_bwd_is_coalg_mor` — same file |
| The transported combinator, its computation law and norm bound | `fix_comb_iso`, `fix_iso_body_conj`, `fix_comb_iso_prom_E`, `fix_comb_iso_norm` — same file |
| The free-type decomposition `tyD_cbv t ≅ !̃(free_base t)` | `free_base`, `free_decomp`, `is_free_prodl`, `is_free_prodr`, `fix_mr_comb` — `theories/programs/ppl_cbv.v` |
| The interpreter wiring `⟦fix s.body⟧ = fix_comb ∘ ⟦λs.body⟧` | `eD_fix_E`, `eD_fix_mr_fun_E`, `eD_fix_mr_prod_E`, `fix_mr_clause` — `theories/programs/ppl_cbv.v` |
| The recursion-unfolding equations at setlike points | `eD_fix_at_setlike`, `eD_fix_unfold`, `eD_fix_at_one1`, `eD_fix_unfold_closed`, `eD_fix_mr_prod_at_setlike`, `eD_fix_mr_prod_at_setlike_neq0` — `theories/programs/infra/cbv_fix_unfold.v` |

### Thm 4.1 — The degeneracy theorem (`Phi_fun_lfp_eq0`)

> **Key result:** the naive zero-seeded value-fixpoint is *provably the zero linhom* — the reason the seeded combinator exists.

For *every* diagonal `diag` and every body `M`, the zero-seeded
Kleene iteration `linhom_lfp (Phi_fun diag M) …` — the construction
that used to be `em_fix.v`'s CBV value-fixpoint operator — equals
the zero linhom. The structural reason: the Kleene step `Phi_fun` is
*linear* in the previous iterate, so it maps the linhom cone-zero
seed to the cone-zero (`Phi_fun_zero` — the `id_Γ ⊗ 0` tensor
vanishes by bilinearity, then post-composition by the linear `M`
preserves zero); by induction every Kleene iterate is zero
(`kleene_lin_Phi_fun_eq0`), and so is the supremum. The collapse
itself is generic — `lfp_eq0` of `theories/stable/fixpoint.v`: any
Kleene step that preserves the zero seed has zero least fixpoint —
so the degeneracy record is exactly `Phi_fun_zero` (the linearity
content) plus the generic lemma.

```coq
(* theories/stable/fixpoint.v (Section KleeneCore) *)
(** ... the least fixpoint collapses to zero: the supremum of the
    constantly-zero chain is zero. *)
Lemma lfp_eq0 : f 0 = 0 -> lfp = (0 : B).

(* theories/programs/infra/em_fix_value.v (Section CbvFixDegeneracy) *)
(** STEP B: the Kleene step kills zero. *)
Lemma Phi_fun_zero : Phi_fun diag M precone_zero = precone_zero.

(** STEP C: every Kleene iterate is zero. *)
Lemma kleene_lin_Phi_fun_eq0 n :
  kleene_lin (Phi_fun diag M) n = precone_zero.

(** STEP D: the zero-seeded Kleene iteration of the naive linear step
    is the zero linhom — DEGENERACY. *)
Lemma Phi_fun_lfp_eq0 :
  linhom_lfp (Phi_fun diag M) (Phi_fun_incr diag M) (Phi_fun_ball diag M) =
  precone_zero.
```

The diagnosis behind the repair: the bottom of a CBV function
*value* type is not the cone-zero of `!L` — it is the promoted zero
`(0)!`, the diverging-function value, which has `e_bang`-mass one
and is therefore not even close to `precone_zero` in the cone order.
A least fixpoint computed from the wrong bottom is the wrong least
fixpoint.

### Def 4.2 — The naive linear Kleene step (`Phi_fun`)

The step that the degeneracy theorem is about: `Phi_fun` sends a
candidate denotation `prev : Γ ⊸ B` to `M ∘ (id_Γ ⊗ prev) ∘ diag` —
"run the body with `prev` bound to the recursive variable" —
extended trivially off the unit ball. Its zero-seeded Kleene
supremum on the unit-ball ω-CPO of `linhom_car Ar Γ B` (via
`em_fix.v`'s linhom LFP core `linhom_lfp`, with the ball bound and
the fixpoint equation `linhom_lfp_fixpoint`) used to be `em_fix.v`'s
CBV value-fixpoint operator.

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
```

The construction, the ball bound and the fixpoint equation are all
true — and all satisfied by the zero linhom, which is exactly what
`Phi_fun_lfp_eq0` shows the iteration is. The operator itself was
removed from `em_fix.v` after the degeneracy proof; the record
survives as `Phi_fun_zero` plus the generic `lfp_eq0`. The step
`Phi_fun`, its three unit-ball laws and the linhom LFP core stay:
they are the scaffolding of the genuine seeded combinator below. The
interpreter never routes through the zero-seeded iteration — the
`ne_fix_mr` *product* case, formerly the last consumer of the
removed operator, goes through the genuine Seely-transported
combinator (see the mutual-recursion transport section below).

### Def 4.3 — The seeded Kleene core (`kleene_from`, `lfp_from`)

The generic Kleene chain `n ↦ fⁿ(b0)` for an *arbitrary* seed `b0`
with `b0 ≤ f b0` replacing the `precone_le0` base of the zero-seeded
chains, stated on a bare `coneType` so that it covers both
cone-point chains (the literal chain `Fⁿ(0!)` of obligation (b)
below) and linhom-level chains. The fixpoint equation holds under
ω-continuity of the step on the ball.

```coq
(* theories/programs/infra/em_fix_value.v (Section SeededKleene) *)
(** The seeded Kleene chain [n ↦ fⁿ(b0)]. *)
Definition kleene_from (n : nat) : B := iter n f b0.

(** The seeded least-fixpoint candidate (sup of the seeded chain). *)
Definition lfp_from : B :=
  cone_sup_ball kleene_from kleene_from_chain kleene_from_ball.

(** The fixpoint equation, under ω-continuity of [f] on the ball. *)
Lemma lfp_from_fixpoint : f lfp_from = lfp_from.
```

### Def 4.4 — The interleaved chain and the value map (`fix_chain`, `fix_value`)

Fix `A` and write `!A := Bang Ar A`. The interleaved chain of a body
`F : !A ⊸ !A` (abbreviated `LL` in the snippets below) is `x_0 = 0 : A`,
`x_{n+1} = der (F (x_n !))`: each iterate is *re-promoted* before it
re-enters the body and *dereferenced* after — so the body always
sees a legitimate (promoted) function value, and the chain lives in
`A` where the genuine bottom is `0`. Monotonicity needs no linearity
of the assignment `F ↦ x_n`: `prom` is totally monotone (it is the
underlying map of the stable `nl`), and `F` and `der` are linear
(`fix_step_incr`).

```coq
(* theories/programs/infra/em_fix_value.v (Section FixCombinator) *)
Definition fix_chain (F : LL) (n : nat) : A :=
  iter n (fun x : A => Lfun (der A) (linhom_fun F (prom x)))
         (precone_zero : A).

(** Per-iterate access law. *)
Lemma fix_chain_S (F : LL) (n : nat) :
  fix_chain F n.+1 = Lfun (der A) (linhom_fun F (prom (fix_chain F n))).
```

The assignment `F ↦ sup_n x_n` is then packaged as a *stable* map —
obligation (a) of the construction. It is the composite of existing
`SCones` morphisms (so total monotonicity, ω-continuity and
path-measurability come for free): the linear-to-stable lift
`linhom_to_stablehom` of the post-action `F ↦ der ∘ F`, curried
through the CCC of `stable/scones_ccc.v` against the `nl`-promotion
of the argument, and closed by the §9.2 fixpoint combinator `Yfix`
of `stable/fixpoint.v` — whose value at a unit-ball `f` is
identified with the plain Kleene supremum `sup_n fⁿ(0)`
(`Yfix_kleeneE`, same file).

```coq
(* theories/programs/infra/em_fix_value.v *)
Definition fix_value : scones_hom LL A :=
  scones_comp (Yfix A) fix_body.

(** The defining computation: [fix_value F] is the sup of the
    INTERLEAVED chain. *)
Lemma fix_value_E (F : LL) (HF : cone_norm F <= 1) :
  sc_fun fix_value F =
  cone_sup_ball (fix_chain F) (fix_chain_chain HF) (fix_chain_ball HF).

(** The fixpoint equation of the value map (from [Yfix_fix]). *)
Lemma fix_value_unfold (F : LL) (HF : cone_norm F <= 1) :
  Lfun (der A) (linhom_fun F (prom (sc_fun fix_value F))) =
  sc_fun fix_value F.
```

### Def 4.5 — The combinator (`fix_comb`, `fix_prom_E`)

A stable map `(!A ⊸ !A) → A` *is* a linear map `!(!A ⊸ !A) ⊸ A`
via the SAFT hom-bijection `lin`/`Theta` of `theories/homs/bang.v`
(`fix_lin := lin fix_value`, with the promoted-point computation
`fix_lin_promE`); `adj_psi` of the `U ⊣ !̃` adjunction then packages
the linear map as a morphism into the cofree coalgebra — so
`fix_comb` is a coalgebra morphism *by construction*, with no fresh
order analysis of the SAFT `Bang`.

```coq
(* theories/programs/infra/em_fix_value.v *)
Definition fix_comb :
    coalg_hom (bang_cofree (linhom_car Ar (Bang Ar A) (Bang Ar A)))
              (bang_cofree A) :=
  adj_psi (P := bang_cofree LL) fix_lin.

(** The prom-point computation law — the defining formula. *)
Lemma fix_prom_E (F : LL) (HF : cone_norm F <= 1) :
  Lfun (ch_mor fix_comb) (prom F) = prom (sc_fun fix_value F).
```

`fix_prom_E` is the law every consumer starts from: on a promoted
body the combinator returns the *promoted* interleaved-Kleene
supremum. Its proof composes `dig_prom` (the cofree structure map
promotes promoted points), `bang_fmap_prom` (the functorial action
computes on promoted points) and `fix_lin_promE`.

### Law 4.6 — Coalgebraic bodies: the literal chain (`fix_coalg_simpl`)

Obligation (b): when the body `F` is itself a morphism of
`!`-coalgebras `!A → !A`, the interleaved chain coincides with the
*literal* Kleene chain `n ↦ Fⁿ(0!)` in `!A`, seeded at the diverging
value `0!` — the naive iteration one would have written by hand. The
bridge is `fix_setlike_prom`: a coalgebraic body sends promoted
points to promoted points (`F(y!) = (der (F (y!)))!`, read off the
coalgebra-morphism square at `y!` plus the right counit law), so
promotion intertwines the two chains (`fix_iter_promE`).

```coq
(* theories/programs/infra/em_fix_value.v (Section FixCoalgebraic) *)
(** A coalgebraic body maps promoted points to promoted points. *)
Lemma fix_setlike_prom (y : A) (Hy : cone_norm y <= 1) :
  linhom_fun F (prom y) =
  prom (Lfun (der A) (linhom_fun F (prom y))).

(** On a coalgebraic body, the combinator is the supremum of the
    literal chain [n ↦ Fⁿ(0!)] (seeded Kleene in [!A]). *)
Lemma fix_coalg_simpl :
  Lfun (ch_mor (fix_comb A)) (prom F) =
  lfp_from (f := linhom_fun F) (b0 := prom (precone_zero : A))
    fix_lit_incr fix_lit_ball fix_seed_ball fix_seed_le.

(** The !A-level unfolding for coalgebraic bodies. *)
Lemma fix_unfold_coalg :
  linhom_fun F (Lfun (ch_mor (fix_comb A)) (prom F)) =
  Lfun (ch_mor (fix_comb A)) (prom F).
```

Note the seed-order obligation `0! ≤ F(0!)` (`fix_seed_le`) — the
base case the zero-seeded `linhom_lfp` could never provide, and the
reason the seeded Kleene core of this file exists.

### Law 4.7 — Non-degeneracy (`fix_prom_neq0`, `fix_id_E`)

On *every* promoted body the combinator returns a promoted point of
`!A`, and a promoted point is never the cone-zero (its `e_bang`-mass
is `one1`) — the direct contrast with `Phi_fun_lfp_eq0`. The
simplest honest instance is the identity body: its interleaved chain
is constantly `0` (since `der (0!) = 0`), so `fix_comb (id!) = 0!` —
the *diverging value*, which is provably nonzero.

```coq
(* theories/programs/infra/em_fix_value.v *)
Lemma fix_prom_neq0 (F : LL) (HF : cone_norm F <= 1) :
  Lfun (ch_mor fix_comb) (prom F) <> precone_zero.

(** [fix_comb (id!) = 0!] — the diverging value. *)
Lemma fix_id_E :
  Lfun (ch_mor (fix_comb A)) (prom fix_idF) = prom (precone_zero : A).

(** The witness: the fix of the identity body is NOT zero. *)
Lemma fix_id_nontrivial :
  Lfun (ch_mor (fix_comb A)) (prom fix_idF) <> precone_zero.
```

### Def 4.8 — The mutual-recursion transport (`seely2_em_iso`, `fix_comb_iso`, `fix_mr_comb`)

The layer that makes `ne_fix_mr` genuine at *products* of free
types, in `theories/programs/infra/em_fix_mr.v` plus the
decomposition layer of `theories/programs/ppl_cbv.v`. The problem:
`fix_comb` lives on *cofree* coalgebras, but the CBV interpretation
of a product is `tyD_cbv (tprod s t) = EM_prod (tyD s) (tyD t)` —
not literally cofree. The solution, in three moves.

**Isomorphisms of `!`-coalgebras.** `coalg_iso P Q` bundles both
directions as `coalg_hom`s plus the two round-trips at the
underlying-`icones_hom` level, with identity / symmetry /
transitivity and the `EM_prod` congruence `coalg_iso_prod` (the
tensor of two coalg isos, via `EM_prod_mor`).

**The Seely-2 iso at the EM level.** For cofree coalgebras the
product *is* cofree on the `&`-product (`sprod`, the cone product —
note: `&`, not the tensor) of the base cones:

```coq
(* theories/programs/infra/em_fix_mr.v (Section Seely2EM) *)
Definition seely2_em_iso (X Y : ICone.type Ar) :
    coalg_iso (EM_prod (bang_cofree X) (bang_cofree Y))
              (bang_cofree (sprod X Y)) :=
  MkCoalgIso (ci_fwd := MkCoalgHom (seely2_fwd_is_coalg_mor X Y))
    (ci_bwd := MkCoalgHom (seely2_bwd_is_coalg_mor X Y))
    (iso_fwdK (Seely2 X Y)) (iso_bwdK (Seely2 X Y)).
```

The carrier of `EM_prod (!̃X) (!̃Y)` is `!X ⊗ !Y` and its structure
map is the `Seely2`-transported `tens_cofree_str`
(`EM_prod_str_cofree2`), so the coalgebra-morphism squares for the
two directions of `Seely2 : !X ⊗ !Y ≅ !(X & Y)` are pure transport
algebra (`seely2_fwd_is_coalg_mor` / `seely2_bwd_is_coalg_mor` —
no point computation).

**The transported combinator.** For any coalgebra `P` with
`iso : coalg_iso P (!̃Z)`, conjugating `fix_comb Z` by the iso gives
`fix_comb_iso iso : EM( !̃(U P ⊸ U P), P )`: bodies `F : U P ⊸ U P`
transport to `!Z ⊸ !Z` by pre/post-composition with the iso's
underlying linear maps (`fix_iso_body_conj`, the hom-functor action
`linhom_map_icones`), the genuine fixpoint runs at `Z`, and the
result is carried back by the iso's backward map. The computation
law is the analogue of `fix_prom_E`:

```coq
(* theories/programs/infra/em_fix_mr.v (Section FixCombIso) *)
Lemma fix_comb_iso_prom_E (F : linhom_car Ar UP UP)
    (HF : cone_norm F <= 1) :
  Lfun (ch_mor fix_comb_iso) (prom F) =
  Lfun (ch_mor (ci_bwd iso))
    (prom (sc_fun (fix_value Z)
       (linhom_map_fun (ch_mor (ci_bwd iso)) (ch_mor (ci_fwd iso)) F))).
```

with the norm bound `fix_comb_iso_norm`. On the `ppl_cbv.v` side,
`free_base t` computes the base cone of a free type (`tfun t1 t2 ↦
U⟦t1⟧ ⊸ U⟦t2⟧`; `tprod t1 t2 ↦ sprod (free_base t1) (free_base
t2)`) and `free_decomp t Hfree : coalg_iso (tyD_cbv t) (!̃(free_base
t))` builds the decomposition by structural induction on the
`is_free_coalg_type` witness — the `tfun` case is the identity iso
(the interpretation *is* `bang_cofree`), the `tprod` case composes
the children's isos (`coalg_iso_prod`) with `seely2_em_iso`.
`fix_mr_comb t Hfree := fix_comb_iso (free_decomp t Hfree)` is then
the genuine value-fixpoint combinator at every free type.

```coq
(* theories/programs/ppl_cbv.v (Section FreeDecomp) *)
Definition fix_mr_comb (t : ppl_type Ar) (Hfree : is_free_coalg_type t) :
    coalg_hom (bang_cofree (linhom_car Ar (coalg_obj (tyD_cbv t))
                                          (coalg_obj (tyD_cbv t))))
              (tyD_cbv t) :=
  fix_comb_iso (@free_decomp t Hfree).
```

The surface witness is the mutual-recursion pair `ex_even_odd_pair`
of `theories/programs/examples.v` (one recursive name at
`tprod (tfun tunit tunit) (tfun tunit tunit)`, each component
calling the other through `fst`/`snd`). Its operational identity is
honest divergence: each component delegates to the other with no base
case, so `ex_even_cbv_diverges` / `ex_odd_cbv_diverges` pin the closed
runs `ex_even @ ()` / `ex_odd @ ()` to the unit-cone zero (mass `0`),
while the pair value itself is `0! ⊗p 0!`
(`ex_even_odd_pair_cbv_value`), never the cone-zero — see
the [Examples tab](../examples/).

### Law 4.9 — The interpreter wiring (`eD_fix_E`, `fix_mr_clause`)

The `ne_fix` clause of `eD_cbv` is the composite
`fix_comb ∘ ⟦λs.body⟧`: the self-abstraction is interpreted as an
ordinary lambda (`adj_psi (tensor_curry ⟦body⟧)`, the `ne_lam`
clause inlined), then post-composed with `fix_comb` at
`L := U⟦t1⟧ ⊸ U⟦t2⟧`. The clause pins are definitional (`by []`).

```coq
(* theories/programs/ppl_cbv.v (Section EDUnfold) *)
Lemma eD_fix_E (G : named_ctx Ar) (s : string) (t1 t2 : ppl_type Ar)
    (M : @named_expr R Ar R_obj ((s, tfun t1 t2) :: G) (tfun t1 t2)) :
  eD_cbv' (ne_fix s M) =
  icones_comp
    (ch_mor (fix_comb (linhom_car Ar (coalg_obj (tyD_cbv t1))
                                     (coalg_obj (tyD_cbv t2)))))
    (ch_mor (adj_psi (P := ctxD_cbv (drop_names G))
                     (B := linhom_car Ar
                             (coalg_obj (tyD_cbv (tfun t1 t2)))
                             (coalg_obj (tyD_cbv (tfun t1 t2))))
             (tensor_curry (eD_cbv' M)))).
Proof. by []. Qed.
```

`ne_fix_mr` dispatches on the (free) body type through
`fix_mr_clause`: at `tfun t1 t2` the same genuine composite
(`eD_fix_mr_fun_E`); at `tprod`-of-frees the same composite with the
Seely-transported combinator `fix_mr_comb` of the previous section
(`eD_fix_mr_prod_E`) — the mutual-recursion fixpoint is genuine at
every free body type.

```coq
(* theories/programs/ppl_cbv.v (Section EDUnfold) *)
(** [ne_fix_mr] at a PRODUCT body type: the GENUINE Seely-transported
    composite — [fix_mr_comb] (= [fix_comb (free_base _)] conjugated by
    [free_decomp]) post-composed with the lambda-packaging of the body. *)
Lemma eD_fix_mr_prod_E (G : named_ctx Ar) (s : string)
    (t1 t2 : ppl_type Ar)
    (Hfree : is_free_coalg_type (tprod t1 t2))
    (M : @named_expr R Ar R_obj ((s, tprod t1 t2) :: G) (tprod t1 t2)) :
  eD_cbv' (ne_fix_mr s (tprod t1 t2) Hfree M) =
  icones_comp
    (ch_mor (fix_mr_comb (tprod t1 t2) Hfree))
    (ch_mor (adj_psi (P := ctxD_cbv (drop_names G))
                     (B := linhom_car Ar
                             (coalg_obj (tyD_cbv (tprod t1 t2)))
                             (coalg_obj (tyD_cbv (tprod t1 t2))))
             (tensor_curry (eD_cbv' M)))).
Proof. by []. Qed.
```

### Law 4.10 — The recursion-unfolding equations (`eD_fix_at_setlike`, `eD_fix_unfold`)

The semantic laws of the wired `ne_fix` clause, stated at *setlike*
unit-ball context points (`coalg_str Γ γ = γ!` — the §9.7 "γ is a
sub-Dirac" reading) in
`theories/programs/infra/cbv_fix_unfold.v`. Writing
`F_γ := curry ⟦body⟧ γ : !L ⊸ !L` for the body's endo-function at
`γ`:

- `eD_fix_at_setlike` — the prom-point *computation* law:
  `⟦fix s.body⟧ γ = (fix_value F_γ)!`, i.e. the denotation is the
  promoted supremum of the interleaved Kleene chain. In particular
  it is never the cone-zero (`eD_fix_at_setlike_neq0`).
- `eD_fix_unfold` — the honest *recursion equation*: one more body
  unfolding at the fixpoint value, re-promoted, is the fixpoint
  value.

```coq
(* theories/programs/infra/cbv_fix_unfold.v *)
Lemma eD_fix_at_setlike (G : named_ctx Ar) (s : string)
    (t1 t2 : ppl_type Ar)
    (body : @named_expr R Ar R_obj ((s, tfun t1 t2) :: G) (tfun t1 t2))
    (gam : coalg_obj (ctxD_cbv (drop_names G))) :
  cone_norm gam <= 1 ->
  Lfun (coalg_str (ctxD_cbv (drop_names G))) gam = prom gam ->
  Lfun (eD_cbv' (ne_fix s body)) gam =
  prom (sc_fun (fix_value (Lty t1 t2))
         (Lfun (tensor_curry (eD_cbv' body)) gam)).

(** THE recursion equation:
    [( der (F_γ (⟦fix s.body⟧ γ)) )! = ⟦fix s.body⟧ γ]. *)
Lemma eD_fix_unfold (G : named_ctx Ar) (s : string)
    (t1 t2 : ppl_type Ar)
    (body : @named_expr R Ar R_obj ((s, tfun t1 t2) :: G) (tfun t1 t2))
    (gam : coalg_obj (ctxD_cbv (drop_names G))) :
  cone_norm gam <= 1 ->
  Lfun (coalg_str (ctxD_cbv (drop_names G))) gam = prom gam ->
  prom (Lfun (der (Lty t1 t2))
         (linhom_fun (Lfun (tensor_curry (eD_cbv' body)) gam)
            (Lfun (eD_cbv' (ne_fix s body)) gam))) =
  Lfun (eD_cbv' (ne_fix s body)) gam.
```

The closed-program corollaries `eD_fix_at_one1` /
`eD_fix_unfold_closed` (same file) state both laws against the
public linhom interpreter `eD` at the unit context point `one1`
(which is setlike, `coalg_str_one1`). The same two laws also hold
verbatim for `ne_fix_mr` at function body types
(`eD_fix_mr_fun_at_setlike` / `eD_fix_mr_fun_unfold`); at *product*
body types the computation law is the Seely-transported analogue
`eD_fix_mr_prod_at_setlike` — the denotation at a setlike `γ` is the
backward transport along `free_decomp` of the promoted fixpoint
value of the conjugated body (`fix_comb_iso_prom_E`), never the
cone-zero (`eD_fix_mr_prod_at_setlike_neq0`). These
equations live in their own file because the setlike-point kit they
consume (`infra/cbv_anchors.v`) imports `ppl_cbv.v` — an import
cycle would result if they sat next to the definitional clause pins.

### Def 4.11 — The SCones fixpoint core (`Yfix`)

The stable-fixpoint core is `Yfix : scones_hom BB B` of
`theories/stable/fixpoint.v` — [paper
§9.2](../../paper/entries/sect-9-2.html): the Kleene fixpoint at the
`SCones` internal hom, a unit-ball chain from `precone_zero` taken
as a supremum. At a bare `SCones` function space the zero seed *is*
the right bottom, and `Yfix` serves recursion directly; at a CBV
function-*value* type the bottom is the promoted zero `0!` instead,
so `Yfix` appears one level down, *inside* the construction of
`fix_value` (`Yfix_kleeneE` identifies its value with the plain
Kleene supremum), with the seeding repaired by the `der`/`prom`
interleaving above.

```coq
(* theories/stable/fixpoint.v *)
(** Paper §9.2: the least-fixpoint combinator [Y], as a morphism of
    [SCones]. *)
Definition Yfix : scones_hom BB B :=
  MkSconesHom (sh_fun Yfix_elt) (sh_meas_stable Yfix_elt) Yfix_norm_le1
    (sh_offball Yfix_elt).
```

---

## CBV semantic laws and regression anchors

**In this chapter:** [Law 5.1](../../ppl/sections/ppl-sec-law-5-1-the-let-at-sample-integral-law.html) · [Law 5.2](../../ppl/sections/ppl-sec-law-5-2-the-affine-cascade-and-the-sup-mass-bridge.html) · [Def 5.3](../../ppl/sections/ppl-sec-def-5-3-the-setlike-point-kit.html) · [Law 5.4](../../ppl/sections/ppl-sec-law-5-4-the-sharing-semantics-anchors.html) · [Law 5.5](../../ppl/sections/ppl-sec-law-5-5-the-rule-and-the-if-pins.html) · [Law 5.6](../../ppl/sections/ppl-sec-law-5-6-the-cbv-marginals.html) · [Law 5.7](../../ppl/sections/ppl-sec-law-5-7-the-conditioning-law-and-the-equivalence.html).

The equational layer between the interpreter and the example
results: pointwise laws *about* `eD` that the rejection-sampling and
mass-identity proofs consume, plus the regression anchors that pin
the operational reading of the CBV interpreter. The anchors exist so
that a refactor of the §7/§9 cartesian machinery that silently
flipped the shared-sample semantics to an independent-product
semantics would break in a named lemma instead of compiling quietly.
The chapter closes with the marginal identities these laws were
built for, and with the conditioning law and the
rejection/conditioning equivalence of
`theories/programs/ex_reject_model.v`.

| Construction | Rocq |
|---|---|
| The sample-let collapse `⟦let x = sample µ in K⟧(γ) = ⟦K⟧(γ ⊗ µ)` | `eD_let_sample_collapse`, `em_pair_mor_const_E` — `theories/programs/infra/let_sample_law.v` |
| The let-at-sample Pettis integral law (arbitrary `γ`) | `eD_let_sample_int`, `ptensor_icone_integral`, `icone_integral_dirac_fmeas` — same file |
| Per-`U` evaluation of an `FMeas`-valued Pettis integral | `icone_integral_fmeas_E` — same file |
| The fused measure-on-`U` form at result type `tR` | `eD_let_sample_mu_E`, sanity `let_sample_var_E` — same file |
| The general let-law — arbitrary bound computation `M : tR`, setlike `γ`: `⟦let x = M in K⟧(γ) = ∫ ⟦K⟧(γ ⊗ δ_r) (⟦M⟧γ)(dr)` | `eD_let_collapse_setlike`, `eD_let_int`, `eD_let_mu_E` — same file |
| Affine Kleene cascade: closed form, geometric form, limit | `affine_iter_closed`, `affine_iter_geom`, `affine_iter_cvg`, `affine_iter_deg_eq0` — `theories/programs/infra/affine_cascade.v` |
| The sup-mass bridge for unit-ball ω-chains in `FMeas` | `fmeas_kleene_sup_U_cvg`, `fmeas_kleene_sup_U_E` — same file |
| The setlike-point kit (Eq-88 comonoid at sub-Dirac points) | `coalg_d_setlike`, `coalg_e_setlike`, `coalg_str_one1`, `coalg_str_tensor_setlike`, `em_pair_mor_constE` — `theories/programs/infra/cbv_anchors.v` |
| The comonoid diagonals are genuinely diagonal (boolean and `FMeas`) | `bool_coalg_d_E`, `coalg_d_FMeas_dirac` — same file |
| The shared-sample witnesses | `let_bernoulli_pair_diag`, `let_sample_pair_diag` — same file |
| The independence contrast | `pair_bernoulli_indep`, `pair_sample_indep` — same file |
| The β-rule at the morphism level | `eD_beta` — same file |
| The if-orientation pins | `eD_if_true`, `eD_if_false` — same file |
| The unnormalised score posterior, against `eD` | `ex_score_posterior_cbv_E`, `ex_score_posterior_cbv_mass` — `theories/programs/infra/cbv_marginals.v` |
| Rejection sampling normalises the score posterior | `ex_reject_normalises_score` — same file |
| The conditioning law — `⟦condition m a⟧(U) = ∫_U f dν_M` for an *arbitrary* model (the score posterior generalised from `sample µ`) | `condition_model_E`, `condition_model_mass`, readable `condition_E`, `condition_prog_evidence` — `theories/programs/ex_reject_model.v` |
| The equivalence — rejection sampling computes the conditioned model's normalised distribution: `Z · ⟦reject_prog⟧ U = ⟦condition_prog⟧ U` | `reject_normalises_condition`, `reject_prog_computes_condition`, `reject_normalises_condition_prob` — same file |
| The sampled-constant marginal at probability test points | `ex_random_constant_cbv_marginal`, `ex_random_constant_cbv_marginal_dirac`, `ex_random_constant_cbv_marginal_mass` — same file |
| The random-affine marginal at Dirac test points | `ex_random_linear_cbv_marginal`, `rl_inner_marginal` — same file |
| The Bayesian-linear-regression model evidence (general observation list) | `ex_bayes_linear_cbv_evidence`, `ex_bayes_linear_cbv_evidence2`, `obs_fold_at` — same file |
| Marginal kit: the `FMeas` counit on probabilities; projections at non-setlike points | `coalg_e_FMeas_prob`, `em_proj1_mor_unitE`, `em_proj1_mor_probE`, `Lfun_scaleE`, `one_dirac_ball`, `one_dirac_setlike` — same file |

### Law 5.1 — The let-at-sample integral law (`eD_let_sample_int`, `eD_let_int`)

> **Key result:** `⟦let x = sample µ in K⟧(γ) = ∫ ⟦K⟧(γ ⊗ δ_r) µ(dr)` — the Pettis integral law the marginal proofs consume.

The law ties the CBV interpretation of `let x = sample µ in K` to
the Pettis integral of `K`'s denotation over the Diracs of `µ`:
*⟦let x = sample µ in K⟧(γ) = ∫ ⟦K⟧(γ ⊗ δ_r) µ(dr)*, pointwise at
arbitrary `γ`. No unit-ball and no setlike hypothesis is needed
anywhere: every step is driven by a genuine `linhom_car` / `icones_hom`
field, all of which hold on the whole cone. The proof is a four-step
composition:

1. *Collapse.* `⟦let x = sample µ in K⟧(γ) = ⟦K⟧(γ ⊗ µ)` — the inner
   `em_pair_mor id (const µ)` erases the context copy through the
   comonoid counit law `emc_counitR` (`em_pair_mor_const_E`, stated for
   an arbitrary constant).
2. *Dirac approximation.* `µ = ∫ δ_r µ(dr)`, re-spelled with the bare
   `dirac_fmeas` integrand (`icone_integral_dirac_fmeas`, from
   `bilin.v`'s Thm 6.1 Dirac approximation).
3. *Tensor.* Tensoring with a fixed point preserves Pettis integrals,
   `γ ⊗ (∫ β dµ) = ∫ (γ ⊗ β r) µ(dr)` — the `linhom_pres_int` field of
   `τ(γ)` (`ptensor_icone_integral`).
4. *Push.* The `icones_hom_pres_int` field of `⟦K⟧` pushes the
   denotation under the integral.

```coq
(* theories/programs/infra/let_sample_law.v *)
(** Step 1, the collapse — arbitrary [γ], no unit-ball hypothesis. *)
Lemma eD_let_sample_collapse (γ : Gamo) :
  Lfun (eD_cbv' (ne_let x (ne_sample mu Hmu) K)) γ =
  Lfun (eD_cbv' K) (γ ⊗p mu).

(** THE LAW — step 4. *)
Lemma eD_let_sample_int (γ : Gamo) :
  linhom_fun (eD' (ne_let x (ne_sample mu Hmu) K)) γ =
  icone_integral (fun r => Lfun (eD_cbv' K) (γ ⊗p dirac_fmeas r))
    (let_sample_path γ) mu.
```

For headline consumption the law is fused with the per-`U`
evaluation of an `FMeas`-valued Pettis integral
(`icone_integral_fmeas_E`, the generalisation of
`FMeas_fmap_setT_E` from `setT` to an arbitrary measurable `U`, read
off the Pettis equation against the test `fmeas_eU U`): when the let
body has type `tR` the denotation is a measure, and its mass on `U`
is an ordinary Lebesgue integral — the exact shape of the
rejection-sampling mass recurrence.

```coq
(* theories/programs/infra/let_sample_law.v *)
Lemma eD_let_sample_mu_E (γ : Gamo) (U : set (ar_carrier Ar R_obj))
    (mU : measurable U) :
  fmeas_mu (linhom_fun (eD' (ne_let x (ne_sample mu Hmu) K)) γ) U =
  \int[fmeas_mu mu]_(r in [set: ar_carrier Ar R_obj])
     (fine (fmeas_mu (Lfun (eD_cbv' K) (γ ⊗p dirac_fmeas r)) U))%:E.

(** Sanity DoD — [⟦let x = sample µ in x⟧(1) = µ]. *)
Lemma let_sample_var_E : linhom_fun (eD' ex_let_sample_var) one1 = mu.
```

**The general let-law.** The sample case is the special case
`M = sample µ` of the general CBV sequencing law for an *arbitrary*
bound computation `M : tR`:
*⟦let x = M in K⟧(γ) = ∫ ⟦K⟧(γ ⊗ δ_r) (⟦M⟧γ)(dr)* — the bound
sub-distribution `⟦M⟧γ` replaces the constant prior.
Unlike the sample case, the step-1 collapse now genuinely consumes
the comonoid copy of the context (`em_pair_mor id ⟦M⟧` feeds `γ` to
*both* legs), so the law holds at setlike unit-ball context points
(`eD_let_collapse_setlike`) — which is harmless: in every consumer
the let sits under binders whose environments are setlike by
construction. Steps 2–4 are reused verbatim — none of them mention
the bound measure. The fused measure-on-`U` form `eD_let_mu_E` is the
exact shape the rejection-sampling *combinator* mass recurrence
consumes (`theories/programs/ex_reject_model.v`, with `M = m @ a` the
model applied to the input).

```coq
(* theories/programs/infra/let_sample_law.v *)
Lemma eD_let_int (γ : Gamo) :
  cone_norm γ <= 1 ->
  Lfun (coalg_str (ctxD_cbv (drop_names G))) γ = prom γ ->
  linhom_fun (eD' (ne_let x M K)) γ =
  icone_integral (fun r => Lfun (eD_cbv' K) (γ ⊗p dirac_fmeas r))
    (let_sample_path R_carrier_meas R_to_carrier_meas K γ)
    (Lfun (eD_cbv' M) γ).
```

### Law 5.2 — The affine cascade and the sup-mass bridge (`affine_iter_closed`, `fmeas_kleene_sup_U_E`)

The scalar core of every CBV mass headline. Given reals
`a, q ≥ 0` and a real sequence with `x 0 = 0` and
`x (n+1) = a + q · x n` — the per-iterate mass of an affine Kleene
chain — the closed form is the partial geometric series, with the
geometric form away from `q = 1` and the limit `a / (1 − q)` when
`q < 1`.

```coq
(* theories/programs/infra/affine_cascade.v *)
(** Closed form: [x n = a * (1 + q + ... + q^(n-1))]. *)
Lemma affine_iter_closed (n : nat) :
  x n = (a * (\sum_(i < n) q ^+ i))%R.

(** Geometric form away from [q = 1]. *)
Lemma affine_iter_geom (n : nat) :
  q != 1%R -> x n = (a * (1 - q ^+ n) / (1 - q))%R.

(** Extended-real limit when [0 <= q < 1]. *)
Lemma affine_iter_cvg :
  (q < 1)%R ->
  (x n)%:E @[n --> \oo] --> ((a / (1 - q))%R%:E : \bar R).
```

The sup-mass bridge then converts a *limit of per-iterate masses*
into the *mass of the Kleene supremum*: for a unit-ball ω-chain
`ν : nat → fmeas R X` and a measurable `U`, the masses
`fmeas_mu (ν n) U` converge to the mass of `cone_sup_ball ν` at `U`
(definitionally `fmeas_sup_ball`, the HB `isCone` instance of
`fmeas.v`), so any limit *is* that mass by Hausdorff uniqueness.

```coq
(* theories/programs/infra/affine_cascade.v (Section FMeasKleeneSup) *)
Lemma fmeas_kleene_sup_U_E (U : set X) (l : \bar R) :
  measurable U ->
  fmeas_mu (nu n) U @[n --> \oo] --> l ->
  fmeas_mu (cone_sup_ball nu nuch nub1 : fmeas R X) U = l.
```

Together with the interleaved-chain laws of the fixpoint chapter,
this is the complete recipe behind every CBV mass identity: reduce
the denotation to a `cone_sup_ball` of per-iterate measures, derive
the affine mass recurrence per iterate (via the let-at-sample law or
the boolean dispatch), close the recurrence with
`affine_iter_closed` / `affine_iter_cvg`, and land with
`fmeas_kleene_sup_U_E`.

### Def 5.3 — The setlike-point kit (`coalg_d_setlike`, `coalg_str_tensor_setlike`)

A point `x` of a coalgebra `(P, str)` is *setlike* when
`str x = x!` — the §9.7 reading "`x` is a (sub-)Dirac". On setlike
unit-ball points the Eq-88 comonoid computes: the diagonal is the
pure tensor square and the counit is the unit point. The setlike
points are closed under the `EM_prod` tensor, and the unit point
`one1`, every Dirac of `FMeas X`, and both boolean Diracs are
setlike — which is what lets every program-level computation below
proceed by evaluating morphism composites at concrete environment
points.

```coq
(* theories/programs/infra/cbv_anchors.v (Section AnchorKit) *)
(** [coalg_d P x = x ⊗ x] when [x] is setlike of norm [≤ 1]. *)
Lemma coalg_d_setlike (P : Coalgebra Ar) (x : coalg_obj P) :
  cone_norm x <= 1 -> Lfun (coalg_str P) x = x! ->
  Lfun (coalg_d P) x = x ⊗p x.

(** Setlike points are closed under the [EM_prod] tensor. *)
Lemma coalg_str_tensor_setlike (P Q : Coalgebra Ar)
    (x : coalg_obj P) (y : coalg_obj Q) :
  cone_norm x <= 1 -> cone_norm y <= 1 ->
  Lfun (coalg_str P) x = x! -> Lfun (coalg_str Q) y = y! ->
  Lfun (coalg_str (EM_prod P Q)) (x ⊗p y) = (x ⊗p y)!.

(** THE workhorse: pairing the identity with a CONSTANT computes at
    EVERY point — no setlike hypothesis on [γ]. *)
Lemma em_pair_mor_constE (Z Q : Coalgebra Ar) (c : coalg_obj Q)
    (Hc : cone_norm c <= 1) (g : coalg_obj Z) :
  Lfun (em_pair_mor (icones_id Ar (coalg_obj Z)) (const_icones Z c Hc)) g =
  g ⊗p c.
```

The kit also pins the comonoid diagonals themselves: the §9.7
boolean coalgebra's diagonal is the convex combination of the
*diagonal* basis tensors (`bool_coalg_d_E` — the independent-product
reading would produce cross terms instead), and the `FMeas` diagonal
sends a Dirac to its diagonal tensor (`coalg_d_FMeas_dirac`): the
§9.7 coalgebra duplicates a *sample*, not the measure.

```coq
(* theories/programs/infra/cbv_anchors.v *)
(** The full boolean diagonal:
    [d(x) = bc_t x · (δ_T ⊗ δ_T) + bc_f x · (δ_F ⊗ δ_F)]. *)
Lemma bool_coalg_d_E (x : bool_cone_car Ar) :
  Lfun (coalg_d (@bool_cone_coalg R Ar)) x =
  bool_case x (bool_dirac_true ⊗p bool_dirac_true)
              (bool_dirac_false ⊗p bool_dirac_false).

Lemma coalg_d_FMeas_dirac (X : ar_obj Ar) (r : ar_carrier Ar X) :
  Lfun (coalg_d (FMeas_coalgebra X)) (dirac_fmeas r) =
  dirac_fmeas r ⊗p dirac_fmeas r.
```

### Law 5.4 — The sharing-semantics anchors (`let_bernoulli_pair_diag`, `pair_bernoulli_indep`)

The load-bearing program-level pin: `let x = Bernoulli(p) in (x, x)`
denotes the *diagonal* pushforward
`p · (δ_T ⊗ δ_T) + (1−p) · (δ_F ⊗ δ_F)` — a shared sample, not the
independent square. The contrast anchors pin the same semantics from
the other side: two *separate* samples,
`(Bernoulli(p), Bernoulli(p))` and `(sample µ, sample µ)`, denote
the independent products `bern ⊗ bern` and `µ ⊗ µ`. Together the two
pairs make the sharing semantics of the CBV `let` a regression
property rather than a folklore expectation.

```coq
(* theories/programs/infra/cbv_anchors.v (Section ProgramAnchors) *)
(** [let x := Bernoulli(p) in (x, x)] — the DIAGONAL pushforward. *)
Lemma let_bernoulli_pair_diag (p : R) (Hp0 : 0 <= p) (Hp1 : p <= 1) :
  linhom_fun (eD' (anchor_let_bern Hp0 Hp1)) one1 =
  bool_case (bernoulli (Ar:=Ar) p Hp0 Hp1)
    (bool_dirac_true ⊗p bool_dirac_true)
    (bool_dirac_false ⊗p bool_dirac_false).

(** [let x := sample δ_{r₀} in (x, x)] — the Dirac twin. *)
Lemma let_sample_pair_diag (r0 : ar_carrier Ar R_obj) :
  linhom_fun (eD' (anchor_let_sample_dirac r0)) one1 =
  dirac_fmeas r0 ⊗p dirac_fmeas r0.

(** The CONTRAST: two separate samples are independent. *)
Lemma pair_sample_indep (mu : fmeas R (ar_carrier Ar R_obj))
    (Hmu : cone_norm mu <= 1) :
  linhom_fun
    (eD' (ne_pair (ne_sample (G := nil) mu Hmu)
                  (ne_sample (G := nil) mu Hmu))) one1 =
  mu ⊗p mu.
```

(For a general prior `µ`, the shared-`let` pair is the Pettis
integral `∫ (δ_r ⊗ δ_r) dµ(r)` by the let-at-sample law above; the
Dirac special case is the anchor.) All anchors are stated against
the public interpreter `eD` through the definitional clause pins of
`ppl_cbv.v` — never re-derived.

### Law 5.5 — The β-rule and the if-pins (`eD_beta`, `eD_if_true`, `eD_if_false`)

Two more morphism-level anchors. The β-rule
`(λx.M) V = let x := V in M` holds as an equality of `icones_hom`s:
the `!̃` round trip `der ∘ !(curry M) ∘ str` collapses by `adj_phiK`
(the adjunction triangle), and the curry/uncurry round trip by
`tensor_uncurry_natL` + `tensor_curryK`. The if-pins orient the
boolean dispatch — a braid slipped into `if_under` would flip the
branches and break exactly here.

```coq
(* theories/programs/infra/cbv_anchors.v (Section ProgramAnchors) *)
(** The β-rule at the [icones_hom] level. *)
Lemma eD_beta (G : named_ctx Ar) (x : string) (t1 t2 : ppl_type Ar)
    (M : @named_expr R Ar R_obj ((x, t1) :: G) t2)
    (V : @named_expr R Ar R_obj G t1) :
  eD_cbv' (ne_app (ne_lam x M) V) = eD_cbv' (ne_let x V M).

Lemma eD_if_true (G : named_ctx Ar) (t : ppl_type Ar)
    (M N : @named_expr R Ar R_obj G t) :
  eD_cbv' (ne_if t ne_true M N) = eD_cbv' M.

Lemma eD_if_false (G : named_ctx Ar) (t : ppl_type Ar)
    (M N : @named_expr R Ar R_obj G t) :
  eD_cbv' (ne_if t ne_false M N) = eD_cbv' N.
```

### Law 5.6 — The CBV marginals (`ex_score_posterior_cbv_E`, `ex_bayes_linear_cbv_evidence`)

The headline semantic identities of the non-recursive basic
sampling/scoring examples of `theories/programs/examples.v`, proved
against the CBV interpreter `eD` in
`theories/programs/infra/cbv_marginals.v` — the consumers this
chapter's machinery was built for. The common route: the
let-at-sample law turns each `let x = sample µ in …` prefix into a
Pettis integral over Diracs of the prior; dereliction / evaluation at
setlike test points pushes inside the integral
(`icones_hom_pres_int` / `linhom_int_eval`); and the integrand
computes pointwise through the setlike-point kit, closing with a
Dirac integral (`icone_integral_dirac_fmeas` or
`icone_integral_fmeas_E`).

**The unnormalised posterior.** The denotation of
`ex_score_posterior` (`let m = sample µ in let _ = score f m in m`)
at the unit context point is, on every measurable `U`, the prior
reweighted by the evidence density — *not* normalised; the mass
corollary `ex_score_posterior_cbv_mass` gives the total evidence
`∫ f dµ`.

```coq
(* theories/programs/infra/cbv_marginals.v (Section ScorePosterior) *)
Theorem ex_score_posterior_cbv_E (U : set (ar_carrier Ar R_obj))
    (mU : measurable U) :
  fmeas_mu
    (linhom_fun (ex_score_posterior_cbv R_carrier_meas R_to_carrier_meas
                   pm Hf_meas) one1) U =
  \int[fmeas_mu mu]_(r in U) (f (cR r))%:E.
```

**The normalisation pairing.** Combining the posterior identity with
the rejection-sampling master identity of
`theories/programs/ex_reject_headline.v`: at a probability prior
(`µ(setT) = 1`), the rejection-sampling denotation times the total
evidence *is* the score denotation — `score` produces the
unnormalised posterior, rejection sampling produces the normalised
one, and the theorem connects the two programs exactly.

```coq
(* theories/programs/infra/cbv_marginals.v (Section ScorePosterior) *)
Theorem ex_reject_normalises_score
    (Hmu1 : fmeas_mu mu [set: ar_carrier Ar R_obj] = 1)
    (U : set (ar_carrier Ar R_obj)) (mU : measurable U) :
  (\int[fmeas_mu mu]_(r in [set: ar_carrier Ar R_obj]) (f (cR r))%:E) *
  fmeas_mu
    (linhom_fun (ex_reject_cbv R_carrier_meas R_to_carrier_meas
                   pm Hf_meas) one1) U =
  fmeas_mu
    (linhom_fun (ex_score_posterior_cbv R_carrier_meas R_to_carrier_meas
                   pm Hf_meas) one1) U.
```

**The sampled-constant marginal, and the probability-test-point
subtlety.** The denotation of `ex_random_constant`
(`let c = sample µ in λx. c`) is a promoted function value;
derelicting it and evaluating at a test point `x` recovers the prior
`µ` — *provided `x` is a probability* (`fmeas_mu x setT = 1`). The
hypothesis is honest, not an artifact: the closure discards its
argument, and discarding in `EM(!)` is the comonoid counit, which on
`FMeas` weighs the kept output by the argument's *total mass*
(`coalg_e_FMeas_prob` / `em_proj1_mor_probE`) — so at `x = 0` the
marginal is `0`, not `µ`, and only mass-1 test points are silently
discarded. Dirac test points are probabilities, giving the corollary
`ex_random_constant_cbv_marginal_dirac`; the per-`U` reading is
`ex_random_constant_cbv_marginal_mass`.

```coq
(* theories/programs/infra/cbv_marginals.v (Section RandomConstantMarginal) *)
Theorem ex_random_constant_cbv_marginal (x : FMeas R_obj) :
  fmeas_mu x [set: ar_carrier Ar R_obj] = 1%E ->
  linhom_fun
    (Lfun (der (Lty tR' tR'))
       (linhom_fun (ex_random_constant_cbv R_carrier_meas
                      R_to_carrier_meas pm) one1)) x = mu.
```

**The random-affine marginal.** The denotation of `ex_random_linear`
(`let m = sample µ in let b = sample µ in λx. m·x + b`), derelicted
and evaluated at a Dirac test point `δ_{r0}`, is on every measurable
`U` the iterated-integral measure `∫∫ δ_{m·r0+b}(U) µ(db) µ(dm)` —
the joint pushforward of two independent prior draws along
`(m, b) ↦ m·r0 + b`. The inner one-sample layer is
`rl_inner_marginal`; the arithmetic computes on Diracs through the
`add_lift` / `mul_lift` Dirac rules.

```coq
(* theories/programs/infra/cbv_marginals.v (Section RandomLinearMarginal) *)
Theorem ex_random_linear_cbv_marginal (r0 : ar_carrier Ar R_obj)
    (U : set (ar_carrier Ar R_obj)) (mU : measurable U) :
  fmeas_mu
    (linhom_fun
       (Lfun (der (Lty tR' tR'))
          (linhom_fun (ex_random_linear_cbv R_carrier_meas
                         R_to_carrier_meas pm) one1))
       (dirac_fmeas r0)) U =
  \int[fmeas_mu mu]_(m in [set: ar_carrier Ar R_obj])
    (fine (\int[fmeas_mu mu]_(b in [set: ar_carrier Ar R_obj])
       (fine (fmeas_mu
          (dirac_fmeas (R_to_carrier R_carrier_eq (cR m * cR r0 + cR b)))
          U))%:E))%:E.
```

**The Bayesian-linear-regression model evidence.** The headline of
the file: `ex_bayes_linear l` samples the random affine model *once*
(it is literally `ex_random_linear`), binds it to `"f"`, conditions
it on each element of the meta-level list `l : seq (obs R)` in turn
(`iter_condition`: each observation `o` scores the model's value at
the known input `obs_x o` by the density `obs_d o`), and returns
`#"f"` — the posterior over functions. The theorem, for a *general* `l`: the
comonoid counit ("total mass") of the function-space denotation is
the **model evidence**.

```coq
(* theories/programs/infra/cbv_marginals.v (Section BayesLinearEvidence) *)
Theorem ex_bayes_linear_cbv_evidence (l : seq (obs R)) :
  ((c1_val (Lfun (coalg_e (tyD_cbv tF))
      (linhom_fun
         (ex_bayes_linear_cbv R_carrier_meas R_to_carrier_meas pm l)
         one1)))%:num)%R =
  fine (\int[fmeas_mu mu]_(m in [set: ar_carrier Ar R_obj])
     (fine (\int[fmeas_mu mu]_(b in [set: ar_carrier Ar R_obj])
        ((\prod_(o <- l) obs_d o (cR m * obs_x o + cR b))%R)%:E))%:E).
```

The 2-observation corollary `ex_bayes_linear_cbv_evidence2` writes
the product literally. The CBV content: the let-bound *function
value* is shared — duplicated by the comonoid `coalg_d` at a
prom-point of the function cone — across all observations and the
return, so every score weighs the *same* sampled function; the
workhorse `obs_fold_at` factors the per-observation scalar weights
out of the fold one at a time, and two let-at-sample integrations
close the evidence.

The supporting kit of the file (its §1) extends the setlike-point kit
to *non-setlike* discarded components: the comonoid counit of the
§9.7 coalgebra `FMeas X` sends every probability measure to `one1`
(`coalg_e_FMeas_prob` — Diracs are setlike, and the Dirac-to-integral
lift plus the Pettis equation on `cone_one` reads off the total
mass), so the first cartesian projection silently discards an
`FMeas`-typed probability (`em_proj1_mor_probE`) and weighs by the
scalar when discarding a `tunit`-typed score result
(`em_proj1_mor_unitE` — how the score weight becomes a
`precone_scale` factor in the score-posterior proof). The
per-program proofs are worked example-by-example in
the [Examples tab](../../examples/index.html).

### Law 5.7 — The conditioning law and the equivalence (`condition_model_E`, `reject_normalises_condition`)

The conditioning combinator promoted to an operator: `condition f m`
takes a **program predicate** `f : b → tbool` and a model `m : a → b`,
and returns the conditioned model
`λa. let x = m a in let _ = assert (f x) in x`, where a failed `assert`
zeroes the trace. Writing `s_r := ⟦f x⟧` for the acceptance
distribution at a returned value `r` and `t(r) := (bc_t s_r)%:num` for
its acceptance probability, the conditioning law (Section
RejectModelCompat of `theories/programs/ex_reject_model.v`) states that at
a unit-ball model value `g!` and a setlike unit-ball input `a₀`,
writing `ν_M := g(a₀)` for the model's output sub-distribution, the
conditioned model's output is the model's output reweighted by `t`. The
proof engine is this chapter's general let-law `eD_let_int_obj` at
`ν_M`, with the assert clause computing on Diracs to
`bool_case s_r (δ_r) 0` and the returned variable projected through
`em_proj1_mor_unitE` / `Lfun_scaleE`.

```coq
(* theories/programs/ex_reject_model.v (Section RejectModelCompat) *)
Theorem condition_model_E (U : set (ar_carrier Ar B))
    (mU : measurable U) :
  fmeas_mu (cond_model_denot R_to_carrier_meas fpred g a0) U =
  \int[fmeas_mu (reject_model_dist g a0)]_(r in U) ((bc_t (sdist r))%:num)%:E.
```

In the readable `⟦·⟧` brackets (Section ReadableHeadlines, over an
arbitrary thunked model `model_prog := λ_. Mbody` with
`model_run := model_prog ()` and
`condition_prog := condition pred_prog model_prog ()`), the law is
`condition_E`, and combining it with the rejection master identity
`reject_prog_master` gives the equivalence — rejection sampling
computes the conditioned model's normalised distribution:

```coq
(* theories/programs/ex_reject_model.v (Section ReadableHeadlines) *)
Theorem condition_E U (mU : measurable U) :
  ⟦ condition_prog ⟧ U = \int[⟦ model_run ⟧]_(x in U) ((bc_t (sdist x))%:num)%:E.

Theorem reject_normalises_condition U (mU : measurable U) :
  ((1 - fine (⟦ model_run ⟧ [set: ar_carrier Ar R_obj])
      + fine (\int[⟦ model_run ⟧]_(x in [set: ar_carrier Ar R_obj])
                ((bc_t (sdist x))%:num)%:E))%R)%:E
    * ⟦ reject_prog ⟧ U
  = ⟦ condition_prog ⟧ U.
```

The division form `reject_prog_computes_condition` divides through at
`0 < Z`, and the probability-model form
`reject_normalises_condition_prob` identifies the normaliser with the
model evidence `⟦condition_prog⟧(setT)`. The historical special case
at the sampler model is `ex_reject_normalises_score` above; the
regression side — `ex_bayes_linear` is *defined* as iterated
conditioning (`condition_at` / `iter_condition`, with the named
anchor `ex_bayes_linear_is_iter_condition` now definitional,
`theories/programs/examples.v`) — and the full narrative live on the
[Examples tab](../../examples/index.html).

---

## The boolean cascade

**In this chapter:** [Def 6.1](../../ppl/sections/ppl-sec-def-6-1-the-2-point-cone.html) · [Def 6.2](../../ppl/sections/ppl-sec-def-6-2-the-universal-co-pairing.html) · [Def 6.3](../../ppl/sections/ppl-sec-def-6-3-icones-hom-packaging.html) · [Def 6.4](../../ppl/sections/ppl-sec-def-6-4-the-sec-9-7-coalgebra-on-the-2-point-cone.html).

The 2-point cone of [paper §4.4 / Theorem
4.24](../../paper/sections/sec-4.html) — the coproduct `1 ⊕ 1` — is
built concretely as `bool_cone_car Ar : {nonneg R} × {nonneg R}`
with norm `‖(p, q)‖ = p + q`. The chapter assembles its full HB
tower, the universal co-pairing `bool_case` with its linhom and
icones packagings, and a hand-rolled §9.7-style `!`-coalgebra
structure that gives `tbool` the shared-sample semantics.

| Construction | Rocq |
|---|---|
| The 2-point ICone with full HB tower | `bool_cone_car`, `bool_dirac_true`, `bool_dirac_false` — `theories/programs/infra/bool_cone.v` |
| The universal co-pairing | `bool_case`, `bool_case_true`, `bool_case_false`, `bool_case_linear`, `bool_case_omega_continuous`, `bool_case_norm_le1`, `bool_case_pres_path`, `bool_case_pres_int` — same file |
| Unit-ball-free variants | `bool_case_omega_continuous_gen`, `bool_case_norm_le_max`, `bool_case_pres_path_gen`, `bool_case_pres_int_gen` — same file |
| Test measurability, generalised | `test_meas_gen` — `theories/mcones/mcone.v` |
| Icones-hom packaging | `bool_case_linhom`, `bool_case_linhom_gen`, `bool_case_icones_hom` — `theories/programs/infra/bool_case_hom.v` |
| α / β decomposition | `alpha_linhom`, `beta_linhom`, `bool_case_linhom_gen_alpha_beta` — same file |
| The §9.7 coalgebra on `bool_cone_car` | `bool_coalg_str`, `bool_cone_coalg`, `bool_cone_dispatch` — `theories/programs/infra/bool_cone_coalg.v` |
| CBV `if_icones` consumer (from the interpreter) | `if_icones`, `if_under` — `theories/programs/ppl_cbv.v` |

### Def 6.1 — The 2-point cone (`bool_cone_car`)

> **Prerequisite:** the 2-point cone realises the [paper §4.4 / Thm 4.24](../../paper/sections/sec-4.html) coproduct `1 ⊕ 1`.

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

### Def 6.2 — The universal co-pairing (`bool_case`)

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

### Def 6.3 — Icones-hom packaging (`bool_case_linhom`, `alpha_linhom`, `beta_linhom`)

The co-pairing is packaged once at each categorical level in
`theories/programs/infra/bool_case_hom.v`: as a linhom
`bool_case_linhom : bool_cone ⊸ A` (with the unit-ball-free
`bool_case_linhom_gen`) and as an icones_hom
`bool_case_icones_hom`.

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
level](../../ppl/sections/ppl-sec-def-2-7-if-then-else-at-the-icones-level.html).

### Def 6.4 — The §9.7 coalgebra on the 2-point cone (`bool_coalg_str`, `bool_cone_coalg`)

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

## What is **not** formalised

A handful of PPL-side items are intentionally left open. (The
call-by-name interpretation, its headlines and its refinement options
are not gaps of this document: they live on the `cbn-track` branch.
The former gap "`ne_fix_mr` at product body types" is **closed**: the
Seely transport of `fix_comb` is delivered in
`theories/programs/infra/em_fix_mr.v` and wired through
`fix_mr_comb` / `fix_mr_clause` of `theories/programs/ppl_cbv.v`,
with the computation law `eD_fix_mr_prod_at_setlike` and the surface
witness `ex_even_odd_pair`.)

The recursion equation `fix F = F (fix F)` is proven where it carries
semantic content, at two levels. At the value level,
`fix_value_unfold` (`theories/programs/infra/em_fix_value.v`) states
`der(F(prom(fix_value F))) = fix_value F` as a *morphism-free*
identity — the fixpoint value satisfies its defining equation
unconditionally. At the interpreter level, `eD_fix_unfold`
(`theories/programs/infra/cbv_fix_unfold.v`) discharges the same
equation at every setlike unit-ball context point — which is every
point a program evaluation reaches: a closed term denotes
`linhom_fun (eD M) one1` with `one1` setlike (`coalg_str_one1`), and
every binding, `let` and `λ` computes through setlike environments.
The unfolding as a *morphism* equation at the remaining,
*non-setlike* context points is intentionally out of scope: such
points never arise from program execution, no result in this
development consumes the morphism-level form, and `adj_psi` reduces
through `coalg_str` only on the promoted-point (setlike) shape. The
categorical statement would buy uniform-fixpoint-operator
cleanliness, not any program-level fact.

| Item | What it is | Why not yet |
|---|---|---|
| External semantic equivalence | A correspondence with another formalised semantics or a real PPL implementation (ProbProg / Pyro / Stan). | The correctness statements in this development are denotational identities at the categorical level. |

---

## How to verify

```sh
make -j

echo "Print Assumptions Skern_to_ICones_fully_faithful." | \
  rocq top -Q theories Icones -l theories/kernels/kernel_embedding.v
echo "Print Assumptions eD."                      | \
  rocq top -Q theories Icones -l theories/programs/ppl_cbv.v
echo "Print Assumptions if_icones."               | \
  rocq top -Q theories Icones -l theories/programs/ppl_cbv.v
echo "Print Assumptions Phi_fun_lfp_eq0."         | \
  rocq top -Q theories Icones -l theories/programs/infra/em_fix_value.v
echo "Print Assumptions fix_prom_E."              | \
  rocq top -Q theories Icones -l theories/programs/infra/em_fix_value.v
echo "Print Assumptions eD_fix_unfold."           | \
  rocq top -Q theories Icones -l theories/programs/infra/cbv_fix_unfold.v
echo "Print Assumptions eD_let_sample_int."       | \
  rocq top -Q theories Icones -l theories/programs/infra/let_sample_law.v
echo "Print Assumptions let_bernoulli_pair_diag." | \
  rocq top -Q theories Icones -l theories/programs/infra/cbv_anchors.v
echo "Print Assumptions meas_stable_diag_bilinear_tensor." | \
  rocq top -Q theories Icones -l theories/stable/diag_bilinear_tensor.v
echo "Print Assumptions ex_score_posterior_cbv_E." | \
  rocq top -Q theories Icones -l theories/programs/infra/cbv_marginals.v
echo "Print Assumptions ex_reject_normalises_score." | \
  rocq top -Q theories Icones -l theories/programs/infra/cbv_marginals.v
echo "Print Assumptions ex_random_constant_cbv_marginal." | \
  rocq top -Q theories Icones -l theories/programs/infra/cbv_marginals.v
echo "Print Assumptions ex_random_linear_cbv_marginal." | \
  rocq top -Q theories Icones -l theories/programs/infra/cbv_marginals.v
echo "Print Assumptions ex_bayes_linear_cbv_evidence." | \
  rocq top -Q theories Icones -l theories/programs/infra/cbv_marginals.v
echo "Print Assumptions fix_comb_iso_prom_E." | \
  rocq top -Q theories Icones -l theories/programs/infra/em_fix_mr.v
echo "Print Assumptions eD_gaussian_sample_agree." | \
  rocq top -Q theories Icones -l theories/programs/infra/kernel_anchors.v
echo "Print Assumptions ex_gaussian_walk_mass." | \
  rocq top -Q theories Icones -l theories/programs/infra/kernel_anchors.v
```

Each command reports only `propositional_extensionality`,
`functional_extensionality_dep` and
`constructive_indefinite_description` (the classical-logic axioms of
`mathcomp-analysis`). Per-entry pages embed the precise identifier
name, file, and a GitHub link to the Rocq source.

For the example programs and their mass / marginal / PMF identities,
see the [Examples tab](../examples/).
