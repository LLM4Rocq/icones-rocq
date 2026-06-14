# A direct-style PPL on top of the integrable-cones model

A typed probabilistic functional language sits on top of the paper's
categorical model. Each type denotes a `!`-coalgebra, each program a
*linear* morphism in `ICone` between the underlying carriers of the
context and result coalgebras, and recursion at function type is
realised by a value-fixpoint *combinator* in the Eilenberg–Moore
category of `!` — the supremum of an interleaved Kleene chain seeded
at the diverging function value, computed pointwise through a
`der`/`prom` sandwich. The language is direct-style
(Plotkin / Girard), named-variable (Saito–Affeldt APLAS 2023), and
probabilistic effects live entirely in the interpretation — there is
no `tprob` type marker, no syntactic `return`, no `bind`. Examples
are listed in the [Examples tab](../examples/). A call-by-name
interpretation of the same surface syntax (through the cartesian
closed `SCones` of paper §7) is preserved on the `cbn-track` branch;
main is CBV-only.

The paper-side correspondence (§§ 2–9 ↔ Rocq) lives on the
[Paper tab](../paper/). This document covers what sits *above* the
paper: the surface language, its CBV interpretation, the fixpoint
and integral-law infrastructure, and the semantic correctness
statements one can make at the categorical level.

---

## The surface language

The source language is a simply-typed lambda calculus with sampling,
scoring, recursion at function type, a two-point boolean type, and
mutual recursion at any free-coalgebra type. The syntax is a single
intrinsically-typed inductive `named_expr Γ τ` in named-variable
style, indexed by a *named* context `named_ctx = seq (string ×
ppl_type)`, and is consumed by the CBV interpretation `eD` of the
next chapter. This chapter walks through the constructor groups of
the inductive, the canonical-structure machinery behind variable
lookup, and the two notation layers: the kernel `ppl_named` grammar
and the derived readable forms on top of it.

| Construction | Rocq |
|---|---|
| Types `tunit`, `tbase X`, `tprod`, `tfun`, `tbool` | `ppl_type` — `theories/programs/ppl.v` |
| Named contexts | `named_ctx`, `drop_names` — same file |
| Named variables (witness) | `named_var`, `nv_head`, `nv_tail` — same file |
| Term constructors | `named_expr` (the 23 constructors below) — same file |
| Free-coalgebra type predicate (gating `ne_fix_mr`) | `is_free_coalg_type` — same file |
| Measurable function application (pushforward) | `ne_meas`, `meas_lift`, `meas_lift_dirac`, `meas_lift_mass` — same file |
| Runtime-parameter distributions `Gaussian(e1,e2)` / `Uniform(e1,e2)` | `ne_gaussian`, `ne_uniform` — same file; `pkernel`, `kernel_lift`, `kernel_lift2`, `gaussian_kernel`, `uniform_kernel` — `theories/programs/distributions.v` |
| Variable lookup via canonical structures | `tagged_nctx`, `find_nv`, `found_nv`, `recurse_nv`, `ne_var'` — same file |
| Surface notation `[ … ]` and the `ppl_named` custom entry | `ppl_named` (custom entry) — same file |
| Bundled densities and surface forms (`Bernoulli p`, `Bernoulli d e`, `Score d e`, `observe`, `Meas`, `sample`, `>`, `let rec`) | `udensity`, `prob`, `mk_udensity`, `mk_prob`, `gauss_udensity`, `gt0_udensity`, `gauss_obs_density`, `negr`, `pmeas`, `prob_pmeas` — same file; `prob_half`, `gaussian`, `uniform`, `ex_surface_demo`, `ex_surface_walk` — `theories/programs/examples.v` |

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

### Effectful term constructors (`ne_sample`, `ne_score`, `ne_bernoulli`, `ne_bernoulli_f`, `ne_if`)

The effectful constructors are direct-style — the probability monad
lives in the interpretation `eD`, not in the source types — and they
divide by what they produce. `ne_sample` is one real draw from a
fixed sub-probability measure (`→ tR'`). `ne_bernoulli` /
`ne_bernoulli_f` are the **boolean coin** (`→ tbool`), the sole
source of boolean randomness, consumed by `ne_if` for probabilistic
branching. `ne_score` is soft conditioning (`→ tunit`). The
real-valued *named* and *runtime-parameter* distributions
(`gaussian` / `uniform`, and `Gaussian` / `Uniform`) are not
primitives: they are built on `ne_sample` and the probability-kernel
layer (the [Runtime-parameter distributions](#) section below). So
the only randomness baked into the syntax is one fixed-measure
sample, one boolean coin, and one score; everything else is derived.

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

`ne_score` carries a density `f : R → R` valued in `[0,1]`; the
bound is the unit-ball discipline of `linhom_icones` (see [Scores,
densities, and the sub-probability
boundary](../../ppl/sections/ppl-sec-scores-densities-and-the-sub-probability-boundary.html)
for what it rules out — genuinely unbounded densities — and how a
bounded density is conditioned via its intrinsic peak). The boolean
coin shares that discipline: `ne_bernoulli p` is the constant coin
`(p, 1 − p)`, and `ne_bernoulli_f f e` is value-dependent — the coin
`(f r, 1 − f r)` at the value `r` of the `tR'`-valued
sub-expression `e` — its CBV engine the path lift `bern_lift` (the
boolean twin of `score_lift`; see [the value-dependent Bernoulli
section](../../ppl/sections/ppl-sec-the-value-dependent-bernoulli-lift.html)).
The `[0,1]` witnesses are never written loose at the surface: the
readable layer carries them in two bundled records. The constant coin
`Bernoulli p` takes a bundled scalar `p : prob` (the pair of bounds
travels with the value); the value-dependent coin `Bernoulli d e` and
the score `Score d e` take a bundled `[0,1]` density `d : udensity`
(measurability and both bounds), with the comparison coin `e1 > e2`
desugaring to `ne_bernoulli_f` at the indicator bundle
`gt0_udensity`. The bundles are built with the smart constructors
`mk_udensity` and `mk_prob`. The Bayesian-conditioning operator
`observe Gaussian { s , y } e` is the same `ne_score` at the bundled
Gaussian observation likelihood `gauss_udensity` (denotation
`observe_gauss_E`). See [Bundled
densities and the `observe`
operator](../../ppl/sections/ppl-sec-bundled-densities-and-the-observe-operator.html)
for the records and smart constructors. The same value-dependent coin
is the accept/reject test of `examples.v::ex_reject`.

### Measurable function application (`ne_meas`, `meas_lift`, `meas_lift_dirac`, `meas_lift_mass`)

`ne_meas f Hf e` pushes the value of the `tR'`-valued sub-expression
`e` through a measurable meta-level function `f : R → R` — surface
form `Meas { f , Hf } e`. Unlike `ne_score` / `ne_bernoulli_f`, no
`[0,1]` bounds are needed: the semantics is the `FMeas` functorial
action (pushforward), whose operator norm is already `≤ 1`.

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
Dirac-path pushforward at the carrier transport
`f̂ = R_to_carrier ∘ f ∘ carrier_to_R`), with the two load-bearing
laws `meas_lift_dirac` (`Meas f` on a point mass is application:
`δ_r ↦ δ_{f r}`) and `meas_lift_mass` (the pushforward preserves
total mass). The CBV clause is `eD_meas_E`
(`theories/programs/ppl_cbv.v`): `⟦Meas f e⟧ = meas_lift ∘ ⟦e⟧` —
the `FMeas`-functorial mirror of the `ne_score` clause.

### Runtime-parameter distributions (`ne_gaussian`, `ne_uniform`, `pkernel`, `kernel_lift`, `kernel_lift2`)

`Gaussian( e1 , e2 )` / `Uniform( e1 , e2 )` draw from the
normal/uniform family whose parameters are the **values** of the two
`tR'`-valued sub-expressions — so a sampled value can itself
parameterise the next draw (hierarchical models, e.g.
`examples.v::ex_gaussian_walk`). No witness braces: the kernel
families are *total*.

```coq
(* theories/programs/ppl.v *)
Inductive named_expr : named_ctx Ar -> T -> Type :=
  (* … *)
  | ne_gaussian : forall G,
      named_expr G tR' -> named_expr G tR' -> named_expr G tR'
  | ne_uniform : forall G,
      named_expr G tR' -> named_expr G tR' -> named_expr G tR'.
```

**The kernel layer** (`theories/programs/distributions.v`). A
`pkernel X Y` bundles a family of sub-probability measures
`pk_ker : X → FMeas Y` with the mathcomp-analysis kernel condition
(`pk_meas`: `x ↦ k(x)(U)` measurable for every measurable `U`) and
the unit-ball bound (`pk_ball`). Such a family *is* a measurable path
(`pkernel_is_path`, paper Def 3.7), so the Thm 6.1 machinery promotes
it to the semantic lift `kernel_lift k : FMeas X ⊸ FMeas Y`,
`ν ↦ ∫ k(x) ν(dx)` (Pettis integral), with the computation laws
`kernel_lift_E` (`(kernel_lift k ν)(U) = ∫ k(x)(U) ν(dx)`),
`kernel_lift_mass` (pointwise-mass-1 kernels preserve total mass) and
`kernel_lift_dirac` (`kernel_lift k δ_x = k(x)`). Two-argument
kernels go through `kernel_lift2 k := kernel_lift k ∘ fmeas_lax` —
the tensored argument pair becomes a joint measure on the product
object, exactly the `add_lift` / `mul_lift` route — with
`kernel_lift2_dirac` and the product-mass law `kernel_lift2_mass`.

Instances: `dirac_kernel` (`kernel_lift dirac_kernel = id`,
`dirac_kernel_lift_id`), `bernoulli_kernel` (the bundled `[0,1]`
value-dependent coin as a two-point measure on `R_obj`, agreeing with
`bern_lift` coordinatewise: `bernoulli_kernel_bern_lift_t` /
`bernoulli_kernel_bern_lift_f`), `gaussian_kernel`
(`(m,s) ↦ normal_prob m s` transported along the carrier cast) and
`uniform_kernel` (`(a,b) ↦ uniform_prob` for `a < b`, else `δ_a`).
**The `s = 0` convention**: `gaussian_kernel` overrides the `s = 0`
fibre to the Dirac `δ_m` — the degenerate weak limit of
`N(m, s) as s → 0` — because mathcomp-analysis' own `normal_prob m 0`
is a junk uniform-`[0,1]` *placeholder* (its `normal_pdf` falls back
to `uniform_pdf 0 1` at `s = 0`), not a meaningful distribution;
`s ≠ 0` (including `s < 0`) keeps mathcomp's genuine normal with
deviation `|s|`. Family measurability *in the parameters*
(`measurable_normal_prob_pair`, `measurable_uniform_int_pair`) is
proved by Fubini–Tonelli against Lebesgue measure.

The CBV clauses (`eD_gaussian_E` / `eD_uniform_E`,
`theories/programs/ppl_cbv.v`) are the `ne_add` shape with the kernel
lift in place of the pushforward:
`⟦Gaussian(e1,e2)⟧ = δ_Γ ; (⟦e1⟧ ⊗ ⟦e2⟧) ; kernel_lift2
gaussian_kernel`. The anchors
(`theories/programs/infra/kernel_anchors.v`): `eD_gaussian_at` /
`eD_gaussian_dirac_E` (on point-mass arguments the draw *is* the
transported `normal_prob`, with the `s = 0` Dirac fibre),
`eD_gaussian_mass` (the result's mass is the product of the argument
masses — the kernel is a pointwise probability,
`gaussian_kernel_norm1`), and the constant-parameter agreement
`eD_gaussian_sample_agree`:
`⟦Gaussian([|m|],[|s|])⟧γ = ⟦sample (gaussian m s)⟧γ` for `s ≠ 0` —
the old bundled-`sample` surface is the kernel surface at real
literals (the two transports are identified by
`pmeas_of_prob_fmeas`). The `Uniform` mirror is
`eD_uniform_at` / `eD_uniform_dirac_E` / `eD_uniform_mass` /
`eD_uniform_sample_agree`.

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

The CBV interpretation in `theories/programs/ppl_cbv.v` resolves `ne_fix`
(and `ne_fix_mr` at function body types) to the composite
`fix_comb ∘ ⟦λs.body⟧`, where `fix_comb` is the seeded value-fixpoint
combinator of `theories/programs/infra/em_fix_value.v` — see
[the CBV value-fixpoint
chapter](../../ppl/chapters/ppl-ch-the-cbv-value-fixpoint-at-function-types.html).

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

The CBV interpretation in
`theories/programs/ppl_cbv.v` dispatches `ne_fix_mr` on the body
type (`fix_mr_clause`): at `tfun t1 t2` it is the *same* genuine
seeded combinator `fix_comb` as `ne_fix`; at products of free types
it is the *same combinator transported along the Seely
decomposition* — `fix_mr_comb`, i.e. `fix_comb (free_base t)`
conjugated by the coalgebra iso `free_decomp : tyD_cbv t ≅
!̃(free_base t)`, whose `tprod` step is the EM-level Seely-2 iso
`EM_prod (!̃X) (!̃Y) ≅ !̃(X & Y)` of
`theories/programs/infra/em_fix_mr.v`. The mutual-recursion fixpoint
is genuine at *every* free body type; the surface witness is
`ex_even_odd_pair` (see the [Examples tab](../examples/)).

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

Direct-style: no `Ret` notation; `let "x" := M in N` desugars to
`ne_let` (not `ne_bind`). Brackets `[ … ]` enter the entry; curly
braces `{ x }` escape back to plain Rocq.

### Bundled densities and the `observe` operator (`udensity`, `prob`, `mk_udensity`, `mk_prob`, `gauss_udensity`, `observe`, `observe_gauss_E`)

The readable layer on top of the kernel notations — sugar only: each
form elaborates to existing constructors (plus the `ne_meas`
pushforward primitive); no new semantics is introduced. The `[0,1]`
proof obligations on coins and scores travel inside two bundled
records, so the surface forms never carry loose witnesses.

```coq
(* theories/programs/ppl.v — the bundled-density kit (Section RealFunKit) *)
Record udensity := MkUdensity {
  ud_f    : R -> R ;
  ud_meas : measurable_fun [set: R] ud_f ;
  ud_ge0  : forall r : R, (0 <= ud_f r)%R ;
  ud_le1  : forall r : R, (ud_f r <= 1)%R }.
Record prob := MkProb {
  pr_val : R ;
  pr_ge0 : (0 <= pr_val)%R ;
  pr_le1 : (pr_val <= 1)%R }.

(* theories/programs/ppl.v — the derived surface layer *)
Notation "'Meas' '{' f ',' Hf '}' e" := (ne_meas f Hf e) (* … *).
Notation "'Bernoulli' p" :=
  (ne_bernoulli (pr_val p) (pr_ge0 p) (pr_le1 p)) (* … *).
Notation "'Bernoulli' d e" :=
  (ne_bernoulli_f (ud_f d) (ud_meas d) (ud_ge0 d) (ud_le1 d) e) (* … *).
Notation "'Score' d e" :=
  (ne_score (ud_f d) (ud_meas d) (ud_ge0 d) (ud_le1 d) e) (* … *).
Notation "'observe' 'Gaussian' '{' s ',' y '}' e" :=
  (ne_score (ud_f (gauss_udensity s y)) (ud_meas (gauss_udensity s y))
            (ud_ge0 (gauss_udensity s y)) (ud_le1 (gauss_udensity s y)) e) (* … *).
Notation "'sample' m" :=
  (ne_sample (pm_meas m) (pm_ball m)) (* … *).
Notation "M > N" :=
  (ne_bernoulli_f (ud_f gt0_udensity) (ud_meas gt0_udensity)
     (ud_ge0 gt0_udensity) (ud_le1 gt0_udensity)
     (ne_add M (ne_meas negr negr_meas N))) (* … *).
Notation "'let' 'rec' f x ':=' M 'in' K" :=
  (ne_let f%string (ne_fix f%string (ne_lam x%string M)) K) (* … *).
```

- **Bundled `[0,1]` densities and scalars — `udensity` / `prob`.** A
  `udensity` packages a `[0,1]`-valued measurable density `ud_f`
  together with its three witnesses (`ud_meas`, `ud_ge0`, `ud_le1`); a
  `prob` packages a `[0,1]` scalar with its two bounds (`pr_ge0`,
  `pr_le1`). The smart constructors `mk_udensity f Hm Hg Hl` and
  `mk_prob p Hg Hl` build them from loose witnesses at example sites.
  Both records have primitive projections, so `ud_f (mk_udensity f …)
  = f` and `pr_val (mk_prob p …) = p` hold *definitionally* — the pins
  the downstream `bern_lift` / `score_lift` computations rely on.
- **The constant coin `Bernoulli p`** takes `p : prob` and flips the
  fair-or-biased coin `(pr_val p, 1 − pr_val p)`; the fair coin is
  `prob_half : prob` (`theories/programs/examples.v`).
- **The value-dependent coin `Bernoulli d e` and the score `Score d
  e`** take a bundled density `d : udensity` and the `tR'`-valued
  scrutinee `e`: the coin flips with success probability `ud_f d r`,
  the score weights the trace by `ud_f d r`, at the runtime value `r`
  of `e`. A coin or score with an explicit density `f` bounded in
  `[0,1]` is written `Bernoulli (mk_udensity f Hm Hg Hl) e` /
  `Score (mk_udensity f Hm Hg Hl) e`.
- **The `observe` operator — `observe Gaussian { s , y } e`.** Bayesian
  conditioning: score the trace by the likelihood of the datum `y`
  under `N(value(e), s)`, normalised by the distribution's intrinsic
  peak so the weight is a legal `[0,1]` density. The deviation `s` and
  datum `y` are Rocq-level constrs (the brace group); the predicted
  MEAN is the surface sub-expression `e` (e.g. a regression prediction
  `m·x + b`). It desugars through `Score (gauss_udensity s y) e`, i.e.
  `ne_score (ud_f (gauss_udensity s y)) … e`; since `ud_f (gauss_udensity
  s y) = gauss_obs_density s y` definitionally, `observe` and `Score`
  share the same density bundle. `gauss_udensity s y : udensity`
  bundles `gauss_obs_density s y = (fun μ ⇒ normal_pdf μ s y /
  normal_peak s)` with its `[0,1]` proofs; there is no user-supplied
  envelope — the peak `normal_peak s` is intrinsic. The denotation
  lemma is `observe_gauss_E` (`theories/programs/ppl_cbv.v`): at a
  setlike Dirac environment the trace is weighted by
  `normal_pdf μ s y / normal_peak s` at the runtime mean `μ`.
- **Bundled sampling `sample m`** — `pmeas` packages a sub-probability
  with its unit-ball witness; `prob_pmeas` transports any
  mathcomp-analysis probability on `R` to a `pmeas`, giving the named
  distributions `gaussian m s` / `uniform a b`
  (`theories/programs/examples.v`): `let "m" := sample gaussian01 in …`.
- **The comparison coin `e1 > e2`** — `ne_bernoulli_f` at the bundled
  indicator density `gt0_udensity` (whose `ud_f` is `gt0_ind`), on
  `e1 + Meas{negr} e2`: on point masses the deterministic test
  `a > b`; on diffuse arguments the probability that an independent
  draw of `e1` exceeds one of `e2`.
- **`let rec f x := M in K`** — OCaml-style recursive function
  binding, `ne_let f (ne_fix f (ne_lam x M)) K`; an annotated form
  `let rec f x ::: T1 ==> T2 := M in K` covers bodies that leave the
  binder type undetermined.
- **`Condition { d } M`** — the Pyro-style soft conditioning operator
  for a bundled density `d : udensity` applied to a closed model `M`
  (`examples.v::ex_condition_comb`; see the [Examples
  tab](../examples/) for the conditioning law and the
  rejection-sampling equivalence).

The end-to-end demos are `ex_surface_demo` (annotated `let rec`,
`sample gaussian01`, the `>` coin) and `ex_surface_walk`
(annotation-free `let rec`, the bundled `Bernoulli`/`Score` forms),
both with elaboration pins (`ex_surface_demo_decomp`) and compile-time
CBV denotations (`ex_surface_demo_cbv` / `ex_surface_walk_cbv`).

### Scores, densities, and the sub-probability boundary (`ne_score`, `cones_hom_norm_le1`, `score_lift`)

This is a sub-probability model, and that fixes exactly which scores
it can express. Every morphism of `ICone` is non-expansive: the
`cones_hom` record carries a norm-bound field, so a map never
increases mass.

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

Scoring weights a measure by a density: `score_lift f` sends a
measure `µ` to `f · µ`, of mass `∫ f dµ`. As a morphism its operator
norm is `sup f`, so `score_lift f` is a map of the category — and
`ne_score f` is well-typed — exactly when `f` is bounded by `1`.
That is the source of the `forall r, f r <= 1` witness on `ne_score`
and `ne_bernoulli_f`: not a modelling convenience but the condition
for the score to be a morphism at all.

The distinction that matters in practice is between *sampling* and
*observing*. Sampling is always fine: `sample (gaussian m s)`
denotes a probability measure of mass `1`, a good morphism for every
`m` and `s`. Observing — scoring by a density, `observe Gaussian {s,y}
e` weighing the trace by the Gaussian likelihood of `y` — is the
constrained operation, a morphism only while the weight stays in
`[0,1]`. The line that matters is **bounded vs unbounded**.

A **bounded** likelihood is always conditionable, and `observe` does
exactly this. `N(μ, σ)` peaks at its intrinsic peak `normal_peak σ =
1/(σ√(2π))`; the *unnormalised* pdf crosses `1` as soon as
`σ < 1/√(2π) ≈ 0.399`, so it is not directly a `[0,1]` weight. But the
peak is a finite bound, and dividing by it gives the legal weight
`gauss_obs_density σ y = normal_pdf μ σ y / normal_peak σ ∈ [0,1]`
(the `udensity` bundle `gauss_udensity σ y`). This is exactly what
`observe` scores by — no user-supplied envelope, the peak is intrinsic
to the distribution. The normaliser cancels in the posterior: the
conditioned distribution `∫_U f dν / ∫ f dν` is independent of any
positive scaling of `f`, so dividing by `normal_peak σ` changes the
total evidence but never the posterior. The same holds for the
conditioning/rejection pair, where dividing by the peak is classical
rejection sampling with that envelope.

Only a **genuinely unbounded** family is out of scope. When a density
has no finite peak — a Gaussian with `σ` free to approach `0`, a
likelihood that can be arbitrarily sharp — no normalisation brings it
inside the unit ball, and the observation is not a morphism of `ICone`
and has no denotation here. This is a property of every
sub-probability model, integrable cones and probabilistic coherence
spaces alike, not of the encoding.

The semantics designed to score by arbitrary unbounded weights is
the *s-finite kernel* model (Staton and collaborators): it drops the
norm bound and lets `score w` denote a measure of any finite mass.
The cone model makes the opposite trade — it keeps the
sub-probability discipline and, in return, carries the higher-order
and analytic structure (the `!` comonad, the Seely and
Eilenberg–Moore development) that the kernel model does not. An
`observe` with an unbounded density is the price of that structure.

---

## Call-by-value interpretation (linhom + comonoid)

**Definition (CBV interpretation).** *Each type `τ` denotes a
`!`-coalgebra `⟦τ⟧ ∈ EM(!)`; each well-typed program `Γ ⊢ M : τ`
denotes a linear morphism `⟦M⟧ : U⟦Γ⟧ ⊸ U⟦τ⟧` in `ICone` — an
element of `linhom_car Ar (coalg_obj ⟦Γ⟧) (coalg_obj ⟦τ⟧)`. Programs
are not coalgebra morphisms (the sampling clause does not commute
with the §9.7 duplicability structure on `FMeas`); the coalgebra
structure of the context is used only through the comonoid pair
`(δ, ε) = (coalg_d, coalg_e)` that every EM(!) object carries by
Melliès' Proposition 28.*

In Rocq this is the function `eD` of `theories/programs/ppl_cbv.v`,
sending a term `M : named_expr Γ τ` to an element of
`linhom_car Ar (coalg_obj (ctxD_cbv (drop_names Γ)))
(coalg_obj (tyD_cbv τ))`, defined by structural recursion on
`named_expr`. Internally it is built from an `icones_hom`-valued
helper `eD_cbv` (an inhabitant of the unit ball of the same
`linhom`) and forwarded to a linhom by `icones_to_linhom`; the two
views are interchangeable. There is no Kleisli wrapping on the
codomain of `tfun`: function *values* are linear maps
`U⟦t1⟧ ⊸ U⟦t2⟧`, and duplicability comes from the outer cofree `!̃`
only.

This chapter presents the type and context translations, the EM
cartesian primitives the interpreter is assembled from, the
interpreter itself clause by clause, and the regression pack that
pins each clause. The semantic laws *about* the interpreter — the
recursion-unfolding equations, the let-at-sample integral law, and
the sharing-semantics anchors — live in
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
| EM cartesian primitives (`δ`, `ε`, projections, pairing) | `coalg_d`, `coalg_e`, `em_proj1_mor`, `em_proj2_mor`, `em_pair_mor`, `em_term_mor` — `theories/homs/em_cartesian.v`; cartesian-η `em_pair_mor_proj_id` — `theories/programs/infra/cbv_adjunction.v` |
| Definitional-unfolding pack (one lemma per clause) | `eD_var_E` … `eD_fix_mr_prod_E` (25 lemmas) — `theories/programs/ppl_cbv.v` (Section EDUnfold) |
| Recursion-unfolding equations (semantic; setlike points) | `eD_fix_at_setlike`, `eD_fix_unfold`, `eD_fix_unfold_closed` — `theories/programs/infra/cbv_fix_unfold.v` |

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

The `ne_fix` clause is the composite `fix_comb ∘ ⟦λs.body⟧`: the
self-abstraction is interpreted as an *ordinary* lambda (the
`ne_lam` clause, inlined because `ne_lam s body` is not a subterm of
`ne_fix s body`), then post-composed with the seeded value-fixpoint
combinator `fix_comb : EM(!̃(!L ⊸ !L), !̃L)` of
`theories/programs/infra/em_fix_value.v`, at `L := U⟦t1⟧ ⊸ U⟦t2⟧` —
see
[the CBV value-fixpoint
chapter](../../ppl/chapters/ppl-ch-the-cbv-value-fixpoint-at-function-types.html).
The `ne_fix_mr` clause dispatches on the body type
(`fix_mr_clause`): the same `fix_comb` composite at `tfun`, the
Seely-transported `fix_mr_comb` at products of frees. Every
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

### The value-dependent Bernoulli lift (`bern_lift`, `bern_lift_dirac`, `bern_lift_mass`)

The semantic engine of `ne_bernoulli_f`: an
`icones_hom (FMeas R_obj) (bool_cone_car Ar)` sending a measure `µ`
on the reals to the 2-point sub-probability
`(∫ f dµ, ∫ (1 − f) dµ)` — sample `r ~ µ`, then flip a coin with
success probability `f r`. It lives in `theories/programs/ppl.v`
(Section BernTmLift), and the `ne_bernoulli_f` clause of `eD_cbv`
post-composes it with the scrutinee's denotation, exactly as
`ne_score` post-composes `score_lift`.

The construction is the *path route*, a verbatim clone of the score
lift: package `r ↦ bernoulli (f (cR r))` as a measurable path into
`bool_cone_car Ar` (the three tests of the bool cone evaluate along
the path to `f∘cR`, `1 − f∘cR` and the constant `1`), then promote
with `int_to_linhom`. The integral semantics is then automatic by
Pettis uniqueness against the componentwise integral `bool_int` of
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
total-mass identity: the coin is norm-1 *pointwise* (it always
lands), so the lift preserves total mass — with `‖µ‖ = 1` the reject
weight is exactly `1 − ∫ f dµ`, which is what makes the headline's
per-iterate mass recurrence affine.

```coq
(* theories/programs/ppl.v (Section BernTmLift) *)
Lemma bern_lift_mass (mu : fmeas R (ar_carrier Ar R_obj)) :
  cone_norm (Lfun bern_lift mu) =
  fine (fmeas_mu mu [set: ar_carrier Ar R_obj]).
```

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

### The definitional-unfolding pack (`eD_var_E` … `eD_fix_mr_prod_E`)

One lemma per `eD_cbv` clause — 25 in total: one for each of the 23
`named_expr` constructors, plus the two per-body-type refinements
`eD_fix_mr_fun_E` / `eD_fix_mr_prod_E` of the dispatched `ne_fix_mr`
clause — pins the exact clause body of the interpreter, so any
refactor of `eD_cbv` (or of the combinators it is built from) breaks
loudly in a named lemma instead of silently changing the semantics.

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
computation law `eD_fix_at_setlike` and the honest recursion
equation `eD_fix_unfold` — live in
`theories/programs/infra/cbv_fix_unfold.v` (they need the
setlike-point kit of `infra/cbv_anchors.v`, which imports this
file); they are documented with the fixpoint combinator itself in
[the CBV value-fixpoint
chapter](../../ppl/chapters/ppl-ch-the-cbv-value-fixpoint-at-function-types.html).

---

## The SCones↔ICones-tensor bilinear stability bridge

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

### Lift `linhom → stablehom` (`linhom_to_stablehom`)

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

---

## The CBV value-fixpoint at function types

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

The chapter tells the story in order. First the *degeneracy
theorem*: the naive zero-seeded iteration — the Kleene iteration of
`theories/programs/infra/em_fix.v`'s linear step
`prev ↦ M ∘ (id ⊗ prev) ∘ δ` from the linhom cone-zero, which used
to be `em_fix.v`'s CBV value-fixpoint operator before its removal —
is *provably the zero linhom*, always (`Phi_fun_lfp_eq0`): a linear
step preserves the zero seed, and the bottom of a CBV function-value
type is not the cone-zero of `!L` but the promoted zero `(0)!`, the
diverging-function value of `e_bang`-mass one. Then the repair: seed
the iteration at the genuine bottom `0 : A` *under* the promotion,
interleaving `der` and `prom` so that each iterate re-enters the
body as a promoted value — the `prom ∘ der` sandwich is what makes
the chain productive for *any* unit-ball body, linear or not (the
step `x ↦ der (F (x!))` is monotone because `prom` is totally
monotone and `F`, `der` are linear). Coalgebra-morphism-ness of the
combinator comes for free: the value map `F ↦ sup_n x_n` is built
from existing `SCones` morphisms, converted to a linear map
`!(!A ⊸ !A) ⊸ A` by the SAFT hom-bijection `lin`, and packaged by
`adj_psi` of the `U ⊣ !̃` adjunction. Finally the *mutual-recursion
transport*: a product of free types is not literally cofree, but it
is *isomorphic* to a cofree coalgebra through the EM-level Seely-2
iso, and conjugating `fix_comb` by that iso makes `ne_fix_mr`
genuine at every free body type.

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

### The degeneracy theorem (`Phi_fun_lfp_eq0`)

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

### The naive linear Kleene step (`Phi_fun`)

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

### The seeded Kleene core (`kleene_from`, `lfp_from`)

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

### The interleaved chain and the value map (`fix_chain`, `fix_value`)

Fix `A` and write `!A := Bang Ar A`, `LL := !A ⊸ !A`. The
interleaved chain of a body `F : LL` is `x_0 = 0 : A`,
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

### The combinator (`fix_comb`, `fix_prom_E`)

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

### Coalgebraic bodies: the literal chain (`fix_coalg_simpl`)

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

### Non-degeneracy (`fix_prom_neq0`, `fix_id_E`)

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

### The mutual-recursion transport (`coalg_iso`, `seely2_em_iso`, `fix_comb_iso`, `free_decomp`, `fix_mr_comb`)

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

### The interpreter wiring (`eD_fix_E`, `fix_mr_clause`)

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

### The recursion-unfolding equations (`eD_fix_at_setlike`, `eD_fix_unfold`)

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

### The SCones fixpoint core (`Yfix`)

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

### The let-at-sample integral law (`eD_let_sample_int`, `eD_let_sample_mu_E`, `eD_let_int`)

The law ties the CBV interpretation of `let x = sample µ in K` to
the Pettis integral of `K`'s denotation over the Diracs of `µ`:
*⟦let x = sample µ in K⟧(γ) = ∫ ⟦K⟧(γ ⊗ δ_r) µ(dr)*, pointwise at
arbitrary `γ`. No unit-ball and no setlike hypothesis is needed
anywhere, because every step is driven by a genuine
`linhom_car` / `icones_hom` field, all of which hold on the whole
cone. The proof is a four-step composition: (1) the sample-let
*collapse* `⟦let x = sample µ in K⟧(γ) = ⟦K⟧(γ ⊗ µ)` — the inner
`em_pair_mor id (const µ)` erases the context copy through the
comonoid counit law `emc_counitR` (`em_pair_mor_const_E`, stated for
an arbitrary constant); (2) the Dirac approximation `µ = ∫ δ_r µ(dr)`
re-spelled with the bare `dirac_fmeas` integrand
(`icone_integral_dirac_fmeas`, from `bilin.v`'s Thm 6.1 Dirac
approximation); (3) tensoring with a fixed point preserves Pettis
integrals, `γ ⊗ (∫ β dµ) = ∫ (γ ⊗ β r) µ(dr)` — the
`linhom_pres_int` field of `τ(γ)` (`ptensor_icone_integral`); and
(4) the `icones_hom_pres_int` field of `⟦K⟧` pushes the denotation
under the integral.

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

### The affine cascade and the sup-mass bridge (`affine_iter_closed`, `fmeas_kleene_sup_U_E`)

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

### The setlike-point kit (`coalg_d_setlike`, `coalg_str_tensor_setlike`)

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

### The sharing-semantics anchors (`let_bernoulli_pair_diag`, `pair_bernoulli_indep`)

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

### The β-rule and the if-pins (`eD_beta`, `eD_if_true`, `eD_if_false`)

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

### The CBV marginals (`ex_score_posterior_cbv_E`, `ex_reject_normalises_score`, `ex_random_constant_cbv_marginal`, `ex_random_linear_cbv_marginal`, `ex_bayes_linear_cbv_evidence`)

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

### The conditioning law and the equivalence (`condition_model_E`, `condition_E`, `reject_normalises_condition`)

The score-posterior identity, promoted to an operator: the Pyro-style
soft conditioning combinator `condition`
(`examples.v::ex_condition_comb`, surface form `Condition { d } M`)
takes a bundled likelihood `d : udensity` and a model `m : ta → tR`,
and returns the conditioned model
`λa. let x = m a in let _ = Score d x in x` (writing `f := ud_f d`).
The conditioning law (Section ConditionModel of
`theories/programs/ex_reject_model.v`) states that at a unit-ball
model value `g!` and a setlike unit-ball input `a₀`, writing
`ν_M := g(a₀)` for the model's output sub-distribution, the
conditioned model's output is the likelihood-reweighted measure —
`ex_score_posterior_cbv_E` with an arbitrary model in place of
`sample µ`. The proof engine is this chapter's general let-law
`eD_let_mu_E` at `ν_M`, with the score clause computing on Diracs
(`eD_score_E` + `score_lift_dirac`) and the returned variable
projected through `em_proj1_mor_unitE` / `Lfun_scaleE`.

```coq
(* theories/programs/ex_reject_model.v (Section ConditionModel) *)
Theorem condition_model_E (U : set (ar_carrier Ar R_obj))
    (mU : measurable U) :
  fmeas_mu cond_model_denot U =
  \int[fmeas_mu (reject_model_dist g a0)]_(r in U) (f (cR r))%:E.
```

In the readable `⟦·⟧` brackets (Section ReadableHeadlines, over an
arbitrary thunked model `model_prog := λ_. Mbody` with
`model_run := model_prog ()` and
`condition_prog := (condition model_prog f) ()`), the law is
`condition_E`, and combining it with the rejection master identity
`reject_prog_master` gives the equivalence — rejection sampling
computes the conditioned model's normalised distribution:

```coq
(* theories/programs/ex_reject_model.v (Section ReadableHeadlines) *)
Theorem condition_E U (mU : measurable U) :
  ⟦ condition_prog ⟧ U = \int[⟦ model_run ⟧]_(x in U) (f (cR x))%:E.

Theorem reject_normalises_condition U (mU : measurable U) :
  ((1 - fine (⟦ model_run ⟧ [set: ar_carrier Ar R_obj])
      + fine (\int[⟦ model_run ⟧]_(x in [set: ar_carrier Ar R_obj])
                (f (cR x))%:E))%R)%:E
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

### Icones-hom packaging (`bool_case_linhom`, `bool_case_icones_hom`, `alpha_linhom`, `beta_linhom`)

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
