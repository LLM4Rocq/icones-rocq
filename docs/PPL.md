# A direct-style PPL on top of the integrable-cones model

A typed probabilistic functional language sits on top of the paper's
categorical model. Each type denotes a `!`-coalgebra, each program a
*linear* morphism in `ICone` between the underlying carriers of the
context and result coalgebras, and recursion at function type is
realised by a value-fixpoint *combinator* in the Eilenberg–Moore
category of `!` — the supremum of an interleaved Kleene chain seeded
at the diverging function value, computed pointwise through a
`der`/`prom` sandwich. The language is direct-style
(Plotkin / Girard) and named-variable (Saito–Affeldt APLAS 2023), and
probabilistic effects live entirely in the interpretation: there is
no `tprob` type marker, no syntactic `return`, no `bind`.
Call-by-value is where the *Eilenberg–Moore* route to the exponential
leads, exactly as the *co-Kleisli* route leads to call-by-name
(Melliès, *Categorical Semantics of Linear Logic* §7.4); the
call-by-name reading of the same surface syntax — through the
cartesian closed `SCones` of paper §7, which is that co-Kleisli side —
is preserved on the `cbn-track` branch, and main is CBV-only. The
choice of side is the reason this layer exists: a probabilistic
call-by-value language is named in the paper's own abstract as the
thing an integration theory for cones is *for*, and is left there as
future work.

The paper-side correspondence (§§ 2–9 ↔ Rocq) lives on the
[Paper tab](../paper/), and the example programs with their mass,
marginal and PMF identities on the [Examples tab](../examples/). This
document covers what sits *above* the paper: the surface language,
its CBV interpretation, the fixpoint and integral-law infrastructure,
and the semantic correctness statements one can make at the
categorical level.

The seven chapters follow the order in which the development is
built. The syntax chapter introduces the intrinsically-typed inductive
`named_expr` and the type and context layer it is indexed by; the
surface-notation chapter adds the canonical-structure search behind
`#"x"` and the grammar the example programs are written in; and the
probability-surface chapter collects the $[0,1]$-typed coins, scores
and observation forms built on top of both. The call-by-value chapter
then gives the interpretation `eD` — the semantic target, the type and
context translations, the interpreter clause by clause, and its
helpers — and the recursion chapter isolates the one clause that
needs a construction of its own, the seeded combinator `fix_comb`
together with its mutual-recursion transport. The semantic-laws
chapter states what can then be proved about `eD`: the $\beta$-rule, the
integral laws, the sharing anchors, and the marginal and conditioning
identities. The boolean-cascade chapter closes with the 2-point cone
that `tbool` denotes — the infrastructure every branching construct of
the earlier chapters rests on.

---

## Syntax: types, contexts, and terms

The source language is a simply-typed lambda calculus with sampling,
scoring, recursion at function type, a two-point boolean type, and
mutual recursion at any free-coalgebra type. Its syntax is a single
intrinsically-typed inductive `named_expr Γ τ` in named-variable style
(Saito–Affeldt APLAS 2023), indexed by a *named* context
`named_ctx = seq (string × ppl_type)`, and consumed by the CBV
interpretation `eD` of the call-by-value chapter. The language is
direct-style (Plotkin / Girard): there is no `tprob` type marker, no
syntactic `return` and no `bind` — the probabilistic effects live
entirely in the interpretation.

This chapter walks the twenty-seven constructors of the inductive group
by group: the type and context layer they are indexed by, the pure
fragment, the effectful constructors, measurable-function application,
the runtime-parameter distributions together with the kernel layer that
backs them, and the two recursion constructors. The canonical-structure
machinery behind `#"x"` and the notation layers on top of the inductive
are the subject of the surface-notation chapter; the four remaining
constructors — the `tProb`-typed `ne_bernoulli_p`, `ne_score_p`,
`ne_to_prob` and `ne_incl` — are declared in the same inductive, but are
introduced together with the wrappers that give them their surface names
in the probability-surface chapter.

| Construction | Statement | Rocq |
|---|---|---|
| Types and contexts | The five surface types, and the string-named contexts they are indexed by. | `ppl_type`, `named_ctx`, `drop_names` — theories/programs/ppl.v |
| Named variables | A witness that some string identifier of the context is bound at a given type. | `named_var`, `nv_head`, `nv_tail` — theories/programs/ppl.v |
| The pure fragment | Thirteen constructors: variables, unit, products, abstraction and application, let, real literals, arithmetic, and the two boolean values. | `named_expr` — theories/programs/ppl.v |
| Sampling, scoring, and branching | One fixed-measure real draw, one boolean coin (constant and value-dependent), one soft-conditioning score, and boolean elimination. | `ne_sample`, `ne_score`, `ne_if` — theories/programs/ppl.v |
| Measurable-function application | Push the value of a real-valued sub-expression through a measurable meta-level function. | `ne_meas`, `meas_lift` — theories/programs/ppl.v |
| Runtime-parameter distributions | Normal and uniform draws whose parameters are the values of two sub-expressions. | `ne_gaussian`, `ne_uniform` — theories/programs/ppl.v |
| Parameterized kernels | Bounded families of sub-probability measures, and their Pettis-integral lift to a linear morphism. | `pkernel`, `kernel_lift`, `kernel_lift2` — theories/programs/distributions.v |
| Recursion at function type | OCaml-style `let rec`, restricted to function types. | `ne_fix` — theories/programs/ppl.v |
| Mutual recursion and free-coalgebra types | Recursion at any body type whose denotation is a free coalgebra, gated by a decidable predicate. | `ne_fix_mr`, `is_free_coalg_type` — theories/programs/ppl.v |

### Types and contexts (`ppl_type`, `named_ctx`, `drop_names`)

The surface types are a five-constructor grammar — unit, a two-point
boolean type, an arbitrary measurable base object `tbase X`, binary
products, and function types. A context is a list of string-named typed
bindings, and the private projection `drop_names` forgets the names,
leaving the type-only De Bruijn skeleton `ppl_ctx`.

```coq
(* theories/programs/ppl.v *)
Inductive ppl_type : Type :=
  | tunit
  | tbool
  | tbase (X : ar_obj Ar)
  | tprod (t1 t2 : ppl_type)
  | tfun  (t1 t2 : ppl_type).

Definition ppl_ctx : Type := list (ppl_type Ar).

Definition named_ctx : Type := list (string * ppl_type Ar).

Definition drop_names (G : named_ctx) : ppl_ctx :=
  map snd G.
```

The categorical interpretation lives on `drop_names G`; the named layer
is only there for the canonical-structure-driven variable lookup at
`#"x"` sites.

> Nothing in the semantics sees the strings — the named context is a
> surface convenience projected away before `ctxD_cbv` is reached.
> `tbase X` leaves the base type abstract over the ambient measurable
> subcategory, so the same syntax is reused at whichever real object
> `R_obj` the interpretation fixes. `tbool` is a separate type rather
> than an encoding because its denotation is the two-point cone
> (`tyD_cbv tbool = bool_cone_coalg`), which is what gives sharing
> rather than independent re-sampling — the boolean-cascade chapter
> builds that cone.

### Named variables (`named_var`, `nv_head`, `nv_tail`)

A variable occurrence is not a string but a *witness*: `named_var G t`
says that some string identifier of `G` is bound to type `t`, with
`nv_head` for the head binding and `nv_tail` for stripping a binding and
recursing. The bridge `named_var_to_has_var` projects such a witness to
the intrinsic De Bruijn index `has_var (drop_names G) t` on which the
interpretation's variable lookup runs.

```coq
(* theories/programs/ppl.v *)
Inductive named_var : named_ctx -> ppl_type Ar -> Type :=
  | nv_head (x : string) (t : ppl_type Ar) (G : named_ctx) :
      named_var ((x, t) :: G) t
  | nv_tail (y : string) (s : ppl_type Ar) (G : named_ctx)
            (t : ppl_type Ar) (v : named_var G t) :
      named_var ((y, s) :: G) t.

Fixpoint named_var_to_has_var (G : named_ctx) (t : ppl_type Ar)
    (v : named_var G t) {struct v} : has_var (drop_names G) t :=
  match v in named_var G0 t0 return has_var (drop_names G0) t0 with
  | nv_head _ t' G' => @hv_zero (drop_names G') t'
  | nv_tail _ sty G' t' v' =>
      @hv_succ (drop_names G') t' sty (named_var_to_has_var v')
  end.
```

> The witness type is the whole of the named layer: `named_expr` stores
> a `named_var`, never a string, so no lookup can fail at interpretation
> time and no scoping side condition is needed. Building the witness
> from a string is the job of the canonical-structure `find_nv` cascade
> behind `#"x"`, and `named_var_to_has_var` is the one-line bridge back
> to the skeletal `has_var` index used by `drop_names`-indexed
> machinery.

### The pure fragment (`named_expr`, `ne_var`, `ne_lam`, `ne_app`, `ne_let`, `ne_false`)

The pure fragment of `named_expr` is a standard intrinsically-typed
simply-typed lambda calculus with products, let, real constants,
arithmetic, and the two boolean values: thirteen of the inductive's
twenty-seven constructors — `ne_var`, `ne_tt`, `ne_pair`, `ne_fst`,
`ne_snd`, `ne_lam`, `ne_app`, `ne_let`, `ne_real`, `ne_add`, `ne_mul`,
`ne_true`, `ne_false`.

```coq
(* theories/programs/ppl.v *)
Inductive named_expr : named_ctx Ar -> T -> Type :=
  | ne_var   (G : named_ctx Ar) (t : T) :
      named_var G t -> named_expr G t
  | ne_tt    (G : named_ctx Ar) : named_expr G tunit
  | ne_pair  (G : named_ctx Ar) (t1 t2 : T) :
      named_expr G t1 -> named_expr G t2 -> named_expr G (tprod t1 t2)
  | ne_fst   (G : named_ctx Ar) (t1 t2 : T) :
      named_expr G (tprod t1 t2) -> named_expr G t1
  | ne_snd   (G : named_ctx Ar) (t1 t2 : T) :
      named_expr G (tprod t1 t2) -> named_expr G t2
  | ne_lam   (G : named_ctx Ar) (x : string) (t1 t2 : T) :
      named_expr ((x, t1) :: G) t2 -> named_expr G (tfun t1 t2)
  (* … ne_fix, ne_fix_mr … *)
  | ne_app   (G : named_ctx Ar) (t1 t2 : T) :
      named_expr G (tfun t1 t2) -> named_expr G t1 -> named_expr G t2
  | ne_let   (G : named_ctx Ar) (x : string) (t1 t2 : T) :
      named_expr G t1 ->
      named_expr ((x, t1) :: G) t2 ->
      named_expr G t2
  (* … ne_sample … *)
  | ne_real  (G : named_ctx Ar) (r : R) : named_expr G tR'
  (* … ne_score … *)
  | ne_add   (G : named_ctx Ar) :
      named_expr G tR' -> named_expr G tR' -> named_expr G tR'
  | ne_mul   (G : named_ctx Ar) :
      named_expr G tR' -> named_expr G tR' -> named_expr G tR'
  (* … ne_meas, ne_gaussian, ne_uniform … *)
  | ne_true  (G : named_ctx Ar) : named_expr G tbool
  | ne_false (G : named_ctx Ar) : named_expr G tbool
  (* … ne_bernoulli, ne_bernoulli_f, ne_if, and the four tProb
     constructors ne_bernoulli_p, ne_score_p, ne_to_prob, ne_incl
     — see the probability-surface chapter … *)
```

Application is direct — `ne_app : named_expr G (tfun t1 t2) ->
named_expr G t1 -> named_expr G t2`, not Moggi fine-grain (the
value/computation split under which applying a function would yield a
suspended computation rather than a term) — and `ne_lam`
does not mark its body as a computation: the effect structure is in the
semantics. `ne_let` is the Plotkin/Girard CBV sequencer, interpreted by
the comonoid-diagonal recipe $\delta_\Gamma ; (id_\Gamma \otimes \llbracket M\rrbracket) ; \llbracket K\rrbracket$.

> Binding and context-shared constructors carry bidirectionality hints
> `&` (e.g. `Arguments ne_lam {R Ar R_obj G} x & {t1 t2} M`), which tell
> the elaborator to resolve the outer context index first and only then
> descend into the sub-expressions. They are load-bearing, not cosmetic:
> without them the `find_nv` canonical-structure lookup at `#"x"` sites
> fires against an open context metavariable and picks the wrong
> instance — exactly the Saito–Affeldt APLAS 2023 §5.1 pattern.

### Sampling, scoring, and branching (`ne_sample`, `ne_score`, `ne_bernoulli`, `ne_bernoulli_f`, `ne_if`)

The effectful constructors are direct-style — the probability monad
lives in the interpretation `eD`, not in the source types — and they
divide by what they produce. `ne_sample` is one real draw from a fixed
sub-probability measure (`→ tR'`). `ne_bernoulli` and `ne_bernoulli_f`
are the boolean coin (`→ tbool`), the sole source of boolean randomness,
consumed by `ne_if` for probabilistic branching. `ne_score` is soft
conditioning (`→ tunit`).

```coq
(* theories/programs/ppl.v *)
Inductive named_expr : named_ctx Ar -> T -> Type :=
  (* … pure constructors above … *)
  | ne_sample (G : named_ctx Ar)
              (mu : fmeas R (ar_carrier Ar R_obj))
              (Hmu : (cone_norm mu <= 1)%R) :
      named_expr G tR'
  | ne_score (G : named_ctx Ar)
             (f : R -> R)
             (Hf_meas : measurable_fun [set: R] f)
             (Hf_ge0 : forall r : R, (0 <= f r)%R)
             (Hf_le1 : forall r : R, (f r <= 1)%R)
             (e : named_expr G tR') : named_expr G tunit
  | ne_bernoulli (G : named_ctx Ar) (p : R)
                 (Hp_ge0 : (0 <= p)%R) (Hp_le1 : (p <= 1)%R) :
      named_expr G tbool
  | ne_bernoulli_f (G : named_ctx Ar)
                   (f : R -> R)
                   (Hf_meas : measurable_fun [set: R] f)
                   (Hf_ge0 : forall r : R, (0 <= f r)%R)
                   (Hf_le1 : forall r : R, (f r <= 1)%R)
                   (e : named_expr G tR') : named_expr G tbool
  | ne_if (G : named_ctx Ar) (t : T) :
      named_expr G tbool ->
      named_expr G t ->
      named_expr G t ->
      named_expr G t
```

`ne_score` carries a density `f : R → R` valued in $[0,1]$; the bound is
the unit-ball discipline of `linhom_icones` (a linear map is packaged as
an `icones_hom` only together with a proof that its operator norm is
$\leq 1$, so it never increases cone-norm), and what it rules out —
genuinely unbounded densities — is discussed with `score_lift`. The
boolean coin shares that discipline: `ne_bernoulli p` is the constant
coin `(p, 1 − p)`, and `ne_bernoulli_f f e` is value-dependent — the
coin `(f r, 1 − f r)` at the value `r` of the `tR'`-valued
sub-expression `e` — its CBV engine the path lift `bern_lift` (the paper
Thm 6.1 promotion of a bounded measurable family of cone points to a
linear morphism, by integration), the boolean twin of `score_lift`. The witness layout of `ne_bernoulli_f`
mirrors `ne_score` one for one.

Only three sources of randomness are baked into the syntax: one
fixed-measure sample, one boolean coin, and one score. Everything else
is derived — the real-valued *named* distributions `gaussian` /
`uniform` of `theories/programs/examples.v` are built on `ne_sample`,
and the *runtime-parameter* ones on `ne_gaussian` / `ne_uniform` and the
probability-kernel layer.

> The $[0,1]$ discipline is carried by a type, not by loose witnesses:
> the probability type `tProb P` — a `tbase` over the $[0,1]$ object of
> a bundle `P : probObj` — is the surface home of every coin and score,
> and the witness-free readable forms built over it (`Bernoulli`,
> `Score`, and the abstract test-function coin at a `testfn`) are the
> subject of the probability-surface chapter. Downstream, `ne_if` is
> resolved by `if_icones` through the universal co-pairing
> `bool_case_linhom` of the boolean-cascade chapter, and
> `ne_bernoulli_f` is the accept/reject primitive of the
> rejection-sampling headline example `ex_reject`.

### Measurable-function application (`ne_meas`, `meas_lift`, `meas_lift_dirac`, `meas_lift_mass`)

`ne_meas f Hf e` pushes the value of the `tR'`-valued sub-expression `e`
through a measurable meta-level function `f : R → R` — surface form
`Meas { f , Hf } e`. Unlike `ne_score` and `ne_bernoulli_f`, no $[0,1]$
bounds are needed: the semantics is the `FMeas` functorial action
(pushforward), whose operator norm is already $\leq 1$.

```coq
(* theories/programs/ppl.v *)
  | ne_meas  (G : named_ctx Ar)
             (f : R -> R)
             (Hf_meas : measurable_fun [set: R] f)
             (e : named_expr G tR') : named_expr G tR'

(* … Section MeasTmLift … *)
Definition meas_fun (c : ar_carrier Ar R_obj) : ar_carrier Ar R_obj :=
  R_to_carrier R_carrier_eq (f (cR c)).

Definition meas_hom : ar_hom Ar R_obj R_obj := meas_fun.

Definition meas_lift : icones_hom Ar (FMeas R_obj) (FMeas R_obj) :=
  FMeas_fmap meas_hom.
```

The semantic engine is `meas_lift := FMeas_fmap meas_hom`, the
Dirac-path pushforward at the carrier transport
$\hat{f} = R_{\text{to\_carrier}} \circ f \circ \text{carrier\_to\_R}$, with two load-bearing laws:
`meas_lift_dirac` (on a point mass, application — $\delta_r \mapsto \delta_{f r}$) and
`meas_lift_mass` (the pushforward preserves total mass).

> The CBV clause is `eD_meas_E` (`theories/programs/ppl_cbv.v`):
> $\llbracket \text{Meas } f e \rrbracket = \text{meas\_lift} \circ \llbracket e \rrbracket$ — the `FMeas`-functorial mirror of the
> `ne_score` clause, with a plain functor action where scoring instead
> needs a path lift — the integral-based promotion (paper Thm 6.1) of a
> measurable family of cone points to a linear morphism. This is the one
> effect-shaped constructor that needs no bound
> proof at all, which is why `Meas { f , Hf } e` carries only the
> measurability witness.

### Runtime-parameter distributions (`ne_gaussian`, `ne_uniform`)

`Gaussian( e1 , e2 )` and `Uniform( e1 , e2 )` draw from the
normal/uniform family whose parameters are the **values** of the two
`tR'`-valued sub-expressions, so a sampled value can itself parameterise
the next draw — hierarchical models such as `ex_gaussian_walk`. There
are no witness braces: the kernel families behind them are total.

```coq
(* theories/programs/ppl.v *)
  | ne_gaussian (G : named_ctx Ar) :
      named_expr G tR' -> named_expr G tR' -> named_expr G tR'
  | ne_uniform (G : named_ctx Ar) :
      named_expr G tR' -> named_expr G tR' -> named_expr G tR'
```

The CBV clauses `eD_gaussian_E` and `eD_uniform_E`
(`theories/programs/ppl_cbv.v`) have the `ne_add` shape with the kernel
lift in place of the pushforward:
$\llbracket \text{Gaussian}(e_1,e_2) \rrbracket = \delta_\Gamma ; (\llbracket e_1 \rrbracket \otimes \llbracket e_2 \rrbracket) ; \text{kernel\_lift2 gaussian\_kernel}$.
The anchors live in `theories/programs/kernel_anchors.v`:
`eD_gaussian_at` and `eD_gaussian_dirac_E` (on point-mass arguments the
draw *is* the transported `normal_prob`, with the $s = 0$ Dirac fibre),
`eD_gaussian_mass` (the result's mass is the product of the argument
masses, since the kernel is a pointwise probability), and the
constant-parameter agreement `eD_gaussian_sample_agree`:
$\llbracket \text{Gaussian}([|m|],[|s|]) \rrbracket \gamma = \llbracket \text{sample (gaussian } m \text{ } s) \rrbracket \gamma$ for $s \neq 0$, the
two transports being identified by `pmeas_of_prob_fmeas`. The `Uniform`
mirror is `eD_uniform_at` / `eD_uniform_dirac_E` / `eD_uniform_mass` /
`eD_uniform_sample_agree`.

> These two constructors are what makes the language usable for
> hierarchical models, and they cost nothing in witnesses because
> totality is discharged once and for all in the kernel layer rather
> than at each call site. `eD_gaussian_sample_agree` is the
> compatibility statement with the older bundled-`sample` surface: at
> real literals the kernel surface and the fixed-measure surface
> denote the same thing.

### Parameterized kernels (`pkernel`, `kernel_lift`, `kernel_lift2`, `gaussian_kernel`, `uniform_kernel`)

A `pkernel X Y` bundles a family of sub-probability measures
`pk_ker : X → FMeas Y` with the mathcomp-analysis kernel condition
(`pk_meas`: $x \mapsto k(x)(U)$ is measurable for every measurable $U$) and
the unit-ball bound (`pk_ball`: each $k(x)$ has cone-norm — total mass —
at most $1$). Such a family *is* a measurable path
(`pkernel_is_path`, paper Def 3.7), so the Thm 6.1 machinery promotes it
to the semantic lift `kernel_lift k` : $\text{FMeas } X \multimap \text{FMeas } Y$,
$\nu \mapsto \int k(x) \, \nu(dx)$ (Pettis integral).

`pkernel` and the paper-side substochastic kernel `Skern_hom`
(theories/kernels/skern.v) are the *same* data in two packagings, and the
bridge `pkernel_to_Skern_hom` / `Skern_hom_to_pkernel` (mutually inverse by
`pkernel_to_Skern_homK` / `Skern_hom_to_pkernelK`) makes that official: the
forward direction is `kernel_path` plus `kernel_path_norm_le1`, the converse
reads `pk_meas` back off the path as `measurable_test_path_section` at the
test `fmeas_eU` and `pk_ball` as `path_norm_ub` composed with
`skern_norm_le1`. `kernel_lift` is then *defined* as the paper's Thm 6.5
embedding functor $K_{\mathrm{lin}}$
(theories/kernels/kernel_embedding.v::`Skern_to_ICones_mor`) evaluated at the
bridged kernel, so the PPL inherits the $\mathbf{Skern}$ category laws
(`Skern_compIl` / `Skern_compIr` / `Skern_compA`), $K_{\mathrm{lin}}$'s
functoriality (`Skern_to_ICones_mor_id` / `Skern_to_ICones_mor_comp`) and its
full faithfulness instead of re-deriving them. This is the only `Require`
edge from theories/programs/ into `Icones.kernels`. (`kernel_int_norm_le1`,
the operator-norm bound $\lVert I(k) \rVert \le 1$ on the Thm 6.1 promotion of
the kernel path, remains available as a standalone fact; the lift no longer
needs it, since the norm bound now travels inside the `Skern_hom`.)

```coq
(* theories/programs/distributions.v *)
Record pkernel : Type := MkPkernel {
  pk_ker : ar_carrier Ar X -> fmeas R (ar_carrier Ar Y);
  pk_meas : forall U : set (ar_carrier Ar Y),
    measurable U ->
    measurable_fun [set: ar_carrier Ar X]
      (fun x => fine (fmeas_mu (pk_ker x) U));
  pk_ball : forall x, (cone_norm (pk_ker x) <= 1)%R
}.

(* … *)
Definition pkernel_to_Skern_hom (k : pkernel) : Skern_hom Ar X Y :=
  MkSkernHom (kernel_path k) (kernel_path_norm_le1 k).

Definition Skern_hom_to_pkernel (κ : Skern_hom Ar X Y) : pkernel :=
  @MkPkernel (path_fun (skern_path κ))
    (fun U mU => Skern_hom_pk_meas κ mU) (Skern_hom_pk_ball κ).

(* … the lift IS the Thm 6.5 embedding functor at the bridged kernel *)
Definition kernel_lift (k : pkernel) :
    icones_hom Ar (FMeas X) (FMeas Y) :=
  Skern_to_ICones_mor (pkernel_to_Skern_hom k).

(* … *)
Definition kernel_lift2 :
    icones_hom Ar (tensor Ar (FMeas X) (FMeas Y)) (FMeas Z) :=
  icones_comp (kernel_lift k) (fmeas_lax X Y).
```

The computation laws are `kernel_lift_E`
($(\text{kernel\_lift } k \, \nu)(U) = \int k(x)(U) \, \nu(dx)$), `kernel_lift_mass`
(pointwise-mass-1 kernels preserve total mass) and `kernel_lift_dirac`
(`kernel_lift k` $\delta_x = k(x)$). Two-argument kernels go through
`kernel_lift2 k` := `kernel_lift k` $\circ$ `fmeas_lax` — the tensored argument
pair becomes a joint measure on the product object, exactly the
`add_lift` / `mul_lift` route — with `kernel_lift2_dirac` and the
product-mass law `kernel_lift2_mass`.

Both computation laws now come from the paper side: `kernel_liftE` is
`Skern_to_ICones_mor_E` at the bridged kernel, and `kernel_lift_dirac` is the
$\mathbf{Skern}$ right-unit law `Skern_compIr` read off at the point $x$.

The instances are `dirac_kernel` (`kernel_lift dirac_kernel = id`, by
`dirac_kernel_lift_id` — a corollary of $K_{\mathrm{lin}}(\delta_X) = \mathrm{id}$
via `pkernel_to_Skern_hom_dirac : pkernel_to_Skern_hom dirac_kernel = Skern_id Ar X`),
`gaussian_kernel` ($(m,s) \mapsto \text{normal\_prob } m \, s$
transported along the carrier cast) and `uniform_kernel`
($(a,b) \mapsto \text{uniform\_prob}$ for $a < b$, else $\delta_a$). Family measurability
*in the parameters* (`measurable_normal_prob_pair`,
`measurable_uniform_int_pair`) is proved by Fubini–Tonelli against
Lebesgue measure.

> The $s = 0$ convention is a deliberate divergence from
> mathcomp-analysis: `gaussian_kernel` overrides the $s = 0$ fibre to
> the Dirac $\delta_m$ — the degenerate weak limit of $N(m, s)$ as $s \to 0$ —
> because mathcomp-analysis' own `normal_prob m 0` is a junk
> uniform-$[0,1]$ placeholder (its `normal_pdf` falls back to
> `uniform_pdf 0 1` at $s = 0$), not a meaningful distribution; $s \neq 0$,
> including $s < 0$, keeps mathcomp's genuine normal with deviation
> $|s|$. Pointwise these two kernels are probabilities
> (`gaussian_kernel_norm1`), which is what makes `eD_gaussian_mass`
> multiplicative. The value-dependent boolean coin is *not* a kernel
> instance: it reaches the semantics through `bern_lift`
> (`theories/programs/ppl.v`), the same `int_to_linhom` /
> `linhom_icones` construction with the two-point boolean cone in place
> of `FMeas Y`.

### Recursion at function type (`ne_fix`)

OCaml-style `let rec`, restricted to function types: the body has access
to the recursive function via a fresh name `s : tfun t1 t2` pushed onto
the context, and the whole construct is again a value of type
`tfun t1 t2`.

```coq
(* theories/programs/ppl.v *)
  | ne_fix   (G : named_ctx Ar) (s : string) (t1 t2 : T) :
      named_expr ((s, tfun t1 t2) :: G) (tfun t1 t2) -> named_expr G (tfun t1 t2)
```

The CBV interpretation in `theories/programs/ppl_cbv.v` resolves
`ne_fix` (and `ne_fix_mr` at function body types) to the composite
`fix_comb` $\circ$ $\llbracket \lambda s.\text{body} \rrbracket$, where `fix_comb` is the seeded value-fixpoint
combinator of `theories/programs/infra/em_fix_value.v`.

> Restricting recursion to function types is the standard choice — it
> is what OCaml does, where `let rec` is thunked — and here it is also
> what makes the fixpoint constructible: a recursive value at a base
> type would have to be the supremum of a chain that degenerates to the
> cone zero. How `fix_comb` avoids that degeneracy is the subject of the
> recursion chapter.

### Mutual recursion and free-coalgebra types (`ne_fix_mr`, `is_free_coalg_type`)

`ne_fix_mr` generalises `ne_fix` to any body type `t` with
`is_free_coalg_type t = true` — the types whose CBV interpretation is a
*free* `!`-coalgebra, namely function types and products thereof. In
particular `t = tprod (tfun A1 B1) (tfun A2 B2)` is the mutual-recursion
shape, where the two components call each other via `fst #"s"` /
`snd #"s"`.

```coq
(* theories/programs/ppl.v *)
Fixpoint is_free_coalg_type (t : ppl_type Ar) : bool :=
  match t with
  | tfun _ _ => true
  | tprod t1 t2 => is_free_coalg_type t1 && is_free_coalg_type t2
  | _ => false
  end.

(* … Section Syntax … *)
  | ne_fix_mr (G : named_ctx Ar) (s : string) (t : T)
              (Hfree : is_free_coalg_type t) :
      named_expr ((s, t) :: G) t -> named_expr G t
```

The CBV interpretation in `theories/programs/ppl_cbv.v` dispatches
`ne_fix_mr` on the body type (`fix_mr_clause`): at `tfun t1 t2` it is
the *same* genuine seeded combinator `fix_comb` as `ne_fix`; at products
of free types it is the *same combinator transported along the Seely
decomposition* — `fix_mr_comb`, i.e. `fix_comb (free_base t)` conjugated
by the coalgebra iso `free_decomp : tyD_cbv t ≅ !̃(free_base t)`, whose
`tprod` step is the EM-level Seely-2 iso
`EM_prod (!̃X) (!̃Y) ≅ !̃(X & Y)` of
`theories/programs/infra/em_fix_mr.v`.

> The predicate is the gate that keeps the construction honest: it
> admits exactly the body types at which the transport exists, and it is
> decidable, so the constructor's witness `Hfree` is discharged by
> computation at every call site. The mutual-recursion fixpoint is
> genuine at *every* free body type — not a truncation — and the surface
> witness is `ex_even_odd_pair` in the Examples tab; the transport
> itself is built in the recursion chapter.

## Surface notation and variable lookup

Between the constructors of `named_expr` and the programs of
`theories/programs/examples.v` sit one inference mechanism and two notation
layers. The mechanism is a canonical-structure search that turns the string in
`#"x"` into a `named_var` witness, together with the context and the type that
witness is taken at. The layers are the kernel grammar — a custom entry
`ppl_named` giving each constructor a concrete syntax, entered by `[ … ]` and
escaped by `{ … }` — and the derived readable forms above it, which are sugar
and elaborate back into constructors. All of it lives in
`theories/programs/ppl.v`, and none of it adds semantics: every surface phrase
is already a `named_expr` before the CBV interpretation `eD` sees it.

| Construction | Statement | Rocq |
|---|---|---|
| Variable lookup by canonical structures | Writing `#"x"` resolves the named context, the type, and the `named_var` witness of the binding `"x"` in a single canonical-structure search. | `tagged_nctx`, `find_nv`, `ne_var'` — theories/programs/ppl.v |
| The kernel grammar | A custom grammar entry gives the constructors of `named_expr` an OCaml-flavoured direct-style concrete syntax, entered by `[ … ]` and left by `{ … }`. | `ppl_named` (custom entry) — theories/programs/ppl.v |
| Derived readable forms | The readable layer above the kernel grammar: notations that are sugar only, each elaborating to constructors that already exist. | `ne_meas` — theories/programs/ppl.v |

### Variable lookup by canonical structures (`tagged_nctx`, `find_nv`, `found_nv`, `recurse_nv`, `ne_var'`)

Writing `#"x"` makes Rocq's canonical-structure search find the named context,
the type, and the `named_var` witness of the binding `"x"` all at once — the
Saito–Affeldt APLAS 2023 §5.2 `find` structure, transplanted to `named_ctx` in
`theories/programs/ppl.v`. The search runs over a *tagged* context: `find_nv s t`
pairs a `tagged_nctx` with a proof that the string `s` is bound to type `t` in it,
and the two tags `found_nctx` (canonical) and `recurse_nctx` (fallback) order the
head case before the tail case.

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

(** The two tags: [found_nctx] (canonical) and [recurse_nctx] (fallback). *)
Definition recurse_nctx (R : realType) (Ar : MeasSubcat R)
    (G : named_ctx Ar) := Tag_nctx G.
Canonical found_nctx (R : realType) (Ar : MeasSubcat R)
    (G : named_ctx Ar) := recurse_nctx G.
```

The search is driven by two canonical instances over that tagged context:
`found_nv` (head case — the sought string is the head binding) is tried first;
otherwise the tag unfolds to `recurse_nctx` and `recurse_nv` recurses on the
tail, with the "different string" side-condition discharged by
`infer (String.eqb s y = false)` — a `vm_compute`-reducible boolean disequality
witness for the concrete strings occurring in programs.

```coq
(* theories/programs/ppl.v *)
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

> The structures and their instances are deliberately declared outside any
> `Section`, so that `R` and `Ar` are strict implicits on the structure itself
> and are inferred at every use site, matching the way Saito–Affeldt set up
> their `find` structure. `ne_var'` is the only entry point the surface needs:
> the `# x` notation of the kernel grammar elaborates to `ne_var' x _` and the
> search supplies the rest. The named layer exists for this lookup alone — the
> categorical interpretation runs on `drop_names G`, which forgets the strings.

### The kernel grammar (`ppl_named` custom entry)

A custom grammar entry `ppl_named` (opened by `Declare Custom Entry ppl_named`
in the source) gives the examples an OCaml-flavoured direct-style surface
syntax. Brackets `[ … ]` enter the entry, curly braces `{ x }` escape back to
plain Rocq, and the atoms are unit, variable lookup, real literals, and the
sampling primitive.

```coq
(* theories/programs/ppl.v — after [Declare Custom Entry ppl_named] *)
Notation "[ e ]" := e (e custom ppl_named at level 90).
Notation "{ x }" := x (in custom ppl_named at level 0, x constr).
Notation "( e )" := e (in custom ppl_named at level 0, e custom ppl_named).
Notation "()" := ne_tt (in custom ppl_named at level 0).
Notation "# x" :=
  (ne_var' x%string _)
  (in custom ppl_named at level 1, x constr at level 0).
Notation "[| r |]" := (ne_real r) (in custom ppl_named at level 1, r constr).
Notation "'Sample' ( mu , Hmu )" :=
  (ne_sample mu Hmu)
  (in custom ppl_named at level 1, mu constr, Hmu constr).
```

The remaining keywords map one-to-one onto the constructors of `named_expr`
(parsing annotations elided below): pairs and projections, application,
arithmetic, the boolean literals and `if`, the binders `\`, `let`, `fix`, and
`fix_mr`.

```coq
(* theories/programs/ppl.v — after [Declare Custom Entry ppl_named] *)
Notation "( e1 , e2 )" := (ne_pair e1 e2) (* … *).
Notation "'fst' e" := (ne_fst e) (* … *).
Notation "'snd' e" := (ne_snd e) (* … *).
Notation "M @ N" := (ne_app M N) (* … left associativity *).
Notation "M + N" := (ne_add M N) (* … *).
Notation "M * N" := (ne_mul M N) (* … *).
Notation "'True'" := ne_true (in custom ppl_named at level 0).
Notation "'False'" := ne_false (in custom ppl_named at level 0).
Notation "'if' e 'then' M 'else' N" := (ne_if _ e M N) (* … *).
Notation "'\' x ':::' A '=>' M" := (ne_lam x%string (t1 := A) M) (* … *).
Notation "'let' x ':=' M 'in' N" := (ne_let x%string M N) (* … *).
Notation "'fix' s ':::' 'tfun' A B 'in' M" :=
  (ne_fix s%string (t1 := A) (t2 := B) M) (* … *).
Notation "'fix_mr' s 'as' T 'by' Hfree 'in' M" :=
  (ne_fix_mr s%string T Hfree M) (* … *).
```

The constant coin `Bernoulli [| p |]` and the runtime-parameter distributions
`Gaussian( e1 , e2 )` / `Uniform( e1 , e2 )` are declared in the same entry and
are shown with their constructors `ne_bernoulli`, `ne_gaussian`, `ne_uniform`.
Direct-style: no `Ret` notation; `let "x" := M in N` desugars to `ne_let` (not
`ne_bind`).

> The grammar is where the direct-style choice becomes visible to the
> programmer: there is no `tprob` type marker, no `Ret`, no `bind` — the
> sequencing form is `ne_let`, and the probabilistic effect appears only in the
> CBV denotation `eD`. The escape `{ x }` is what keeps the entry small: the
> Coq-level witnesses a constructor needs (`Hmu` in `Sample ( mu , Hmu )`, `Hf`
> in `Meas { f , Hf } e`) are written as ambient Rocq terms instead of being
> given surface syntax of their own.

### Derived readable forms (`ne_meas`, the `sample` and `let rec` notations)

Above the kernel grammar sits a readable layer whose notations are sugar only:
each elaborates to constructors that already exist — plus the pushforward
primitive `ne_meas` — and no new semantics is introduced. Three of its forms are
language-level: measurable application `Meas { f , Hf } e`, bundled sampling
`sample m`, and the OCaml-style `let rec`, in an annotation-free and an
annotated variant.

```coq
(* theories/programs/ppl.v — the derived surface forms, the readable layer *)
Notation "'Meas' '{' f ',' Hf '}' e" :=
  (ne_meas f Hf e) (* … *).
Notation "'sample' m" :=
  (ne_sample (pm_meas m) (pm_ball m))
  (in custom ppl_named at level 1, m constr at level 0).
Notation "'let' 'rec' f x ':=' M 'in' K" :=
  (ne_let f%string (ne_fix f%string (ne_lam x%string M)) K) (* … *).
Notation "'let' 'rec' f x ':::' T1 '==>' T2 ':=' M 'in' K" :=
  (ne_let f%string
     (ne_fix f%string (t1 := T1) (t2 := T2) (ne_lam x%string (t1 := T1) M))
     K) (* … *).
```

`let rec f x := M in K` is `ne_let f (ne_fix f (ne_lam x M)) K` — a recursive
function immediately let-bound under the same name — with binder types inferred
from the body; the annotated form `let rec f x ::: T1 ==> T2 := M in K` pins them
for bodies that leave them undetermined. `sample m` takes a bundled
sub-probability `m : pmeas` and unpacks it into the two arguments of
`ne_sample` (`pm_meas m` and `pm_ball m`) that the unbundled
`Sample ( mu , Hmu )` form asks the user to supply. The rest of the readable
layer is the probability surface — the `tProb` wrappers `Bernoulli`, `Score`,
`Sigmoid`, `Gausslik`, `Gt0`, `test`, `Const`, `InclP`, the `observe` operator,
and the comparison coin `e1 > e2` — described in the chapter on `tProb` and
`observe`.

> Keeping this layer sugar means the interpreter has one case per constructor and
> none per surface form: `eD` never meets a `let rec` or a `sample`. The price is
> grammar discipline — every keyword must parse disjointly from the others, which
> is why the constant coin carries a bracketed literal, `Bernoulli [| p |]`, that
> keeps it apart from the value-dependent coin `Bernoulli e` of the probability
> surface.

## The probability surface: tProb and observe

Coins, scores and observations all traffic in numbers that must lie in
$[0,1]$. Rather than attach that side condition to each use site, the
surface carries it in a **type**: a bundle `probObj` packages the
$[0,1]$ sub-object of the ambient measurable-space category, and
`tProb P` is the surface type of its elements. Every form in this
chapter — the coins and scores, the density primitives, the abstract
test-function coin, the bundled constants, and the general `observe`
operator — is a witness-free wrapper that pushes a measurable $[0,1]$
map through the bundle's universal factoring `po_into`. Two closed demo
programs then show the surface as a user actually writes it, and the
chapter closes with the reason the discipline is not negotiable: in a
sub-probability model a score is a morphism of the category exactly
when its density is bounded by `1`.

| Construction | Statement | Rocq |
|---|---|---|
| The probability object bundle | The $[0,1]$ sub-object interface `probObj` and the surface type `tProb P := tbase (po_obj P)`, whose values are $[0,1]$-supported | `probObj`, `po_into`, `tProb` — theories/programs/ppl.v |
| Coins and scores | `Bernoulli e` flips with the probability read off a `tProb` value; `Score e` weighs the trace by it; the literal coin takes a bare real | `pbern`, `pscore`, `ne_bernoulli` — theories/programs/ppl.v |
| Sigmoid and Gaussian likelihood | The two named $[0,1]$ maps that turn a real expression into a `tProb` value: the logistic map and the peak-normalised Gaussian density | `psigmoid`, `pgausslik`, `gauss_obs_density` — theories/programs/ppl.v |
| Strict positivity and the comparison coin | The indicator $\mathbb{1}_{(0,\infty)}$ as a `tProb`-producing primitive, and the comparison coin built on the sign of a difference | `pgt0`, `gt0_ind`, `negr` — theories/programs/ppl.v |
| Test functions | The bundled measurable $[0,1]$-valued test function `testfn` and the abstract coin `test f e` that evaluates it at a runtime value | `testfn`, `ptest`, `ex_reject` — theories/programs/ppl.v; theories/programs/examples.v |
| Constants, bundled measures, and inclusion | The constant-probability map, the bundled sub-probability behind `sample m`, and the forgetful read of a `tProb` value back to the line | `pconst`, `pmeas`, `pincl` — theories/programs/ppl.v |
| The observe operator | `pobserve D y` scores a distribution's runtime parameter by its peak-normalised density at the observed datum `y`; `obsGaussian` is the first instance | `pobserve`, `obsGaussian`, `observe_gauss_E` — theories/programs/ppl.v; theories/programs/ppl_cbv.v |
| The surface in use: recursive bindings and the demos | Two closed programs exercising `let rec`, `sample`, the comparison coin and the unified coin/score forms, with elaboration pins | `ex_surface_demo`, `ex_surface_walk` — theories/programs/examples.v |
| Scores, densities, and the sub-probability boundary | Every morphism is non-expansive, so a score is expressible exactly when its density is bounded: the line is bounded vs unbounded, not discrete vs continuous | `score_lift`, `cones_hom_norm_le1` — theories/programs/ppl.v; theories/cones/cone_cat.v |

### The probability object bundle (`probObj`, `po_obj`, `po_incl`, `po_into`, `po_density`, `tProb`)

The $[0,1]$ discipline of coins and scores is carried by a type. A
single bundle `probObj` packages the $[0,1]$ sub-object the surface
needs: a distinguished object `po_obj` together with its inclusion
`po_incl : po_obj → R_obj`, the two $[0,1]$ bounds on the inclusion,
and the universal factoring `po_into` of any measurable $[0,1]$ map
`h : R → R` through the inclusion ($h = \iota \circ$ `po_into` $h$, the computation
law `po_into_E`). The probability type is `tProb P := tbase (po_obj P)`:
a value of type `tProb P` is a $[0,1]$-supported measure, and a coin or
score over it integrates the inclusion $\iota$ — the mean of the supported
measure.

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
Definition po_density (P : probObj Ar) (x : ar_carrier Ar (po_obj P)) : R :=
  carrier_to_R (po_robj_eq P) (po_incl P x).
```

`tProb` is kept **folded** — a `Definition`, not a `Notation` — so that a
constructor wrapper meeting an `e : tProb P` recovers `P` by plain
first-order unification of `tProb ?P` against the folded type; the
sibling `tProb_robj P := tbase (po_robj P)` folds the bundle's real
object the same way and is the domain of the `tProb`-producing
primitives. Beyond the factoring, the bundle exposes the carrier density
`po_density P : po_obj P → R` — the inclusion read into `R`, the
success-probability / weight a coin or score over `tProb P` uses — and
the two lifts `bern_lift_P` / `score_lift_P` at the base object
`po_obj`.

> The surface forms are witness-free: the bounds travel with the type,
> never as loose proof obligations. Every wrapper in this chapter (`pbern`,
> `pscore`, `psigmoid`, `pgausslik`, `pgt0`, `pconst`, `ptest`, `pincl`,
> `pobserve`) feeds a $[0,1]$ map into `po_into` and hands back a
> `tProb P` expression, so `po_into` never appears at a use site.
> `bern_lift_P` and `score_lift_P` are the interpretation-side
> counterparts, taken at the base object `po_obj` rather than at the
> real object; they are used by the CBV interpreter.

### Coins and scores (`pbern`, `pscore`, `ne_bernoulli`)

Two forms consume a `tProb P` value. The coin `Bernoulli e` flips with
the success probability carried by `e`; the score `Score e` weighs the
trace by it. Both read the number through the bundle density
`po_density P`, and both infer `P` from the type of `e`. A third,
constant form `Bernoulli [| p |]` takes a bare real literal instead of a
`tProb` expression.

```coq
(* theories/programs/ppl.v — Section ProbSurfaceWrappers *)
(** Value-dependent [tProb]-coin: [P] inferred from [e : tProb P]. *)
Definition pbern (e : nexpr (tProb P)) : nexpr tbool :=
  ne_bernoulli_p (po_density P) (po_density_meas P) (po_ge0 P) (po_le1 P) e.

(** Term-level score by the bundle density: [P] inferred from [e]. *)
Definition pscore (e : nexpr (tProb P)) : nexpr tunit :=
  ne_score_p (po_density P) (po_density_meas P) (po_ge0 P) (po_le1 P) e.

Notation "'Bernoulli' e" := (pbern e)  (* … *).
Notation "'Score' e"     := (pscore e) (* … *).

Notation "'Bernoulli' '[|' p '|]'" :=
  (ne_bernoulli p ltac:(prob_lit_bound) ltac:(prob_lit_bound))
  (in custom ppl_named at level 1, p constr at level 0).
```

`pbern` and `pscore` are the `tProb` instances of the constructors
`ne_bernoulli_p` and `ne_score_p`, taken at the bundle's own density and
its two bounds, so nothing is supplied at a use site: the bundle `P` is
inferred from `e`'s type, as in `Bernoulli (Sigmoid #"x")` or
`Score (Gausslik e { 1 / 2 , y })`. The constant coin
`Bernoulli [| p |]` is instead the constructor `ne_bernoulli` at a bare
real `p : R`, with the two bounds `0 <= p` and `p <= 1` discharged on
the spot by the `prob_lit_bound` tactic — no bundle, no loose witness,
so the fair coin is `Bernoulli [| (1/2 : R) |]`. For a probability that
is not a literal, the sibling `BernoulliC p` takes a bundled `prob`
record.

> The unification story is the whole design. Because `tProb` is folded
> and because `psigmoid` / `pgausslik` / `pgt0` / `pconst` / `ptest` all
> *return* `tProb P`, a nested `Bernoulli (Sigmoid #"x")` threads one
> `?P` top-down and the bundle is never written. `pscore` is also what
> `pobserve` reuses: an observation is a score by a normalised density.

### Sigmoid and Gaussian likelihood (`psigmoid`, `sigmoid`, `pgausslik`, `gauss_obs_density`)

Two named $[0,1]$ maps turn a real-valued expression into a `tProb`
value. `Sigmoid e` pushes the runtime value of `e` through the logistic
map `sigmoid` (`sigmoid x` is `expR x / (1 + expR x)`);
`Gausslik e { s , y }` pushes it through the
envelope-normalised Gaussian likelihood `gauss_obs_density s y`, reading
the mean expression first and then the meta-level `{ stddev , datum }`
braces.

```coq
(* theories/programs/ppl.v *)
Definition sigmoid (x : R) : R := expR x / (1 + expR x).

Definition gauss_obs_density (s y : R) : R -> R :=
  fun mu => normal_pdf mu s y / normal_peak s.

(* … Section ProbSurfaceWrappers … *)
Definition psigmoid (e : nexpr (tProb_robj P)) : nexpr (tProb P) :=
  ne_to_prob (po_into P sigmoid measurable_sigmoid sigmoid_ge0 sigmoid_le1) e.

Definition pgausslik (s y : R) (e : nexpr (tProb_robj P)) : nexpr (tProb P) :=
  ne_to_prob (po_into P (gauss_obs_density s y) (gauss_obs_density_meas s y)
                (gauss_obs_density_ge0 s y) (gauss_obs_density_le1 s y)) e.
```

Each is built once, in `ppl.v`, by feeding the underlying $[0,1]$ map —
whose measurability and bounds already exist — into the bundle factoring
`po_into`; the result is a `ne_to_prob` node of type `tProb P`, and the
use site never sees `po_into`. `gauss_obs_density s y mu` is
`normal_pdf mu s y / normal_peak s`: dividing by the distribution's
intrinsic peak is what makes the likelihood a legal $[0,1]$ weight. At
`s = 0` the family is degenerate (`normal_peak 0 = 0`) and the ratio is
`0`, the Dirac convention shared with `gaussian_kernel`.

> The pattern generalises: a new `tProb`-producing primitive is one
> $[0,1]$ map plus its three witnesses, handed to `po_into`. `Gausslik`
> is the primitive `observe` is built on — `pobserve (obsGaussian e s) y`
> and `pscore (pgausslik s y e)` are the same term. Why peak
> normalisation is a necessity rather than a convenience is the subject
> of the last entry of this chapter.

### Strict positivity and the comparison coin (`pgt0`, `gt0_ind`, `negr`)

`Gt0 e` pushes a real value through the strict-positivity indicator
`gt0_ind = `$\mathbb{1}_{(0,\infty)}$, landing in `tProb`. It is the primitive behind the
comparison coin `>`: the derived form `e1 > e2` reads
`Bernoulli (Gt0 (e1 + Meas { negr , negr_meas } e2))`, flipping on the
sign of the difference.

```coq
(* theories/programs/ppl.v *)
(** Negation. *)
Definition negr (r : R) : R := - r.

Lemma negr_meas : measurable_fun [set: R] negr.
Proof. exact: measurable_funN. Qed.

(** The strict-positivity indicator [\1_(0, ∞)]. *)
Definition gt0_ind (r : R) : R := \1_([set x : R | 0 < x]) r.

(* … Section ProbSurfaceWrappers … *)
Definition pgt0 (e : nexpr (tProb_robj P)) : nexpr (tProb P) :=
  ne_to_prob (po_into P gt0_ind gt0_ind_meas gt0_ind_ge0 gt0_ind_le1) e.
```

On point masses the comparison coin is the deterministic test
`a > b`; on diffuse arguments it flips with the probability that an
independent draw of `e1` exceeds one of `e2`. `negr` is the negation map
and enters only through the `Meas` pushforward, to form the difference:
`ex_surface_demo` writes the coin out in full as
`Bernoulli (Gt0 (# "m" + Meas {negr, negr_meas} [| 0%R |]))`.

> `Gt0` replaced an earlier meta-level density notation: the indicator is
> now pushed through `po_into` like any other $[0,1]$ map, so the coin
> carries no loose witness and needs no clamp. Both surface demos,
> `ex_surface_demo` and `ex_surface_walk`, exercise it.

### Test functions (`testfn`, `test_fun`, `test`, `ptest`)

`test f e` is the abstract test-function coin. Here `f : testfn` is a
measurable $[0,1]$-valued **test function** — a map you integrate
measures *against*, with $\int f \, d\mu$ the test pairing that is literally the
content of the score-posterior and rejection headline theorems
($\int f \, d\mu \cdot \nu(U) = \int_U f \, d\mu$, `ex_reject_master`). `test f e` evaluates
the test at the runtime value of `e`, landing in `tProb`: the
object-language counterpart of the integration pairing.

```coq
(* theories/programs/ppl.v *)
Record testfn := MkTestfn {
  test_fun : R -> R ;
  test_meas : measurable_fun [set: R] test_fun ;
  test_ge0 : forall r : R, (0 <= test_fun r)%R ;
  test_le1 : forall r : R, (test_fun r <= 1)%R
}.

(** A test function is applied as a plain function via its carrier map. *)
Coercion test_fun : testfn >-> Funclass.

(* … Section ProbSurfaceWrappers … *)
Definition ptest (d : testfn R) (e : nexpr (tProb_robj P)) : nexpr (tProb P) :=
  ne_to_prob (po_into P (test_fun d) (test_meas d) (test_ge0 d) (test_le1 d)) e.
```

The `testfn` record bundles the carrier map `test_fun` with its
measurability and $0 \leq f \leq 1$ witnesses (`test_meas` / `test_ge0` /
`test_le1`) and **coerces to its function**
(`Coercion test_fun : testfn >-> Funclass`), so `f r` and $\int f \, d\mu$ read
directly; all projections are primitive, so
`test_fun (mk_testfn f _ _ _) = f` holds definitionally. `ptest` folds
`po_into (test_fun f)` into one witness-free wrapper, making `test f`
the `testfn`-parameterised sibling of `Sigmoid` / `Gausslik`: a use site
reads `Bernoulli (test f #"x")` or `Score (test f #"m")`. Test functions
are the *soft*, score-based side of conditioning: `Score (test f #"x")`
is the score posterior `ex_score_posterior`
(`theories/programs/examples.v`, analysed in
`theories/programs/cbv_marginals.v`), and `ex_reject`
(`theories/programs/examples.v`, analysed in
`theories/programs/ex_reject_headline.v`) accepts through the coin
`Bernoulli (test f #"x")`. The `reject` / `condition`
combinators take a different acceptance test — a boolean program
predicate `f : tb → tbool` applied by ordinary application
(`ne_condition`, `theories/programs/reject_condition.v`).

> Contrast `observe Gaussian e { s } y`, the special case where the test
> comes from a concrete distribution's peak-normalised density. The
> score-posterior and rejection theorems quantify over an *arbitrary*
> test `f`, which is exactly why the abstract `test f` form exists; see
> the [Examples tab](../../examples/index.html) for `ex_reject` and its
> normalised posterior.

### Constants, bundled measures, and inclusion (`pconst`, `prob`, `pmeas`, `prob_pmeas`, `pincl`)

Three surface forms carry bundled data rather than a computed density.
`Const` is the constant-literal `tProb`-map: `Const pr e` takes a
bundled probability `pr : prob`. `sample m` draws from a bundled
sub-probability `m : pmeas`. `InclP` runs the other way: `InclP e` is
the forgetful read of a `tProb P` value back to the line along the
inclusion $\iota$.

```coq
(* theories/programs/ppl.v *)
Record prob := MkProb {
  pr_val : R ;
  pr_ge0 : (0 <= pr_val)%R ;
  pr_le1 : (pr_val <= 1)%R
}.

Record pmeas : Type := MkPmeas {
  pm_meas : fmeas R (ar_carrier Ar R_obj);
  pm_ball : (cone_norm pm_meas <= 1)%R
}.

(** The bundled sub-probability. *)
Definition prob_pmeas : pmeas Ar R_obj := MkPmeas prob_fmeas prob_fmeas_ball.

(* … Section ProbSurfaceWrappers … *)
Definition pconst (pr : prob R) (e : nexpr (tProb_robj P)) : nexpr (tProb P) :=
  ne_to_prob (po_into P (cst (pr_val pr)) (measurable_cst (pr_val pr))
                (fun=> pr_ge0 pr) (fun=> pr_le1 pr)) e.

(** Forgetful read of a [tProb] value back to the line along [ι]. *)
Definition pincl (e : nexpr (tProb P)) : nexpr (tProb_robj P) :=
  ne_incl (po_incl P) e.
```

`prob` bundles a constant $[0,1]$ scalar with its two bounds, and
`pconst pr` feeds the constant map `cst (pr_val pr)` to `po_into`, so
`Bernoulli (Const pr [| 0 |])` is the constant value-coin used by the
parameterised `ex_almost_loop`. `pmeas` bundles a finite measure with
its unit-ball witness `pm_ball` (its total mass is at most `1`), which is
what lets `sample m` take a single argument; `prob_pmeas` transports any mathcomp-analysis
probability on `R` to a `pmeas`, giving the named distributions
`gaussian m s` and `uniform a b` of `theories/programs/examples.v`, as
in `let "m" := sample gaussian01 in …`. `pincl` is the constructor
`ne_incl` at `po_incl P`, landing in `tProb_robj P` — the real-line type
`tR` at the bundle's real object.

> The three share one habit: the proof obligation is packed into the
> argument, not left at the call. `prob` and `pmeas` are the *data*
> bundles (a scalar with its bounds, a measure with its mass bound) where
> `probObj` is the *object* bundle; `pincl` is the only form in the
> chapter that leaves `tProb`, and it is the inclusion $\iota$ itself read as
> a term constructor.

### The observe operator (`pobserve`, `obsDist`, `obsGaussian`, `od_arg`, `od_dens`, `observe_gauss_E`)

`observe` is a general conditioning **operator**, not a
Gaussian-specific notation. `pobserve D y` takes a
distribution-with-density record `D : obsDist` and an observed datum
`y : R`, and scores the trace by `od_dens D y` at the runtime parameter
`od_arg D`. The surface reads `observe Gaussian e { s } y`: mean
expression first, then the standard deviation in braces, then the
trailing observed point.

```coq
(* theories/programs/ppl.v — Section ObserveOperator *)
Record obsDist := MkObsDist {
  od_arg  : nexpr (tProb_robj P) ;        (* runtime parameter (e.g. mean) *)
  od_dens : R -> R -> R ;                  (* [od_dens point param] ∈ [0,1] *)
  od_meas : forall y, measurable_fun [set: R] (od_dens y) ;
  od_ge0  : forall y r, (0 <= od_dens y r)%R ;
  od_le1  : forall y r, (od_dens y r <= 1)%R ;
}.

Definition pobserve (D : obsDist) (y : R) : nexpr tunit :=
  pscore (ne_to_prob (po_into P (od_dens D y) (od_meas D y)
                        (od_ge0 D y) (od_le1 D y)) (od_arg D)).

Definition obsGaussian (e : nexpr (tProb_robj P)) (s : R) : obsDist :=
  {| od_arg  := e;
     od_dens := gauss_obs_density s;
     od_meas := gauss_obs_density_meas s;
     od_ge0  := fun y r => gauss_obs_density_ge0 s y r;
     od_le1  := fun y r => gauss_obs_density_le1 s y r |}.

Notation "'observe' 'Gaussian' e '{' s '}' y" :=
  (pobserve (obsGaussian e s) y) (* … *).
```

`od_arg` is the runtime parameter — the predicted mean — and
`od_dens point param` the family of $[0,1]$-valued densities, carried
with their measurability and bound witnesses `od_meas` / `od_ge0` /
`od_le1`. `obsGaussian e s` is the first instance (`od_arg := e`,
`od_dens := gauss_obs_density s`), so
`pobserve (obsGaussian e s) y = pscore (pgausslik s y e)` holds
definitionally, recorded as `pobserve_obsGaussian`. What this expresses
is Bayesian conditioning: score the trace by the likelihood of `y` under
$N(\text{value}(e), s)$, normalised by the distribution's intrinsic peak
`normal_peak s` so that the weight is a legal $[0,1]$ density — no
user-supplied envelope. The denotation lemma is `observe_gauss_E`
(`theories/programs/ppl_cbv.v`): at a setlike Dirac environment
(*setlike*: `coalg_str` $\gamma = \gamma!$, i.e. the environment is a
(sub-)Dirac rather than a mixture) the
trace is weighted by $\text{normal\_pdf}\, \mu\, s\, y / \text{normal\_peak}\, s$ at the runtime
mean $\mu$.

> Adding another observable distribution is a new `obsDist` instance plus
> a one-line sugar; `pobserve`, and the `pscore` it reuses, stay fixed.
> The brace group in the surface form also keeps the grammar disjoint
> from the sampling primitive `ne_gaussian`'s `Gaussian ( e1 , e2 )`:
> observing and sampling a Gaussian are different operators and read
> differently.

### The surface in use: recursive bindings and the demos (`ex_surface_demo`, `ex_surface_walk`, `ex_surface_demo_decomp`)

The forms of this chapter are exercised end to end by two closed
programs. `ex_surface_demo` combines the annotated `let rec`, a
`sample` of a bundled distribution, and the comparison coin;
`ex_surface_walk` uses the annotation-free `let rec` and the unified
`Bernoulli` / `Score` forms. Concretely, `ex_surface_walk` reads
`walk x = let b = Bernoulli (Gt0 x) in let _ = Score (Gt0 x) in if b then x else walk (x * 1/2)`,
run as `walk 1`, where `Gt0 x` is the strict-positivity indicator
$\mathbb{1}_{x > 0}$. Both recursive bindings are the derived
`let rec` sugar over `ne_fix` introduced in the surface-notation
chapter.

```coq
(* theories/programs/examples.v — Section SurfaceDemo *)
Definition ex_surface_demo : @named_expr R Ar (po_robj P) nil tbool :=
  [ let rec "model" "x" ::: tunit ==> tbool :=
      (let "m" := sample gaussian01 in
       if Bernoulli (Gt0 (# "m" + Meas {negr, negr_meas} [| 0%R |]))
       then True else False)
    in # "model" @ () ].

Definition ex_surface_walk : @named_expr R Ar (po_robj P) nil tR' :=
  [ let rec "walk" "x" :=
      (let "b" := Bernoulli (Gt0 # "x") in
       let "_" := Score (Gt0 # "x") in
       if # "b" then # "x" else # "walk" @ # "x" * [| 1 / 2 |])
    in # "walk" @ [| 1 |] ].
```

`ex_surface_demo` needs the annotated variant because its binder `"x"`
is unused, so the body leaves the binder type undetermined;
`ex_surface_walk` does not. The elaborations are pinned by
`ex_surface_demo_decomp`, and the compile-time CBV denotations by
`ex_surface_demo_cbv` and `ex_surface_walk_cbv`.

> These two programs are the readable layer's regression test: they are
> written exactly as a user would write them, and `ex_surface_demo_decomp`
> is a `by []` proof that the sugar is the constructor term it claims to
> be. The recursive call in `ex_surface_walk` is also the surface entry
> point into the value fixpoint `fix_comb` of the recursion chapter.

### Scores, densities, and the sub-probability boundary (`cones_hom_norm_le1`, `score_lift`)

This is a sub-probability model, and that fixes exactly which scores it
can express. Every morphism of `ICone` is non-expansive: the
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
$\mu$ to $f \cdot \mu$, of mass $\int f \, d\mu$. As a morphism its operator norm is
$\sup f$, so `score_lift f` is a map of the category — and `ne_score f`
is well-typed — exactly when `f` is bounded by `1`. That is the source
of the `forall r, f r <= 1` witness on `ne_score` and `ne_bernoulli_f`:
not a modelling convenience but the condition for the score to be a
morphism at all.

The distinction that matters in practice is between *sampling* and
*observing*. Sampling is always fine: `sample (gaussian m s)` denotes a
probability measure of mass $1$, a good morphism for every `m` and `s`.
Observing — scoring by a density, `observe Gaussian e {s} y` weighing
the trace by the Gaussian likelihood of `y` — is the constrained
operation, a morphism only while the weight stays in $[0,1]$. The line
that matters is **bounded vs unbounded**.

A **bounded** likelihood is always conditionable, and `observe` does
exactly this. $N(\mu, \sigma)$ peaks at its intrinsic peak
`normal_peak` $\sigma = 1/(\sigma\sqrt{2\pi})$; the *unnormalised* pdf crosses $1$ as soon
as $\sigma < 1/\sqrt{2\pi} \approx 0.399$, so it is not directly a $[0,1]$ weight. But
the peak is a finite bound, and dividing by it gives the legal weight
`gauss_obs_density` $\sigma\, y = \text{normal\_pdf}\, \mu\, \sigma\, y / \text{normal\_peak}\, \sigma \in [0,1]$ — a
map into the $[0,1]$ object `po_obj P`, factored through the bundle
inclusion by `po_into`. This is exactly what `Gausslik e { σ , y }`,
hence `observe`, scores by. The normaliser cancels in the posterior: the
conditioned distribution $\int_U f \, d\nu / \int f \, d\nu$ is independent of any
positive scaling of `f`, so dividing by `normal_peak σ` changes the
total evidence but never the posterior. The same holds for the
conditioning/rejection pair, where dividing by the peak is classical
rejection sampling with that envelope.

Only a **genuinely unbounded** family is out of scope. When a density
has no finite peak — a Gaussian with `σ` free to approach `0`, a
likelihood that can be arbitrarily sharp — no normalisation brings it
inside the unit ball, and the observation is not a morphism of `ICone`
and has no denotation here. This is a property of every sub-probability
model, integrable cones and probabilistic coherence spaces alike, not of
the encoding.

The semantics designed to score by arbitrary unbounded weights is the
*s-finite kernel* model (Staton and collaborators): it drops the norm
bound and lets `score w` denote a measure of any finite mass. The cone
model makes the opposite trade — it keeps the sub-probability discipline
and, in return, carries the higher-order and analytic structure (the `!`
comonad, the Seely and Eilenberg–Moore development) that the kernel
model does not. An `observe` with an unbounded density is the price of
that structure.

> Read backwards, this entry explains the rest of the chapter:
> `cones_hom_norm_le1` is the field that must be discharged for every
> score, and `po_into` is the single place in the surface where a
> $[0,1]$ bound is ever checked. Every witness-free form of this chapter exists so
> that the check happens once, in `ppl.v`, instead of at each use site.

## Call-by-value semantics

**Definition (CBV interpretation).** *Each type $\tau$ denotes a
`!`-coalgebra $\llbracket \tau \rrbracket \in EM(!)$; each well-typed program $\Gamma \vdash M : \tau$
denotes a linear morphism $\llbracket M \rrbracket : U\llbracket \Gamma \rrbracket \multimap U\llbracket \tau \rrbracket$ in `ICone` — an
element of `linhom_car Ar (coalg_obj` $\llbracket \Gamma \rrbracket$`) (coalg_obj` $\llbracket \tau \rrbracket$`). Programs
are not coalgebra morphisms (the sampling clause does not commute
with the §9.7 duplicability structure on `FMeas`); the coalgebra
structure of the context is used only through the comonoid pair
$(\delta, \varepsilon)$ = `(coalg_d, coalg_e)` that every EM(!) object carries by
Melliès' Proposition 28.*

In Rocq this is the function `eD` of `theories/programs/ppl_cbv.v`,
sending a term `M : named_expr` $\Gamma$ $\tau$ to an element of
`linhom_car Ar (coalg_obj (ctxD_cbv (drop_names` $\Gamma$`)))
(coalg_obj (tyD_cbv` $\tau$`))`, defined by structural recursion on
`named_expr`. Internally it is built from an `icones_hom`-valued
helper `eD_cbv` (an inhabitant of the unit ball of the same
`linhom`) and forwarded to a linhom by `icones_to_linhom`; the two
views are interchangeable. There is no Kleisli wrapping on the
codomain of `tfun`: function *values* are linear maps
$U\llbracket t_1 \rrbracket \multimap U\llbracket t_2 \rrbracket$, and duplicability comes from the outer cofree `!̃`
only.

Why *this* interpretation, and why it is a chapter of its own. The
paper's model is a Seely category — the linear-logic exponential `!`
of paper §9 — and a Seely category admits two standard routes from
linear morphisms to a language semantics: the **co-Kleisli** category
of `!`, which gives **call-by-name**, and the **Eilenberg–Moore**
category of `!`-coalgebras, which gives **call-by-value**
(Melliès, *Categorical Semantics of Linear Logic*, §7.4). The
co-Kleisli side is the paper's own §7: the cartesian closed `SCones`
of stable maps, documented on the [Paper tab](../paper/), and it is
the side the `cbn-track` branch interprets. This chapter takes the
other one. That is what makes every type here denote a
`!`-coalgebra rather than a plain cone, why the context comonoid
$(\delta, \varepsilon) = ($`coalg_d`, `coalg_e`$)$ is the primitive every clause
branches on, and why recursion needs a *value* fixpoint in $EM(!)$
rather than the `SCones` operator `Yfix` (which nevertheless supplies
its analytic core — see the recursion chapter). Neither call-by-value
nor call-by-push-value is carried out in the paper itself; the paper
names them, in its abstract, as the languages its integration theory
is built to reach.

The chapter is ordered as the construction is built. It opens with
the semantic target — the EM cartesian toolbox every clause branches
on — then gives the type and context translations, the interpreter
itself clause by clause, the constant and lifted helpers its value
and effect clauses call, and finally the regression pack that pins
each clause definitionally. The semantic laws *about* the
interpreter — the recursion-unfolding equations `eD_fix_at_setlike`
and `eD_fix_unfold`, the let-at-sample integral law, and the
sharing-semantics anchors — live in the recursion chapter and in the
semantic-laws chapter.

| Construction | Statement | Rocq |
|---|---|---|
| The semantic target: EM cartesian structure | Every `!`-coalgebra carries a commutative comonoid $(\delta, \varepsilon)$, and these comonoids make $(EM(!), \otimes, 1)$ cartesian: pairing, projections and the terminal morphism are definable from $(\delta, \varepsilon)$ alone. | `coalg_d`, `coalg_e`, `em_pair_mor` — theories/cbv/em_cartesian.v; theories/cbv/cbv_adjunction.v |
| Type translation | Each surface type denotes a `!`-coalgebra; the function type denotes the cofree coalgebra on the clean internal hom, with no `Tobj` wrap anywhere. | `tyD_cbv` — theories/programs/ppl_cbv.v |
| Context translation | A context denotes the right-nested iterated EM product of its types' coalgebras, and variable lookup is the evident chain of projections. | `ctxD_cbv`, `var_lookup_cbv` — theories/programs/ppl_cbv.v |
| Term interpretation | The denotation of a term, by structural recursion on `named_expr`: uniformly comonoid-primitive, `icones_hom`-valued internally and linhom-valued in public. | `eD_cbv`, `eD` — theories/programs/ppl_cbv.v |
| Constant icones helpers | Each value or sampling constructor denotes a constant morphism out of the context: the counit discards the context, then the constant value is injected. | `sample_icones`, `real_icones`, `bernoulli_icones` — theories/programs/ppl_cbv.v |
| The value-dependent Bernoulli lift | The semantics of `ne_bernoulli_f`: a measure $\mu$ on the reals is sent to the 2-point sub-probability $(\int f \, d\mu, \int (1 - f) \, d\mu)$. | `bern_lift`, `bern_lift_mass`, `bern_lift_P` — theories/programs/ppl.v |
| If-then-else at the icones level | The CBV value-level conditional: two branches and a scrutinee into the 2-point cone, co-paired and evaluated with no Kleisli wrapping at any step. | `if_icones`, `if_under` — theories/programs/ppl_cbv.v (Section IfICones) |
| The definitional-unfolding pack | One `by []` lemma per interpreter clause, pinning the exact clause body so a refactor breaks loudly in a named lemma instead of silently changing the semantics. | `eD_var_E`, `eD_let_E`, `eD_fix_mr_prod_E` — theories/programs/ppl_cbv.v (Section EDUnfold) |

> **Paper — Abstract** (arXiv 2212.02371 / LMCS **21**(1:1) 2025).
> Measurable cones, with linear and measurable functions as morphisms,
> are a model of intuitionistic linear logic and of call-by-name
> probabilistic PCF which accommodates 'continuous data types' such as
> the real line. So far however, they lacked a major feature to make
> them a model of more general probabilistic programming languages
> (notably call-by-value and call-by-push-value languages): a theory of
> integration for functions whose codomain is a cone, which is the key
> ingredient for interpreting the sampling programming primitives.

> **Difference.** The paper stops at the model: it builds the
> integration theory and the two exponentials, and leaves the
> call-by-value / call-by-push-value languages its abstract names as
> future work. This chapter takes the Eilenberg–Moore step and
> interprets a call-by-value language, on top of the axiom-free Seely
> category of paper §9 — so nothing here is filed as a paper-§ result,
> and the whole chapter is *beyond the paper* in the sense the
> [Paper tab](../paper/)'s "Beyond the paper" chapter uses. There is no
> call-by-push-value layer: no adjunction splitting values from
> computations is formalised, and no Moggi metalanguage — both are
> recorded in this document's "What is **not** formalised" chapter.

### The semantic target: EM cartesian structure (`coalg_d`, `coalg_e`, `em_pair_mor`, `em_proj1_mor`, `em_proj2_mor`, `em_term_mor`)

Every `!`-coalgebra carries a commutative comonoid $(\delta, \varepsilon) =
(\text{coalg\_d}, \text{coalg\_e})$ transported from the Seely comonoid on its
cofree resolution, and these comonoids make $(EM(!), \otimes, 1)$
cartesian — pairing, projections and the terminal morphism are all
definable from $(\delta, \varepsilon)$ alone. This is the entire toolbox the CBV
interpreter branches on.

The constructions live in `theories/cbv/em_cartesian.v` (Melliès
§7.4 Prop 28 / Cor 20 — see the Paper-tab pages [EM(!) is fully
cartesian](../../paper/beyond/beyond-em.html) and [Cartesian-η of
EM(!)](../../paper/beyond/beyond-cartesian-of-em.html)).

```coq
(* theories/cbv/em_cartesian.v *)

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

The unbundled cartesian-η identity `em_pair_mor_proj_id` — pairing the
two projections back together is the identity,
$\text{em\_pair\_mor}(\text{em\_proj1\_mor}, \text{em\_proj2\_mor}) = \mathrm{id}_{P \otimes Q}$ — is exposed
in `theories/cbv/cbv_adjunction.v` (Section EmPairProjId)
and proved by promoted-point extensionality on the cofree pair, then
transported along the `coalg_str` retract.

```coq
(* theories/cbv/cbv_adjunction.v (Section EmPairProjId) *)
(** Cartesian-η: pairing the two projections is the identity. *)
Lemma em_pair_mor_proj_id (P Q : Coalgebra Ar) :
  @em_pair_mor R Ar (EM_prod P Q) P Q (em_proj1_mor P Q) (em_proj2_mor P Q)
  = icones_id Ar (coalg_obj (EM_prod P Q)).
```

> The reader who expects a cartesian *category* of programs should
> note what is and is not claimed here: `EM(!)` is cartesian, but the
> interpreter does not live in it. `eD_cbv` produces plain
> `icones_hom`s, and `coalg_d` / `coalg_e` are used purely as
> morphisms of `ICone` — the diagonal that duplicates a context, the
> counit that discards it. `em_pair_mor` is the single branching
> primitive of the interpreter (let, pair, application, arithmetic,
> and the scrutinee pairing inside `if_icones` all go through it),
> and `em_term_mor` is the denotation of `ne_tt`.

### Type translation (`tyD_cbv`)

Each surface type is sent to a `!`-coalgebra: `tunit` to the
terminal coalgebra, `tbase X` to the Theorem 9.7 coalgebra on `FMeas
X`, `tbool` to the §9.7-style coalgebra on the 2-point cone, `tprod`
to the EM cartesian product, and `tfun t1 t2` to the cofree
coalgebra on the *clean* internal hom $U\llbracket t_1 \rrbracket \multimap U\llbracket t_2 \rrbracket$.

```coq
(* theories/programs/ppl_cbv.v (Section TypeInterpCBV) *)
Fixpoint tyD_cbv (t : ppl_type Ar) : Coalgebra Ar :=
  match t with
  | tunit => EM_term
  (* … *)
  | tbool => bool_cone_coalg
  | tbase X => FMeas_coalgebra X
  | tprod s1 s2 => EM_prod (tyD_cbv s1) (tyD_cbv s2)
  (* Clean CBV function type — no [Tobj] on the codomain. *)
  | tfun A B => bang_cofree (linhom_car Ar (coalg_obj (tyD_cbv A))
                                          (coalg_obj (tyD_cbv B)))
  end.
```

The `tbase` clause is the
[Thm 9.7 coalgebra](../../paper/entries/thm-9-7.html) of
`theories/exp/coalgebra.v`; the `tbool` clause uses
`bool_cone_coalg` of `theories/programs/infra/bool_cone_coalg.v`,
documented in the boolean-cascade chapter.

> Both coalgebra choices give the *shared-sample* semantics expected
> of a PPL — a duplicated draw is the diagonal pushforward, not the
> independent product $\mu \otimes \mu$ a cofree `bang_cofree (bool_cone_car Ar)`
> would give; the program-level statement is `let_bernoulli_pair_diag`
> in the semantic-laws chapter.
> There is no `Tobj` wrap anywhere: function values are clean linear
> maps, which is what lets `ne_app` dereference with `der` and apply
> directly. The `tfun` clause is also what fixes the type at which
> `fix_comb` is instantiated in the recursion chapter.

### Context translation (`ctxD_cbv`, `var_lookup_cbv`)

A context denotes the right-nested iterated EM product of its types'
coalgebras, with the terminal coalgebra `EM_term` at the nil case;
variable lookup is then the evident chain of `em_proj1` /
`em_proj2` projections, using only the comonoid counits — no
diagonal, no strength.

```coq
(* theories/programs/ppl_cbv.v (Section TypeInterpCBV) *)
Fixpoint ctxD_cbv (G : ppl_ctx Ar) : Coalgebra Ar :=
  match G with
  | nil => EM_term
  | t :: G' => EM_prod (ctxD_cbv G') (tyD_cbv t)
  end.
```

```coq
(* theories/programs/ppl_cbv.v (Section VarLookupCBV) *)
Fixpoint var_lookup_cbv (G : ppl_ctx Ar) (t : ppl_type Ar)
    (v : has_var G t) {struct v} :
    coalg_hom (ctxD_cbv G) (tyD_cbv t) :=
  match v in has_var G0 t0 return coalg_hom (ctxD_cbv G0) (tyD_cbv t0) with
  | hv_zero G' t' => em_proj2 (ctxD_cbv G') (tyD_cbv t')
  | hv_succ G' t' s v' =>
      coalg_comp (var_lookup_cbv v') (em_proj1 (ctxD_cbv G') (tyD_cbv s))
  end.
```

> The head of the context list sits on the *right* of the product, so
> `hv_zero` is the second component and `hv_succ` strips the head —
> the orientation `var_lookup_cbv` projects against. Note that
> `var_lookup_cbv` is `coalg_hom`-valued, unlike the interpreter
> itself: a projection *is* a coalgebra morphism, and the `ne_var`
> clause of `eD_cbv` forgets that structure with `ch_mor`.
> `drop_names` mediates between the named contexts of the surface
> syntax and the `ppl_ctx` this fixpoint consumes.

### Term interpretation (`eD_cbv`, `eD`)

The interpreter is uniformly comonoid-primitive: every branching
node (let, pair, app, if, arithmetic, boolean) uses the $\delta_\Gamma$
diagonal of the context to give each sub-term its own copy of $\Gamma$;
multi-use of a free variable is then free in the cone. The cofree
exponential `!̃` appears only at two boundaries — `ne_lam`, where the
body is curried and promoted via `adj_psi` of the $U \dashv \tilde{!}$ adjunction,
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
  (* … ne_bernoulli_p, ne_score_p, ne_to_prob, ne_incl — the four
     tProb clauses, each a post-composition with bern_lift_g /
     score_lift_g / FMeas_fmap; see the probability-surface chapter … *)
  end.

Definition eD M : linhom_car Ar (coalg_obj (ctxD_cbv (drop_names G)))
                                (coalg_obj (tyD_cbv t)) :=
  icones_to_linhom (eD_cbv M).
```

The effect clauses share one shape — post-compose a lift with the
sub-term's denotation. `ne_score` uses `score_lift`, `ne_meas` the
pushforward `meas_lift`, `ne_bernoulli_f` the value-dependent
`bern_lift`, and `ne_gaussian` / `ne_uniform` the runtime-parameter
lift `kernel_lift2` applied to `gaussian_kernel` / `uniform_kernel`
of `theories/programs/distributions.v`. The behaviour of those two
clauses on point masses, on total mass and on sampling agreement is
pinned by the anchors `eD_gaussian_at`, `eD_gaussian_dirac_E`,
`eD_gaussian_mass` and `eD_gaussian_sample_agree` (with `Uniform`
mirrors) of `theories/programs/kernel_anchors.v`.

The `ne_fix` clause is the composite $\text{fix\_comb} \circ \llbracket \lambda s.\text{body} \rrbracket$: the
self-abstraction is interpreted as an *ordinary* lambda (the
`ne_lam` clause, inlined because `ne_lam s body` is not a subterm of
`ne_fix s body`), then post-composed with the seeded value-fixpoint
combinator $\text{fix\_comb} : EM(\tilde{!}(!L \multimap !L), \tilde{!}L)$ of
`theories/programs/infra/em_fix_value.v`, at $L := U\llbracket t_1 \rrbracket \multimap U\llbracket t_2 \rrbracket$.
The `ne_fix_mr` clause dispatches on the body type
(`fix_mr_clause`): the same `fix_comb` composite at `tfun`, the
Seely-transported `fix_mr_comb` at products of frees. Every
other clause is built from the SMC primitives (`linhom_comp`,
`tensor_mor`, `tensor_braid`, `tensor_curry` / `tensor_uncurry`) and
the coalgebra-comonoid pair (`coalg_d`, `coalg_e`) only.

> The two views of the interpreter are interchangeable and both are
> used: `eD_cbv` is `icones_hom`-valued, which keeps the norm-$\leq 1$
> witness definitionally available to every clause, while the public
> `eD` forgets it with `icones_to_linhom` so that statements about
> denotations can be phrased as equations between linear maps. A
> paper reader expecting a Kleisli-style $\llbracket \Gamma \rrbracket \to T\llbracket \tau \rrbracket$ should note
> that no monad appears: the probabilistic effect is already inside
> the cone, and the recursion combinators are documented in the
> recursion chapter.

### Constant icones helpers (`sample_icones`, `real_icones`, `true_icones`, `false_icones`, `bernoulli_icones`)

Each effect / value constructor — `ne_sample`, `ne_real`,
`ne_bernoulli`, `ne_true`, `ne_false`, that is the `sample`, `real`,
`bernoulli` and `true` / `false` helpers — denotes a *constant*
`icones_hom` out of the context: the context's $\varepsilon_\Gamma$ discards the
context, then the constant value (a unit-ball measure, Dirac, or
two-point distribution) is injected through `const_icones` of
`theories/programs/ppl.v`. (A *unit-ball* measure has total mass at most
`1` — `cone_norm` $\leq 1$ — i.e. it is a genuine sub-probability.)

```coq
(* theories/programs/ppl_cbv.v (Section ConstHelpersCBV) *)
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

(** Constant [icones_hom] at the [true]-Dirac of [bool_cone]. *)
Definition true_icones (G : Coalgebra Ar) :
    icones_hom Ar (coalg_obj G) (bool_cone_car Ar) :=
  const_icones G (bool_dirac_true : bool_cone_car Ar)
                 bool_dirac_true_norm_le1.

(** Constant [icones_hom] at the Bernoulli sub-probability [(p, 1-p)]. *)
Definition bernoulli_icones (G : Coalgebra Ar) (p : R)
    (Hp_ge0 : (0 <= p)%R) (Hp_le1 : (p <= 1)%R) :
    icones_hom Ar (coalg_obj G) (bool_cone_car Ar) :=
  const_icones G (bernoulli p Hp_ge0 Hp_le1)
                 (bernoulli_norm_le1 p Hp_ge0 Hp_le1).
```

`false_icones` is the mirror of `true_icones` at `bool_dirac_false`.

> With `tyD_cbv tbool = bool_cone_coalg`, the carrier of $\llbracket \text{tbool} \rrbracket$ is
> `bool_cone_car Ar` directly (not `Bang _`), so the value is the
> basis point `bool_dirac_true` itself — no `prom` wrap is needed.
> Each helper carries its own unit-ball witness, which is why the
> corresponding clauses of `eD_cbv` are literally the helper applied
> to `ctxD_cbv (drop_names G0)` and are pinned verbatim by
> `eD_sample_E`, `eD_real_E`, `eD_true_E`, `eD_false_E` and
> `eD_bernoulli_E`.

### The value-dependent Bernoulli lift (`bern_lift`, `bern_lift_dirac`, `bern_lift_mass`, `bern_lift_P`, `score_lift_P`)

The semantic engine of `ne_bernoulli_f`: an
`icones_hom (FMeas R_obj) (bool_cone_car Ar)` sending a measure $\mu$
on the reals to the 2-point sub-probability
$(\int f \, d\mu, \int (1 - f) \, d\mu)$ — sample $r \sim \mu$, then flip a coin with
success probability $f r$. It lives in `theories/programs/ppl.v`
(Section BernTmLift), and the `ne_bernoulli_f` clause of `eD_cbv`
post-composes it with the scrutinee's denotation, exactly as
`ne_score` post-composes `score_lift`.

The construction is the *path route*, the `bool_cone` twin of the score
lift: package $x \mapsto \text{bernoulli } (g\,x)$ as a measurable path into
`bool_cone_car Ar` (the three tests of the bool cone evaluate along
the path to $g$, $1 - g$ and the constant $1$), then promote
with `int_to_linhom`. The integral semantics is then automatic by
Pettis uniqueness against the componentwise integral `bool_int` of
`theories/icones/bool_cone.v` — the content of `bern_lift_E`,
from which the two coordinate readings `bern_lift_t_E` and
`bern_lift_f_E` follow.

The path is built **once**, in the carrier-density primitive
`bern_lift_g` (Section BernTmLiftG), which takes the density directly
as a measurable $[0,1]$ map `g : ar_carrier Ar X -> R` at an arbitrary
base object `X`. `bern_lift` is that primitive instantiated at
`X := R_obj`, `g := f ∘ cR`; every law of `bern_lift` is the
corresponding `bern_lift_g` law at the instance, and the only statement
that is not a plain instance is the Dirac identity, which reads at a
*real* point `r` and so pays one `R_to_carrierK` round trip.
(`score_lift` stands to `score_lift_g` in exactly the same way.)

```coq
(* theories/programs/ppl.v (Section BernTmLift) *)
(** The lift as an [icones_hom]: [bern_lift_g] at [g := f ∘ cR]. *)
Definition bern_lift :
    icones_hom Ar (FMeas R_obj) (bool_cone_car Ar) :=
  bern_lift_g bern_f_cR_meas Hf_cR_ge0 Hf_cR_le1.

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
lands), so the lift preserves total mass — with $\|\mu\| = 1$ the reject
weight is exactly $1 - \int f \, d\mu$, which is what makes the headline's
per-iterate mass recurrence affine.

```coq
(* theories/programs/ppl.v (Section BernTmLift) *)
Lemma bern_lift_mass (mu : fmeas R (ar_carrier Ar R_obj)) :
  cone_norm (Lfun bern_lift mu) =
  fine (fmeas_mu mu [set: ar_carrier Ar R_obj]).
```

The `tProb` surface needs the same two lifts at the $[0,1]$ object
`po_obj P` of a bundle `P : probObj` rather than at `R_obj` — the
*other* instance of the same primitives. `bern_lift_P` and
`score_lift_P` instantiate
`bern_lift_g` / `score_lift_g` at `X := po_obj P` with the carrier density `po_density P`
and the bundle's $[0,1]$ witnesses (`po_ge0` / `po_le1`), with no
`R_to_carrier` round trip: `bern_lift_P` is the engine behind `Bernoulli e`,
`score_lift_P` behind `Score e`. The Dirac and mass laws transport
verbatim (`bern_lift_P_dirac`, `score_lift_P_dirac`).

```coq
(* theories/programs/ppl.v (Section ProbObjLifts) *)
Variable (P : probObj Ar).

Definition bern_lift_P
  : icones_hom Ar (FMeas (po_obj P)) (bool_cone_car Ar) :=
  bern_lift_g (po_density_meas P) (po_ge0 P) (po_le1 P).

Definition score_lift_P
  : icones_hom Ar (FMeas (po_obj P)) (cone_one_car Ar) :=
  score_lift_g (po_density_meas P) (po_ge0 P) (po_le1 P).
```

> The lift is *value-dependent* in a strong sense: the coin's bias is
> read off the sampled real rather than fixed at elaboration time,
> which is what distinguishes `ne_bernoulli_f` from the constant
> `bernoulli_icones`. Two design points are worth flagging. First,
> the integral semantics is not proved by computation but by Pettis
> uniqueness — `bern_lift` and `bool_int` solve the same equation.
> Second, the mass law is the reason a rejection loop terminates in
> the model at all; it is consumed by the affine cascade in the
> semantic-laws chapter.

### If-then-else at the icones level (`if_icones`, `if_under`)

The CBV value-level if-then-else takes two branches $m, n :
\text{icones\_hom } G \to A$ and a scrutinee $b : G \to \text{bool\_cone}$ and returns a
clean $\text{icones\_hom } G \to A$, with no Kleisli wrapping at any step. It
is the *single* consumer-side packaging of the boolean cascade: the
branches are co-paired by `bool_case_linhom`, SMCC-uncurried over
$\text{bool\_cone} \otimes G$, braided, and finally pre-composed with the EM
pairing $\langle \text{id}_G, b \rangle$.

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
§9.7 coalgebra) are documented in the boolean-cascade chapter.

> The scrutinee is paired with the *identity* on the context rather
> than discarded and re-supplied, so both branches see the same copy
> of $\Gamma$ that produced the boolean: this is what makes
> `let x = Bernoulli(p) in if x then … else …` correlated rather than
> resampled. Linearity of the co-pairing means the conditional is
> the linear combination of its branches weighted by the scrutinee's
> two coordinates, which is exactly what the branch pins `eD_if_true`
> and `eD_if_false` of the semantic-laws chapter compute at a Dirac
> scrutinee.

### The definitional-unfolding pack (`eD_var_E`, `eD_let_E`, `eD_fix_E` … `eD_fix_mr_prod_E`)

One lemma per `eD_cbv` clause — one for each `named_expr`
constructor, plus the two per-body-type refinements
`eD_fix_mr_fun_E` / `eD_fix_mr_prod_E` of the dispatched
`ne_fix_mr` clause — pins the exact clause body of the interpreter,
so any refactor of `eD_cbv` (or of the combinators it is built from)
breaks loudly in a named lemma instead of silently changing the
semantics.

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
```

The remaining members of the pack are `eD_tt_E`, `eD_pair_E`,
`eD_fst_E`, `eD_snd_E`, `eD_lam_E`, `eD_app_E`, `eD_sample_E`,
`eD_real_E`, `eD_score_E`, `eD_add_E`, `eD_mul_E`, `eD_meas_E`,
`eD_gaussian_E`, `eD_uniform_E`, `eD_true_E`, `eD_false_E`,
`eD_bernoulli_E`, `eD_bernoulli_f_E`, `eD_bernoulli_p_E`,
`eD_score_p_E`, `eD_to_prob_E`, `eD_incl_E`, `eD_if_E`,
`eD_fix_mr_E`, `eD_fix_mr_fun_E` and `eD_fix_mr_prod_E`, all in the
same section and all proved by `by []`.

The *semantic* recursion-unfolding equations — the prom-point
computation law `eD_fix_at_setlike`, the honest recursion
equation `eD_fix_unfold` and its closed-context form
`eD_fix_unfold_closed` — live in
`theories/programs/infra/cbv_fix_unfold.v` (they need the
setlike-point kit of `theories/programs/infra/cbv_anchors.v`, which
imports this file); they are documented with the fixpoint combinator
itself in the recursion chapter. (A point is *setlike* when
`coalg_str` $x = x!$ — the §9.7 reading "$x$ is a (sub-)Dirac"; a
*prom-point* is one of the form `prom F`.)

> These lemmas carry no mathematical content — that is the point.
> They are the regression surface of the interpreter: a statement
> such as `eD_fix_E` is a machine-checked transcription of "the
> `ne_fix` clause is `fix_comb` post-composed with the promoted
> curried body", so a later edit that changes the combinator, the
> adjunction transpose or the argument order fails here rather than
> in a downstream marginal computation. A paper reader can read the
> pack as the displayed definition of $\llbracket {-} \rrbracket$, clause by clause.

## Recursion: the CBV value fixpoint

The CBV-side `let rec` is the value-fixpoint *combinator*
`fix_comb : EM( !̃(!A ⊸ !A), !̃A )` — a morphism of `!`-coalgebras between the
cofree coalgebras, determined on promoted bodies `F!` (for `F` in the unit ball
of `!A ⊸ !A`) by `fix_comb` $(F!) = (\sup_n x_n)!$, where $x_0 = 0 : A$ and
$x_{n+1} = \mathrm{der}(F (x_n !))$ is the *interleaved* Kleene chain. It lives in
`theories/programs/infra/em_fix_value.v` and is what the `ne_fix` clause (and
`ne_fix_mr` at every free body type) of `theories/programs/ppl_cbv.v`
post-composes onto the body's lambda packaging:
$\llbracket \text{fix } s.\text{body} \rrbracket = \text{fix\_comb} \circ \llbracket \lambda s.\text{body} \rrbracket$ — directly at function body types, and
through the Seely transport of `theories/programs/infra/em_fix_mr.v` at
products of free types.

The chapter tells the story in order. First the *degeneracy theorem*: the naive
zero-seeded iteration — the Kleene iteration of
`theories/programs/infra/em_fix.v`'s linear step $\text{prev} \mapsto M \circ (\text{id} \otimes \text{prev}) \circ \delta$
from the linhom cone-zero, which used to be `em_fix.v`'s CBV value-fixpoint
operator before its removal — is *provably the zero linhom*, always
(`Phi_fun_lfp_eq0`): a linear step preserves the zero seed, and the bottom of a
CBV function-value type is not the cone-zero of `!L` but the promoted zero
`(0)!`, the diverging-function value of `e_bang`-mass one. Then the
stable-map infrastructure the repair consumes (paper-§7 material, carried in
the CBV layer at `theories/cbv/diag_bilinear_tensor.v`, a file imported by exactly
`em_fix_value.v` and `em_fix_mr.v`): the lift `linhom_to_stablehom`, which
turns linear data into a *stable* map, and the diagonal bridge
`meas_stable_diag_bilinear_tensor`, which applies a bilinear `ICones` map along
a stable argument without leaving `SCones`.

Then the repair itself: seed the iteration at the genuine bottom `0 : A`
*under* the promotion, interleaving `der` and `prom` so that each iterate
re-enters the body as a promoted value — the $\mathrm{prom} \circ \mathrm{der}$ sandwich is what
makes the chain productive for *any* unit-ball body, linear or not (the step
$x \mapsto \mathrm{der}(F (x!))$ is monotone because `prom` is totally monotone and `F`,
`der` are linear). Coalgebra-morphism-ness of the combinator comes for free:
the value map $F \mapsto \sup_n x_n$ is built from existing `SCones` morphisms,
converted to a linear map `!(!A ⊸ !A) ⊸ A` by the SAFT hom-bijection `lin`, and
packaged by `adj_psi` of the `U ⊣ !̃` adjunction. Finally the *mutual-recursion
transport*: a product of free types is not literally cofree, but it is
*isomorphic* to a cofree coalgebra through the EM-level Seely-2 iso, and
conjugating `fix_comb` by that iso makes `ne_fix_mr` genuine at every free body
type; the chapter closes with the interpreter wiring, the unfolding equations
it satisfies, and the `SCones` fixpoint core `Yfix` on which everything rests.

| Construction | Statement | Rocq |
|---|---|---|
| Why the naive fixpoint degenerates | The zero-seeded Kleene iteration of the naive linear step is the zero linhom, for every diagonal and every body. | `Phi_fun_lfp_eq0`, `Phi_fun_zero` — theories/programs/infra/em_fix_value.v; `lfp_eq0` — theories/stable/fixpoint.v |
| The naive linear Kleene step | The linear step $\text{prev} \mapsto M \circ (\text{id} \otimes \text{prev}) \circ \text{diag}$ and the linhom least-fixpoint core it used to be iterated in. | `Phi_fun`, `linhom_lfp`, `linhom_lfp_fixpoint` — theories/programs/infra/em_fix.v |
| Lifting linear morphisms to stable functions | Every inhabitant of the internal hom is a stable map of cones, and the packaging function is itself measurable-stable. | `linhom_to_stablehom`, `linhom_to_stablehom_meas_stable` — theories/cbv/diag_bilinear_tensor.v |
| Bilinear stability through the tensor | Applying a bilinear `ICones` map along a measurable-stable argument yields a measurable-stable diagonal. | `meas_stable_diag_bilinear_tensor` — theories/cbv/diag_bilinear_tensor.v |
| The seeded Kleene core | The Kleene chain from an arbitrary seed $b_0$ with $b_0 \leq f b_0$, and its fixpoint equation. | `kleene_from`, `lfp_from`, `lfp_from_fixpoint` — theories/programs/infra/em_fix_value.v |
| The interleaved chain and the value map | The chain $x_{n+1} = \mathrm{der}(F (x_n !))$ and the stable map sending a body to its supremum. | `fix_chain`, `fix_value`, `fix_value_E` — theories/programs/infra/em_fix_value.v |
| The fixpoint combinator | The value map as a morphism of cofree `!`-coalgebras, with its prom-point computation law. | `fix_comb`, `fix_comb_mor`, `fix_prom_E` — theories/programs/infra/em_fix_value.v |
| Coalgebraic bodies: the literal chain | On a coalgebra-morphism body the interleaved chain coincides with the literal chain $n \mapsto F^n(0!)$. | `fix_setlike_prom`, `fix_coalg_simpl`, `fix_unfold_coalg` — theories/programs/infra/em_fix_value.v |
| Non-degeneracy | On every promoted body the combinator returns a promoted point, which is never the cone-zero. | `fix_prom_neq0`, `fix_id_E`, `fix_id_nontrivial` — theories/programs/infra/em_fix_value.v |
| The mutual-recursion transport | Conjugating the combinator by an isomorphism of `!`-coalgebras — the EM-level Seely-2 iso — gives a fixpoint at coalgebras that are only isomorphic to cofree ones. | `coalg_iso`, `seely2_em_iso`, `fix_comb_iso` — theories/programs/infra/em_fix_mr.v |
| The free-type decomposition | Every free CBV type is isomorphic to the cofree coalgebra on a base cone, which yields the genuine combinator at that type. | `free_base`, `free_decomp`, `fix_mr_comb` — theories/programs/ppl_cbv.v |
| The interpreter wiring | The `ne_fix_mr` clause dispatches on the free body type, post-composing the combinator that type calls for onto the body's lambda packaging. | `fix_mr_clause`, `eD_fix_mr_fun_E`, `eD_fix_mr_prod_E` — theories/programs/ppl_cbv.v |
| The recursion-unfolding equations | At setlike context points the denotation is the promoted Kleene supremum, and one more body unfolding returns it. | `eD_fix_at_setlike`, `eD_fix_unfold` — theories/programs/infra/cbv_fix_unfold.v |
| The SCones fixpoint core | The paper-§9.2 Kleene least-fixpoint combinator at the `SCones` internal hom. | `Yfix` — theories/stable/fixpoint.v; `Yfix_kleeneE` — theories/programs/infra/em_fix_value.v |

### Why the naive fixpoint degenerates (`Phi_fun_lfp_eq0`, `Phi_fun_zero`, `lfp_eq0`)

For *every* diagonal `diag` and every body `M`, the zero-seeded Kleene
iteration `linhom_lfp (Phi_fun diag M) …` — the construction that used to be
`em_fix.v`'s CBV value-fixpoint operator — equals the zero linhom. The
structural reason: the Kleene step `Phi_fun` is *linear* in the previous
iterate, so it maps the linhom cone-zero seed to the cone-zero (`Phi_fun_zero`
— the $\text{id}_\Gamma \otimes 0$ tensor vanishes by bilinearity, which
is `tensor_mor_R_lin_zero`, the pure-tensor map being linear in its
right argument; then post-composition by the linear `M` preserves zero);
by induction every Kleene iterate is zero
(`kleene_lin_Phi_fun_eq0`), and so is the supremum.

The collapse itself is generic — any Kleene step that preserves the zero seed
has zero least fixpoint — so the degeneracy record is exactly `Phi_fun_zero`
(the linearity content) plus the generic lemma.

```coq
(* theories/stable/fixpoint.v (Section KleeneCore) *)
(** ... the least fixpoint collapses to zero: the supremum of the
    constantly-zero chain is zero. *)
Lemma lfp_eq0 : f 0 = 0 -> lfp = (0 : B).
```

```coq
(* theories/programs/infra/em_fix_value.v (Section CbvFixDegeneracy) *)
(** STEP A: [id_Γ ⊗ 0 = 0] at the linhom level. *)
Lemma tensor_mor_R_lin_zero :
  tensor_mor_R_lin Gamma
    (linhom_icones (precone_zero : linhom_car Ar Gamma B) (zero_ball _ _)) =
  precone_zero.

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

> The diagnosis behind the repair: the bottom of a CBV function *value* type is
> not the cone-zero of `!L` — it is the promoted zero `(0)!`, the
> diverging-function value, which has `e_bang`-mass one — `e_bang` is the
> coalgebra's discard/counit map `!A ⊸ 1`, and every promoted point takes
> the full-weight value `one1` there, unlike the cone-zero — and is
> therefore not even close to `precone_zero` in the cone order. A least fixpoint computed
> from the wrong bottom is the wrong least fixpoint; every later entry of this
> chapter exists to compute it from the right one, and `fix_prom_neq0` is the
> direct contrast.

### The naive linear Kleene step (`Phi_fun`, `linhom_lfp`, `linhom_lfp_fixpoint`)

The step that the degeneracy theorem is about: `Phi_fun` sends a candidate
denotation $\text{prev} : \Gamma \multimap B$ to $M \circ (\text{id}_\Gamma \otimes \text{prev}) \circ \text{diag}$ — "run the body with
`prev` bound to the recursive variable" — extended trivially off the unit ball
(the elements `x` with `cone_norm x <= 1`).
Its zero-seeded Kleene supremum on the unit-ball $\omega$-CPO of `linhom_car Ar Γ B`
(that ball, ordered so that every increasing chain in it has a supremum;
via `em_fix.v`'s linhom LFP core `kleene_lin` / `linhom_lfp`, with the
fixpoint equation `linhom_lfp_fixpoint`) used to be `em_fix.v`'s
CBV value-fixpoint operator.

```coq
(* theories/programs/infra/em_fix.v *)
(** The "safe" version of [Phi_fun] taking a norm-witness as input. *)
Definition Phi_fun_safe
    (prev : linhom_car Ar Gamma B)
    (Hprev : cone_norm prev <= 1) :
    linhom_car Ar Gamma B :=
  linhom_post M
    (linhom_pre_act diag
      (tensor_mor_R_lin Gamma
        (linhom_icones prev Hprev))).
```

`Phi_fun` itself is the `pselect`-totalised wrapper of `Phi_fun_safe`,
returning `precone_zero` off the ball; `Phi_fun_unit` is the agreement
law, saying that on the unit ball — where the whole Kleene chain lives
— the totalised operator *is* the safe one, for any norm witness. The
monotonicity law `Phi_fun_incr` then transports a precone-order
inequality $\text{prev}_1 \leq \text{prev}_2$ through the three linear layers; the
layer that actually carries the approximant is the tensor, whose
monotonicity witness is `tensor_mor_R_lin_incr`, and the generic fact
underneath every layer is `linear_increasing` of
`theories/cones/basic_lemmas.v`: a linear map of cones is increasing
for the cone order, because $x \leq y$ means $y = x + z$ and linearity turns
that into $f\,y = f\,x + f\,z$.

```coq
(* theories/programs/infra/em_fix.v *)
(** On the unit ball the totalised operator is the safe one. *)
Lemma Phi_fun_unit (prev : linhom_car Ar Gamma B)
    (Hprev : cone_norm prev <= 1) :
  Phi_fun prev = Phi_fun_safe prev Hprev.

(** The tensor layer is monotone in the carried approximant. *)
Lemma tensor_mor_R_lin_incr (G C1 C2 : ICone.type Ar)
    (prev1 prev2 : linhom_car Ar C1 C2)
    (Hprev1 : cone_norm prev1 <= 1) (Hprev2 : cone_norm prev2 <= 1) :
  precone_le prev1 prev2 ->
  precone_le (tensor_mor_R_lin G (linhom_icones prev1 Hprev1))
             (tensor_mor_R_lin G (linhom_icones prev2 Hprev2)).
```

```coq
(* theories/cones/basic_lemmas.v *)
(** A linear map is increasing: if [y = x + z] then [f y = f x + f z]. *)
Lemma linear_increasing (f : P -> Q) :
  is_linear f -> is_increasing f.
```

The construction, the ball bound and the fixpoint equation are all true — and
all satisfied by the zero linhom, which is exactly what `Phi_fun_lfp_eq0` shows
the iteration is. The operator itself was removed from `em_fix.v` after the
degeneracy proof; the record survives as `Phi_fun_zero` plus the generic
`lfp_eq0`.

> The step `Phi_fun`, its unit-ball laws `Phi_fun_ball` / `Phi_fun_incr` and the
> linhom LFP core `kleene_lin` / `linhom_lfp` / `linhom_lfp_fixpoint` stay in
> `em_fix.v` for one reason: they are what the degeneracy theorem above is
> *about*. They are **not** scaffolding for the genuine seeded combinator
> `fix_comb`, which routes through none of them — it is built on
> `em_fix_value.v`'s own seeded Kleene core `kleene_from` / `lfp_from`, where
> the cone-zero seed is replaced by an arbitrary $b_0$ with $b_0 \leq f\,b_0$.
> The interpreter never routes through the zero-seeded iteration — the
> `ne_fix_mr` *product* case, formerly the last consumer of the removed
> operator, goes through the genuine Seely-transported combinator
> `fix_mr_comb`.
>
> The $\omega$-continuity component that fed only the removed operator —
> `Phi_fun_omega_cont`, `tensor_mor_omega_cont_R`, `linhom_pre_icones_sup`,
> `linhom_post_icones_sup`, and the unit-ball side conditions
> `kleene_lin_ball` / `kleene_lin_chain` / `linhom_lfp_norm_le1` — was
> removed together with that operator (it documented properties of a
> construction the degeneracy theorem retired).

### Lifting linear morphisms to stable functions (`linhom_to_stablehom`, `linhom_to_stablehom_meas_stable`)

Every inhabitant of the internal hom `linhom_car Ar B C` is a stable
(totally monotonic, norm-bounded, and $\omega$-continuous on unit-ball chains —
paper Def 7.7) and
measurable map of cones, and the `linhom → stablehom` packaging function
`linhom_to_stablehom : linhom_car Ar B C → stablehom B C` is *itself*
measurable-stable — the internal-hom version of paper Lemma 7.31.

```coq
(* theories/cbv/diag_bilinear_tensor.v *)
Definition linhom_to_stablehom (h : linhom_car Ar B C) : stablehom B C :=
  MkStablehom (sc_clamp (linhom_fun h))
              (sc_clamp_meas_stable (linhom_meas_stable h))
              (sc_clamp_offball_field _).

Lemma linhom_to_stablehom_meas_stable :
  is_meas_stable (linhom_to_stablehom : linhom_car Ar B C -> stablehom B C).
```

The 0-extension off the unit ball is the standard `sc_clamp`.

> This is the lift the CBV value-fixpoint consumes: `fix_lts` of
> `theories/programs/infra/em_fix_value.v` applies it to the post-action
> $F \mapsto \mathrm{der} \circ F$, feeding `fix_value` — it is the first ingredient of the value
> map, and the reason a chapter of stable-map material sits inside the recursion
> story.

### Bilinear stability through the tensor (`meas_stable_diag_bilinear_tensor`)

For any measurable-stable $K : G \to E_A$ (totally monotonic, norm-bounded and
$\omega$-continuous on unit-ball chains, and measurable-path preserving — paper
Def 7.7 / Def 7.10) and any bilinear $\Phi : G \otimes E_A \to E_B$ (an
`icones_hom` out of the tensor), the diagonal evaluation $g \mapsto \Phi(g \otimes K g)$ is
measurable-stable — the bridge that lets a bilinear `ICones` map be applied
along a stable argument without leaving `SCones`.

The proof is pure structural composition through paper Theorem 5.12's
tensor↔internal-hom adjunction; no §7.3 finite-difference replay is required.
It rewrites the diagonal through the adjunction, then assembles the lift (the
inner `linhom_to_stablehom` is meas-stable by Lemma 7.31,
`linhom_to_stablehom_meas_stable`), the
post-composition with `tensor_curry Φ` (`meas_stable_comp_post`, with its
pre-composition twin `meas_stable_comp_pre`), the diagonal pair
(`id_spair_meas_stable`, the specialisation of the general stable pairing
`spair_meas_stable`), and paper Lemma 7.27 (`ev` is meas-stable) — finally
rescaling by linearity of `ev_fun` in its first slot.

```coq
(* theories/cbv/diag_bilinear_tensor.v *)
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

> `EA` and `EB` are kept as arbitrary integrable cones rather than instantiated
> to `Bang Ar A` / `Bang Ar B`, so that `diag_bilinear_tensor.v` does not have to
> import the exponential adjunction: it stays pure `homs`/`stable` material even
> though the CBV layer is where it is consumed. The two consumers are exactly
> `theories/programs/infra/em_fix_value.v` and
> `theories/programs/infra/em_fix_mr.v`.

### The seeded Kleene core (`kleene_from`, `lfp_from`, `lfp_from_fixpoint`)

The generic Kleene chain $n \mapsto f^n(b_0)$ for an *arbitrary* seed $b_0$ with
$b_0 \leq f b_0$ replacing the `precone_le0` base of the zero-seeded chains, stated
on a bare `coneType` so that it covers both cone-point chains (the literal
chain $F^n(0!)$ of `fix_coalg_simpl`) and linhom-level chains. The fixpoint
equation holds under $\omega$-continuity of the step on the ball.

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

> The whole point of the seed hypothesis $b_0 \leq f b_0$ is that the zero-seeded
> `linhom_lfp` of `em_fix.v` could never provide it at a function-value type,
> where the bottom is `0!` and not `precone_zero` — that is the base case
> `fix_seed_le` discharges in `fix_coalg_simpl`.

### The interleaved chain and the value map (`fix_chain`, `fix_chain_S`, `fix_value`, `fix_value_E`, `fix_value_unfold`)

Fix `A` and write $!A := \text{Bang Ar } A$, $LL := !A \multimap !A$. The interleaved chain of
a body $F : LL$ is $x_0 = 0 : A$, $x_{n+1} = \mathrm{der}(F (x_n !))$: each iterate is
*re-promoted* before it re-enters the body and *dereferenced* after — so the
body always sees a legitimate (promoted) function value, and the chain lives in
`A` where the genuine bottom is `0`. Monotonicity needs no linearity of the
assignment $F \mapsto x_n$: `prom` is totally monotone on the unit ball
(`prom_incr`: it is the underlying map of the stable `nl`, so its total
monotonicity is read off `sc_meas_stable`), and `F` and `der` are linear
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

The assignment $F \mapsto \sup_n x_n$ is then packaged as a *stable* map — obligation
(a) of the construction. It is the composite of existing `SCones` morphisms (so
total monotonicity, $\omega$-continuity and path-measurability come for free): the
linear-to-stable lift `linhom_to_stablehom` of the post-action $F \mapsto \mathrm{der} \circ F$
(this is `fix_lts`), curried through the CCC (cartesian closed category) of `theories/stable/scones_ccc.v`
against the `nl`-promotion of the argument, and closed by the §9.2 fixpoint
combinator `Yfix` of `theories/stable/fixpoint.v` — whose value at a unit-ball
`f` is identified with the plain Kleene supremum $\sup_n f^n(0)$ by
`Yfix_kleeneE`. The chain's own unit-ball and chain conditions are
`fix_chain_ball` and `fix_chain_chain`.

The two named pieces of that composite are worth having by name,
because they are where the chain's step actually lives.
`fix_lts_fun` is the underlying function of the `SCones` morphism
`fix_lts`: it lifts the post-action $F \mapsto \mathrm{der} \circ F$ to a stable map
through `linhom_to_stablehom`. `fix_step` is the composite that
evaluates it against the `nl`-promoted argument —
$\mathrm{Ev} \circ \langle \text{fix\_lts} \circ \pi_1,\ \text{nl} \circ \pi_2 \rangle$ — and `fix_body` is its CCC
currying. `fix_step_E` is the payoff — on
unit-ball points the curried-and-evaluated composite computes to
exactly one step of the interleaved chain, $(F, x) \mapsto \mathrm{der}(F(x!))$, so
nothing about the `SCones` detour survives into the chain's equations.

```coq
(* theories/programs/infra/em_fix_value.v (Section FixCombinator) *)
(** [fix_lts : LL → (!A ⇒ₛ A)], as a plain function. *)
Definition fix_lts_fun (F : LL) : stablehom BA A :=
  linhom_to_stablehom (linhom_post (der A) F).

(** [fix_step : LL × A → A], the SCones composite. *)
Definition fix_step : scones_hom (sprod LL A) A :=
  scones_comp (Ev BA A)
    (scpair (scones_comp fix_lts pF) (scones_comp (nl A) px)).

(** Pointwise computation of the step on the ball. *)
Lemma fix_step_E (F : LL) (x : A) :
  cone_norm F <= 1 -> cone_norm x <= 1 ->
  sc_fun fix_step (sprod_pair F x) =
  Lfun (der A) (linhom_fun F (prom x)).
```

```coq
(* theories/programs/infra/em_fix_value.v *)
(** Promotion is monotone on the unit ball ([nl] is totally monotone). *)
Lemma prom_incr (x y : A) :
  precone_le x y -> cone_norm y <= 1 ->
  precone_le (prom x) (prom y).
```

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

> The $\mathrm{prom} \circ \mathrm{der}$ sandwich is the whole repair: it makes the chain productive
> for *any* unit-ball body, linear or not, whereas the linear step `Phi_fun`
> was productive for none. `fix_value` is the object the rest of the chapter
> transports — `fix_comb` promotes it, `fix_comb_iso` conjugates it, and
> `eD_fix_at_setlike` reads it off the interpreter.

### The fixpoint combinator (`fix_comb`, `fix_comb_mor`, `fix_prom_E`)

`fix_comb` is the value-fixpoint combinator: on a promoted unit-ball body
`F : !A ⊸ !A` it returns the promoted supremum of the interleaved chain,
`fix_comb` $(F!) = (\sup_n x_n)!$ (the chapter's opening formula, pinned by
`fix_prom_E` below). A stable map `(!A ⊸ !A) → A` *is* a linear map
`!(!A ⊸ !A) ⊸ A` via the SAFT (Special Adjoint Functor Theorem)
hom-bijection `lin`/`Theta` of `theories/exp/bang.v`
(`fix_lin := lin fix_value`, with the promoted-point computation
`fix_lin_promE`); `adj_psi` of the `U ⊣ !̃` adjunction then packages the linear
map as a morphism into the
cofree coalgebra — so `fix_comb` is a coalgebra morphism *by construction*,
with no fresh order analysis of the SAFT `Bang`.

```coq
(* theories/programs/infra/em_fix_value.v *)
Definition fix_comb :
    coalg_hom (bang_cofree (linhom_car Ar (Bang Ar A) (Bang Ar A)))
              (bang_cofree A) :=
  adj_psi (P := bang_cofree LL) fix_lin.

Lemma fix_comb_mor :
  ch_mor fix_comb = icones_comp (bang_fmap fix_lin) (dig LL).

(** The prom-point computation law — the defining formula. *)
Lemma fix_prom_E (F : LL) (HF : cone_norm F <= 1) :
  Lfun (ch_mor fix_comb) (prom F) = prom (sc_fun fix_value F).
```

`fix_prom_E` is the law every consumer starts from: on a promoted body the
combinator returns the *promoted* interleaved-Kleene supremum. Its proof
composes `dig_prom` (the cofree structure map promotes promoted points),
`bang_fmap_prom` (the functorial action computes on promoted points) and
`fix_lin_promE`.

> Obligation (a) — that the value assignment is a coalgebra morphism — is
> discharged by construction rather than by a proof: everything upstream of
> `adj_psi` is already a morphism of the relevant categories. Downstream,
> `fix_prom_E` is what `fix_coalg_simpl`, `fix_prom_neq0`, `fix_comb_iso_prom_E`
> and `eD_fix_at_setlike` all rewrite with.

### Coalgebraic bodies: the literal chain (`fix_setlike_prom`, `fix_coalg_simpl`, `fix_unfold_coalg`)

Obligation (b): when the body `F` is itself a morphism of `!`-coalgebras
$!A \to !A$, the interleaved chain coincides with the *literal* Kleene chain
$n \mapsto F^n(0!)$ in `!A`, seeded at the diverging value `0!` — the naive iteration
one would have written by hand. The bridge is `fix_setlike_prom`: a
coalgebraic body sends promoted points to promoted points
($F(y!) = (\mathrm{der}(F (y!)))!$, read off the coalgebra-morphism square at `y!` plus
the right counit law), so promotion intertwines the two chains
(`fix_iter_promE`).

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

> Note the seed-order obligation $0! \leq F(0!)$ (`fix_seed_le`) — the base case
> the zero-seeded `linhom_lfp` could never provide, and the reason the seeded
> Kleene core `kleene_from` / `lfp_from` of this file exists. Obligation (b) is
> what certifies that the interleaved definition agrees with the hand-written
> one wherever the hand-written one makes sense.

### Non-degeneracy (`fix_prom_neq0`, `fix_id_E`, `fix_id_nontrivial`)

On *every* promoted body the combinator returns a promoted point of `!A`, and a
promoted point is never the cone-zero (its `e_bang`-mass is `one1`: it takes
full weight under the coalgebra's discard/counit map `e_bang`, never the zero
scalar) — the
direct contrast with `Phi_fun_lfp_eq0`. The simplest honest instance is the
identity body `fix_idF`: its interleaved chain is constantly `0` (since
$\mathrm{der}(0!) = 0$), so `fix_comb` $(id!) = 0!$ — the *diverging value*, which is
provably nonzero. The general fact the entry rests on is `prom_neq0`: *no*
promoted unit-ball point is the cone-zero, because `e_bang` sends it to `one1`
(`e_bang_prom`) while it sends the zero to the zero scalar.
`fix_prom_neq0` is that lemma applied to the combinator's own output.

```coq
(* theories/programs/infra/em_fix_value.v *)
(** A promoted unit-ball point is never the cone-zero of [!A]. *)
Lemma prom_neq0 (x : A) :
  cone_norm x <= 1 -> prom x <> (precone_zero : Bang Ar A).

Lemma fix_prom_neq0 (F : LL) (HF : cone_norm F <= 1) :
  Lfun (ch_mor fix_comb) (prom F) <> precone_zero.

(** [fix_comb (id!) = 0!] — the diverging value. *)
Lemma fix_id_E :
  Lfun (ch_mor (fix_comb A)) (prom fix_idF) = prom (precone_zero : A).

(** The witness: the fix of the identity body is NOT zero. *)
Lemma fix_id_nontrivial :
  Lfun (ch_mor (fix_comb A)) (prom fix_idF) <> precone_zero.
```

> Divergence and the cone-zero are different semantic facts in this model: a
> diverging function value is $0!$, of `e_bang`-mass one, while the cone-zero
> is the denotation of a run that has been scored away. The degenerate
> `Phi_fun_lfp_eq0` conflated the two; these three lemmas pin the separation,
> and `eD_fix_at_setlike_neq0` propagates it to the interpreter.

### The mutual-recursion transport (`coalg_iso`, `seely2_em_iso`, `fix_comb_iso`)

The layer that makes `ne_fix_mr` genuine at *products* of free types, in
`theories/programs/infra/em_fix_mr.v`. The problem: `fix_comb` lives on
*cofree* coalgebras, but the CBV interpretation of a product is
`tyD_cbv (tprod s t) = EM_prod (tyD s) (tyD t)` — not literally cofree. The
solution, in three moves.

**Isomorphisms of `!`-coalgebras.** `coalg_iso P Q` bundles both directions as
`coalg_hom`s plus the two round-trips at the underlying-`icones_hom` level,
with identity / symmetry / transitivity (`coalg_iso_id`, `coalg_iso_sym`,
`coalg_iso_trans`) and the `EM_prod` congruence `coalg_iso_prod` (the tensor of
two coalg isos, built from `coalg_hom_prod` and hence from `EM_prod_mor`).

```coq
(* theories/programs/infra/em_fix_mr.v (Section CoalgIso) *)
Record coalg_iso (P Q : Coalgebra Ar) : Type := MkCoalgIso {
  ci_fwd : coalg_hom P Q;
  ci_bwd : coalg_hom Q P;
  ci_fwdK : icones_comp (ch_mor ci_bwd) (ch_mor ci_fwd) =
            icones_id Ar (coalg_obj P);
  ci_bwdK : icones_comp (ch_mor ci_fwd) (ch_mor ci_bwd) =
            icones_id Ar (coalg_obj Q);
}.
```

**The Seely-2 iso at the EM level.** For cofree coalgebras the product *is*
cofree on the `&`-product (`sprod`, the cone product — note: `&`, not the
tensor) of the base cones: $\text{EM\_prod}(\tilde{!}X, \tilde{!}Y) \cong \tilde{!}(X \mathbin{\&} Y)$.

```coq
(* theories/programs/infra/em_fix_mr.v (Section Seely2EM) *)
Definition seely2_em_iso (X Y : ICone.type Ar) :
    coalg_iso (EM_prod (bang_cofree X) (bang_cofree Y))
              (bang_cofree (sprod X Y)) :=
  MkCoalgIso (ci_fwd := MkCoalgHom (seely2_fwd_is_coalg_mor X Y))
    (ci_bwd := MkCoalgHom (seely2_bwd_is_coalg_mor X Y))
    (iso_fwdK (Seely2 X Y)) (iso_bwdK (Seely2 X Y)).
```

The carrier of $\text{EM\_prod}(\tilde{!}X, \tilde{!}Y)$ is $!X \otimes !Y$ and its structure map is the
`Seely2`-transported `tens_cofree_str` (`EM_prod_str_cofree2`), so the
coalgebra-morphism squares for the two directions of
$\text{Seely2} : !X \otimes !Y \cong !(X \mathbin{\&} Y)$ are pure transport algebra
(`seely2_fwd_is_coalg_mor` / `seely2_bwd_is_coalg_mor` — no point computation).

**The transported combinator.** For any coalgebra `P` with
`iso : coalg_iso P (!̃Z)`, conjugating `fix_comb Z` by the iso gives
`fix_comb_iso iso : EM( !̃(U P ⊸ U P), P )`: bodies `F : U P ⊸ U P` transport to
`!Z ⊸ !Z` by pre/post-composition with the iso's underlying linear maps
(`fix_iso_body_conj`, the hom-functor action `linhom_map_icones`), the genuine
fixpoint runs at `Z`, and the result is carried back by the iso's backward map.
The computation law is the analogue of `fix_prom_E`, and comes with the norm
bound `fix_comb_iso_norm`.

```coq
(* theories/programs/infra/em_fix_mr.v (Section FixCombIso) *)
Definition fix_comb_iso :
    coalg_hom (bang_cofree (linhom_car Ar UP UP)) P :=
  coalg_comp (ci_bwd iso)
    (coalg_comp (fix_comb Z) (bang_cofree_hom fix_iso_body_conj)).

Lemma fix_comb_iso_prom_E (F : linhom_car Ar UP UP)
    (HF : cone_norm F <= 1) :
  Lfun (ch_mor fix_comb_iso) (prom F) =
  Lfun (ch_mor (ci_bwd iso))
    (prom (sc_fun (fix_value Z)
       (linhom_map_fun (ch_mor (ci_bwd iso)) (ch_mor (ci_fwd iso)) F))).
```

> Nothing here re-proves a fixpoint: `fix_comb_iso` is a composite of
> `coalg_hom`s, so it is a coalgebra morphism for the same reason `fix_comb`
> is, and its computation law is `fix_prom_E` read through the iso. The
> `ppl_cbv.v` side supplies the iso — see `free_decomp`.

### The free-type decomposition (`free_base`, `free_decomp`, `is_free_prodl`, `is_free_prodr`, `fix_mr_comb`)

On the `theories/programs/ppl_cbv.v` side, `free_base t` computes the base cone
of a free type ($\text{tfun } t_1 \, t_2 \mapsto U\llbracket t_1 \rrbracket \multimap U\llbracket t_2 \rrbracket$;
$\text{tprod } t_1 \, t_2 \mapsto \text{sprod}(\text{free\_base } t_1, \text{free\_base } t_2)$) and
`free_decomp t Hfree : coalg_iso (tyD_cbv t) (!̃(free_base t))` witnesses
$\text{tyD\_cbv } t \cong \tilde{!}(\text{free\_base } t)$, built by structural induction on the
`is_free_coalg_type` witness — the
`tfun` case is the identity iso (the interpretation *is* `bang_cofree`), the
`tprod` case composes the children's isos (`coalg_iso_prod`, using the
inversion lemmas `is_free_prodl` / `is_free_prodr`) with `seely2_em_iso`.
`fix_mr_comb t Hfree := fix_comb_iso (free_decomp t Hfree)` is then the genuine
value-fixpoint combinator at every free type.

```coq
(* theories/programs/ppl_cbv.v (Section FreeDecomp) *)
Definition fix_mr_comb (t : ppl_type Ar) (Hfree : is_free_coalg_type t) :
    coalg_hom (bang_cofree (linhom_car Ar (coalg_obj (tyD_cbv t))
                                          (coalg_obj (tyD_cbv t))))
              (tyD_cbv t) :=
  fix_comb_iso (@free_decomp t Hfree).
```

The surface witness is the mutual-recursion pair `ex_even_odd_pair` of
`theories/programs/examples.v` (one recursive name at
`tprod (tfun tunit tunit) (tfun tunit tunit)`, each component calling the other
through `fst`/`snd`) — readably,
`ex_even_odd_pair = fix_mr p. (λn. snd p n, λn. fst p n)`.
Its operational identity is honest divergence: each
component delegates to the other with no base case, so `ex_even_cbv_diverges` /
`ex_odd_cbv_diverges` pin the closed runs `ex_even @ ()` / `ex_odd @ ()` to the
unit-cone zero (mass `0`), while the pair value itself is $0! \otimes_p 0!$
(`ex_even_odd_pair_cbv_value`), never the cone-zero — see the
[Examples tab](../../examples/index.html).

> The catch-all clause of `free_base` is arbitrary, because non-free types
> never reach it: `is_free_coalg_type` gates the recursion, and the impossible
> branches of `free_decomp` are closed by contradiction on that witness.

### The interpreter wiring (`fix_mr_clause`, `eD_fix_mr_fun_E`)

Where `ne_fix` post-composes `fix_comb` directly — the composite pinned by
`eD_fix_E` in the definitional-unfolding pack of the call-by-value chapter —
`ne_fix_mr` has to choose its combinator by inspecting the body type. That
choice is `fix_mr_clause`, a match on the free body type with the non-free
branches closed by the `is_free_coalg_type` witness.

```coq
(* theories/programs/ppl_cbv.v *)
Definition fix_mr_clause (G0 : Coalgebra Ar) (ty : T)
    (Hfree : is_free_coalg_type ty)
    (d : icones_hom Ar (tensor Ar (coalg_obj G0) (coalg_obj (tyD_cbv ty)))
                       (coalg_obj (tyD_cbv ty))) :
    icones_hom Ar (coalg_obj G0) (coalg_obj (tyD_cbv ty)) :=
  (match ty as ty0 return (* … motive … *) _ with
  | tfun t1 t2 => fun _ d =>
      icones_comp
        (ch_mor (fix_comb (linhom_car Ar (coalg_obj (tyD_cbv t1))
                                         (coalg_obj (tyD_cbv t2)))))
        (ch_mor (adj_psi (P := G0) (* … *) (tensor_curry d)))
  | tprod t1 t2 => fun Hf d =>
      icones_comp
        (ch_mor (fix_mr_comb (tprod t1 t2) Hf))
        (ch_mor (adj_psi (P := G0) (* … *) (tensor_curry d)))
  | _ => fun Hf _ => match notF Hf with end
  end) Hfree d.
```

Both branches are the same shape — a combinator post-composed with the body's
lambda packaging — and differ only in which combinator: at `tfun t1 t2` the
genuine `fix_comb` (pinned by `eD_fix_mr_fun_E`, the same composite as
`eD_fix_E`); at `tprod`-of-frees the Seely-transported `fix_mr_comb` (pinned by
`eD_fix_mr_prod_E`). The mutual-recursion fixpoint is therefore genuine at
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

> Dispatching inside the clause rather than at the constructor is what keeps
> `ne_fix_mr` a single constructor with a single interpretation: the body type
> chooses the combinator, and the impossible branches cost nothing because the
> `is_free_coalg_type` witness closes them. Both pins are therefore still
> definitional, which is why they are proved `by []` and belong with the rest
> of the definitional-unfolding pack rather than with the semantic laws.

### The recursion-unfolding equations (`eD_fix_at_setlike`, `eD_fix_unfold`)

The semantic laws of the wired `ne_fix` clause, stated at *setlike* unit-ball
context points ($\text{coalg\_str}(\Gamma, \gamma) = \gamma!$ — the §9.7 "γ is a sub-Dirac" reading) in
`theories/programs/infra/cbv_fix_unfold.v`. Writing
$F_\gamma := \text{curry}(\llbracket \text{body} \rrbracket)(\gamma) : !L \multimap !L$ for the body's endo-function at `γ`:

- `eD_fix_at_setlike` — the prom-point *computation* law:
  $\llbracket \text{fix } s.\text{body} \rrbracket(\gamma) = (\text{fix\_value}(F_\gamma))!$, i.e. the denotation is the promoted
  supremum of the interleaved Kleene chain. In particular it is never the
  cone-zero (`eD_fix_at_setlike_neq0`).
- `eD_fix_unfold` — the honest *recursion equation*: one more body unfolding at
  the fixpoint value, re-promoted, is the fixpoint value.

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

The closed-program corollaries `eD_fix_at_one1` / `eD_fix_unfold_closed` (same
file) state both laws against the public linhom interpreter `eD` at the unit
context point `one1` (which is setlike, `coalg_str_one1`). The same two laws
also hold verbatim for `ne_fix_mr` at function body types
(`eD_fix_mr_fun_at_setlike` / `eD_fix_mr_fun_unfold`); at *product* body types
the computation law is the Seely-transported analogue
`eD_fix_mr_prod_at_setlike` — the denotation at a setlike `γ` is the backward
transport along `free_decomp` of the promoted fixpoint value of the conjugated
body (`fix_comb_iso_prom_E`), never the cone-zero
(`eD_fix_mr_prod_at_setlike_neq0`).

> These equations live in their own file because the setlike-point kit they
> consume (`theories/programs/infra/cbv_anchors.v`) imports
> `theories/programs/ppl_cbv.v` — an import cycle would result if they sat next
> to the definitional clause pins `eD_fix_E` / `eD_fix_mr_prod_E`.

### The SCones fixpoint core (`Yfix`, `Yfix_kleeneE`)

The stable-fixpoint core is `Yfix : scones_hom BB B` of
`theories/stable/fixpoint.v` — paper §9.2: the Kleene fixpoint at the `SCones`
(the category of integrable cones and stable-and-measurable maps)
internal hom, sending a stable endomap of an arbitrary integrable cone `B`
(`BB` is that internal hom, `B ⇒ B`) to its least fixpoint in `B`, a
unit-ball chain from `precone_zero` taken as a supremum.

```coq
(* theories/stable/fixpoint.v *)
(** Paper §9.2: the least-fixpoint combinator [Y], as a morphism of
    [SCones]. *)
Definition Yfix : scones_hom BB B :=
  MkSconesHom (sh_fun Yfix_elt) (sh_meas_stable Yfix_elt) Yfix_norm_le1
    (sh_offball Yfix_elt).
```

At a bare `SCones` function space the zero seed *is* the right bottom, and
`Yfix` serves recursion directly; at a CBV function-*value* type the bottom is
the promoted zero $0!$ instead — promotion `prom` sends a point `x` to `x!`
and dereliction `der` is the counit taking `x!` back to `x` — so `Yfix`
appears one level down, *inside* the
construction of `fix_value`, with the seeding repaired by the `der`/`prom`
interleaving. The identification of its value with the plain Kleene supremum
$\sup_n f^n(0)$ is `Yfix_kleeneE`, proved in
`theories/programs/infra/em_fix_value.v` next to its only use.

> This entry is the floor of the chapter: everything above is a repair of the
> *seed*, not of the fixpoint theory. `Yfix` is unchanged from the paper's §9.2
> and is shared with the stable-cones development; only its point of
> application moved.

## Semantic laws and regression anchors

The equational layer between the interpreter and the example results:
pointwise laws *about* `eD` that the rejection-sampling and
mass-identity proofs consume, plus the regression anchors that pin the
operational reading of the CBV interpreter. The anchors exist so that a
refactor of the §7/§9 cartesian machinery that silently flipped the
shared-sample semantics to an independent-product semantics would break
in a named lemma instead of compiling quietly. The chapter opens with
the morphism-level rewriting laws, continues with the integral laws and
the point-evaluation kits they run on, and closes with the marginal
identities these laws were built for, with the conditioning law and the
rejection/conditioning equivalence of
`theories/programs/ex_reject_model.v`.

| Construction | Statement | Rocq |
|---|---|---|
| The β-rule and the if-pins | $(\lambda x.M) V = \text{let } x := V \text{ in } M$, and the boolean dispatch is oriented — `if true` selects the left branch, `if false` the right | `eD_beta`, `eD_if_true`, `eD_if_false` — theories/programs/infra/cbv_anchors.v |
| The let-at-sample integral law | $\llbracket \text{let } x = \text{sample } \mu \text{ in } K \rrbracket(\gamma) = \int \llbracket K \rrbracket(\gamma \otimes \delta_r) \mu(dr)$, and the same law at an arbitrary bound computation | `eD_let_sample_int`, `eD_let_sample_mu_E`, `eD_let_int` — theories/programs/infra/let_sample_law.v |
| The affine cascade, the sup-mass bridge, and the mass bookkeeping | The scalar recurrence $x(n+1) = a + q \cdot x_n$ in closed form; the mass of a Kleene supremum as the limit of the per-iterate masses; and the acceptance-mass integrals of a bounded nonnegative integrand, with the complementary weight $\int h\,d\nu = \nu(\text{setT}) - \int g\,d\nu$ at $g + h \equiv 1$ | `affine_iter_closed` — theories/prelude/geom_series.v; `fmeas_kleene_sup_U_E`, `fmeas_int_le_mass`, `fmeas_int_compl` — theories/mcones/fmeas.v |
| The setlike-point kit | At setlike unit-ball points the Eq-88 comonoid computes: the diagonal is the pure tensor square $x \otimes x$, the counit is the unit point; and the three interpreter clauses every rider runs on — lambda, application, if — compute there | `coalg_d_setlike`, `coalg_str_tensor_setlike`, `em_pair_mor_constE`, `adj_psi_at_setlike`, `eD_app_at_setlike`, `if_icones_at`, `linhom_fun_sup_ball` — theories/programs/infra/cbv_anchors.v |
| The sharing-semantics anchors | `let x = Bernoulli(p) in (x, x)` denotes the diagonal pushforward; two separate draws denote the independent product $\otimes$ | `let_bernoulli_pair_diag`, `pair_bernoulli_indep` — theories/programs/infra/cbv_anchors.v |
| The marginal kit at non-setlike points | The `FMeas` counit sends every probability measure to the unit point, so a discarded probability leaves the kept component unchanged | `coalg_e_FMeas_prob`, `em_proj1_mor_probE`, `one_dirac_setlike` — theories/programs/cbv_marginals.v |
| The score posterior and its normalisation | `score` denotes the prior reweighted by the evidence density; rejection sampling denotes the same measure, normalised | `ex_score_posterior_cbv_E`, `ex_reject_normalises_score` — theories/programs/cbv_marginals.v |
| The marginals of random functions | A sampled constant derelicts to the prior at probability test points; the random affine model derelicts to the joint pushforward at Diracs | `ex_random_constant_cbv_marginal`, `ex_random_linear_cbv_marginal` — theories/programs/cbv_marginals.v |
| The Bayesian-linear model evidence | The comonoid counit of the function-space denotation of `ex_bayes_linear l` is the model evidence | `ex_bayes_linear_cbv_evidence`, `obs_fold_at` — theories/programs/cbv_marginals.v |
| The conditioning law and the equivalence | $\llbracket \text{condition } f \, m \rrbracket(U) = \int_U t \, d\nu_M$ at the predicate's true-weight $t$, for an arbitrary model; rejection sampling computes that measure, normalised | `condition_model_E`, `condition_E`, `reject_normalises_condition` — theories/programs/ex_reject_model.v |

### The β-rule and the if-pins (`eD_beta`, `eD_if_true`, `eD_if_false`)

Two morphism-level anchors on the pure fragment. The $\beta$-rule
$(\lambda x.M) V = \text{let } x := V \text{ in } M$ holds as an equality of `icones_hom`s, not
merely pointwise at chosen environments; the if-pins state that `eD`
sends `if true then M else N` to $\llbracket M \rrbracket$ and `if false then M else N` to
$\llbracket N \rrbracket$.

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

In the $\beta$-rule the `!̃` round trip `der ∘ !(curry M) ∘ str` collapses by
`adj_phiK` (the adjunction triangle), and the curry/uncurry round trip
by `tensor_uncurry_natL` + `tensor_curryK`. In the if-pins the constant
scrutinee erases the diagonal copy through `em_pair_mor_constE`, after
which the dispatch computes on the boolean basis.

> The if-pins are cheap to state and expensive to omit: a braid slipped
> into `if_under` would flip the branches and break exactly here. Both
> the $\beta$-rule and the pins are equalities of `eD_cbv` morphisms rather
> than pointwise identities at chosen environments, and both are proved
> from the definitional clause pins of `ppl_cbv.v` rather than by
> re-deriving the interpreter.

### The let-at-sample integral law (`eD_let_sample_int`, `eD_let_sample_mu_E`, `eD_let_int`)

The law ties the CBV interpretation of `let x = sample µ in K` to the
Pettis integral of `K`'s denotation over the Diracs of `µ`:
$$\llbracket \text{let } x = \text{sample } \mu \text{ in } K \rrbracket(\gamma) = \int \llbracket K \rrbracket(\gamma \otimes \delta_r) \mu(dr)$$
pointwise at arbitrary $\gamma$. No unit-ball and no setlike hypothesis is needed
anywhere (a point is *unit-ball* when its cone-norm is $\leq 1$, and *setlike*
when `coalg_str` $\gamma = \gamma!$ — a single (sub-)Dirac rather than a
mixture), because every step is driven by a genuine `linhom_car` /
`icones_hom` field, all of which hold on the whole cone.

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

The proof is a four-step composition: (1) the sample-let *collapse*
`eD_let_sample_collapse`, $\llbracket \text{let } x = \text{sample } \mu \text{ in } K \rrbracket(\gamma) = \llbracket K \rrbracket(\gamma \otimes \mu)$ — the inner
`em_pair_mor id (const µ)` erases the context copy through the comonoid
counit law `emc_counitR` (`em_pair_mor_const_E`, stated for an arbitrary
constant); (2) the Dirac approximation $\mu = \int \delta_r \, \mu(dr)$ re-spelled with
the bare `dirac_fmeas` integrand (`icone_integral_dirac_fmeas`, from
`bilin.v`'s Thm 6.1 Dirac approximation); (3) tensoring with a fixed
point preserves Pettis integrals, $\gamma \otimes (\int \beta \, d\mu) = \int (\gamma \otimes \beta_r) \mu(dr)$ —
the `linhom_pres_int` field of `τ(γ)` (`ptensor_icone_integral`); and
(4) the `icones_hom_pres_int` field of $\llbracket K \rrbracket$ pushes the denotation under
the integral.

For headline consumption the law is fused with the per-$U$ evaluation of
an `FMeas`-valued Pettis integral (`icone_integral_fmeas_E`, the
generalisation of `FMeas_fmap_setT_E` from `setT` to an arbitrary
measurable $U$, read off the Pettis equation against the test
`fmeas_eU U`): when the let body has type `tR` the denotation is a
measure, and its mass on $U$ is an ordinary Lebesgue integral — the
exact shape of the rejection-sampling mass recurrence. The sanity
check `let_sample_var_E` reads the law at the identity body:
$\llbracket \text{let } x = \text{sample } \mu \text{ in } x \rrbracket(1) = \mu$.

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
$$\llbracket \text{let } x = M \text{ in } K \rrbracket(\gamma) = \int \llbracket K \rrbracket(\gamma \otimes \delta_r) (\llbracket M \rrbracket \gamma)(dr)$$
the bound sub-distribution $\llbracket M \rrbracket \gamma$ replaces the constant prior. Unlike the sample
case, the step-1 collapse now genuinely consumes the comonoid copy of
the context (`em_pair_mor id` $\llbracket M \rrbracket$ feeds `γ` to *both* legs), so the law
holds at setlike unit-ball context points (`eD_let_collapse_setlike`).
Steps 2–4 are reused verbatim — none of them mention the bound measure.
The law is proved once at an *arbitrary* bound return object `B`
(`eD_let_collapse_setlike_obj` / `eD_let_int_obj` / `eD_let_mu_E_obj`,
with `M : tbase B` and the Pettis integral over `ar_carrier Ar B`); the
`tR`-bound forms below are its `B := R_obj` instances.

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

> The setlike hypothesis of the general law is harmless: in every
> consumer the let sits under binders whose environments are setlike by
> construction. The fused measure-on-$U$ form `eD_let_mu_E` is the exact
> shape the rejection-sampling *combinator* mass recurrence consumes
> (`theories/programs/ex_reject_model.v`, with `M = m @ a` the model
> applied to the input), and it is the proof engine of
> `condition_model_E`.

### The affine cascade and the sup-mass bridge (`affine_iter_closed`, `affine_iter_geom`, `affine_iter_cvg`, `fmeas_kleene_sup_U_E`)

The scalar core of every CBV mass headline. Given reals $a, q \geq 0$ and a
real sequence with $x_0 = 0$ and $x_{n+1} = a + q \cdot x_n$ — the
per-iterate mass of an affine Kleene chain — the closed form is the
partial geometric series $x_n = a \sum_{i < n} q^i$, with the geometric
form $x_n = a (1 - q^n) / (1 - q)$ away from $q = 1$ and
the limit $a / (1 - q)$ when $q < 1$.

```coq
(* theories/prelude/geom_series.v *)
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

The degenerate corner $q = 1, a = 0$, where the geometric form does not
apply, is covered separately by `affine_iter_deg_eq0`: every iterate
vanishes. The sup-mass bridge then converts a *limit of per-iterate
masses* into the *mass of the Kleene supremum*: for a unit-ball $\omega$-chain
$\nu : \mathbb{N} \to \mathit{fmeas}\ R\ X$ and a measurable $U$, the masses
`fmeas_mu (ν n) U` converge to the mass of `cone_sup_ball ν` at $U$
(`fmeas_kleene_sup_U_cvg`; definitionally `fmeas_sup_ball`, the HB
`isCone` instance of `fmeas.v`), so any limit *is* that mass by
Hausdorff uniqueness.

```coq
(* theories/mcones/fmeas.v (Section FMeasKleeneSup) *)
Lemma fmeas_kleene_sup_U_E (U : set X) (l : \bar R) :
  measurable U ->
  fmeas_mu (nu n) U @[n --> \oo] --> l ->
  fmeas_mu (cone_sup_ball nu nuch nub1 : fmeas R X) U = l.
```

> Together with the interleaved-chain laws of the recursion chapter
> (`fix_chain`), this is the complete recipe behind every CBV mass
> identity: reduce the denotation to a `cone_sup_ball` of per-iterate
> measures, derive the affine mass recurrence per iterate (via the
> let-at-sample law `eD_let_sample_mu_E` or the boolean dispatch), close
> the recurrence with `affine_iter_closed` / `affine_iter_cvg`, and land
> with `fmeas_kleene_sup_U_E`.

### The setlike-point kit (`coalg_d_setlike`, `coalg_e_setlike`, `coalg_str_one1`, `coalg_str_tensor_setlike`, `em_pair_mor_constE`, `adj_psi_at_setlike`, `eD_app_at_setlike`, `if_icones_at`, `linhom_fun_sup_ball`)

A point $x$ of a coalgebra $(P, \text{str})$ is *setlike* when $\text{str } x = x!$ —
the §9.7 reading "$x$ is a (sub-)Dirac". On setlike unit-ball points the
Eq-88 comonoid computes: the diagonal is the pure tensor square
(`coalg_d_setlike`) and the counit is the unit point
(`coalg_e_setlike`). The setlike points are closed under the `EM_prod`
tensor, and the unit point `one1` (`coalg_str_one1`), every Dirac of
`FMeas X`, and both boolean Diracs are setlike. The kit's workhorse
`em_pair_mor_constE` needs no setlike hypothesis at all: pairing the
identity with a constant computes at *every* point,
$\langle \text{id}, \text{const}\,c \rangle(\gamma) = \gamma \otimes c$.

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

The kit also pins the comonoid diagonals themselves: the §9.7 boolean
coalgebra's diagonal is the convex combination of the *diagonal* basis
tensors,
$d(x) = \text{bc}_t(x)\,(\delta_T \otimes \delta_T) + \text{bc}_f(x)\,(\delta_F \otimes \delta_F)$
at the true- and false-weights $\text{bc}_t$, $\text{bc}_f$ of a point of
the 2-point boolean cone (`bool_coalg_d_E` — the independent-product reading would
produce cross terms instead), and the `FMeas` diagonal sends a Dirac to
its diagonal tensor (`coalg_d_FMeas_dirac`).
The two basis corollaries `bool_coalg_d_true` and `bool_coalg_d_false`
are the diagonal read at $\delta_T$ and $\delta_F$ themselves — $d(\delta_T) = \delta_T \otimes \delta_T$ and
$d(\delta_F) = \delta_F \otimes \delta_F$ — which is what every branch-level computation of
the chapter actually rewrites with; both follow from `coalg_d_setlike`
at the basis points, since `bool_coalg_str` sends each of them to its
own promotion.

```coq
(* theories/programs/infra/cbv_anchors.v (Section AnchorKit) *)
(** Basis corollary: [d(δ_T) = δ_T ⊗ δ_T]. *)
Lemma bool_coalg_d_true :
  Lfun (coalg_d (@bool_cone_coalg R Ar)) bool_dirac_true =
  bool_dirac_true ⊗p bool_dirac_true.

(** Basis corollary: [d(δ_F) = δ_F ⊗ δ_F]. *)
Lemma bool_coalg_d_false :
  Lfun (coalg_d (@bool_cone_coalg R Ar)) bool_dirac_false =
  bool_dirac_false ⊗p bool_dirac_false.

(** The full diagonal:
    [d(x) = bc_t x · (δ_T ⊗ δ_T) + bc_f x · (δ_F ⊗ δ_F)]. *)
Lemma bool_coalg_d_E (x : bool_cone_car Ar) :
  Lfun (coalg_d (@bool_cone_coalg R Ar)) x =
  bool_case x (bool_dirac_true ⊗p bool_dirac_true)
              (bool_dirac_false ⊗p bool_dirac_false).

Lemma coalg_d_FMeas_dirac (X : ar_obj Ar) (r : ar_carrier Ar X) :
  Lfun (coalg_d (FMeas_coalgebra X)) (dirac_fmeas r) =
  dirac_fmeas r ⊗p dirac_fmeas r.
```

On top of the comonoid facts the same file owns the four *computation
laws* every CBV rider runs on, so that no example file has to restate
them: the `U ⊣ !̃` packaging of a lambda promotes at a setlike
environment (`adj_psi_at_setlike`), the application clause computes
there (`eD_app_at_setlike`, generic over the real object and its
carrier casts), the if-clause dispatches into the weighted co-pairing
`bool_case` (`if_icones_at`), and linhom-cone suprema are read
pointwise (`linhom_fun_sup_ball`, on `cone_sup_ball_irr` of
`theories/cones/omega_general.v`). Two per-iterate helpers ride along:
`kleene_prom_ball` / `kleene_prom_setlike` (every Kleene iterate of a
unit-ball body promotes to a setlike unit-ball point) and
`bool_case_mass` (the mass of a dispatch between a Dirac and a measure).

```coq
(* theories/programs/infra/cbv_anchors.v (Section AnchorKit) *)
(** The [U ⊣ !̃] packaging PROMOTES at setlike unit-ball points. *)
Lemma adj_psi_at_setlike (P : Coalgebra Ar) (B : ICone.type Ar)
    (g : icones_hom Ar (coalg_obj P) B) (gam : coalg_obj P) :
  cone_norm gam <= 1 -> Lfun (coalg_str P) gam = gam! ->
  Lfun (ch_mor (adj_psi (P := P) g)) gam = (Lfun g gam)!.
```

> This kit is what lets every program-level computation in the chapter
> proceed by evaluating morphism composites at concrete environment
> points, rather than by equational reasoning on morphisms. The two
> diagonal pins say the same thing twice, in the boolean cone and in
> `FMeas`: the §9.7 coalgebra duplicates a *sample*, not the measure —
> which is exactly the property the sharing-semantics anchors turn into
> a program-level statement.

### The sharing-semantics anchors (`let_bernoulli_pair_diag`, `let_sample_pair_diag`, `pair_bernoulli_indep`, `pair_sample_indep`)

The load-bearing program-level pin: `let x = Bernoulli(p) in (x, x)`
denotes the *diagonal* pushforward
$p \cdot (\delta_T \otimes \delta_T) + (1-p) \cdot (\delta_F \otimes \delta_F)$ — a shared sample, not the
independent square. The Dirac twin `let x = sample δ_{r₀} in (x, x)`
states the same for the sampler.

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
```

The contrast anchors pin the same semantics from the other side: two
*separate* draws, `(Bernoulli(p), Bernoulli(p))` and
`(sample µ, sample µ)`, denote the independent products $\text{bern} \otimes \text{bern}$
and $\mu \otimes \mu$. Together the two pairs make the sharing semantics of the
CBV `let` a regression property rather than a folklore expectation.

```coq
(* theories/programs/infra/cbv_anchors.v (Section ProgramAnchors) *)
(** The CONTRAST — two separate Bernoulli draws are independent. *)
Lemma pair_bernoulli_indep (p : R) (Hp0 : 0 <= p) (Hp1 : p <= 1) :
  linhom_fun
    (eD' (ne_pair (ne_bernoulli (G := nil) p Hp0 Hp1)
                  (ne_bernoulli (G := nil) p Hp0 Hp1))) one1 =
  bernoulli (Ar:=Ar) p Hp0 Hp1 ⊗p bernoulli (Ar:=Ar) p Hp0 Hp1.

(** The same for two separate [sample µ]. *)
Lemma pair_sample_indep (mu : fmeas R (ar_carrier Ar R_obj))
    (Hmu : cone_norm mu <= 1) :
  linhom_fun
    (eD' (ne_pair (ne_sample (G := nil) mu Hmu)
                  (ne_sample (G := nil) mu Hmu))) one1 =
  mu ⊗p mu.
```

> For a general prior $\mu$, the shared-`let` pair is the Pettis integral
> $\int (\delta_r \otimes \delta_r) \, d\mu(r)$ by the let-at-sample law `eD_let_sample_int`;
> the Dirac special case is the anchor, because it is the one a
> regression run can check without an integral. All four anchors are
> stated against the public interpreter `eD` through the definitional
> clause pins of `ppl_cbv.v` — never re-derived.

### The marginal kit at non-setlike points (`coalg_e_FMeas_prob`, `em_proj1_mor_unitE`, `em_proj1_mor_probE`, `Lfun_scaleE`, `one_dirac_ball`, `one_dirac_setlike`)

The setlike-point kit computes the Eq-88 comonoid at (sub-)Dirac points;
the marginal identities also need it where the *discarded* component is
not setlike — a discarded probability measure, a discarded score scalar.
The counit of the §9.7 coalgebra `FMeas X` sends every probability
measure to `one1`: Diracs are setlike, and the Dirac-to-integral lift
plus the Pettis equation on `cone_one` reads off the total mass.

```coq
(* theories/programs/cbv_marginals.v (Section FMeasCounitKit) *)
Lemma coalg_e_FMeas_prob (X : ar_obj Ar) (nu : FMeas X) :
  fmeas_mu nu [set: ar_carrier Ar X] = 1%E ->
  Lfun (coalg_e (FMeas_coalgebra X)) nu = one1.
```

The two projection lemmas read off the consequences for the cartesian
first projection — discarding a scored `tunit` component scales the kept
value by that scalar ($x \otimes s \mapsto s \cdot x$,
`em_proj1_mor_unitE`), while discarding a probability measure leaves it
unchanged ($x \otimes \nu \mapsto x$, `em_proj1_mor_probE`) — and
`Lfun_scaleE` (the `linearZ` field of the
underlying `cones_hom`) moves the resulting `precone_scale` factor
through any morphism.

```coq
(* theories/programs/cbv_marginals.v (Section EMProjKit) *)
(** Discarding a [tunit]-typed component weighs by the scalar. *)
Lemma em_proj1_mor_unitE (P : Coalgebra Ar)
    (x : coalg_obj P) (s : cone_one_car Ar) :
  Lfun (em_proj1_mor (R:=R) P (EM_term : Coalgebra Ar)) (x ⊗p s) =
  precone_scale (c1_val s) x.

(** Discarding an [FMeas]-typed PROBABILITY changes nothing. *)
Lemma em_proj1_mor_probE (P : Coalgebra Ar) (X : ar_obj Ar)
    (x : coalg_obj P) (nu : FMeas X) :
  fmeas_mu nu [set: ar_carrier Ar X] = 1%E ->
  Lfun (em_proj1_mor (R:=R) P (FMeas_coalgebra X)) (x ⊗p nu) = x.

(** Morphism application commutes with [precone_scale]. *)
Lemma Lfun_scaleE (B C : ICone.type Ar) (h : icones_hom Ar B C)
    (c : {nonneg R}) (x : B) :
  Lfun h (precone_scale c x) = precone_scale c (Lfun h x).
```

The kit closes with the environment point every single-binder
computation is evaluated at — $\text{one1} \otimes \delta_r$, the context of one
`tR`-binding — shown to be a setlike unit-ball point, by
`coalg_str_tensor_setlike` at `coalg_str_one1` and the Dirac
coalgebra law.

```coq
(* theories/programs/cbv_marginals.v (Section OneDiracEnv) *)
Lemma one_dirac_ball (r : ar_carrier Ar R_obj) :
  cone_norm ((one1 : cone_one_car Ar) ⊗p dirac_fmeas r) <= 1.

Lemma one_dirac_setlike (r : ar_carrier Ar R_obj) :
  Lfun (coalg_str (EM_prod (EM_term : Coalgebra Ar)
                     (FMeas_coalgebra R_obj)))
       ((one1 : cone_one_car Ar) ⊗p dirac_fmeas r) =
  ((one1 : cone_one_car Ar) ⊗p dirac_fmeas r)!.
```

> Discarding is not free in `EM(!)`: it is the comonoid counit, and on
> `FMeas` the counit weighs by the argument's *total mass*. That is why
> `em_proj1_mor_probE` carries a probability hypothesis, and why
> `em_proj1_mor_unitE` is how the weight of a discarded `tunit`-typed
> score result becomes a `precone_scale` factor in the score-posterior
> proof rather than disappearing.

### The score posterior and its normalisation (`ex_score_posterior_cbv_E`, `ex_score_posterior_cbv_mass`, `ex_reject_normalises_score`)

The denotation of `ex_score_posterior`
(`let m = sample µ in let _ = score f m in m`) at the unit context point
is, on every measurable $U$, the prior reweighted by the evidence
density — *not* normalised; the mass corollary
`ex_score_posterior_cbv_mass` gives the total evidence $\int f \, d\mu$. The
identity is proved against the CBV interpreter `eD` in
`theories/programs/cbv_marginals.v`, reparameterized over a
bundled `probObj` `P`, a bundled prior `pmeas` and a bundled `testfn`.

```coq
(* theories/programs/cbv_marginals.v (Section ScorePosterior) *)
Theorem ex_score_posterior_cbv_E (U : set (ar_carrier Ar R_obj))
    (mU : measurable U) :
  fmeas_mu
    (linhom_fun (ex_score_posterior_cbv P R_to_carrier_meas pm f) one1) U =
  \int[fmeas_mu mu]_(r in U) (f (cR r))%:E.
```

This is the first of the headline identities about the non-recursive
sampling/scoring examples of `theories/programs/examples.v`, and they
all follow one route: the let-at-sample law turns each
`let x = sample µ in …` prefix into a Pettis integral over Diracs of the
prior; dereliction / evaluation at setlike test points pushes inside the
integral (`icones_hom_pres_int` / `linhom_int_eval`); and the integrand
computes pointwise through the setlike-point kit, closing with a Dirac
integral (`icone_integral_dirac_fmeas` or `icone_integral_fmeas_E`).

Combining the posterior identity with the rejection-sampling master
identity `ex_reject_master` of
`theories/programs/ex_reject_headline.v` gives the normalisation
pairing: at a probability prior ($\mu(\mathit{setT}) = 1$), the rejection-sampling
denotation times the total evidence *is* the score denotation.

```coq
(* theories/programs/cbv_marginals.v (Section ScorePosterior) *)
Theorem ex_reject_normalises_score
    (Hmu1 : fmeas_mu mu [set: ar_carrier Ar R_obj] = 1)
    (U : set (ar_carrier Ar R_obj)) (mU : measurable U) :
  (\int[fmeas_mu mu]_(r in [set: ar_carrier Ar R_obj]) (f (cR r))%:E) *
  fmeas_mu
    (linhom_fun (ex_reject_cbv P R_to_carrier_meas pm f) one1) U =
  fmeas_mu
    (linhom_fun (ex_score_posterior_cbv P R_to_carrier_meas pm f) one1) U.
```

> `score` produces the unnormalised posterior, rejection sampling
> produces the normalised one, and the theorem connects the two
> *programs* exactly — not two hand-written measures. The
> predicate-based counterpart, at an arbitrary model and a boolean
> program predicate, is `reject_normalises_condition`; this pairing is
> the soft, score-based reading at the sampler model, proved
> independently.

### The marginals of random functions (`ex_random_constant_cbv_marginal`, `ex_random_constant_cbv_marginal_dirac`, `ex_random_constant_cbv_marginal_mass`, `ex_random_linear_cbv_marginal`, `rl_inner_marginal`)

The denotation of `ex_random_constant` (`let c = sample µ in λx. c`) is
a promoted function value; derelicting it and evaluating at a test point
`x` recovers the prior $\mu$ — *provided `x` is a probability*
(`fmeas_mu x setT = 1`). Dirac test points are probabilities, giving the
corollary `ex_random_constant_cbv_marginal_dirac`; the per-$U$ reading
is `ex_random_constant_cbv_marginal_mass`.

```coq
(* theories/programs/cbv_marginals.v (Section RandomConstantMarginal) *)
Theorem ex_random_constant_cbv_marginal (x : FMeas R_obj) :
  fmeas_mu x [set: ar_carrier Ar R_obj] = 1%E ->
  linhom_fun
    (Lfun (der (Lty tR' tR'))
       (linhom_fun (ex_random_constant_cbv R_carrier_meas
                      R_to_carrier_meas pm) one1)) x = mu.
```

The probability hypothesis is honest, not an artifact: the closure
discards its argument, and discarding in `EM(!)` is the comonoid counit,
which on `FMeas` weighs the kept output by the argument's *total mass*
(`coalg_e_FMeas_prob` / `em_proj1_mor_probE`) — so at `x = 0` the
marginal is `0`, not $\mu$, and only mass-1 test points are silently
discarded. The random-affine model
`ex_random_linear` (`let m = sample µ in let b = sample µ in λx. m·x + b`),
derelicted and evaluated at a Dirac test point `δ_{r0}`, is on every
measurable $U$ the iterated-integral measure $\int\int \delta_{m \cdot r_0+b}(U) \, \mu(db) \, \mu(dm)$ —
the joint pushforward of two independent prior draws along
$(m, b) \mapsto m \cdot r_0 + b$.

```coq
(* theories/programs/cbv_marginals.v (Section RandomLinearMarginal) *)
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

> The inner one-sample layer is `rl_inner_marginal`, and the arithmetic
> computes on Diracs through the `add_lift` / `mul_lift` Dirac rules.
> Both marginals follow the route of the score posterior — the
> let-at-sample law, then pointwise evaluation through the setlike-point
> kit — and `ex_random_linear` is reused verbatim as the prior of the
> Bayesian-linear model evidence.

### The Bayesian-linear model evidence (`ex_bayes_linear_cbv_evidence`, `ex_bayes_linear_cbv_evidence2`, `obs_fold_at`)

The headline of `theories/programs/cbv_marginals.v`:
`ex_bayes_linear l` samples the random affine model *once* (it is
literally `ex_random_linear`), binds it to `"f"`, conditions it on each
element of the meta-level list `l : seq (obs R)` in turn
(`iter_condition`: each observation `o` scores the model's value at the
known input `obs_x o` by the density `obs_d o`), and returns `#"f"` —
the posterior over functions. The theorem, for a *general* $l$: the
comonoid counit ("total mass") of the function-space denotation is the
**model evidence**.

```coq
(* theories/programs/cbv_marginals.v (Section BayesLinearEvidence) *)
Theorem ex_bayes_linear_cbv_evidence (l : seq (obs R)) :
  ((c1_val (Lfun (coalg_e (tyD_cbv tF))
      (linhom_fun
         (ex_bayes_linear_cbv P R_to_carrier_meas pm l)
         one1)))%:num)%R =
  fine (\int[fmeas_mu mu]_(m in [set: ar_carrier Ar R_obj])
     (fine (\int[fmeas_mu mu]_(b in [set: ar_carrier Ar R_obj])
        ((\prod_(o <- l) obs_d o (cR m * obs_x o + cR b))%R)%:E))%:E).
```

The 2-observation corollary `ex_bayes_linear_cbv_evidence2` writes the
product literally. The CBV content: the let-bound *function value* is
shared — duplicated by the comonoid `coalg_d` at a prom-point of the
function cone — across all observations and the return, so every score
weighs the *same* sampled function; the workhorse `obs_fold_at` factors
the per-observation scalar weights out of the fold one at a time, and
two let-at-sample integrations close the evidence.

> This is where the sharing semantics pinned by
> `let_bernoulli_pair_diag` pays off at scale: every observation scores
> the *same* sampled function, so an independent-product reading of the
> comonoid would hand each observation a freshly sampled model instead.
> The per-program proofs are worked example-by-example in the
> [Examples tab](../../examples/index.html).

### The conditioning law and the equivalence (`condition_model_E`, `condition_E`, `reject_normalises_condition`)

The score-posterior identity, promoted to an operator: the conditioning
combinator `ne_condition` (`theories/programs/reject_condition.v`) takes
a boolean program predicate `f : tb → tbool` and a model `m : ta → tb`,
both as program arguments, and returns the conditioned model
`λa. let x = m a in let _ = (if f x then () else fail) in x` — no coin,
no `Score`, the test applied by ordinary application, `f x`.
Its counterpart is `reject_prog := ne_reject pred_prog model_prog ()`,
where `ne_reject = λf. fix rx. λm. λa. let x = m a in if f x then x else rx m a`
resamples until the predicate accepts, using no `fail` and no `Score`.
The predicate's value at a returned point `r` is `sdist r`, a point of
the 2-point cone, and the reweighting scalar is its true-weight
`(bc_t (sdist r))%:num`, written $t$ below. The conditioning law states
that at a unit-ball predicate value `fpred!`, a unit-ball model value
`g!` and a setlike unit-ball input `a₀`, writing $\nu_M := g(a_0)$ for the
model's output sub-distribution, the conditioned model's output is
$\nu_M$ reweighted by $t$ — `ex_score_posterior_cbv_E` with an arbitrary
model and an arbitrary predicate in place of `sample µ` and a fixed
test function.

```coq
(* theories/programs/ex_reject_model.v (Section RejectModelCompat) *)
Theorem condition_model_E (U : set (ar_carrier Ar B))
    (mU : measurable U) :
  fmeas_mu (cond_model_denot R_to_carrier_meas fpred g a0) U =
  \int[fmeas_mu (reject_model_dist g a0)]_(r in U) ((bc_t (sdist r))%:num)%:E.
```

The proof engine is the object-generic let-law `eD_let_int_obj` at
$\nu_M$ — the statements hold at an arbitrary return object `B` — with the
assert clause computing on Diracs through `bool_case` on `sdist r` and
the returned variable projected through `em_proj1_mor_unitE` /
`Lfun_scaleE`; `condition_model_mass` is the total-mass corollary. In
the readable $\llbracket \cdot \rrbracket$ brackets (Section ReadableHeadlines, over an
arbitrary thunked model `model_prog := λ_. Mbody`, an arbitrary
predicate `pred_prog := λx. Fbody`, with `model_run := model_prog ()`
and `condition_prog := ne_condition pred_prog model_prog ()`), the law
is `condition_E`, and combining it with the rejection master identity
`reject_prog_master` for `reject_prog` gives the equivalence —
rejection sampling computes the conditioned model's normalised
distribution.

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

Writing $Z := 1 - \llbracket \text{model\_run} \rrbracket(\mathit{setT}) + \int t \, d\llbracket \text{model\_run} \rrbracket$ for the factor
displayed above, the division form `reject_prog_computes_condition`
divides through at $0 < Z$, and the probability-model form
`reject_normalises_condition_prob` identifies $Z$ with the
model evidence $\llbracket \text{condition\_prog} \rrbracket(\mathit{setT})$, itself the content of
`condition_prog_evidence`.

> The same equivalence in its soft, score-based reading — a `testfn`
> instead of a predicate, at the sampler model — is
> `ex_reject_normalises_score`. On the regression side, `ex_bayes_linear`
> is *defined* as iterated score-based conditioning (`condition_at` /
> `iter_condition`, with the named anchor
> `ex_bayes_linear_is_iter_condition` now definitional,
> `theories/programs/examples.v`), so the two readings of conditioning
> meet on the same models; the full narrative lives on the
> [Examples tab](../../examples/index.html).

## The boolean cascade

The 2-point cone of [paper §4.4 / Theorem
4.24](../../paper/sections/sec-4.html) — the coproduct $1 \oplus 1$ — is
built concretely as `bool_cone_car Ar : {nonneg R} × {nonneg R}` with
norm $\lVert (p, q) \rVert = p + q$. Around that carrier the development runs a
cascade of four stages, each one the input of the next: the carrier
with its full HB tower, the universal co-pairing `bool_case` and its
analytic obligations, the packaging of the co-pairing as a linhom and
as an icones_hom, and finally a hand-rolled §9.7-style `!`-coalgebra
structure that gives `tbool` its shared-sample semantics.

| Construction | Statement | Rocq |
|---|---|---|
| The 2-point cone | The carrier $(p, q)$ of non-negative weights on true and false, with norm $p + q$ and the two Dirac basis points, carrying the full `ICone` tower. | `bool_cone_car`, `bool_dirac_true`, `bool_dirac_false` — theories/icones/bool_cone.v |
| The universal co-pairing | The eliminator $[a, b](x) = bc_t(x) \cdot a + bc_f(x) \cdot b$, with its Dirac equations and its linearity, $\omega$-continuity, norm, path and integral obligations. | `bool_case`, `bool_case_true`, `bool_case_false` — theories/icones/bool_cone.v |
| Icones-hom packaging | The co-pairing packaged at each categorical level, and its α/β sum decomposition. | `bool_case_linhom`, `bool_case_icones_hom`, `alpha_linhom` — theories/exp/bool_case_hom.v |
| The coalgebra on the 2-point cone | A `!`-coalgebra structure on the 2-point cone mirroring the §9.7 `FMeas` coalgebra, with the basis-point dispatch lemma that discharges its two laws. | `bool_coalg_str`, `bool_cone_coalg`, `bool_cone_dispatch` — theories/programs/infra/bool_cone_coalg.v |

### The 2-point cone (`bool_cone_car`, `bool_dirac_true`, `bool_dirac_false`)

The boolean value cone is the pair $(p, q)$ of non-negative weights on
true and false, with norm $\lVert (p, q) \rVert = p + q$ — concretely the paper
§4.4 / Thm 4.24 coproduct `cone_one_car` $\oplus$ `cone_one_car`, with the two
Dirac basis points as the boolean values.

```coq
(* theories/icones/bool_cone.v *)
Record bool_cone_car (dummy : MeasSubcat R) : Type :=
  MkBoolCone { bc_t : {nonneg R}; bc_f : {nonneg R} }.

Local Notation T := (bool_cone_car Ar).

Definition bool_dirac_true : T := MkBoolCone Ar 1%:nng 0%:nng.
Definition bool_dirac_false : T := MkBoolCone Ar 0%:nng 1%:nng.

Lemma bool_dirac_true_norm : cone_norm bool_dirac_true = 1.
Lemma bool_dirac_false_norm : cone_norm bool_dirac_false = 1.
```

The same file then equips the carrier, stage by stage, with the
`isPrecone`, `isCone`, `isMCone` and `isICone` instances, so that
`bool_cone_car Ar` is an `ICone.type Ar` and not merely a record of two
scalars.

> A paper writes the boolean object as the coproduct $1 \oplus 1$ and reads
> its universal property off the coproduct diagram; here the carrier is
> fixed concretely so that the whole HB tower can be registered on it by
> hand. The unused `dummy : MeasSubcat R` parameter is the trick already
> used for `cone_one_car`: it forces `Ar` to survive section discharge,
> without which the `isMCone` instance cannot be registered. Everything
> in the rest of the cascade — `bool_case`, `bool_cone_coalg`, and the
> CBV reading of `tbool` — is built on this carrier.

### The universal co-pairing (`bool_case`, `bool_case_true`, `bool_case_false`)

The co-pairing $[a, b](x) = bc_t(x) \cdot a + bc_f(x) \cdot b$ — writing
$bc_t(x)$, $bc_f(x)$ for the true- and false-weight components of
$x = (p, q)$ — realises the
coproduct universal property of [paper §4.4 / Thm
4.24](../../paper/sections/sec-4.html): it restores the branch values
on the two basis points, is linear in `x`, $\omega$-continuous on the unit
ball, norm-bounded, and preserves measurable paths and integrals.

```coq
(* theories/icones/bool_cone.v *)
Local Notation T := (bool_cone_car Ar).

Definition bool_case (x : T) (a b : A) : A :=
  precone_add
    (precone_scale (bc_t x) a)
    (precone_scale (bc_f x) b).

Lemma bool_case_true (a b : A) : bool_case bool_dirac_true a b = a.
Lemma bool_case_false (a b : A) : bool_case bool_dirac_false a b = b.

Lemma bool_case_linear (a b : A) : is_linear (fun x : T => bool_case x a b).

Lemma bool_case_omega_continuous
    (a b : A) (Ha : cone_norm a <= 1) (Hb : cone_norm b <= 1) :
  is_omega_continuous (fun x : T => bool_case x a b).

Lemma bool_case_norm_le1
    (a b : A) (Ha : cone_norm a <= 1) (Hb : cone_norm b <= 1) (x : T) :
  cone_norm (bool_case x a b) <= cone_norm x.
```

The two remaining `ICone`-level obligations are structural rather than
algebraic: `bool_case_pres_path` sends a measurable path into the
2-point cone to a measurable path in the target, and
`bool_case_pres_int` commutes the co-pairing with `icone_integral`.

The `_gen` variants drop the unit-ball hypotheses on the branches —
`bool_case_omega_continuous_gen`, `bool_case_pres_path_gen`,
`bool_case_pres_int_gen` — and they are the *primary* proofs: the plain
`bool_case_omega_continuous`, `bool_case_pres_path`, `bool_case_pres_int`
are one-line derived instances of them, kept under their own names
because the unit-ball packaging and the CBV anchors index on those
signatures. The norm bound is `bool_case_norm_le_max`, used through its
canonical instance `bool_case_norm_le_max0` at
$M := \max(\lVert a\rVert, \lVert b\rVert) \vee 0$ (and its unit-ball
corollary `bool_case_norm_le_max0_ball`, which is the shape
`linhom_pre_bounded` / `linhom_norm_sup_lub` want); the generalised test
measurability `test_meas_gen` of `theories/mcones/mcone.v` is what lets
the path-preservation proofs drop the unit ball on test scrutinees.

> The two Dirac equations are the coproduct universal property in
> elementary form: a paper would obtain them from the diagram and stop
> there, whereas here they are the cheap part and the analytic
> obligations — $\omega$-continuity through the sup on the unit ball, path
> measurability, Pettis-style integral commutation — are the work. The
> plain and `_gen` families are two signatures over one proof: the plain
> names are what a norm-$\leq 1$ caller wants to see, the `_gen` names are
> where the mathematics actually lives, and the unit-ball hypotheses
> survive in the plain statements only as the interface the unit-ball
> packaging is written against.

### Icones-hom packaging (`bool_case_linhom`, `bool_case_icones_hom`, `alpha_linhom`, `beta_linhom`)

The co-pairing is packaged once at each categorical level in
`theories/exp/bool_case_hom.v`: as a linhom
`bool_case_linhom : bool_cone` $\multimap$ `A` and as an icones_hom
`bool_case_icones_hom`. The packaging work is done once, in the
unit-ball-free `bool_case_linhom_gen`; `bool_case_linhom` *is*
`bool_case_linhom_gen`, with the norm hypotheses retained in the
signature because the $\lVert\cdot\rVert \leq 1$ bound
`bool_case_linhom_norm_le1` — what the `linhom_icones` bridge consumes —
does need them.

```coq
(* theories/exp/bool_case_hom.v *)
Local Notation T := (bool_cone_car Ar).

(** Unit-ball-free packaging; uses [bool_case_norm_le_max0_ball]. *)
Definition bool_case_linhom_gen (a b : A) : linhom_car Ar T A.

Definition bool_case_linhom
    (a b : A) (Ha : cone_norm a <= 1) (Hb : cone_norm b <= 1) :
    linhom_car Ar T A :=
  bool_case_linhom_gen a b.

Definition bool_case_icones_hom
    (a b : A) (Ha : cone_norm a <= 1) (Hb : cone_norm b <= 1) :
    icones_hom Ar T A.

Definition alpha_linhom (a : A) : linhom_car Ar T A :=
  bool_case_linhom_gen a precone_zero.

Definition beta_linhom (b : A) : linhom_car Ar T A :=
  bool_case_linhom_gen precone_zero b.

Lemma bool_case_linhom_gen_alpha_beta (a b : A) (x : T) :
  linhom_fun (bool_case_linhom_gen a b) x =
  precone_add (linhom_fun (alpha_linhom a) x) (linhom_fun (beta_linhom b) x).
```

The general variant decomposes as `bool_case_linhom_gen` $a \, b =$ `alpha_linhom` $a +$ `beta_linhom` $b$ (`bool_case_linhom_gen_alpha_beta`, same
file) — the $\alpha/\beta$ decomposition that reduces its integral- and
path-preservation obligations to the two scaled-projection linhoms
`alpha_linhom` / `beta_linhom`.

> No new mathematics happens in this file; it only lifts `bool_case`
> through the two packaging layers so the eliminator can appear as a
> morphism in the categorical constructions. The α/β split is what makes
> the unit-ball-free packaging go through: `bool_case` is not bilinear in
> the pair of branches `(a, b)`, but it is a sum of two pieces each of
> which is linear in one branch. The CBV consumer of the linhom
> packaging is `if_icones` (together with `if_under`) of
> `theories/programs/ppl_cbv.v`, in the call-by-value semantics chapter;
> the icones_hom packaging is consumed by `bool_coalg_str`.

### The coalgebra on the 2-point cone (`bool_coalg_str`, `bool_cone_coalg`, `bool_cone_dispatch`)

The 2-point cone carries a hand-rolled `!`-coalgebra structure
`bool_coalg_str : bool_cone` $\multimap$ `!bool_cone` mirroring [Theorem
9.7](../../paper/entries/thm-9-7.html)'s `FMeas_coalgebra`: the §9.7
integral $\text{Coalg}_X(\mu) = \int \text{prom}(\delta_x) \, d\mu(x)$ degenerates on the two-point
carrier to the finite sum $p \cdot \delta_T + q \cdot \delta_F \mapsto p \cdot \text{prom}(\delta_T) + q \cdot \text{prom}(\delta_F)$.
Both branches are legitimate co-pairing data because a promoted
unit-ball point is itself unit-ball — `prom_ball`
(`theories/exp/bang.v`), the ball law of the `!`-promotion, which the
two Dirac branches instantiate.
(Here `prom` $x = x!$ promotes a point into `!`, `der : !B ⊸ B` is the
`!`-comonad's dereliction and `dig : !B ⊸ !!B` its comultiplication.)

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

(** On the false basis: [bool_coalg_str(δ_F) = prom(δ_F)]. *)
Lemma bool_coalg_str_false :
  Lfun bool_coalg_str bool_dirac_false = prom (bool_dirac_false : T).

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

(** Pointwise expansion: [x = bool_case x δ_T δ_F] for every [x]. *)
Lemma bool_cone_basis_expand (x : T) :
  x = bool_case x bool_dirac_true bool_dirac_false.

(** Sanity pins: the packaged coalgebra is the expected pair. *)
Lemma bool_cone_coalg_obj : coalg_obj bool_cone_coalg = T.

Lemma bool_cone_coalg_str_E : coalg_str bool_cone_coalg = bool_coalg_str.
```

```coq
(* theories/exp/bang.v *)
(** For [‖x‖ ≤ 1], the promoted point [x!] is in the unit ball of [!B]. *)
Lemma prom_ball (B : ICone.type Ar) (x : B) :
  cone_norm x <= 1 -> cone_norm (prom x) <= 1.
```

This is the structure that makes `tyD_cbv tbool` give *shared-sample*
semantics: the comonoid induced on $\llbracket$`tbool`$\rrbracket$ is the diagonal
pushforward, so a duplicated boolean is shared rather than
independently re-sampled — the four-point product the cofree
`bang_cofree` structure would give — as pinned at program level by
`let_bernoulli_pair_diag`. The two coalgebra laws
(`bool_coalg_counit`, `bool_coalg_coassoc`) reduce on the basis points
to the comonad identities `der` $\circ$ `prom` $=$ `id` and `dig` $\circ$ `prom` $=$ `prom` $\circ$
`prom`, dispatched by the universal-property extensionality lemma
`bool_cone_dispatch` (any two linear morphisms out of the 2-point cone
agreeing on `δ_T` and `δ_F` are equal) — and `bool_cone_dispatch` is
itself true because of `bool_cone_basis_expand`, the pointwise identity
$x = \text{bool\_case}\,x\,\delta_T\,\delta_F$: every point of the 2-point cone *is* the
co-pairing of the two basis points weighted by its own coordinates, so
linearity carries agreement on the basis to agreement everywhere. Two
`by []` sanity pins record what the packaged `Coalgebra` actually is —
`bool_cone_coalg_obj` (its carrier is `bool_cone_car Ar`) and
`bool_cone_coalg_str_E` (its structure map is `bool_coalg_str`) — so a
refactor of the packaging breaks in a named lemma.

> Theorem 9.7 builds the coalgebra on `FMeas X` for a measurable space
> `X`; the boolean type has no `measurableType` backing in this
> development, so the structure is rebuilt by hand on the concrete
> two-point carrier, where the defining integral collapses to a two-term
> sum. The choice is semantically load-bearing rather than cosmetic — it
> is what separates shared-sample from independent-product readings of a
> duplicated boolean. `bool_cone_dispatch` is the workhorse of the file:
> both coalgebra laws are discharged by checking the two basis points,
> which is the whole benefit of having built the cone concretely.

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

The recursion equation `fix` $F = F ($ `fix` $F)$ is proven where it carries
semantic content, at two levels. At the value level,
`fix_value_unfold` (`theories/programs/infra/em_fix_value.v`) states
`der` $(F($ `prom` $($ `fix_value` $F)) = $ `fix_value` $F$ as a *morphism-free*
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

One entry of the table below is a *scope* statement rather than a
deferral, and reads wrongly as a hole if it is not said out loud:
$EM(!)$ is not cartesian closed, and is not expected to be. That is a
structural fact about Eilenberg–Moore categories of a linear-exponential
comonad, not a diagram chase left undone. What $EM(!)$ *is* — cartesian,
unconditionally (`EMComon_all`), with the linear side reached by the
monoidal adjunction `ICones_CBV` — is exactly what the linhom-valued
reading of this chapter consumes: a program denotes a linear morphism
between the *carriers*, so the function type never has to be an
exponential *in* $EM(!)$. Cartesian closure lives on the other side of
Melliès §7.4, in the co-Kleisli category — the `SCones` of paper §7,
whose `SCones_CCC` record is on the [Paper tab](../paper/).

| Item | What it is | Why not yet |
|---|---|---|
| External semantic equivalence | A correspondence with another formalised semantics or a real PPL implementation (ProbProg / Pyro / Stan). | The correctness statements in this development are denotational identities at the categorical level. |
| Cartesian *closure* of $EM(!)$ | An exponential object $Q^P$ inside the Eilenberg–Moore category, making $(EM(!), \otimes, 1)$ a CCC the way `SCones` is one. | Not a gap: $EM(!)$ of a linear-exponential comonad is cartesian (`EMComon_all`, `EM_Cartesian` — theories/cbv/em_cartesian.v) but is not cartesian closed and is not expected to be. The linhom-valued interpretation needs only the cartesian structure plus the SMCC of `ICone`; cartesian closure is the co-Kleisli side's property (`SCones_CCC` — theories/stable/scones_ccc.v). |
| Adequacy, normalization, full abstraction | The operational metatheory: an operational semantics for `named_expr`, a soundness/adequacy pair against `eD`, and a full-abstraction result. | These need an operational semantics and a definability argument, neither of which a denotational model supplies; nothing in this development is stated operationally. |
| Coproducts beyond the boolean case | A general sum type $t_1 + t_2$ with injections and case analysis, of which `tbool` would be the two-point instance. | The cones model has no general coproduct; what exists is the concrete 2-point cone `bool_cone_car` (theories/icones/bool_cone.v) with its hand-built coalgebra and universal co-pairing `bool_case`, which is enough for branching but does not generalise to arbitrary summands. |
| A Moggi metalanguage | An explicit value/computation split — a computation type constructor $T\tau$ with `return`/`bind`, in the style of the computational metalanguage or of call-by-push-value. | Orthogonal to the framing adopted here: `eD` is linhom-valued and comonoid-primitive, there is no `Tobj` wrapper on the codomain of `tfun`, and no monad appears anywhere in the interpretation. A metalanguage layer would be a second interpretation, not a refinement of this one. |

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
  rocq top -Q theories Icones -l theories/cbv/diag_bilinear_tensor.v
echo "Print Assumptions ex_score_posterior_cbv_E." | \
  rocq top -Q theories Icones -l theories/programs/cbv_marginals.v
echo "Print Assumptions ex_reject_normalises_score." | \
  rocq top -Q theories Icones -l theories/programs/cbv_marginals.v
echo "Print Assumptions ex_random_constant_cbv_marginal." | \
  rocq top -Q theories Icones -l theories/programs/cbv_marginals.v
echo "Print Assumptions ex_random_linear_cbv_marginal." | \
  rocq top -Q theories Icones -l theories/programs/cbv_marginals.v
echo "Print Assumptions ex_bayes_linear_cbv_evidence." | \
  rocq top -Q theories Icones -l theories/programs/cbv_marginals.v
echo "Print Assumptions fix_comb_iso_prom_E." | \
  rocq top -Q theories Icones -l theories/programs/infra/em_fix_mr.v
echo "Print Assumptions eD_gaussian_sample_agree." | \
  rocq top -Q theories Icones -l theories/programs/kernel_anchors.v
echo "Print Assumptions ex_gaussian_walk_mass." | \
  rocq top -Q theories Icones -l theories/programs/kernel_anchors.v
```

Each command reports only `propositional_extensionality`,
`functional_extensionality_dep` and
`constructive_indefinite_description` (the classical-logic axioms of
`mathcomp-analysis`). Per-entry pages embed the precise identifier
name, file, and a GitHub link to the Rocq source.

For the example programs and their mass / marginal / PMF identities,
see the [Examples tab](../examples/).
