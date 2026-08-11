# End-to-end PPL example programs

Each surface program of `theories/programs/examples.v` is reproduced
here together with its correctness identities, all proved against the
call-by-value interpreter `eD` of `theories/programs/ppl_cbv.v`. The
programs are written in the direct-style `ppl_named` custom entry of
`theories/programs/ppl.v` (brackets `[ … ]` enter the entry; curly
braces `{ x }` escape back to plain Rocq), and together they exercise
every constructor of the language. A call-by-name interpretation of
the same surface programs is preserved on the `cbn-track` branch; main
is CBV-only.

The centrepiece is the conditioning/rejection pair. `condition f m`
(`ne_condition`) is the declarative operator: run the model, keep the
output with the acceptance probability of the boolean program predicate
`f`, return it. `reject f m` (`ne_reject`) is the executable sampler for
the same target: run the model, accept the output when `f` says so,
retry on rejection. The theorem `reject_normalises_condition`
(`theories/programs/ex_reject_model.v`) states that rejection sampling
computes the conditioned model's normalised distribution, writing
$\llbracket e \rrbracket$ throughout for the CBV denotation of a program `e`:
$Z \cdot \llbracket\text{reject}\,f\,m\rrbracket U = \llbracket\text{condition}\,f\,m\rrbracket U$ with
$Z := 1 - \nu_M(\text{setT}) + \int t\,d\nu_M$, for an arbitrary probabilistic
model — a function value that is itself free to contain samples,
scores and recursion. The hard-coded sampler `ex_reject` runs the same
argument at the simplest model with a `testfn` coin instead of a
predicate (`ex_reject_master`), and the combinator's own sampler
instance is `ex_reject_comb_sampler_master`. The non-recursive
programs carry
closed-form CBV marginal identities, up to the model evidence of a
higher-order Bayesian linear regression
(`ex_bayes_linear_cbv_evidence`,
`theories/programs/cbv_marginals.v`), itself re-read as iterated
conditioning (`ex_bayes_linear_is_iter_condition`,
`theories/programs/examples.v`).

The surface layer the programs are written in — the constant coin
`Bernoulli [| p |]` over a real literal, the value coin `Bernoulli e`
and the score `Score e` over the probability type `tProb`, the
`tProb`-producing primitives `Sigmoid e` / `Gausslik e { s , y }` /
`Gt0 e` / `test f e` / `Const pr e`, the Bayesian-conditioning
operator `observe Gaussian e { s } y ≡ Score (Gausslik e { s , y })`,
measurable function application `Meas { f , Hf } e`, bundled
distributions `sample m`, the runtime-parameter forms
`Gaussian( e1 , e2 )` / `Uniform( e1 , e2 )` (the constructors
`ne_gaussian` / `ne_uniform` over the `pkernel` layer), the comparison
coin `e1 > e2`, and OCaml-style `let rec` — where `Sigmoid`,
`Gausslik`, `Gt0`, `test` (the abstract
test-function coin, folding the `po_into` factoring of a bundled test
function `f : testfn` into `ptest`) and `Const` push a real value into
the probability type `tProb` (and `InclP` reads it back) — is
documented on the [PPL tab](../ppl/) and demoed end to end by
`ex_surface_demo` / `ex_surface_walk`
(`theories/programs/examples.v`).

Four chapters, in reading order. *Basic sampling and scoring* takes
the three non-recursive programs — two random functions and one scored
parameter — and pins each to a closed-form CBV marginal. *Runtime-parameter
distributions* puts a program-computed value in a parameter slot: the
higher-order Bayesian linear regression with its model evidence and its
reading as iterated conditioning, and the two-level Gaussian hierarchy
that a bundled-measure surface cannot express. *Recursive probabilistic
examples* turns to `ne_fix` and `ne_fix_mr`: bare divergence, the
geometric law atom by atom, almost-sure escape and its `p = 0` corner,
and mutual recursion at a pair of function types. *Conditioning and
rejection sampling* runs the declarative and the executable operator
side by side — the conditioning law, the rejection master identity at
the model and program levels, the equivalence theorem joining them, and
the sampler instance `ex_reject` with its normalised posterior.

The paper-side correspondence (§§ 2–9 ↔ Rocq) lives on the
[Paper tab](../paper/); the PPL infrastructure (the surface inductive,
the CBV interpretation, the fixpoint machinery, the semantic laws)
lives on the [PPL tab](../ppl/). This document covers the examples
themselves.

---

## Basic sampling and scoring

Three end-to-end probabilistic programs of
`theories/programs/examples.v` without recursion: two random-function
programs and a one-parameter score program. The calculus
shape mirrors the higher-order probabilistic calculus of
Heunen–Kammar–Staton–Yang (*A Convenient Category for Higher-Order
Probability Theory*); the semantics here is the integrable-cones model,
not quasi-Borel spaces. One of the three is also the raw material of the
next chapter: `ex_random_linear` is reused verbatim as the model of the
Bayesian linear regression `ex_bayes_linear`.

Each program ships a closed-form CBV identity tying its denotation to
the corresponding distribution, proved in
`theories/programs/cbv_marginals.v`. Every proof follows the same
route: the let-at-sample integral law `eD_let_sample_int`
(`theories/programs/infra/let_sample_law.v`) turns each
`let x = sample µ in …` prefix into a Pettis integral over Diracs of the
prior, dereliction and evaluation at setlike test points push inside the
integral, and the integrand computes pointwise down to a Dirac integral.

| Example | Statement | Rocq |
|---|---|---|
| ex_random_constant: a random constant function | Sample a constant $c \sim \mu$, return $\lambda x. c$; derelicting the function value and evaluating it at any probability test point recovers the prior $\mu$. | `ex_random_constant`, `ex_random_constant_cbv_marginal` — theories/programs/examples.v; theories/programs/cbv_marginals.v |
| ex_random_linear: a random affine function | Sample slope and intercept from $\mu$, return $\lambda x. m \cdot x + b$; at a Dirac test point the marginal is the iterated integral $\int\int \delta_{m \cdot r_0 + b}(U)\,d\mu(b)\,d\mu(m)$. | `ex_random_linear`, `ex_random_linear_cbv_marginal`, `rl_inner_marginal` — theories/programs/examples.v; theories/programs/cbv_marginals.v |
| ex_score_posterior: score reweights the prior | Sample a parameter, score it by a bundled test function, return it; the denotation's measure of every measurable `U` is $\int_U f\,d\mu$, with total mass the evidence $\int f\,d\mu$. | `ex_score_posterior`, `ex_score_posterior_cbv_E`, `ex_score_posterior_cbv_mass` — theories/programs/examples.v; theories/programs/cbv_marginals.v |

### ex_random_constant: a random constant function (`ex_random_constant`, `ex_random_constant_cbv_marginal`, `ex_random_constant_cbv_marginal_dirac`, `ex_random_constant_cbv_marginal_mass`)

The constant-output random function. After sampling a single random
constant $c \sim \mu$, the program returns the function $\lambda x. c$: every call
returns the same value, but the function itself was sampled from $\mu$.
The main identity is the marginal at a test point: derelicting the
(promoted) function value and evaluating it at a test point recovers the
prior $\mu$. (Dereliction, `der`, is the counit that recovers a plain
value `x` from its promoted form `x!` — `der_prom`,
`theories/exp/bang.v`.)

```coq
(* theories/programs/examples.v *)
Definition ex_random_constant :
    @named_expr R Ar R_obj nil (tfun tR' tR') :=
  [ let "c" := sample m in \ "x" ::: tR' => # "c" ].
```

The program has type `tfun tR tR` — a distribution over a
(constant-output) function space, not over reals. Derelicting its
denotation and evaluating at any *probability* test point `x`
(`fmeas_mu x setT = 1`) gives back $\mu$, uniformly in the test point;
Diracs are probabilities, so the corollary
`ex_random_constant_cbv_marginal_dirac` specialises the statement to
$\delta_{r_0}$.

```coq
(* theories/programs/cbv_marginals.v (Section RandomConstantMarginal) *)
Theorem ex_random_constant_cbv_marginal (x : FMeas R_obj) :
  fmeas_mu x [set: ar_carrier Ar R_obj] = 1%E ->
  linhom_fun
    (Lfun (der (Lty tR' tR'))
       (linhom_fun (ex_random_constant_cbv R_carrier_meas
                      R_to_carrier_meas pm) one1)) x = mu.

Theorem ex_random_constant_cbv_marginal_dirac (r0 : ar_carrier Ar R_obj) :
  linhom_fun
    (Lfun (der (Lty tR' tR'))
       (linhom_fun (ex_random_constant_cbv R_carrier_meas
                      R_to_carrier_meas pm) one1)) (dirac_fmeas r0) = mu.
```

The per-`U` reading of the same equality is
`ex_random_constant_cbv_marginal_mass`: the marginal's measure of every
measurable `U` equals $\mu(U)$.

```coq
(* theories/programs/cbv_marginals.v (Section RandomConstantMarginal) *)
Theorem ex_random_constant_cbv_marginal_mass (x : FMeas R_obj)
    (Hx1 : fmeas_mu x [set: ar_carrier Ar R_obj] = 1%E)
    (U : set (ar_carrier Ar R_obj)) :
  fmeas_mu
    (linhom_fun
       (Lfun (der (Lty tR' tR'))
          (linhom_fun (ex_random_constant_cbv R_carrier_meas
                         R_to_carrier_meas pm) one1)) x) U =
  fmeas_mu mu U.
```

Proof idea: the let-at-sample law turns the denotation into the Pettis
integral $\int (\ell_c)! \mu(dc)$ of the promoted closures
$\ell_c := \llbracket\lambda x. c\rrbracket(1 \otimes \delta_c)$ (the lambda clause promotes at the setlike
one-Dirac environment, `adj_psi_at_setlike` of
`theories/programs/infra/cbv_anchors.v`). Dereliction and evaluation
at `x` push inside the integral (`icones_hom_pres_int` /
`linhom_int_eval`); the integrand computes to $\delta_c$ — the unused
argument `x` is discarded silently because it is a probability
(`em_proj1_mor_probE`) and the closure returns the captured constant;
finally $\int \delta_c\,d\mu(c) = \mu$ (`icone_integral_dirac_fmeas`).

> The probability hypothesis on the test point is honest, not an
> artifact. Discarding an argument in `EM(!)` is the comonoid counit,
> which on `FMeas` weighs the kept output by the argument's total mass
> (`coalg_e_FMeas_prob`); at `x = 0` the marginal is `0`, not $\mu$. Only
> mass-1 test points are discarded silently. This is the smallest
> program of the chapter whose value lives at a function type, so it is
> where that discipline is first paid: the identity is about a *sampled
> function*, and reading a marginal off it means going through
> dereliction and evaluation rather than through a measure on reals.

### ex_random_linear: a random affine function (`ex_random_linear`, `ex_random_linear_cbv_marginal`, `rl_inner_marginal`)

A random-coefficients linear regression: sample slope `m` and intercept
`b` from $\mu$, return the function $\lambda x. m \cdot x + b$ — a random affine
function with independent prior draws for slope and intercept.
Derelicted and evaluated at a Dirac test point $\delta_{r_0}$, the
denotation's measure of every measurable `U` is the iterated integral
$\int\int \delta_{m \cdot r_0 + b}(U)\,d\mu(b)\,d\mu(m)$. (Dereliction,
`der`, recovers a plain value `x` from its promoted form `x!`.)

```coq
(* theories/programs/examples.v *)
Definition ex_random_linear :
    @named_expr R Ar R_obj nil (tfun tR' tR') :=
  [ let "m" := sample m in
    let "b" := sample m in
    \ "x" ::: tR' => # "m" * # "x" + # "b" ].
```

The program exercises `ne_add` and `ne_mul` via the arithmetic lifts of
`theories/programs/ppl.v`; on Dirac inputs the lifts reduce to scalar
arithmetic (`add_lift_dirac` / `mul_lift_dirac`).

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

The two sample binders are peeled one at a time. The inner continuation
`ex_rl_inner` (one sample left, the slope already bound) marginalises to
a single integral over the intercept, and the outer theorem is that
lemma integrated over the slope.

```coq
(* theories/programs/cbv_marginals.v (Section RandomLinearMarginal) *)
Lemma rl_inner_marginal (m r0 : ar_carrier Ar R_obj)
    (U : set (ar_carrier Ar R_obj)) (mU : measurable U) :
  fmeas_mu
    (linhom_fun
       (Lfun (der (Lty tR' tR'))
          (Lfun (eD_cbv' (ex_rl_inner pm)) (one1 ⊗p dirac_fmeas m)))
       (dirac_fmeas r0)) U =
  \int[fmeas_mu mu]_(b in [set: ar_carrier Ar R_obj])
     (fine (fmeas_mu
        (dirac_fmeas (R_to_carrier R_carrier_eq (cR m * cR r0 + cR b)))
        U))%:E.
```

Proof idea: two applications of the let-at-sample law peel the two
sample binders into nested Pettis integrals; dereliction and evaluation
at $\delta_{r_0}$ push inside both layers. At the three-Dirac environment
$1 \otimes \delta_m \otimes \delta_b \otimes \delta_{r_0}$ (a setlike unit-ball point — setlike
meaning fixed by the comonoid structure, `coalg_str x = x!`, so it
duplicates and discards like an ordinary value — every Dirac is setlike;
unit-ball meaning cone-norm at most `1`) the variable
projections return the three Diracs, the body computes through the Dirac
rules of `mul_lift` and `add_lift` to $\delta_{m \cdot r_0 + b}$ (`rl_body_at`), and
the per-`U` evaluation of an `FMeas`-valued Pettis integral
(`icone_integral_fmeas_E`) lands the iterated Lebesgue integral.

> This is the first program of the chapter whose marginal is a genuine
> two-fold integral rather than a single prior, so it is what pins down
> that successive `sample` binders are read as independent draws and that
> the arithmetic in a closure body computes on Diracs. It is also not a
> standalone curiosity: it is the *model* of the Bayesian linear
> regression `ex_bayes_linear` of the next chapter — that program is
> literally `let "f" := ex_random_linear in …`, so every observation
> scored there is scored against the affine function this entry
> marginalises.

### ex_score_posterior: score reweights the prior (`ex_score_posterior`, `ex_score_posterior_cbv_E`, `ex_score_posterior_cbv_mass`)

Scoring a sampled parameter — the one-dimensional unnormalised
posterior, in the textbook prior / score / return shape: sample a
parameter `m` from the prior $\mu$, score by a bundled $[0,1]$ test
function `f : testfn`, return `m`. The program has type `tR`, and its
denotation's measure of every measurable `U` is $\int_U f\,d\mu$ — the prior
reweighted by the test pairing, with total mass $\int f\,d\mu$.

```coq
(* theories/programs/examples.v *)
Definition ex_score_posterior :
    @named_expr R Ar (po_robj P) nil tR' :=
  [ let "m" := sample m in
    let "_" := Score (test f # "m") in
    # "m" ].
```

The scoring step goes through the abstract test-function coin `test f`
of the bundled test function `f : testfn`: `Score` weighs by
`po_density P` of the factored value, which `po_into_E`
(`theories/programs/ppl.v`) reads back as `test_fun f` of the sampled
real. The identity below is the unnormalised posterior — the prior
reweighted by the density, not normalised — and its mass corollary is
the evidence.

```coq
(* theories/programs/cbv_marginals.v (Section ScorePosterior) *)
Theorem ex_score_posterior_cbv_E (U : set (ar_carrier Ar R_obj))
    (mU : measurable U) :
  fmeas_mu
    (linhom_fun (ex_score_posterior_cbv P R_to_carrier_meas pm f) one1) U =
  \int[fmeas_mu mu]_(r in U) (f (cR r))%:E.

Theorem ex_score_posterior_cbv_mass :
  fmeas_mu
    (linhom_fun (ex_score_posterior_cbv P R_to_carrier_meas pm f) one1)
    [set: ar_carrier Ar R_obj] =
  \int[fmeas_mu mu]_(r in [set: ar_carrier Ar R_obj]) (f (cR r))%:E.
```

Proof idea: the let-at-sample mass law `eD_let_sample_mu_E` turns the
denotation's measure of `U` into an integral over $r \sim \mu$ of the
continuation's mass at the one-Dirac environment $1 \otimes \delta_r$. There the
score clause evaluates to the scalar `f(r)` (`eD_score_E` +
`score_lift_dirac`), and the returned variable under the score binder is
computed by `em_proj1_mor_unitE`: a `tunit`-typed score result is not
setlike (a setlike point is one fixed by the comonoid structure,
`coalg_str x = x!`, hence copied and discarded like an ordinary value),
so the first projection discards it as its scalar weight,
turning the score into the `precone_scale` factor `f(r)` on the returned
$\delta_r$ (`sp_cont_at_dirac`). The Dirac's measure of `U` is the indicator,
and the integral collapses to $\int_U f\,d\mu$.

> This program is the anchor for the whole conditioning/rejection
> chapter: `score` produces the unnormalised posterior, rejection
> sampling produces the normalised one, and `ex_reject_normalises_score`
> (`theories/programs/cbv_marginals.v`) connects the two programs
> exactly — the rejection denotation times the total evidence $\int f\,d\mu$
> *is* the measure computed here. Note also what the score does not do:
> nothing in the semantics divides by the evidence, so the denotation of
> a scored program is a sub-probability whose mass is the evidence, and
> normalisation only ever appears as a theorem relating two programs.

## Runtime-parameter distributions

A distribution whose parameters are real literals can be bundled ahead of
the program and drawn with `sample`; a distribution whose parameter is a
value the program itself computes cannot. The two examples of this chapter
both put a program value into a parameter slot. The Bayesian linear
regression observes a Gaussian whose mean is the model's own prediction
`#"f" @ [|obs_x o|]` at a known input, through the observation operator
`observe Gaussian e { s } y`; the Gaussian hierarchy draws a Gaussian whose
mean is the *sampled value* `#"s"` of a previous draw, through the
runtime-parameter constructor `ne_gaussian` (surface `Gaussian(e1,e2)`, with
`ne_uniform` its uniform sibling, both resolved by the `pkernel` layer). The
hierarchical model is precisely the shape that a bundled-measure surface
cannot express.

The chapter runs the regression first — the program, its observation data,
and the two model-evidence identities — then isolates the bridge that makes
"the regression *is* iterated conditioning" a definitional statement rather
than an informal reading, and closes with the two-level hierarchy, whose
denotation reduces to a hierarchy integral and whose total mass is exactly
`1`.

| Example | Statement | Rocq |
|---|---|---|
| ex_bayes_linear: the Bayesian linear model | The random affine model, bound once and conditioned on a list of Gaussian observations; the counit of its denotation is the model evidence. | `ex_bayes_linear`, `ex_bayes_linear_cbv_evidence`, `ex_bayes_linear_cbv_evidence2` — theories/programs/examples.v; theories/programs/cbv_marginals.v |
| Observation folding and iterated conditioning | One observation is one soft-conditioning step of the model at a known input; the regression is defined as the fold of those steps, and unfolds to the raw score fold. | `condition_at`, `iter_condition`, `ex_bayes_linear_is_iter_condition` — theories/programs/examples.v |
| ex_gaussian_walk: a Gaussian hierarchy | `let s = Gaussian(0,1) in Gaussian(s,1)`: the denotation's measure of every measurable `U` is the hierarchy integral, and the total mass is exactly `1`. | `ex_gaussian_walk`, `ex_gaussian_walk_E`, `ex_gaussian_walk_mass` — theories/programs/examples.v; theories/programs/kernel_anchors.v |

### ex_bayes_linear: the Bayesian linear model (`ex_bayes_linear`, `ex_bayes_linear3`, `ex_bayes_linear_cbv_evidence`, `ex_bayes_linear_cbv_evidence2`)

The Bayesian linear regression of Staton–Yang–Heunen–Kammar–Wood
(arXiv 1701.02547 §2.1). The model is a random function: exactly
`ex_random_linear` of the previous chapter, a distribution over affine
functions with slope and intercept drawn from the prior. The program samples
the model once, binds it to `"f"`, folds the observation list into a series
of `observe` steps, and returns `#"f"` — the posterior over functions. On a
concrete two-observation list the surface syntax reads:

```coq
(* theories/programs/examples.v — the 2-observation surface form
   (definitionally equal to ex_bayes_linear [:: o1; o2], pinned by a
   Check (erefl : …) in the source) *)
[ let "f" := (let "m" := sample m in
              let "b" := sample m in
              \ "x" ::: tR' => # "m" * # "x" + # "b") in
  let "_" := observe Gaussian (# "f" @ [| obs_x o1 |])
                      { 1 / 2 } (obs_y o1) in
  let "_" := observe Gaussian (# "f" @ [| obs_x o2 |])
                      { 1 / 2 } (obs_y o2) in
  # "f" ]
```

Each observation is a `Record obs = MkObs { obs_x ; obs_y }` packaging a
known input point `obs_x` and the observed datum `obs_y`. The likelihood
deviation is a single fixed noise `σ = 1/2` for every observation. Its
observation density is the envelope-normalised Gaussian likelihood
`obs_d o := gauss_obs_density (1/2) (obs_y o)`, i.e.
`obs_d o r = normal_pdf r (1/2) (obs_y o) / normal_peak (1/2)` $\in [0,1]$
(`theories/programs/ppl.v`) — the surface form is the
`observe Gaussian (#"f" @ [|obs_x o|]) { 1/2 } (obs_y o) ≡ Score (Gausslik (#"f" @ [|obs_x o|]) { 1/2 , obs_y o })`
operator (mean expression first, then `{ stddev }`, then the observed
datum). The `[0,1]` bound is intrinsic to the distribution — the peak is
bundled in `gauss_obs_density` — so the observation carries no user-supplied
envelope. Conditioning is a score: the model's value `#"f" @ [|obs_x o|]` at
the known input is scored by `obs_d o`.

```coq
(* theories/programs/examples.v — Section Obs *)
Record obs := MkObs {
  obs_x : R;                       (* the input point *)
  obs_y : R }.                     (* the observed datum *)

Definition obs_d (o : obs) : R -> R := gauss_obs_density (1 / 2) (obs_y o).
```

`ex_bayes_linear l` is the program at a general meta-level observation list
`l : seq (obs R)`, and `ex_bayes_linear3` is the concrete 3-observation
instance. The headline identity is the model evidence: the counit ("total
mass") of the function-space denotation is the iterated integral of the
product of the observation densities `obs_d` at the model's values, over the
priors on slope and intercept.

```coq
(* theories/programs/cbv_marginals.v — Section BayesLinearEvidence *)
Theorem ex_bayes_linear_cbv_evidence (l : seq (obs R)) :
  ((c1_val (Lfun (coalg_e (tyD_cbv tF))
      (linhom_fun
         (ex_bayes_linear_cbv P R_to_carrier_meas pm l)
         one1)))%:num)%R =
  fine (\int[fmeas_mu mu]_(m in [set: ar_carrier Ar R_obj])
     (fine (\int[fmeas_mu mu]_(b in [set: ar_carrier Ar R_obj])
        ((\prod_(o <- l) obs_d o (cR m * obs_x o + cR b))%R)%:E))%:E).
```

The literal 2-observation instance writes the product out: the counit mass at
`[:: o1; o2]` is $\int\int$ `obs_d` $o_1 (m \cdot x_1 + b) \cdot$ `obs_d` $o_2 (m \cdot x_2 + b)\,d\mu\,d\mu$.

```coq
(* theories/programs/cbv_marginals.v — Section BayesLinearEvidence *)
Theorem ex_bayes_linear_cbv_evidence2 (o1 o2 : obs R) :
  ((c1_val (Lfun (coalg_e (tyD_cbv tF))
      (linhom_fun
         (ex_bayes_linear_cbv P R_to_carrier_meas pm
            [:: o1; o2])
         one1)))%:num)%R =
  fine (\int[fmeas_mu mu]_(m in [set: ar_carrier Ar R_obj])
     (fine (\int[fmeas_mu mu]_(b in [set: ar_carrier Ar R_obj])
        ((obs_d o1 (cR m * obs_x o1 + cR b) *
          obs_d o2 (cR m * obs_x o2 + cR b))%R)%:E))%:E).
```

Proof idea: the per-`(m,b)` weights factor out of the fold one observation at
a time — `obs_fold_at` says the fold at the depth-`n` environment is the
promoted closure scaled by $\prod_{o \in l}$ `obs_d` $o (m \cdot x_o + b)$ — and then two
applications of the let-at-sample law `eD_let_sample_int` integrate those
weights against the priors on slope and intercept, in that order.

> Call-by-value matters here. The sampled function is bound once and shared
> across every observation and the return: each access to `#"f"` goes through
> the comonoid duplication `coalg_d` of the let-clause diagonal at the
> function-type cone `!(U⟦tR⟧ ⊸ U⟦tR⟧)`. That duplication is what makes all
> observations score the *same* sampled function (and the returned posterior
> be over that same function), rather than each score drawing a fresh model.
> The evidence identity is in that sense a higher-order anchor: the thing
> being conditioned, and returned, is a function value of type
> `tfun tR' tR'`, not a real. The non-obvious cross-link is to
> `ex_score_posterior`: this program is that one-parameter score program
> repeated, at a model that is itself a distribution over functions.

### Observation folding and iterated conditioning (`condition_at`, `iter_condition`, `obs_fold`, `ex_bayes_linear_is_iter_condition`, `ex_bayes_linear_obs_fold`)

This entry defines `condition_at`, one soft-conditioning step of the
Bayesian linear regression `ex_bayes_linear` at a single observation, and
its fold `iter_condition` over the observation list; readably,
`condition_at v o K = let "_" := observe Gaussian (v @ [| obs_x o |]) { 1 / 2 } (obs_y o) in K`,
with `v` the context variable holding the model.
The regression *is* iterated conditioning, by definition. Scoring
`#"f" @ [|obs_x o|]` by `obs_d o` conditions the model `#"f"` at the
input `obs_x o`, in the soft, score-based reading: the reweighting is a
score by the `[0,1]` density `obs_d o`, not the boolean predicate of
`ne_condition` in the conditioning chapter, and the term is in A-normal
form (the
regression scores the application directly and returns the function at
the end, instead of binding the model's value and returning it).
`condition_at o` packages one such step and `iter_condition` is its fold over
a meta-level list `l : seq (obs R)`.

```coq
(* theories/programs/examples.v — Section IteratedConditioning *)
Definition condition_at (G : named_ctx Ar)
    (v : named_var G (tfun tR' tR')) (o : obs R) (t : ppl_type Ar)
    (K : @named_expr R Ar (po_robj P) (("_"%string, tunit) :: G) t) :
    @named_expr R Ar (po_robj P) G t :=
  ne_let "_"%string
    (ne_score_p (po_density P) (po_density_meas P) (po_ge0 P) (po_le1 P)
       (ne_to_prob (obs_phi o)
          (ne_app (ne_var v) (ne_real (obs_x o)))))
    K.

Fixpoint iter_condition (G : named_ctx Ar)
    (v : named_var G (tfun tR' tR')) (l : seq (obs R)) :
    @named_expr R Ar (po_robj P) G (tfun tR' tR') :=
  match l with
  | nil => ne_var v
  | o :: l' =>
      condition_at v o (iter_condition (nv_tail "_"%string tunit _ v) l')
  end.
```

`ex_bayes_linear l` is *defined* as the model bound once followed by
`iter_condition`, so the agreement anchor `ex_bayes_linear_is_iter_condition`
holds by `erefl`.

```coq
(* theories/programs/examples.v — Section BayesLinear *)
Definition ex_bayes_linear (l : seq (obs R)) :
    @named_expr R Ar (po_robj P) nil (tfun tR' tR') :=
  ne_let "f"%string (ex_random_linear m)
    (iter_condition (nv_head "f"%string (tfun tR' tR') nil) l).

Theorem ex_bayes_linear_is_iter_condition (l : seq (obs R)) :
  ex_bayes_linear l =
  ne_let "f"%string (ex_random_linear m)
    (iter_condition (nv_head "f"%string (tfun tR' tR') nil) l).
Proof. by []. Qed.
```

The historical raw score-fold shape survives as the derived reading
`ex_bayes_linear_obs_fold`: `obs_fold` emits, for each observation, the same
`ne_score_p` node that `condition_at` emits, with the `named_var` witness
locating `"f"` extended by `nv_tail` in lock-step with the growing context.

```coq
(* theories/programs/examples.v — Section BayesLinear *)
Fixpoint obs_fold (G : named_ctx Ar) (v : named_var G (tfun tR' tR'))
    (l : seq (obs R)) : @named_expr R Ar (po_robj P) G (tfun tR' tR') :=
  match l with
  | nil => ne_var v
  | o :: l' =>
      ne_let "_"%string
        (ne_score_p (po_density P) (po_density_meas P) (po_ge0 P) (po_le1 P)
           (ne_to_prob
              (po_into P (obs_d o) (obs_meas o) (obs_ge0 o) (obs_le1 o))
              (ne_app (ne_var v) (ne_real (obs_x o)))))
        (obs_fold (nv_tail "_"%string tunit _ v) l')
  end.

Lemma ex_bayes_linear_obs_fold (l : seq (obs R)) :
  ex_bayes_linear l =
  ne_let "f"%string (ex_random_linear m)
    (obs_fold (nv_head "f"%string (tfun tR' tR') nil) l).
```

> The point of this entry is that "Bayesian linear regression = iterated
> conditioning" is not a commentary about the program but its definition:
> `ex_bayes_linear_is_iter_condition` is closed by `by []`. Two readings then
> come for free — the surface-syntax reading (the `#"f"` lookups resolve
> through the accumulated `("_", tunit)` slots by canonical-structure search,
> so the sugar of the `ex_bayes_linear` entry elaborates to exactly the `nv_tail` chain
> `iter_condition` builds) and the raw-fold reading `ex_bayes_linear_obs_fold`,
> which is what the evidence proof rewrites with before it starts integrating.
> `obs_fold` has to be a Rocq `Fixpoint` producing raw constructors because
> the `ppl_named` custom entry cannot recurse over a meta-level `seq`; that is
> the only reason two shapes exist at all, and the fold is what the depth-`n`
> lemma `obs_fold_at` is stated about.

### ex_gaussian_walk: a Gaussian hierarchy (`ex_gaussian_walk`, `ex_gaussian_walk_E`, `ex_gaussian_walk_mass`)

A two-level Gaussian hierarchy, `let s := Gaussian(0,1) in Gaussian(s,1)`,
written with the runtime-parameter `Gaussian(e1,e2)` constructor
`ne_gaussian` (no witnesses; the kernel family
`gaussian_kernel` is a total `pkernel`): the parameter of the second draw is
the *sampled value* of the first. The constant-parameter first stage is the
kernel surface at real literals — `eD_gaussian_sample_agree` pins it to the
bundled `sample (gaussian 0 1)` form.

```coq
(* theories/programs/examples.v — Section GaussianWalk *)
Definition ex_gaussian_walk : @named_expr R Ar R_obj nil tR' :=
  [ let "s" := Gaussian( [| 0%R |] , [| 1%R |] ) in
    Gaussian( # "s" , [| 1%R |] ) ].
```

The denotation's measure of every measurable `U` is the hierarchy integral
$\int N($`cR`$r, 1)($`toC`$^{-1} U)\,dN(0,1)(r)$, taken against the transported prior
`gw_prior`; the mass corollary says the program is a probability, with total
mass exactly $1$.

```coq
(* theories/programs/kernel_anchors.v — Section GaussianWalkAnchors *)
Lemma ex_gaussian_walk_E (U : set (ar_carrier Ar R_obj)) :
  measurable U ->
  fmeas_mu (linhom_fun
              (eD' (ex_gaussian_walk : @named_expr R Ar R_obj nil tR'))
              one1) U =
  \int[fmeas_mu gw_prior]_(r in [set: ar_carrier Ar R_obj])
     (fine (normal_prob (cR r) 1 (toC @^-1` U)))%:E.

Lemma ex_gaussian_walk_mass :
  fmeas_mu (linhom_fun
              (eD' (ex_gaussian_walk : @named_expr R Ar R_obj nil tR'))
              one1) [set: ar_carrier Ar R_obj] = 1.
```

Proof idea: the general let-law `eD_let_mu_E`
(`theories/programs/infra/let_sample_law.v`) turns the denotation's measure
of `U` into an integral of the body's mass at the one-Dirac environment
$1 \otimes \delta_r$ against the bound sub-distribution — here the first stage, which
the setlike/Dirac anchor `eD_gaussian_at` computes to the transported prior
$N(0,1)$. (A point is *setlike* when it is fixed by the comonoid structure,
`coalg_str x = x!` — every Dirac is — so it duplicates and discards like an
ordinary value.) Under the binder, `#"s"` projects to $\delta_r$ and the literal `[|1|]`
to $\delta_{\mathrm{toC}\ 1}$, so the same anchor computes the body to the gaussian kernel
at $(r, 1)$, whose per-`U` reading (`gaussian_ker_cast_E`) is
$N($`cR`$r, 1)($`toC`$^{-1} U)$. For the mass corollary the integrand is identically
$1$ (the kernel is a pointwise probability, `gaussian_kernel_norm1`) and
$\int 1\,dN(0,1) = 1$ (`fmeas_of_prob_setT`).

> This is the example that the runtime-parameter constructor exists for: with
> only bundled measures on the surface, the second draw's mean cannot mention
> `#"s"`, and the hierarchy is inexpressible. Everything downstream of the
> constructor is unchanged — the same let-law `eD_let_mu_E` and the same
> setlike/Dirac machinery that serve the constant-parameter programs carry the
> proof, and the only new ingredient is that the anchor `eD_gaussian_at` is
> applied at an environment where the mean argument reduces to $\delta_r$ rather
> than to a literal Dirac. The mass-$1$ corollary is the regression anchor
> worth keeping: a hierarchy of probability kernels is still a probability, so
> any later loss of mass in a program of this family is a scoring effect and
> not an artefact of nesting draws.

## Recursive probabilistic examples

The programs of this chapter combine `ne_fix` — and, in the last two
entries, `ne_fix_mr` — with the boolean cascade, exhibiting productive
partial termination. Their CBV mass identities, and for the two
halting samplers the full distribution refinements that pin the
denotations as *measures*, are proved in
`theories/programs/ex_geom.v`, `theories/programs/ex_almost_loop.v` and
`theories/programs/ex_even_odd.v` against the seeded
value-fixpoint interpreter (`fix_comb`, `fix_value`), by the same
reduction-chain-plus-affine-cascade recipe as the rejection sampler of
the next chapter.

Four programs across five entries, ordered by how tightly the
denotation is pinned. `ex_loop` is the bare recursion, with no coin and
no recorded identity of its own. `ex_geom` halts almost surely and its
measure is identified atom by atom. `ex_almost_loop` parameterises the
same loop by a flip probability and splits: mass one at $p > 0$, the
zero point at $p = 0$. Finally `ex_even_odd_pair` exercises the
mutual-recursion path, where the pair value and the divergence of its
two projections are separate statements — and only the second is
mass `0`.

| Example | Statement | Rocq |
|---|---|---|
| ex_loop: unproductive divergence | `let rec l _ = l () in l ()` at `tunit` — an infinite chain of unit-typed recursive calls, no sampling and no scoring; no identity of its own, the mass-`0` theorem being carried by `ex_almost_loop_cbv_zero` at `p = 0`. | `ex_loop`, `ex_loop_cbv` — theories/programs/examples.v |
| ex_geom: the geometric distribution | The fair-coin counter halts almost surely, and its denotation is the geometric law: the atom at the embedded natural `k` carries mass $\left(\frac{1}{2}\right)^{k+1}$. | `ex_geom`, `ex_geom_cbv_distribution`, `ex_geom_cbv_pmf` — theories/programs/examples.v; theories/programs/ex_geom.v |
| ex_almost_loop: escape with probability one | A Bernoulli-guarded loop parameterised by a bundled probability: at $p > 0$ the denotation is the unit point `one1`, at $p = 0$ it is the zero point of the unit cone. | `ex_almost_loop`, `ex_almost_loop_cbv_dirac`, `ex_almost_loop_cbv_zero` — theories/programs/examples.v; theories/programs/ex_almost_loop.v |
| ex_even_odd_pair: mutual recursion at a pair of functions | One recursive name bound by `ne_fix_mr` at a pair of function types; the pair denotation is `0! ⊗p 0!`, the pair of promoted-zero functions — *not* the cone-zero. | `ex_even_odd_pair`, `ex_even_odd_pair_cbv_value` — theories/programs/examples.v; theories/programs/ex_even_odd.v |
| ex_even and ex_odd: divergence of the projections | Each projection of the recursive pair delegates to the other with no base case; applied to `()`, both land in the unit cone as its zero element — mass `0`. | `ex_even`, `ex_even_cbv_diverges`, `ex_odd_cbv_diverges` — theories/programs/examples.v; theories/programs/ex_even_odd.v |

### ex_loop: unproductive divergence (`ex_loop`)

Bare divergence: `let rec l _ = l () in l ()`. No sampling, no
scoring — an infinite chain of unit-typed recursive calls, of total
mass `0`.

```coq
(* theories/programs/examples.v *)
Definition ex_loop :
    @named_expr R Ar R_obj nil tunit :=
  [ let rec "l" "_" ::: tunit ==> tunit := # "l" @ ()
    in # "l" @ () ].
```

The `let rec` is written in its annotated form because the binder `"_"`
is unused, so its type cannot be inferred from the body. The program
does elaborate: `ex_loop_cbv` of `theories/programs/examples.v` is its
CBV denotation, recorded there as a smoke test.

No standalone CBV identity is recorded for the bare loop: the
certain-divergence statement for this recursion shape is carried by
the parameterised twin at `p = 0`. In the entry
*ex_almost_loop: escape with probability one*,
`ex_almost_loop_cbv_zero` pins the denotation of the
Bernoulli-guarded loop with a never-succeeding coin to
`precone_zero`, and `ex_loop` is the same loop with the coin erased.

> This entry is a syntax-and-elaboration anchor rather than a semantic
> one: it is the smallest program that puts `ne_fix` at `tunit`, and it
> is the shape every other recursion in the chapter refines by placing
> a coin in front of the recursive call. The expectation gap is
> deliberate and stated above — the mass-`0` theorem lives on
> `ex_almost_loop_cbv_zero`, whose `p = 0` case is exactly the
> constantly-zero Kleene chain the bare loop produces.

### ex_geom: the geometric distribution (`ex_geom`, `ex_geom_cbv_mass_one`, `ex_geom_cbv_distribution`, `ex_geom_cbv_pmf`)

A geometric counter built from a fair-coin Bernoulli recursion —
`let rec g _ = if Bernoulli [| (1/2:R) |] then 0 else 1 + g () in g ()`:
each call halts with probability `½` (returning `0`) and otherwise
recurses, adding `1` to the returned real. The program denotes a
measure of total mass `1` — the sampler halts almost surely
(`ex_geom_cbv_mass_one`) — and that measure is the geometric law: on
every measurable `U` the denotation evaluates as the series
$\sum_k (1/2)^{k+1} \delta_k(U)$ (`ex_geom_cbv_distribution`), and the atom at
the embedded natural `k` carries mass exactly $\left(\frac{1}{2}\right)^{k+1}$
(`ex_geom_cbv_pmf`).

```coq
(* theories/programs/examples.v *)
Definition ex_geom : @named_expr R Ar (po_robj P) nil tR' :=
  [ let rec "g" "_" ::: tunit ==> tR' :=
      (if Bernoulli [| (1 / 2 : R) |]
       then [| 0%R |]
       else [| 1%R |] + # "g" @ ())
    in # "g" @ () ].
```

The result type `tR'` is the local notation for `tR (po_robj P)`, the
real type at the probability object. The fair coin is the clean
constant-literal form `Bernoulli [| (1/2 : R) |]`: the success
probability is a bare real literal and its `[0,1]` bounds are
discharged by `lra` — no bundle, no `Const`, no loose witnesses.

```coq
(* theories/programs/ex_geom.v — Section GeomRider *)
Theorem ex_geom_cbv_mass_one :
  fmeas_mu g_denot [set: ar_carrier Ar R_obj] = 1.
```

The mass identity is the `U = setT` specialisation of the
distribution, where the geometric weights sum to `1`. The distribution
itself — $\sum_k (1/2)^{k+1} \delta_{gpt(k)}(U)$ — is stated against two local
notations: the embedded point `gpt k` places the natural `k` in the
real carrier, and `geom_w k` is the weight $\left(\frac{1}{2}\right)^{k+1}$ as an ereal.

```coq
(* theories/programs/ex_geom.v — Section GeomRider
   gpt k := R_to_carrier R_carrier_eq (k%:R : R)
   geom_w k := (((1 / 2 : R) ^+ k.+1)%:E) *)
Theorem ex_geom_cbv_distribution (U : set (ar_carrier Ar R_obj))
    (mU : measurable U) :
  fmeas_mu g_denot U =
  \sum_(k <oo) geom_w k * fmeas_mu (dirac_fmeas (gpt k)) U.
```

The atoms are distinct (`gpt_inj`) and each singleton is measurable
(`measurable_gpt`), so evaluating the series at `[set gpt k]` isolates
one surviving term — the PMF.

```coq
(* theories/programs/ex_geom.v — Section GeomRider *)
Theorem ex_geom_cbv_pmf (k : nat) :
  fmeas_mu g_denot [set gpt k] = ((1 / 2 : R) ^+ k.+1)%:E.
```

(`g_denot` abbreviates `linhom_fun (ex_geom_cbv P R_to_carrier_meas) one1`,
the CBV denotation of the closed program at the unit context point.)
Proof idea: the rejection-sampling reduction chain on a simpler
program. The outer application collapses by `der` $\circ$ `prom` cancellation
(`ex_geom_app_E`); the denotation is the `cone_sup_ball` of the
per-iterate measures (`ex_geom_sup_E`); one Kleene step computes to
the boolean dispatch $\nu_{n+1} = \tfrac{1}{2}\cdot\delta_0 + \tfrac{1}{2}\cdot($ `add_lift` ` $(\delta_1 \otimes \nu_n))$
(`g_step`); the translation-mass invariance `add_lift_mass` reduces
the mass cascade to $x_{n+1} = \tfrac{1}{2} + \tfrac{1}{2}\cdot x_n$ (`g_val_S`); the affine
cascade (`theories/prelude/geom_series.v`) and the sup-mass bridge
(`theories/mcones/fmeas.v`) close the limit at `1`.
The distribution refinement runs the same induction per set: the
per-`U` step recurrence `g_iter_U_S` splits the THEN branch into
$\left(\frac{1}{2}\right) \delta_0$ and the ELSE branch into the previous iterate pushed
forward by `+1` (`g_shift_atom`), so the `n`-th iterate is the
truncated geometric law $\sum_{k<n} (1/2)^{k+1} \delta_{gpt(k)}$
(`g_iter_closed`); the partial sums converge to the full ereal series
(`g_iter_series_cvg`) through the same `cone_sup_ball` limit, giving
`ex_geom_cbv_distribution`.

> This is the chapter's strongest identity, and the one that makes the
> denotational reading operational: a recursive sampler with an
> unbounded number of iterations is pinned not merely to a total mass
> but to a named law, atom by atom. It regression-anchors the whole
> value-fixpoint stack at once — `fix_comb` and the interleaved chain
> `fix_chain` for the recursion, the boolean cascade for the coin, the
> `add_lift` translation for the `1 +` in the ELSE branch, and the
> affine cascade for the limit. The distribution and the PMF are the
> refinement `ex_geom_cbv_mass_one` alone could not give: mass one is
> compatible with any halting law, whereas
> `ex_geom_cbv_distribution` identifies which one.

### ex_almost_loop: escape with probability one (`ex_almost_loop`, `ex_almost_loop_cbv_mass_one`, `ex_almost_loop_cbv_dirac`, `ex_almost_loop_cbv_zero`)

A parameterised Bernoulli cascade,
`let rec l _ = if Bernoulli (Const pr [|0|]) then () else l () in l ()`:
with probability `p` the recursion halts (returning `()`), and with
probability `1 − p` it recurses.
When `p > 0` the program terminates almost surely (total mass `1`);
when `p = 0` it diverges (total mass `0`). The dichotomy is an honest
theorem pair rather than a side condition on one statement.

```coq
(* theories/programs/examples.v *)
Definition ex_almost_loop (pr : prob R) :
    @named_expr R Ar (po_robj P) nil tunit :=
  [ let rec "l" "_" ::: tunit ==> tunit :=
      (if Bernoulli (Const pr [| 0%R |])
       then ()
       else # "l" @ ())
    in # "l" @ () ].
```

The parameter is a bundled probability `pr : prob`, and `Const pr` is
the constant `tProb`-value coin carrying its `[0,1]` bounds, so the
program needs no loose witnesses. The denotation at `tunit` is a point
of the unit cone (the CBV `tunit` is the terminal coalgebra on
`cone_one_car`), so the termination probability is visible as the
point's norm.

```coq
(* theories/programs/ex_almost_loop.v — Section AlmostLoopRider *)
Theorem ex_almost_loop_cbv_mass_one : (0 < p)%R ->
  cone_norm al_denot = 1%R.

Theorem ex_almost_loop_cbv_zero : p = 0%R -> al_denot = precone_zero.
```

At `p > 0` the denotation is moreover pinned as the *element* `one1` —
the unit point, the Dirac on the one-point space — strengthening the
norm identity to the point itself, since a norm-one element of the
one-dimensional unit cone is `one1` (`cone_one_norm_eq1`).

```coq
(* theories/programs/ex_almost_loop.v — Section AlmostLoopRider *)
Theorem ex_almost_loop_cbv_dirac : (0 < p)%R -> al_denot = one1.
```

(`al_denot` abbreviates
`linhom_fun (ex_almost_loop_cbv P R_to_carrier_meas pr) one1`, and
`p := pr_val pr`; the $0 \leq p \leq 1$ bounds travel inside the bundled
`pr : prob`, so the program carries no loose witnesses.)
Proof idea: as for the geometric counter — reduce to the
`cone_sup_ball` of the iterate points (`ex_almost_loop_sup_E`),
compute one Kleene step to the scalar recurrence
$al\_val(n+1) = p + (1-p)\cdot al\_val(n)$ (`al_step` / `al_val_S`), and
close with `affine_iter_cvg_real`: the limit $\tfrac{p}{1 - (1-p)} = 1$
for $p > 0$, the constantly-zero chain at $p = 0$. The element
identity is then immediate: the unit cone is one-dimensional, so
`cone_one_norm_eq1` upgrades the norm-one fact to `al_denot = one1`.

> The value of the entry is the pair, not either half. Almost-sure
> termination is the interesting direction, but a semantics that could
> only prove mass one would be suspect; `ex_almost_loop_cbv_zero`
> exhibits the same program, at the one parameter where it must fail,
> denoting `precone_zero`. That the `p = 0` case is also the missing
> theorem for `ex_loop` is what lets the bare loop stay
> identity-free. The upgrade from norm to element in
> `ex_almost_loop_cbv_dirac` is cheap here only because the unit cone
> is one-dimensional — the analogous upgrade for `ex_geom` is the
> genuine work of `ex_geom_cbv_distribution`.

### ex_even_odd_pair: mutual recursion at a pair of functions (`ex_even_odd_pair`, `ex_even_odd_pair_cbv`, `ex_even_odd_pair_cbv_value`)

The mutual-recursion witness. `ne_fix_mr` binds one recursive name `p`
at the free-coalgebra type
`tprod (tfun tunit tunit) (tfun tunit tunit)` — a pair of functions —
and each component calls the other via the `fst` / `snd` projections
of the rec-bound product.

```coq
(* theories/programs/examples.v *)
Local Notation pair_ty := (tprod (tfun tunit tunit) (tfun tunit tunit)).

Definition ex_even_odd_lam_a :
    @named_expr R Ar R_obj (("p"%string, pair_ty) :: nil)
                           (tfun tunit tunit) :=
  [ \ "n" ::: tunit => snd # "p" @ # "n" ].

Definition ex_even_odd_lam_b :
    @named_expr R Ar R_obj (("p"%string, pair_ty) :: nil)
                           (tfun tunit tunit) :=
  [ \ "n" ::: tunit => fst # "p" @ # "n" ].

Definition ex_even_odd_pair :
    @named_expr R Ar R_obj nil pair_ty :=
  [ fix_mr "p" as pair_ty by erefl
       in ({ex_even_odd_lam_a}, {ex_even_odd_lam_b}) ].
```

This is the classic even/odd mutual-recursion shape: the first
component is `λn. snd p @ n` and the second is `λn. fst p @ n`, so
each immediately delegates to the *other* with **no base case**. The
two lambdas are spliced in through the `{ … }` escape because the
lambda notation sits at a level above the pair-component level. The
CBV denotation elaborates through the genuine Seely-transported
fixpoint path `fix_mr_comb` of `theories/programs/ppl_cbv.v`
(`fix_mr_clause` at `tprod`), built on
`theories/programs/infra/em_fix_mr.v` (the Seely isomorphism
`Seely2 : !B₁ ⊗ !B₂ ≅ !(B₁ & B₂)` of `theories/exp/seely_defs.v`, with
`Seely2 (x₁! ⊗ x₂!) = ⟨x₁,x₂⟩!`, lets a promoted pair be read as, and
rebuilt from, a pair of promotions); `ex_even_odd_pair_cbv` of
`theories/programs/examples.v` is that elaboration recorded as a
smoke test.

```coq
(* theories/programs/ex_even_odd.v — Section ExEvenOddRider *)
Lemma ex_even_odd_pair_cbv_value :
  Lfun (eD_cbv' (ex_even_odd_pair : @named_expr R Ar R_obj nil pair_ty))
       one1 =
  (precone_zero : L)! ⊗p (precone_zero : L)!.
```

(`Lfun h` abbreviates the underlying cones-hom function, `_!` is
`prom`, and `_ ⊗p _` the `ptensor` of the promoted unit-cone homset
`L`.) The honest accuracy point is that this pair value is *not* the
cone-zero: `0! ⊗p 0!` is the backward Seely transport of the promoted
base-cone zero, and it is provably distinct from the cone-zero
(`eD_fix_mr_prod_at_setlike_neq0`,
`theories/programs/infra/cbv_fix_unfold.v`). The mass-`0` content
appears **only** after projecting and applying to `()`, in the
projections entry `ex_even` / `ex_odd`.

**Proof idea.** The recursion is seeded at the cone-zero, and the
zero-seeded interleaved-Kleene chain stays there: `even_odd_iter_zero`
shows every iterate `fix_chain eo_W0 n = precone_zero` by induction
(each step is `der 0! = 0`). Hence the value-fixpoint at the base cone
is the sup of zero iterates, `ex_even_odd_fix_value_zero`. Feeding
this through the semantic computation law `eD_fix_mr_prod_at_setlike`
gives the pair value `0! ⊗p 0!`.

> Mutual recursion is where a denotational semantics is easiest to
> overclaim, and this entry records the precise place the naive reading
> fails. One might expect a diverging mutual recursion to denote the
> zero element outright; it does not, because the recursive name is
> bound at a *product of function types*, and a pair of everywhere-zero
> functions is not the zero point of the pair cone. Keeping
> `ex_even_odd_pair_cbv_value` separate from the divergence theorems is
> therefore not pedantry but the content: the pair value is what
> `fix_mr_comb` computes, and the mass statement is what projection and
> application extract from it.

### ex_even and ex_odd: divergence of the projections (`ex_even`, `ex_odd`, `ex_even_cbv_diverges`, `ex_odd_cbv_diverges`)

The two projections of the recursive pair, each a closed function of
type `tfun tunit tunit`. Since neither component has a base case, the
closed runs `ex_even @ ()` and `ex_odd @ ()` never terminate, and the
operational identity is honest divergence — mass `0`.

```coq
(* theories/programs/examples.v *)
Definition ex_even :
    @named_expr R Ar R_obj nil (tfun tunit tunit) :=
  [ fst {ex_even_odd_pair} ].

Definition ex_odd :
    @named_expr R Ar R_obj nil (tfun tunit tunit) :=
  [ snd {ex_even_odd_pair} ].
```

Both projection runs land in the **unit cone** as its zero element,
where `ex_even_run := ne_app ex_even ne_tt` and `ex_odd_run` likewise;
`precone_zero` in the one-dimensional unit cone is mass `0`, so these
two theorems are the certain-divergence statements of the mutual
recursion.

```coq
(* theories/programs/ex_even_odd.v — Section ExEvenOddRider *)
Theorem ex_even_cbv_diverges :
  Lfun (eD_cbv' ex_even_run) one1 = precone_zero.

Theorem ex_odd_cbv_diverges :
  Lfun (eD_cbv' ex_odd_run) one1 = precone_zero.
```

Each projection-then-apply starts from the pair value
`ex_even_odd_pair_cbv_value` and uses the homogeneity helper
`linhom_cone_one_zero` (with `cone_one_scale_rep`): a linhom out of
the one-dimensional unit cone that vanishes at `one1` is the zero
linhom, so the derelicted promoted-zero function evaluated at the unit
point is `precone_zero`.

> These are the statements a reader looking for "the mutual recursion
> diverges" should cite, and they are deliberately about the *runs*
> `ex_even_run` / `ex_odd_run`, never about `ex_even` and `ex_odd`
> themselves, whose denotations are promoted-zero functions rather than
> zero points. The proof reuses the same one-dimensionality argument
> that upgrades `ex_almost_loop_cbv_mass_one` to
> `ex_almost_loop_cbv_dirac`, here in the opposite direction: at the
> unit cone, vanishing at `one1` is already vanishing everywhere.

## Conditioning and rejection sampling

`condition f m` is the declarative operator: run the model `m`, keep the
value it produced with the acceptance probability of the predicate `f`,
and return it — an unnormalised measure. `reject f m` is the executable
one: run the model, accept the candidate `x` when `f x` says so,
otherwise discard it and retry with a fresh run. The acceptance test is
itself a program, a predicate `f : tb → tbool` applied by ordinary
application, and the retry loop may run forever, so termination is a
theorem here, not an assumption.

The chapter proves that the two operators agree:
`reject_normalises_condition` states, unconditionally and without
division, that $Z \cdot \llbracket\text{reject}\,f\,m\rrbracket U = \llbracket\text{condition}\,f\,m\rrbracket U$, at `ta = tunit`
over an arbitrary thunked model program; the model-level family carries
the arbitrary input type and return object. The combinators themselves
are generic in the input type `ta` and the return object `tb`, and the
model `m : ta → tb` is a program argument free to sample, score and
recurse, so it may diverge; the statements are sub-probability
honest and the missing mass reappears in `Z`. Score-based conditioning
through a bundled `testfn` is untouched by this design and lives on in
the standalone sampler `ex_reject` and in the score posterior; it is the
two combinators that read a boolean predicate instead. Six
abbreviations and the normaliser recur below.

- `f` — the acceptance test: a boolean program predicate for the two
  combinators, a bundled `testfn` for the standalone `ex_reject`.
- $\nu_M$ — the model's output sub-distribution, `reject_model_dist`.
- $m_0 := \nu_M(\text{setT})$ — its total mass.
- $t$ — the acceptance probability at a returned value: the true-weight
  `bc_t` of `sdist r`, the predicate applied to $\delta_r$ and a point of
  `bool_cone_car`.
- $I_f := \int t\,d\nu_M$ — the acceptance mass.
- $I_{Uf} U := \int_U t\,d\nu_M$ — the same pairing restricted to a measurable $U$.
- $Z := 1 - m_0 + I_f$ — the normaliser.

The eight entries run the argument once: the two combinators and their
give-up term, the conditioning law, the master identity at the model and
then the program level, the equivalence theorem, the sampler instance
`ex_reject` with its normalised posterior, and the deterministic corner.

| Example | Statement | Rocq |
|---|---|---|
| Fail, assert, and the two combinators | Closed programs over a boolean program predicate: assert-and-return conditioning, propose-accept-or-retry rejection, and the mass-zero give-up term. | `ne_reject`, `ne_condition`, `ne_fail` — theories/programs/reject_condition.v |
| The conditioning law: predicate reweighting | The conditioned output is the model's output reweighted by the acceptance probability $\int_U t\,d\nu_M$, semantically and through the interpreter. | `condition_model_E`, `condition_E`, `condition_prog_evidence` — theories/programs/ex_reject_model.v |
| The rejection master identity: model level | $Z \cdot \nu(U) = I_{Uf} U$ for every measurable $U$, unconditional and division-free, at an arbitrary return object. | `reject_model_master`, `reject_model_is_normalised`, `reject_model_zero` — theories/programs/ex_reject_model.v |
| The rejection master identity: program level | The same identity through the interpreter, over an arbitrary thunked model program and an arbitrary predicate program. | `reject_prog_master`, `reject_prog_is_normalised`, `reject_prog_zero` — theories/programs/ex_reject_model.v |
| The equivalence theorem | Rejection sampling normalises conditioning: $Z \cdot \llbracket\text{reject\_prog}\rrbracket U = \llbracket\text{condition\_prog}\rrbracket U$, division-free and unconditional. | `reject_normalises_condition`, `reject_prog_computes_condition` — theories/programs/ex_reject_model.v |
| ex_reject: the sampler instance | At `ex_sampler` with a unit-mass prior the identity becomes the classical $\int t\,d\mu \cdot \nu(U) = \int_U t\,d\mu$. | `ex_reject`, `ex_reject_master`, `ex_reject_comb_sampler_master` — theories/programs/examples.v; theories/programs/ex_reject_headline.v; theories/programs/ex_reject_model.v |
| The normalised posterior of ex_reject | With positive acceptance mass the sampler denotes $(\int_U f\,d\mu) / (\int f\,d\mu)$, terminates almost surely, normalises the score posterior. | `ex_reject_is_normalised_posterior`, `ex_reject_mass_one`, `ex_reject_normalises_score` — theories/programs/ex_reject_headline.v; theories/programs/cbv_marginals.v |
| Hard conditioning as the deterministic instance | A deterministic predicate makes `t` the indicator of the accept set; the give-up term denotes the zero measure. | `ne_fail_zero`, `bc_t` — theories/programs/ex_reject_model.v; theories/icones/bool_cone.v |

### Fail, assert, and the two combinators (`ne_reject`, `ne_condition`, `ne_fail`, `ne_assert`)

Both combinators are closed programs of type
`(tb → tbool) → (ta → tb) → (ta → tb)`, over an arbitrary input type
`ta` and an arbitrary return object `tb`. Concretely,
`reject f = fix rx. λm. λa. let x = m a in if f x then x else rx m a`,
while `condition f = λm. λa. let x = m a in let _ = (if f x then () else fail) in x`.
The predicate and the model are
both program arguments, and the terms use only `fix` / `\` / `@` / `if` /
`()` / `let` — no coin, no `Score`, no lift node, the acceptance test
being applied by ordinary application, `f x`. (A *lift node* is a
surface constructor whose denotation goes through a semantic lift —
`bern_lift` for a coin, `score_lift` for `Score`, `kernel_lift` for a
runtime-parameter draw.) They differ only
in the else-branch: `reject` retries a rejected draw at the same model
and input, `condition` gives up.

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

Giving up is `ne_fail`, namely `fail = (fix fail. λ_. fail ()) ()`, a
guarded diverging fixpoint — the CBV
lambda-guard is mandatory, since recursion must pass through a value —
and `ne_assert b` is `if b then () else fail`. The `let _ = assert (f x)
in x` reading of `ne_condition` is inlined in the source, because a
failed assert zeroes the mass whatever value follows.

```coq
(* theories/programs/reject_condition.v *)
Definition ne_fail {G : named_ctx Ar} {t : ppl_type Ar} : nexpr G t :=
  [ (fix "fail" ::: tfun tunit t in \ "_" ::: tunit => # "fail" @ ()) @ () ].

Definition ne_assert {G : named_ctx Ar} : nexpr G (tfun tbool tunit) :=
  [ \ "b" ::: tbool => (if # "b" then () else { ne_fail }) ].
```

The theorems below quantify over three values: the predicate is the
promotion `fpred!` of an arbitrary unit-ball map into the 2-point cone,
the model is the promotion `g!` of an arbitrary unit-ball map
`g : U⟦ta⟧ ⊸ FMeas`, and the input is an arbitrary setlike point $a_0$
(Diracs at `ta = tR`, the unit point at `ta = tunit`). Here a *unit-ball*
map is a linear map of cone-norm at most `1`, and a *setlike* point is one
fixed by the comonoid structure, `coalg_str x = x!`, hence copied and
discarded like an ordinary value. Every
lambda-written model and predicate denotes such a point (`ne_lam`,
`adj_psi_at_setlike` of `theories/programs/infra/cbv_anchors.v`), so no
generality is lost; $\nu_M := g(a_0)$ and
`sdist r` is the predicate applied to $\delta_r$.

> The design decision worth naming is that the acceptance test is a
> program argument like the model, not a semantic coin — applying it is
> ordinary application, so nothing in the combinators mentions `testfn`
> or a lift node. One term therefore covers both predicate regimes, a
> deterministic predicate giving hard conditioning and a coin predicate
> a randomised one; the second generality axis, an arbitrary return
> object `tb`, comes free from the object-generic let-law.

### The conditioning law: predicate reweighting (`condition_model_E`, `condition_model_mass`, `condition_E`, `condition_prog_evidence`)

Conditioning reweights: the conditioned model's output is $\int_U t\,d\nu_M$
for every measurable $U$, unnormalised, with the model evidence
$I_f := \int t\,d\nu_M$ at $U = \text{setT}$ ($\nu_M$ the model's output
sub-distribution, $t$ the acceptance probability at a returned value).
`condition_model_E` and its mass corollary
`condition_model_mass` state that semantically; `condition_E` and
`condition_prog_evidence` state it through the interpreter, at an
arbitrary model *program* and an arbitrary predicate *program*. Either
way the shape is that of `ex_score_posterior_cbv_E` — a prior reweighted
by a $[0,1]$ scalar — at an arbitrary model and an arbitrary predicate,
the predicate's acceptance probability standing where the score had a
fixed test function; neither statement is an instance of the other.

The program-level reading runs on four closed programs: a thunked model
`model_prog := λ_. Mbody`, a predicate `pred_prog := λx. Fbody`, the
model's run `model_run := model_prog ()`, and the conditioned model
`condition_prog`, that is `condition pred_prog model_prog ()`, at the
same unit input.

```coq
(* theories/programs/ex_reject_model.v — Section ReadableHeadlines *)
Definition model_prog : @named_expr R Ar R_obj nil (tfun tunit tR') :=
  [ \ "_" ::: tunit => {Mbody} ].

Definition pred_prog : @named_expr R Ar R_obj nil (tfun tR' tbool) :=
  [ \ "x" ::: tR' => {Fbody} ].

Definition model_run : @named_expr R Ar R_obj nil tR' :=
  [ {model_prog} @ () ].

Definition condition_prog : @named_expr R Ar R_obj nil tR' :=
  [ {ne_condition tunit tR'} @ {pred_prog} @ {model_prog} @ () ].
```

At the model level the law is stated against `cond_model_denot`, the CBV
application of the combinator value to `fpred!`, then `g!`, then `a₀`,
with `reject_model_dist g a0` for $\nu_M$; the mass corollary is the case
`U = setT`. (In the snippets `%:num` reads the underlying real of the
non-negative weight `bc_t` and `fine` projects `\bar R` to `R`; both are
bookkeeping.)

```coq
(* theories/programs/ex_reject_model.v — Section RejectModelCompat *)
Theorem condition_model_E (U : set (ar_carrier Ar B))
    (mU : measurable U) :
  fmeas_mu (cond_model_denot R_to_carrier_meas fpred g a0) U =
  \int[fmeas_mu (reject_model_dist g a0)]_(r in U) ((bc_t (sdist r))%:num)%:E.

Theorem condition_model_mass :
  fmeas_mu (cond_model_denot R_to_carrier_meas fpred g a0)
    [set: ar_carrier Ar B] =
  \int[fmeas_mu (reject_model_dist g a0)]_
     (r in [set: ar_carrier Ar B]) ((bc_t (sdist r))%:num)%:E.
```

Specialising the two values to the denotations `model_lin` and
`pred_lin` of `model_prog` and `pred_prog` gives the same two statements
in the $\llbracket\cdot\rrbracket$ notation the equivalence theorem consumes.

```coq
(* theories/programs/ex_reject_model.v — Section ReadableHeadlines *)
Theorem condition_E U (mU : measurable U) :
  ⟦ condition_prog ⟧ U = \int[⟦ model_run ⟧]_(x in U) ((bc_t (sdist x))%:num)%:E.

Theorem condition_prog_evidence :
  ⟦ condition_prog ⟧ [set: ar_carrier Ar R_obj] =
  \int[⟦ model_run ⟧]_(x in [set: ar_carrier Ar R_obj]) ((bc_t (sdist x))%:num)%:E.
Proof. exact: (condition_E measurableT). Qed.
```

Proof idea: one let-law application at $\nu_M$, no recursion. The
object-generic let-law `eD_let_int_obj`
(`theories/programs/infra/let_sample_law.v`) turns the bound model
application into a Lebesgue integral over $\nu_M$, and at each Dirac $\delta_r$
the assert-and-return continuation computes to the weighted point mass
$t(r)\cdot\delta_r$ by `bool_case` on `sdist r` (`cm_scrut_E`, `cm_assert_E`,
`cm_K_at_dirac`, with the discard kit `em_proj1_mor_unitE` and
`Lfun_scaleE`).

> This half of the chapter is deliberately recursion-free: the
> combinator's reduction chain is the rejection chain minus the fixpoint,
> so one application of the let-law replaces a Kleene argument. The two
> readings are kept apart on purpose — only the program-level pair
> composes literally with `reject_prog_master` in the equivalence
> theorem, and only the model-level pair carries the full generality over
> arbitrary return objects and unit-ball values.

### The rejection master identity: model level (`reject_model_master`, `reject_model_is_normalised`, `reject_model_mass`, `reject_model_mass_one`, `reject_model_zero`)

The semantic content of `reject`, in division-free form. Run the model
once and exactly one of three things happens: the predicate accepts
(mass $I_f$), it rejects and we retry (mass $m_0 - I_f$), or the model
diverges (mass $1 - m_0$). Only rejection loops, so a trial settles with
mass $1 - (m_0 - I_f) = Z$, and writing $\nu$ for the denotation of
`(reject f m) a` the master identity is $Z \cdot \nu(U) = I_{Uf} U$ (writing
$I_{Uf} U := \int_U t\,d\nu_M$ for the acceptance mass restricted to $U$,
with $\nu_M$ the model's output distribution and $t$ the acceptance
probability at a returned value) for every
measurable $U$, unconditionally — the geometric sum over retries, stated
without dividing.

```coq
(* theories/programs/ex_reject_model.v — Section RejectModelCompat *)
Theorem reject_model_master U (mU : measurable U) :
  ((1 - fine (fmeas_mu (reject_model_dist g a0) [set: ar_carrier Ar B])
      + fine (\int[fmeas_mu (reject_model_dist g a0)]_
                (x in [set: ar_carrier Ar B]) ((bc_t (sdist x))%:num)%:E))%R)%:E
    * fmeas_mu (reject_model_denot R_to_carrier_meas fpred g a0) U
  = \int[fmeas_mu (reject_model_dist g a0)]_(x in U) ((bc_t (sdist x))%:num)%:E.

Theorem reject_model_is_normalised :
  (0 < 1 - fine (fmeas_mu (reject_model_dist g a0) [set: ar_carrier Ar B])
     + fine (\int[fmeas_mu (reject_model_dist g a0)]_
               (x in [set: ar_carrier Ar B]) ((bc_t (sdist x))%:num)%:E))%R ->
  forall U, measurable U ->
  fmeas_mu (reject_model_denot R_to_carrier_meas fpred g a0) U =
  ((fine (\int[fmeas_mu (reject_model_dist g a0)]_(x in U) ((bc_t (sdist x))%:num)%:E)
    / (1 - fine (fmeas_mu (reject_model_dist g a0) [set: ar_carrier Ar B])
         + fine (\int[fmeas_mu (reject_model_dist g a0)]_
                   (x in [set: ar_carrier Ar B]) ((bc_t (sdist x))%:num)%:E)))%R)%:E.

Theorem reject_model_mass_one :
  fine (fmeas_mu (reject_model_dist g a0) [set: ar_carrier Ar B]) = 1%R ->
  0 < \int[fmeas_mu (reject_model_dist g a0)]_
        (x in [set: ar_carrier Ar B]) ((bc_t (sdist x))%:num)%:E ->
  fmeas_mu (reject_model_denot R_to_carrier_meas fpred g a0)
    [set: ar_carrier Ar B] = 1.
```

These statements all need the predicate to be *total*
(`cone_norm (sdist r) = 1`, that is `bc_t + bc_f = 1` at every returned
value), which is what lands the rejection weight `bc_f` on the
sub-probability normaliser; both intended regimes, a deterministic
bool-Dirac and a Bernoulli coin, are total. The further hypothesis
$0 < Z$ of `reject_model_is_normalised` is loop progress,
automatic once $0 < I_f$; at $U = \text{setT}$ it gives `reject_model_mass`,
$\nu(\text{setT}) = I_f / Z$, the probability that some trial eventually accepts,
and for a probability model ($m_0 = 1$) `reject_model_mass_one` sharpens
that to almost-sure termination. In the degenerate corner $Z = 0$ — a
probability model that never accepts, so the loop never terminates —
both sides of the master identity vanish. A separate corner is certain
rejection: at $t \equiv 0$ the denotation is the zero measure whatever $m_0$
is (`reject_model_zero`).

```coq
(* theories/programs/ex_reject_model.v — Section RejectModelCompat *)
Theorem reject_model_zero :
  (forall r : ar_carrier Ar B, (bc_t (sdist r))%:num = 0%R) ->
  reject_model_denot R_to_carrier_meas fpred g a0 = precone_zero.
```

Proof idea (`theories/programs/ex_reject_model.v`), in three moves.

- **To a chain.** `reject_comb_val_E`, `reject_after_f_val_E` and
  `reject_model_app_E` denote the closed program as the promoted
  `λf`-then-`fix "rx"` value and strip all three CBV applications by
  $\text{der} \circ \text{prom}$ cancellation (promotion sends a point `x` to
  `x!`, the counit `der` takes it back); `reject_model_sup_E` then reads the
  denotation as the `cone_sup_ball` of the iterates
  $\nu_n := \text{der}(\text{fix\_chain}\,\text{rm\_W0}\,n\,(g!))(a_0)$, evaluation and the counit
  `der` commuting with the Kleene supremum (`linhom_fun_sup_ball` twice,
  `Lfun_sup_ball`). The three computation laws used throughout
  (`adj_psi_at_setlike`, `eD_app_at_setlike`, `if_icones_at`) and the
  pointwise-sup reading `linhom_fun_sup_ball` are the shared setlike-point
  kit of `theories/programs/infra/cbv_anchors.v`, not local to this file.
- **One step.** `reject_model_iter_S` unfolds a step to the let-if body
  at the extended setlike environment, and `reject_model_if_at_dirac`
  computes it: the scrutinee is the applied predicate `sdist r`
  (`rm_scrut_E` through `eD_app_at_setlike`), and `bool_case` (via
  `if_icones_at`) keeps $\delta_r$ with weight $t(r)$ and takes the previous
  iterate $\nu_n$ with weight `bc_f`; the let-bound model application is
  $\nu_M$ (`rm_model_app_E`).
- **Sum.** `eD_let_int_obj` integrates the iterate over $\nu_M$, giving the
  affine recurrence `reject_model_iter_mass`, whose retry mass
  $\int \text{bc\_f}\,d\nu_M = m_0 - I_f$ (`rm_int_onem`, the generic
  `fmeas_int_compl` of `theories/mcones/fmeas.v`) keeps the model's own
  divergence mass out of the loop; the affine cascade `affine_iter_cvg`
  (`theories/prelude/geom_series.v`) at $a := I_{Uf} U$,
  $q := m_0 - I_f$ gives the limit $I_{Uf} U / (1 - q)$,
  `fmeas_kleene_sup_U_E` identifies it with $\nu(U)$, and $q = 1$ is the
  constantly-zero chain.

```coq
(* theories/programs/ex_reject_model.v *)
Lemma reject_model_iter_mass n U (mU : measurable U) :
  fmeas_mu (reject_model_iter n.+1) U =
  IUf U + ((m0 - fine If)%R)%:E * fmeas_mu (reject_model_iter n) U.
```

> The chapter's technical centre: a program that may loop forever is
> shown to denote an exact measure, `reject_model_master` carrying no
> hypothesis on the model at all. Two modelling decisions are load-bearing —
> stating the identity multiplicatively rather than as a quotient, so it
> survives the non-terminating corner, and isolating the model's own
> divergence mass from the rejection weight, so the per-trial contraction
> factor is $m_0 - I_f$ and not $1 - I_f$. Everything above the Kleene layer
> is reused machinery (`fix_comb`, `eD_let_int_obj`, `affine_iter_cvg`,
> `fmeas_kleene_sup_U_E`), already object-generic; the file contributes
> the dispatch computation and the recurrence, not new analysis.

### The rejection master identity: program level (`reject_prog_master`, `reject_prog_is_normalised`, `reject_prog_mass_one`, `reject_prog_zero`)

The same four statements read through the interpreter, at the thunked
model `model_prog = λ_. Mbody` and the predicate `pred_prog = λx. Fbody`
of the conditioning law, over arbitrary program bodies `Mbody` and
`Fbody`:
`reject_prog` is `ne_reject` applied to both and run at the unit input.
Here $\nu_M$ is literally $\llbracket\text{model\_run}\rrbracket$, so $Z$ reads
$1 - \llbracket\text{model\_run}\rrbracket(\text{setT}) + \int t\,d\llbracket\text{model\_run}\rrbracket$.
The master identity itself is
$Z \cdot \llbracket\text{reject\_prog}\rrbracket U = \int_U t\,d\llbracket\text{model\_run}\rrbracket$
for every measurable $U$.

```coq
(* theories/programs/ex_reject_model.v — Section ReadableHeadlines *)
Definition reject_prog : @named_expr R Ar R_obj nil tR' :=
  [ {ne_reject tunit tR'} @ {pred_prog} @ {model_prog} @ () ].
```

```coq
(* theories/programs/ex_reject_model.v — Section ReadableHeadlines *)
Theorem reject_prog_master U (mU : measurable U) :
  ((1 - fine (⟦ model_run ⟧ [set: ar_carrier Ar R_obj])
      + fine (\int[⟦ model_run ⟧]_(x in [set: ar_carrier Ar R_obj])
                ((bc_t (sdist x))%:num)%:E))%R)%:E
    * ⟦ reject_prog ⟧ U
  = \int[⟦ model_run ⟧]_(x in U) ((bc_t (sdist x))%:num)%:E.
```

The three corollaries transport likewise: the division form under loop
progress, almost-sure termination for probability models with positive
acceptance mass, and the zero measure under certain rejection.

```coq
(* theories/programs/ex_reject_model.v — Section ReadableHeadlines *)
Theorem reject_prog_is_normalised :
  (0 < 1 - fine (⟦ model_run ⟧ [set: ar_carrier Ar R_obj])
     + fine (\int[⟦ model_run ⟧]_(x in [set: ar_carrier Ar R_obj])
               ((bc_t (sdist x))%:num)%:E))%R ->
  forall U, measurable U ->
  ⟦ reject_prog ⟧ U =
  ((fine (\int[⟦ model_run ⟧]_(x in U) ((bc_t (sdist x))%:num)%:E)
    / (1 - fine (⟦ model_run ⟧ [set: ar_carrier Ar R_obj])
         + fine (\int[⟦ model_run ⟧]_(x in [set: ar_carrier Ar R_obj])
                   ((bc_t (sdist x))%:num)%:E)))%R)%:E.

Theorem reject_prog_mass_one :
  ⟦ model_run ⟧ [set: ar_carrier Ar R_obj] = 1 ->
  0 < \int[⟦ model_run ⟧]_(x in [set: ar_carrier Ar R_obj])
        ((bc_t (sdist x))%:num)%:E ->
  ⟦ reject_prog ⟧ [set: ar_carrier Ar R_obj] = 1.

Theorem reject_prog_zero U :
  (forall r : ar_carrier Ar R_obj, (bc_t (sdist r))%:num = 0%R) ->
  ⟦ reject_prog ⟧ U = 0.
```

Each proof is a one-line transport: rewrite `reject_prog` and
`model_run` by their value bridges (`reject_prog_val_E`,
`model_run_val_E`), then apply the object-generic model-level theorem at
`pred_lin`, `model_lin` and the unit input.

> The split from the model level is not duplication. That family
> quantifies over arbitrary unit-ball linear maps at an arbitrary return
> object — maximal generality, no program behind it — while this one
> quantifies over arbitrary programs `Mbody` and `Fbody` against `⟦·⟧`,
> the only form that composes syntactically with `condition_E`. Its
> price, a thunked model of type `tunit → tR` at the real object, is
> exactly the generality the model level is kept for.

### The equivalence theorem (`reject_normalises_condition`, `reject_prog_computes_condition`, `reject_normalises_condition_prob`)

The two operators compute the same distribution up to the normaliser
$Z := 1 - \llbracket\text{model\_run}\rrbracket(\text{setT}) + \int t\,d\llbracket\text{model\_run}\rrbracket$:
$Z \cdot \llbracket\text{reject\_prog}\rrbracket U = \llbracket\text{condition\_prog}\rrbracket U$, division-free and
unconditional. The sampler `reject_prog` and the conditioned run
`condition_prog` are the programs the two master identities already
fixed — `reject pred_prog model_prog ()` and
`condition pred_prog model_prog ()`, the same model program and the same
predicate program at the same unit input — so the statements compose
literally.

```coq
(* theories/programs/ex_reject_model.v — Section ReadableHeadlines *)
Theorem reject_normalises_condition U (mU : measurable U) :
  ((1 - fine (⟦ model_run ⟧ [set: ar_carrier Ar R_obj])
      + fine (\int[⟦ model_run ⟧]_(x in [set: ar_carrier Ar R_obj])
                ((bc_t (sdist x))%:num)%:E))%R)%:E
    * ⟦ reject_prog ⟧ U
  = ⟦ condition_prog ⟧ U.

Theorem reject_normalises_condition_prob U (mU : measurable U) :
  ⟦ model_run ⟧ [set: ar_carrier Ar R_obj] = 1 ->
  ⟦ condition_prog ⟧ [set: ar_carrier Ar R_obj] * ⟦ reject_prog ⟧ U
  = ⟦ condition_prog ⟧ U.
```

When the loop makes progress ($0 < Z$) the division form applies and
reads $\llbracket\text{reject\_prog}\rrbracket U = \llbracket\text{condition\_prog}\rrbracket U / Z$.

```coq
(* theories/programs/ex_reject_model.v — Section ReadableHeadlines *)
Theorem reject_prog_computes_condition :
  (0 < 1 - fine (⟦ model_run ⟧ [set: ar_carrier Ar R_obj])
     + fine (\int[⟦ model_run ⟧]_(x in [set: ar_carrier Ar R_obj])
               ((bc_t (sdist x))%:num)%:E))%R ->
  forall U, measurable U ->
  ⟦ reject_prog ⟧ U =
  ((fine (⟦ condition_prog ⟧ U)
    / (1 - fine (⟦ model_run ⟧ [set: ar_carrier Ar R_obj])
         + fine (\int[⟦ model_run ⟧]_(x in [set: ar_carrier Ar R_obj])
                   ((bc_t (sdist x))%:num)%:E)))%R)%:E.
```

The proof is two lines: rewrite the right-hand side by the conditioning
law `condition_E` and apply the master identity `reject_prog_master`,
both sides being $\int_U t\,d\llbracket\text{model\_run}\rrbracket$. The probability-model form
additionally identifies the normaliser with the evidence,
$1 - 1 + I_f = \llbracket\text{condition\_prog}\rrbracket(\text{setT})$, at the
acceptance mass $I_f := \int t\,d\llbracket\text{model\_run}\rrbracket$.

> Keeping both halves in one `⟦·⟧` framework is the payoff: the two
> operators are applied to the *same* model program and the *same*
> predicate at the *same* input, so "rejection sampling is correct" is an
> equation between denotations rather than an informal correspondence.
> The unconditional multiplicative form is what makes it honest for
> models that may diverge — no hypothesis on `Mbody`, and the case where
> neither side has mass included — with
> `reject_normalises_condition_prob`, normaliser equals evidence, as the
> textbook reading and a corollary, not the definition.

### ex_reject: the sampler instance (`ex_sampler`, `ex_reject`, `sampler_lin`, `inst_dist_E`, `ex_reject_comb_sampler_master`, `ex_reject_master`)

At the model `λ_. sample µ` (`ex_sampler`) with a unit-mass prior,
$\nu_M = \mu$ and $m_0 = 1$, and the master identity specialises to the
classical $\int t\,d\mu \cdot \nu(U) = \int_U t\,d\mu$. The standalone program `ex_reject`,
of type `tR`, was proved first and is kept as a regression anchor; it is
the one program of this chapter that still accepts through a bundled
`testfn`: sample the prior, flip the value coin `Bernoulli (test f x)`,
recurse on rejection through an explicit acceptance continuation. Readably,
`ex_reject = let rec rs accept = (let x = sample µ in if Bernoulli (test f x) then accept x else rs accept) in rs (λy. y)`.

```coq
(* theories/programs/examples.v *)
Definition ex_sampler : @named_expr R Ar R_obj nil (tfun tunit tR') :=
  [ \ "_" ::: tunit => sample m ].

Definition ex_reject : @named_expr R Ar (po_robj P) nil tR' :=
  [ let rec "rs" "accept" :=
      (let "x" := sample m in
       if Bernoulli (test f # "x")
       then # "accept" @ # "x"
       else # "rs" @ # "accept")
    in # "rs" @ (\ "y" ::: tR' => # "y") ].
```

Its theorems are proved directly in
`theories/programs/ex_reject_headline.v` against `reject_denot`, the
denotation of `ex_reject_cbv`; the master identity there is division-free
and graceful at $\int f\,d\mu = 0$. (`cR` coerces a carrier point to a real, so
`f (cR x)` is the test function read at a sampled value.)

```coq
(* theories/programs/ex_reject_headline.v — Section RejectHeadline *)
Theorem ex_reject_master U : measurable U ->
  \int[fmeas_mu mu]_(x in [set: ar_carrier Ar R_obj]) ((f (cR x))%:E)
    * fmeas_mu reject_denot U
  = \int[fmeas_mu mu]_(x in U) ((f (cR x))%:E).
```

The combinator's own sampler instance is the predicate-based version.
`sampler_lin` is the sampler model's linear map, `inst_dist_E` identifies
its output with the prior µ, and `ex_reject_comb_sampler_master`
re-derives the classical identity at `m₀ = 1` for an arbitrary total
predicate value.

```coq
(* theories/programs/ex_reject_model.v — Section SamplerInstance *)
Lemma inst_dist_E :
  reject_model_dist (ta := tunit) sampler_lin one1 = mu.

Theorem ex_reject_comb_sampler_master U (mU : measurable U) :
  ((\int[fmeas_mu mu]_(r in [set: ar_carrier Ar R_obj]) ((bc_t (sdist r))%:num)%:E) *
   fmeas_mu inst_denot U =
   \int[fmeas_mu mu]_(r in U) ((bc_t (sdist r))%:num)%:E)%E.
```

> Two programs, two independent proofs, one shape of answer — and the
> place where the two conditioning styles meet: `ex_reject` accepts
> through the `testfn` coin `Bernoulli (test f x)`, the combinator
> through a boolean program predicate, and at `m₀ = 1` both collapse the
> normaliser `Z` to the acceptance mass. The older headline stays a
> regression anchor precisely because nothing forces the two routes to
> agree a priori.

### The normalised posterior of ex_reject (`ex_reject_is_normalised_posterior`, `ex_reject_posterior_simple`, `ex_reject_mass_one`, `ex_reject_zero`, `ex_reject_normalises_score`)

The division form of the `ex_reject_master` identity of the previous
entry, at the standalone sampler `ex_reject`. When acceptance has positive mass,
`ex_reject` denotes the normalised posterior of the prior `µ` given the
test function `f`: writing $\nu$ for `reject_denot`, the denotation of
`ex_reject_cbv`, the headline identity is
$\nu(U) = (\int_U f\,d\mu) / (\int f\,d\mu)$ for every measurable $U$.

```coq
(* theories/programs/ex_reject_headline.v — Section RejectHeadline *)
Theorem ex_reject_is_normalised_posterior :
  0 < \int[fmeas_mu mu]_(x in [set: ar_carrier Ar R_obj]) ((f (cR x))%:E) ->
  forall U, measurable U ->
  fmeas_mu reject_denot U =
  ((fine (\int[fmeas_mu mu]_(x in U) ((f (cR x))%:E))
    / fine (\int[fmeas_mu mu]_(x in [set: ar_carrier Ar R_obj])
              ((f (cR x))%:E)))%R)%:E.
```

Three corollaries pin the corners: at $\int f\,d\mu = 1$ no normalisation is
needed and the denotation is the reweighted prior itself; positive
acceptance mass gives $\nu(\text{setT}) = 1$; and at $f \equiv 0$ the denotation is the
zero measure.

```coq
(* theories/programs/ex_reject_headline.v — Section RejectHeadline *)
Theorem ex_reject_posterior_simple :
  \int[fmeas_mu mu]_(x in [set: ar_carrier Ar R_obj]) ((f (cR x))%:E) = 1 ->
  forall U, measurable U ->
  fmeas_mu reject_denot U = \int[fmeas_mu mu]_(x in U) ((f (cR x))%:E).

Theorem ex_reject_mass_one :
  0 < \int[fmeas_mu mu]_(x in [set: ar_carrier Ar R_obj]) ((f (cR x))%:E) ->
  fmeas_mu reject_denot [set: ar_carrier Ar R_obj] = 1.

Theorem ex_reject_zero :
  (forall r : R, f r = 0%R) -> reject_denot = precone_zero.
```

Finally `ex_reject_normalises_score` is the equivalence at this instance,
stated in `theories/programs/cbv_marginals.v` where the score
posterior lives: at $\mu(\text{setT}) = 1$, rejection sampling normalises exactly
the score program's unnormalised posterior,
$(\int f\,d\mu) \cdot \nu_{\text{reject}}(U) = \nu_{\text{score}}(U)$.

```coq
(* theories/programs/cbv_marginals.v — Section ScorePosterior *)
Theorem ex_reject_normalises_score
    (Hmu1 : fmeas_mu mu [set: ar_carrier Ar R_obj] = 1)
    (U : set (ar_carrier Ar R_obj)) (mU : measurable U) :
  (\int[fmeas_mu mu]_(r in [set: ar_carrier Ar R_obj]) (f (cR r))%:E) *
  fmeas_mu
    (linhom_fun (ex_reject_cbv P R_to_carrier_meas pm f) one1) U =
  fmeas_mu
    (linhom_fun (ex_score_posterior_cbv P R_to_carrier_meas pm f) one1) U.
```

> Here the chapter lands back on a concrete program a reader can run in
> their head: that quotient is the textbook description
> of rejection sampling, proved of a program with an unbounded loop, so
> almost-sure termination `ex_reject_mass_one` is a theorem and the
> `f ≡ 0` corner is proved rather than excluded by hypothesis. This
> entry is also where soft, score-based conditioning is still the whole
> story — `ex_reject_normalises_score` pins `ex_reject` and
> `ex_score_posterior`, with its unnormalised identity
> `ex_score_posterior_cbv_E`, to the same measure.

### Hard conditioning as the deterministic instance (`ne_fail_zero`)

There is no separate hard-conditioning machinery: when the predicate is
deterministic — `sdist r` a Dirac of the 2-point cone `bool_cone_car` —
its true-weight $t$ is the indicator of the accept set
$A := \{ x \mid f x = \text{true} \}$, so $I_f$ becomes $\nu_M(A)$ and $I_{Uf} U$ becomes
$\nu_M(A \cap U)$. The conditioning law then reads
$\llbracket\text{condition}\,f\,m\rrbracket(U) = \nu_M(A \cap U)$, the unnormalised conditional, and the
master identity reads $Z \cdot \llbracket\text{reject}\,f\,m\rrbracket(U) = \nu_M(A \cap U)$ with
$Z = 1 - m_0 + \nu_M(A)$, which at $m_0 = 1$ is exactly $\nu_M(U \mid A)$. The
one dedicated fact is `ne_fail_zero`: the give-up term denotes the zero
measure.

```coq
(* theories/programs/ex_reject_model.v — Section FailZero *)
Theorem ne_fail_zero :
  Lfun (eD_cbv' (@ne_fail R Ar (po_robj P) G t)) gam = precone_zero.
```

Its Kleene chain from `⊥` is constant, so `ne_fail`
denotes `precone_zero` at every setlike unit-ball environment — the same
"divergence is the zero measure" reading the fixpoint semantics uses,
and exactly the else-branch that `ne_condition` runs on a rejected
value. A coin predicate gives the same identities as the deterministic
one, with `t` a density rather than an indicator.

> No indicator bridge, no primed statements, no second theory: hard and
> randomised conditioning differ only in which predicate value is
> plugged into the same master identity, and `bool_case` on `sdist r` is
> the single place the distinction is made. The price is the totality
> hypothesis `bc_t + bc_f = 1`, which both regimes satisfy but a wholly
> arbitrary program predicate need not.

## What is **not** formalised

The open items are CBV-side; the call-by-name interpretation and its
headlines are not gaps of this document — they live on the
`cbn-track` branch. Three former gaps are closed: mutual recursion at
product types (`ne_fix_mr` at products of free types elaborates
through the genuine Seely-transported fixpoint `fix_mr_comb`, with
the surface witness `ex_even_odd_pair` of the recursion chapter); the
operational content of that witness (`ex_even_cbv_diverges` /
`ex_odd_cbv_diverges` pin the projection runs `ex_even @ ()` /
`ex_odd @ ()` to the unit-cone zero — certain divergence, mass `0`);
and runtime-parameter distributions (`Gaussian( e1 , e2 )` /
`Uniform( e1 , e2 )` over the probability-kernel layer of
`theories/programs/distributions.v`, with the hierarchy demo
`ex_gaussian_walk`).

| Item | What it is | Why not yet |
|---|---|---|
| Runtime-parameter kernels for other distribution families | `pkernel` instances beyond `dirac` / `bernoulli` / `gaussian` / `uniform` (e.g. exponential, beta) and surface forms for them. | Each family needs its own parameter-measurability proof (the Fubini–Tonelli route of `measurable_normal_prob_pair`) and a totalisation convention for degenerate parameters; the kernel layer itself is generic and ready. |

These choices are deliberate; each requires substantial
infrastructure outside the current scope and does not block any
existing result.

---

## How to verify

```sh
make -j

# Basic sampling/scoring examples — the CBV marginals + the evidence
echo "Print Assumptions ex_random_constant_cbv_marginal." | \
  rocq top -Q theories Icones -l theories/programs/cbv_marginals.v
echo "Print Assumptions ex_random_linear_cbv_marginal."   | \
  rocq top -Q theories Icones -l theories/programs/cbv_marginals.v
echo "Print Assumptions ex_score_posterior_cbv_E."        | \
  rocq top -Q theories Icones -l theories/programs/cbv_marginals.v
echo "Print Assumptions ex_bayes_linear_cbv_evidence."    | \
  rocq top -Q theories Icones -l theories/programs/cbv_marginals.v

# Runtime-parameter distributions — the Gaussian hierarchy demo
echo "Print Assumptions ex_gaussian_walk_E."    | \
  rocq top -Q theories Icones -l theories/programs/kernel_anchors.v
echo "Print Assumptions ex_gaussian_walk_mass." | \
  rocq top -Q theories Icones -l theories/programs/kernel_anchors.v

# Recursive probabilistic examples — the CBV mass identities
echo "Print Assumptions ex_geom_cbv_mass_one."          | \
  rocq top -Q theories Icones -l theories/programs/ex_geom.v
echo "Print Assumptions ex_almost_loop_cbv_mass_one."   | \
  rocq top -Q theories Icones -l theories/programs/ex_almost_loop.v
echo "Print Assumptions ex_almost_loop_cbv_zero."       | \
  rocq top -Q theories Icones -l theories/programs/ex_almost_loop.v

# The rejection-sampling combinator — master identity, normalised
# distribution, and the instance bridge
echo "Print Assumptions reject_model_master."           | \
  rocq top -Q theories Icones -l theories/programs/ex_reject_model.v
echo "Print Assumptions reject_model_is_normalised."    | \
  rocq top -Q theories Icones -l theories/programs/ex_reject_model.v
echo "Print Assumptions ex_reject_comb_sampler_master." | \
  rocq top -Q theories Icones -l theories/programs/ex_reject_model.v

# The condition combinator — the conditioning law and the equivalence
echo "Print Assumptions condition_model_E."             | \
  rocq top -Q theories Icones -l theories/programs/ex_reject_model.v
echo "Print Assumptions condition_E."                   | \
  rocq top -Q theories Icones -l theories/programs/ex_reject_model.v
echo "Print Assumptions reject_normalises_condition."   | \
  rocq top -Q theories Icones -l theories/programs/ex_reject_model.v
echo "Print Assumptions reject_normalises_condition_prob." | \
  rocq top -Q theories Icones -l theories/programs/ex_reject_model.v
echo "Print Assumptions ex_bayes_linear_is_iter_condition." | \
  rocq top -Q theories Icones -l theories/programs/examples.v

# The standalone rejection sampler + the score pairing
echo "Print Assumptions ex_reject_master."              | \
  rocq top -Q theories Icones -l theories/programs/ex_reject_headline.v
echo "Print Assumptions ex_reject_is_normalised_posterior." | \
  rocq top -Q theories Icones -l theories/programs/ex_reject_headline.v
echo "Print Assumptions ex_reject_normalises_score."    | \
  rocq top -Q theories Icones -l theories/programs/cbv_marginals.v
```

Each command reports only `propositional_extensionality`,
`functional_extensionality_dep` and
`constructive_indefinite_description` (the classical-logic axioms of
`mathcomp-analysis`). Per-entry pages embed the precise identifier
name, file, and a GitHub link to the Rocq source.

For the underlying surface inductive and the CBV interpretation, see
the [PPL tab](../ppl/). For the paper-side
correspondence (§§ 2–9 ↔ Rocq), see the [Paper tab](../paper/).
