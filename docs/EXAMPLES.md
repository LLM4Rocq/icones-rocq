# End-to-end PPL example programs

Each surface program of `theories/programs/examples.v` is reproduced
here together with its correctness identities, all proved against the
call-by-value interpreter `eD` of `theories/programs/ppl_cbv.v`. The
programs are written in the direct-style `ppl_named` custom entry of
`theories/programs/ppl.v` (brackets `[ … ]` enter the entry; curly
braces `{ x }` escape back to plain Rocq), and together they exercise
every constructor of the language.

The centrepiece is the conditioning/rejection pair. `condition f m`
(`ne_condition`) is the Pyro-style soft conditioning operator: run the
model, keep the output with the acceptance probability of a program
predicate `f`, return it. `reject f m` (`ne_reject`) is the executable
sampler for the same target: run the model, accept the output with that
probability, retry on rejection. Both live in
`theories/programs/reject_condition.v`, built from `fix` / `\` / `@` /
`if` / `()` / `let` alone. The theorem `reject_normalises_condition`
(`theories/programs/ex_reject_model.v`) states that rejection sampling
computes the conditioned model's normalised distribution:
*Z · ⟦reject f m⟧ U = ⟦condition f m⟧ U* with
*Z := 1 − ν_M(setT) + ∫ t dν_M*, for an arbitrary probabilistic model —
a function value that is itself free to contain samples, scores and
recursion. Its sampler instance recovers textbook rejection sampling
(`ex_reject_comb_sampler_master`).

The non-recursive programs carry closed-form CBV marginal identities,
up to the model evidence of a higher-order Bayesian linear regression
(`ex_bayes_linear_cbv_evidence`,
`theories/programs/infra/cbv_marginals.v`), itself re-read as
iterated conditioning (`ex_bayes_linear_is_iter_condition`,
`theories/programs/examples.v`). A call-by-name interpretation of the
same surface programs is preserved on the `cbn-track` branch; main is
CBV-only.

The surface layer the programs are written in is documented in full in
[the surface-language chapter](../../ppl/chapters/ppl-ch-the-surface-language.html)
and demoed end to end by `ex_surface_demo` / `ex_surface_walk`
(`theories/programs/examples.v`). Its forms group as:

- **Coins and scores:** the constant coin `Bernoulli [| p |]` over a
  real literal, the value coin `Bernoulli e`, and the score `Score e`
  over the probability type `tProb`.
- **`tProb`-producing primitives:** `Sigmoid e`, `Gausslik e { s , y }`,
  `Gt0 e`, `test f e`, and `Const pr e` — each pushes a real value into
  `tProb`, and `InclP` reads it back. (`test f e` is the abstract
  test-function coin, folding the `po_into` factoring of a bundled
  `f : testfn` into `ptest`.)
- **Conditioning:** the Bayesian-conditioning operator
  `observe Gaussian e { s } y ≡ Score (Gausslik e { s , y })`, and the
  `reject` / `condition` combinators over a program predicate
  (`theories/programs/reject_condition.v`).
- **Application and distributions:** measurable function application
  `Meas { f , Hf } e`, bundled distributions `sample m`, the
  runtime-parameter forms `Gaussian( e1 , e2 )` / `Uniform( e1 , e2 )`,
  and the comparison coin `e1 > e2`.
- **Binders:** OCaml-style `let rec`.

The paper-side correspondence (§§ 2–9 ↔ Rocq) lives on the
[Paper tab](../paper/); the PPL infrastructure (the surface
inductive, the CBV interpretation, the fixpoint machinery, the
semantic laws) lives on the [PPL tab](../ppl/). This document covers
the examples themselves.

**Chapter map.** This tab has three chapters:

- [Basic sampling and scoring examples](../../examples/chapters/examples-ch-basic-sampling-and-scoring-examples.html) — five non-recursive programs: two random functions, a one-parameter score posterior, the higher-order Bayesian linear regression, and a two-level Gaussian hierarchy, each with a closed-form CBV marginal.
- [Recursive probabilistic examples](../../examples/chapters/examples-ch-recursive-probabilistic-examples.html) — `ne_fix` with the boolean cascade: bare divergence, the geometric counter, almost-sure termination, and even/odd mutual recursion.
- [Conditioning and rejection sampling](../../examples/chapters/examples-ch-conditioning-and-rejection-sampling.html) — the `reject` / `condition` combinators over a program predicate, the conditioning law, the master identity, the equivalence theorem, and the classical-sampler instance.

**Example catalogue.** Each row is one worked program (or headline law) and the one idea it demonstrates.

<table class="catalogue">
<thead><tr><th>Label</th><th>Program</th><th>Demonstrates</th></tr></thead>
<tbody>
<tr><td>Ex 1.1</td><td><code>ex_random_constant</code></td><td>a distribution over constant-output functions; the marginal recovers the prior</td></tr>
<tr><td>Ex 1.2</td><td><code>ex_random_linear</code></td><td>a random affine function — also the model of the Bayesian regression</td></tr>
<tr><td>Ex 1.3</td><td><code>ex_score_posterior</code></td><td>prior / score / return — the one-parameter unnormalised posterior</td></tr>
<tr><td>Ex 1.4</td><td><code>ex_bayes_linear</code></td><td>higher-order Bayesian linear regression, read as iterated conditioning</td></tr>
<tr><td>Ex 1.5</td><td><code>ex_gaussian_walk</code></td><td>a two-level Gaussian hierarchy via the runtime-parameter <code>Gaussian(e1,e2)</code></td></tr>
<tr><td>Ex 2.1</td><td><code>ex_loop</code></td><td>bare divergence — total mass 0</td></tr>
<tr><td>Ex 2.2</td><td><code>ex_geom</code></td><td>the geometric law from a fair-coin recursion</td></tr>
<tr><td>Ex 2.3</td><td><code>ex_almost_loop</code></td><td>almost-sure termination vs. divergence, keyed by the coin parameter</td></tr>
<tr><td>Ex 2.4</td><td><code>ex_even_odd_pair</code></td><td>mutual recursion at a product of function types</td></tr>
<tr><td>Def 3.1</td><td><code>ne_reject</code> / <code>ne_condition</code></td><td>the two combinators over a program predicate</td></tr>
<tr><td>Thm 3.2</td><td><code>condition_model_E</code></td><td>conditioning reweights the model by the acceptance probability</td></tr>
<tr><td>Thm 3.3</td><td><code>reject_model_master</code></td><td>the division-free rejection master identity</td></tr>
<tr><td>Thm 3.4</td><td><code>reject_normalises_condition</code></td><td>rejection sampling normalises the conditioned model</td></tr>
<tr><td>Ex 3.5</td><td><code>ex_reject</code></td><td>the classical rejection sampler as the sampler instance</td></tr>
<tr><td>Thm 3.6</td><td><code>ne_fail_zero</code></td><td>hard conditioning as the deterministic-predicate instance</td></tr>
</tbody>
</table>

---

## Basic sampling and scoring examples

**In this chapter:** [Ex 1.1](../../examples/sections/examples-sec-ex-1-1-constant-random-function.html) · [Ex 1.2](../../examples/sections/examples-sec-ex-1-2-random-linear-function.html) · [Ex 1.3](../../examples/sections/examples-sec-ex-1-3-scored-posterior.html) · [Ex 1.4](../../examples/sections/examples-sec-ex-1-4-bayesian-linear-regression.html) · [Ex 1.5](../../examples/sections/examples-sec-ex-1-5-gaussian-random-walk.html).

Five non-recursive end-to-end probabilistic programs: two
random-function programs, a one-parameter score program, the
higher-order Bayesian linear regression built from them, and a
two-level Gaussian hierarchy. The calculus shape mirrors the
higher-order probabilistic calculus of Heunen–Kammar–Staton–Yang
(*A Convenient Category for Higher-Order Probability Theory*); the
semantics is the integrable-cones model, not quasi-Borel spaces.

Each program ships a closed-form CBV identity tying its denotation to
the matching distribution, proved in
`theories/programs/infra/cbv_marginals.v` (the Gaussian hierarchy in
`theories/programs/infra/kernel_anchors.v`). Every proof takes the
same route: the let-at-sample integral law `eD_let_sample_int`
(`theories/programs/infra/let_sample_law.v`) turns each
`let x = sample µ in …` prefix into a Pettis integral over Diracs of
the prior; dereliction and evaluation at setlike test points push
inside the integral; the integrand computes pointwise down to a
Dirac integral.

### Ex 1.1 — Constant random function (`ex_random_constant`)

The constant-output random function. After sampling one random
constant $c \sim \mu$, the program returns $\lambda x.\, c$: every
call returns the same value, but the function itself was sampled from
$\mu$. The main identity is the marginal at a test point — derelicting
the promoted function value and evaluating at a test point recovers
the prior $\mu$.

| Result | Statement | Rocq |
|---|---|---|
| Def (`ex_random_constant`) | `let c := sample µ in λx. c` of type `tfun tR tR`: a distribution over a constant-output function space. | `ex_random_constant` — `theories/programs/examples.v` |
| Thm (`ex_random_constant_cbv_marginal`) | Derelicting the denotation and evaluating at any *probability* test point $x$ ($\mathtt{fmeas\_mu}\ x\ \mathtt{setT} = 1$) recovers the prior $\mu$, uniformly in the test point. | `ex_random_constant_cbv_marginal` — `theories/programs/infra/cbv_marginals.v` |
| Cor (`ex_random_constant_cbv_marginal_dirac`) | At a Dirac test point $\delta_{r_0}$ the marginal is the prior — Diracs are probabilities. | `ex_random_constant_cbv_marginal_dirac` — same file |
| Cor (`ex_random_constant_cbv_marginal_mass`) | The marginal's measure of every measurable $U$ equals $\mu(U)$. | `ex_random_constant_cbv_marginal_mass` — same file |

```coq
(* theories/programs/examples.v *)
Definition ex_random_constant :
    @named_expr R Ar R_obj nil (tfun tR' tR') :=
  [ let "c" := sample m in \ "x" ::: tR' => # "c" ].
```

```coq
(* theories/programs/infra/cbv_marginals.v — Section RandomConstantMarginal *)
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

```coq
(* theories/programs/infra/cbv_marginals.v — Section RandomConstantMarginal *)
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

Proof idea: the let-at-sample law turns the denotation into the
Pettis integral $\int (\ell_c)!\, \mu(dc)$ of the promoted closures
$\ell_c := \llbracket \lambda x.\, c \rrbracket(1 \otimes \delta_c)$
(the lambda clause promotes at the setlike one-Dirac environment,
`adj_psi_at_setlike`). Dereliction and evaluation at $x$ push inside
the integral (`icones_hom_pres_int` / `linhom_int_eval`); the
integrand computes to $\delta_c$ — the unused argument $x$ is
discarded silently, being a probability (`em_proj1_mor_probE`), and
the closure returns the captured constant; finally
$\int \delta_c\, \mu(dc) = \mu$ (`icone_integral_dirac_fmeas`).

The probability hypothesis on the test point is honest, not an
artifact. Discarding an argument in `EM(!)` is the comonoid counit,
which on `FMeas` weighs the kept output by the argument's total mass
(`coalg_e_FMeas_prob`); at $x = 0$ the marginal is $0$, not $\mu$.
Only mass-$1$ test points are discarded silently.

### Ex 1.2 — Random linear function (`ex_random_linear`)

A random-coefficients linear regression: sample slope $m$ and
intercept $b$ from $\mu$, return $\lambda x.\, m\cdot x + b$. It
exercises `ne_add` and `ne_mul` via the arithmetic lifts of
`theories/programs/ppl.v`; on Dirac inputs the lifts reduce to scalar
arithmetic (`add_lift_dirac` / `mul_lift_dirac`). This is also the
*model* of the Bayesian linear regression `ex_bayes_linear` below —
that program is literally `let "f" := ex_random_linear in …`.

| Result | Statement | Rocq |
|---|---|---|
| Def (`ex_random_linear`) | `let m := sample µ in let b := sample µ in λx. m·x + b` of type `tfun tR tR`: a random affine function, slope and intercept drawn independently from the prior. | `ex_random_linear` — `theories/programs/examples.v` |
| Thm (`ex_random_linear_cbv_marginal`) | Derelicted and evaluated at a Dirac test point $\delta_{r_0}$, the denotation's measure of every measurable $U$ is the iterated integral $\int\!\!\int \delta_{m\cdot r_0+b}(U)\, \mu(db)\, \mu(dm)$. | `ex_random_linear_cbv_marginal` — `theories/programs/infra/cbv_marginals.v` |
| Lem (`rl_inner_marginal`) | The inner continuation (one sample left) marginalises to a single integral over the intercept. | `rl_inner_marginal` — same file |

```coq
(* theories/programs/examples.v *)
Definition ex_random_linear :
    @named_expr R Ar R_obj nil (tfun tR' tR') :=
  [ let "m" := sample m in
    let "b" := sample m in
    \ "x" ::: tR' => # "m" * # "x" + # "b" ].
```

```coq
(* theories/programs/infra/cbv_marginals.v — Section RandomLinearMarginal *)
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

```coq
(* theories/programs/infra/cbv_marginals.v — Section RandomLinearMarginal *)
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
sample binders into nested Pettis integrals; dereliction and
evaluation at $\delta_{r_0}$ push inside both layers. At the
three-Dirac environment $(1 \otimes \delta_m \otimes \delta_b)
\otimes \delta_{r_0}$ (a setlike unit-ball point) the variable
projections return the three Diracs, the body computes through the
Dirac rules of `mul_lift` and `add_lift` to $\delta_{m\cdot r_0+b}$
(`rl_body_at`), and the per-$U$ evaluation of an `FMeas`-valued
Pettis integral (`icone_integral_fmeas_E`) lands the iterated
Lebesgue integral.

### Ex 1.3 — Scored posterior (`ex_score_posterior`)

Scoring a sampled parameter — the one-dimensional unnormalised
posterior, in the textbook prior / score / return shape: sample a
parameter $m$ from the prior $\mu$, score by a bundled $[0,1]$ test
function `f : testfn`, return $m$. The denotation's measure of every
measurable $U$ is $\int_U f\, d\mu$ — the prior reweighted by the
test pairing, with total mass $\int f\, d\mu$.

This program pairs with the conditioning/rejection chapter below:
`score` produces the unnormalised posterior, rejection sampling the
normalised one, and `ex_reject_normalises_score` (in that chapter's
closing section) connects the two exactly.

| Result | Statement | Rocq |
|---|---|---|
| Def (`ex_score_posterior`) | `let m := sample µ in let _ := Score (test f #"m") in #"m"` of type `tR`: sample, score the parameter by the abstract test-function coin `test f` of the bundled `f : testfn`, return the parameter. | `ex_score_posterior` — `theories/programs/examples.v` |
| Thm (`ex_score_posterior_cbv_E`) | The denotation's measure of every measurable $U$ is $\int_U f\, d\mu$ — the prior reweighted by the density, unnormalised. | `ex_score_posterior_cbv_E` — `theories/programs/infra/cbv_marginals.v` |
| Cor (`ex_score_posterior_cbv_mass`) | The total mass of the denotation is the evidence $\int f\, d\mu$. | `ex_score_posterior_cbv_mass` — same file |

```coq
(* theories/programs/examples.v *)
Definition ex_score_posterior :
    @named_expr R Ar (po_robj P) nil tR' :=
  [ let "m" := sample m in
    let "_" := Score (test f # "m") in
    # "m" ].
```

```coq
(* theories/programs/infra/cbv_marginals.v — Section ScorePosterior *)
Theorem ex_score_posterior_cbv_E (U : set (ar_carrier Ar R_obj))
    (mU : measurable U) :
  fmeas_mu
    (linhom_fun (ex_score_posterior_cbv R_carrier_meas R_to_carrier_meas
                   pm Hf_meas) one1) U =
  \int[fmeas_mu mu]_(r in U) (f (cR r))%:E.
```

```coq
(* theories/programs/infra/cbv_marginals.v — Section ScorePosterior *)
Theorem ex_score_posterior_cbv_mass :
  fmeas_mu
    (linhom_fun (ex_score_posterior_cbv R_carrier_meas R_to_carrier_meas
                   pm Hf_meas) one1)
    [set: ar_carrier Ar R_obj] =
  \int[fmeas_mu mu]_(r in [set: ar_carrier Ar R_obj]) (f (cR r))%:E.
```

Proof idea: the let-at-sample mass law `eD_let_sample_mu_E` turns the
denotation's measure of $U$ into an integral over $r \sim \mu$ of the
continuation's mass at the one-Dirac environment $1 \otimes \delta_r$.
There the score clause evaluates to the scalar $f(r)$ (`eD_score_E` +
`score_lift_dirac`), and the returned variable under the score binder
is computed by `em_proj1_mor_unitE`: a `tunit`-typed score result is
not setlike, so the first projection discards it as its scalar
weight, turning the score into the `precone_scale` factor $f(r)$ on
the returned $\delta_r$ (`sp_cont_at_dirac`). The Dirac's measure of
$U$ is the indicator, and the integral collapses to $\int_U f\, d\mu$.

### Ex 1.4 — Bayesian linear regression (`ex_bayes_linear`)

> **Key result:** the regression *is* iterated conditioning by definition (`ex_bayes_linear_is_iter_condition`, by `erefl`); its evidence is the double integral $\int\!\!\int \prod \mathtt{obs\_d}\, d\mu\, d\mu$.

The Bayesian linear regression of Staton–Yang–Heunen–Kammar–Wood
(arXiv 1701.02547 §2.1), in three steps.

First, the model is a random function: exactly `ex_random_linear`
above, a distribution over affine functions with slope and intercept
drawn from the prior.

Second, inference conditions the model on data. Each observation is a
`Record obs = MkObs { obs_x ; obs_y }` packaging a known input point
`obs_x` and observed datum `obs_y`. The likelihood noise is a single
fixed $\sigma = 1/2$ for every observation. Its density is the
envelope-normalised Gaussian likelihood
`obs_d o := gauss_obs_density (1/2) (obs_y o)`, i.e.
$\mathtt{obs\_d}\ o\ r = \mathtt{normal\_pdf}\ r\ (1/2)\ (\mathtt{obs\_y}\ o) / \mathtt{normal\_peak}\ (1/2) \in [0,1]$
(`theories/programs/ppl.v`) — surface form
`observe Gaussian (#"f" @ [|obs_x o|]) { 1/2 } (obs_y o) ≡ Score (Gausslik (#"f" @ [|obs_x o|]) { 1/2 , obs_y o })`
(mean expression first, then `{ stddev }`, then the observed datum).
The peak is intrinsic to the distribution, so the observation carries
no user-supplied envelope. Conditioning is a score: the model's value
`#"f" @ [|obs_x o|]` at the known input is scored by `obs_d o`. The
program samples the model once, binds it to `"f"`, folds the
observation list into `observe` steps, and returns `#"f"` — the
posterior over functions.

Third, the regression *is* iterated conditioning, by definition.
Scoring `#"f" @ [|obs_x o|]` by `obs_d o` is the score clause of the
next chapter's `condition` operator, at model `#"f"` and input
`obs_x o`; the only difference is A-normal form (`condition` binds
the model's value and returns it, while the regression scores the
application directly and returns the function at the end).
`condition_at o` packages one step, `iter_condition` folds it over a
meta-level list `l : seq (obs R)`, and `ex_bayes_linear l` is the
model bound once followed by `iter_condition` — agreement anchor
`ex_bayes_linear_is_iter_condition` holds by `erefl`. The raw
score-fold shape is the derived reading `ex_bayes_linear_obs_fold`,
and `ex_bayes_linear3` is the concrete 3-observation instance.

| Result | Statement | Rocq |
|---|---|---|
| Def (`ex_bayes_linear`) | Bind the random affine model to `"f"`, condition it on each observation of `l` in turn (`condition_at` / `iter_condition`) via `observe` and its density `obs_d` / `gauss_obs_density`, return `#"f"`. | `ex_bayes_linear`, `condition_at`, `iter_condition`, `obs_fold`, `obs_d`, `ex_bayes_linear3` — `theories/programs/examples.v` |
| Prop (`ex_bayes_linear_is_iter_condition`) | The regression equals the model bound once followed by the iterated-conditioning fold — definitionally. | `ex_bayes_linear_is_iter_condition`, derived reading `ex_bayes_linear_obs_fold` — same file |
| Thm (`ex_bayes_linear_cbv_evidence`) | For a general list $l$, the counit (total mass) of the function-space denotation is the evidence $\int\!\!\int \prod_{o\in l} \mathtt{obs\_d}\ o\ (m\cdot \mathtt{obs\_x}\ o + b)\, d\mu(b)\, d\mu(m)$. | `ex_bayes_linear_cbv_evidence` — `theories/programs/infra/cbv_marginals.v` |
| Cor (`ex_bayes_linear_cbv_evidence2`) | The literal 2-observation instance: the counit mass at `[:: o1; o2]` is $\int\!\!\int \mathtt{obs\_d}\ o_1\ (m\cdot x_1+b) \cdot \mathtt{obs\_d}\ o_2\ (m\cdot x_2+b)\, d\mu\, d\mu$. | `ex_bayes_linear_cbv_evidence2` — same file |

```coq
(* theories/programs/examples.v *)
Definition ex_bayes_linear (l : seq (obs R)) :
    @named_expr R Ar (po_robj P) nil (tfun tR' tR') :=
  ne_let "f"%string (ex_random_linear m)
    (iter_condition (nv_head "f"%string (tfun tR' tR') nil) l).
```

```coq
(* theories/programs/examples.v *)
Theorem ex_bayes_linear_is_iter_condition (l : seq (obs R)) :
  ex_bayes_linear l =
  ne_let "f"%string (ex_random_linear m)
    (iter_condition (nv_head "f"%string (tfun tR' tR') nil) l).
Proof. by []. Qed.
```

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

```coq
(* theories/programs/infra/cbv_marginals.v — Section BayesLinearEvidence *)
Theorem ex_bayes_linear_cbv_evidence (l : seq (obs R)) :
  ((c1_val (Lfun (coalg_e (tyD_cbv tF))
      (linhom_fun
         (ex_bayes_linear_cbv R_carrier_meas R_to_carrier_meas pm l)
         one1)))%:num)%R =
  fine (\int[fmeas_mu mu]_(m in [set: ar_carrier Ar R_obj])
     (fine (\int[fmeas_mu mu]_(b in [set: ar_carrier Ar R_obj])
        ((\prod_(o <- l) obs_d o (cR m * obs_x o + cR b))%R)%:E))%:E).
```

```coq
(* theories/programs/infra/cbv_marginals.v — Section BayesLinearEvidence *)
Theorem ex_bayes_linear_cbv_evidence2 (o1 o2 : obs R) :
  ((c1_val (Lfun (coalg_e (tyD_cbv tF))
      (linhom_fun
         (ex_bayes_linear_cbv R_carrier_meas R_to_carrier_meas pm
            [:: o1; o2])
         one1)))%:num)%R =
  fine (\int[fmeas_mu mu]_(m in [set: ar_carrier Ar R_obj])
     (fine (\int[fmeas_mu mu]_(b in [set: ar_carrier Ar R_obj])
        ((obs_d o1 (cR m * obs_x o1 + cR b) *
          obs_d o2 (cR m * obs_x o2 + cR b))%R)%:E))%:E).
```

Call-by-value matters here.

- **Sharing:** the sampled function is bound once and shared across
  every observation and the return — each access to `#"f"` goes
  through the comonoid duplication `coalg_d` of the let-clause
  diagonal at the function-type cone
  $!(U\llbracket \mathtt{tR} \rrbracket \multimap U\llbracket \mathtt{tR} \rrbracket)$.
  That duplication makes all observations score the *same* sampled
  function (and the posterior be over that function), not a fresh
  model per score.
- **Proof:** the per-$(m,b)$ weights factor out of the fold one
  observation at a time (`obs_fold_at`: the fold at the depth-$n$
  environment is the promoted closure scaled by
  $\prod_{o\in l} \mathtt{obs\_d}\ o\ (m\cdot x_o + b)$), and two
  applications of the let-at-sample law integrate the weights against
  the priors.

Cross-links: the model's own marginal identity is
`ex_random_linear_cbv_marginal` above; the one-parameter score
program is `ex_score_posterior` above.

### Ex 1.5 — Gaussian random walk (`ex_gaussian_walk`)

A two-level Gaussian hierarchy, written with the runtime-parameter
`Gaussian(e1,e2)` constructor (`ne_gaussian`,
[the runtime-parameter section of the surface
chapter](../../ppl/sections/ppl-sec-runtime-parameter-distributions.html)):
the second draw's parameter is the *sampled value* of the first. The
constant-parameter first stage is the kernel surface at real literals
(`eD_gaussian_sample_agree` pins it to the bundled
`sample (gaussian 0 1)` form).

| Result | Statement | Rocq |
|---|---|---|
| Def (`ex_gaussian_walk`) | `let s := Gaussian(0,1) in Gaussian(s,1)` of type `tR`: the first draw's sampled value parameterises the second. | `ex_gaussian_walk` — `theories/programs/examples.v` |
| Thm (`ex_gaussian_walk_E`) | The denotation's measure of every measurable $U$ is the hierarchy integral $\int \mathcal{N}(\mathtt{cR}\ r, 1)(\mathtt{toC}^{-1}\, U)\, d\mathcal{N}(0,1)(r)$. | `ex_gaussian_walk_E` — `theories/programs/infra/kernel_anchors.v` |
| Cor (`ex_gaussian_walk_mass`) | The program is a probability: total mass exactly $1$. | `ex_gaussian_walk_mass` — same file |

```coq
(* theories/programs/examples.v *)
Definition ex_gaussian_walk : @named_expr R Ar R_obj nil tR' :=
  [ let "s" := Gaussian( [| 0%R |] , [| 1%R |] ) in
    Gaussian( # "s" , [| 1%R |] ) ].
```

```coq
(* theories/programs/infra/kernel_anchors.v *)
Lemma ex_gaussian_walk_E (U : set (ar_carrier Ar R_obj)) :
  measurable U ->
  fmeas_mu (linhom_fun (eD' ex_gaussian_walk) one1) U =
  \int[fmeas_mu gw_prior]_(r in [set: ar_carrier Ar R_obj])
     (fine (normal_prob (cR r) 1 (toC @^-1` U)))%:E.

Lemma ex_gaussian_walk_mass :
  fmeas_mu (linhom_fun (eD' ex_gaussian_walk) one1)
    [set: ar_carrier Ar R_obj] = 1.
```

Proof idea: the general let-law `eD_let_mu_E`
(`theories/programs/infra/let_sample_law.v`) turns the denotation's
measure of $U$ into an integral of the body's mass at the one-Dirac
environment $1 \otimes \delta_r$ against the bound sub-distribution —
here the first stage, which the setlike/Dirac anchor `eD_gaussian_at`
computes to the transported prior $\mathcal{N}(0,1)$. Under the
binder, `#"s"` projects to $\delta_r$ and the literal `[|1|]` to
$\delta_{\mathtt{toC}\, 1}$, so the same anchor computes the body to
the gaussian kernel at $(r, 1)$, whose per-$U$ reading
(`gaussian_ker_cast_E`) is $\mathcal{N}(\mathtt{cR}\ r, 1)(\mathtt{toC}^{-1}\, U)$.
For the mass corollary the integrand is identically $1$ (the kernel
is a pointwise probability, `gaussian_kernel_norm1`) and
$\int 1\, d\mathcal{N}(0,1) = 1$ (`fmeas_of_prob_setT`).

---

## Recursive probabilistic examples

**In this chapter:** [Ex 2.1](../../examples/sections/examples-sec-ex-2-1-bare-divergence.html) · [Ex 2.2](../../examples/sections/examples-sec-ex-2-2-geometric-distribution.html) · [Ex 2.3](../../examples/sections/examples-sec-ex-2-3-almost-sure-termination.html) · [Ex 2.4](../../examples/sections/examples-sec-ex-2-4-even-odd-mutual-recursion.html).

Recursive probabilistic programs combining `ne_fix` with the boolean
cascade, exhibiting productive partial termination. The CBV mass
identities — plus, for the two halting samplers, full distribution
refinements pinning the denotations as *measures* — are proved in
`theories/programs/ex_reject_headline.v` against the seeded
value-fixpoint interpreter (`fix_comb`,
[the CBV value-fixpoint chapter](../../ppl/chapters/ppl-ch-the-cbv-value-fixpoint-at-function-types.html)),
by the same reduction-chain-plus-affine-cascade recipe as the next
chapter's rejection sampler.

### Ex 2.1 — Bare divergence (`ex_loop`)

> **Key result:** no sampling, no scoring — an infinite chain of unit-typed recursive calls of total mass $0$.

Bare divergence: `let rec l _ = l () in l ()` of type `tunit`. With no
sampling or scoring and no termination, the program denotes the zero
sub-distribution: total mass $0$.

```coq
(* theories/programs/examples.v *)
Definition ex_loop :
    @named_expr R Ar R_obj nil tunit :=
  [ let rec "l" "_" ::: tunit ==> tunit := # "l" @ ()
    in # "l" @ () ].
```

No standalone CBV identity is recorded for the bare loop: the
certain-divergence statement for this shape is carried by the
parameterised twin at $p = 0$. `ex_almost_loop_cbv_zero` below pins
the Bernoulli-guarded loop with a never-succeeding coin to
`precone_zero`, and `ex_loop` is that loop with the coin erased.

### Ex 2.2 — Geometric distribution (`ex_geom`)

> **Key result:** the fair-coin counter halts almost surely (total mass $1$) and its law is exactly the geometric series $\sum_k (1/2)^{k+1}\delta_k$ (`ex_geom_cbv_distribution`).

A geometric counter from a fair-coin Bernoulli recursion (the
constant-literal coin `Bernoulli [| (1/2 : R) |]`): each call halts
with probability $\tfrac12$ (returning $0$), else recurses, adding $1$
to the returned real. The program denotes a measure of total mass $1$
— the sampler halts almost surely — and that measure is the geometric
law: on every measurable $U$ the denotation is the series
$\sum_k (1/2)^{k+1}\delta_k(U)$ (`ex_geom_cbv_distribution`), with the
atom at the embedded natural $k$ carrying mass exactly $(1/2)^{k+1}$
(`ex_geom_cbv_pmf`). The embedded point
`gpt k := R_to_carrier R_carrier_eq (k%:R)` places $k$ in the real
carrier; the points are distinct (`gpt_inj`) and each singleton is
measurable (`measurable_gpt`). The mass identity
`ex_geom_cbv_mass_one` is the $U = \mathtt{setT}$ specialisation, where
the geometric weights sum to $1$.

| Result | Statement | Rocq |
|---|---|---|
| Def (`ex_geom`) | `let rec g _ = if Bernoulli [| (1/2:R) |] then 0 else 1 + g () in g ()` of type `tR` — the fair coin is the constant-literal `Bernoulli [| (1/2:R) |]`, its $[0,1]$ bounds discharged by `lra`. | `ex_geom` — `theories/programs/examples.v` |
| Thm (`ex_geom_cbv_mass_one`) | Total mass one on the whole carrier: the sampler halts almost surely. | `ex_geom_cbv_mass_one` — `theories/programs/ex_reject_headline.v` |
| Thm (`ex_geom_cbv_distribution`) | On every measurable $U$ the denotation is the geometric series $\sum_k (1/2)^{k+1}\delta_{\mathtt{gpt}\,k}(U)$. | `ex_geom_cbv_distribution` — same file |
| Thm (`ex_geom_cbv_pmf`) | The atom at the embedded natural $\mathtt{gpt}\,k$ carries mass exactly $(1/2)^{k+1}$: the geometric PMF. | `ex_geom_cbv_pmf` — same file |

```coq
(* theories/programs/examples.v *)
Definition ex_geom : @named_expr R Ar (po_robj P) nil tR' :=
  [ let rec "g" "_" ::: tunit ==> tR' :=
      (if Bernoulli [| (1 / 2 : R) |]
       then [| 0%R |]
       else [| 1%R |] + # "g" @ ())
    in # "g" @ () ].
```

```coq
(* theories/programs/ex_reject_headline.v — Section GeomRider *)
Theorem ex_geom_cbv_mass_one :
  fmeas_mu g_denot [set: ar_carrier Ar R_obj] = 1.
```

```coq
(* theories/programs/ex_reject_headline.v — Section GeomRider
   gpt k := R_to_carrier R_carrier_eq (k%:R : R)
   geom_w k := (((1 / 2 : R) ^+ k.+1)%:E) *)
Theorem ex_geom_cbv_distribution (U : set (ar_carrier Ar R_obj))
    (mU : measurable U) :
  fmeas_mu g_denot U =
  \sum_(k <oo) geom_w k * fmeas_mu (dirac_fmeas (gpt k)) U.
```

```coq
(* theories/programs/ex_reject_headline.v — Section GeomRider *)
Theorem ex_geom_cbv_pmf (k : nat) :
  fmeas_mu g_denot [set gpt k] = ((1 / 2 : R) ^+ k.+1)%:E.
```

(`g_denot` abbreviates
`linhom_fun (ex_geom_cbv R_carrier_meas R_to_carrier_meas) one1`,
the CBV denotation of the closed program at the unit context point.)
Proof idea: the rejection-sampling reduction chain on a simpler
program. The outer application collapses by `der`$\circ$`prom`
cancellation (`ex_geom_app_E`), and the denotation is the
`cone_sup_ball` of the per-iterate measures (`ex_geom_sup_E`). One
Kleene step gives the boolean dispatch
$\nu_{n+1} = \tfrac12\delta_0 + \tfrac12\,(\mathtt{add\_lift}\,(\delta_1 \otimes \nu_n))$
(`g_step`).

- **Mass:** translation-mass invariance `add_lift_mass` reduces the
  mass cascade to $x_{n+1} = \tfrac12 + \tfrac12 x_n$ (`g_val_S`); the
  affine cascade and sup-mass bridge of
  `theories/programs/infra/affine_cascade.v` close the limit at $1$.
- **Distribution:** the same induction runs per set. The per-$U$ step
  recurrence `g_iter_U_S` splits the THEN branch into $\tfrac12\delta_0$
  and the ELSE branch into the previous iterate pushed forward by $+1$
  (`g_shift_atom`), so the $n$-th iterate is the truncated geometric law
  $\sum_{k<n} (1/2)^{k+1}\delta_{\mathtt{gpt}\,k}$ (`g_iter_closed`). The
  partial sums converge to the full ereal series (`g_iter_series_cvg`)
  through the same `cone_sup_ball` limit, giving
  `ex_geom_cbv_distribution`; evaluating at the singleton `[set gpt k]`
  isolates the single surviving atom for `ex_geom_cbv_pmf`.

### Ex 2.3 — Almost-sure termination (`ex_almost_loop`)

A parameterised Bernoulli cascade: with probability $p$ the recursion
halts (returning `()`), with probability $1 - p$ it recurses. For
$p > 0$ the program terminates almost surely (total mass $1$); at
$p = 0$ it diverges (total mass $0$). The dichotomy is an honest
theorem pair: the denotation at `tunit` is a point of the unit cone
(the CBV `tunit` is the terminal coalgebra on `cone_one_car`), so the
termination probability is the point's norm. For $p > 0$ the denotation
is moreover pinned as the *element* `one1` — the unit point, the Dirac
on the one-point space — strengthening the norm identity to the point
itself (`ex_almost_loop_cbv_dirac`), since a norm-one element of the
one-dimensional unit cone is `one1` (`cone_one_norm_eq1`).

| Result | Statement | Rocq |
|---|---|---|
| Def (`ex_almost_loop`) | `let rec l _ = if Bernoulli (Const pr [|0|]) then () else l () in l ()` of type `tunit`. The parameter is a bundled probability `pr : prob`; `Const pr` is the constant `tProb`-value coin carrying its $[0,1]$ bounds, so the program needs no loose witnesses. | `ex_almost_loop` — `theories/programs/examples.v` |
| Thm (`ex_almost_loop_cbv_mass_one`) | For every $p > 0$ the denotation has norm one: almost-sure termination. | `ex_almost_loop_cbv_mass_one` — `theories/programs/ex_reject_headline.v` |
| Thm (`ex_almost_loop_cbv_dirac`) | For every $p > 0$ the denotation IS the unit point `one1` (the Dirac on the one-point space), strengthening the norm identity to the element. | `ex_almost_loop_cbv_dirac` — same file |
| Thm (`ex_almost_loop_cbv_zero`) | At $p = 0$ the denotation is the zero point of the unit cone: the loop diverges with probability one. | `ex_almost_loop_cbv_zero` — same file |

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

```coq
(* theories/programs/ex_reject_headline.v — Section AlmostLoopRider *)
Theorem ex_almost_loop_cbv_mass_one : (0 < p)%R ->
  cone_norm al_denot = 1%R.

Theorem ex_almost_loop_cbv_zero : p = 0%R -> al_denot = precone_zero.
```

```coq
(* theories/programs/ex_reject_headline.v — Section AlmostLoopRider *)
Theorem ex_almost_loop_cbv_dirac : (0 < p)%R -> al_denot = one1.
```

(`al_denot` abbreviates
`linhom_fun (ex_almost_loop_cbv R_carrier_meas R_to_carrier_meas pr) one1`,
and `p := pr_val pr`; the $0 \leq p \leq 1$ bounds travel inside the
bundled `pr : prob`, so the program carries no loose witnesses.)
Proof idea: as for the geometric counter — reduce to the
`cone_sup_ball` of the iterate points (`ex_almost_loop_sup_E`),
compute one Kleene step to the scalar recurrence
$\mathtt{al\_val}\,(n{+}1) = p + (1-p)\,\mathtt{al\_val}\,n$
(`al_step` / `al_val_S`), and close with `affine_iter_cvg_real`: the
limit $p / (1 - (1-p)) = 1$ for $p > 0$, the constantly-zero chain at
$p = 0$. The element identity is then immediate: the unit cone is
one-dimensional, so `cone_one_norm_eq1` upgrades the norm-one fact to
`al_denot = one1`.

### Ex 2.4 — Even/odd mutual recursion (`ex_even_odd_pair`)

The mutual-recursion witness. `ne_fix_mr` binds one recursive name
`p` at the free-coalgebra type
`tprod (tfun tunit tunit) (tfun tunit tunit)` — a pair of functions —
and each component calls the other via the `fst` / `snd` projections of
the rec-bound product. This is the classic even/odd shape: `ex_even` is
$\lambda n.\, \mathtt{snd}\ p\ n$, `ex_odd` is
$\lambda n.\, \mathtt{fst}\ p\ n$, so each component delegates to the
*other* with **no base case**. The closed runs `ex_even @ ()` and
`ex_odd @ ()` never terminate: honest divergence, mass $0$.

Both projection runs land in the **unit cone** as its zero element.
`ex_even_cbv_diverges` and `ex_odd_cbv_diverges` state
`Lfun (eD_cbv' ex_even_run) one1 = precone_zero` (resp. `ex_odd_run`),
where `ex_even_run := ne_app ex_even ne_tt` — certain divergence, since
`precone_zero` in the one-dimensional unit cone is mass $0$.

The accuracy point: the **pair** denotation is *not* the cone-zero.
`ex_even_odd_pair_cbv_value` shows the pair value is
`(precone_zero : L)! ⊗p (precone_zero : L)!` — a pair of
*promoted-zero functions* $0!\otimes_{\mathrm p}0!$, the backward Seely
transport of the promoted base-cone zero, which is provably never the
cone-zero (`eD_fix_mr_prod_at_setlike_neq0`,
`theories/programs/infra/cbv_fix_unfold.v`). The mass-$0$ content
appears **only** after projecting (`fst` / `snd`) *and* applying to
`()`, landing in the unit cone. The CBV denotation elaborates through
the genuine Seely-transported fixpoint path `fix_mr_comb` of
`theories/programs/ppl_cbv.v` (`fix_mr_clause` at `tprod`), built on
`theories/programs/infra/em_fix_mr.v` — see the PPL tab's
value-fixpoint chapter.

| Result | Statement | Rocq |
|---|---|---|
| Def (`ex_even_odd_pair`) | $\mathtt{fix\_mr}\ p : (1\to 1) \times (1\to 1).\ (\lambda n.\, \mathtt{snd}\ p\ n,\ \lambda n.\, \mathtt{fst}\ p\ n)$ — one recursive name bound at a pair of function types, each component calling the other. | `ex_even_odd_pair`, `ex_even_odd_pair_cbv` — `theories/programs/examples.v` |
| Def (`ex_even` / `ex_odd`) | The two projections of the recursive pair. | `ex_even`, `ex_odd` — same file |
| Thm (`ex_even_cbv_diverges`) | The closed run `ex_even @ ()` lands in the unit cone as the zero element — mass $0$, certain divergence. | `ex_even_cbv_diverges` — `theories/programs/ex_reject_headline.v` |
| Thm (`ex_odd_cbv_diverges`) | The closed run `ex_odd @ ()` likewise denotes the unit-cone zero — mass $0$. | `ex_odd_cbv_diverges` — same file |
| Lem (`ex_even_odd_pair_cbv_value`) | The pair denotation is $0!\otimes_{\mathrm p}0!$, the pair of promoted-zero functions — *not* the cone-zero. Divergence is the statement about the projections applied to `()`. | `ex_even_odd_pair_cbv_value` — same file |

```coq
(* theories/programs/examples.v *)
Definition ex_even_odd_pair :
    @named_expr R Ar R_obj nil pair_ty :=
  [ fix_mr "p" as pair_ty by erefl
       in ({ex_even_odd_lam_a}, {ex_even_odd_lam_b}) ].
```

```coq
(* theories/programs/examples.v *)
Definition ex_even :
    @named_expr R Ar R_obj nil (tfun tunit tunit) :=
  [ fst {ex_even_odd_pair} ].

Definition ex_odd :
    @named_expr R Ar R_obj nil (tfun tunit tunit) :=
  [ snd {ex_even_odd_pair} ].
```

(`pair_ty` abbreviates `tprod (tfun tunit tunit) (tfun tunit tunit)`;
the two spliced lambdas are $\lambda n.\, \mathtt{snd}\ \#\mathtt{"p"}\ @\ \#\mathtt{"n"}$
and $\lambda n.\, \mathtt{fst}\ \#\mathtt{"p"}\ @\ \#\mathtt{"n"}$.)

```coq
(* theories/programs/ex_reject_headline.v — Section ExEvenOddRider *)
Theorem ex_even_cbv_diverges :
  Lfun (eD_cbv' ex_even_run) one1 = precone_zero.
```

```coq
(* theories/programs/ex_reject_headline.v — Section ExEvenOddRider *)
Theorem ex_odd_cbv_diverges :
  Lfun (eD_cbv' ex_odd_run) one1 = precone_zero.
```

```coq
(* theories/programs/ex_reject_headline.v — Section ExEvenOddRider *)
Lemma ex_even_odd_pair_cbv_value :
  Lfun (eD_cbv' (ex_even_odd_pair : @named_expr R Ar R_obj nil pair_ty))
       one1 =
  (precone_zero : L)! ⊗p (precone_zero : L)!.
```

(`ex_even_run := ne_app ex_even ne_tt`, `ex_odd_run` likewise;
`Lfun h` abbreviates the underlying cones-hom function, `_!` is `prom`,
and $\_\otimes_{\mathrm p}\_$ the `ptensor` of the promoted unit-cone
homset `L`.)

**Proof idea.**

- **Chain stays zero:** seeded at the cone-zero, the zero-seeded
  interleaved-Kleene chain stays there — `even_odd_iter_zero` shows
  every iterate `fix_chain eo_W0 n = precone_zero` by induction (each
  step is $\mathtt{der}\ 0! = 0$). Hence the value-fixpoint at the base
  cone is the sup of zero iterates, `ex_even_odd_fix_value_zero`.
- **Pair value:** feeding this through the semantic computation law
  `eD_fix_mr_prod_at_setlike` gives the pair value $0!\otimes_{\mathrm p}0!$.
- **Projections:** each projection-then-apply uses the homogeneity
  helper `linhom_cone_one_zero` (with `cone_one_scale_rep`) — a linhom
  out of the one-dimensional unit cone that vanishes at `one1` is the
  zero linhom, so the derelicted promoted-zero function at the unit
  point is `precone_zero`.

---

## Conditioning and rejection sampling

**In this chapter:** [Def 3.1](../../examples/sections/examples-sec-def-3-1-the-reject-and-condition-combinators.html) · [Thm 3.2](../../examples/sections/examples-sec-thm-3-2-the-conditioning-law.html) · [Thm 3.3](../../examples/sections/examples-sec-thm-3-3-the-rejection-master-identity.html) · [Thm 3.4](../../examples/sections/examples-sec-thm-3-4-the-equivalence-theorem.html) · [Ex 3.5](../../examples/sections/examples-sec-ex-3-5-specialising-to-a-sampler.html) · [Thm 3.6](../../examples/sections/examples-sec-thm-3-6-hard-conditioning-as-the-deterministic-instance.html).

Conditioning is the declarative side of Bayesian inference:
`condition f m` runs the model `m`, keeps the value with the acceptance
probability of a **program predicate** `f`, and returns it — the model's
output reweighted by acceptance, as an unnormalised measure. Rejection
sampling is the executable side: `reject f m` runs the model to propose a
candidate `x`, accepts it with that same probability, and on rejection
retries with a fresh run — a loop that may run forever, so termination is
a theorem, not an assumption.

The acceptance test is **itself a program**, a predicate
`f : b → tbool` on the output value, passed as an argument like the model
`m : a → b`. Applying it is ordinary application `# "f" @ # "x"` — no
lift node, no `ne_test`. Since `tbool` is not `bool` but a point of the
2-point sub-probability cone `bool_cone_car`, $\llbracket f\,x\rrbracket$
is the *acceptance distribution* at $x$, and its true-mass
$t(x) := (\texttt{bc\_t}\,\llbracket f\,x\rrbracket)\%{:}\texttt{num} \in [0,1]$
is the acceptance probability — the only quantity the combinators read.
Two regimes, one mechanism: a **deterministic** predicate
($\llbracket f\,x\rrbracket$ a Dirac) gives $t = 1_A$, the indicator of
the accept set $A := \{\, x \mid f\,x = \texttt{true}\,\}$ (hard
conditioning); a **coin** predicate ($\llbracket f\,x\rrbracket$
non-Dirac) gives a density $t$ (soft conditioning). The pairing
$\int t\,d\nu_M$ is the whole content of the headline theorems:
$\int t\,d\nu_M \cdot \nu(U) = \int_U t\,d\nu_M$, acceptance probability
paired against the model's output measure over $U$.

The test enters a program through the `test f e` coin: evaluate `f` at
runtime value `e`, landing in `tProb` — the object-language counterpart
of that pairing. (The `observe Dist y` form is the special case where the
test is a concrete distribution's peak-normalised density.)

Keeping `f` abstract is the point: a concrete density is just one test,
so an opaque `f` makes the theorems hold for every test at once.

The chapter proves the two sides agree. `reject_normalises_condition`
states, division-free and unconditionally, that
$$Z \cdot \llbracket \texttt{reject}\,f\,m\rrbracket\,U = \llbracket \texttt{condition}\,f\,m\rrbracket\,U, \qquad Z := 1 - \nu_M(\texttt{setT}) + \int t\,d\nu_M,$$
where $\nu_M$ is the model's output sub-distribution and $t$ the
acceptance probability. If the model diverges, $\nu_M(\texttt{setT}) < 1$
and the $1 - \nu_M(\texttt{setT})$ term carries the missing mass. The
formal content lives in `theories/programs/ex_reject_model.v` (clean
combinators in `theories/programs/reject_condition.v`), with the
standalone sampler regression anchor in
`theories/programs/ex_reject_headline.v` and the score pairing in
`theories/programs/infra/cbv_marginals.v`.

### Def 3.1 — The reject and condition combinators (`ne_reject`, `ne_condition`)

> **Key result:** `reject` and `condition` are the *same program modulo the else-branch* — `reject` retries a rejected draw, `condition` gives up (runs `ne_fail`, which zeroes the mass). Both are built from `fix` / `\` / `@` / `if` / `()` / `let` alone.

Both combinators are closed programs of type
`(b → tbool) → (a → b) → (a → b)`, for arbitrary PPL input and return
objects `a`, `b`. They take a **program predicate** `f : b → tbool` and a
model `m : a → b`, both as program arguments, and use only
`fix` / `\` / `@` / `if` / `()` / `let` — no `ne_test`, no coin, no
`Score`. They differ only in the else-branch: `reject` retries a rejected
draw, `condition` gives up (runs `fail`, which zeroes the mass).

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

The give-up term `ne_fail` is a guarded diverging fixpoint (the CBV
$\lambda$-guard is mandatory: recursion must pass through a value), whose
Kleene chain from $\bot$ is constant, so it denotes the zero
sub-distribution `precone_zero`; `ne_assert b = if b then () else fail`
reweights by the acceptance probability, since a failed `assert` zeroes
the trace whatever value follows.

```coq
(* theories/programs/reject_condition.v *)
Definition ne_fail {G : named_ctx Ar} {t : ppl_type Ar} : nexpr G t :=
  [ (fix "fail" ::: tfun tunit t in \ "_" ::: tunit => # "fail" @ ()) @ () ].

Definition ne_assert {G : named_ctx Ar} : nexpr G (tfun tbool tunit) :=
  [ \ "b" ::: tbool => (if # "b" then () else { ne_fail }) ].
```

In surface form, both of type `(b → tbool) → (a → b) → (a → b)`:
$$\texttt{reject} = \lambda f.\ \texttt{fix}\ rx.\ \lambda m.\ \lambda a.\ \texttt{let}\ x = m\,a\ \texttt{in}\ \texttt{if}\ (f\,x)\ \texttt{then}\ x\ \texttt{else}\ rx\,m\,a$$
$$\texttt{condition} = \lambda f.\ \lambda m.\ \lambda a.\ \texttt{let}\ x = m\,a\ \texttt{in}\ \texttt{let}\ \_ = \texttt{assert}\,(f\,x)\ \texttt{in}\ x$$
The give-up term $\texttt{fail} = (\texttt{fix}\ \texttt{fail}.\ \lambda().\ \texttt{fail}\,())\,()$
denotes the zero sub-distribution `precone_zero`, and
$\texttt{assert}\,b = \texttt{if}\ b\ \texttt{then}\ ()\ \texttt{else}\ \texttt{fail}$
(`ne_fail`, `ne_assert`).

The theorems below quantify over the model value and the input value. The
model argument is the promoted point `g!` of an arbitrary unit-ball
linear map $g : U\llbracket ta\rrbracket \multimap \mathsf{FMeas}$; every
lambda-written model denotes such a point, so no generality is lost (the
`ne_lam` clause promotes the curried body at setlike environments,
`adj_psi_at_setlike`). The input is an arbitrary setlike unit-ball point
$a_0 : U\llbracket ta\rrbracket$ — at `ta = tR` exactly the Diracs, at
`ta = tunit` the unit point. Throughout write $\nu_M := g(a_0)$ for the
model's output sub-distribution and $m_0 := \nu_M(\texttt{setT})$ for its
total mass.

### Thm 3.2 — The conditioning law (`condition_model_E`)

The semantic content of `condition`: the conditioned output is the
model's output reweighted by the acceptance probability $t$, namely
$\llbracket \texttt{condition}\,f\,m\rrbracket(U) = \int_U t\,d\nu_M$ for
every measurable $U$ — unnormalised, with the model evidence
$\int t\,d\nu_M$ at $U = \texttt{setT}$. This generalises the
unnormalised-posterior identity `ex_score_posterior_cbv_E` from the
sampler $m = \lambda\_.\ \texttt{sample}\ \mu$ to an arbitrary model and
program predicate. Writing $\texttt{sdist}\,r := \texttt{fpred}(\delta_r)$
for the acceptance distribution at a returned value $r$, the reweighting
scalar is its true-mass $(\texttt{bc\_t}\,(\texttt{sdist}\,r))\%{:}\texttt{num}$.

| Result | Statement | Rocq |
|---|---|---|
| Thm (`condition_model_E`) | $\llbracket \texttt{condition}\,f\,m\rrbracket(U) = \int_U t\,d\nu_M$ for every measurable $U$, at unit-ball model value `g!` and setlike unit-ball input $a_0$. | `condition_model_E` — `theories/programs/ex_reject_model.v` |
| Cor (`condition_model_mass`) | The conditioned model's total mass is the model evidence $\int t\,d\nu_M$. | `condition_model_mass` — same file |
| Thm (`condition_E`) | Readable form: $\llbracket \texttt{condition\_prog}\rrbracket\,U = \int_U t\,d\llbracket \texttt{model\_run}\rrbracket$ for an arbitrary thunked model program and program predicate. | `condition_E` — same file (Section ReadableHeadlines) |
| Cor (`condition_prog_evidence`) | $\llbracket \texttt{condition\_prog}\rrbracket(\texttt{setT}) = \int t\,d\llbracket \texttt{model\_run}\rrbracket$ — the evidence, readable form. | `condition_prog_evidence` — same file |

```coq
(* theories/programs/ex_reject_model.v — Section RejectModelCompat *)
Theorem condition_model_E (U : set (ar_carrier Ar B))
    (mU : measurable U) :
  fmeas_mu (cond_model_denot R_to_carrier_meas fpred g a0) U =
  \int[fmeas_mu (reject_model_dist g a0)]_(r in U) ((bc_t (sdist r))%:num)%:E.
```

```coq
(* theories/programs/ex_reject_model.v — Section ReadableHeadlines *)
Theorem condition_E U (mU : measurable U) :
  ⟦ condition_prog ⟧ U = \int[⟦ model_run ⟧]_(x in U) ((bc_t (sdist x))%:num)%:E.
```

```coq
(* theories/programs/ex_reject_model.v — Section RejectModelCompat *)
Theorem condition_model_mass :
  fmeas_mu (cond_model_denot R_to_carrier_meas fpred g a0)
    [set: ar_carrier Ar B] =
  \int[fmeas_mu (reject_model_dist g a0)]_
     (r in [set: ar_carrier Ar B]) ((bc_t (sdist r))%:num)%:E.
```

```coq
(* theories/programs/ex_reject_model.v — Section ReadableHeadlines *)
Theorem condition_prog_evidence :
  ⟦ condition_prog ⟧ [set: ar_carrier Ar R_obj] =
  \int[⟦ model_run ⟧]_(x in [set: ar_carrier Ar R_obj]) ((bc_t (sdist x))%:num)%:E.
Proof. exact: (condition_E measurableT). Qed.
```

(`cond_model_denot` is the CBV application of the combinator value to the
predicate `fpred!`, model `g!`, then $a_0$; `reject_model_dist g a0` is
$\nu_M$, and $\texttt{sdist}\,r := \texttt{fpred}(\delta_r)$ the acceptance
distribution at $r$. In the readable form,
$\texttt{model\_prog} := \lambda\_.\ \texttt{Mbody}$ is an arbitrary
thunked model, $\texttt{pred\_prog} := \lambda x.\ \texttt{Fbody}$ an
arbitrary program predicate, `model_run := model_prog ()`, and
`condition_prog := condition pred_prog model_prog ()`.) Proof idea: the
object-generic let-law `eD_let_int_obj`
(`theories/programs/infra/let_sample_law.v`) turns the bound model
application into a Lebesgue integral over $\nu_M$, and at each Dirac
$\delta_r$ the assert-and-return continuation computes to the weighted
point mass $t(r)\cdot\delta_r$ via `bool_case` on `sdist r` (with the
score-discard kit `em_proj1_mor_unitE`). No recursion: the combinator's
reduction chain is the rejection chain minus the fixpoint.

### Thm 3.3 — The rejection master identity (`reject_model_master`)

> **Key result:** division-free and unconditional — $Z \cdot \nu(U) = \int_U t\,d\nu_M$ with $Z := 1 - m_0 + \int t\,d\nu_M$; the sub-probability $1 - m_0$ term carries the model's own divergence mass.

Run the model once: exactly one of three things happens. It returns a
value the predicate **accepts** (probability $\int t\,d\nu_M$),
**rejects**, so we retry (probability $m_0 - \int t\,d\nu_M$), or it
**diverges** (probability $1 - m_0$). Only rejection loops, so each trial
*settles* — accepts or diverges — with probability
$1 - (m_0 - \int t\,d\nu_M) = Z$, the chapter's normaliser. Summing the
geometric series over retries gives the output measure $\nu$ of
`(reject f m) a`, and the master identity states it without division:
$$Z \cdot \nu(U) = \int_U t\,d\nu_M \qquad \text{for every measurable } U.$$
Divide by $Z$ for the normalised distribution when $Z > 0$. Two corners
close the picture: a probability model ($m_0 = 1$) has normaliser the
classical evidence $\int t\,d\nu_M$ and accepts almost surely; if nothing
is ever accepted ($Z = 0$, e.g. $t \equiv 0$) both sides vanish — certain
rejection diverges. Totality of the predicate
($\forall r,\ \texttt{cone\_norm}\,(\texttt{sdist}\,r) = 1$, i.e.
$\texttt{bc\_t}\,s_r + \texttt{bc\_f}\,s_r = 1$) lets the else-weight
$\texttt{bc\_f}\,s_r$ land the sub-probability normaliser; both doc
regimes — a deterministic bool-Dirac and a bernoulli coin — are total.

| Result | Statement | Rocq |
|---|---|---|
| Thm (`reject_model_master`) | $Z \cdot \nu(U) = \int_U t\,d\nu_M$ for every measurable $U$, unconditionally — division-free, sub-probability honest ($Z = 1 - m_0 + \int t\,d\nu_M$). | `reject_model_master` — `theories/programs/ex_reject_model.v` |
| Thm (`reject_model_is_normalised`) | $Z > 0$ (automatic once $0 < \int t\,d\nu_M$) $\Rightarrow \nu(U) = \int_U t\,d\nu_M / Z$ — the normalised distribution. | `reject_model_is_normalised` — same file |
| Cor (`reject_model_mass`) | $\nu(\texttt{setT}) = \int t\,d\nu_M / Z$ — probability that some trial eventually accepts. | `reject_model_mass` — same file |
| Cor (`reject_model_mass_one`) | Probability model ($m_0 = 1$) with $0 < \int t\,d\nu_M$ $\Rightarrow \nu(\texttt{setT}) = 1$: accepts almost surely. | `reject_model_mass_one` — same file |
| Thm (`reject_model_zero`) | $t \equiv 0$ $\Rightarrow \nu = 0$ — certain rejection diverges, whatever the model does. | `reject_model_zero` — same file |
| Thm (`reject_prog_master`) | Readable form, against $\llbracket\cdot\rrbracket$ over an arbitrary thunked model program and program predicate. | `reject_prog_master`, `reject_prog_is_normalised`, `reject_prog_mass_one`, `reject_prog_zero` — same file (Section ReadableHeadlines) |

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

```coq
(* theories/programs/ex_reject_model.v — Section RejectModelCompat *)
Theorem reject_model_zero :
  (forall r : ar_carrier Ar B, (bc_t (sdist r))%:num = 0%R) ->
  reject_model_denot R_to_carrier_meas fpred g a0 = precone_zero.
```

(`reject_model_denot` is the CBV application of the program value to the
predicate `fpred!`, model value `g!`, then input $a_0$;
`reject_model_dist g a0` is the model's output sub-distribution $\nu_M$,
$m_0 := \texttt{fine}\,(\nu_M(\texttt{setT}))$,
$\texttt{sdist}\,r := \texttt{fpred}(\delta_r)$ the acceptance
distribution at $r$,
$t(r) := (\texttt{bc\_t}\,(\texttt{sdist}\,r))\%{:}\texttt{num}$ its
acceptance probability, and the spelled-out integrals are $\int t\,d\nu_M$
over the carrier and $\int_U t\,d\nu_M$ over $U$.)

Proof idea, in six steps (`theories/programs/ex_reject_model.v`):

1. `reject_comb_val_E` / `reject_after_f_val_E` / `reject_model_app_E`
   — the closed program denotes the promoted `λf`-then-`fix "rx"` value,
   read at setlike base environment $1 \otimes \texttt{fpred!}$; the three
   CBV applications (predicate `fpred!`, model `g!`, input $a_0$) strip
   promotions by $\texttt{der} \circ \texttt{prom}$ cancellation before
   any continuity argument.
2. `reject_model_sup_E` — the denotation is the `cone_sup_ball` of the
   per-iterate measures
   $\nu_n := \texttt{der}(\texttt{fix\_chain}\ W_0\ n\ (\texttt{g!}))(a_0)$:
   evaluation at `g!`, the counit `der`, and evaluation at $a_0$ all
   commute with the Kleene supremum (`linhom_fun_sup_ball` twice, plus
   `Lfun_sup_ball`).
3. `reject_model_iter_S` — one Kleene step is the inner let-if body at
   the extended setlike environment
   $(((1 \otimes \texttt{fpred!}) \otimes \texttt{rs\_n!}) \otimes \texttt{g!}) \otimes a_0$.
4. `reject_model_if_at_dirac` — at the Dirac extension the dispatch
   computes to $\texttt{bool\_case}\ s_r\ (\delta_r)\ (\nu_n)$ (via
   `if_icones_at`), where
   $s_r := \llbracket f\,x\rrbracket = \texttt{fpred}(\delta_r)$ is the
   applied predicate value (`rm_scrut_E` through `eD_app_at_setlike`):
   accept-weight $t(r)$ keeps the candidate $\delta_r$, reject-weight
   $\texttt{bc\_f}\,s_r$ takes the else-branch — the recursive call at the
   same model and input, the previous iterate $\nu_n$. The let-bound model
   application computes to $\nu_M$ (`rm_model_app_E`).
5. `reject_model_iter_mass` — the object-generic let-law `eD_let_int_obj`
   turns the iterate into a Lebesgue integral over $\nu_M$, giving the
   affine mass recurrence
   $\nu_{n+1}(U) = \int_U t\,d\nu_M + (m_0 - \int t\,d\nu_M) \cdot \nu_n(U)$
   (the source abbreviates $\int t\,d\nu_M$ as `If` and $\int_U t\,d\nu_M$
   as `IUf U`); the retry mass
   $\int \texttt{bc\_f}\,s\,d\nu_M = m_0 - \int t\,d\nu_M$ keeps the
   model's own divergence mass out of the loop.
6. The affine cascade (`affine_iter_cvg`,
   `theories/programs/infra/affine_cascade.v`) — written
   $x_{n+1} = a + q\cdot x_n$ with $a := \int_U t\,d\nu_M$ and
   $q := m_0 - \int t\,d\nu_M$ — converges to $a / (1 - q)$, and the
   sup-mass bridge `fmeas_kleene_sup_U_E` identifies that limit with
   $\nu(U)$; the degenerate corner $q = 1$ is covered by the
   constantly-zero chain.

```coq
(* theories/programs/ex_reject_model.v *)
Lemma reject_model_iter_mass n U (mU : measurable U) :
  fmeas_mu (reject_model_iter n.+1) U =
  IUf U + ((m0 - fine If)%R)%:E * fmeas_mu (reject_model_iter n) U.
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

**Object-generic core.** The theorems above are stated over an
*arbitrary* return object `B` — a model `m : a → b` for any PPL types
`a`, `b` — with acceptance scalar
$t(x) = (\texttt{bc\_t}\,(\texttt{sdist}\,x))\%{:}\texttt{num}$ read off
the program predicate. The `RejectModelCompat` anchors of this chapter
(`reject_model_master`, `reject_model_is_normalised`,
`reject_model_mass`, `reject_model_mass_one`, `reject_model_zero`,
`condition_model_E`, `condition_model_mass`) are thin wrappers over the
object-generic core in the same file. The measure backbone
(`dirac_fmeas`, `Coalg_dirac`, `FMeas_coalgebra`, the affine cascade, the
object-generic let-law `eD_let_int_obj`) is already object-generic, so
the proof reuses it unchanged. Only the model value `g!`, predicate value
`fpred!`, and input $a_0$ are quantified over.

### Thm 3.4 — The equivalence theorem (`reject_normalises_condition`)

> **Key result:** rejection sampling computes the conditioned model's normalised distribution — $Z \cdot \llbracket \texttt{reject\_prog}\rrbracket\,U = \llbracket \texttt{condition\_prog}\rrbracket\,U$, division-free and unconditional.

The two operators compute the same distribution up to the normaliser:
$$Z \cdot \llbracket \texttt{reject\_prog}\rrbracket\,U = \llbracket \texttt{condition\_prog}\rrbracket\,U, \qquad Z := 1 - \llbracket \texttt{model\_run}\rrbracket(\texttt{setT}) + \int t\,d\llbracket \texttt{model\_run}\rrbracket,$$
division-free and unconditional. Both statements live in the same
$\llbracket\cdot\rrbracket$ framework (Section ReadableHeadlines of
`theories/programs/ex_reject_model.v`), over the same arbitrary model
program, program predicate, and unit input, so they compose literally.

| Result | Statement | Rocq |
|---|---|---|
| Thm (`reject_normalises_condition`) | Rejection computes the conditioned model's normalised distribution: $Z \cdot \llbracket \texttt{reject\_prog}\rrbracket\,U = \llbracket \texttt{condition\_prog}\rrbracket\,U$ with $Z := 1 - \llbracket \texttt{model\_run}\rrbracket(\texttt{setT}) + \int t\,d\llbracket \texttt{model\_run}\rrbracket$, unconditionally. | `reject_normalises_condition` — `theories/programs/ex_reject_model.v` |
| Cor (`reject_prog_computes_condition`) | Division form: if $0 < Z$ then $\llbracket \texttt{reject\_prog}\rrbracket\,U = \llbracket \texttt{condition\_prog}\rrbracket\,U / Z$. | `reject_prog_computes_condition` — same file |
| Cor (`reject_normalises_condition_prob`) | For probability models the normaliser is the conditioned model's total mass (the evidence): $\llbracket \texttt{condition\_prog}\rrbracket(\texttt{setT}) \cdot \llbracket \texttt{reject\_prog}\rrbracket\,U = \llbracket \texttt{condition\_prog}\rrbracket\,U$. | `reject_normalises_condition_prob` — same file |

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
law `condition_E` and apply the rejection master identity
`reject_prog_master` — both sides equal $\int_U t\,d\llbracket \texttt{model\_run}\rrbracket$.
The probability-model form additionally identifies the normaliser with
the evidence
($1 - 1 + \int t\,d\nu_M = \int t\,d\nu_M = \llbracket \texttt{condition\_prog}\rrbracket(\texttt{setT})$).

### Ex 3.5 — Specialising to a sampler (`ex_reject`)

Instantiating the model to $\lambda\_.\ \texttt{sample}\ \mu$
(`ex_sampler`) with a unit-mass prior recovers textbook rejection
sampling against a prior: $\nu_M = \mu$, $m_0 = 1$, and the master
identity specialises to the classical
$\int t\,d\mu \cdot \nu(U) = \int_U t\,d\mu$. Two programs realise this.
The standalone program `ex_reject` — sample from the prior, accept with
probability $f(x)$ (the value coin `Bernoulli (test f #"x")` over a
bundled test function `f : testfn`), recurse on rejection through an
explicit acceptance continuation — was proved first and kept as a
regression anchor; its theorems (`ex_reject_master`,
`ex_reject_is_normalised_posterior`, …) are proved directly in
`theories/programs/ex_reject_headline.v`. The clean combinator's sampler
instance (Section SamplerInstance of
`theories/programs/ex_reject_model.v`) is the program-predicate version:
`reject` applied to the sampler model at an arbitrary total predicate
value, re-derived through the object-generic master. Finally
`ex_reject_normalises_score` is the equivalence at this instance:
rejection normalises exactly the score program's unnormalised posterior.

| Result | Statement | Rocq |
|---|---|---|
| Def (`ex_reject`) | $\texttt{let rec}\ rs\ accept = \texttt{let}\ x = \texttt{sample}\ \mu\ \texttt{in}\ \texttt{if}\ \texttt{Bernoulli}\,(\texttt{test}\ f\ x)\ \texttt{then}\ accept\ x\ \texttt{else}\ rs\ accept\ \texttt{in}\ rs\,(\lambda y. y)$ of type `tR` — the standalone regression sampler at a bundled test function `f : testfn`, accepting through the `test f` coin, abstracted over an acceptance continuation. | `ex_reject`, `ex_reject_cbv`, `ex_sampler` — `theories/programs/examples.v` |
| Thm (`ex_reject_master`) | $\int f\,d\mu \cdot \nu(U) = \int_U f\,d\mu$ for every measurable $U$, unconditionally (graceful at $\int f\,d\mu = 0$) — the standalone sampler; the combinator's sampler instance re-derives the same identity through the object-generic core `reject_model_master_obj`. | `ex_reject_master` — `theories/programs/ex_reject_headline.v`; `reject_model_master_obj` — `theories/programs/ex_reject_model.v` |
| Thm (`ex_reject_is_normalised_posterior`) | If $0 < \int f\,d\mu$ then $\nu(U) = (\int_U f\,d\mu) / (\int f\,d\mu)$ — the normalised posterior of the prior $\mu$ given the test function $f$. | `ex_reject_is_normalised_posterior`, `ex_reject_posterior_simple`, `ex_reject_mass_one`, `ex_reject_zero` — same file |
| Thm (`ex_reject_comb_sampler_master`) | The combinator applied to sampler model `ex_sampler` at the unit input reproduces the classical rejection identity $\int t\,d\mu \cdot \nu(U) = \int_U t\,d\mu$ at $m_0 = 1$, for an arbitrary total program predicate. | `ex_reject_comb_sampler_master` — `theories/programs/ex_reject_model.v` |
| Thm (`ex_reject_normalises_score`) | $(\int f\,d\mu) \cdot \nu_{\texttt{reject}}(U) = \nu_{\texttt{score}}(U)$ at $\mu(\texttt{setT}) = 1$: the equivalence theorem at the sampler instance, connecting `ex_reject` with `ex_score_posterior`. | `ex_reject_normalises_score` — `theories/programs/infra/cbv_marginals.v` |

```coq
(* theories/programs/examples.v *)
Definition ex_reject : @named_expr R Ar (po_robj P) nil tR' :=
  [ let rec "rs" "accept" :=
      (let "x" := sample m in
       if Bernoulli (test f # "x")
       then # "accept" @ # "x"
       else # "rs" @ # "accept")
    in # "rs" @ (\ "y" ::: tR' => # "y") ].
```

```coq
(* theories/programs/ex_reject_headline.v — Section RejectHeadline *)
Theorem ex_reject_master U : measurable U ->
  \int[fmeas_mu mu]_(x in [set: ar_carrier Ar R_obj]) ((f (cR x))%:E)
    * fmeas_mu reject_denot U
  = \int[fmeas_mu mu]_(x in U) ((f (cR x))%:E).
```

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

```coq
(* theories/programs/ex_reject_model.v — Section SamplerInstance *)
Theorem ex_reject_comb_sampler_master U (mU : measurable U) :
  ((\int[fmeas_mu mu]_(r in [set: ar_carrier Ar R_obj]) ((bc_t (sdist r))%:num)%:E) *
   fmeas_mu inst_denot U =
   \int[fmeas_mu mu]_(r in U) ((bc_t (sdist r))%:num)%:E)%E.
```

```coq
(* theories/programs/infra/cbv_marginals.v — Section ScorePosterior *)
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

### Thm 3.6 — Hard conditioning as the deterministic instance (`ne_fail_zero`)

> **Key result:** one statement covers both regimes — a deterministic predicate gives the indicator $1_A$ (hard conditioning), a coin predicate a density $t$ (soft conditioning). No indicator bridge, no `ne_test`, no primed forms.

There is no separate hard-reject machinery: the hard (boolean) regime is
the *deterministic-predicate instance* of the unified master theorem
above. When `f` is a genuine boolean predicate ($\llbracket f\,x\rrbracket$
a Dirac), the acceptance probability $t$ is the indicator $1_A$ of the
accept set $A := \{\, x \mid f\,x = \texttt{true}\,\}$, so every
$\int t\,d\nu_M$ becomes $\nu_M(A)$ and every $\int_U t\,d\nu_M$ becomes
$\nu_M(A \cap U)$. The master identity reads
$Z \cdot \llbracket \texttt{reject}\,f\,m\rrbracket(U) = \nu_M(A \cap U)$
with $Z = 1 - m_0 + \nu_M(A)$, and the conditioning law reads
$\llbracket \texttt{condition}\,f\,m\rrbracket(U) = \nu_M(A \cap U)$; for
a probability model this is the conditional $\nu_M(\cdot \mid A)$. The
soft (coin) regime is the same identities with $t$ a density. No
indicator bridge, no `ne_test`, no primed forms — one statement covers
both (design doc `docs/hard_reject_condition.md`).

The one dedicated fact is `ne_fail_zero`: the give-up term denotes the
zero measure. `ne_fail`'s Kleene chain from $\bot$ is constant, so
$\llbracket \texttt{ne\_fail}\rrbracket = \texttt{precone\_zero}$ at every
setlike unit-ball environment — the same "divergence = zero measure" used
by the fixpoint semantics, and exactly the `else`-branch that `condition`
runs on a rejected value.

```coq
(* theories/programs/ex_reject_model.v — Section FailZero *)
Theorem ne_fail_zero :
  Lfun (eD_cbv' (@ne_fail R Ar (po_robj P) G t)) gam = precone_zero.
```

---

## What is **not** formalised

The open items are CBV-side; the call-by-name interpretation and its
headlines are not gaps of this document — they live on the
`cbn-track` branch. Three former gaps are closed: mutual recursion at
product types (`ne_fix_mr` at products of free types elaborates
through the genuine Seely-transported fixpoint `fix_mr_comb`, with
the surface witness `ex_even_odd_pair` above); the operational content
of that witness (`ex_even_cbv_diverges` / `ex_odd_cbv_diverges` pin
the projection runs `ex_even @ ()` / `ex_odd @ ()` to the unit-cone
zero — certain divergence, mass `0`); and runtime-parameter
distributions (`Gaussian( e1 , e2 )` / `Uniform( e1 , e2 )` over the
probability-kernel layer of `theories/programs/distributions.v`,
with the hierarchy demo `ex_gaussian_walk` above).

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
  rocq top -Q theories Icones -l theories/programs/infra/cbv_marginals.v
echo "Print Assumptions ex_random_linear_cbv_marginal."   | \
  rocq top -Q theories Icones -l theories/programs/infra/cbv_marginals.v
echo "Print Assumptions ex_score_posterior_cbv_E."        | \
  rocq top -Q theories Icones -l theories/programs/infra/cbv_marginals.v
echo "Print Assumptions ex_bayes_linear_cbv_evidence."    | \
  rocq top -Q theories Icones -l theories/programs/infra/cbv_marginals.v

# Runtime-parameter distributions — the Gaussian hierarchy demo
echo "Print Assumptions ex_gaussian_walk_E."    | \
  rocq top -Q theories Icones -l theories/programs/infra/kernel_anchors.v
echo "Print Assumptions ex_gaussian_walk_mass." | \
  rocq top -Q theories Icones -l theories/programs/infra/kernel_anchors.v

# Recursive probabilistic examples — the CBV mass identities
echo "Print Assumptions ex_geom_cbv_mass_one."          | \
  rocq top -Q theories Icones -l theories/programs/ex_reject_headline.v
echo "Print Assumptions ex_almost_loop_cbv_mass_one."   | \
  rocq top -Q theories Icones -l theories/programs/ex_reject_headline.v
echo "Print Assumptions ex_almost_loop_cbv_zero."       | \
  rocq top -Q theories Icones -l theories/programs/ex_reject_headline.v

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
  rocq top -Q theories Icones -l theories/programs/infra/cbv_marginals.v
```

Each command reports only `propositional_extensionality`,
`functional_extensionality_dep` and
`constructive_indefinite_description` (the classical-logic axioms of
`mathcomp-analysis`). Per-entry pages embed the precise identifier
name, file, and a GitHub link to the Rocq source.

For the underlying surface inductive and the CBV interpretation, see
the [PPL tab](../ppl/). For the paper-side
correspondence (§§ 2–9 ↔ Rocq), see the [Paper tab](../paper/).
