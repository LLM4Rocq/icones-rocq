# End-to-end PPL example programs

Each surface program in `theories/programs/examples.v` is reproduced
here with its headline correctness identities, all proved against the
call-by-value interpreter `eD` of `theories/programs/ppl_cbv.v`. The
programs are written exclusively in the direct-style `ppl_named`
custom entry of `theories/programs/ppl.v` (brackets `[ … ]` enter the
entry; curly braces `{ x }` escape back to plain Rocq). Every
constructor of the language is exercised somewhere below. The
centrepiece is the conditioning/rejection pair: `condition M f`
(`ex_condition_comb`) is the Pyro-style soft conditioning operator —
run the model, score the output by the likelihood `f`, return it —
and `reject M f` (`ex_reject_comb`) is the executable sampler — run
the model, accept the output with probability `f`, retry on
rejection. THE THEOREM (`reject_normalises_condition`,
`theories/programs/ex_reject_model.v`): rejection sampling computes
the conditioned model's normalised distribution,
`Z · ⟦reject M f⟧ = ⟦condition M f⟧` with
`Z := 1 − ν_M(setT) + ∫ f dν_M`, for an arbitrary probabilistic
*model* (a function value, itself free to contain samples, scores and
recursion) — with the original hard-coded sampler `ex_reject`
recovered as the combinator's simplest instance
(`ex_reject_comb_sampler_E`). The basic sampling and scoring programs
carry closed-form CBV marginal identities, up to and including the
model evidence of a higher-order Bayesian linear regression
(`ex_bayes_linear_cbv_evidence`,
`theories/programs/infra/cbv_marginals.v`) — itself re-read as
*iterated conditioning* (`ex_bayes_linear_is_iter_condition`,
`theories/programs/examples.v`). A call-by-name interpretation of the
same surface programs is preserved on the `cbn-track` branch; main is
CBV-only.

The surface language itself gained a readable layer in the latest
pass (`theories/programs/ppl.v`): witness-free `Bernoulli e` /
`Score e` forms (densities clamped into `[0,1]` by `clamp`),
measurable function application `Meas { f , Hf } e` (`ne_meas`),
bundled distributions `sample m` for `m : pmeas` with the named
`gaussian` / `uniform` of `theories/programs/examples.v`, the
RUNTIME-PARAMETER forms `Gaussian( e1 , e2 )` / `Uniform( e1 , e2 )`
(`ne_gaussian` / `ne_uniform`, over the probability-kernel layer of
`theories/programs/distributions.v` — hierarchical models, demoed by
`ex_gaussian_walk` below), the comparison coin `e1 > e2`, OCaml-style
`let rec f x := M in K` sugar, and the `Condition { f , … } M` form
below — demoed end to end by `ex_surface_demo` / `ex_surface_walk`
(`theories/programs/examples.v`) and documented in
[the surface-language chapter](../../ppl/chapters/ppl-ch-the-surface-language.html).

The paper-side correspondence (§§ 2–9 ↔ Rocq) lives on the
[Paper tab](../paper/); the categorical-level PPL infrastructure
(the surface inductive, the CBV interpretation, the fixpoint
machinery, the semantic laws) lives on the [PPL tab](../ppl/). This
document covers the **examples themselves**.

---

## Beyond the paper — Basic sampling and scoring examples

End-to-end probabilistic programs that *do not* use recursion: two
random-function programs, a one-parameter score program, and the
higher-order Bayesian linear regression built out of them. The
calculus *shape* they are written in mirrors the canonical
higher-order probabilistic calculus of Heunen–Kammar–Staton–Yang,
*A Convenient Category for Higher-Order Probability Theory* — only
the surface-calculus shape is borrowed; the semantics here is the
integrable-cones model, not quasi-Borel spaces. Each program
exercises a different constructor group of the language (`ne_let` +
`ne_sample`, `ne_add` + `ne_mul`, `ne_score`, `ne_app` on a shared
function value) and ships a closed-form CBV identity tying its
denotation to the corresponding distribution, proved in
`theories/programs/infra/cbv_marginals.v`. The surface constructors
and the named-variable machinery the programs are written in are
documented in
[the surface-language chapter](../../ppl/chapters/ppl-ch-the-surface-language.html).
Every proof follows the same route: the let-at-sample integral law
`eD_let_sample_int` (`theories/programs/infra/let_sample_law.v`)
turns each `let x = sample µ in …` prefix into a Pettis integral over
Diracs of the prior, dereliction / evaluation at setlike test points
pushes inside the integral, and the integrand computes pointwise down
to a Dirac integral.

| Paper-style label | English statement | Rocq |
|---|---|---|
| Constant random function | `let c := sample µ in λx. c` of type `tfun tR tR` denotes a distribution over a function space (constant-output): its marginal at every probability test point is the prior `µ`. | `ex_random_constant` — `theories/programs/examples.v`; `ex_random_constant_cbv_marginal` — `theories/programs/infra/cbv_marginals.v` |
| Random affine function | `let m := sample µ in let b := sample µ in λx. m·x + b` of type `tfun tR tR` denotes a random-coefficients linear regression model: its marginal at a Dirac test point `δ_{r0}` is the iterated-integral pushforward of two prior draws along `(m, b) ↦ m·r0 + b`. | `ex_random_linear` — `theories/programs/examples.v`; `ex_random_linear_cbv_marginal` — `theories/programs/infra/cbv_marginals.v` |
| Scored parameter (one-dimensional unnormalised posterior) | `let m := sample µ in let _ := score f #"m" in #"m"` of type `tR` denotes the unnormalised posterior over the sampled parameter: its measure on every measurable `U` is `∫_U f dµ`. | `ex_score_posterior` — `theories/programs/examples.v`; `ex_score_posterior_cbv_E` — `theories/programs/infra/cbv_marginals.v` |
| Bayesian linear regression (posterior over functions) | Sample the random affine model ONCE, bind it to `"f"`, score one observation per element of an observation list against the model's value at a known input, return `#"f"` — the posterior over functions. The total mass of the denotation is the model evidence `∫∫ ∏_o obs_d o (m·obs_x o + b) dµ dµ`. | `ex_bayes_linear` — `theories/programs/examples.v`; `ex_bayes_linear_cbv_evidence` — `theories/programs/infra/cbv_marginals.v` |
| Two-level Gaussian hierarchy (runtime-parameter distributions) | `let s := Gaussian(0,1) in Gaussian(s,1)` of type `tR`: the parameter of the second draw is the SAMPLED value of the first. Its measure on every measurable `U` is the hierarchy integral `∫ N(r,1)(U) dN(0,1)(r)`, and its total mass is exactly `1`. | `ex_gaussian_walk` — `theories/programs/examples.v`; `ex_gaussian_walk_E`, `ex_gaussian_walk_mass` — `theories/programs/infra/kernel_anchors.v` |

### ex_random_constant (`ex_random_constant`, `ex_random_constant_cbv_marginal`, `ex_random_constant_cbv_marginal_dirac`, `ex_random_constant_cbv_marginal_mass`)

The constant-output random function. After sampling a
single random constant `c ~ µ`, the program returns the function
`λx. c` — every call to the function returns the same value, but the
function itself was sampled from `µ`. The headline correctness
statement is the *marginal at the test point*: derelicting the
(promoted) function value and evaluating it at a test point recovers
the prior `µ`.

```coq
(* theories/programs/examples.v *)
Definition ex_random_constant :
    @named_expr R Ar R_obj nil (tfun tR' tR') :=
  [ let "c" := sample m in \ "x" ::: tR' => # "c" ].
```

All identities live in `theories/programs/infra/cbv_marginals.v`
(Section RandomConstantMarginal), stated against the public
linhom-valued denotation `ex_random_constant_cbv` at the unit context
point `one1`.

| Side | Headline | Status |
|---|---|---|
| CBV — derelicting the denotation and evaluating at any PROBABILITY test point recovers the prior µ, uniformly in the test point. | `ex_random_constant_cbv_marginal` — *fmeas_mu x setT = 1 → ⟦ex_random_constant⟧(one1) derelicted at x = µ* | axiom-free |
| CBV — at a Dirac test point the marginal is the prior (Diracs are probabilities). | `ex_random_constant_cbv_marginal_dirac` — *the marginal at δ_{r0} equals µ* | axiom-free |
| CBV — the marginal's mass at every measurable set is exactly the prior's mass on that set. | `ex_random_constant_cbv_marginal_mass` — *the marginal's measure at every U equals µ(U)* | axiom-free |

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

Proof idea: the let-at-sample law turns the denotation into the
Pettis integral `∫ (ℓ_c)! µ(dc)` of the promoted closures
`ℓ_c := ⟦λx. c⟧(1 ⊗ δ_c)` (the lambda clause promotes at the setlike
one-Dirac environment, `adj_psi_at_setlike`); dereliction and
evaluation at `x` push inside the integral (`icones_hom_pres_int` /
`linhom_int_eval`); the integrand computes to `δ_c` — the unused
argument `x` is discarded silently because it is a probability
(`em_proj1_mor_probE`), and the closure returns the captured
constant; finally `∫ δ_c µ(dc) = µ` (`icone_integral_dirac_fmeas`).

The probability hypothesis on the test point is honest, not an
artifact: discarding an argument in `EM(!)` is the comonoid counit,
which on `FMeas` weighs the kept output by the argument's *total
mass* (`coalg_e_FMeas_prob`) — at `x = 0` the marginal is `0`, not
`µ`. Only mass-1 test points are discarded silently.

### ex_random_linear (`ex_random_linear`, `ex_random_linear_cbv_marginal`, `rl_inner_marginal`)

A random-coefficients linear regression: sample slope `m` and
intercept `b` from `µ`, return the function `λx. m·x + b`. Exercises
`ne_add` and `ne_mul` via the arithmetic lifts of
`theories/programs/ppl.v`; on Dirac inputs the lifts reduce to scalar
arithmetic (`add_lift_dirac` / `mul_lift_dirac`). The marginal
identity ties the surface program to the iterated-integral
pushforward of two independent prior draws along
`(m, b) ↦ m·r0 + b`. This program is also the *model* of the
Bayesian linear regression `ex_bayes_linear` below — the regression
program is literally `let "f" := ex_random_linear in …`.

```coq
(* theories/programs/examples.v *)
Definition ex_random_linear :
    @named_expr R Ar R_obj nil (tfun tR' tR') :=
  [ let "m" := sample m in
    let "b" := sample m in
    \ "x" ::: tR' => # "m" * # "x" + # "b" ].
```

Both identities live in `theories/programs/infra/cbv_marginals.v`
(Section RandomLinearMarginal).

| Side | Headline | Status |
|---|---|---|
| CBV — derelicted and evaluated at a Dirac test point δ_{r0}, the denotation's measure on every measurable U is the iterated integral ∫∫ δ_{m·r0+b}(U) µ(db) µ(dm). | `ex_random_linear_cbv_marginal` — *fmeas_mu (⟦ex_random_linear⟧(one1) derelicted at δ_{r0}) U = ∫∫ δ_{m·r0+b}(U) µ(db) µ(dm)* | axiom-free |
| CBV — the inner continuation (one sample left) marginalises to a single integral over the intercept. | `rl_inner_marginal` — *the marginal of ⟦ex_rl_inner⟧(1 ⊗ δ_m) at δ_{r0} on U is ∫ δ_{m·r0+b}(U) µ(db)* | axiom-free |

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

Proof idea: two applications of the let-at-sample law peel the two
sample binders into nested Pettis integrals; dereliction / evaluation
at `δ_{r0}` push inside both layers; at the three-Dirac environment
`(1 ⊗ δ_m ⊗ δ_b) ⊗ δ_{r0}` (a setlike unit-ball point) the variable
projections return the three Diracs, the body computes through the
Dirac rules of `mul_lift` and `add_lift` to `δ_{m·r0+b}`
(`rl_body_at`), and the per-`U` evaluation of an `FMeas`-valued
Pettis integral (`icone_integral_fmeas_E`) lands the iterated
Lebesgue integral.

### ex_score_posterior (`ex_score_posterior`, `ex_score_posterior_cbv_E`, `ex_score_posterior_cbv_mass`)

Scoring a sampled parameter — the one-dimensional unnormalised
posterior. The textbook prior / score / return shape: sample a
parameter `m` from the prior `µ`, score by a measurable density
`f(m) ∈ [0, 1]`, return `m`. Exercises `ne_score` and delivers the
**unnormalised posterior**: the denotation's measure on every
measurable `U` is `∫_U f dµ` — the prior reweighted by the evidence
density, with total mass the evidence `∫ f dµ`. (This program was
historically misnamed `ex_bayes_linear`; it is not a linear
regression. The genuine higher-order Bayesian linear regression is
the next entry.)

```coq
(* theories/programs/examples.v *)
Definition ex_score_posterior :
    @named_expr R Ar R_obj nil tR' :=
  [ let "m" := sample m in
    let "_" := Score { f, Hf_meas, Hf_ge0, Hf_le1 } # "m" in
    # "m" ].
```

Both identities live in `theories/programs/infra/cbv_marginals.v`
(Section ScorePosterior). They pair with the rejection-sampling
headline of the chapter below: `score` produces the *unnormalised*
posterior, rejection sampling produces the *normalised* one, and
`ex_reject_normalises_score` (same file) connects the two programs
exactly — see the score-pairing entry of the rejection-sampling
chapter below.

| Side | Headline | Status |
|---|---|---|
| CBV — the denotation's measure on every measurable U is the restricted evidence integral: the prior reweighted by the density, NOT normalised. | `ex_score_posterior_cbv_E` — *fmeas_mu ⟦ex_score_posterior⟧(one1) U = ∫_U f∘cR dµ* | axiom-free |
| CBV — the total mass of the denotation is the evidence ∫ f dµ. | `ex_score_posterior_cbv_mass` — *fmeas_mu ⟦ex_score_posterior⟧(one1) setT = ∫ f∘cR dµ* | axiom-free |

```coq
(* theories/programs/infra/cbv_marginals.v — Section ScorePosterior *)
Theorem ex_score_posterior_cbv_E (U : set (ar_carrier Ar R_obj))
    (mU : measurable U) :
  fmeas_mu
    (linhom_fun (ex_score_posterior_cbv R_carrier_meas R_to_carrier_meas
                   pm Hf_meas Hf_ge0 Hf_le1) one1) U =
  \int[fmeas_mu mu]_(r in U) (f (cR r))%:E.
```

Proof idea: the let-at-sample mass law `eD_let_sample_mu_E` turns the
denotation's measure on `U` into an integral over `r ~ µ` of the
continuation's mass at the one-Dirac environment `1 ⊗ δ_r`; there the
score clause evaluates to the scalar `f(r)` (`score_lift_dirac`), and
the returned variable under the score binder is computed by
`em_proj1_mor_unitE` — a `tunit`-typed score result is *not* setlike,
so the first projection discards it as its scalar weight, turning the
score into the `precone_scale` factor `f(r)` on the returned `δ_r`
(`sp_cont_at_dirac`); the Dirac's measure of `U` is the indicator,
and the integral collapses to `∫_U f dµ`.

### ex_bayes_linear (`ex_bayes_linear`, `ex_bayes_linear3`, `ex_bayes_linear_cbv_evidence`, `ex_bayes_linear_cbv_evidence2`)

The paper-faithful Bayesian linear regression (the shape of
Staton–Yang–Heunen–Kammar–Wood, arXiv 1701.02547 §2.1) — told in
three steps.

**The model is a random function.** The model is exactly
`ex_random_linear` above: `let m := sample µ in let b := sample µ in
λx. m·x + b`, a distribution over affine functions with slope and
intercept drawn from the prior.

**Bayesian inference = condition the model on data.** Each
observation is a `Record obs` packaging a known input point `obs_x`
and an observation density `obs_d : R → [0,1]` (with measurability
and bound witnesses — e.g. a normal pdf around the measured output,
scaled into `[0,1]`). Conditioning is a `score`: the model's value
`#"f" @ [|obs_x o|]` at the known input is scored by `obs_d o`. The
program samples the model ONCE, binds it to `"f"`, folds the
observation list into a series of scores, and returns `#"f"` — the
**posterior over functions**.

```coq
(* theories/programs/examples.v — the 2-observation surface form
   (definitionally equal to ex_bayes_linear [:: o1; o2], pinned by a
   Check (erefl : …) in the source) *)
[ let "f" := (let "m" := sample m in
              let "b" := sample m in
              \ "x" ::: tR' => # "m" * # "x" + # "b") in
  let "_" := Score { obs_d o1 , obs_meas o1 , obs_ge0 o1 , obs_le1 o1 }
               # "f" @ [| obs_x o1 |] in
  let "_" := Score { obs_d o2 , obs_meas o2 , obs_ge0 o2 , obs_le1 o2 }
               # "f" @ [| obs_x o2 |] in
  # "f" ]
```

**The regression IS iterated conditioning — by definition.** Each
observation step is a soft conditioning of the model's value at the
observation point: scoring `#"f" @ [|obs_x o|]` by `obs_d o` is the
score clause of the `condition` operator (the centrepiece chapter
below) at the model `#"f"` and the input `obs_x o` — the only
difference is A-normal form (`condition` binds the model's value and
returns it; the regression scores the application directly and
returns the *function* at the end). `condition_at o` packages one
such step and `iter_condition` is its fold over a general meta-level
list `l : seq (obs R)` (the `ppl_named` custom entry cannot recurse
over a meta-level `seq`); `ex_bayes_linear l` is **defined** as the
model bound once followed by `iter_condition`, with the named
agreement anchor `ex_bayes_linear_is_iter_condition`
(`theories/programs/examples.v`) now holding by `erefl`. The
historical raw score-fold shape is the derived reading
`ex_bayes_linear_obs_fold` (via `obs_fold_is_iter_condition`), and
`ex_bayes_linear3` is the concrete 3-observation instance; the
1-observation conditioning step and the 2-observation surface form
are pinned by `Check (erefl : …)` in the source.

**The theorems.** The headline `ex_bayes_linear_cbv_evidence`
(Section BayesLinearEvidence of
`theories/programs/infra/cbv_marginals.v`), for a *general*
observation list `l`: the total mass of the posterior-over-functions
— the comonoid counit of the function-type coalgebra applied to the
denotation — is the **model evidence**, the integral of the
likelihood of all observations under the priors. The 2-observation
corollary `ex_bayes_linear_cbv_evidence2` writes the product
literally.

| Side | Headline | Status |
|---|---|---|
| CBV — the counit ("total mass") of the function-space denotation is the model evidence, for a general observation list. | `ex_bayes_linear_cbv_evidence` — *c1_val (coalg_e ⟦ex_bayes_linear l⟧(one1)) = ∫∫ ∏_{o∈l} obs_d o (m·obs_x o + b) dµ(b) dµ(m)* | axiom-free |
| CBV — the literal 2-observation instance. | `ex_bayes_linear_cbv_evidence2` — *the counit mass at `[:: o1; o2]` is ∫∫ obs_d o1 (m·x₁+b) · obs_d o2 (m·x₂+b) dµ dµ* | axiom-free |

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

**Why call-by-value matters here.** The sampled function is bound
ONCE and shared across every observation *and* the return: each
access to `#"f"` goes through the comonoid duplication `coalg_d` of
the let-clause diagonal at the function-type cone
`!(U⟦tR⟧ ⊸ U⟦tR⟧)` — duplicating a sampled *function value* at a
prom-point of the function cone is exactly what the `!`-comonoid
machinery is for. That duplication is what makes all observations
score the SAME sampled function (and the returned posterior be over
that same function), rather than each score drawing a fresh model.
This is the higher-order sharing story — stronger than the
first-order accept-passing sharing of `ex_reject` below, where the
shared value is a real-valued sample. In the proof, the per-`(m,b)`
weights factor out of the fold one observation at a time
(`obs_fold_at`: `⟦obs_fold v l⟧` at the depth-`n` environment is the
promoted closure scaled by `∏_{o∈l} obs_d o (m·x_o + b)`), and two
applications of the let-at-sample law integrate the weights against
the priors.

Cross-links: the model's own marginal identity is
`ex_random_linear_cbv_marginal` above; the one-parameter score
program (with its rejection pairing `ex_reject_normalises_score`) is
`ex_score_posterior` above.

### ex_gaussian_walk (`ex_gaussian_walk`, `ex_gaussian_walk_E`, `ex_gaussian_walk_mass`)

The two-level Gaussian hierarchy — the previously-inexpressible
hierarchical model, written with the runtime-parameter
`Gaussian(e1,e2)` constructor (`ne_gaussian`,
[the runtime-parameter section of the surface
chapter](../../ppl/sections/ppl-sec-runtime-parameter-distributions.html)):
the parameter of the second draw is the *sampled value* of the
first. The constant-parameter first stage is just the kernel surface
at real literals (`eD_gaussian_sample_agree` pins it to the old
`sample (gaussian 0 1)` form).

```coq
(* theories/programs/examples.v *)
Definition ex_gaussian_walk : @named_expr R Ar R_obj nil tR' :=
  [ let "s" := Gaussian( [| 0%R |] , [| 1%R |] ) in
    Gaussian( # "s" , [| 1%R |] ) ].
```

| Side | Headline | Status |
|---|---|---|
| CBV — the denotation's measure on every measurable U is the hierarchy integral: integrate the second-stage normal against the first-stage prior. | `ex_gaussian_walk_E` — *fmeas_mu ⟦ex_gaussian_walk⟧(one1) U = ∫ N(cR r, 1)(toC⁻¹ U) dN(0,1)(r)* | axiom-free |
| CBV — the program is a probability: total mass exactly 1. | `ex_gaussian_walk_mass` — *fmeas_mu ⟦ex_gaussian_walk⟧(one1) setT = 1* | axiom-free |

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
measure on `U` into an integral of the body's mass at the one-Dirac
environment `1 ⊗ δ_r` against the bound sub-distribution — here the
first stage, which the setlike/Dirac anchor `eD_gaussian_at` computes
to the transported prior `N(0,1)` (`gw_prior`,
`gaussian_ker_fun_cast` at literals). Under the binder, `#"s"`
projects to `δ_r` and the literal `[|1|]` to `δ_{toC 1}`, so the same
anchor computes the body to the gaussian kernel at `(r, 1)`; its
per-`U` reading (`gaussian_ker_cast_E`) is `N(cR r, 1)(toC⁻¹ U)`.
For the mass corollary the integrand is identically `1`
(`normal_prob` is a probability; pointwise norm-1 is
`gaussian_kernel_norm1`), and `∫ 1 dN(0,1) = 1`
(`fmeas_of_prob_setT`).

---

## Beyond the paper — Recursive probabilistic examples (productive partial termination)

Recursive probabilistic programs combining `ne_fix` with the
`ne_if` / `ne_bernoulli` boolean cascade to exhibit *productive
partial termination*. The CBV mass identities are proved in
`theories/programs/ex_reject_headline.v` against the seeded
value-fixpoint interpreter (`fix_comb`,
[the CBV value-fixpoint chapter](../../ppl/chapters/ppl-ch-the-cbv-value-fixpoint-at-function-types.html))
by the same reduction-chain-plus-affine-cascade recipe as the
rejection-sampling headline of the next chapter; the surface
recursion constructor is documented in
[the surface-language chapter](../../ppl/chapters/ppl-ch-the-surface-language.html).

| Paper-style label | English statement | Rocq |
|---|---|---|
| Bare divergence | `let rec l _ = l () in l ()` of type `tunit`, total mass `0`. | `ex_loop` — `theories/programs/examples.v` |
| Geometric distribution | `let rec g _ = if Bernoulli(½) then 0 else 1 + g () in g ()` of type `tR'`, total mass `1`: the sampler halts almost surely. | `ex_geom` — `examples.v`; `ex_geom_cbv_mass_one` — `theories/programs/ex_reject_headline.v` |
| Parameterised partial termination | `let rec l _ = if Bernoulli(p) then () else l () in l ()` of type `tunit`: mass `1` when `p > 0`, mass `0` when `p = 0`. | `ex_almost_loop` — `examples.v`; `ex_almost_loop_cbv_mass_one`, `ex_almost_loop_cbv_zero` — `theories/programs/ex_reject_headline.v` |
| Mutual recursion at a product of functions | `fix_mr p : (1→1) × (1→1). (λn. snd p n, λn. fst p n)` — one recursive name bound at a *pair* of function types, each component calling the other; the elaboration witness for the genuine Seely-transported mutual-recursion fixpoint. | `ex_even_odd_pair`, `ex_even`, `ex_odd` — `theories/programs/examples.v` |

### ex_loop (`ex_loop`)

Bare divergence: `let rec l _ = l () in l ()`. No effect, no
sampling, no scoring — just an infinite chain of unit-typed
recursive calls. Mathematically the program has total mass `0`: the
recursion never terminates.

```coq
(* theories/programs/examples.v *)
Definition ex_loop :
    @named_expr R Ar R_obj nil tunit :=
  [ let rec "l" "_" ::: tunit ==> tunit := # "l" @ ()
    in # "l" @ () ].
```

No standalone CBV headline is recorded for the bare loop: the
certain-divergence statement for this recursion shape is carried by
the parameterised twin at `p = 0` — `ex_almost_loop_cbv_zero` in the
next entry pins the denotation of the Bernoulli-guarded loop with
never-succeeding coin to `precone_zero`, and `ex_loop` is the same
loop with the coin erased.

### ex_geom (`ex_geom`, `ex_geom_cbv_mass_one`)

A geometric counter built via a fair-coin Bernoulli recursion: each
call halts with probability `½` (returning `0`) and otherwise
recurses, adding `1` to the returned real. The program denotes a
measure of total mass `1` — the sampler halts almost surely.

```coq
(* theories/programs/examples.v *)
Definition ex_geom : @named_expr R Ar R_obj nil tR' :=
  [ let rec "g" "_" ::: tunit ==> tR' :=
      (if Bernoulli [| (1 / 2 : R) |]
       then [| 0%R |]
       else [| 1%R |] + # "g" @ ())
    in # "g" @ () ].
```

| Side | Headline | Status |
|---|---|---|
| CBV — the denotation of the geometric counter under the CBV interpreter `eD` has total mass one on the whole carrier: the sampler halts almost surely. | `ex_geom_cbv_mass_one` — *fmeas_mu ⟦ex_geom⟧(one1) setT = 1* | axiom-free |

The proof follows the rejection-sampling reduction chain on the
simpler program: the outer application collapses by `der ∘ prom`
cancellation (`ex_geom_app_E`), the denotation is identified with
the `cone_sup_ball` of the per-iterate measures
`g_iter n := (fix_chain g_W0 n)(one1)` (`ex_geom_sup_E`), one Kleene
step computes to the boolean dispatch
`ν_{n+1} = ½·δ_0 + ½·(add_lift (δ_1 ⊗ ν_n))` (`g_step`), the
translation-mass invariance `add_lift_mass` reduces the mass cascade
to `x_{n+1} = ½ + ½·x_n` (`g_val_S`), and the affine cascade plus
the sup-mass bridge of `theories/programs/infra/affine_cascade.v`
close the limit at `1`.

```coq
(* theories/programs/ex_reject_headline.v — Section GeomRider *)
(** Almost-sure termination of the geometric counter: the CBV
    denotation is a PROBABILITY distribution. *)
Theorem ex_geom_cbv_mass_one :
  fmeas_mu g_denot [set: ar_carrier Ar R_obj] = 1.
```

(`g_denot` abbreviates
`linhom_fun (ex_geom_cbv R_carrier_meas R_to_carrier_meas) one1`,
the CBV denotation of the closed program at the unit context point.)

### ex_almost_loop_p (`ex_almost_loop`, `ex_almost_loop_cbv_mass_one`, `ex_almost_loop_cbv_zero`)

A parameterised Bernoulli cascade: with probability `p` the
recursion halts (returning `()`) and with probability `1 − p` it
recurses. When `p > 0` the function terminates almost surely (total
mass `1`); when `p = 0` it diverges (total mass `0`). The dichotomy
is an honest theorem pair on the CBV side: the denotation at `tunit`
is a *point of the unit cone* (the CBV `tunit` is the terminal
coalgebra on `cone_one_car`), so the termination probability is
visible as the point's norm.

```coq
(* theories/programs/examples.v *)
Definition ex_almost_loop (p : R) :
    @named_expr R Ar R_obj nil tunit :=
  [ let rec "l" "_" ::: tunit ==> tunit :=
      (if Bernoulli [| p |]
       then ()
       else # "l" @ ())
    in # "l" @ () ].
```

| Side | Headline | Status |
|---|---|---|
| CBV — for every strictly positive p, the CBV denotation (a point of the unit cone, whose norm is the termination probability) has norm one. | `ex_almost_loop_cbv_mass_one` — *if 0 < p then cone_norm ⟦ex_almost_loop p⟧(one1) = 1* | axiom-free |
| CBV — when p is zero, the CBV denotation is the zero point of the unit cone: the loop diverges with probability one. | `ex_almost_loop_cbv_zero` — *if p = 0 then ⟦ex_almost_loop p⟧(one1) = precone_zero* | axiom-free |

The proof mirrors the geometric rider: reduce to the
`cone_sup_ball` of the iterate points `al_iter n`
(`ex_almost_loop_sup_E`), compute one Kleene step to the scalar
recurrence `al_val (n+1) = p + (1−p)·al_val n` (`al_step` /
`al_val_S`), and close with `affine_iter_cvg_real` — the limit
`p / (1 − (1−p)) = 1` for `p > 0`, and the constantly-zero chain at
`p = 0`.

```coq
(* theories/programs/ex_reject_headline.v — Section AlmostLoopRider *)
(** Almost-sure termination at positive flip probability: the
    denotation has full mass. *)
Theorem ex_almost_loop_cbv_mass_one : (0 < p)%R ->
  cone_norm al_denot = 1%R.

(** Certain divergence at [p = 0]: the chain is constantly zero. *)
Theorem ex_almost_loop_cbv_zero : p = 0%R -> al_denot = precone_zero.
```

(`al_denot` abbreviates
`linhom_fun (ex_almost_loop_cbv R_carrier_meas R_to_carrier_meas p) one1`;
the `0 ≤ p ≤ 1` witnesses live in the theorems, not the program — the
unified `Bernoulli [| p |]` clamps.)

### ex_even_odd_pair (`ex_even_odd_pair`, `ex_even`, `ex_odd`, `ex_even_odd_pair_cbv`)

The mutual-recursion witness: `ne_fix_mr` binds ONE recursive name
`p` at the free-coalgebra type `tprod (tfun tunit tunit) (tfun tunit
tunit)` — a *pair* of functions — and each component calls the other
via the `fst` / `snd` projections of the rec-bound product. This is
the classic even/odd mutual-recursion *shape* (each component
immediately delegates to the other, so operationally it diverges);
the point of the entry is the elaboration-level witness, not a mass
claim: the CBV denotation `ex_even_odd_pair_cbv` elaborates through
the **genuine** Seely-transported fixpoint path `fix_mr_comb` of
`theories/programs/ppl_cbv.v` (`fix_mr_clause` at `tprod`), closed by
commit-level work in `theories/programs/infra/em_fix_mr.v` — see the
PPL tab's value-fixpoint chapter. No mass identities are claimed for
this entry.

```coq
(* theories/programs/examples.v *)
Definition ex_even_odd_pair :
    @named_expr R Ar R_obj nil pair_ty :=
  [ fix_mr "p" as pair_ty by erefl
       in ({ex_even_odd_lam_a}, {ex_even_odd_lam_b}) ].
```

(`pair_ty` abbreviates `tprod (tfun tunit tunit) (tfun tunit tunit)`;
the two spliced lambdas are `λn. snd #"p" @ #"n"` and
`λn. fst #"p" @ #"n"`, and `ex_even` / `ex_odd` are the two
projections of the pair.) The semantic computation law behind the
elaboration is `eD_fix_mr_prod_at_setlike` with non-degeneracy
witness `eD_fix_mr_prod_at_setlike_neq0`
(`theories/programs/infra/cbv_fix_unfold.v`): at a setlike unit-ball
context point the denotation is the backward Seely transport of the
genuine interleaved-Kleene fixpoint value, and it is never the
cone-zero.

---

## Beyond the paper — Rejection sampling computes the conditioned model's normalised distribution

The headline of the development, told start to finish — as a pair of
**higher-order combinators** over an arbitrary probabilistic model.
`condition M f` is the Pyro-style soft conditioning operator: run the
model, *score* the produced value by the likelihood `f` (values in
`[0, 1]`), return it — the declarative statement "what my model
outputs, reweighted by `f`", as an unnormalised measure. `reject M f`
is the executable sampler for the same target: run the model to
propose a candidate `x`, accept it with probability `f(x)`, and on
rejection throw the candidate away and retry with a fresh run — a
loop that may in principle run forever, so termination is itself a
theorem, not an assumption. THE THEOREM
(`reject_normalises_condition`): rejection sampling computes the
conditioned model's normalised distribution,

```
Z · ⟦ reject M f ⟧ U = ⟦ condition M f ⟧ U,    Z := 1 − ν_M(setT) + ∫ f dν_M
```

— division-free and unconditional, with the division form at `0 < Z`
and, for probability models, the normaliser equal to the conditioned
model's total mass (the model evidence).

Both combinators are closed programs of type `(ta → tR) → (ta → tR)`
taking a probabilistic *model* — any function value `m : ta → tR`,
itself a lambda-written program free to contain samples, scores,
recursion, … — and the theorems quantify over the model and input
values and are **sub-probability honest**: the model may itself
diverge, and its missing mass `1 − m₀` shows up in the normaliser.
The formal content lives in `theories/programs/ex_reject_model.v`
(the combinators' reduction chains, the master identity, the
conditioning law, THE EQUIVALENCE, and the instance bridge),
`theories/programs/ex_reject_headline.v` (the original hard-coded
sampler `ex_reject`, now the simplest instance) and
`theories/programs/infra/cbv_marginals.v` (the score pairing), on
top of the surface programs of `theories/programs/examples.v`.

| Paper-style label | English statement | Rocq |
|---|---|---|
| The condition combinator | `condition = λm. λa. let x = m a in let _ = Score{f} x in x` of type `(ta → tR) → (ta → tR)` — Pyro-style soft conditioning: run the model at the input, weigh the trace by the likelihood of the produced value, return the value. Surface form `Condition { f , … } M`. | `ex_condition_comb`, `ex_condition`, `ex_condition_comb_cbv` — `theories/programs/examples.v` |
| The conditioning law | Writing `ν_M := ⟦m⟧(a)` for the model's output sub-distribution: `⟦condition m a⟧(U) = ∫_U f dν_M` for every measurable `U` — the model's output reweighted by the likelihood (unnormalised); at `U = setT` the model evidence. Generalises `ex_score_posterior_cbv_E` from `sample µ` to any model. | `condition_model_E`, `condition_model_mass`, readable forms `condition_E`, `condition_prog_evidence` — `theories/programs/ex_reject_model.v` |
| THE EQUIVALENCE | `Z · ⟦reject_prog⟧ U = ⟦condition_prog⟧ U` with `Z := 1 − ⟦model_run⟧(setT) + ∫ f d⟦model_run⟧`, unconditionally; division form `⟦reject_prog⟧ U = ⟦condition_prog⟧ U / Z` at `0 < Z`; at a probability model `⟦condition_prog⟧(setT) · ⟦reject_prog⟧ U = ⟦condition_prog⟧ U` — the normaliser IS the evidence. | `reject_normalises_condition`, `reject_prog_computes_condition`, `reject_normalises_condition_prob` — `theories/programs/ex_reject_model.v` |
| The rejection-sampling combinator | `fix rs = λm. λa. let x = m a in if Bernoulli_f{f} x then x else rs m a` of type `(ta → tR) → (ta → tR)`, for an arbitrary input type `ta` — run the model at the input, accept with probability `f x`, recurse on rejection at the same model and input. | `ex_reject_comb`, `ex_reject_comb_cbv` — `theories/programs/examples.v` |
| The combinator master identity | Writing `ν_M := ⟦m⟧(a)` for the model's output sub-distribution, `m₀ := ν_M(setT)`, `If := ∫ f dν_M`: `(1 − m₀ + If) · ν(U) = ∫_U f dν_M` for every measurable `U`, unconditionally. | `reject_model_master` — `theories/programs/ex_reject_model.v` |
| The normalised distribution | If `0 < 1 − m₀ + If` (loop progress), `ν(U) = (∫_U f dν_M) / (1 − m₀ + If)` — the sub-probability-honest normaliser; at a probability model (`m₀ = 1`) it is the classical `∫ f dν_M`. | `reject_model_is_normalised`, `reject_model_mass`, `reject_model_mass_one`, `reject_model_zero` — same file |
| Rejection sampling (the simplest instance) | `let rec rs accept = let x = sample m in if Bernoulli_f{f} x then accept x else rs accept in rs (λy. y)` of type `tR` — sample from the prior, accept with probability `f x`, recurse on rejection. | `ex_reject`, `ex_reject_cbv` — `theories/programs/examples.v` |
| The master identity (instance) | `∫f dµ · ν(U) = ∫_U f dµ` for every measurable `U`, unconditionally (graceful at `∫f dµ = 0`). | `ex_reject_master` — `theories/programs/ex_reject_headline.v`; re-derived from the combinator as `ex_reject_comb_sampler_master` — `theories/programs/ex_reject_model.v` |
| The normalised posterior (instance) | If acceptance has positive mass, `ν(U) = (∫_U f dµ) / (∫ f dµ)` — the program denotes the posterior of the prior `µ` given the soft predicate `f`. | `ex_reject_is_normalised_posterior` — same file |
| The instance bridge | The combinator applied to the sampler model `λ_. sample µ` (`ex_sampler`) at the unit input denotes THE SAME measure as `ex_reject` — equal Kleene-iterate masses pass to the suprema. | `ex_reject_comb_sampler_E` — `theories/programs/ex_reject_model.v` |
| The score pairing | `(∫ f dµ) · ν_reject(U) = ν_score(U)` at `µ(setT) = 1`: rejection sampling normalises exactly the score program's unnormalised posterior. | `ex_reject_normalises_score` — `theories/programs/infra/cbv_marginals.v` |

### The condition combinator (`ex_condition_comb`, `ex_condition`, `ex_condition_comb_cbv`)

`ex_condition_comb` is the Pyro-style soft conditioning operator — a
closed program of type `(ta → tR) → (ta → tR)`, the same type as the
rejection combinator below, for an **arbitrary** PPL input type `ta`:

```coq
(* theories/programs/examples.v *)
Definition ex_condition_comb :
    @named_expr R Ar R_obj nil (tfun (tfun ta tR') (tfun ta tR')) :=
  [ \ "m" ::: (tfun ta tR') =>
      \ "a" ::: ta =>
        (let "x" := # "m" @ # "a" in
         let "_" := Score { f , Hf_meas , Hf_ge0 , Hf_le1 } # "x" in
         # "x") ].
```

Token by token:

- `\ "m" ::: (tfun ta tR') => \ "a" ::: ta => …` — the operator takes
  the **model** `m` (any function value `ta → tR`) and returns the
  conditioned model: a new function of the same type.
- `let "x" := # "m" @ # "a" in …` — run the model at the input.
- `let "_" := Score { f , … } # "x" in # "x"` — weigh the trace by
  the likelihood `f(x)` of the produced value (`ne_score`), then
  return the value. This is exactly the score-and-return tail of
  `ex_score_posterior`, with the model application in place of the
  hard-coded `sample µ`.

`ex_condition M` packages the application: `condition M f` is the
conditioned MODEL, again a closed program of type `ta → tR`. The
surface form `Condition { f , Hm , Hg , Hl } M` (witness braces
first, like `Score`) elaborates to the same term, pinned by a
`Check (erefl : …)` in the source. No recursion is involved: the
combinator's reduction chain is the rejection chain *minus* the
fixpoint (Section ConditionModel of
`theories/programs/ex_reject_model.v`).

### The conditioning law (`condition_model_E`, `condition_model_mass`, `condition_E`, `condition_prog_evidence`)

The semantic content of `condition`: at a unit-ball model value `g!`
and a setlike unit-ball input `a₀` (the same quantification as the
rejection theorems — every lambda-written model denotes such a
point), the conditioned model's output is the model's output
**reweighted by the likelihood**:

```coq
(* theories/programs/ex_reject_model.v — Section ConditionModel *)
Theorem condition_model_E (U : set (ar_carrier Ar R_obj))
    (mU : measurable U) :
  fmeas_mu cond_model_denot U =
  \int[fmeas_mu (reject_model_dist g a0)]_(r in U) (f (cR r))%:E.
```

(`cond_model_denot` is the CBV application of the combinator value to
`g!` then `a₀`; `reject_model_dist g a0` is `ν_M := g(a₀)`, the
model's output sub-distribution — the same object the rejection
theorems normalise against.) This is the generalisation of the
unnormalised-posterior identity `ex_score_posterior_cbv_E`
(`theories/programs/infra/cbv_marginals.v`) from the sampler
`m = λ_. sample µ` to an **arbitrary** model; at `U = setT`
(`condition_model_mass`) it is the **model evidence** `∫ f dν_M`.

In the readable `⟦·⟧` form (Section ReadableHeadlines, where
`model_prog := λ_. Mbody` is an arbitrary thunked model,
`model_run := model_prog ()`, and
`condition_prog := (condition model_prog f) ()`):

```coq
(* theories/programs/ex_reject_model.v — Section ReadableHeadlines *)
Theorem condition_E U (mU : measurable U) :
  ⟦ condition_prog ⟧ U = \int[⟦ model_run ⟧]_(x in U) (f (cR x))%:E.
```

The proof is the score-posterior computation run at `ν_M`: the
general let-law `eD_let_mu_E`
(`theories/programs/infra/let_sample_law.v`) turns the bound model
application into a Lebesgue integral over `ν_M`, and at each Dirac
`δ_r` the score-and-return continuation computes to the weighted
point mass `(f r)·δ_r` (`score_lift_dirac` + the score-discard kit
`em_proj1_mor_unitE` of `theories/programs/infra/cbv_marginals.v`).

### THE EQUIVALENCE (`reject_normalises_condition`, `reject_prog_computes_condition`, `reject_normalises_condition_prob`)

The capstone: the two operators compute the same distribution, up to
the normaliser. Both statements live in the same `⟦·⟧` framework
(Section ReadableHeadlines of `theories/programs/ex_reject_model.v`),
over the same arbitrary model program and the same unit input, so
they compose literally:

| Side | Headline | Status |
|---|---|---|
| CBV — rejection sampling computes the conditioned model's normalised distribution, division-free and unconditional. | `reject_normalises_condition` — *Z · ⟦reject_prog⟧ U = ⟦condition_prog⟧ U, Z := 1 − ⟦model_run⟧(setT) + ∫ f d⟦model_run⟧* | axiom-free |
| CBV — the division form: when the loop makes progress. | `reject_prog_computes_condition` — *0 < Z → ⟦reject_prog⟧ U = (fine (⟦condition_prog⟧ U) / Z)%:E* | axiom-free |
| CBV — for probability models the normaliser IS the conditioned model's total mass (the evidence). | `reject_normalises_condition_prob` — *⟦model_run⟧(setT) = 1 → ⟦condition_prog⟧(setT) · ⟦reject_prog⟧ U = ⟦condition_prog⟧ U* | axiom-free |

```coq
(* theories/programs/ex_reject_model.v — Section ReadableHeadlines *)
Theorem reject_normalises_condition U (mU : measurable U) :
  ((1 - fine (⟦ model_run ⟧ [set: ar_carrier Ar R_obj])
      + fine (\int[⟦ model_run ⟧]_(x in [set: ar_carrier Ar R_obj])
                (f (cR x))%:E))%R)%:E
    * ⟦ reject_prog ⟧ U
  = ⟦ condition_prog ⟧ U.

Theorem reject_normalises_condition_prob U (mU : measurable U) :
  ⟦ model_run ⟧ [set: ar_carrier Ar R_obj] = 1 ->
  ⟦ condition_prog ⟧ [set: ar_carrier Ar R_obj] * ⟦ reject_prog ⟧ U
  = ⟦ condition_prog ⟧ U.
```

The proof of the equivalence is two lines: rewrite the right-hand
side by the conditioning law `condition_E` and apply the rejection
master identity `reject_prog_master` — both sides equal
`∫_U f d⟦model_run⟧`. The probability-model form additionally
identifies the normaliser with the evidence (`1 − 1 + ∫f dν_M
= ∫f dν_M = ⟦condition_prog⟧(setT)`). The score pairing
`ex_reject_normalises_score` below is the historical special case of
this statement at the sampler model.

### The rejection-sampling combinator (`ex_reject_comb`, `reject_model_master`, `reject_model_is_normalised`, `reject_model_mass`, `reject_model_mass_one`, `reject_model_zero`)

`ex_reject_comb` is a higher-order, probabilistic, possibly
non-terminating closed term of type `(ta → tR) → (ta → tR)`, for an
**arbitrary** PPL input type `ta`:

```coq
(* theories/programs/examples.v *)
Definition ex_reject_comb :
    @named_expr R Ar R_obj nil (tfun (tfun ta tR') (tfun ta tR')) :=
  [ fix "rs" ::: tfun (tfun ta tR') (tfun ta tR') in
      \ "m" ::: (tfun ta tR') =>
        \ "a" ::: ta =>
          (let "x" := # "m" @ # "a" in
           if Bernoulli_f { f , Hf_meas , Hf_ge0 , Hf_le1 } # "x"
           then # "x"
           else # "rs" @ # "m" @ # "a") ].
```

Token by token:

- `fix "rs" ::: tfun (tfun ta tR') (tfun ta tR') in …` — the
  recursion binder (`ne_fix`) at the function type
  *model → (input → real)*: the fixpoint VALUE is the combinator
  itself. Semantically this is the seeded value-fixpoint combinator
  `fix_comb`.
- `\ "m" ::: (tfun ta tR') => \ "a" ::: ta => …` — the combinator
  abstracts over the **model** `m` (any function value `ta → tR`)
  and the **input** `a`; both are carried through the recursion as
  ordinary lambda parameters.
- `let "x" := # "m" @ # "a" in …` — propose: RUN THE MODEL at the
  input. This is the generalisation point: where `ex_reject` had the
  hard-coded `sample m`, the combinator binds the output of
  an arbitrary model application.
- `if Bernoulli_f { f, … } # "x" then # "x" else …` — the
  value-dependent coin (`ne_bernoulli_f`): accept the candidate with
  probability `f(x)`, returning it directly.
- `# "rs" @ # "m" @ # "a"` — on rejection, recurse at the *same*
  model and the *same* input: the new call re-runs `m a`, drawing a
  fresh candidate from the model's output distribution.

**The semantic set-up.** The theorems quantify over the model VALUE
and the input VALUE: the model argument is the promoted point `g!` of
an arbitrary unit-ball linear map `g : U⟦ta⟧ ⊸ FMeas` — every
lambda-written model denotes such a point (the `ne_lam` clause
promotes the curried body at setlike environments,
`adj_psi_at_setlike`; `sampler_val_E` is the worked instance), so no
generality is lost — and the input is an arbitrary setlike unit-ball
point `a₀ : U⟦ta⟧` (at `ta = tR` these are exactly the Diracs; at
`ta = tunit` the unit point).

**What the theorems say.** Write `ν_M := g(a₀)` for the model's
output distribution at the input — a SUB-probability: the model may
itself diverge — `m₀ := ν_M(setT)` for its total mass,
`If := ∫ f dν_M`, `IUf U := ∫_U f dν_M`, and `ν` for the denotation
of `(ex_reject_comb m) a`. All in
`theories/programs/ex_reject_model.v` (Section RejectModel),
axiom-free:

| Side | Headline | Status |
|---|---|---|
| CBV — the division-free, sub-probability-honest master identity, unconditionally: a single trial is rejected with probability `m₀ − If` (the model terminated AND the coin said no), so the success-per-trial mass is `1 − (m₀ − If)`. | `reject_model_master` — *measurable U → (1 − m₀ + If) · fmeas_mu ν U = IUf U* | axiom-free |
| CBV — when the loop makes progress (automatic as soon as `0 < If`, and also whenever the model is a strict sub-probability), the combinator denotes the normalised distribution. | `reject_model_is_normalised` — *0 < 1 − m₀ + If → fmeas_mu ν U = (fine (IUf U) / (1 − m₀ + fine If))%:E* | axiom-free |
| CBV — the total-mass identity: the probability that some trial eventually accepts. | `reject_model_mass` — *ν(setT) = If / (1 − m₀ + If)* | axiom-free |
| CBV — almost-sure termination for probability models with positive acceptance. | `reject_model_mass_one` — *m₀ = 1 → 0 < If → ν(setT) = 1* | axiom-free |
| CBV — certain rejection diverges, whatever the model does. | `reject_model_zero` — *(∀r, f r = 0) → ν = precone_zero* | axiom-free |

In plain English: each trial runs the model (which terminates with
probability `m₀`) and flips the coin; the trial *succeeds* with
probability `If = ∫ f dν_M`, is *rejected-and-retried* with
probability `m₀ − If`, and *hangs inside the model* with probability
`1 − m₀`. The combinator's output mass on `U` is therefore the
geometric-series sum `IUf U · Σ_n (m₀ − If)^n`, i.e.
`IUf U / (1 − m₀ + If)` — the master identity states exactly this,
division-free. The degenerate corner `1 − m₀ + If = 0` (a probability
model whose output `f`-mass is zero — the loop never terminates) is
graceful: both sides vanish. At `m₀ = 1` the normaliser is the
classical evidence `∫ f dν_M`, and the textbook posterior statement
drops out.

```coq
(* theories/programs/ex_reject_model.v — Section RejectModel *)
Theorem reject_model_master U (mU : measurable U) :
  ((1 - m0 + fine If)%R)%:E * fmeas_mu reject_model_denot U = IUf U.

Theorem reject_model_is_normalised :
  (0 < 1 - m0 + fine If)%R ->
  forall U, measurable U ->
  fmeas_mu reject_model_denot U =
  ((fine (IUf U) / (1 - m0 + fine If))%R)%:E.

Theorem reject_model_mass_one :
  m0 = 1%R -> 0 < If ->
  fmeas_mu reject_model_denot [set: ar_carrier Ar R_obj] = 1.
```

(`reject_model_denot` is the CBV application of the program value to
the model value `g!` and then the input `a₀`; `m0`, `If`, `IUf U` are
notations for `fine (ν_M(setT))`, `∫ f∘cR dν_M`, `∫_U f∘cR dν_M`
with `ν_M := linhom_fun g a₀`.)

**How the proof goes.** The reduction chain of the original headline,
parameterised (`theories/programs/ex_reject_model.v`):

1. `reject_comb_val_E` / `reject_model_app_E` — the closed fixpoint
   program denotes the promoted fixpoint VALUE, and the two CBV
   applications (to the model `g!`, then the input `a₀`) strip
   promotions by `der ∘ prom` cancellation before any continuity
   argument.
2. `reject_model_sup_E` — the denotation is the `cone_sup_ball` of
   the per-iterate measures
   `ν_n := der(fix_chain W₀ n (g!))(a₀)`: evaluation at `g!`, the
   counit `der`, and evaluation at `a₀` all commute with the Kleene
   supremum (`linhom_fun_sup_ball` twice, plus `Lfun_sup_ball` — the
   ω-continuity field every `Cones` morphism carries by definition).
3. `reject_model_iter_S` — one Kleene step is the inner let-if body
   at the extended setlike environment `((1 ⊗ rs_n!) ⊗ g!) ⊗ a₀`.
4. `reject_model_if_at_dirac` — at the Dirac extension the dispatch
   computes: the scrutinee is the coin `bernoulli (f r)`, THEN
   returns the accepted candidate `δ_r`, and ELSE — the recursive
   call at the SAME model and input — is the previous iterate `ν_n`.
   The let-bound model application itself computes to the model's
   output distribution: `⟦m @ a⟧ = ν_M` (`rm_model_app_E`).
5. `reject_model_iter_mass` — the GENERAL let-law `eD_let_mu_E`
   (`theories/programs/infra/let_sample_law.v`: the let-at-sample
   law with the bound sub-distribution `⟦M⟧γ` in place of the
   constant prior; setlike `γ`) turns the iterate into a Lebesgue
   integral over `ν_M`, giving the affine mass recurrence
   `ν_{n+1}(U) = IUf U + (m₀ − If) · ν_n(U)` — the rejection weight
   is `∫(1−f) dν_M = m₀ − If`: the model's own divergence mass never
   re-enters the loop.
6. The affine cascade (`affine_iter_cvg`,
   `theories/programs/infra/affine_cascade.v`) with `a := IUf U` and
   `q := m₀ − If` computes the limit `IUf U / (1 − q)`, and the
   sup-mass bridge `fmeas_kleene_sup_U_E` identifies it with `ν(U)`;
   the degenerate corner `q = 1` (forcing `m₀ = 1`, `If = 0`) is
   covered by the constantly-zero chain.

```coq
(* theories/programs/ex_reject_model.v *)
Lemma reject_model_iter_mass n U (mU : measurable U) :
  fmeas_mu (reject_model_iter n.+1) U =
  IUf U + ((m0 - fine If)%R)%:E * fmeas_mu (reject_model_iter n) U.
```

**The instance bridge.** At `ta := tunit` and the lambda-written
sampler model `λ_. sample µ` (`ex_sampler`,
`theories/programs/examples.v`) with a unit-mass prior, `ν_M = µ`
(`sampler_out_E`) and `m₀ = 1`: the combinator REPRODUCES the
original headline. `ex_reject_comb_sampler_E` proves the combinator
applied to the sampler model and the unit input denotes **the same
measure** as `ex_reject` — the two programs have different surface
shapes (the old one abstracts over an acceptance continuation, the
combinator over a model), but their Kleene chains satisfy the same
per-iterate mass cascade from `0`, so the suprema coincide by
uniqueness of limits. `ex_reject_comb_sampler_master` then re-derives
the old master identity `∫f dµ · ν(U) = ∫_U f dµ` through the bridge.

```coq
(* theories/programs/ex_reject_model.v — Section SamplerInstance *)
Theorem ex_reject_comb_sampler_E :
  inst_denot =
  linhom_fun (ex_reject_cbv R_carrier_meas R_to_carrier_meas
                m Hf_meas Hf_ge0 Hf_le1) one1.
```

### ex_reject — the simplest instance (`ex_reject`, `ex_reject_master`, `ex_reject_is_normalised_posterior`, `ex_reject_mass_one`, `ex_reject_zero`)

The original hard-coded rejection sampler — now the simplest instance
of the combinator above (the model is `λ_. sample µ`, the input the
unit point; `ex_reject_comb_sampler_E` identifies the denotations).
Its own theorems stand unchanged, proved directly in
`theories/programs/ex_reject_headline.v`. `ex_reject` is a
higher-order, probabilistic, possibly non-terminating closed term of
type `tR`:

```coq
(* theories/programs/examples.v *)
Definition ex_reject : @named_expr R Ar R_obj nil tR' :=
  [ let rec "rs" "accept" :=
      (let "x" := sample m in
       if Bernoulli_f { f , Hf_meas , Hf_ge0 , Hf_le1 } # "x"
       then # "accept" @ # "x"
       else # "rs" @ # "accept")
    in # "rs" @ (\ "y" ::: tR' => # "y") ].
```

Token by token:

- `let rec "rs" "accept" := … in …` — the OCaml-style recursion
  binding (sugar for `ne_let` of `ne_fix` of `ne_lam`): `rs` names
  the sampler itself inside its own body, and the binder types are
  inferred from the body. Semantically the fixpoint is the seeded
  value-fixpoint combinator `fix_comb`. The sampler is
  **higher-order**: it abstracts over the acceptance continuation
  `accept`, a function value passed to the recursive call unchanged.
- `let "x" := sample m in …` — propose: draw a candidate
  `x` from the bundled prior `m : pmeas` (`ne_sample`; the bundle
  carries the unit-ball witness).
- `if Bernoulli_f { f, … } # "x" then … else …` — the
  **value-dependent** coin (`ne_bernoulli_f`): flip with success
  probability `f(x)`, where `x` is the candidate just drawn. The
  four escaped witnesses package `f`'s measurability and `[0, 1]`
  bounds.
- `# "accept" @ # "x"` — on acceptance, pass the candidate to the
  continuation.
- `# "rs" @ # "accept"` — on rejection, recurse with the *same*
  continuation: the new call re-runs the `let`-`sample`, drawing a
  fresh candidate.
- `in # "rs" @ (\ "y" ::: tR' => # "y")` — in the `let rec`
  continuation the recursive sampler is applied to the identity
  continuation, so the whole program returns the accepted sample
  itself.

**What the theorems say.** Write `ν := ⟦ex_reject⟧(one1)` for the
closed CBV denotation, `If := ∫ f dµ` for the acceptance mass, and
`IUf U := ∫_U f dµ`. Under `‖µ‖ ≤ 1`, `µ(setT) = 1` and a measurable
`f : R → [0,1]`, all in `theories/programs/ex_reject_headline.v`
(Section RejectHeadline), axiom-free:

| Side | Headline | Status |
|---|---|---|
| CBV — the division-free master identity: the acceptance mass times the denotation's mass at every measurable U equals the restricted acceptance integral, unconditionally. | `ex_reject_master` — *measurable U → If · fmeas_mu ν U = IUf U* | axiom-free |
| CBV — when acceptance has positive mass, the denotation is exactly the normalised posterior of the prior µ given the soft predicate f. | `ex_reject_is_normalised_posterior` — *0 < If → fmeas_mu ν U = (fine (IUf U) / fine If)%:E* | axiom-free |
| CBV — when the acceptance density already integrates to one, the denotation is the reweighted prior itself, with no normalisation needed. | `ex_reject_posterior_simple` — *If = 1 → fmeas_mu ν U = IUf U* | axiom-free |
| CBV — almost-sure termination: positive acceptance mass makes the sampler's output a probability distribution of total mass one. | `ex_reject_mass_one` — *0 < If → fmeas_mu ν setT = 1* | axiom-free |
| CBV — certain rejection diverges: an identically-zero acceptance density makes the denotation the zero measure. | `ex_reject_zero` — *(∀r, f r = 0) → ν = precone_zero* | axiom-free |

In plain English: the master identity `If · ν(U) = IUf U` holds with
no side condition and no division, so it is graceful even when
acceptance is impossible. When acceptance has positive mass, dividing
through gives the textbook statement — the program denotes the
posterior `ν(U) = (∫_U f dµ)/(∫ f dµ)` — and taking `U` to be the
whole line gives mass `1`: the sampler terminates almost surely. At
the other extreme, `f ≡ 0` is the always-rejecting sampler: the loop
never exits, and its denotation is the zero measure — divergence is
represented honestly, as missing mass, not as an error.

```coq
(* theories/programs/ex_reject_headline.v — Section RejectHeadline *)
(** THE HEADLINE: when acceptance has positive mass, rejection
    sampling denotes the NORMALISED POSTERIOR. *)
Theorem ex_reject_is_normalised_posterior :
  0 < If -> forall U, measurable U ->
  fmeas_mu reject_denot U = ((fine (IUf U) / fine If)%R)%:E.

(** The division-free master form — unconditional, graceful at
    [∫ f dµ = 0]. *)
Theorem ex_reject_master U : measurable U ->
  If * fmeas_mu reject_denot U = IUf U.

(** Almost-sure termination: positive acceptance mass gives a
    PROBABILITY distribution. *)
Theorem ex_reject_mass_one : 0 < If ->
  fmeas_mu reject_denot [set: ar_carrier Ar R_obj] = 1.

(** Certain rejection diverges: the denotation is the zero measure. *)
Theorem ex_reject_zero : (forall r : R, f r = 0%R) ->
  reject_denot = precone_zero.
```

**Why call-by-value matters here.** Each retry re-executes
`let x = sample µ`, so every iteration draws a *fresh* candidate —
while within one iteration the single bound `x` is shared between
the coin (`Bernoulli_f … #"x"`) and the accepted return value
(`accept @ #"x"`): the candidate that passed the test is exactly the
one returned. That sharing is the diagonal of the context comonoid,
the same `let`-sharing semantics pinned by the regression anchors of
[the CBV semantic-laws chapter](../../ppl/chapters/ppl-ch-cbv-semantic-laws-and-regression-anchors.html)
(`let_sample_pair_diag` vs `pair_sample_indep`) — and it is what
makes the per-iterate measures depend only on the previous iterate,
so the Kleene chain below is a genuine independent-retry recurrence.

**How the proof goes.** A six-step reduction chain
(`theories/programs/ex_reject_headline.v`):

1. `ex_reject_app_E` — the outer application of the promoted
   fixpoint to the identity continuation collapses (`der ∘ prom`
   cancels before any continuity argument), leaving `fix_value`
   applied to the body's endo-function.
2. `ex_reject_sup_E` — the denotation is the `cone_sup_ball` of the
   per-iterate measures `ν_n := (fix_chain W₀ n)(a₀)`, because
   evaluation at a point commutes with the Kleene supremum
   (linhom-cone sups are pointwise, `linhom_fun_sup_ball`).
3. `ex_reject_iter_S` — one Kleene step is the inner let-if body
   evaluated at the extended setlike environment.
4. `ex_reject_inner_at_dirac` — at the environment `γ ⊗ δ_r` the
   branch dispatch computes: the scrutinee is the coin
   `bernoulli (f r)` (`bern_lift_dirac`), THEN returns the accepted
   sample `δ_r`, and ELSE — the recursive call at the same
   continuation — is the previous iterate `ν_n`.
5. `ex_reject_iter_mass` — the let-at-sample mass law
   `eD_let_sample_mu_E` turns the iterate into a Lebesgue integral
   over the prior, giving the affine mass recurrence
   `ν_{n+1}(U) = ∫_U f dµ + (1 − ∫ f dµ) · ν_n(U)` (the rejection
   weight `∫(1−f) dµ = 1 − ∫f dµ` uses `µ(setT) = 1`).
6. The affine-cascade closed form `affine_iter_cvg`
   (`theories/programs/infra/affine_cascade.v`) computes the limit
   `IUf U / If` of the per-iterate masses, and the sup-mass bridge
   `fmeas_kleene_sup_U_E` identifies that limit with the mass of the
   supremum — i.e. with `ν(U)`.

The master form then multiplies through (graceful at `If = 0`, where
monotonicity forces `IUf U = 0` too), and the mass-one / zero
corollaries specialise `U := setT` and `f ≡ 0`.

```coq
(* theories/programs/ex_reject_headline.v *)
Lemma ex_reject_iter_mass n U (mU : measurable U) :
  fmeas_mu (reject_iter n.+1) U =
  IUf U + ((1 - fine If)%R)%:E * fmeas_mu (reject_iter n) U.
```

### The score pairing (`ex_reject_normalises_score`)

The rejection sampler pairs with the one-parameter score program of
the basic-examples chapter: `ex_score_posterior` (sample, *score* by
`f`, return) denotes the **unnormalised** posterior — its measure on
`U` is `∫_U f dµ` (`ex_score_posterior_cbv_E`) — while `ex_reject`
(sample, *accept-or-retry* by `f`) denotes the **normalised**
posterior. The theorem connects the two programs exactly: at a
probability prior, the rejection denotation times the total evidence
*is* the score denotation.

| Side | Headline | Status |
|---|---|---|
| CBV — rejection sampling normalises exactly the score posterior: (∫ f dµ) · ν_reject(U) = ν_score(U) at µ(setT) = 1, for every measurable U. | `ex_reject_normalises_score` — *(∫ f∘cR dµ) · fmeas_mu ⟦ex_reject⟧(one1) U = fmeas_mu ⟦ex_score_posterior⟧(one1) U* | axiom-free |

```coq
(* theories/programs/infra/cbv_marginals.v — Section ScorePosterior *)
(** Rejection sampling normalises exactly this measure: combining
    [ex_reject_master] with the posterior identity, the rejection
    denotation times the total evidence is the Bayes denotation. *)
Theorem ex_reject_normalises_score
    (Hmu1 : fmeas_mu mu [set: ar_carrier Ar R_obj] = 1)
    (U : set (ar_carrier Ar R_obj)) (mU : measurable U) :
  (\int[fmeas_mu mu]_(r in [set: ar_carrier Ar R_obj]) (f (cR r))%:E) *
  fmeas_mu
    (linhom_fun (ex_reject_cbv R_carrier_meas R_to_carrier_meas
                   pm Hf_meas Hf_ge0 Hf_le1) one1) U =
  fmeas_mu
    (linhom_fun (ex_score_posterior_cbv R_carrier_meas R_to_carrier_meas
                   pm Hf_meas Hf_ge0 Hf_le1) one1) U.
```

The proof is one line on top of the two headlines: rewrite the
right-hand side by `ex_score_posterior_cbv_E` and apply
`ex_reject_master`. Two inference idioms — soft evidence via `score`,
hard retry via rejection — and the model proves they compute the same
posterior up to the evidence constant.

---

## What is **not** formalised

The open items are CBV-side; the call-by-name interpretation and its
headlines are not gaps of this document — they live on the
`cbn-track` branch. (The former gap "mutual recursion at product
types" is **closed**: `ne_fix_mr` at products of free types now
elaborates through the genuine Seely-transported fixpoint
`fix_mr_comb` of `theories/programs/ppl_cbv.v`, built on
`theories/programs/infra/em_fix_mr.v`, with the surface witness
`ex_even_odd_pair` above.)

(The former item "runtime-parameter distributions" is **delivered**:
`Gaussian( e1 , e2 )` / `Uniform( e1 , e2 )` over the
probability-kernel layer of `theories/programs/distributions.v`, with
the hierarchy demo `ex_gaussian_walk` and its mass-1 identity above.)

| Item | What it is | Why not yet |
|---|---|---|
| CBV distribution refinements for the recursive programs | Pinning the CBV denotations of `ex_geom` / `ex_almost_loop` as *measures* (the geometric PMF `(1/2)^(k+1)` at every `k`; the Dirac at 0), not just their total mass. | The mass identities reduce to a scalar affine cascade; the distribution identities need the per-set version of the same per-iterate induction, which has not been written. |
| Operational content for the mutual-recursion witness | A mass or distribution identity for `ex_even_odd_pair` / `ex_even` / `ex_odd` (the pair diverges by design, so the honest statement is a divergence/mass-zero claim at the projections). | The entry is an elaboration-level witness for the Seely-transported fixpoint path; its reduction chain has not been written. |
| Runtime-parameter kernels for other distribution families | `pkernel` instances beyond `dirac` / `bernoulli` / `gaussian` / `uniform` (e.g. exponential, beta) and surface forms for them. | Each family needs its own parameter-measurability proof (the Fubini–Tonelli route of `measurable_normal_prob_pair`) and a totalisation convention for degenerate parameters; the kernel layer itself is generic and ready. |

These choices are deliberate; each requires substantial
infrastructure outside the current scope and does not block any
*existing* headline result.

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

# The rejection-sampling COMBINATOR — master identity, normalised
# distribution, and the instance bridge
echo "Print Assumptions reject_model_master."           | \
  rocq top -Q theories Icones -l theories/programs/ex_reject_model.v
echo "Print Assumptions reject_model_is_normalised."    | \
  rocq top -Q theories Icones -l theories/programs/ex_reject_model.v
echo "Print Assumptions ex_reject_comb_sampler_E."      | \
  rocq top -Q theories Icones -l theories/programs/ex_reject_model.v

# The condition combinator — the conditioning law and THE EQUIVALENCE
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

# The original rejection-sampling instance + the score pairing
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
