# End-to-end PPL example programs

Each surface program of `theories/programs/examples.v` is reproduced
here together with its correctness identities, all proved against the
call-by-value interpreter `eD` of `theories/programs/ppl_cbv.v`. The
programs are written in the direct-style `ppl_named` custom entry of
`theories/programs/ppl.v` (brackets `[ … ]` enter the entry; curly
braces `{ x }` escape back to plain Rocq), and together they exercise
every constructor of the language.

The centrepiece is the conditioning/rejection pair. `condition M f`
(`ex_condition_comb`) is the Pyro-style soft conditioning operator:
run the model, score the output by the likelihood `f`, return it.
`reject M f` (`ex_reject_comb`) is the executable sampler for the
same target: run the model, accept the output with probability `f`,
retry on rejection. The theorem `reject_normalises_condition`
(`theories/programs/ex_reject_model.v`) states that rejection
sampling computes the conditioned model's normalised distribution:
*Z · ⟦reject M f⟧ U = ⟦condition M f⟧ U* with
*Z := 1 − ν_M(setT) + ∫ f dν_M*, for an arbitrary probabilistic
model — a function value that is itself free to contain samples,
scores and recursion. The original hard-coded sampler `ex_reject` is
recovered as the combinator's simplest instance
(`ex_reject_comb_sampler_E`).

The non-recursive programs carry closed-form CBV marginal identities,
up to the model evidence of a higher-order Bayesian linear regression
(`ex_bayes_linear_cbv_evidence`,
`theories/programs/infra/cbv_marginals.v`), itself re-read as
iterated conditioning (`ex_bayes_linear_is_iter_condition`,
`theories/programs/examples.v`). A call-by-name interpretation of the
same surface programs is preserved on the `cbn-track` branch; main is
CBV-only.

The surface layer the programs are written in — witness-free
`Bernoulli e` / `Score e` (densities clamped into `[0,1]`),
measurable function application `Meas { f , Hf } e`, bundled
distributions `sample m`, the runtime-parameter forms
`Gaussian( e1 , e2 )` / `Uniform( e1 , e2 )`, the comparison coin
`e1 > e2`, OCaml-style `let rec`, and the `Condition { f , Hm } M`
form — is documented in
[the surface-language chapter](../../ppl/chapters/ppl-ch-the-surface-language.html)
and demoed end to end by `ex_surface_demo` / `ex_surface_walk`
(`theories/programs/examples.v`).

The paper-side correspondence (§§ 2–9 ↔ Rocq) lives on the
[Paper tab](../paper/); the PPL infrastructure (the surface
inductive, the CBV interpretation, the fixpoint machinery, the
semantic laws) lives on the [PPL tab](../ppl/). This document covers
the examples themselves.

---

## Basic sampling and scoring examples

Five end-to-end probabilistic programs without recursion: two
random-function programs, a one-parameter score program, the
higher-order Bayesian linear regression built out of them, and a
two-level Gaussian hierarchy. The calculus shape mirrors the
higher-order probabilistic calculus of Heunen–Kammar–Staton–Yang
(*A Convenient Category for Higher-Order Probability Theory*); the
semantics here is the integrable-cones model, not quasi-Borel spaces.

Each program ships a closed-form CBV identity tying its denotation to
the corresponding distribution, proved in
`theories/programs/infra/cbv_marginals.v` (the Gaussian hierarchy in
`theories/programs/infra/kernel_anchors.v`). Every proof follows the
same route: the let-at-sample integral law `eD_let_sample_int`
(`theories/programs/infra/let_sample_law.v`) turns each
`let x = sample µ in …` prefix into a Pettis integral over Diracs of
the prior, dereliction and evaluation at setlike test points push
inside the integral, and the integrand computes pointwise down to a
Dirac integral.

### ex_random_constant (`ex_random_constant`, `ex_random_constant_cbv_marginal`, `ex_random_constant_cbv_marginal_dirac`, `ex_random_constant_cbv_marginal_mass`)

The constant-output random function. After sampling a single random
constant `c ~ µ`, the program returns the function `λx. c`: every
call returns the same value, but the function itself was sampled from
`µ`. The main identity is the marginal at a test point: derelicting
the (promoted) function value and evaluating it at a test point
recovers the prior `µ`.

| Result | Statement | Rocq |
|---|---|---|
| Def (`ex_random_constant`) | `let c := sample µ in λx. c` of type `tfun tR tR` — a distribution over a (constant-output) function space. | `ex_random_constant` — `theories/programs/examples.v` |
| Thm (`ex_random_constant_cbv_marginal`) | Derelicting the denotation and evaluating at any *probability* test point `x` (`fmeas_mu x setT = 1`) recovers the prior `µ`, uniformly in the test point. | `ex_random_constant_cbv_marginal` — `theories/programs/infra/cbv_marginals.v` |
| Cor (`ex_random_constant_cbv_marginal_dirac`) | At a Dirac test point `δ_{r0}` the marginal is the prior — Diracs are probabilities. | `ex_random_constant_cbv_marginal_dirac` — same file |
| Cor (`ex_random_constant_cbv_marginal_mass`) | The marginal's measure of every measurable `U` equals `µ(U)`. | `ex_random_constant_cbv_marginal_mass` — same file |

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
Pettis integral `∫ (ℓ_c)! µ(dc)` of the promoted closures
`ℓ_c := ⟦λx. c⟧(1 ⊗ δ_c)` (the lambda clause promotes at the setlike
one-Dirac environment, `adj_psi_at_setlike`). Dereliction and
evaluation at `x` push inside the integral (`icones_hom_pres_int` /
`linhom_int_eval`); the integrand computes to `δ_c` — the unused
argument `x` is discarded silently because it is a probability
(`em_proj1_mor_probE`) and the closure returns the captured
constant; finally `∫ δ_c µ(dc) = µ` (`icone_integral_dirac_fmeas`).

The probability hypothesis on the test point is honest, not an
artifact. Discarding an argument in `EM(!)` is the comonoid counit,
which on `FMeas` weighs the kept output by the argument's total mass
(`coalg_e_FMeas_prob`); at `x = 0` the marginal is `0`, not `µ`.
Only mass-1 test points are discarded silently.

### ex_random_linear (`ex_random_linear`, `ex_random_linear_cbv_marginal`, `rl_inner_marginal`)

A random-coefficients linear regression: sample slope `m` and
intercept `b` from `µ`, return the function `λx. m·x + b`. The
program exercises `ne_add` and `ne_mul` via the arithmetic lifts of
`theories/programs/ppl.v`; on Dirac inputs the lifts reduce to scalar
arithmetic (`add_lift_dirac` / `mul_lift_dirac`). This program is
also the *model* of the Bayesian linear regression `ex_bayes_linear`
below — the regression program is literally
`let "f" := ex_random_linear in …`.

| Result | Statement | Rocq |
|---|---|---|
| Def (`ex_random_linear`) | `let m := sample µ in let b := sample µ in λx. m·x + b` of type `tfun tR tR` — a random affine function with independent prior draws for slope and intercept. | `ex_random_linear` — `theories/programs/examples.v` |
| Thm (`ex_random_linear_cbv_marginal`) | Derelicted and evaluated at a Dirac test point `δ_{r0}`, the denotation's measure of every measurable `U` is the iterated integral `∫∫ δ_{m·r0+b}(U) µ(db) µ(dm)`. | `ex_random_linear_cbv_marginal` — `theories/programs/infra/cbv_marginals.v` |
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
evaluation at `δ_{r0}` push inside both layers. At the three-Dirac
environment `(1 ⊗ δ_m ⊗ δ_b) ⊗ δ_{r0}` (a setlike unit-ball point)
the variable projections return the three Diracs, the body computes
through the Dirac rules of `mul_lift` and `add_lift` to `δ_{m·r0+b}`
(`rl_body_at`), and the per-`U` evaluation of an `FMeas`-valued
Pettis integral (`icone_integral_fmeas_E`) lands the iterated
Lebesgue integral.

### ex_score_posterior (`ex_score_posterior`, `ex_score_posterior_cbv_E`, `ex_score_posterior_cbv_mass`)

Scoring a sampled parameter — the one-dimensional unnormalised
posterior, in the textbook prior / score / return shape: sample a
parameter `m` from the prior `µ`, score by a measurable density
`f(m) ∈ [0, 1]`, return `m`. The denotation's measure of every
measurable `U` is `∫_U f dµ` — the prior reweighted by the evidence
density, with total mass the evidence `∫ f dµ`.

This program pairs with the conditioning/rejection chapter below:
`score` produces the unnormalised posterior, rejection sampling
produces the normalised one, and `ex_reject_normalises_score`
(stated in the closing section of that chapter) connects the two
programs exactly.

| Result | Statement | Rocq |
|---|---|---|
| Def (`ex_score_posterior`) | `let m := sample µ in let _ := Score (Meas{f} #"m") in #"m"` of type `tR` — sample, score by the density `f`, return the parameter. | `ex_score_posterior` — `theories/programs/examples.v` |
| Thm (`ex_score_posterior_cbv_E`) | The denotation's measure of every measurable `U` is `∫_U f dµ` — the prior reweighted by the density, not normalised. | `ex_score_posterior_cbv_E` — `theories/programs/infra/cbv_marginals.v` |
| Cor (`ex_score_posterior_cbv_mass`) | The total mass of the denotation is the evidence `∫ f dµ`. | `ex_score_posterior_cbv_mass` — same file |

```coq
(* theories/programs/examples.v *)
Definition ex_score_posterior :
    @named_expr R Ar R_obj nil tR' :=
  [ let "m" := sample m in
    let "_" := Score (Meas { f , Hf_meas } # "m") in
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
denotation's measure of `U` into an integral over `r ~ µ` of the
continuation's mass at the one-Dirac environment `1 ⊗ δ_r`. There the
score clause evaluates to the scalar `f(r)` (`eD_score_meas_E` +
`score_lift_dirac`), and the returned variable under the score binder
is computed by `em_proj1_mor_unitE`: a `tunit`-typed score result is
not setlike, so the first projection discards it as its scalar
weight, turning the score into the `precone_scale` factor `f(r)` on
the returned `δ_r` (`sp_cont_at_dirac`). The Dirac's measure of `U`
is the indicator, and the integral collapses to `∫_U f dµ`.

### ex_bayes_linear (`ex_bayes_linear`, `ex_bayes_linear3`, `condition_at`, `iter_condition`, `obs_fold`, `ex_bayes_linear_is_iter_condition`, `ex_bayes_linear_obs_fold`, `ex_bayes_linear_cbv_evidence`, `ex_bayes_linear_cbv_evidence2`)

The Bayesian linear regression of Staton–Yang–Heunen–Kammar–Wood
(arXiv 1701.02547 §2.1), in three steps.

First, the model is a random function: exactly `ex_random_linear`
above, a distribution over affine functions with slope and intercept
drawn from the prior.

Second, inference conditions the model on data. Each observation is a
`Record obs` packaging a known input point `obs_x` and an observation
density `obs_d : R → [0,1]` with measurability and bound witnesses
(for example a normal pdf around the measured output, scaled into
`[0,1]`). Conditioning is a score: the model's value
`#"f" @ [|obs_x o|]` at the known input is scored by `obs_d o`. The
program samples the model once, binds it to `"f"`, folds the
observation list into a series of scores, and returns `#"f"` — the
posterior over functions.

Third, the regression *is* iterated conditioning, by definition.
Scoring `#"f" @ [|obs_x o|]` by `obs_d o` is the score clause of the
`condition` operator of the next chapter, at the model `#"f"` and
the input `obs_x o`; the only difference is A-normal form
(`condition` binds the model's value and returns it, while the
regression scores the application directly and returns the function
at the end). `condition_at o` packages one such step,
`iter_condition` is its fold over a meta-level list
`l : seq (obs R)`, and `ex_bayes_linear l` is defined as the model
bound once followed by `iter_condition` — the agreement anchor
`ex_bayes_linear_is_iter_condition` holds by `erefl`. The historical
raw score-fold shape is the derived reading
`ex_bayes_linear_obs_fold`, and `ex_bayes_linear3` is the concrete
3-observation instance.

| Result | Statement | Rocq |
|---|---|---|
| Def (`ex_bayes_linear`) | Bind the random affine model to `"f"`, condition it on each observation of the list `l` in turn (`condition_at` / `iter_condition`), return `#"f"`. | `ex_bayes_linear`, `condition_at`, `iter_condition`, `obs_fold`, `ex_bayes_linear3` — `theories/programs/examples.v` |
| Prop (`ex_bayes_linear_is_iter_condition`) | The regression equals the model bound once followed by the iterated-conditioning fold — definitionally. | `ex_bayes_linear_is_iter_condition`, derived reading `ex_bayes_linear_obs_fold` — same file |
| Thm (`ex_bayes_linear_cbv_evidence`) | For a general observation list `l`, the counit ("total mass") of the function-space denotation is the model evidence `∫∫ ∏_{o∈l} obs_d o (m·obs_x o + b) dµ(b) dµ(m)`. | `ex_bayes_linear_cbv_evidence` — `theories/programs/infra/cbv_marginals.v` |
| Cor (`ex_bayes_linear_cbv_evidence2`) | The literal 2-observation instance: the counit mass at `[:: o1; o2]` is `∫∫ obs_d o1 (m·x₁+b) · obs_d o2 (m·x₂+b) dµ dµ`. | `ex_bayes_linear_cbv_evidence2` — same file |

```coq
(* theories/programs/examples.v *)
Definition ex_bayes_linear (l : seq (obs R)) :
    @named_expr R Ar R_obj nil (tfun tR' tR') :=
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
  let "_" := Score (Meas { obs_d o1 , obs_meas o1 }
                      (# "f" @ [| obs_x o1 |])) in
  let "_" := Score (Meas { obs_d o2 , obs_meas o2 }
                      (# "f" @ [| obs_x o2 |])) in
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

Call-by-value matters here. The sampled function is bound once and
shared across every observation and the return: each access to
`#"f"` goes through the comonoid duplication `coalg_d` of the
let-clause diagonal at the function-type cone `!(U⟦tR⟧ ⊸ U⟦tR⟧)`.
That duplication is what makes all observations score the *same*
sampled function (and the returned posterior be over that same
function), rather than each score drawing a fresh model. In the
proof, the per-`(m,b)` weights factor out of the fold one
observation at a time (`obs_fold_at`: the fold at the depth-`n`
environment is the promoted closure scaled by
`∏_{o∈l} obs_d o (m·x_o + b)`), and two applications of the
let-at-sample law integrate the weights against the priors.

Cross-links: the model's own marginal identity is
`ex_random_linear_cbv_marginal` above; the one-parameter score
program is `ex_score_posterior` above.

### ex_gaussian_walk (`ex_gaussian_walk`, `ex_gaussian_walk_E`, `ex_gaussian_walk_mass`)

A two-level Gaussian hierarchy, written with the runtime-parameter
`Gaussian(e1,e2)` constructor (`ne_gaussian`,
[the runtime-parameter section of the surface
chapter](../../ppl/sections/ppl-sec-runtime-parameter-distributions.html)):
the parameter of the second draw is the *sampled value* of the
first. The constant-parameter first stage is the kernel surface at
real literals (`eD_gaussian_sample_agree` pins it to the bundled
`sample (gaussian 0 1)` form).

| Result | Statement | Rocq |
|---|---|---|
| Def (`ex_gaussian_walk`) | `let s := Gaussian(0,1) in Gaussian(s,1)` of type `tR` — the sampled value of the first draw parameterises the second. | `ex_gaussian_walk` — `theories/programs/examples.v` |
| Thm (`ex_gaussian_walk_E`) | The denotation's measure of every measurable `U` is the hierarchy integral `∫ N(cR r, 1)(toC⁻¹ U) dN(0,1)(r)`. | `ex_gaussian_walk_E` — `theories/programs/infra/kernel_anchors.v` |
| Cor (`ex_gaussian_walk_mass`) | The program is a probability: total mass exactly `1`. | `ex_gaussian_walk_mass` — same file |

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
measure of `U` into an integral of the body's mass at the one-Dirac
environment `1 ⊗ δ_r` against the bound sub-distribution — here the
first stage, which the setlike/Dirac anchor `eD_gaussian_at` computes
to the transported prior `N(0,1)`. Under the binder, `#"s"` projects
to `δ_r` and the literal `[|1|]` to `δ_{toC 1}`, so the same anchor
computes the body to the gaussian kernel at `(r, 1)`, whose per-`U`
reading (`gaussian_ker_cast_E`) is `N(cR r, 1)(toC⁻¹ U)`. For the
mass corollary the integrand is identically `1` (the kernel is a
pointwise probability, `gaussian_kernel_norm1`) and
`∫ 1 dN(0,1) = 1` (`fmeas_of_prob_setT`).

---

## Recursive probabilistic examples

Recursive probabilistic programs combining `ne_fix` with the boolean
cascade, exhibiting productive partial termination. The CBV mass
identities — and, for the two halting samplers, the full
distribution refinements that pin the denotations as *measures* —
are proved in `theories/programs/ex_reject_headline.v`
against the seeded value-fixpoint interpreter (`fix_comb`,
[the CBV value-fixpoint chapter](../../ppl/chapters/ppl-ch-the-cbv-value-fixpoint-at-function-types.html)),
by the same reduction-chain-plus-affine-cascade recipe as the
rejection sampler of the next chapter.

### ex_loop (`ex_loop`)

Bare divergence: `let rec l _ = l () in l ()`. No sampling, no
scoring — an infinite chain of unit-typed recursive calls, of total
mass `0`.

| Result | Statement | Rocq |
|---|---|---|
| Def (`ex_loop`) | `let rec l _ = l () in l ()` of type `tunit` — the recursion never terminates; total mass `0`. | `ex_loop` — `theories/programs/examples.v` |

```coq
(* theories/programs/examples.v *)
Definition ex_loop :
    @named_expr R Ar R_obj nil tunit :=
  [ let rec "l" "_" ::: tunit ==> tunit := # "l" @ ()
    in # "l" @ () ].
```

No standalone CBV identity is recorded for the bare loop: the
certain-divergence statement for this recursion shape is carried by
the parameterised twin at `p = 0` — `ex_almost_loop_cbv_zero` below
pins the denotation of the Bernoulli-guarded loop with a
never-succeeding coin to `precone_zero`, and `ex_loop` is the same
loop with the coin erased.

### ex_geom (`ex_geom`, `ex_geom_cbv_mass_one`, `ex_geom_cbv_distribution`, `ex_geom_cbv_pmf`)

A geometric counter built from a fair-coin Bernoulli recursion: each
call halts with probability `½` (returning `0`) and otherwise
recurses, adding `1` to the returned real. The program denotes a
measure of total mass `1` — the sampler halts almost surely — and
that measure is the geometric law: on every measurable `U` the
denotation evaluates as the series `Σ_k (1/2)^(k+1) δ_k(U)`
(`ex_geom_cbv_distribution`), and the atom at the embedded natural
`k` carries mass exactly `(1/2)^(k+1)` (`ex_geom_cbv_pmf`). The
embedded point `gpt k := R_to_carrier R_carrier_eq (k%:R)` places the
natural `k` in the real carrier; the points are distinct
(`gpt_inj`) and each singleton is measurable (`measurable_gpt`). The
mass identity `ex_geom_cbv_mass_one` is the `U = setT` specialisation
where the geometric weights sum to `1`.

| Result | Statement | Rocq |
|---|---|---|
| Def (`ex_geom`) | `let rec g _ = if Bernoulli(½) then 0 else 1 + g () in g ()` of type `tR`. | `ex_geom` — `theories/programs/examples.v` |
| Thm (`ex_geom_cbv_mass_one`) | The denotation has total mass one on the whole carrier: the sampler halts almost surely. | `ex_geom_cbv_mass_one` — `theories/programs/ex_reject_headline.v` |
| Thm (`ex_geom_cbv_distribution`) | On every measurable `U` the denotation is the geometric series `Σ_k (1/2)^(k+1) δ_{gpt k}(U)`. | `ex_geom_cbv_distribution` — same file |
| Thm (`ex_geom_cbv_pmf`) | The atom at the embedded natural `gpt k` carries mass exactly `(1/2)^(k+1)`: the geometric PMF. | `ex_geom_cbv_pmf` — same file |

```coq
(* theories/programs/examples.v *)
Definition ex_geom : @named_expr R Ar R_obj nil tR' :=
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
program. The outer application collapses by `der ∘ prom` cancellation
(`ex_geom_app_E`); the denotation is the `cone_sup_ball` of the
per-iterate measures (`ex_geom_sup_E`); one Kleene step computes to
the boolean dispatch `ν_{n+1} = ½·δ_0 + ½·(add_lift (δ_1 ⊗ ν_n))`
(`g_step`); the translation-mass invariance `add_lift_mass` reduces
the mass cascade to `x_{n+1} = ½ + ½·x_n` (`g_val_S`); the affine
cascade and the sup-mass bridge of
`theories/programs/infra/affine_cascade.v` close the limit at `1`.
The distribution refinement runs the same induction per set: the
per-`U` step recurrence `g_iter_U_S` splits the THEN branch into
`(1/2) δ_0` and the ELSE branch into the previous iterate pushed
forward by `+1` (`g_shift_atom`), so the `n`-th iterate is the
truncated geometric law `Σ_{k<n} (1/2)^(k+1) δ_{gpt k}`
(`g_iter_closed`); the partial sums converge to the full ereal
series (`g_iter_series_cvg`) through the same `cone_sup_ball`
limit, giving `ex_geom_cbv_distribution`, and evaluating it at the
singleton `[set gpt k]` isolates the single surviving atom for
`ex_geom_cbv_pmf`.

### ex_almost_loop (`ex_almost_loop`, `ex_almost_loop_cbv_mass_one`, `ex_almost_loop_cbv_dirac`, `ex_almost_loop_cbv_zero`)

A parameterised Bernoulli cascade: with probability `p` the recursion
halts (returning `()`), and with probability `1 − p` it recurses.
When `p > 0` the program terminates almost surely (total mass `1`);
when `p = 0` it diverges (total mass `0`). The dichotomy is an honest
theorem pair: the denotation at `tunit` is a point of the unit cone
(the CBV `tunit` is the terminal coalgebra on `cone_one_car`), so the
termination probability is visible as the point's norm. At `p > 0`
the denotation is moreover pinned as the *element* `one1` — the unit
point, the Dirac on the one-point space — strengthening the norm
identity to the point itself (`ex_almost_loop_cbv_dirac`), since a
norm-one element of the one-dimensional unit cone is `one1`
(`cone_one_norm_eq1`).

| Result | Statement | Rocq |
|---|---|---|
| Def (`ex_almost_loop`) | `let rec l _ = if Bernoulli(p) then () else l () in l ()` of type `tunit`. The unified `Bernoulli [\| p \|]` clamps, so the program needs no `[0,1]` witnesses on `p`. | `ex_almost_loop` — `theories/programs/examples.v` |
| Thm (`ex_almost_loop_cbv_mass_one`) | For every `p > 0` the denotation has norm one: almost-sure termination. | `ex_almost_loop_cbv_mass_one` — `theories/programs/ex_reject_headline.v` |
| Thm (`ex_almost_loop_cbv_dirac`) | For every `p > 0` the denotation IS the unit point `one1` (the Dirac on the one-point space), strengthening the norm identity to the element. | `ex_almost_loop_cbv_dirac` — same file |
| Thm (`ex_almost_loop_cbv_zero`) | At `p = 0` the denotation is the zero point of the unit cone: the loop diverges with probability one. | `ex_almost_loop_cbv_zero` — same file |

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
`linhom_fun (ex_almost_loop_cbv R_carrier_meas R_to_carrier_meas p) one1`;
the `0 ≤ p ≤ 1` witnesses live in the theorems, not the program.)
Proof idea: as for the geometric counter — reduce to the
`cone_sup_ball` of the iterate points (`ex_almost_loop_sup_E`),
compute one Kleene step to the scalar recurrence
`al_val (n+1) = p + (1−p)·al_val n` (`al_step` / `al_val_S`), and
close with `affine_iter_cvg_real`: the limit `p / (1 − (1−p)) = 1`
for `p > 0`, the constantly-zero chain at `p = 0`. The element
identity is then immediate: the unit cone is one-dimensional, so
`cone_one_norm_eq1` upgrades the norm-one fact to `al_denot = one1`.

### ex_even_odd_pair (`ex_even_odd_pair`, `ex_even`, `ex_odd`, `ex_even_cbv_diverges`, `ex_odd_cbv_diverges`, `ex_even_odd_pair_cbv_value`)

The mutual-recursion witness. `ne_fix_mr` binds one recursive name
`p` at the free-coalgebra type
`tprod (tfun tunit tunit) (tfun tunit tunit)` — a pair of
functions — and each component calls the other via the `fst` / `snd`
projections of the rec-bound product. This is the classic even/odd
mutual-recursion shape: `ex_even` is `λn. snd p @ n`, `ex_odd` is
`λn. fst p @ n`, so each component immediately delegates to the
*other* with **no base case**. The closed runs
`ex_even @ ()` and `ex_odd @ ()` therefore never terminate, and the
operational identity is honest divergence — mass `0`.

Both projection runs land in the **unit cone** as its zero element:
`ex_even_cbv_diverges` and `ex_odd_cbv_diverges` state that
`Lfun (eD_cbv' ex_even_run) one1 = precone_zero` (resp. `ex_odd_run`),
where `ex_even_run := ne_app ex_even ne_tt`. That is the certain
divergence — `precone_zero` in the one-dimensional unit cone is mass
`0`.

The honest accuracy point: the **pair** denotation is *not* the
cone-zero. `ex_even_odd_pair_cbv_value` shows the pair value is
`(precone_zero : L)! ⊗p (precone_zero : L)!` — a pair of
*promoted-zero functions* `0! ⊗p 0!`, the backward Seely transport of
the promoted base-cone zero. That element is provably never the
cone-zero (`eD_fix_mr_prod_at_setlike_neq0`,
`theories/programs/infra/cbv_fix_unfold.v`). The mass-`0` content
appears **only** after projecting (`fst` / `snd`) *and* applying to
`()`, landing in the unit cone. The CBV denotation elaborates through
the genuine Seely-transported fixpoint path `fix_mr_comb` of
`theories/programs/ppl_cbv.v` (`fix_mr_clause` at `tprod`), built on
`theories/programs/infra/em_fix_mr.v` — see the PPL tab's
value-fixpoint chapter.

| Result | Statement | Rocq |
|---|---|---|
| Def (`ex_even_odd_pair`) | `fix_mr p : (1→1) × (1→1). (λn. snd p n, λn. fst p n)` — one recursive name bound at a pair of function types, each component calling the other. | `ex_even_odd_pair`, `ex_even_odd_pair_cbv` — `theories/programs/examples.v` |
| Def (`ex_even` / `ex_odd`) | The two projections of the recursive pair. | `ex_even`, `ex_odd` — same file |
| Thm (`ex_even_cbv_diverges`) | The closed run `ex_even @ ()` lands in the unit cone as the zero element — mass `0`, certain divergence. | `ex_even_cbv_diverges` — `theories/programs/ex_reject_headline.v` |
| Thm (`ex_odd_cbv_diverges`) | The closed run `ex_odd @ ()` likewise denotes the unit-cone zero — mass `0`. | `ex_odd_cbv_diverges` — same file |
| Lem (`ex_even_odd_pair_cbv_value`) | The pair denotation is `0! ⊗p 0!`, the pair of promoted-zero functions — *not* the cone-zero. Divergence is the statement about the projections applied to `()`. | `ex_even_odd_pair_cbv_value` — same file |

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
the two spliced lambdas are `λn. snd #"p" @ #"n"` and
`λn. fst #"p" @ #"n"`.)

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
`Lfun h` abbreviates the underlying cones-hom function and `_!` is
`prom`, `_ ⊗p _` the `ptensor` of the promoted unit-cone homset `L`.)

**Proof idea.** The recursion is seeded at the cone-zero, and the
zero-seeded interleaved-Kleene chain stays there: `even_odd_iter_zero`
shows every iterate `fix_chain eo_W0 n = precone_zero` by induction
(each step is `der 0! = 0`). Hence the value-fixpoint at the base cone
is the sup of zero iterates, `ex_even_odd_fix_value_zero`. Feeding
this through the semantic computation law `eD_fix_mr_prod_at_setlike`
gives the pair value `0! ⊗p 0!`. Each projection-then-apply then uses
the homogeneity helper `linhom_cone_one_zero` (with
`cone_one_scale_rep`): a linhom out of the one-dimensional unit cone
that vanishes at `one1` is the zero linhom, so the derelicted
promoted-zero function evaluated at the unit point is `precone_zero`.

---

## Conditioning and rejection sampling

Conditioning is the declarative side of Bayesian inference:
`condition M f` runs the model `M`, scores the produced value by the
likelihood `f` (values in `[0, 1]`), and returns it — "what my model
outputs, reweighted by `f`", as an unnormalised measure. Rejection
sampling is the executable side: `reject M f` runs the model to
propose a candidate `x`, accepts it with probability `f(x)`, and on
rejection throws the candidate away and retries with a fresh run — a
loop that may in principle run forever, so termination is itself a
theorem, not an assumption.

The chapter proves that the two sides agree. The theorem
`reject_normalises_condition` states, division-free and
unconditionally, that *Z · ⟦reject M f⟧ U = ⟦condition M f⟧ U* with
*Z := 1 − ν_M(setT) + ∫ f dν_M*, where `ν_M` is the model's output
sub-distribution. Both combinators take an arbitrary probabilistic
model — any function value `m : ta → tR`, itself free to contain
samples, scores and recursion — and the statements are
sub-probability honest: the model may itself diverge, and its
missing mass `1 − m₀` shows up in the normaliser. The formal content
lives in `theories/programs/ex_reject_model.v`, with the standalone
sampler instance in `theories/programs/ex_reject_headline.v` and the
score pairing in `theories/programs/infra/cbv_marginals.v`.

### The condition and reject combinators (`ex_condition_comb`, `ex_condition`, `ex_condition_comb_cbv`, `ex_condition_cbv`, `ex_reject_comb`, `ex_reject_comb_cbv`)

Both combinators are closed programs of type
`(ta → tR) → (ta → tR)`, for an arbitrary PPL input type `ta`. The
conditioning operator is a plain double lambda: it takes the model
`m`, takes the input `a`, runs the model at the input, scores the
produced value by the likelihood, and returns the value — the
score-and-return tail of `ex_score_posterior` with a model
application in place of the hard-coded `sample µ`.

```coq
(* theories/programs/examples.v *)
Definition ex_condition_comb :
    @named_expr R Ar R_obj nil (tfun (tfun ta tR') (tfun ta tR')) :=
  [ \ "m" ::: (tfun ta tR') =>
      \ "a" ::: ta =>
        (let "x" := # "m" @ # "a" in
         let "_" := Score (Meas { f , Hf_meas } # "x") in
         # "x") ].
```

The rejection sampler wraps the same propose step in a recursion: it
runs the model, accepts the candidate `x` with probability `f(x)`
(the value-dependent coin `Bernoulli (Meas{f} #"x")`), and on
rejection recurses at the *same* model and the *same* input — the
recursive call re-runs `m a`, drawing a fresh candidate. The
recursion binder `fix "rs"` sits at the function type
*model → (input → real)*, so the fixpoint value is the combinator
itself; semantically it is the seeded value-fixpoint combinator
`fix_comb`.

```coq
(* theories/programs/examples.v *)
Definition ex_reject_comb :
    @named_expr R Ar R_obj nil (tfun (tfun ta tR') (tfun ta tR')) :=
  [ fix "rs" ::: tfun (tfun ta tR') (tfun ta tR') in
      \ "m" ::: (tfun ta tR') =>
        \ "a" ::: ta =>
          (let "x" := # "m" @ # "a" in
           if Bernoulli (Meas { f , Hf_meas } # "x")
           then # "x"
           else # "rs" @ # "m" @ # "a") ].
```

`ex_condition M` packages the application: `condition M f` is the
conditioned model, again a closed program of type `ta → tR`, with
the surface form `Condition { f , Hm } M` pinned to the same term by
a `Check (erefl : …)` in the source.

```coq
(* theories/programs/examples.v — Section ConditionCombinator *)
Definition ex_condition (M : @named_expr R Ar R_obj nil (tfun ta tR')) :
    @named_expr R Ar R_obj nil (tfun ta tR') :=
  [ {ex_condition_comb} @ {M} ].
```

| Result | Statement | Rocq |
|---|---|---|
| Def (`ex_condition_comb`) | `condition = λm. λa. let x = m a in let _ = Score (Meas{f} x) in x` of type `(ta → tR) → (ta → tR)` — run the model at the input, weigh the trace by the likelihood of the produced value, return the value. | `ex_condition_comb`, `ex_condition_comb_cbv` — `theories/programs/examples.v` |
| Def (`ex_condition`) | The applied form `condition M f` and its surface notation `Condition { f , Hm } M`. | `ex_condition`, `ex_condition_cbv` — same file |
| Def (`ex_reject_comb`) | `fix rs = λm. λa. let x = m a in if Bernoulli (Meas{f} x) then x else rs m a` of the same type — run the model at the input, accept with probability `f x`, recurse on rejection at the same model and input. | `ex_reject_comb`, `ex_reject_comb_cbv` — `theories/programs/examples.v` |

The theorems below quantify over the model value and the input
value: the model argument is the promoted point `g!` of an arbitrary
unit-ball linear map `g : U⟦ta⟧ ⊸ FMeas` — every lambda-written
model denotes such a point (the `ne_lam` clause promotes the curried
body at setlike environments, `adj_psi_at_setlike`), so no
generality is lost — and the input is an arbitrary setlike unit-ball
point `a₀ : U⟦ta⟧` (at `ta = tR` these are exactly the Diracs; at
`ta = tunit` the unit point). Throughout, write `ν_M := g(a₀)` for
the model's output sub-distribution, `m₀ := ν_M(setT)` for its total
mass, `If := ∫ f dν_M` and `IUf U := ∫_U f dν_M`.

### The conditioning law (`condition_model_E`, `condition_model_mass`, `condition_E`, `condition_prog_evidence`)

The semantic content of `condition`: the conditioned model's output
is the model's output reweighted by the likelihood,
`⟦condition m a⟧(U) = ∫_U f dν_M` for every measurable `U` —
unnormalised, with the model evidence `∫ f dν_M` at `U = setT`. This
generalises the unnormalised-posterior identity
`ex_score_posterior_cbv_E` from the sampler `m = λ_. sample µ` to an
arbitrary model.

| Result | Statement | Rocq |
|---|---|---|
| Thm (`condition_model_E`) | `⟦condition m a⟧(U) = ∫_U f dν_M` for every measurable `U`, at a unit-ball model value `g!` and a setlike unit-ball input `a₀`. | `condition_model_E` — `theories/programs/ex_reject_model.v` |
| Cor (`condition_model_mass`) | The conditioned model's total mass is the model evidence `∫ f dν_M`. | `condition_model_mass` — same file |
| Thm (`condition_E`) | The readable form: `⟦condition_prog⟧ U = ∫_U f d⟦model_run⟧` for an arbitrary thunked model program. | `condition_E` — same file (Section ReadableHeadlines) |
| Cor (`condition_prog_evidence`) | `⟦condition_prog⟧(setT) = ∫ f d⟦model_run⟧` — the evidence, in the readable form. | `condition_prog_evidence` — same file |

```coq
(* theories/programs/ex_reject_model.v — Section ConditionModel *)
Theorem condition_model_E (U : set (ar_carrier Ar R_obj))
    (mU : measurable U) :
  fmeas_mu cond_model_denot U =
  \int[fmeas_mu (reject_model_dist g a0)]_(r in U) (f (cR r))%:E.
```

```coq
(* theories/programs/ex_reject_model.v — Section ReadableHeadlines *)
Theorem condition_E U (mU : measurable U) :
  ⟦ condition_prog ⟧ U = \int[⟦ model_run ⟧]_(x in U) (f (cR x))%:E.
```

```coq
(* theories/programs/ex_reject_model.v — Section ConditionModel *)
Theorem condition_model_mass :
  fmeas_mu cond_model_denot [set: ar_carrier Ar R_obj] =
  \int[fmeas_mu (reject_model_dist g a0)]_
     (r in [set: ar_carrier Ar R_obj]) (f (cR r))%:E.
Proof. exact: (condition_model_E measurableT). Qed.
```

```coq
(* theories/programs/ex_reject_model.v — Section ReadableHeadlines *)
Theorem condition_prog_evidence :
  ⟦ condition_prog ⟧ [set: ar_carrier Ar R_obj] =
  \int[⟦ model_run ⟧]_(x in [set: ar_carrier Ar R_obj]) (f (cR x))%:E.
Proof. exact: (condition_E measurableT). Qed.
```

(`cond_model_denot` is the CBV application of the combinator value
to `g!` and then `a₀`; `reject_model_dist g a0` is `ν_M`. In the
readable form, `model_prog := λ_. Mbody` is an arbitrary thunked
model, `model_run := model_prog ()`, and
`condition_prog := (condition model_prog f) ()`.) Proof idea: the
score-posterior computation run at `ν_M`. The general let-law
`eD_let_mu_E` (`theories/programs/infra/let_sample_law.v`) turns the
bound model application into a Lebesgue integral over `ν_M`, and at
each Dirac `δ_r` the score-and-return continuation computes to the
weighted point mass `(f r)·δ_r` (`eD_score_meas_E` +
`score_lift_dirac`, with the score-discard kit
`em_proj1_mor_unitE`). No recursion is involved: the combinator's
reduction chain is the rejection chain minus the fixpoint.

### The rejection master identity (`reject_model_master`, `reject_model_is_normalised`, `reject_model_mass`, `reject_model_mass_one`, `reject_model_zero`, `reject_prog_master`, `reject_prog_is_normalised`, `reject_prog_mass_one`, `reject_prog_zero`)

The semantic content of `reject`, in division-free form: writing `ν`
for the denotation of `(reject_comb m) a`,
*(1 − m₀ + If) · ν(U) = IUf U* for every measurable `U`,
unconditionally. A single trial is rejected with probability
`m₀ − If` (the model terminated and the coin said no), so the
success-per-trial mass is `1 − (m₀ − If) = 1 − m₀ + If`; the output
mass on `U` is the geometric-series sum `IUf U · Σ_n (m₀ − If)^n`,
which the master identity states without division. The degenerate
corner `1 − m₀ + If = 0` (a probability model whose output `f`-mass
is zero, so the loop never terminates) is graceful: both sides
vanish. When the loop makes progress the division form gives the
normalised distribution, and at `m₀ = 1` the normaliser is the
classical evidence `∫ f dν_M`.

| Result | Statement | Rocq |
|---|---|---|
| Thm (`reject_model_master`) | `(1 − m₀ + If) · ν(U) = IUf U` for every measurable `U`, unconditionally — division-free and sub-probability honest. | `reject_model_master` — `theories/programs/ex_reject_model.v` |
| Thm (`reject_model_is_normalised`) | If `0 < 1 − m₀ + If` (loop progress, automatic as soon as `0 < If`), then `ν(U) = IUf U / (1 − m₀ + If)` — the normalised distribution. | `reject_model_is_normalised` — same file |
| Cor (`reject_model_mass`) | `ν(setT) = If / (1 − m₀ + If)` — the probability that some trial eventually accepts. | `reject_model_mass` — same file |
| Cor (`reject_model_mass_one`) | For a probability model (`m₀ = 1`) with positive acceptance (`0 < If`), `ν(setT) = 1`: the sampler terminates almost surely. | `reject_model_mass_one` — same file |
| Thm (`reject_model_zero`) | If `f ≡ 0` then `ν = 0` — certain rejection diverges, whatever the model does. | `reject_model_zero` — same file |
| Thm (`reject_prog_master`) | The readable form of the master identity, against `⟦·⟧` over an arbitrary thunked model program. | `reject_prog_master`, `reject_prog_is_normalised`, `reject_prog_mass_one`, `reject_prog_zero` — same file (Section ReadableHeadlines) |

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

```coq
(* theories/programs/ex_reject_model.v — Section RejectModel *)
Theorem reject_model_mass :
  (0 < 1 - m0 + fine If)%R ->
  fmeas_mu reject_model_denot [set: ar_carrier Ar R_obj] =
  ((fine If / (1 - m0 + fine If))%R)%:E.
Proof. move=> Hpos; exact: (reject_model_is_normalised Hpos measurableT). Qed.

Theorem reject_model_zero :
  (forall r : R, f r = 0%R) -> reject_model_denot = precone_zero.
```

(`reject_model_denot` is the CBV application of the program value to
the model value `g!` and then the input `a₀`; `m0`, `If`, `IUf U`
are notations for `fine (ν_M(setT))`, `∫ f∘cR dν_M`, `∫_U f∘cR dν_M`.)

Proof idea, in six steps (`theories/programs/ex_reject_model.v`):

1. `reject_comb_val_E` / `reject_model_app_E` — the closed fixpoint
   program denotes the promoted fixpoint value, and the two CBV
   applications (to the model `g!`, then the input `a₀`) strip
   promotions by `der ∘ prom` cancellation before any continuity
   argument.
2. `reject_model_sup_E` — the denotation is the `cone_sup_ball` of
   the per-iterate measures
   `ν_n := der(fix_chain W₀ n (g!))(a₀)`: evaluation at `g!`, the
   counit `der`, and evaluation at `a₀` all commute with the Kleene
   supremum (`linhom_fun_sup_ball` twice, plus `Lfun_sup_ball`).
3. `reject_model_iter_S` — one Kleene step is the inner let-if body
   at the extended setlike environment `((1 ⊗ rs_n!) ⊗ g!) ⊗ a₀`.
4. `reject_model_if_at_dirac` — at the Dirac extension the dispatch
   computes: the scrutinee is the coin `bernoulli (f r)`
   (`eD_bernoulli_meas_E` + `bern_lift_dirac`), the then-branch
   returns the accepted candidate `δ_r`, and the else-branch — the
   recursive call at the same model and input — is the previous
   iterate `ν_n`. The let-bound model application itself computes to
   `ν_M` (`rm_model_app_E`).
5. `reject_model_iter_mass` — the general let-law `eD_let_mu_E`
   turns the iterate into a Lebesgue integral over `ν_M`, giving the
   affine mass recurrence
   `ν_{n+1}(U) = IUf U + (m₀ − If) · ν_n(U)`; the rejection weight is
   `∫(1−f) dν_M = m₀ − If`, so the model's own divergence mass never
   re-enters the loop.
6. The affine cascade (`affine_iter_cvg`,
   `theories/programs/infra/affine_cascade.v`) with `a := IUf U` and
   `q := m₀ − If` computes the limit `IUf U / (1 − q)`, and the
   sup-mass bridge `fmeas_kleene_sup_U_E` identifies it with `ν(U)`;
   the degenerate corner `q = 1` is covered by the constantly-zero
   chain.

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
                (f (cR x))%:E))%R)%:E
    * ⟦ reject_prog ⟧ U
  = \int[⟦ model_run ⟧]_(x in U) (f (cR x))%:E.
```

### The equivalence theorem (`reject_normalises_condition`, `reject_prog_computes_condition`, `reject_normalises_condition_prob`)

The two operators compute the same distribution, up to the
normaliser: *Z · ⟦reject_prog⟧ U = ⟦condition_prog⟧ U* with
*Z := 1 − ⟦model_run⟧(setT) + ∫ f d⟦model_run⟧*, division-free and
unconditional. Both statements live in the same `⟦·⟧` framework
(Section ReadableHeadlines of `theories/programs/ex_reject_model.v`),
over the same arbitrary model program and the same unit input, so
they compose literally.

| Result | Statement | Rocq |
|---|---|---|
| Thm (`reject_normalises_condition`) | Rejection sampling computes the conditioned model's normalised distribution: `Z · ⟦reject_prog⟧ U = ⟦condition_prog⟧ U` with `Z := 1 − ⟦model_run⟧(setT) + ∫ f d⟦model_run⟧`, unconditionally. | `reject_normalises_condition` — `theories/programs/ex_reject_model.v` |
| Cor (`reject_prog_computes_condition`) | The division form: if `0 < Z` then `⟦reject_prog⟧ U = ⟦condition_prog⟧ U / Z`. | `reject_prog_computes_condition` — same file |
| Cor (`reject_normalises_condition_prob`) | For probability models the normaliser is the conditioned model's total mass (the evidence): `⟦condition_prog⟧(setT) · ⟦reject_prog⟧ U = ⟦condition_prog⟧ U`. | `reject_normalises_condition_prob` — same file |

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

```coq
(* theories/programs/ex_reject_model.v — Section ReadableHeadlines *)
Theorem reject_prog_computes_condition :
  (0 < 1 - fine (⟦ model_run ⟧ [set: ar_carrier Ar R_obj])
     + fine (\int[⟦ model_run ⟧]_(x in [set: ar_carrier Ar R_obj])
               (f (cR x))%:E))%R ->
  forall U, measurable U ->
  ⟦ reject_prog ⟧ U =
  ((fine (⟦ condition_prog ⟧ U)
    / (1 - fine (⟦ model_run ⟧ [set: ar_carrier Ar R_obj])
         + fine (\int[⟦ model_run ⟧]_(x in [set: ar_carrier Ar R_obj])
                   (f (cR x))%:E)))%R)%:E.
```

The proof is two lines: rewrite the right-hand side by the
conditioning law `condition_E` and apply the rejection master
identity `reject_prog_master` — both sides equal
`∫_U f d⟦model_run⟧`. The probability-model form additionally
identifies the normaliser with the evidence
(`1 − 1 + ∫f dν_M = ∫f dν_M = ⟦condition_prog⟧(setT)`).

### Specialising to a sampler (`ex_sampler`, `ex_reject`, `ex_reject_cbv`, `ex_reject_comb_sampler_E`, `ex_reject_comb_sampler_master`, `ex_reject_master`, `ex_reject_is_normalised_posterior`, `ex_reject_posterior_simple`, `ex_reject_mass_one`, `ex_reject_zero`, `ex_reject_normalises_score`)

Instantiating the model to `λ_. sample µ` (`ex_sampler`) with a
unit-mass prior recovers textbook rejection sampling against a
prior: `ν_M = µ`, `m₀ = 1`, and the master identity specialises to
the classical `∫f dµ · ν(U) = ∫_U f dµ`. The standalone program
`ex_reject` — sample from the prior, accept with probability `f(x)`,
recurse on rejection through an explicit acceptance continuation —
was proved first and is kept as a regression anchor; its theorems
are proved directly in `theories/programs/ex_reject_headline.v`.
The bridge `ex_reject_comb_sampler_E` identifies the two
denotations (the two Kleene chains satisfy the same per-iterate mass
cascade, so the suprema coincide), and `ex_reject_normalises_score`
is the equivalence theorem at this instance: rejection sampling
normalises exactly the score program's unnormalised posterior.

| Result | Statement | Rocq |
|---|---|---|
| Def (`ex_reject`) | `let rec rs accept = let x = sample µ in if Bernoulli (Meas{f} x) then accept x else rs accept in rs (λy. y)` of type `tR` — the standalone sampler, abstracted over an acceptance continuation. | `ex_reject`, `ex_reject_cbv`, `ex_sampler` — `theories/programs/examples.v` |
| Thm (`ex_reject_master`) | `∫f dµ · ν(U) = ∫_U f dµ` for every measurable `U`, unconditionally (graceful at `∫f dµ = 0`). | `ex_reject_master` — `theories/programs/ex_reject_headline.v` |
| Thm (`ex_reject_is_normalised_posterior`) | If `0 < ∫f dµ` then `ν(U) = (∫_U f dµ) / (∫ f dµ)` — the normalised posterior of the prior `µ` given the soft predicate `f`; `ν(setT) = 1` (`ex_reject_mass_one`); at `∫f dµ = 1` no normalisation is needed (`ex_reject_posterior_simple`); at `f ≡ 0` the denotation is the zero measure (`ex_reject_zero`). | `ex_reject_is_normalised_posterior`, `ex_reject_posterior_simple`, `ex_reject_mass_one`, `ex_reject_zero` — same file |
| Thm (`ex_reject_comb_sampler_E`) | The combinator applied to the sampler model `λ_. sample µ` at the unit input denotes the same measure as `ex_reject`; the master identity re-derived through the bridge is `ex_reject_comb_sampler_master`. | `ex_reject_comb_sampler_E`, `ex_reject_comb_sampler_master` — `theories/programs/ex_reject_model.v` |
| Thm (`ex_reject_normalises_score`) | `(∫ f dµ) · ν_reject(U) = ν_score(U)` at `µ(setT) = 1`: the equivalence theorem at the sampler instance, connecting `ex_reject` with `ex_score_posterior`. | `ex_reject_normalises_score` — `theories/programs/infra/cbv_marginals.v` |

```coq
(* theories/programs/examples.v *)
Definition ex_reject : @named_expr R Ar R_obj nil tR' :=
  [ let rec "rs" "accept" :=
      (let "x" := sample m in
       if Bernoulli (Meas { f , Hf_meas } # "x")
       then # "accept" @ # "x"
       else # "rs" @ # "accept")
    in # "rs" @ (\ "y" ::: tR' => # "y") ].
```

```coq
(* theories/programs/ex_reject_headline.v — Section RejectHeadline *)
Theorem ex_reject_master U : measurable U ->
  If * fmeas_mu reject_denot U = IUf U.
```

```coq
(* theories/programs/ex_reject_headline.v — Section RejectHeadline *)
Theorem ex_reject_is_normalised_posterior :
  0 < If -> forall U, measurable U ->
  fmeas_mu reject_denot U = ((fine (IUf U) / fine If)%R)%:E.
```

```coq
(* theories/programs/ex_reject_model.v — Section SamplerInstance *)
Theorem ex_reject_comb_sampler_E :
  inst_denot =
  linhom_fun (ex_reject_cbv R_carrier_meas R_to_carrier_meas
                m Hf_meas) one1.
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
echo "Print Assumptions ex_reject_comb_sampler_E."      | \
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
