# EXAMPLES.md — End-to-end PPL example programs

Each surface program in `theories/programs/examples.v` is reproduced
here with its headline correctness identities, all proved against the
call-by-value interpreter `eD` of `theories/programs/ppl_cbv.v`. The
programs are written exclusively in the direct-style `ppl_named`
custom entry of `theories/programs/ppl.v` (brackets `[ … ]` enter the
entry; curly braces `{ x }` escape back to plain Rocq). Every
constructor of the language is exercised somewhere below. The
rejection-sampling program carries the headline of the development —
its denotation is the normalised posterior
(`ex_reject_is_normalised_posterior`) — and the three non-recursive
QBS-style programs carry closed-form CBV marginal identities
(`theories/programs/infra/cbv_qbs_marginals.v`). A call-by-name
interpretation of the same surface programs is preserved on the
`cbn-track` branch; main is CBV-only.

The paper-side correspondence (§§ 2–9 ↔ Rocq) lives on the
[Paper tab](../paper/); the categorical-level PPL infrastructure
(the surface inductive, the CBV interpretation, the fixpoint
machinery, the semantic laws) lives on the [PPL tab](../ppl/). This
document covers the **examples themselves**.

---

## Beyond the paper — QBS-style examples

The QBS-paper flagship programs. Three end-to-end probabilistic
programs that *do not* use recursion. Each one exercises a different
constructor of the language (`ne_let` + `ne_sample`, `ne_add` +
`ne_mul`, `ne_score`) and ships a closed-form CBV marginal identity
tying its denotation to the corresponding distribution, proved in
`theories/programs/infra/cbv_qbs_marginals.v`. The surface
constructors and the named-variable machinery the programs are
written in are documented in
[the surface-language chapter](../../ppl/chapters/ppl-ch-the-surface-language.html).
Every proof follows the same route: the let-at-sample integral law
`eD_let_sample_int` (`theories/programs/infra/let_sample_law.v`)
turns each `let x = sample µ in …` prefix into a Pettis integral over
Diracs of the prior, dereliction / evaluation at setlike test points
pushes inside the integral, and the integrand computes pointwise down
to a Dirac integral.

| Paper-style label | English statement | Rocq |
|---|---|---|
| Constant random function | `let c := sample µ in λx. c` of type `tfun tR tR` denotes the QBS-flagship "distribution over a function space" (constant-output): its marginal at every probability test point is the prior `µ`. | `ex_random_constant` — `theories/programs/examples.v`; `ex_random_constant_cbv_marginal` — `theories/programs/infra/cbv_qbs_marginals.v` |
| Random affine function | `let m := sample µ in let b := sample µ in λx. m·x + b` of type `tfun tR tR` denotes a random-coefficients linear regression model: its marginal at a Dirac test point `δ_{r0}` is the iterated-integral pushforward of two prior draws along `(m, b) ↦ m·r0 + b`. | `ex_random_linear` — `theories/programs/examples.v`; `ex_random_linear_cbv_marginal` — `theories/programs/infra/cbv_qbs_marginals.v` |
| Unnormalised Bayesian posterior | `let m := sample µ in let _ := score f #"m" in #"m"` of type `tR` denotes the unnormalised posterior: its measure on every measurable `U` is `∫_U f dµ`. | `ex_bayes_linear` — `theories/programs/examples.v`; `ex_bayes_linear_cbv_posterior` — `theories/programs/infra/cbv_qbs_marginals.v` |

### ex_random_constant (`ex_random_constant`, `ex_random_constant_cbv_marginal`, `ex_random_constant_cbv_marginal_dirac`, `ex_random_constant_cbv_marginal_mass`)

The QBS flagship constant-output random function. After sampling a
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
  [ let "c" := Sample (mu, Hmu) in \ "x" ::: tR' => # "c" ].
```

All identities live in `theories/programs/infra/cbv_qbs_marginals.v`
(Section RandomConstantMarginal), stated against the public
linhom-valued denotation `ex_random_constant_cbv` at the unit context
point `one1`.

| Side | Headline | Status |
|---|---|---|
| CBV — derelicting the denotation and evaluating at any PROBABILITY test point recovers the prior µ, uniformly in the test point. | `ex_random_constant_cbv_marginal` — *fmeas_mu x setT = 1 → ⟦ex_random_constant⟧(one1) derelicted at x = µ* | axiom-free |
| CBV — at a Dirac test point the marginal is the prior (Diracs are probabilities). | `ex_random_constant_cbv_marginal_dirac` — *the marginal at δ_{r0} equals µ* | axiom-free |
| CBV — the marginal's mass at every measurable set is exactly the prior's mass on that set. | `ex_random_constant_cbv_marginal_mass` — *the marginal's measure at every U equals µ(U)* | axiom-free |

```coq
(* theories/programs/infra/cbv_qbs_marginals.v — Section RandomConstantMarginal *)
Theorem ex_random_constant_cbv_marginal (x : FMeas R_obj) :
  fmeas_mu x [set: ar_carrier Ar R_obj] = 1%E ->
  linhom_fun
    (Lfun (der (Lty tR' tR'))
       (linhom_fun (ex_random_constant_cbv R_carrier_meas
                      R_to_carrier_meas Hmu) one1)) x = mu.

Theorem ex_random_constant_cbv_marginal_dirac (r0 : ar_carrier Ar R_obj) :
  linhom_fun
    (Lfun (der (Lty tR' tR'))
       (linhom_fun (ex_random_constant_cbv R_carrier_meas
                      R_to_carrier_meas Hmu) one1)) (dirac_fmeas r0) = mu.
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
`(m, b) ↦ m·r0 + b`.

```coq
(* theories/programs/examples.v *)
Definition ex_random_linear :
    @named_expr R Ar R_obj nil (tfun tR' tR') :=
  [ let "m" := Sample (mu, Hmu) in
    let "b" := Sample (mu, Hmu) in
    \ "x" ::: tR' => # "m" * # "x" + # "b" ].
```

Both identities live in `theories/programs/infra/cbv_qbs_marginals.v`
(Section RandomLinearMarginal).

| Side | Headline | Status |
|---|---|---|
| CBV — derelicted and evaluated at a Dirac test point δ_{r0}, the denotation's measure on every measurable U is the iterated integral ∫∫ δ_{m·r0+b}(U) µ(db) µ(dm). | `ex_random_linear_cbv_marginal` — *fmeas_mu (⟦ex_random_linear⟧(one1) derelicted at δ_{r0}) U = ∫∫ δ_{m·r0+b}(U) µ(db) µ(dm)* | axiom-free |
| CBV — the inner continuation (one sample left) marginalises to a single integral over the intercept. | `rl_inner_marginal` — *the marginal of ⟦ex_rl_inner⟧(1 ⊗ δ_m) at δ_{r0} on U is ∫ δ_{m·r0+b}(U) µ(db)* | axiom-free |

```coq
(* theories/programs/infra/cbv_qbs_marginals.v — Section RandomLinearMarginal *)
Theorem ex_random_linear_cbv_marginal (r0 : ar_carrier Ar R_obj)
    (U : set (ar_carrier Ar R_obj)) (mU : measurable U) :
  fmeas_mu
    (linhom_fun
       (Lfun (der (Lty tR' tR'))
          (linhom_fun (ex_random_linear_cbv R_carrier_meas
                         R_to_carrier_meas Hmu) one1))
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

### ex_bayes_linear (`ex_bayes_linear`, `ex_bayes_linear_cbv_posterior`, `ex_bayes_linear_cbv_mass`)

The textbook prior / score / observe shape of Bayesian inference:
sample a parameter `m` from the prior `µ`, score by a measurable
density `f(m) ∈ [0, 1]`, return `m`. Exercises `ne_score` and
delivers the **unnormalised posterior**: the denotation's measure on
every measurable `U` is `∫_U f dµ` — the prior reweighted by the
evidence density, with total mass the evidence `∫ f dµ`.

```coq
(* theories/programs/examples.v *)
Definition ex_bayes_linear :
    @named_expr R Ar R_obj nil tR' :=
  [ let "m" := Sample (mu, Hmu) in
    let "_" := Score { f, Hf_meas, Hf_ge0, Hf_le1 } # "m" in
    # "m" ].
```

Both identities live in `theories/programs/infra/cbv_qbs_marginals.v`
(Section BayesPosterior). They pair with the rejection-sampling
headline of the chapter below: `score` produces the *unnormalised*
posterior, rejection sampling produces the *normalised* one, and
`ex_reject_normalises_bayes` (same file) connects the two programs
exactly — see the Bayes-pairing entry of the rejection-sampling
chapter below.

| Side | Headline | Status |
|---|---|---|
| CBV — the denotation's measure on every measurable U is the restricted evidence integral: the prior reweighted by the density, NOT normalised. | `ex_bayes_linear_cbv_posterior` — *fmeas_mu ⟦ex_bayes_linear⟧(one1) U = ∫_U f∘cR dµ* | axiom-free |
| CBV — the total mass of the denotation is the evidence ∫ f dµ. | `ex_bayes_linear_cbv_mass` — *fmeas_mu ⟦ex_bayes_linear⟧(one1) setT = ∫ f∘cR dµ* | axiom-free |

```coq
(* theories/programs/infra/cbv_qbs_marginals.v — Section BayesPosterior *)
Theorem ex_bayes_linear_cbv_posterior (U : set (ar_carrier Ar R_obj))
    (mU : measurable U) :
  fmeas_mu
    (linhom_fun (ex_bayes_linear_cbv R_carrier_meas R_to_carrier_meas
                   Hmu Hf_meas Hf_ge0 Hf_le1) one1) U =
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
(`bl_cont_at_dirac`); the Dirac's measure of `U` is the indicator,
and the integral collapses to `∫_U f dµ`.

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
| Bare divergence | `(let rec l = λ_. l ()) ()` of type `tunit`, total mass `0`. | `ex_loop` — `theories/programs/examples.v` |
| Geometric distribution | `(let rec g = λ_. if Bernoulli(½) then 0 else 1 + g ()) ()` of type `tR'`, total mass `1`: the sampler halts almost surely. | `ex_geom` — `examples.v`; `ex_geom_cbv_mass_one` — `theories/programs/ex_reject_headline.v` |
| Parameterised partial termination | `(let rec l = λ_. if Bernoulli(p) then () else l ()) ()` of type `tunit`: mass `1` when `p > 0`, mass `0` when `p = 0`. | `ex_almost_loop` — `examples.v`; `ex_almost_loop_cbv_mass_one`, `ex_almost_loop_cbv_zero` — `theories/programs/ex_reject_headline.v` |

### ex_loop (`ex_loop`)

Bare divergence: `let rec l = λ_. l () in l ()`. No effect, no
sampling, no scoring — just an infinite chain of unit-typed
recursive calls. Mathematically the program has total mass `0`: the
recursion never terminates.

```coq
(* theories/programs/examples.v *)
Definition ex_loop :
    @named_expr R Ar R_obj nil tunit :=
  [ (fix "l" ::: tfun tunit tunit in \ "_" ::: tunit => # "l" @ ()) @ () ].
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
  [ (fix "g" ::: tfun tunit tR' in
       \ "_" ::: tunit =>
         (if Bernoulli { (1 / 2 : R), bernoulli_half_ge0, bernoulli_half_le1 }
          then [| 0%R |]
          else [| 1%R |] + # "g" @ ())) @ () ].
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
Definition ex_almost_loop (p : R)
    (Hp_ge0 : (0 <= p)%R) (Hp_le1 : (p <= 1)%R) :
    @named_expr R Ar R_obj nil tunit :=
  [ (fix "l" ::: tfun tunit tunit in
       \ "_" ::: tunit =>
         (if Bernoulli { p, Hp_ge0, Hp_le1 }
          then ()
          else # "l" @ ())) @ () ].
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
`linhom_fun (ex_almost_loop_cbv R_carrier_meas R_to_carrier_meas Hp0 Hp1) one1`.)

---

## Beyond the paper — Rejection sampling denotes the normalised posterior

The headline of the development, told start to finish. *What
rejection sampling is*: you want to sample from a distribution you
can only describe as "the prior `µ`, reweighted by an acceptance
function `f` with values in `[0, 1]`". Rejection sampling does it
with a loop — propose a candidate `x` from the prior, accept it with
probability `f(x)`, and on rejection throw the candidate away and
retry with a fresh draw. The accepted output is distributed as the
reweighted prior, *renormalised* — and the loop may in principle run
forever, so termination is itself a theorem, not an assumption. The
formal content lives in `theories/programs/ex_reject_headline.v`
(the reduction chain and the five theorems, axiom-free) and
`theories/programs/infra/cbv_qbs_marginals.v` (the Bayes pairing),
on top of the surface program of `theories/programs/examples.v`.

| Paper-style label | English statement | Rocq |
|---|---|---|
| Rejection sampling | `(let rec rs = λaccept. let x = sample µ in if Bernoulli_f{f} x then accept x else rs accept) (λy. y)` of type `tR` — sample from the prior, accept with probability `f x`, recurse on rejection. | `ex_reject`, `ex_reject_cbv` — `theories/programs/examples.v` |
| The master identity | `∫f dµ · ν(U) = ∫_U f dµ` for every measurable `U`, unconditionally (graceful at `∫f dµ = 0`). | `ex_reject_master` — `theories/programs/ex_reject_headline.v` |
| The normalised posterior | If acceptance has positive mass, `ν(U) = (∫_U f dµ) / (∫ f dµ)` — the program denotes the posterior of the prior `µ` given the soft predicate `f`. | `ex_reject_is_normalised_posterior` — same file |
| The Bayes pairing | `(∫ f dµ) · ν_reject(U) = ν_bayes(U)` at `µ(setT) = 1`: rejection sampling normalises exactly the score program's unnormalised posterior. | `ex_reject_normalises_bayes` — `theories/programs/infra/cbv_qbs_marginals.v` |

### ex_reject (`ex_reject`, `ex_reject_master`, `ex_reject_is_normalised_posterior`, `ex_reject_mass_one`, `ex_reject_zero`)

`ex_reject` is a higher-order, probabilistic, possibly
non-terminating closed term of type `tR`:

```coq
(* theories/programs/examples.v *)
Definition ex_reject : @named_expr R Ar R_obj nil tR' :=
  [ (fix "rs" ::: tfun (tfun tR' tR') tR' in
       \ "accept" ::: (tfun tR' tR') =>
         (let "x" := Sample (mu , Hmu) in
          if Bernoulli_f { f , Hf_meas , Hf_ge0 , Hf_le1 } # "x"
          then # "accept" @ # "x"
          else # "rs" @ # "accept"))
    @ (\ "y" ::: tR' => # "y") ].
```

Token by token:

- `fix "rs" ::: tfun (tfun tR' tR') tR' in …` — the recursion
  binder (`ne_fix`): `rs` names the sampler itself inside its own
  body, at the function type *continuation → real*. Semantically
  this is the seeded value-fixpoint combinator `fix_comb`.
- `\ "accept" ::: (tfun tR' tR') => …` — the sampler is
  **higher-order**: it abstracts over the acceptance continuation
  `accept`, a function value passed to the recursive call unchanged.
- `let "x" := Sample (mu, Hmu) in …` — propose: draw a candidate
  `x` from the prior `µ` (`ne_sample`; the witness `Hmu` bounds the
  prior's mass by 1).
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
- `@ (\ "y" ::: tR' => # "y")` — finally the recursive sampler is
  applied to the identity continuation, so the whole program returns
  the accepted sample itself.

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

### The Bayes pairing (`ex_reject_normalises_bayes`)

The rejection sampler pairs with the score program of the QBS
chapter: `ex_bayes_linear` (sample, *score* by `f`, return) denotes
the **unnormalised** posterior — its measure on `U` is `∫_U f dµ`
(`ex_bayes_linear_cbv_posterior`) — while `ex_reject` (sample,
*accept-or-retry* by `f`) denotes the **normalised** posterior. The
theorem connects the two programs exactly: at a probability prior,
the rejection denotation times the total evidence *is* the
Bayes-score denotation.

| Side | Headline | Status |
|---|---|---|
| CBV — rejection sampling normalises exactly the Bayes-score posterior: (∫ f dµ) · ν_reject(U) = ν_bayes(U) at µ(setT) = 1, for every measurable U. | `ex_reject_normalises_bayes` — *(∫ f∘cR dµ) · fmeas_mu ⟦ex_reject⟧(one1) U = fmeas_mu ⟦ex_bayes_linear⟧(one1) U* | axiom-free |

```coq
(* theories/programs/infra/cbv_qbs_marginals.v — Section BayesPosterior *)
(** Rejection sampling normalises exactly this measure: combining
    [ex_reject_master] with the posterior identity, the rejection
    denotation times the total evidence is the Bayes denotation. *)
Theorem ex_reject_normalises_bayes
    (Hmu1 : fmeas_mu mu [set: ar_carrier Ar R_obj] = 1)
    (U : set (ar_carrier Ar R_obj)) (mU : measurable U) :
  (\int[fmeas_mu mu]_(r in [set: ar_carrier Ar R_obj]) (f (cR r))%:E) *
  fmeas_mu
    (linhom_fun (ex_reject_cbv R_carrier_meas R_to_carrier_meas
                   Hmu Hf_meas Hf_ge0 Hf_le1) one1) U =
  fmeas_mu
    (linhom_fun (ex_bayes_linear_cbv R_carrier_meas R_to_carrier_meas
                   Hmu Hf_meas Hf_ge0 Hf_le1) one1) U.
```

The proof is one line on top of the two headlines: rewrite the
right-hand side by `ex_bayes_linear_cbv_posterior` and apply
`ex_reject_master`. Two inference idioms — soft evidence via `score`,
hard retry via rejection — and the model proves they compute the same
posterior up to the evidence constant.

---

## What is **not** formalised

The open items are CBV-side; the call-by-name interpretation and its
headlines are not gaps of this document — they live on the
`cbn-track` branch.

| Item | What it is | Why not yet |
|---|---|---|
| CBV distribution refinements for the recursive programs | Pinning the CBV denotations of `ex_geom` / `ex_almost_loop` as *measures* (the geometric PMF `(1/2)^(k+1)` at every `k`; the Dirac at 0), not just their total mass. | The mass identities reduce to a scalar affine cascade; the distribution identities need the per-set version of the same per-iterate induction, which has not been written. |
| Mutual recursion at product types (`ne_fix_mr` at `tprod`) | A surface example exercising `ne_fix_mr` at `tprod (tfun A1 B1) (tfun A2 B2)` with a genuine semantics. | The CBV clause at product body types still routes through the provably-zero `Yfix_fun_lin` (`eD_fix_mr_prod_E`, the honest scope record); the repair needs the Seely transport of `fix_comb` — see the PPL tab's gaps table. |

These choices are deliberate; each requires substantial
infrastructure outside the current scope and does not block any
*existing* headline result.

---

## How to verify

```sh
make -j

# QBS-style examples — the CBV marginals
echo "Print Assumptions ex_random_constant_cbv_marginal." | \
  rocq top -Q theories Icones -l theories/programs/infra/cbv_qbs_marginals.v
echo "Print Assumptions ex_random_linear_cbv_marginal."   | \
  rocq top -Q theories Icones -l theories/programs/infra/cbv_qbs_marginals.v
echo "Print Assumptions ex_bayes_linear_cbv_posterior."   | \
  rocq top -Q theories Icones -l theories/programs/infra/cbv_qbs_marginals.v

# Recursive probabilistic examples — the CBV mass identities
echo "Print Assumptions ex_geom_cbv_mass_one."          | \
  rocq top -Q theories Icones -l theories/programs/ex_reject_headline.v
echo "Print Assumptions ex_almost_loop_cbv_mass_one."   | \
  rocq top -Q theories Icones -l theories/programs/ex_reject_headline.v
echo "Print Assumptions ex_almost_loop_cbv_zero."       | \
  rocq top -Q theories Icones -l theories/programs/ex_reject_headline.v

# The rejection-sampling headline + the Bayes pairing
echo "Print Assumptions ex_reject_master."              | \
  rocq top -Q theories Icones -l theories/programs/ex_reject_headline.v
echo "Print Assumptions ex_reject_is_normalised_posterior." | \
  rocq top -Q theories Icones -l theories/programs/ex_reject_headline.v
echo "Print Assumptions ex_reject_normalises_bayes."    | \
  rocq top -Q theories Icones -l theories/programs/infra/cbv_qbs_marginals.v
```

Each command reports only `propositional_extensionality`,
`functional_extensionality_dep` and
`constructive_indefinite_description` (the classical-logic axioms of
`mathcomp-analysis`). Per-entry pages embed the precise identifier
name, file, and a GitHub link to the Rocq source.

For the underlying surface inductive and the CBV interpretation, see
the [PPL tab](../ppl/) — `docs/PPL.md`. For the paper-side
correspondence (§§ 2–9 ↔ Rocq), see the [Paper tab](../paper/) —
`docs/PAPER.md`.
