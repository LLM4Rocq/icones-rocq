# EXAMPLES.md — End-to-end PPL example programs

Each surface program in `theories/programs/examples.v` is reproduced
here with its headline correctness identities. The programs are
written exclusively in the direct-style `ppl_named` custom entry of
`theories/programs/ppl.v` (brackets `[ … ]` enter the entry; curly
braces `{ x }` escape back to plain Rocq). Every constructor of the
language and every CBN-side clause is exercised somewhere below; the
CBV interpretation of `theories/programs/ppl_cbv.v` accepts the same
surface terms, and the rejection-sampling program now carries the
CBV headline of the development: its denotation is the normalised
posterior (`ex_reject_is_normalised_posterior`).

The paper-side correspondence (§§ 2–9 ↔ Rocq) lives on the
[Paper tab](../paper/); the categorical-level PPL infrastructure
(the surface inductive, the two interpretations, the fixpoint
machinery) lives on the [PPL tab](../ppl/). This document covers the
**examples themselves**.

---

## Beyond the paper — QBS-style examples

The QBS-paper flagship programs. Three end-to-end probabilistic
programs that *do not* use recursion. Each one exercises a different
constructor of the language (`ne_let` + `ne_sample`, `ne_add` +
`ne_mul`, `ne_score`) and ships a CBN-side headline identity tying
its denotation to the corresponding distribution. The surface
constructors and the named-variable machinery the programs are
written in are documented in
[the surface-language chapter](../../ppl/chapters/ppl-ch-the-surface-language.html).
On the CBV side the three surface terms compile through `eD`, and
the let-at-sample integral law `eD_let_sample_int`
(`theories/programs/infra/let_sample_law.v`) now provides the
reduction engine for their marginals; restating the three CBN
headlines against `eD` is a follow-up (see the gaps table below).

| Paper-style label | English statement | Rocq |
|---|---|---|
| Constant random function | `let c := sample µ in λx. c` of type `tfun tR tR` denotes the QBS-flagship "distribution over a function space" (constant-output). | `ex_random_constant` — `theories/programs/examples.v` |
| Random affine function | `let m := sample µ in let b := sample µ in λx. m·x + b` of type `tfun tR tR` denotes a random-coefficients linear regression model. | `ex_random_linear` — same file |
| Unnormalised Bayesian posterior | `let m := sample µ in let _ := score f #"m" in #"m"` of type `tR` denotes the unnormalised posterior of total mass `∫ f(m) dµ(m)`. | `ex_bayes_linear` — same file |

### ex_random_constant (`ex_random_constant`, `ex_random_constant_CBN_headline`, `ex_random_constant_CBN_marginal_mass`)

The QBS flagship constant-output random function. After sampling a
single random constant `c ~ µ`, the program returns the function
`λx. c` — every call to the function returns the same value, but the
function itself was sampled from `µ`. The headline correctness
statement is the *marginal at every `x`*: evaluating the function at
any test point recovers the prior `µ`.

```coq
(* theories/programs/examples.v *)
Definition ex_random_constant :
    @named_expr R Ar R_obj nil (tfun tR' tR') :=
  [ let "c" := Sample (mu, Hmu) in \ "x" ::: tR' => # "c" ].
```

All three CBN identities live in
`theories/programs/ppl_cbn_headlines.v`, stated against the fully
instantiated CBN denotation `eD_CBN_complete`.

| Side | Headline | Status |
|---|---|---|
| CBN — the denotation reduces definitionally to the composite of the lambda body's interpretation after the pairing of the identity with the sample clause. | `ex_random_constant_CBN_headline_struct` — *⟦ex_random_constant⟧ = scones_comp ⟦λx. c⟧ (spair id sample-µ)* | axiom-free |
| CBN — evaluating the sampled function at any unit-ball test point recovers the prior µ, uniformly in the test point. | `ex_random_constant_CBN_headline` — *sh_fun (sc_fun ⟦ex_random_constant⟧ g) x = µ* | axiom-free |
| CBN — the marginal at every test point assigns to each measurable set exactly the mass the prior assigns to it. | `ex_random_constant_CBN_marginal_mass` — *the marginal's mass at every measurable U equals µ(U)* | axiom-free |

The structural reduction is definitional: the `eD_CBN` clauses for
`ne_let` and `ne_lam` unfold by computation, so the denotation
literally *is* the `scones_comp` of the lambda's interpretation
(`ex_rc_lam`) after the `spair` of the identity and the sample
clause — the proof is `by []`.

```coq
(* theories/programs/ppl_cbn_headlines.v *)
Lemma ex_random_constant_CBN_headline_struct :
  eD_CBN_complete (ex_random_constant mu Hmu) =
  scones_comp (eD_CBN_complete ex_rc_lam)
              (spair (scones_id (ctxD_CBN (drop_names nil)))
                     (cbn_sample_clause_def nil mu Hmu)).
Proof. by []. Qed.
```

The marginal identity starts from the structural reduction, peels the
composite on the unit ball (`scomp_ball` / `scpair_ball`), and
evaluates the sample clause to `µ`. The lambda's interpretation is a
`curry`, so the β-rule `curry_appE` turns application at `x` into the
body's evaluation at the extended environment `((g, µ), x)`; the
variable lookup `#"c"` then projects out the sampled `µ`
(`cbn_var_c_pointwise_E`: it is `sprod_snd` of `sprod_fst` of the
environment).

```coq
(* theories/programs/ppl_cbn_headlines.v *)
Lemma ex_random_constant_CBN_headline
    (g : ctxD_CBN (drop_names nil)) (Hg : (cone_norm g <= 1)%R)
    (x : FMeas R_obj) (Hx : (cone_norm x <= 1)%R) :
  sh_fun (sc_fun (eD_CBN_complete (ex_random_constant mu Hmu)) g) x = mu.
```

The pointwise mass identity is a one-line corollary: rewriting by the
marginal identity makes the two measures syntactically equal, so
their masses agree at every measurable set `U`.

```coq
(* theories/programs/ppl_cbn_headlines.v *)
Corollary ex_random_constant_CBN_marginal_mass
    (g : ctxD_CBN (drop_names nil)) (Hg : (cone_norm g <= 1)%R)
    (x : FMeas R_obj) (Hx : (cone_norm x <= 1)%R)
    (U : set (ar_carrier Ar R_obj)) :
  fmeas_mu (sh_fun (sc_fun (eD_CBN_complete (ex_random_constant mu Hmu)) g) x) U
   = fmeas_mu mu U.
Proof. by rewrite ex_random_constant_CBN_headline. Qed.
```

### ex_random_linear (`ex_random_linear`, `ex_random_linear_arith_marginal_at`, `ex_random_linear_CBN_marginal_zero`)

A random-coefficients linear regression: sample slope `m` and
intercept `b` from `µ`, return the function `λx. m·x + b`. Exercises
`ne_add` and `ne_mul` via the FMeas lax-monoidal map of paper §5; on
Dirac inputs the lifts reduce to scalar arithmetic. The marginal
identity ties the surface program to the joint pushforward of
`µ ⊗ µ` along `(m, b) ↦ m·x + b`.

```coq
(* theories/programs/examples.v *)
Definition ex_random_linear :
    @named_expr R Ar R_obj nil (tfun tR' tR') :=
  [ let "m" := Sample (mu, Hmu) in
    let "b" := Sample (mu, Hmu) in
    \ "x" ::: tR' => # "m" * # "x" + # "b" ].
```

The honest bilinear marginal lives in
`theories/programs/ppl_cbn_arith_eff.v`, whose arithmetic clauses are
built from the SCones/ICones tensor bridge of
[the bilinear-stability-bridge chapter](../../ppl/chapters/ppl-ch-the-sconesicones-tensor-bilinear-stability-bridge.html);
the baseline degenerate marginal lives in
`theories/programs/ppl_cbn_headlines.v`.

| Side | Headline | Status |
|---|---|---|
| CBN — under the option-β arithmetic clauses, the marginal at any unit-ball argument is the honest bilinear lift of the two sampled coefficients. | `ex_random_linear_arith_marginal_at` — *the marginal at arg is add_FMeas (mul_FMeas µ arg) µ, the pushforward of µ ⊗ µ along (m, b) ↦ m·arg + b* | axiom-free |
| CBN — under the baseline option-γ clauses the same marginal degenerates to the zero measure, exposing the pragmatic add/mul clauses honestly. | `ex_random_linear_CBN_marginal_zero` — *the marginal at every x is precone_zero* | axiom-free |

The honest marginal is proved against `eD_CBN_full_arith`, the CBN
pipeline whose `cbn_add_clause_arith` / `cbn_mul_clause_arith` are
the bilinear `add_FMeas_scones` / `mul_FMeas_scones` composed with an
`spair`. The proof unfolds the two nested let-sample layers
definitionally, β-reduces the lambda with `curry_appE`, computes the
body to *add_FMeas (mul_FMeas m x) b* via
`ex_rl_lam_arith_pointwise`, and finally identifies the three
variable lookups in the environment `(((0, µ), µ), arg)` as `µ`, `µ`
and `arg` respectively.

```coq
(* theories/programs/ppl_cbn_arith_eff.v *)
Theorem ex_random_linear_arith_marginal_at
    (arg : FMeas R_obj) (Harg : (cone_norm arg <= 1)%R) :
  sh_fun (sc_fun (eD_CBN_full_arith ex_random_linear) precone_zero) arg
  = add_FMeas (mul_FMeas mu arg) mu.
```

The degenerate counterpart documents *why* the baseline option-γ
clauses cannot see the arithmetic: the M3 `cbn_add_clause_def` /
`cbn_mul_clause_def` are constant at `precone_zero` (no tensor bridge
is used), so the lambda body's denotation is constant at the zero
measure regardless of the values of `m`, `b` and `x`. The proof
replays the same structural reduction and closes with
`cbn_add_pointwise_E`, the pointwise computation of the constant add
clause.

```coq
(* theories/programs/ppl_cbn_headlines.v *)
Lemma ex_random_linear_CBN_marginal_zero
    (g : ctxD_CBN (drop_names nil)) (Hg : (cone_norm g <= 1)%R)
    (x : FMeas R_obj) (Hx : (cone_norm x <= 1)%R) :
  sh_fun (sc_fun (eD_CBN_complete (ex_random_linear mu Hmu)) g) x =
  (precone_zero : FMeas R_obj).
```

### ex_bayes_linear (`ex_bayes_linear`, `ex_bayes_linear_CBN_headline`, `ex_bayes_linear_CBN_mass`)

The textbook prior / score / observe shape of Bayesian inference:
sample a parameter `m` from the prior `µ`, score by a measurable
density `f(m) ∈ [0, 1]`, return `m`. Exercises `ne_score` and
delivers the unnormalised posterior of total mass `∫ f(m) dµ(m)`.

```coq
(* theories/programs/examples.v *)
Definition ex_bayes_linear :
    @named_expr R Ar R_obj nil tR' :=
  [ let "m" := Sample (mu, Hmu) in
    let "_" := Score { f, Hf_meas, Hf_ge0, Hf_le1 } # "m" in
    # "m" ].
```

Both CBN identities live in
`theories/programs/ppl_cbn_headlines.v`. The honest non-degenerate
arithmetic refinement that would expose the genuine weighted
posterior is the subject of
[the CBN arithmetic-refinement chapter](../../ppl/chapters/ppl-ch-the-cbn-arithmetic-refinement-option.html).

| Side | Headline | Status |
|---|---|---|
| CBN — the denotation at any unit-ball environment equals the prior µ itself: under option-γ the score lands in the terminal object and cannot weight the result. | `ex_bayes_linear_CBN_headline` — *sc_fun ⟦ex_bayes_linear⟧ g = µ* | axiom-free |
| CBN — the total mass of the denotation on every measurable set is exactly the prior's mass on that set. | `ex_bayes_linear_CBN_mass` — *the denotation's mass at every measurable U equals µ(U)* | axiom-free |

The key observation is that `ne_score` is typed at `tunit`, whose CBN
reading `tyD_CBN tunit = Stop Ar` is the **terminal** object — so the
score's "weight" is forced to be the unique terminal morphism and the
binding `let "_" := score …` cannot interact with the returned value.
Concretely, the proof reduces the outer let to the sample clause
(yielding `µ`), then `ex_bl_cont_pointwise_E` shows the continuation
returns `sprod_snd` of its environment — the sampled `m` — by the
variable-lookup computation `cbn_var_m_pointwise_E`. This is the
honest statement at the option-γ baseline; the option-α/β refinements
that recover the weighted posterior are listed under *What is not
formalised* below.

```coq
(* theories/programs/ppl_cbn_headlines.v *)
Lemma ex_bayes_linear_CBN_headline
    (g : ctxD_CBN (drop_names nil))
    (Hg : (cone_norm g <= 1)%R) :
  sc_fun (eD_CBN_complete (ex_bayes_linear mu Hmu f Hf_meas Hf_ge0 Hf_le1)) g = mu.
```

The mass identity is a one-line corollary of the pointwise identity:
rewriting by the headline turns both sides into the mass of `µ` at
`U`.

```coq
(* theories/programs/ppl_cbn_headlines.v *)
Corollary ex_bayes_linear_CBN_mass
    (g : ctxD_CBN (drop_names nil)) (Hg : (cone_norm g <= 1)%R)
    (U : set (ar_carrier Ar R_obj)) :
  fmeas_mu (sc_fun
              (eD_CBN_complete (ex_bayes_linear mu Hmu f Hf_meas Hf_ge0 Hf_le1))
              g) U = fmeas_mu mu U.
Proof. by rewrite ex_bayes_linear_CBN_headline. Qed.
```

---

## Beyond the paper — Recursive probabilistic examples (productive partial termination)

Recursive probabilistic programs combining `ne_fix` with the
`ne_if` / `ne_bernoulli` boolean cascade to exhibit *productive
partial termination*. Each program ships with the honest mass
identity on the CBN interpretation, instantiating the shared
Kleene-chain machinery of
[the Bernoulli-cascade-framework chapter](../../ppl/chapters/ppl-ch-the-bernoulli-cascade-framework.html);
the surface recursion constructor is documented in
[the surface-language chapter](../../ppl/chapters/ppl-ch-the-surface-language.html)
and the CBV-side interpretation of recursion in
[the CBV value-fixpoint chapter](../../ppl/chapters/ppl-ch-the-cbv-value-fixpoint-at-function-types.html).
The CBV-side mass identities now exist for both probabilistic
programs of this chapter: `ex_geom_cbv_mass_one` and
`ex_almost_loop_cbv_mass_one` / `ex_almost_loop_cbv_zero`, proven in
`theories/programs/ex_reject_headline.v` against the seeded
value-fixpoint interpreter (`fix_comb`) by the same
reduction-chain-plus-affine-cascade recipe as the rejection-sampling
headline of the next chapter.

| Paper-style label | English statement | Rocq |
|---|---|---|
| Bare divergence | `(let rec l = λ_. l ()) ()` of type `tunit`, total mass `0`. | `ex_loop`, `ex_loop_CBN_headline` — `theories/programs/examples.v` + `theories/programs/ppl_cbn_headlines.v` |
| Geometric distribution | `(let rec g = λ_. if Bernoulli(½) then 0 else 1 + g ()) ()` of type `tR'`, geometric distribution with parameter `½`. | `ex_geom`, `ex_geom_CBN_mass_one`, `ex_geom_CBN_PMF` — `examples.v` + `ppl_cbn_geom.v` + `ppl_cbn_geom_dist.v` |
| Parameterised partial termination | `(let rec l = λ_. if Bernoulli(p) then () else l ()) ()` of type `tunit`. | `ex_almost_loop`, `ex_almost_loop_p_CBN_mass_one_if_pos`, `ex_almost_loop_p_CBN_mass_zero_if_zero`, `ex_almost_loop_p_CBN_is_dirac_zero`, `ex_almost_loop_p_CBN_is_zero_if_zero` — `examples.v` + `ppl_cbn_almost_loop.v` + `ppl_cbn_almost_loop_dist.v` |

### ex_loop (`ex_loop`, `ex_loop_CBN_headline`)

Bare divergence: `let rec l = λ_. l () in l ()`. No effect, no
sampling, no scoring — just an infinite chain of unit-typed
recursive calls. Mathematically the program has total mass `0` (the
recursion never terminates); the CBN side trivially equals the
terminal map (`tunit`'s denotation is `Stop`, a singleton).

```coq
(* theories/programs/examples.v *)
Definition ex_loop :
    @named_expr R Ar R_obj nil tunit :=
  [ (fix "l" ::: tfun tunit tunit in \ "_" ::: tunit => # "l" @ ()) @ () ].
```

| Side | Headline | Status |
|---|---|---|
| CBN — the denotation of the diverging loop is exactly the unique terminal map into the singleton cone Stop. | `ex_loop_CBN_headline` — *⟦ex_loop⟧ = ders (Stop_mor _)* | axiom-free |

The proof is terminality itself: the codomain `tyD_CBN tunit = Stop
Ar` is the terminal object of ICones, a singleton cone, so any two
SCones arrows into it agree extensionally. `scones_hom_eq` reduces
the equality to every point `g`, where `Stop_eq` collapses the two
values — two lines of proof.

```coq
(* theories/programs/ppl_cbn_headlines.v *)
Lemma ex_loop_CBN_headline :
  eD_CBN_complete ex_loop =
  ders (Stop_mor (ctxD_CBN (drop_names nil))).
Proof.
apply: scones_hom_eq => g.
exact: Stop_eq.
Qed.
```

### ex_geom (`ex_geom`, `ex_geom_CBN_mass_one`, `ex_geom_CBN_PMF`, `ex_geom_cbv_mass_one`)

A geometric counter built via a fair-coin Bernoulli recursion: each
call halts with probability `½` (returning `0`) and otherwise
recurses, adding `1` to the returned real. The program denotes the
geometric distribution with parameter `½` — total mass `1` and PMF
`(1/2)^(k+1)` at every `k`.

```coq
(* theories/programs/examples.v *)
Definition ex_geom : @named_expr R Ar R_obj nil tR' :=
  [ (fix "g" ::: tfun tunit tR' in
       \ "_" ::: tunit =>
         (if Bernoulli { (1 / 2 : R), bernoulli_half_ge0, bernoulli_half_le1 }
          then [| 0%R |]
          else [| 1%R |] + # "g" @ ())) @ () ].
```

The CBN mass-one and PMF theorems instantiate
[the Bernoulli-cascade framework](../../ppl/chapters/ppl-ch-the-bernoulli-cascade-framework.html)
at parameter `½`, halt value `δ₀` and continuation `shift_scones 1`
(the FMeas pushforward along the measurable shift `(+1)`); the
recursion operator is the SCones `Yfix`. On the CBV side the
recursion is the seeded value-fixpoint combinator `fix_comb` of
[the CBV value-fixpoint chapter](../../ppl/chapters/ppl-ch-the-cbv-value-fixpoint-at-function-types.html),
and the mass-one identity `ex_geom_cbv_mass_one` is proven directly
against the CBV interpreter in
`theories/programs/ex_reject_headline.v` (Section GeomRider).

| Side | Headline | Status |
|---|---|---|
| CBN — the cascade fixpoint implementing the program's recursion has total mass one, so the geometric sampler halts almost surely. | `ex_geom_CBN_mass_one` — *the mass of ex_geom_CBN_fix on the whole carrier is 1* | axiom-free |
| CBN — the cascade fixpoint assigns mass (1/2)^(k+1) to the singleton at every natural k: it is exactly the geometric distribution. | `ex_geom_CBN_PMF` — *the mass at the singleton k equals (1/2)^(k+1)* | axiom-free |
| CBN — the full CBN denotation reduces definitionally to an evaluation of the Yfix fixpoint of the curried body paired with the terminal map. | `ex_geom_CBN_headline` — *⟦ex_geom⟧ = Ev ∘ spair (Yfix ∘ curry ⟦body⟧) (ders Stop_mor)* | axiom-free |
| CBV — the denotation of the geometric counter under the CBV interpreter `eD` has total mass one on the whole carrier: the sampler halts almost surely on the call-by-value side too. | `ex_geom_cbv_mass_one` — *fmeas_mu ⟦ex_geom⟧(one1) setT = 1* | axiom-free |

For the mass identity, `ex_geom_CBN_fix` is the SCones least fixpoint
(`sfix_bcascade`) of the cascade operator `phi_CBN_geom`, the
CBN-side operator faithfully implementing the body's reduction
*µ ↦ if Bernoulli(½) then δ₀ else shift(µ)*. The framework's
closed-form lemma `kleene_bcascade_mass_closed` computes the n-th
Kleene iterate's mass to *1 − (1/2)ⁿ* — the shift continuation is
mass-preserving (`shift_scones_mass_pres`, via `FMeas_fmap_setT_E`)
and `δ₀` has mass 1 — and `sfix_bcascade_mass_one_if_pos` passes to
the limit by `fmeas_sup_cvg` monotone convergence plus `cvg_unique`.

```coq
(* theories/programs/ppl_cbn_geom.v *)
Definition ex_geom_CBN_fix : FMeas R_obj :=
  sfix_bcascade (1/2)%R (bernoulli_half_ge0 R) (bernoulli_half_le1 R)
                halt_geom halt_geom_ball
                (shift_scones R_carrier_eq R_carrier_meas R_to_carrier_meas 1).

Theorem ex_geom_CBN_mass_one :
  fmeas_mu ex_geom_CBN_fix [set: ar_carrier Ar R_obj] = 1%:E.
```

The PMF refines the mass identity to a *measure* identity per
iterate: `kleene_geom_partial` proves by induction that the n-th
Kleene iterate **is** the explicit partial sum
*Σ_{j<n} (1/2)^(j+1) δ_j*, using linearity of the shift lift
(extracted from `linhom_pre_linear`) and the Dirac-pushforward rule
`shift_lift_dirac`. At the singleton `{k}` the iterate masses are
therefore *eventually constant* at `(1/2)^(k+1)` (for every `n > k`),
so the monotone limit identified by `fmeas_sup_cvg` and
`cvg_unique` is exactly `(1/2)^(k+1)`.

```coq
(* theories/programs/ppl_cbn_geom_dist.v *)
Theorem ex_geom_CBN_PMF (k : nat) :
  fmeas_mu (ex_geom_CBN_fix R_carrier_eq R_carrier_meas R_to_carrier_meas)
           [set R_to_carrier R_carrier_eq k%:R]
  = ((1 / 2)%R ^+ k.+1)%R%:E.
```

The structural reduction at the `eD_CBN_complete` level is
definitional (`by []`): the `ne_fix` / `ne_app` clauses unfold to the
`Ev`-after-`spair` composite of `Yfix` applied to the curried body
and the terminal map. Under the baseline option-γ clauses the body's
arithmetic degenerates, which is exactly why the mass-one and PMF
headlines above are stated against the faithfully-defined cascade
operator rather than this composite.

```coq
(* theories/programs/ppl_cbn_headlines.v *)
Lemma ex_geom_CBN_headline :
  eD_CBN_complete ex_geom =
  scones_comp (Ev (Stop Ar) (FMeas R_obj))
    (spair (scones_comp (Yfix (stablehom (Stop Ar) (FMeas R_obj)))
                        (curry (eD_CBN_complete ex_geom_body)))
           (ders (Stop_mor (Stop Ar)))).
Proof. by []. Qed.
```

The CBV identity follows the rejection-sampling reduction chain on
the simpler program: the outer application collapses by `der ∘ prom`
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
(* theories/programs/ex_reject_headline.v (Section GeomRider) *)
(** Almost-sure termination of the geometric counter: the CBV
    denotation is a PROBABILITY distribution. *)
Theorem ex_geom_cbv_mass_one :
  fmeas_mu g_denot [set: ar_carrier Ar R_obj] = 1.
```

(`g_denot` abbreviates
`linhom_fun (ex_geom_cbv R_carrier_meas R_to_carrier_meas) one1`,
the CBV denotation of the closed program at the unit context point.)

### ex_almost_loop_p (`ex_almost_loop`, `ex_almost_loop_p_CBN_mass_one_if_pos`, `ex_almost_loop_p_CBN_is_dirac_zero`, `ex_almost_loop_cbv_mass_one`)

A parameterised Bernoulli cascade: with probability `p` the
recursion halts (returning `()`) and with probability `1 − p` it
recurses. When `p > 0` the function terminates almost surely (total
mass `1`); when `p = 0` it diverges (total mass `0`). The dichotomy
is encoded in two pairs of headline theorems on the CBN side.

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

Like `ex_geom`, the mass and distribution theorems instantiate
[the Bernoulli-cascade framework](../../ppl/chapters/ppl-ch-the-bernoulli-cascade-framework.html)
— this time at parameter `p`, halt value `δ₀` and the *identity*
continuation `scones_id`.

| Side | Headline | Status |
|---|---|---|
| CBN — for every strictly positive halting probability p, the cascade fixpoint has total mass one: the loop terminates almost surely. | `ex_almost_loop_p_CBN_mass_one_if_pos` — *if p > 0 then the mass of the fixpoint on the whole carrier is 1* | axiom-free |
| CBN — when the halting probability p is zero, the cascade fixpoint has total mass zero: the loop diverges with probability one. | `ex_almost_loop_p_CBN_mass_zero_if_zero` — *if p = 0 then the mass of the fixpoint on the whole carrier is 0* | axiom-free |
| CBN — for every strictly positive p, the fixpoint is the Dirac measure at zero itself, not merely a measure of the right mass. | `ex_almost_loop_p_CBN_is_dirac_zero` — *if p > 0 then the fixpoint equals δ₀ as a measure* | axiom-free |
| CBN — when p is zero, the fixpoint is the zero measure itself, extensionally at every measurable set. | `ex_almost_loop_p_CBN_is_zero_if_zero` — *if p = 0 then the fixpoint equals precone_zero* | axiom-free |
| CBN — the full CBN denotation collapses to the unique terminal map, uniformly in the parameter p, by terminality of Stop. | `ex_almost_loop_CBN_headline` — *⟦ex_almost_loop p⟧ = ders (Stop_mor _)* | axiom-free |
| CBV — for every strictly positive p, the CBV denotation (a point of the unit cone, whose norm is the termination probability) has norm one. | `ex_almost_loop_cbv_mass_one` — *if 0 < p then cone_norm ⟦ex_almost_loop p⟧(one1) = 1* | axiom-free |
| CBV — when p is zero, the CBV denotation is the zero point of the unit cone: the loop diverges with probability one on the call-by-value side too. | `ex_almost_loop_cbv_zero` — *if p = 0 then ⟦ex_almost_loop p⟧(one1) = precone_zero* | axiom-free |

The two mass headlines are direct instances of the framework's
`sfix_bcascade_mass_one_if_pos` / `sfix_bcascade_mass_zero_if_zero`:
the only program-specific obligations are that the halt value `δ₀`
has mass 1 (`halt_alp_mass`) and that the identity continuation
preserves mass on the unit ball (`scones_id_mass_pres`). Underneath,
the framework computes the Kleene-iterate mass to the closed form
*1 − (1 − p)ⁿ* and passes to the limit.

```coq
(* theories/programs/ppl_cbn_almost_loop.v *)
Definition ex_almost_loop_p_CBN_fix : FMeas R_obj :=
  sfix_bcascade p Hp_ge0 Hp_le1 halt_alp halt_alp_ball
                (scones_id (FMeas R_obj)).

Theorem ex_almost_loop_p_CBN_mass_one_if_pos :
  (0 < p)%R ->
  fmeas_mu ex_almost_loop_p_CBN_fix [set: ar_carrier Ar R_obj] = 1%:E.
```

The divergent case needs no limit argument beyond the closed form:
when `p = 0` the prefactor *1 − (1 − 0)ⁿ* vanishes for every `n`, so
every Kleene iterate has mass zero and so does their supremum.

```coq
(* theories/programs/ppl_cbn_almost_loop.v *)
Theorem ex_almost_loop_p_CBN_mass_zero_if_zero :
  p = 0%R ->
  fmeas_mu ex_almost_loop_p_CBN_fix [set: ar_carrier Ar R_obj] = 0%E.
```

The "is" statements are stronger than the mass identities: they pin
down the fixpoint *as a measure*. The workhorse is the per-iterate
identity `kleene_alp_pointwise` — by induction, the n-th iterate's
mass at **every** measurable `U` is *(1 − (1 − p)ⁿ) · δ₀(U)*. For
`p > 0` the scalar prefactor converges to 1
(`cvg_geom_factor_to_one`), so at each `U` the iterate masses
converge to `δ₀(U)`; `fmeas_eq` plus `cvg_unique` against the
`fmeas_sup_cvg` limit then identify the fixpoint with the Dirac at 0.

```coq
(* theories/programs/ppl_cbn_almost_loop_dist.v *)
(* halt_alp_ := dirac_fmeas (R_to_carrier R_carrier_eq 0%R) : FMeas R_obj *)
Theorem ex_almost_loop_p_CBN_is_dirac_zero :
  (0 < p)%R ->
  ex_almost_loop_p_CBN_fix R_carrier_eq p Hp_ge0 Hp_le1 = halt_alp_.
```

For `p = 0` the same per-iterate identity is identically zero, so the
iterate masses converge to `0` at every measurable set and the
fixpoint is extensionally the zero measure.

```coq
(* theories/programs/ppl_cbn_almost_loop_dist.v *)
Theorem ex_almost_loop_p_CBN_is_zero_if_zero :
  p = 0%R ->
  ex_almost_loop_p_CBN_fix R_carrier_eq p Hp_ge0 Hp_le1 =
  (precone_zero : FMeas R_obj).
```

Finally, the structural wrapper at the `eD_CBN_complete` level is the
same terminality argument as `ex_loop`: the codomain `tyD_CBN tunit =
Stop Ar` is a singleton, so the denotation equals the unique terminal
map for *every* `p` — `scones_hom_eq` followed by `Stop_eq`.

```coq
(* theories/programs/ppl_cbn_headlines.v *)
Lemma ex_almost_loop_CBN_headline (p : R)
    (Hp_ge0 : (0 <= p)%R) (Hp_le1 : (p <= 1)%R) :
  eD_CBN_complete (ex_almost_loop p Hp_ge0 Hp_le1) =
  ders (Stop_mor (ctxD_CBN (drop_names nil))).
Proof.
apply: scones_hom_eq => g.
exact: Stop_eq.
Qed.
```

On the CBV side the denotation at `tunit` is a *point of the unit
cone* (the CBV `tunit` is the terminal coalgebra on `cone_one_car`,
not the SCones singleton `Stop`), so the termination probability is
visible as the point's norm and the dichotomy is an honest theorem
pair rather than a terminality triviality. The proof mirrors the
geometric rider: reduce to the `cone_sup_ball` of the iterate points
`al_iter n` (`ex_almost_loop_sup_E`), compute one Kleene step to the
scalar recurrence `al_val (n+1) = p + (1−p)·al_val n` (`al_step` /
`al_val_S`), and close with `affine_iter_cvg_real` — the limit
`p / (1 − (1−p)) = 1` for `p > 0`, and the constantly-zero chain at
`p = 0`.

```coq
(* theories/programs/ex_reject_headline.v (Section AlmostLoopRider) *)
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

The CBV headline. `ex_reject` is a higher-order (the recursive
function abstracts over the acceptance continuation), probabilistic
(continuous `sample` plus the value-dependent `Bernoulli_f`),
non-terminating (rejection recurses, and may loop forever) program
whose denotation under the CBV interpreter `eD` is identified in
closed form: writing `ν := ⟦ex_reject⟧(one1)`, `If := ∫ f dµ` and
`IUf U := ∫_U f dµ`, the master identity is `If · ν(U) = IUf U` —
unconditionally — and for `0 < If` the denotation *is* the
normalised posterior `ν(U) = (∫_U f dµ) / (∫ f dµ)` of the prior `µ`
given the soft acceptance predicate `f`. Everything lives in
`theories/programs/ex_reject_headline.v` (1661 lines, axiom-free),
on top of the surface program of `theories/programs/examples.v`, the
seeded value-fixpoint combinator, the let-at-sample integral law,
the affine cascade, and the setlike-point kit.

| Paper-style label | English statement | Rocq |
|---|---|---|
| Rejection sampling | `(let rec rs = λaccept. let x = sample µ in if Bernoulli_f{f} x then accept x else rs accept) (λy. y)` of type `tR` — sample from the prior, accept with probability `f x`, recurse on rejection. | `ex_reject`, `ex_reject_cbv` — `theories/programs/examples.v` |
| The master identity | `∫f dµ · ν(U) = ∫_U f dµ` for every measurable `U`, unconditionally (graceful at `∫f dµ = 0`). | `ex_reject_master` — `theories/programs/ex_reject_headline.v` |
| The normalised posterior | If acceptance has positive mass, `ν(U) = (∫_U f dµ) / (∫ f dµ)` — the program denotes the posterior of the prior `µ` given the soft predicate `f`. | `ex_reject_is_normalised_posterior` — same file |

### ex_reject (`ex_reject`, `ex_reject_master`, `ex_reject_is_normalised_posterior`)

Normalised-posterior rejection sampling: sample `x ~ µ`, accept with
probability `f x` (the value-dependent Bernoulli `ne_bernoulli_f`),
and on rejection *recurse*. The recursive function abstracts over
the acceptance continuation `accept`, and the headline instantiates
it at the identity `λy. y`, so the program returns the accepted
sample itself.

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

Under `‖µ‖ ≤ 1`, `µ(setT) = 1` and a measurable `f : R → [0,1]`,
the five theorems (all in
`theories/programs/ex_reject_headline.v`, Section RejectHeadline,
with `reject_denot` the denotation at `one1`):

| Side | Headline | Status |
|---|---|---|
| CBV — the division-free master identity: the acceptance mass times the denotation's mass at every measurable U equals the restricted acceptance integral, unconditionally. | `ex_reject_master` — *measurable U → If · fmeas_mu reject_denot U = IUf U* | axiom-free |
| CBV — when acceptance has positive mass, the denotation is exactly the normalised posterior of the prior µ given the soft predicate f. | `ex_reject_is_normalised_posterior` — *0 < If → fmeas_mu reject_denot U = (fine (IUf U) / fine If)%:E* | axiom-free |
| CBV — when the acceptance density already integrates to one, the denotation is the reweighted prior itself, with no normalisation needed. | `ex_reject_posterior_simple` — *If = 1 → fmeas_mu reject_denot U = IUf U* | axiom-free |
| CBV — almost-sure termination: positive acceptance mass makes the sampler's output a probability distribution of total mass one. | `ex_reject_mass_one` — *0 < If → fmeas_mu reject_denot setT = 1* | axiom-free |
| CBV — certain rejection diverges: an identically-zero acceptance density makes the denotation the zero measure. | `ex_reject_zero` — *(∀r, f r = 0) → reject_denot = precone_zero* | axiom-free |

```coq
(* theories/programs/ex_reject_headline.v (Section RejectHeadline) *)
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
```

The proof is a six-step reduction chain. (1) `ex_reject_app_E`: the
outer application of the promoted fixpoint to the identity
continuation collapses — `der ∘ prom` cancels *before* any
continuity argument, leaving `fix_value` applied to the body's
endo-function. (2) `ex_reject_sup_E`: the denotation is the
`cone_sup_ball` of the per-iterate measures
`ν_n := (fix_chain W₀ n)(a₀)` — evaluation at a point commutes with
the Kleene supremum because linhom-cone sups are pointwise.
(3) `ex_reject_iter_S`: the Kleene step is the inner let-if body at
the extended setlike environment. (4) `ex_reject_inner_at_dirac`: at
the environment `γ ⊗ δ_r` the branch dispatch computes — the
scrutinee is `Bernoulli (f r)` (by `bern_lift_dirac`), the THEN
branch returns the accepted sample `δ_r`, the ELSE branch is the
recursive call at the same continuation, which is exactly the
previous iterate `ν_n`. (5) `ex_reject_iter_mass`: the let-at-sample
law `eD_let_sample_mu_E` turns the iterate into a Lebesgue integral
over the prior, giving the affine mass recurrence

```
ν_{n+1}(U) = ∫_U f dµ + (1 − ∫ f dµ) · ν_n(U)
```

(the rejection weight `∫(1−f) dµ = 1 − ∫f dµ` uses `µ(setT) = 1`).
(6) The affine-cascade closed form `affine_iter_cvg` computes the
limit `IUf U / If` of the per-iterate masses, and the sup-mass
bridge `fmeas_kleene_sup_U_E` identifies it with the mass of the
supremum. The master form then multiplies through (graceful at
`If = 0`, where monotonicity forces `IUf U = 0` too), and the
mass-one / zero corollaries specialise `U := setT` and `f ≡ 0`.

```coq
(* theories/programs/ex_reject_headline.v *)
Lemma ex_reject_iter_mass n U (mU : measurable U) :
  fmeas_mu (reject_iter n.+1) U =
  IUf U + ((1 - fine If)%R)%:E * fmeas_mu (reject_iter n) U.
```

The same file also carries the two riders re-proving the lost CBV
mass identities against the clean interpreter:
`ex_geom_cbv_mass_one` (Section GeomRider) and
`ex_almost_loop_cbv_mass_one` / `ex_almost_loop_cbv_zero`
(Section AlmostLoopRider) — see the sections above.

---

## What is **not** formalised

| Item | What it is | Why not yet |
|---|---|---|
| CBV marginal headlines for the QBS trio | The CBV analogues of `ex_random_constant_CBN_marginal_mass`, `ex_random_linear_arith_marginal_at`, `ex_bayes_linear_CBN_mass` restated against the linhom-valued `eD` of `ppl_cbv.v`. (The *recursive* CBV mass identities are no longer a gap: `ex_geom_cbv_mass_one`, `ex_almost_loop_cbv_mass_one` / `ex_almost_loop_cbv_zero` and the rejection-sampling headline are proven in `theories/programs/ex_reject_headline.v`.) | The reduction engine now exists — the let-at-sample integral law `eD_let_sample_int` of `theories/programs/infra/let_sample_law.v` is exactly the lemma these marginals need — so this is a follow-up, not a blocker. |
| CBV distribution refinements for the recursive programs | The CBV analogues of the per-measure CBN refinements `ex_geom_CBN_PMF` and `ex_almost_loop_p_CBN_is_dirac_zero` — pinning the CBV denotation as a *measure* (PMF / Dirac), not just its total mass. | The mass identities reduce to a scalar affine cascade; the distribution identities need the per-set version of the same per-iterate induction (the analogue of `kleene_geom_partial`), which has not been replayed on the CBV side. |
| Mutual recursion at product types (`ne_fix_mr` at `tprod`) | A surface example exercising `ne_fix_mr` at `tprod (tfun A1 B1) (tfun A2 B2)` with a genuine semantics. | The CBV clause at product body types still routes through the provably-zero `Yfix_fun_lin` (`eD_fix_mr_prod_E`, the honest scope record); the repair needs the Seely transport of `fix_comb` — see the PPL tab's gaps table. |
| Option-α unit-type refinement | Replace `tyD_CBN tunit := Stop` by `Bang(FMeas *)` so `ne_score` does not collapse to a constant under CBN. | Needs a parallel `eD_CBN_full_alpha` interpretation and clauses; the option-β refinement of arithmetic (already shipped) is independent and orthogonal. |

These choices are deliberate; each requires substantial
infrastructure outside the current scope and does not block any
*existing* headline result.

---

## How to verify

```sh
make -j

# QBS-style examples
echo "Print Assumptions ex_random_constant_CBN_headline." | \
  rocq top -Q theories Icones -l theories/programs/ppl_cbn_headlines.v
echo "Print Assumptions ex_random_linear_arith_marginal_at." | \
  rocq top -Q theories Icones -l theories/programs/ppl_cbn_arith_eff.v
echo "Print Assumptions ex_random_linear_CBN_marginal_zero." | \
  rocq top -Q theories Icones -l theories/programs/ppl_cbn_headlines.v
echo "Print Assumptions ex_bayes_linear_CBN_headline." | \
  rocq top -Q theories Icones -l theories/programs/ppl_cbn_headlines.v

# Recursive probabilistic examples
echo "Print Assumptions ex_loop_CBN_headline."          | \
  rocq top -Q theories Icones -l theories/programs/ppl_cbn_headlines.v
echo "Print Assumptions ex_geom_CBN_mass_one."          | \
  rocq top -Q theories Icones -l theories/programs/ppl_cbn_geom.v
echo "Print Assumptions ex_geom_CBN_PMF."               | \
  rocq top -Q theories Icones -l theories/programs/ppl_cbn_geom_dist.v
echo "Print Assumptions ex_almost_loop_p_CBN_mass_one_if_pos." | \
  rocq top -Q theories Icones -l theories/programs/ppl_cbn_almost_loop.v
echo "Print Assumptions ex_almost_loop_p_CBN_is_dirac_zero."   | \
  rocq top -Q theories Icones -l theories/programs/ppl_cbn_almost_loop_dist.v

# The rejection-sampling headline + the CBV mass riders
echo "Print Assumptions ex_reject_master."              | \
  rocq top -Q theories Icones -l theories/programs/ex_reject_headline.v
echo "Print Assumptions ex_reject_is_normalised_posterior." | \
  rocq top -Q theories Icones -l theories/programs/ex_reject_headline.v
echo "Print Assumptions ex_geom_cbv_mass_one."          | \
  rocq top -Q theories Icones -l theories/programs/ex_reject_headline.v
echo "Print Assumptions ex_almost_loop_cbv_mass_one."   | \
  rocq top -Q theories Icones -l theories/programs/ex_reject_headline.v
```

Each command reports only `propositional_extensionality`,
`functional_extensionality_dep` and
`constructive_indefinite_description` (the classical-logic axioms of
`mathcomp-analysis`). Per-entry pages embed the precise identifier
name, file, and a GitHub link to the Rocq source.

For the underlying surface inductive and the two interpretations,
see the [PPL tab](../ppl/) — `docs/PPL.md`. For the paper-side
correspondence (§§ 2–9 ↔ Rocq), see the [Paper tab](../paper/) —
`docs/PAPER.md`.
