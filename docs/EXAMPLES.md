# EXAMPLES.md — End-to-end PPL example programs

Each surface program in `theories/programs/examples.v` is reproduced
here with its headline correctness identities. The programs are
written exclusively in the direct-style `ppl_named` custom entry of
`theories/programs/ppl.v` (brackets `[ … ]` enter the entry; curly
braces `{ x }` escape back to plain Rocq). Every constructor of the
language and every CBN-side clause is exercised somewhere below; the
CBV interpretation of `theories/programs/ppl_cbv.v` accepts the same
surface terms.

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
its denotation to the corresponding distribution.

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

The CBN denotation of mass and marginal lives in
`theories/programs/ppl_cbn_headlines.v`. The CBV interpretation of
the same surface term lives in `theories/programs/ppl_cbv.v` as
`eD ex_random_constant`; the program is non-recursive, so its CBV
denotation lands cleanly through the linhom-valued `eD` (no
recursion machinery needed) — the corresponding marginal identity is
a follow-up that can now be written against the linhom-valued `eD`.

| Side | Headline | Status |
|---|---|---|
| CBN — structural reduction | `ex_random_constant_CBN_headline_struct` | axiom-free |
| CBN — marginal at every `x` | `ex_random_constant_CBN_headline`: `sh_fun (sc_fun ⟦…⟧ g) x = µ` | axiom-free |
| CBN — pointwise marginal mass | `ex_random_constant_CBN_marginal_mass`: `= µ(U)` | axiom-free |

```coq
(* theories/programs/ppl_cbn_headlines.v *)
Lemma ex_random_constant_CBN_headline
    (g : ctxD_CBN (drop_names nil)) (Hg : (cone_norm g <= 1)%R)
    (x : FMeas R_obj) (Hx : (cone_norm x <= 1)%R) :
  sh_fun (sc_fun (eD_CBN_complete ex_random_constant) g) x = mu.
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

The honest bilinear CBN marginal lives in
`theories/programs/ppl_cbn_arith_eff.v`. The CBV interpretation of
the same surface term lives in `theories/programs/ppl_cbv.v`; the
program is non-recursive, so its CBV denotation lands cleanly
through the linhom-valued `eD`, and a linhom-level marginal
identity can be re-derived against the new `eD` as a follow-up — not
blocked by anything in the recursion infrastructure.

| Side | Headline | Status |
|---|---|---|
| CBN — option-β marginal | `ex_random_linear_arith_marginal_at` (via the bilinear bridge) | axiom-free |
| CBN — option-γ degenerate marginal | `ex_random_linear_CBN_marginal_zero` (= `precone_zero`) | axiom-free |

```coq
(* theories/programs/ppl_cbn_arith_eff.v *)
Theorem ex_random_linear_arith_marginal_at
    (arg : FMeas R_obj) (Harg : (cone_norm arg <= 1)%R) :
  sh_fun (sc_fun (eD_CBN_full_arith ex_random_linear) precone_zero) arg
  = add_FMeas (mul_FMeas mu arg) mu.
```

The CBN identity reads "the marginal at any unit-ball argument `arg`
is the honest bilinear lift `add_FMeas (mul_FMeas µ arg) µ`" —
recovering the QBS-paper-flagship "distribution over `λx. m·x + b`
for `m, b ∼ µ`" reading, instantiated at the option-β arithmetic.

### ex_bayes_linear (`ex_bayes_linear`, `ex_bayes_linear_CBN_headline`)

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

The CBN headline of the marginal lives in
`theories/programs/ppl_cbn_headlines.v`. The CBV interpretation of
the same surface term lives in `theories/programs/ppl_cbv.v` as
`eD ex_bayes_linear`; the program is non-recursive, so its CBV
denotation lands cleanly through the linhom-valued `eD` — the
measure-level posterior identity is a follow-up that can now be
written against the new `eD`, not blocked by the recursion
infrastructure.

| Side | Headline | Status |
|---|---|---|
| CBN — marginal identity | `ex_bayes_linear_CBN_headline`: `= µ` (under option-γ; score lands in terminal) | axiom-free |
| CBN — mass corollary | `ex_bayes_linear_CBN_mass`: `= µ(U)` | axiom-free |

```coq
(* theories/programs/ppl_cbn_headlines.v *)
Lemma ex_bayes_linear_CBN_headline
    (g : ctxD_CBN (drop_names nil))
    (Hg : (cone_norm g <= 1)%R) :
  sc_fun (eD_CBN_complete ex_bayes_linear) g = mu.
```

The CBN side under option-γ: since `tyD_CBN tunit = Stop` is the
terminal, `score` collapses to the terminal map and the program's
denotation reduces to the prior `µ` itself. This is the honest
statement at the option-γ baseline; the option-β refinement would
expose the genuine weighted posterior at the SCones level (still
pending — see *What is not formalised* below).

---

## Beyond the paper — Recursive probabilistic examples (productive partial termination)

Recursive probabilistic programs combining `ne_fix` with the
`ne_if` / `ne_bernoulli` boolean cascade to exhibit *productive
partial termination*. Each program ships with the honest mass
identity on the CBN interpretation; the CBV interpretation of the
same surface terms now lands through the `Yfix_fun_lin` Kleene
fixpoint of `theories/programs/infra/em_fix.v` (the value-fixpoint
infrastructure is in place). Specific CBV-side mass identities
mirroring the CBN-side proofs have not yet been written — a
follow-up, not blocked.

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

The CBV interpretation of `ex_loop` in `theories/programs/ppl_cbv.v`
now lands through `Yfix_fun_lin` on the clean `linhom`-cone (see
*The CBV value-fixpoint at function types* on the PPL tab); the
operational mass-zero identity is a follow-up that can now be written
against the new `eD`, not blocked.

| Side | Headline | Status |
|---|---|---|
| CBN — terminal-uniqueness | `ex_loop_CBN_headline`: `= ders (Stop_mor _)` | axiom-free |

```coq
(* theories/programs/ppl_cbn_headlines.v *)
Lemma ex_loop_CBN_headline :
  eD_CBN_complete ex_loop =
  ders (Stop_mor (ctxD_CBN (drop_names nil))).
```

CBN-side trivial: codomain is `Stop Ar`, a singleton, so any two
arrows into it are equal by terminality.

### ex_geom (`ex_geom`, `ex_geom_CBN_mass_one`, `ex_geom_CBN_PMF`)

A geometric counter built via a fair-coin Bernoulli recursion: each
call halts with probability `½` (returning `0`) and otherwise
recurses, adding `1` to the returned real. The program denotes the
geometric distribution with parameter `½` — total mass `1` and PMF
`(1/2)^{k+1}` at every `k`.

```coq
(* theories/programs/examples.v *)
Definition ex_geom : @named_expr R Ar R_obj nil tR' :=
  [ (fix "g" ::: tfun tunit tR' in
       \ "_" ::: tunit =>
         (if Bernoulli { (1 / 2 : R), bernoulli_half_ge0, bernoulli_half_le1 }
          then [| 0%R |]
          else [| 1%R |] + # "g" @ ())) @ () ].
```

The CBV interpretation of `ex_geom` in `theories/programs/ppl_cbv.v`
now lands through `Yfix_fun_lin` on the clean `linhom`-cone. The
CBV-side mass-one identity (the analogue of `ex_geom_CBN_mass_one`)
has not yet been written against the new `Yfix_fun_lin`; the
value-fixpoint machinery is in place, so the proof is a follow-up
rather than blocked. The CBN side ships the full identity.

| Side | Headline | Status |
|---|---|---|
| CBN — total mass identity | `ex_geom_CBN_mass_one`: `mass = 1` | axiom-free |
| CBN — geometric PMF | `ex_geom_CBN_PMF`: `mass({k}) = (1/2)^{k+1}` | axiom-free |
| CBN — structural reduction | `ex_geom_CBN_headline`: outer `Ev ∘ spair (Yfix ∘ curry body) (ders Stop_mor)` | axiom-free |

**Theorem (geometric distribution headline, CBN).** *The CBN
denotation of `ex_geom` matches the geometric distribution with
parameter `½` at every `k ∈ ℕ`: the mass at the singleton `{k}` is
`(1/2)^{k+1}`. In particular the total mass is `1`.*

```coq
(* theories/programs/ppl_cbn_geom.v *)
Theorem ex_geom_CBN_mass_one :
  fmeas_mu ex_geom_CBN_fix [set: ar_carrier Ar R_obj] = 1%:E.

(* theories/programs/ppl_cbn_geom_dist.v *)
Theorem ex_geom_CBN_PMF (k : nat) :
  fmeas_mu (ex_geom_CBN_fix R_carrier_eq R_carrier_meas R_to_carrier_meas)
           [set R_to_carrier R_carrier_eq k%:R]
  = ((1 / 2)%R ^+ k.+1)%R%:E.
```

The CBN side uses the closed-form Kleene cascade `1 − (1/2)^n`,
replayed at the SCones level via the `phi_bcascade` framework of
*The Bernoulli-cascade framework* on the PPL tab; the PMF at the
singleton `{k}` is eventually equal to `(1/2)^{k+1}` and both
identities pass to the limit via `cone_sup_ball` monotone
convergence.

```coq
(* theories/programs/ppl_cbn_headlines.v *)
Lemma ex_geom_CBN_headline :
  eD_CBN_complete ex_geom =
  scones_comp (Ev (Stop Ar) (FMeas R_obj))
    (spair (scones_comp (Yfix (stablehom (Stop Ar) (FMeas R_obj)))
                        (curry (eD_CBN_complete ex_geom_body)))
           (ders (Stop_mor (Stop Ar)))).
```

### ex_almost_loop_p (`ex_almost_loop`, `ex_almost_loop_p_CBN_mass_one_if_pos`, `ex_almost_loop_p_CBN_mass_zero_if_zero`, `ex_almost_loop_p_CBN_is_dirac_zero`, `ex_almost_loop_p_CBN_is_zero_if_zero`)

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

The CBV interpretation in `theories/programs/ppl_cbv.v` now lands
through `Yfix_fun_lin` on the clean `linhom`-cone; the operational
mass dichotomy on the CBV side has not yet been written against the
new `Yfix_fun_lin`, but the value-fixpoint machinery is in place — a
follow-up rather than a blocker.

| Side | Headline | Status |
|---|---|---|
| CBN — mass = 1 if `p > 0` | `ex_almost_loop_p_CBN_mass_one_if_pos` | axiom-free |
| CBN — mass = 0 if `p = 0` | `ex_almost_loop_p_CBN_mass_zero_if_zero` | axiom-free |
| CBN — fixpoint is Dirac at 0 (`p > 0`) | `ex_almost_loop_p_CBN_is_dirac_zero` | axiom-free |
| CBN — fixpoint is zero (`p = 0`) | `ex_almost_loop_p_CBN_is_zero_if_zero` | axiom-free |
| CBN — terminal-uniqueness wrapper | `ex_almost_loop_CBN_headline`: `= ders (Stop_mor _)` | axiom-free |

```coq
(* theories/programs/ppl_cbn_almost_loop.v *)
Theorem ex_almost_loop_p_CBN_mass_one_if_pos :
  (0 < p)%R ->
  fmeas_mu ex_almost_loop_p_CBN_fix [set: ar_carrier Ar R_obj] = 1%:E.

Theorem ex_almost_loop_p_CBN_mass_zero_if_zero :
  p = 0%R ->
  fmeas_mu ex_almost_loop_p_CBN_fix [set: ar_carrier Ar R_obj] = 0%E.
```

The CBN side recovers the closed form `1 − (1−p)^n` (geometric
series in `1 − p`) via the `phi_bcascade` framework instantiated at
`halt := δ_0`, `cont_op := scones_id`; for `p > 0` it converges to
`1`, for `p = 0` it is identically `0`.

```coq
(* theories/programs/ppl_cbn_almost_loop_dist.v *)
Theorem ex_almost_loop_p_CBN_is_dirac_zero :
  (0 < p)%R ->
  ex_almost_loop_p_CBN_fix R_carrier_eq p Hp_ge0 Hp_le1 = halt_alp_.

Theorem ex_almost_loop_p_CBN_is_zero_if_zero :
  p = 0%R ->
  ex_almost_loop_p_CBN_fix R_carrier_eq p Hp_ge0 Hp_le1 =
  (precone_zero : FMeas R_obj).
```

The "is" statements are stronger than the mass identities: the
fixpoint *is* the Dirac at `0` (resp. `precone_zero`) — not just an
arbitrary measure with the right mass. Proved by extensional
measure equality via the kleene-cascade convergence at every
measurable set.

---

## What is **not** formalised

| Item | What it is | Why not yet |
|---|---|---|
| CBV-side mass identities and distribution headlines for the example programs | The CBV analogues of `ex_geom_arr_mass_one`, `ex_loop_CBN_headline`, `ex_almost_loop_p_CBN_mass_one_if_pos` / `_mass_zero_if_zero`, `ex_random_constant_*_marginal_*`, `ex_random_linear_*_marginal_*`, `ex_bayes_linear_*_headline` against the new linhom-valued `eD` of `ppl_cbv.v`. | The surface programs are defined and their interpretations land cleanly (recursive ones through `Yfix_fun_lin`, non-recursive ones directly through the linhom-valued `eD`), but the example-specific structural reduction lemmas and measure-level identities have not yet been written against the new `eD`. Not blocked — follow-up work. |
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
