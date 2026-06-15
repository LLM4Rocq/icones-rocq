# Icones — Integration in Cones, formalized in Rocq

[![Build](https://img.shields.io/github/actions/workflow/status/LLM4Rocq/icones-rocq/build.yml?branch=main&style=for-the-badge&label=build)](https://github.com/LLM4Rocq/icones-rocq/actions/workflows/build.yml)
[![Blueprint CI](https://img.shields.io/github/actions/workflow/status/LLM4Rocq/icones-rocq/blueprint.yml?branch=main&style=for-the-badge&label=blueprint%20CI)](https://github.com/LLM4Rocq/icones-rocq/actions/workflows/blueprint.yml)
[![Blueprint](https://img.shields.io/badge/blueprint-online-blue?style=for-the-badge)](https://llm4rocq.github.io/icones-rocq/blueprint/)
[![Blueprint PDF](https://img.shields.io/badge/blueprint-PDF-red?style=for-the-badge)](https://llm4rocq.github.io/icones-rocq/blueprint.pdf)
[![Auditor — Paper](https://img.shields.io/badge/auditor-paper-green?style=for-the-badge)](https://llm4rocq.github.io/icones-rocq/auditor/paper/)
[![Auditor — PPL](https://img.shields.io/badge/auditor-PPL-green?style=for-the-badge)](https://llm4rocq.github.io/icones-rocq/auditor/ppl/)
[![Rocq 9.1.1](https://img.shields.io/badge/rocq-9.1.1-orange?style=for-the-badge)](https://rocq-prover.org/)
[![License](https://img.shields.io/badge/license-CC--BY--4.0-blue.svg?style=for-the-badge)](https://creativecommons.org/licenses/by/4.0/)

A machine-checked Rocq / mathcomp-analysis formalization of *Integration in Cones*
by Thomas Ehrhard and Guillaume Geoffroy
([LMCS 21(1:1), 2025](https://doi.org/10.46298/LMCS-21(1:1)2025);
[arXiv:2212.02371](https://arxiv.org/abs/2212.02371)).

## What this is

The paper builds a **denotational semantics for higher-order probabilistic programs over
continuous data** — programs that can `sample` from distributions (over the real line, not
just coin flips), reweight executions (`score`), use functions as first-class values, and
recurse — and shows the resulting model is *also* a **model of linear logic**. This
repository reconstructs that model in Rocq, fully machine-checked, on top of the
`mathcomp-analysis` measure-theory library.

The guiding idea (due to Kozen) is that **a probabilistic program is a distribution
transformer**: a type denotes a *space of generalized (sub)distributions*, and a program
denotes a structure-preserving map between such spaces. Three things have to be made precise,
and each names a layer of the model:

- those spaces of distributions are **cones**;
- the meaning of sampling and expectation is **integration**;
- the way programs compose — in particular, *using a value once* versus *copying it* — is
  organized by **linear logic** (the tensor `⊗`, the linear function space `⊸`, and the `!`
  "may-copy" modality).

That last point is worth a sentence, because it drives half the development. Using an argument
twice is genuinely *not* the same as using two independent copies: `x + x` pushes a
distribution forward along `r ↦ 2r`, while `y + z` on independent inputs *convolves* the two
distributions. Linear logic is exactly the discipline that distinguishes "use once" from "may
copy" — and it is what lets one read **call-by-name and call-by-value off the same model**.

## The foundation: cones, measurable cones, integrable cones

The model is assembled in three layers, each adding *just enough* structure to integrate:

| The need | The structure | What it is |
|---|---|---|
| Outcomes can be **blended with probabilities** (a weighted mix) and have a **size** (total mass); recursion needs **limits**. | **cone** | a space whose elements you can add and scale by `r ≥ 0` (never subtract), with a norm and ω-completeness |
| Sampling **continuous** data forces **integration**, which only makes sense against a notion of **measurability**. | **measurable cone** | a cone that additionally knows *which maps to and from it count as measurable* |
| The meaning of `sample` / expectation **is** an integral, which must **exist** and **land back in the space**. | **integrable cone** | a measurable cone in which cone-valued integrals always exist (a Pettis integral) |

`ICones` is the category of integrable cones together with the structure-preserving maps
between them (linear, continuous, integral-preserving). In Rocq this is a four-level
[Hierarchy Builder](https://github.com/math-comp/hierarchy-builder) tower —
`Precone → Cone → MCone → ICone` — on a single carrier type.

## Main results

All of the following are formalized and **axiom-free** (see [below](#fully-axiom-free)). Names
in `monospace` are the corresponding Rocq declarations.

- **Conservativity — the model is the right one (Theorem 6.5).** The category `Skern` of
  substochastic kernels — the *standard* first-order probabilistic model — embeds **fully and
  faithfully** into `ICones` (`Skern_to_ICones_fully_faithful`). The cone model genuinely
  *extends* the established semantics to higher order; it does not quietly change it.
- **Multiplicative linear logic (Theorem 5.15).** `ICones` is a **symmetric monoidal closed
  category** (`ICones_smcc`): the tensor `⊗`, the linear hom `⊸`, the bifunctor action and
  its identity law, the structural isomorphisms (associator, unitors, braiding) and the
  coherence laws (triangle, pentagon, hexagon, braiding involution), and the closedness iso.
  (The bifunctor's composition law and the naturality of the structural isos are proved as
  standalone lemmas, not packed into the `ICones_SMCC` record.)
- **The ordinary functional calculus + recursion (Theorem 7.32, §9.2).** The "stable" maps
  between cones form a **cartesian closed category** `SCones` (`SCones_ccc`) — a model of the
  non-linear simply-typed calculus — equipped with **least-fixpoint operators at every type**
  (`lfp`, `Yfix`) for general recursion.
- **The full linear-logic model (Theorem 9.5).** The exponential modality `!`
  (`Bang_comonad`), built from the linear/non-linear adjunction `E ⊣ Der`, makes `ICones` a
  **Seely category** (`ICones_Seely`) — a model of intuitionistic linear logic — via the
  isomorphisms `!A ⊗ !B ≅ !(A & B)` and `1 ≅ !⊤` (whose construction rests on Lemma 9.4,
  `stab_lin_swap`). The adjoint `E` exists because the dereliction `Der` preserves all
  limits — equalisers (`der_preserves_limits`) and products (`der_preserves_prod_proj`) —
  feeding the same SAFT argument as the tensor.
- **Sampling as a data type (Theorem 9.7).** Each measurable space `X` makes the cone of
  measures `FMeas(X)` a `!`-**coalgebra** (`FMeas_coalgebra`), and `X ↦ FMeas(X)` is a functor
  into the Eilenberg–Moore category of `!`. This is the structure that interprets sampling as
  a value — and the entry point to a call-by-value reading.

| Paper | Result | Rocq |
|---|---|---|
| §2–§4 | Cones, measurable & integrable cones; Pettis integral; Fubini; `ICones` complete | `ICone`, `icone_integral`, … |
| §5 | Internal hom `⊸`, tensor `⊗`, SMCC (Thm 5.15) | `ICones_smcc` |
| §6 | Kernels embed fully faithfully (Thm 6.5) | `Skern_to_ICones_fully_faithful` |
| §7 | Stable functions; cartesian closed `SCones` (Thm 7.32) | `SCones_ccc` |
| §9.2 | Least fixpoints / `Y` at every type | `lfp`, `Yfix` |
| §9 | `!` comonad; Seely category (Thm 9.5); `FMeas` coalgebra (Thm 9.7) | `Bang_comonad`, `ICones_Seely`, `FMeas_coalgebra` |

### Fully axiom-free

Every result above depends only on the three standard classical-logic axioms inherited from
`mathcomp-analysis` — `propositional_extensionality`, `functional_extensionality_dep`,
`constructive_indefinite_description` — with **no project-specific axioms** and **no
`Admitted`** anywhere (~75k lines across 75 files). Run [`./verify.sh`](./verify.sh) to
clean-rebuild and `Print Assumptions` the headline results yourself.

This is worth a note. The tensor `⊗`, the exponential `!`, and the Seely isomorphisms are
obtained — in both the paper and this formalization — via **Freyd's Special Adjoint Functor
Theorem** (SAFT): the functor `C ⊸ −` preserves limits, and `ICones` is complete,
well-powered, and has a coseparator, so it has a left adjoint. The paper invokes SAFT without
exhibiting a carrier (Remark 5.1 gives no explicit formula for `⊗`). The formalization follows
the **same route**, but — since Coq cannot cite SAFT as a black box — it **mechanizes the SAFT
argument itself**: it proves `ICones` well-powered and runs Freyd's construction, building the
adjoint as a wide intersection of subobjects of a coseparator power
(`theories/icones/representable.v`, `theories/homs/tensor_construct.v`). So these are the same
SAFT-given objects as in the paper, with their construction fully spelled out — which is what
lets the development carry no `Parameter`/`Axiom` interfaces and leave nothing "assumed."

## Beyond the paper: a probabilistic programming language

The Ehrhard–Geoffroy paper stops at the §9 LNL / Seely model; a probabilistic
**programming language** built on top of it is explicitly stated future work
(the conclusion: *"In future work we will explain how this model can be used for
interpreting call-by-value or even call-by-push-value … languages …"*). This
repository takes a substantial step in that direction. **A complete top-down
description of the PPL — what it is, what works today, what is missing and why
— is in [docs/PPL.md](./docs/PPL.md)** and on the
[PPL tab](https://llm4rocq.github.io/icones-rocq/auditor/ppl/) of the auditor
dashboard.

A one-paragraph summary: we built a multi-variable named-variable surface
syntax (`named_expr`, modelled on Saito–Affeldt APLAS 2023) and a
**call-by-value (CBV)** interpretation of it via the Eilenberg–Moore
category of `!` (a call-by-name interpretation of the same surface
syntax, via the cartesian closed `SCones` — including its
`ex_geom_CBN_mass_one` headline — is preserved on the
[`cbn-track`](../../tree/cbn-track) branch; `main` is CBV-only).
The headline result of the PPL layer: **rejection sampling computes
the conditioned model's normalised distribution** — `condition M f`
(`ex_condition_comb`) is the Pyro-style soft conditioning operator
and `reject M f` (`ex_reject_comb`) the executable sampler, both
higher-order combinators of type `(ta → tR) → (ta → tR)` over an
arbitrary probabilistic model `m : ta → tR` (a function value, itself
free to contain samples, scores and recursion); writing `ν_M` for the
model's output sub-distribution, the conditioning law gives
`⟦condition m a⟧(U) = ∫_U f dν_M` (`condition_model_E` /
`condition_E`) and the equivalence
`Z · ⟦reject_prog⟧ U = ⟦condition_prog⟧ U` with
`Z := 1 − ν_M(setT) + ∫ f dν_M` holds unconditionally
(`reject_normalises_condition`; division form
`reject_prog_computes_condition`; at probability models the
normaliser is the model evidence `⟦condition_prog⟧(setT)`,
`reject_normalises_condition_prob`). Underneath sits the
sub-probability-honest master identity
`(1 − m₀ + If) · ν(U) = ∫_U f dν_M` (`reject_model_master`,
`m₀ := ν_M(setT)`, `If := ∫ f dν_M`), hence
`ν(U) = (∫_U f dν_M)/(1 − m₀ + If)` under loop progress
(`reject_model_is_normalised`), with almost-sure termination for
probability models (`reject_model_mass_one`) and honest divergence at
`f ≡ 0` (`reject_model_zero`) — all in
`theories/programs/ex_reject_model.v`, axiom-free. The Bayesian
linear regression below is *defined as* iterated conditioning
(the named anchor `ex_bayes_linear_is_iter_condition` is now
definitional). The original
hard-coded sampler is the simplest instance: at the model
`λ_. sample µ`, the combinator denotes **the same measure** as
`ex_reject` (`ex_reject_comb_sampler_E`), whose direct theorems
(`ex_reject_master`, `ex_reject_is_normalised_posterior`,
`ex_reject_mass_one`, `ex_reject_zero`) remain in
`theories/programs/ex_reject_headline.v`, axiom-free. The same file proves the **CBV distribution identities** for the
geometric and almost-loop programs: the geometric counter denotes the
geometric law — the geometric PMF `(1/2)^(k+1)` at every embedded
natural `k` (`ex_geom_cbv_distribution`, `ex_geom_cbv_pmf`), with the
total-mass-1 specialisation `ex_geom_cbv_mass_one`; the almost-loop
denotation is the unit Dirac `one1` for `p > 0`
(`ex_almost_loop_cbv_dirac`, strengthening
`ex_almost_loop_cbv_mass_one`) and the zero point at `p = 0`
(`ex_almost_loop_cbv_zero`), and
`theories/programs/infra/cbv_marginals.v` proves the **CBV marginal
headlines** of the basic sampling/scoring examples — the unnormalised
score posterior `ex_score_posterior_cbv_E`, paired exactly with the
rejection sampler by `ex_reject_normalises_score`, the marginal
identities `ex_random_constant_cbv_marginal` /
`ex_random_linear_cbv_marginal`, and the **model evidence of a
higher-order Bayesian linear regression**
(`ex_bayes_linear_cbv_evidence`: the program samples a random affine
function once, conditions it on each observation in turn
(`iter_condition`), and returns the posterior over functions — its total
mass is the iterated evidence integral, for a general observation
list).

The CBV interpreter is a clean **linhom-valued, comonoid-primitive**
presentation in `theories/programs/ppl_cbv.v`. Types are sent into
`EM(!̃)` as coalgebras (`tyD`), and a term denotes a *linear* morphism
`U ctxD Γ ⊸ U tyD τ` of the underlying cone. Variable use is handled by
the commutative comonoid `(δ, ε)` that every coalgebra carries
(Cor 20): each branching node copies the context through `δ_Γ`, so
multi-use of a variable is free. The exponential `!̃` appears only at
function boundaries — `ne_lam` wraps a value by currying and promoting
via the U ⊣ !̃ adjunction `adj_psi`, `ne_app` extracts it via
dereliction `der` — and everywhere else the
interpretation is plain cartesian. Recursion (`ne_fix`, and `ne_fix_mr`
at *every* free body type) is the **seeded value-fixpoint combinator**
`fix_comb : EM(!̃(!A⊸!A), !̃A)` of
`theories/programs/infra/em_fix_value.v`: the supremum of the
interleaved Kleene chain `x₀ = 0`, `x_{n+1} = der (F (x_n!))`, seeded
at the genuine bottom of the value type (the diverging-function value
`0!`, not the cone-zero of the wrapped hom) and packaged as a coalgebra
morphism via `lin` + `adj_psi`. At products of free types
(mutual recursion, witness `ex_even_odd_pair`) the combinator is
conjugated by the EM-level Seely-2 decomposition
`EM_prod (!̃X) (!̃Y) ≅ !̃(X & Y)` of
`theories/programs/infra/em_fix_mr.v` (`seely2_em_iso`,
`fix_comb_iso`). The naive zero-seeded iteration of
`theories/programs/infra/em_fix.v`'s linear Kleene step is *provably
the zero linhom* (`Phi_fun_lfp_eq0` in
`theories/programs/infra/em_fix_value.v`); the operator it used to
define was removed after that proof. The `tbool` clause uses the §9.7-style coalgebra
structure on `bool_cone_car` (`bool_cone_coalg` in
`theories/programs/infra/bool_cone_coalg.v`), giving the shared-sample
diagonal-pushforward semantics for programs like
`let x = Bernoulli(p) in (x, x)` — pinned by the regression anchors of
`theories/programs/infra/cbv_anchors.v`
(`let_bernoulli_pair_diag` vs the independent-product contrast
`pair_bernoulli_indep`). The semantic engine behind the headline is the
**let-at-sample Pettis integral law** `eD_let_sample_int`
(`theories/programs/infra/let_sample_law.v`):
`⟦let x = sample µ in K⟧(γ) = ∫ ⟦K⟧(γ ⊗ δ_r) µ(dr)` at arbitrary `γ`.
The surface also has **runtime-parameter distributions**
`Gaussian( e1 , e2 )` / `Uniform( e1 , e2 )` (`ne_gaussian` /
`ne_uniform`) over a generic probability-kernel layer
(`pkernel` / `kernel_lift` / `kernel_lift2` in
`theories/programs/distributions.v`), enabling hierarchical models —
`let s = Gaussian(0,1) in Gaussian(s,1)` (`ex_gaussian_walk`) is
proved a probability of mass `1` with the hierarchy integral as its
measure (`ex_gaussian_walk_E` / `ex_gaussian_walk_mass` in
`theories/programs/infra/kernel_anchors.v`).

Two pieces of this layer are formalizations we have not seen elsewhere
in Coq / Rocq: the cartesian-η identity `em_pair_mor_proj_id` (Fox 1976
at the icones level), and the diagonal bilinear stability bridge
`meas_stable_diag_bilinear_tensor` at the SCones↔ICones-tensor
junction.

The PPL is built and **axiom-free** (the same three classical `boolp` axioms as
the paper-side results).

## Status

Paper **§2–§9** are formalized: the entire linear-logic model, axiom-free. Beyond the paper,
the **call-by-value interpretation** of the surface PPL syntax is built (the call-by-name
interpretation is preserved on the [`cbn-track`](../../tree/cbn-track) branch):

- **Call-by-value via `EM(!)`** (`theories/programs/ppl_cbv.v` and infra under
  `programs/infra/`). The interpreter is linhom-valued and comonoid-primitive: types
  go to coalgebras via `tyD`, and a term denotes a linear morphism
  `U ctxD Γ ⊸ U tyD τ`. Recursion is the seeded value-fixpoint combinator
  `fix_comb` of `theories/programs/infra/em_fix_value.v` (the interleaved
  Kleene chain `x_{n+1} = der (F (x_n!))` seeded at the diverging value;
  the naive zero-seeded iteration is provably the zero linhom,
  `Phi_fun_lfp_eq0`), with the recursion-unfolding equations in
  `theories/programs/infra/cbv_fix_unfold.v`. **The CBV headline —
  conditioning and rejection are equivalent**: the Pyro-style
  `condition` operator denotes the likelihood-reweighted model output
  `∫_U f dν_M` (`condition_model_E` / `condition_E`), and rejection
  sampling over ANY model computes exactly its normalisation —
  `Z · ⟦reject_prog⟧ U = ⟦condition_prog⟧ U` with
  `Z := 1 − ν_M(setT) + ∫ f dν_M` (`reject_normalises_condition`, on
  top of `reject_model_master` / `reject_model_is_normalised`, all in
  `theories/programs/ex_reject_model.v`; hard-coded instance
  `ex_reject_master` / `ex_reject_is_normalised_posterior` in
  `theories/programs/ex_reject_headline.v` and the instance bridge
  `ex_reject_comb_sampler_E`), via the let-at-sample Pettis
  integral law `eD_let_sample_int` and its arbitrary-bound-computation
  generalisation `eD_let_int` (`theories/programs/infra/let_sample_law.v`),
  the affine-cascade closed form + sup-mass bridge
  (`theories/programs/infra/affine_cascade.v`), and the setlike-point
  regression anchors (`theories/programs/infra/cbv_anchors.v`). The same
  file carries the CBV mass identities `ex_geom_cbv_mass_one` and
  `ex_almost_loop_cbv_mass_one` / `ex_almost_loop_cbv_zero`. The `tbool`
  clause uses the §9.7-style coalgebra `bool_cone_coalg` on
  `bool_cone_car` (in `theories/programs/infra/bool_cone_coalg.v`) for
  shared-sample diagonal semantics.
- **The readable surface layer** (`theories/programs/ppl.v` /
  `theories/programs/examples.v`): the constant coin `Bernoulli [| p |]`
  over a real literal (its `[0,1]` bounds discharged by `lra`), the
  value coin `Bern e` and the score `Sc e` over the probability type
  `tProb` (the `[0,1]` object of a `probObj` bundle, so the bound is
  carried by the type), the `tProb`-producing primitives `Sigmoid e` /
  `Gausslik { s , y } e` / `Gt0 e` / `ToProb { φ } e` / `Const pr e`,
  the Bayesian-conditioning operator
  `observe Gaussian { s , y } e ≡ Sc (Gausslik { s , y } e)` (scoring
  by the envelope-normalised Gaussian likelihood `gauss_obs_density s y`),
  measurable function application `Meas { f , Hf } e` (the `ne_meas`
  pushforward constructor), bundled distributions `sample m` over `pmeas`
  with named `gaussian` / `uniform` transported from mathcomp-analysis,
  the comparison coin `e1 > e2`, OCaml-style `let rec f x := M in K`
  sugar, and the `Condition { d } M` form — demoed end to end by
  `ex_surface_demo` / `ex_surface_walk`.
- **The CBV marginals** (`theories/programs/infra/cbv_marginals.v`,
  axiom-free): the non-recursive basic sampling/scoring examples carry
  closed-form CBV identities — `ex_score_posterior_cbv_E` (the denotation of
  the score program is the unnormalised posterior `∫_U f dµ`),
  `ex_random_constant_cbv_marginal` (the sampled constant function's marginal
  at every probability test point is the prior),
  `ex_random_linear_cbv_marginal` (the random-affine marginal at Dirac test
  points is the iterated-integral pushforward), and
  `ex_bayes_linear_cbv_evidence` (the total mass of the
  posterior-over-functions of the Bayesian linear regression is the model
  evidence, for a general observation list). The pairing theorem
  `ex_reject_normalises_score` connects the score program and the rejection
  sampler exactly: `(∫ f dµ) · ν_reject(U) = ν_score(U)` at a probability prior.
- **The SCones↔ICones-tensor diagonal bilinear stability bridge**
  `meas_stable_diag_bilinear_tensor` (`theories/stable/diag_bilinear_tensor.v`,
  axiom-free) — its `linhom_to_stablehom` lift is the stable ingredient of the
  CBV value-fixpoint (`fix_value`).

The full top-down description — what the interpretation does, what works today, what is
missing, and **why** — is in [`docs/PPL.md`](./docs/PPL.md) and on the
[PPL tab](https://llm4rocq.github.io/icones-rocq/auditor/ppl/) of the auditor dashboard.

**Open** (genuinely beyond §9): the **§8** analytic exponential and its category `ACONES`;
the **§9** Eilenberg–Moore *full-subcategory* theorem (needs a Polish / standard-Borel
layer not yet formalized); and the **§10** probabilistic-coherence-space embedding.
**On the PPL side**: the recursive examples are now pinned as measures (the geometric
PMF, the unit Dirac, and the mutual-recursion divergence identity), and the recursion
equation is proven at the value level (`fix_value_unfold`, morphism-free) and at every
reachable context point (`eD_fix_unfold`); the morphism-level form at non-setlike,
unreachable points is intentionally out of scope — see [`docs/PPL.md`](./docs/PPL.md).

[`PLAN.md`](./PLAN.md) has the full roadmap and design notes.

## Repository layout

```
theories/
├── prelude/   classical-logic, ereal/nonneg helpers, the ω-cpo
├── cones/     precones → cones, the category Cones                       (§2)
├── mcones/    measurable cones, the measure cone FMeas, Path, MCones     (§3)
├── icones/    Pettis integral, integrable cones, Fubini, completeness,   (§4)
│              well-poweredness + the representability machinery
├── homs/      internal hom ⊸, tensor ⊗ + SMCC, the ! comonad + E⊣Der,    (§5, §9)
│              the Seely category, the FMeas !-coalgebra;
│              the call-by-value model structure (beyond the paper):       (CBV)
│                em_cat.v            EM(!) + the cofree adjunction U ⊣ !̃
│                em_seely_comonoid.v the Seely comonoid d/e on !A (LC2–4)
│                em_cartesian.v      full EM(!) cartesian via ⊗ (Cor 20)
│                fmeas_lax.v         FMeas is lax symmetric monoidal
│                                    (µ ⊗ ν ↦ µ × ν as an icones_hom)
├── stable/    stable functions, the CCC SCones, fixpoints, Lemma 9.4     (§7, §9.2)
│              diag_bilinear_tensor.v  the SCones↔ICones-tensor diagonal     (PPL)
│                                      bilinear stability bridge
│                                      meas_stable_diag_bilinear_tensor;
│                                      its linhom_to_stablehom lift feeds
│                                      the CBV value-fixpoint
├── kernels/   substochastic kernels Skern and the embedding (Thm 6.5)    (§6)
└── programs/  the PPL — surface syntax and its CBV interpretation
               (the CBN interpretation lives on branch cbn-track):
                 ppl.v               surface syntax (types, terms,
                                     surface notation) + measure / arith
                                     / Bernoulli helpers
                 ppl_cbv.v           CBV interpreter — linhom-valued,
                                     comonoid-primitive; tyD / ctxD / eD;
                                     !̃ only at ne_lam / ne_app
                 examples.v          surface programs (ex_random_*,
                                     ex_score_posterior, ex_bayes_linear,
                                     ex_loop, ex_geom, ex_almost_loop,
                                     ex_even_odd_pair, ex_reject,
                                     ex_reject_comb, ex_condition_comb +
                                     Condition surface form, condition_at /
                                     iter_condition — ex_bayes_linear IS
                                     the iterated conditioning,
                                     gaussian / uniform, ex_surface_demo) —
                                     pure syntax + the eD-applied CBV
                                     denotations (ex_*_cbv)
                 ex_reject_headline.v
                                     the original CBV headline: rejection
                                     sampling denotes the normalised
                                     posterior (ex_reject_master,
                                     ex_reject_is_normalised_posterior,
                                     ex_reject_mass_one, ex_reject_zero)
                                     + the CBV mass riders
                                     ex_geom_cbv_mass_one,
                                     ex_almost_loop_cbv_mass_one/_zero
                 ex_reject_model.v   THE CBV capstone: the rejection
                                     COMBINATOR over any model
                                     (reject_model_master,
                                     reject_model_is_normalised), the
                                     condition combinator's law
                                     (condition_model_E, condition_E)
                                     and the equivalence
                                     (reject_normalises_condition +
                                     division / probability forms)
                 infra/              PPL support:
                   bool_cone.v         2-point ICone (paper §4.4
                                       coproduct cone_one ⊕ cone_one)
                   bool_cone_coalg.v   §9.7-style !-coalgebra structure
                                       on bool_cone_car — diagonal
                                       pushforward, used for the
                                       CBV tbool shared-sample semantics
                   bool_case_hom.v     bool_case as linhom + icones_hom
                   cbv_adjunction.v    Linear-Logic / EM-cartesian /
                                       bang-comonoid plumbing — no
                                       Moggi monad
                   em_fix.v            the naive linear Kleene step
                                       Phi_fun + the linhom LFP core
                                       (its zero-seeded operator was
                                       removed after the degeneracy
                                       proof Phi_fun_lfp_eq0)
                   em_fix_value.v      fix_comb — the seeded CBV
                                       value-fixpoint combinator
                                       (interleaved Kleene chain,
                                       fix_prom_E, fix_coalg_simpl,
                                       Phi_fun_lfp_eq0); ne_fix
                                       resolves here
                   em_fix_mr.v         the Seely-transported fixpoint
                                       for mutual recursion: coalg_iso,
                                       seely2_em_iso (EM_prod (!̃X) (!̃Y)
                                       ≅ !̃(X & Y)), fix_comb_iso —
                                       ne_fix_mr at products of free
                                       types resolves here
                   cbv_fix_unfold.v    the recursion-unfolding
                                       equations of the wired ne_fix
                                       clause (eD_fix_at_setlike,
                                       eD_fix_unfold) + the ne_fix_mr
                                       twins at tfun and tprod
                   let_sample_law.v    the let-at-sample Pettis
                                       integral law eD_let_sample_int
                                       and its measure-on-U form
                   affine_cascade.v    affine Kleene cascades: closed
                                       form, limit, and the FMeas
                                       sup-mass bridge
                   cbv_anchors.v       semantic regression anchors —
                                       setlike-point kit, shared-sample
                                       diagonal vs independent-product
                                       contrast, eD_beta, if-pins
                   cbv_marginals.v     the CBV marginal headlines of
                                       the basic sampling/scoring
                                       examples — the unnormalised
                                       score posterior
                                       (ex_score_posterior_cbv_E),
                                       the score/rejection pairing
                                       (ex_reject_normalises_score),
                                       the marginals
                                       ex_random_constant_cbv_marginal /
                                       ex_random_linear_cbv_marginal,
                                       and the Bayesian-regression
                                       model evidence
                                       (ex_bayes_linear_cbv_evidence)
```

Two parallel entry points for reviewing the formalization without first opening the
sources:

- A LaTeX **blueprint** (Patrick Massot's `leanblueprint` style, adapted to Rocq) describing
  the mathematics in English alongside its Rocq counterpart, with each statement linked to
  its `theories/` declaration and a rendered dependency graph:
  **[online](https://llm4rocq.github.io/icones-rocq/blueprint/)** ·
  **[PDF](https://llm4rocq.github.io/icones-rocq/blueprint.pdf)** · sources in
  [`blueprint/src/`](./blueprint/src/).
- An interactive **auditor dashboard** with two tabs:
  the **[Paper tab](https://llm4rocq.github.io/icones-rocq/auditor/paper/)**
  (paper-to-Rocq correspondence for §§ 2–9, plus the paper-cited meta-theorems we
  mechanised) and the **[PPL tab](https://llm4rocq.github.io/icones-rocq/auditor/ppl/)**
  (top-down description of the PPL: what works, what is missing, why). Searchable,
  deep-linkable per entry, with per-entry links to coqdoc and GitHub. Sources in
  [`docs/PAPER.md`](./docs/PAPER.md) + [`docs/PPL.md`](./docs/PPL.md).

## Building

Requires Rocq 9.1+ (tested on 9.1.1), `rocq-mathcomp` 2.5+, `rocq-mathcomp-analysis` 1.16+,
`rocq-hierarchy-builder` 1.10+, `rocq-elpi` 3.3+.

```bash
opam install rocq-mathcomp-analysis rocq-hierarchy-builder
make
./verify.sh        # clean rebuild + Print Assumptions on the headline results
```

Building the blueprint locally:

```bash
pip install -r blueprint/requirements.txt
sudo apt install graphviz libgraphviz-dev texlive-xetex texlive-latex-extra \
                 texlive-fonts-extra latexmk
rocqblueprint web      # HTML → blueprint/web/
rocqblueprint pdf      # PDF  → blueprint/print/print.pdf
```

CI ([`build.yml`](./.github/workflows/build.yml)) runs `make` and the axiom check on every push
and PR; [`blueprint.yml`](./.github/workflows/blueprint.yml) builds the blueprint and publishes
it to GitHub Pages from `main`.

## Paper and license

The reference is *Integration in Cones* by Thomas Ehrhard and Guillaume Geoffroy, open access
on [arXiv](https://arxiv.org/abs/2212.02371) and in
[LMCS 21(1:1), 2025](https://doi.org/10.46298/LMCS-21(1:1)2025). Rocq proofs annotate the
paper section and lemma they correspond to; the PDF is not bundled here.

Licensed [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/) — the same licence as the
paper (see [`LICENSE`](./LICENSE)). When reusing this work, please cite both the paper and
this formalization.
