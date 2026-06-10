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
`PreCone → Cone → MCone → ICone` — on a single carrier type.

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
`Admitted`** anywhere (~66k lines across 76 files). Run [`./verify.sh`](./verify.sh) to
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
syntax (`named_expr`, modelled on Saito–Affeldt APLAS 2023), and gave it **two
parallel interpretations** of the same source language —
**call-by-value (CBV)** via the Eilenberg–Moore category of `!`
(EM route) and **call-by-name (CBN)** via the cartesian closed `SCones`
(the co-Kleisli of `!`, with free recursion from `Yfix`).
On the CBN side, the geometric program carries an axiom-free mass-1
identity `ex_geom_CBN_mass_one`, closed by a Kleene-cascade
`1 − (1/2)ⁿ` argument inside `SCones`. The
**SCones↔ICones-tensor diagonal bilinear stability bridge**
`meas_stable_diag_bilinear_tensor` — the structural unblocker of honest
CBN bilinear arithmetic and of CBV recursion — has also landed
axiom-free.

The CBV interpreter has recently been redesigned around a clean
**linhom-valued, comonoid-primitive** presentation in
`theories/programs/ppl_cbv.v`. Types are sent into `EM(!̃)` as
coalgebras (`tyD`), and a term denotes a *linear* morphism
`U ctxD Γ ⊸ U tyD τ` of the underlying cone. Variable use is handled by
the commutative comonoid `(δ, ε)` that every coalgebra carries
(Cor 20): each branching node copies the context through `δ_Γ`, so
multi-use of a variable is free. The exponential `!̃` appears only at
function boundaries — `ne_lam` wraps a value via the strength `str_Γ`,
`ne_app` extracts it via dereliction `der` — and everywhere else the
interpretation is plain cartesian. The CBV mass identities for the
recursive examples (`ex_loop`, `ex_geom`, `ex_almost_loop`) are
currently pending a Kleene-operator port to this new cone; the prior
Bang-level fixpoint machinery was tied to a deprecated Moggi-monad
presentation and has been removed.

Two pieces of this layer are formalizations we have not seen elsewhere
in Coq / Rocq: the cartesian-η identity `em_pair_mor_proj_id` (Fox 1976
at the icones level), and the diagonal bilinear stability bridge
`meas_stable_diag_bilinear_tensor` at the SCones↔ICones-tensor
junction.

The PPL is built and **axiom-free** (the same three classical `boolp` axioms as
the paper-side results).

## Status

Paper **§2–§9** are formalized: the entire linear-logic model, axiom-free. Beyond the paper,
**two parallel interpretations** of the same surface PPL syntax are built:

- **Call-by-value via `EM(!)`** (`theories/programs/ppl_cbv.v` and infra under
  `programs/infra/`). The interpreter is linhom-valued and comonoid-primitive: types
  go to coalgebras via `tyD`, and a term denotes a linear morphism
  `U ctxD Γ ⊸ U tyD τ`. Non-recursive programs are interpretable axiom-free,
  including the QBS-style headlines (`ex_random_constant`, `ex_random_linear`,
  `ex_bayes_linear_is_weighted`). CBV mass identities for the recursive examples
  (`ex_loop`, `ex_geom`, `ex_almost_loop`) are pending a Kleene-operator port to
  the clean cone; the prior fixpoint machinery was tied to a deprecated
  Moggi-monad presentation and has been removed.
- **Call-by-name via `SCones`** (`theories/programs/ppl_cbn.v` + `ppl_cbn_eff.v` +
  `ppl_cbn_bool.v` + `ppl_cbn_arith.v` + `ppl_cbn_geom.v`). Trunk + effects + boolean cascade
  + `FMeas` arithmetic foundation are all axiom-free. Free recursion at every function type
  via the paper §9.2 `Yfix`. The **CBN mass-1 identity** `ex_geom_CBN_mass_one` lives in
  `theories/programs/ppl_cbn_geom.v`.
- **The SCones↔ICones-tensor diagonal bilinear stability bridge**
  `meas_stable_diag_bilinear_tensor` (`theories/stable/diag_bilinear_tensor.v`,
  axiom-free) — the structural unblocker of CBV recursion and of honest CBN bilinear
  arithmetic via `add_FMeas`/`mul_FMeas`, and of the CBV/CBN soundness comparison.

The full top-down description — what each interpretation does, what works today, what is
missing, and **why** — is in [`docs/PPL.md`](./docs/PPL.md) and on the
[PPL tab](https://llm4rocq.github.io/icones-rocq/auditor/ppl/) of the auditor dashboard.

**Open** (genuinely beyond §9): the **§8** analytic exponential and its category `ACONES`;
the **§9** Eilenberg–Moore *full-subcategory* theorem (needs a Polish / standard-Borel
layer not yet formalized); and the **§10** probabilistic-coherence-space embedding.
**Open on the PPL side**: the **CBV/CBN soundness theorem** (no proof that
`⟦M⟧_CBV` and `⟦M⟧_CBN` agree, which would require commuting `!` with effect-bearing
types); the **refined CBN `add`/`mul` install** on top of `add_FMeas`/`mul_FMeas` via
the bridge above (structural; not yet packaged because the CBN headlines run under
the lightweight option-γ baseline); the **CBV recursion combinator at `ne_fix`** —
a Kleene operator on the clean linhom-valued cone.

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
│                                      meas_stable_diag_bilinear_tensor
├── kernels/   substochastic kernels Skern and the embedding (Thm 6.5)    (§6)
└── programs/  the PPL — surface syntax and two parallel interpretations:
                 ppl.v               shared surface syntax (types, terms,
                                     surface notation) + measure / arith
                                     / Bernoulli helpers shared between
                                     CBV and CBN
                 ppl_cbv.v           CBV interpreter — linhom-valued,
                                     comonoid-primitive; tyD / ctxD / eD;
                                     !̃ only at ne_lam / ne_app
                 ppl_cbn.v           CBN trunk: tyD_CBN, eD_CBN core
                                     (var/lam/app/let/pair/fst/snd),
                                     ne_fix via SCones Yfix (axiom-free)
                 ppl_cbn_*.v         CBN headlines (geom, almost_loop) +
                                     boolean and arithmetic extensions +
                                     geometric / almost-loop distribution
                                     proofs
                 examples.v          surface programs (ex_random_*,
                                     ex_bayes_linear, ex_loop, ex_geom,
                                     ex_almost_loop, ex_geom_body) —
                                     pure syntax, shared between CBV
                                     and CBN
                 infra/              PPL support:
                   bool_cone.v         2-point ICone (paper §4.4
                                       coproduct cone_one ⊕ cone_one)
                   bool_case_hom.v     bool_case as linhom + icones_hom
                   bool_case_scones.v  bool_case SCones-side (CBN bool)
                   cbv_adjunction.v    Linear-Logic / EM-cartesian /
                                       bang-comonoid plumbing — no
                                       Moggi monad; consumed by CBV
                                       and CBN
                   cbn_bernoulli_cascade.v
                                       generic CBN Bernoulli cascade
                                       (sfix_bcascade) used by ex_geom
                                       and ex_almost_loop on the CBN
                                       side
                   geom_dist_infra.v   shared infrastructure for CBN
                                       geometric / almost-loop
                                       distribution proofs
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
