# Icones — Integration in Cones, formalized in Rocq

[![Build](https://img.shields.io/github/actions/workflow/status/LLM4Rocq/icones-rocq/build.yml?branch=main&style=for-the-badge&label=build)](https://github.com/LLM4Rocq/icones-rocq/actions/workflows/build.yml)
[![Blueprint CI](https://img.shields.io/github/actions/workflow/status/LLM4Rocq/icones-rocq/blueprint.yml?branch=main&style=for-the-badge&label=blueprint%20CI)](https://github.com/LLM4Rocq/icones-rocq/actions/workflows/blueprint.yml)
[![Blueprint](https://img.shields.io/badge/blueprint-online-blue?style=for-the-badge)](https://llm4rocq.github.io/icones-rocq/blueprint/)
[![Blueprint PDF](https://img.shields.io/badge/blueprint-PDF-red?style=for-the-badge)](https://llm4rocq.github.io/icones-rocq/blueprint.pdf)
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
  category** (`ICones_smcc`): the tensor `⊗`, the linear hom `⊸`, and all the coherence
  (associator, unitors, braiding; triangle, pentagon, hexagon).
- **The ordinary functional calculus + recursion (Theorem 7.32, §9.2).** The "stable" maps
  between cones form a **cartesian closed category** `SCones` (`SCones_ccc`) — a model of the
  non-linear simply-typed calculus — equipped with **least-fixpoint operators at every type**
  (`lfp`, `Yfix`) for general recursion.
- **The full linear-logic model (Theorem 9.5).** The exponential modality `!`
  (`Bang_comonad`), built from the linear/non-linear adjunction `E ⊣ Der`, makes `ICones` a
  **Seely category** (`ICones_Seely`) — a model of intuitionistic linear logic — via the
  isomorphisms `!A ⊗ !B ≅ !(A & B)` and `1 ≅ !⊤` (whose construction rests on Lemma 9.4,
  `stab_lin_swap`).
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
`Admitted`** anywhere (~52k lines across 53 files). Run [`./verify.sh`](./verify.sh) to
clean-rebuild and `Print Assumptions` the headline results yourself.

This is worth a note because the tensor `⊗`, the exponential `!`, and the Seely isomorphisms
*exist*, in the paper, only abstractly — Ehrhard and Geoffroy obtain them non-constructively
via Freyd's Special Adjoint Functor Theorem, with no formula. The formalization instead
**constructs them concretely** (a wide-intersection / representability argument; see
[`PLAN.md`](./PLAN.md) §13), so the development carries no `Parameter`/`Axiom` interfaces and
nothing is left "assumed."

## Status

Paper **§2–§9** are formalized: the entire linear-logic model, axiom-free.

- **In progress:** a **call-by-value** layer — making the Eilenberg–Moore category of `!`
  cartesian and exhibiting the monoidal adjunction to `ICones`, following Melliès's
  *Categorical Semantics of Linear Logic* §7.4. The foundational pieces (the EM category, the
  cofree adjunction, the comonoid structure) are done; the cartesianness step is under way.
- **Open** (genuinely beyond §9): the **§8** analytic exponential and its category `ACONES`;
  the **§9** Eilenberg–Moore *full-subcategory* theorem (which needs a Polish / standard-Borel
  layer not yet formalized); and the **§10** probabilistic-coherence-space embedding.

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
│              the Seely category, the FMeas !-coalgebra, EM(!)
├── stable/    stable functions, the CCC SCones, fixpoints, Lemma 9.4     (§7, §9.2)
└── kernels/   substochastic kernels Skern and the embedding (Thm 6.5)    (§6)
```

A LaTeX **blueprint** (Patrick Massot's `leanblueprint` style, adapted to Rocq) describes the
mathematics in English alongside its Rocq counterpart, with each statement linked to its
`theories/` declaration and a rendered dependency graph. It is the recommended entry point for
reviewing the formalization without first opening the sources:
**[online](https://llm4rocq.github.io/icones-rocq/blueprint/)** ·
**[PDF](https://llm4rocq.github.io/icones-rocq/blueprint.pdf)** · sources in
[`blueprint/src/`](./blueprint/src/).

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
