# Icones — Integration in Cones, formalized in Rocq

[![Build](https://img.shields.io/github/actions/workflow/status/LLM4Rocq/icones-rocq/build.yml?branch=main&style=for-the-badge&label=build)](https://github.com/LLM4Rocq/icones-rocq/actions/workflows/build.yml)
[![Blueprint CI](https://img.shields.io/github/actions/workflow/status/LLM4Rocq/icones-rocq/blueprint.yml?branch=main&style=for-the-badge&label=blueprint%20CI)](https://github.com/LLM4Rocq/icones-rocq/actions/workflows/blueprint.yml)
[![Blueprint](https://img.shields.io/badge/blueprint-online-blue?style=for-the-badge)](https://llm4rocq.github.io/icones-rocq/blueprint/)
[![Blueprint PDF](https://img.shields.io/badge/blueprint-PDF-red?style=for-the-badge)](https://llm4rocq.github.io/icones-rocq/blueprint.pdf)
[![Rocq 9.1.1](https://img.shields.io/badge/rocq-9.1.1-orange?style=for-the-badge)](https://rocq-prover.org/)
[![License](https://img.shields.io/badge/license-CC--BY--4.0-blue.svg?style=for-the-badge)](https://creativecommons.org/licenses/by/4.0/)

A Rocq / mathcomp-analysis formalization of *Integration in Cones* by
Thomas Ehrhard and Guillaume Geoffroy
([LMCS 21(1:1), 2025](https://doi.org/10.46298/LMCS-21(1:1)2025),
[arXiv:2212.02371](https://arxiv.org/abs/2212.02371)).

> The `Blueprint online` / `Blueprint PDF` badges resolve once the
> blueprint workflow has deployed to GitHub Pages (enable Pages →
> "GitHub Actions" in the repository settings).

## Status

**MVP complete.** The development covers paper §2 – §6 and culminates
in paper Theorem 6.5: the substochastic-kernel category `Skern` embeds
fully and faithfully into the category `ICones` of integrable cones
(`Icones.kernels.thm65.Skern_to_ICones_fully_faithful`).

- ~19k lines of Rocq across 24 files, **zero project-specific axioms**
  and **zero `Admitted`** — the headline theorem depends only on the
  three classical-logic axioms inherited from `mathcomp-analysis`
  (`propositional_extensionality`, `functional_extensionality_dep`,
  `constructive_indefinite_description`).
- See [`PLAN.md`](./PLAN.md) for the milestone roadmap (M1 – M5) and the
  strategic design decisions.

Out of scope for the MVP (documented in `PLAN.md`): the tensor product
`⊗`, the `!` exponential comonad, stable / analytic functions, the
LNL adjunction, and the PCS embedding.

## Build

Requires:

- Rocq 9.1+ (tested on 9.1.1)
- `rocq-mathcomp` 2.5+
- `rocq-mathcomp-analysis` 1.16+
- `rocq-hierarchy-builder` 1.10+
- `rocq-elpi` 3.3+

Install dependencies from the released opam repository and build:

```bash
opam install rocq-mathcomp-analysis rocq-hierarchy-builder
make
```

## Layout

```
theories/
├── prelude/    -- classical-logic + ereal/nonneg helpers + ω-cpo
├── cones/      -- precone, cone, basic lemmas, examples, category Cones   (paper §2, M1)
├── mcones/     -- Ar, measurable cones, FMeas, Path, category MCones      (paper §3, M2)
├── icones/     -- Pettis integral, integrable cones, Fubini, completeness (paper §4, M3)
├── homs/       -- internal hom C ⊸ D (linhom) and the iso of Thm 6.1      (paper §5.1/§5.2 + §6, M4/M5)
└── kernels/    -- substochastic kernels Skern and the embedding Thm 6.5   (paper §6, M5)
```

## Blueprint

A LaTeX *blueprint* (in the Patrick Massot / `leanblueprint` style,
adapted to Rocq) describes the formalisation in mathematical English
alongside its Rocq counterpart. Each statement carries a `\rocq{...}`
pointer to the corresponding declaration in `theories/`, and the web
version renders a dependency graph. The blueprint is the canonical
artefact for auditors who want to review the formalisation without
opening the Rocq sources first.

Sources live under [`blueprint/src/`](./blueprint/src/) — one chapter
per milestone:

- `chapters/01-cones.tex` — paper §2 (M1)
- `chapters/02-mcones.tex` — paper §3 (M2)
- `chapters/03-icones.tex` — paper §4 (M3)
- `chapters/04-linhom.tex` — paper §5.1 + §5.2 (M4)
- `chapters/05-skern.tex` — paper §6 + MVP (M5)

To build locally:

```bash
pip install -r blueprint/requirements.txt
sudo apt install graphviz libgraphviz-dev texlive-xetex \
                 texlive-latex-extra texlive-fonts-extra latexmk
rocqblueprint web      # HTML → blueprint/web/
rocqblueprint pdf      # PDF  → blueprint/print/print.pdf
```

In CI, [`.github/workflows/blueprint.yml`](./.github/workflows/blueprint.yml)
builds both the HTML and the PDF on every push to `main` (and on PRs),
uploads them as artefacts, and (on `main` only) publishes them to
GitHub Pages. The blueprint workflow uses `continue-on-error: true`
throughout and is independent of the gating Rocq build below — a
blueprint failure never blocks a PR.

The Rocq build itself is gated by
[`.github/workflows/build.yml`](./.github/workflows/build.yml), which
runs `make` and the MVP axiom check on every push and PR.

## Reproducing the MVP headline

Run [`./verify.sh`](./verify.sh) to clean-rebuild the project and
`Print Assumptions` the MVP headline
`Icones.kernels.thm65.Skern_to_ICones_fully_faithful` (paper Theorem
6.5). The expected output lists only the classical-logic axioms
inherited from `mathcomp-analysis`; the project itself contains zero
`Axiom` declarations and zero `Admitted` lemmas.

## Paper sources

The paper is *Integration in Cones* by Thomas Ehrhard and Guillaume
Geoffroy, available open access:

- arXiv: <https://arxiv.org/abs/2212.02371>
- LMCS 21(1:1), 2025: DOI [10.46298/LMCS-21(1:1)2025](https://doi.org/10.46298/LMCS-21(1:1)2025)

The paper is the canonical reference for the Rocq sources; proofs
annotate the paper section and lemma number they correspond to. The
PDF is not bundled in this repository — fetch it from the links above.

## License

[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/) — the same
licence under which the underlying LMCS paper is published. See
[`LICENSE`](./LICENSE). When reusing this work, please cite both the
original paper and this formalisation.
