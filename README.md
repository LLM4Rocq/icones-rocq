# Icones — Integration in Cones, formalized in Rocq

A Rocq/mathcomp-analysis formalization of *Integration in Cones* by Thomas Ehrhard
and Guillaume Geoffroy ([LMCS 21:1, 2025](https://lmcs.episciences.org/15021),
[arXiv:2212.02371](https://arxiv.org/abs/2212.02371)).

## Status

Early development. See [`PLAN.md`](./PLAN.md) for scope, milestones, and the
strategic decisions guiding the formalization. The current target is the MVP:
a faithful formalization of paper §2 – §4 + §5.1 + §6, culminating in
Theorem 6.5 (the substochastic-kernel category `Skern` embeds fully and
faithfully into `ICones`).

## Build

Requires:

- Rocq 9.1+ (tested on 9.1.1)
- `rocq-mathcomp` 2.5+
- `rocq-mathcomp-analysis` 1.16+
- `rocq-hierarchy-builder` 1.10+
- `rocq-elpi` 3.3+

Install dependencies from the released opam repository:

```bash
opam install rocq-mathcomp-analysis rocq-hierarchy-builder
```

Build:

```bash
make
```

## Layout

```
theories/
├── prelude/          -- classical-logic + ereal/nonneg helpers + ω-cpo
└── cones/            -- precone, cone, category Cones (paper §2)
```

Further sub-directories (`mcones/`, `icones/`, `homs/`, `kernels/`) appear as
the corresponding milestones M2–M5 land.

## License

MIT. See [`LICENSE`](./LICENSE).

## Paper sources

The paper is *Integration in Cones* by Thomas Ehrhard and Guillaume
Geoffroy, available open access:

- arXiv: <https://arxiv.org/abs/2212.02371>
- LMCS 21(1:1), 2025: DOI [10.46298/LMCS-21(1:1)2025](https://doi.org/10.46298/LMCS-21(1:1)2025)

The paper is the canonical reference for the Rocq sources; proofs
annotate the paper section and lemma number they correspond to. The
PDF is not bundled in this repository — fetch it from the links above.

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

In CI, the workflow [`.github/workflows/blueprint.yml`](./.github/workflows/blueprint.yml)
builds both the HTML and the PDF on every push to `main` (and on PRs),
uploads them as artefacts, and (on `main` only) publishes them to
GitHub Pages. The blueprint workflow is independent of the Rocq build
and uses `continue-on-error: true` throughout: a blueprint failure
never blocks a PR.

## Reproducing the MVP headline

Run [`./verify.sh`](./verify.sh) to clean-rebuild the project and
`Print Assumptions` the MVP headline
`Icones.kernels.thm65.Skern_to_ICones_fully_faithful` (paper Theorem
6.5). The expected output lists only the classical-logic axioms
inherited from `mathcomp-analysis`; the project itself contains zero
`Axiom` declarations and zero `Admitted` lemmas.
