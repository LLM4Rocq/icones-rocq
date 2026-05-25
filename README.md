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

## Status

A formalization of paper **§2 – §9** (paper §8, analytic functions, is
out of scope). ~40k lines of Rocq across 45 files, **zero `Admitted`**.
Every remaining project-specific axiom is confined to a *single*
clearly-marked *staging interface* under `theories/axioms/`; everything
else uses only the three classical-logic axioms inherited from
`mathcomp-analysis` (`propositional_extensionality`,
`functional_extensionality_dep`, `constructive_indefinite_description`).
The development therefore splits into an **axiom-free core** and a
(now single-interface) **staged tier**. The tensor `⊗` / SMCC structure
and the exponential `!` comonad have both been **discharged** — they
moved out of the staged tier into the axiom-free core — leaving only the
*existence* of the Seely isomorphisms staged, mechanized *modulo*
`seely_interface`, to be discharged by proving SAFT for `ICones`
(see [`PLAN.md`](./PLAN.md) §13).

### Axiom-free core (zero project axioms)

- **Cones, measurable cones, integrable cones** (paper §2 – §4): the
  `PreCone → Cone → MCone → ICone` Hierarchy-Builder tower, the Pettis
  integral, a Fubini theorem, and completeness of `ICones`.
- **The kernel-embedding core** (paper §5.1 – §5.2 and §6), capstone
  **Theorem 6.5**: the substochastic-kernel category `Skern` embeds
  fully and faithfully into `ICones`
  (`Icones.kernels.thm65.Skern_to_ICones_fully_faithful`). This is the
  project's canonical **axiom-free regression anchor**.
- **The stable cartesian closed category `SCones`** (paper §7): local
  cones, total monotonicity, finite differences and **Theorem 7.19**,
  the composition theorem **Theorem 7.30**, and **Theorem 7.32** in
  full — `SCones` is cartesian closed (products, evaluation, currying) —
  together with the dereliction functor `Der : ICones → SCones`.
- **The symmetric monoidal closed structure** (paper §5.3 – §5.5): the
  tensor `⊗`, **Theorem 5.12** (`(B⊗C)⊸D ≃ B⊸(C⊸D)`, `tensor_hom_iso`),
  Theorem 5.13 (multiplicativity of the tensor norm), and **Theorem 5.15**
  (`ICones` is an SMCC, `homs.smcc.ICones_smcc`), with the four structural
  isos `α/λ/ρ/σ` and all coherence (triangle / pentagon / hexagon,
  `σ² = id`) *proved*. **This is now fully discharged and axiom-free**:
  the former `theories/axioms/saft_interface.v` (18 `Parameter`s) was
  proved via the concrete SAFT construction and **deleted**; `tensor.v`
  re-exports the proved modules (`tensor_construct.v`, `tensor_hom_iso.v`,
  `tensor_iso.v`) under `Opaque` seals.
- **Least-fixpoint operators** (paper §9.2): the Kleene fixpoint on the
  cone unit-ball ω-cpo and the fixpoint combinator `Y` as an `SCones`
  morphism.
- **The exponential `!` comonad** (paper §9, the `E ⊣ Der`
  linear/non-linear adjunction): `Der : ICones → SCones` preserves all
  limits (**Theorem 7.34**, `der_preserves_limits` in
  `stable/der_continuous.v`), so the Special Adjoint Functor Theorem
  yields the left adjoint `E`; the induced comonad `! = E∘Der` (counit
  `der`, comultiplication `dig`, and all comonad laws,
  `homs.bang.Bang_comonad`) is constructed in `homs/bang_construct.v`
  and is **axiom-free** — the `E ⊣ Der` interface (`exp_interface`) was
  discharged in place (its `Parameter`s/`Axiom`s became
  `Definition`s/`Lemma`s backed by `bang_construct`).
- **Towards SAFT** ([`PLAN.md`](./PLAN.md) §13.1): `ICones`
  **well-poweredness** (paper Theorem 4.18) genuinely proved, the
  subobject-intersection machinery, and **Theorem 5.9** (`(C ⊸ −)`
  preserves all limits) — the ingredients that will discharge the
  staged tier.

### Staged tier (the one remaining interface: `seely_interface`)

The staged tier has shrunk to a single interface. Both
`saft_interface` (the tensor — discharged and **deleted**) and
`exp_interface` (the `E ⊣ Der` adjunction — discharged **in place**)
are now part of the axiom-free core above. What remains staged is the
*existence* of the Seely isomorphisms, fully proved *relative to* the
five `Parameter`s/`Axiom`s of `theories/axioms/seely_interface.v`
(`Seely2`, `Seely2E`, `Seely2_natural`, `Seely0`, `Seely0E`) — the
SAFT/Yoneda *representability* content the paper obtains via Freyd's
Special Adjoint Functor Theorem.

- **The Seely category** (paper §9, Theorem 9.5,
  `homs.seely.ICones_Seely`): **`ICones` is a Seely category** — the
  axiom-free comonad `!` made a strong monoidal comonad against the
  axiom-free tensor `⊗`. *All* the coherence **laws** are proved
  (`seely_comult`, `seely_assoc`, `seely_braid`, `seely_lunit`,
  `seely_runit`, the dereliction squares), each via the `!`-tensor
  promotion extensionality (paper Lemma `tens-excl-equal-charact`). Only
  the *existence* of the Seely isomorphisms `!A ⊗ !B ≅ !(A & B)`
  (`Seely2`) and `1 ≅ !⊤` (`Seely0`), characterized on promoted pure
  tensors, remains staged in `seely_interface.v`. The remaining
  discharge work is **Lemma 9.4** (`B ⇒ (C⊸D) ≅ C ⊸ (B⇒D)`, natural)
  plus the unit point-bijection (`SCones(⊤,C) ≃ ICones(1,C)`); the
  contravariant-Yoneda assembly tool `co_yoneda_iso`
  (`homs.icones_iso`) is already merged.

The axiom-free core does **not** depend on `seely_interface` —
`Skern_to_ICones_fully_faithful`, the tensor/SMCC, the `!` comonad, and
everything else in the core stay axiom-clean regardless of the staged
tier.

**In progress / future work** ([`PLAN.md`](./PLAN.md)): discharging the
last staged interface (`seely_interface`) — Lemma 9.4 plus the unit
point-bijection — which would move the Seely category into the
axiom-free core; **Theorem 9.7** (`FMeas(X)` is a `!`-coalgebra, paper
§9.1) is currently being formalized in `theories/homs/coalgebra.v` (not
yet merged); paper §8 (analytic functions, `ACones`); and the
probabilistic-coherence-space embedding. `PLAN.md` has the full roadmap
(milestones M1 – M5 and the §13 axiom-free plan).

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
├── cones/      -- precone, cone, basic lemmas, examples, category Cones,    (paper §2, M1)
│                  radius-aware Scott-continuity (omega_general)             (paper §7 prereq)
├── mcones/     -- Ar, measurable cones, FMeas, Path, category MCones,       (paper §3, M2)
│                  test-pullback infrastructure (test_pullback)              (paper §5.3)
├── icones/     -- Pettis integral, integrable cones, Fubini, completeness,  (paper §4, M3)
│                  well-poweredness + SAFT machinery (representable)         (paper §4.18, §13.1)
├── homs/       -- internal hom C ⊸ D (linhom), iso of Thm 6.1 (bilin),      (paper §5.1/§5.2 + §6, M4/M5)
│                  isos in ICones (icones_iso, co_yoneda_iso), the h⊸g       (paper §5.3)
│                  functor (linhom_functor), (C⊸−) preserves limits          (Thm 5.9)
│                  (limpl_continuous); tensor ⊗ + SMCC — AXIOM-FREE          (paper §5.3–§5.5, Thm 5.15,
│                  (tensor/_construct/_hom_iso/_iso, smcc);                    discharged)
│                  the ! comonad — AXIOM-FREE (bang, bang_construct)         (paper §9, E⊣Der)
│                  + the Seely category (seely, modulo seely_interface)      (paper §9, Thm 9.5)
├── axioms/     -- the one remaining staged interface: the Seely-iso         (paper §9)
│                  existence (seely_interface, 5 decls); exp_interface
│                  DISCHARGED in place; saft_interface DISCHARGED + DELETED
├── stable/     -- local cones, total monotonicity, the stable hom B ⇒ₛ C,   (paper §7)
│                  finite differences (Thm 7.19), the composition theorem
│                  (Thm 7.30), the cartesian closed SCones (Thm 7.32:
│                  scones_cat + scones_ccc), fixpoints (fixpoint, §9.2),
│                  and Der preserves limits (der_continuous, Thm 7.34)
└── kernels/    -- substochastic kernels Skern and the embedding Thm 6.5     (paper §6, M5)
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
- `chapters/05-skern.tex` — paper §6, the kernel embedding (M5)
- `chapters/06-tensor.tex` — paper §5.3–§5.5, the tensor + SMCC (axiom-free)
- `chapters/07-stable.tex` — paper §7, the stable CCC `SCones`
- `chapters/08-exponential.tex` — paper §9, the exponential `!` (comonad, axiom-free) + Seely category (modulo `seely_interface`)

To build locally:

```bash
pip install -r blueprint/requirements.txt
sudo apt install graphviz libgraphviz-dev texlive-xetex \
                 texlive-latex-extra texlive-fonts-extra latexmk
rocqblueprint web      # HTML → blueprint/web/
rocqblueprint pdf      # PDF  → blueprint/print/print.pdf
```

In CI, [`.github/workflows/blueprint.yml`](./.github/workflows/blueprint.yml)
builds the HTML (and best-effort PDF) on every push to `main` (and on
PRs), uploads them as artefacts, and (on `main` only) publishes them to
GitHub Pages. The blueprint web build is the gating step: if it fails,
the coqdoc build and the Pages deploy are skipped and the workflow
(and its badge) goes red — an honest signal. It stays independent of
the main Rocq build and never *blocks* a PR, because it is simply not
marked a required status check (not because failures are hidden).

The Rocq build itself is gated by
[`.github/workflows/build.yml`](./.github/workflows/build.yml), which
runs `make` and the axiom-free-core axiom check on every push and PR.

## Reproducing the axiom-free anchor

Run [`./verify.sh`](./verify.sh) to clean-rebuild the project and
`Print Assumptions` the axiom-free regression anchor
`Icones.kernels.thm65.Skern_to_ICones_fully_faithful` (paper Theorem
6.5, the capstone of the kernel-embedding core). The expected output
lists only the classical-logic axioms inherited from `mathcomp-analysis`.
The project's own `Axiom`/`Parameter` declarations are now confined to a
single staging interface (`theories/axioms/seely_interface.v`, the
Seely-iso existence); everything else — including this anchor, the
tensor/SMCC, and the `!` comonad — contains zero `Axiom` declarations
and zero `Admitted` lemmas.

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
