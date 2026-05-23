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

**MVP complete.** The development covers paper §2 – §6 and culminates
in paper Theorem 6.5: the substochastic-kernel category `Skern` embeds
fully and faithfully into the category `ICones` of integrable cones
(`Icones.kernels.thm65.Skern_to_ICones_fully_faithful`).

- ~33.6k lines of Rocq across 37 files. The MVP headline theorem
  carries **zero project-specific axioms** and **zero `Admitted`** — it
  depends only on the three classical-logic axioms inherited from
  `mathcomp-analysis` (`propositional_extensionality`,
  `functional_extensionality_dep`, `constructive_indefinite_description`).
- See [`PLAN.md`](./PLAN.md) for the milestone roadmap (M1 – M5) and the
  strategic design decisions.

## Iteration 2 (in progress)

Iteration 2 extends the development past the MVP towards the symmetric
monoidal closed structure (paper §5.3–§5.5) and the stable / measurable
functions (paper §7). The live, axiom-free staged plan is `PLAN.md` §13
(with §12 the retained axiomatized fallback). Status:

- **Tensor `⊗` and the symmetric monoidal closed structure (paper
  §5.3–§5.5)** — mechanized *against a staged SAFT interface*. The
  morphism-level internal-hom functor `h ⊸ g` (Prop 5.8) is built in
  `homs/linhom_functor.v` via the reusable test-pullback machinery
  (`mcones/test_pullback.v`); `homs/icones_iso.v` packages isomorphisms
  in `ICones`. The pure tensor, bifunctoriality, Theorem 5.12
  (`(B⊗C)⊸D ≃ B⊸(C⊸D)`), Theorem 5.13 and Prop 5.14 live in
  `homs/tensor.v`; the associator/unitors/symmetry as isos and **all**
  the coherence (triangle / pentagon / hexagon, `σ² = id`) are
  **derived** in `homs/smcc.v`, culminating in Theorem 5.15 (`ICones`
  is an SMCC). **Honesty note:** the SAFT/Yoneda *representability*
  content the paper obtains via Freyd's Special Adjoint Functor
  Theorem — the existence of the tensor object and the structural
  isomorphisms — is currently **axiomatized** as a handful of
  `Parameter`s in `theories/axioms/saft_interface.v`. Everything in
  `tensor.v` / `smcc.v` is proved *modulo* that clearly-delimited
  interface; it is **not yet axiom-free**. The plan (`PLAN.md` §13.1) is
  to *discharge* those `Parameter`s by proving SAFT for `ICones`
  (M-SAFT). The MVP headline (Theorem 6.5) is independent of this
  interface and remains axiom-clean.

- **Stable functions (paper §7)** — axiom-clean (only the inherited
  classical base), no `Admitted`. In `theories/stable/` and
  `theories/cones/omega_general.v`:
  - the local cone `B_x` as a full integrable cone (§7.1,
    `local_cone.v`);
  - the radius-aware ω-continuity / Scott-continuity foundation
    (`omega_general.v`), total monotonicity (Def 7.5) and the stable /
    measurable predicates (§7.2, `totmono.v`), and the stable internal
    hom `B ⇒ₛ C` as a full integrable cone (`stablehom.v`);
  - finite differences and **Theorem 7.19** (totally monotonic ⟺
    n-increasing for all n) in `findiff.v`;
  - **Theorem 7.30**: stable functions are closed under composition
    (the §7.3 "Faà di Bruno" core), `compose.v`;
  - the category **SCones** of integrable cones and stable measurable
    maps (§7.4), with the dereliction inclusion `Ders : ICones → SCones`
    (Lemma 7.31) and products (Theorem 7.32, products part) in
    `scones_cat.v`. The category, `Ders` and products are done; the
    cartesian-closed structure (tupling, evaluation, currying) is in
    progress.

- The whole of iteration 2 keeps the **zero project-specific axioms**
  discipline (only the three classical-logic axioms from
  `mathcomp-analysis`), **except** the explicitly-staged
  `saft_interface.v` `Parameter`s above. The MVP headline theorem is
  unaffected.

Out of scope / future work (documented in `PLAN.md`): discharging the
staged SAFT interface (M-SAFT, `PLAN.md` §13.1), the `!` exponential
comonad, paper §8 analytic functions, the §9 LNL adjunction, and the
PCS embedding.

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
├── icones/     -- Pettis integral, integrable cones, Fubini, completeness   (paper §4, M3)
├── homs/       -- internal hom C ⊸ D (linhom), iso of Thm 6.1 (bilin),      (paper §5.1/§5.2 + §6, M4/M5)
│                  isos in ICones (icones_iso), the h⊸g functor              (paper §5.3, iter 2)
│                  (linhom_functor), tensor ⊗ (tensor) and the SMCC (smcc)   (paper §5.3–§5.5, iter 2)
├── axioms/     -- the staged SAFT/tensor interface for ⊗ (to be discharged) (paper §5.4, iter 2)
├── stable/     -- local cones, total monotonicity, the stable hom B ⇒ₛ C,   (paper §7, iter 2)
│                  finite differences (Thm 7.19), the composition theorem
│                  (Thm 7.30), and the category SCones (Thm 7.30/7.32)
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
builds the HTML (and best-effort PDF) on every push to `main` (and on
PRs), uploads them as artefacts, and (on `main` only) publishes them to
GitHub Pages. The blueprint web build is the gating step: if it fails,
the coqdoc build and the Pages deploy are skipped and the workflow
(and its badge) goes red — an honest signal. It stays independent of
the main Rocq build and never *blocks* a PR, because it is simply not
marked a required status check (not because failures are hidden).

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
