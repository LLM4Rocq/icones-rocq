# Formalization plan: *Integration in Cones* (Ehrhard & Geoffroy, LMCS 2025)

Paper: <https://arxiv.org/abs/2212.02371> · LMCS DOI 10.46298/LMCS-21(1:1)2025 · 98 pages
(fetch the PDF from those open-access links; it is not bundled here).

> **Terminology note (2026-05-24).** The label **"MVP"** used throughout the
> historical planning sections below (the original §2–§6 deliverable: the
> `Skern → ICones` embedding, paper Thm 6.5) is **retired**. The project has
> outgrown it — it now covers paper §2–§9. The current framing is
> **axiom-free core vs staged tier**: the *axiom-free core* (zero project
> axioms) is §2–§7 (incl. the full stable CCC `SCones`), the §9.2 fixpoints,
> well-poweredness (Thm 4.18), and Thm 5.9; the *staged tier* (mechanized
> modulo the three `theories/axioms/*` interfaces, to be discharged by SAFT)
> is the §5.3–§5.5 tensor SMCC and the §9 exponential `!` + Seely category.
> Read "MVP" below as "the axiom-free kernel-embedding core (§2–§6)";
> `Skern_to_ICones_fully_faithful` is now described as the *axiom-free
> regression anchor*. The README reflects the current framing.

---

## 0. TL;DR

The paper builds a **denotational semantics for higher-order probabilistic programs** by equipping
Selinger-style positive cones with a Pettis-style integral, yielding a symmetric-monoidal-closed
category `ICones` and two cartesian-closed sub-categories of stable/analytic functions, giving a
model of Linear Logic with an exponential `!`. ~176 numbered statements across 10 sections.

After surveying the paper, mathcomp-analysis 1.16.0, and the broader Rocq ecosystem (mathcomp-qbs,
Yalla, monae, Bochner integral of Boldo–Clément–Faissole, etc.), and after a frank
devil's-advocate review, the recommended formalization plan is:

- **MVP goal (≈ 9–12 person-months for an mathcomp-analysis-grade engineer)**: paper §2–4 + concrete
  `⊸` from §5.1 + Theorem 6.1 (`Path(X,B) ≃ FMeas(X) ⊸ B`) + Theorem 6.5 (`Skern → ICones` is fully
  faithful). No tensor `⊗`, no `!`, no stable/analytic, no PCS. The kernel embedding alone is a
  defensible, publishable result.
- **Strategic choice 1: try a "positive cone of a Banach space" definition first** (Phase 0).
  Build cones as the non-negative subset of an `R`-Banach space carrier, inheriting mathcomp-analysis
  algebra/topology. If `FMeas(X)`, `Path(X, B)`, and `B ⊸ C` all fit, we keep this; otherwise fall
  back to a parallel `R≥0`-semimodule tower (Phase 0′, +3 months).
- **Strategic choice 2: don't axiomatize `⊗` and `!` for the MVP**. Build `⊸` concretely (the paper
  *does* construct it in §5.1). Tensor and exponential are research-software-class deliverables that
  involve postulating ~10 coherence diagrams; defer them to a post-MVP stretch goal with a documented
  axiom budget.
- **Stretch milestones** (each its own 6–12 person-month project): §5 SMCC closure with axiomatised
  `⊗`; §7 stable functions and CCC `SCones`; §9 `!`-comonad axiomatised through SAFT; §10 PCS
  embedding. §8 (analytic functions) is the hardest single section and is deliberately not in scope.

---

## 1. Paper scope and what we are formalizing

| § | Title | LoC est. | MVP? | Notes |
|---|-------|---|---|---|
| 2 | Cones | 1.5–2 k | yes | precone, cone, norm, ω-completeness, category `Cones` |
| 3 | Measurable cones | 1.0–1.5 k | yes | `Ar` parameter, test family `M_X`, paths, `MCones`, `FMeas(X)` |
| 4 | Integrable cones | 2.0–3.0 k | yes | Pettis-style integral (Def 4.1), Lemma 4.7, Fubini 4.15, `ICones` complete/well-powered |
| 5.1 | Internal hom `⊸` | 0.5–1.0 k | yes | concrete construction |
| 5.2–5.5 | Bilinear, ⊗, SMCC | 3.0–5.0 k | **stretch** | requires axiomatising SAFT consequences |
| 6 | Categorical properties of integration | 1.0–1.5 k | yes (Thm 6.1, 6.5) | the MVP money theorem |
| 7 | Stable & measurable functions | 4.0–6.0 k | stretch | totally-monotonic combinatorics, CCC `SCones` |
| 8 | Analytic functions | 6.0–10 k | **out of scope** | polarisation, Taylor expansion, `ACones` CCC |
| 9 | LNL adjunction, `!` | 2.0–3.0 k | stretch (with axioms) | Seely category, fixpoints |
| 10 | PCS embedding | 2.0–3.0 k | future | Cantor-space equalizer |

The **MVP deliverable** is a single theorem: `Skern → ICones` is fully faithful (paper Thm 6.5),
proved over a concrete development that mirrors sections 2, 3, 4, 5.1 and 6. This is the smallest
scope that demonstrates the framework's value (it shows that classical sub-stochastic kernels are a
genuine sub-category of the cone model and that integrable cones generalise them in a non-trivial
way).

---

## 2. Foundations and dependencies

- **Toolchain**: Rocq 9.1.1 (opam switch `rocq-9.2`), `rocq-mathcomp 2.5.0`, `HB 1.10.2`,
  `rocq-mathcomp-analysis 1.16.0`. All already installed.
- **Hard dependencies**: `mathcomp-analysis` (measure, integration, kernels, Giry monad, ereals,
  topology, normed-Z-modules).
- **Soft dependencies / inspirations**:
  - `mathcomp-qbs` (LLM4Rocq) — measurability-structure encoding template; we mirror its style of
    bundling QBS-like data atop mathcomp-analysis.
  - Boldo–Clément–Faissole Bochner integral — methodological template for the Pettis existence
    proof (simple functions + dominated convergence). Re-implemented on mathcomp-analysis, not
    inherited.
  - No other Rocq formalisation of cones / PCS / Selinger's model exists; the broader Rocq
    ecosystem contributes nothing we can directly reuse.
- **Classical principles**: we will rely on `boolp` (`classic`, `pselect`, `xchoose`,
  `Prop_irrelevance`) and on the constructive-choice machinery of mathcomp-analysis. Axioms beyond
  this are documented in §7.

Key mathcomp-analysis hooks we will lean on (file references in checkout of `math-comp/analysis`):

- `classical/boolp.v` — classical logic, `xchoose`, `Prop_irrelevance`.
- `reals/reals.v`, `reals/constructive_ereal.v` — `realType`, `\bar R`, `{nonneg R}`,
  `posnumP`.
- `theories/topology_theory/*` — `Nbhs`, `Topological`, `Uniform`, `Complete`, `PseudoMetric`.
- `theories/normedtype_theory/*` — `NormedModule R`, `CompleteNormedModule`, `{linear_continuous U
  -> V}` (the test/morphism prototype).
- `theories/measure_theory/*` — `Measurable`, σ-algebras, `Measure`, `FiniteMeasure`, `SubProbability`,
  `pushforward`, `dirac`.
- `theories/lebesgue_integral_theory/*` — `\int[mu]_x f x`, `monotone_convergence`, `fatou`,
  `dominated_convergence`, `fubini_tonelli1`, `fubini_tonelli2`.
- `theories/lebesgue_integral_theory/giry.v` — `giry_ret`, `giry_join`, `giry_bind`.
- `theories/kernel.v` — `Kernel`, `SFiniteKernel`, `FiniteKernel`, `SubProbabilityKernel`,
  `R.-fker X ~> Y`, kernel composition.
- `theories/sequences.v`, `theories/esum.v`, `theories/measurable_realfun.v`, `theories/convex.v`,
  `classical/unstable.v` (the new `SemiNorm`/`Norm` HB structures).

Gaps in mathcomp-analysis we **cannot avoid filling ourselves**:

1. `R≥0`-acting positive semimodule layer if Phase 0 fails.
2. ω-cpo / dcpo structure on the unit ball of a normed object.
3. Cone / measurable cone / integrable cone HB hierarchy.
4. Cone-valued (Pettis-style) integration.
5. The internal hom `⊸` of integrable cones.
6. Anything categorical beyond what we prove pointwise (no SMCC infrastructure exists in Rocq).

---

## 3. Two strategic decisions

### 3.1 How to define a cone in Rocq — Phase 0 vs Phase 0′

**Default (Phase 0): cones as positive parts of Banach spaces.**

```coq
HB.mixin Record isCone (V : completeNormedModuleType R) (P : set V) := {
  cone_zero : 0 \in P;
  cone_add  : forall x y, x \in P -> y \in P -> x + y \in P;
  cone_scale: forall (r : {nonneg R}) x, x \in P -> r%:num *: x \in P;
  cone_pos  : forall x, x \in P -> 0 <= `|x|;
  cone_omegacomplete : (* ω-completeness on the unit ball, as a sup operator *)
    forall (u : nat -> V), (forall n, u n \in P) -> (forall n, u n <= u n.+1) ->
      (forall n, `|u n| <= 1) -> { x : V | x \in P /\ ... };
}.
HB.structure Definition Cone V := { P of isCone V P }.
```

**Pros**: inherits all of mathcomp-analysis's algebra/topology; `+`, `*:`, `\|·\|`, continuity,
linearity, bilinearity all come for free; integral lemmas in the surrounding Banach space port over.

**Cons**: not every cone is realisable in a Banach space *in general* (the paper acknowledges this).
But the cones we need for the MVP — `FMeas(X)`, `Path(X, B)`, `B ⊸ C` — are all realisable: each
sits naturally inside a Banach space of signed/bounded measures or bounded measurable functions.

**Acceptance criterion for Phase 0**: write `FMeas(X)` as the positive part of the Banach space of
finite signed measures (or of bounded `\bar R`-valued additive functions — to be decided), prove the
five cone axioms hold, and prove the ω-completeness explicitly via monotone convergence on
`µ ↦ µ(U)` for each `U ∈ σX`. **Budget: 2 weeks.** If this scope is achievable, we adopt Phase 0
permanently. If `\bar R`-vs-`R` plumbing or Banach-completion obstacles balloon, we abort to
Phase 0′.

**Fallback (Phase 0′): independent `R≥0`-semimodule tower.**

```coq
HB.mixin Record isPrecone (P : Type) := {
  cone_add  : P -> P -> P;
  cone_zero : P;
  cone_scal : {nonneg R} -> P -> P;
  cone_addA : associative cone_add;
  cone_addC : commutative cone_add;
  cone_add0r: left_id cone_zero cone_add;
  cone_cancel : forall x y z, cone_add x y = cone_add x z -> y = z;
  cone_pos  : forall x y, cone_add x y = cone_zero -> x = cone_zero;
  cone_scal_distr : ... ;
}.
(* further mixins layer on norm, order, ω-completeness *)
```

**Pros**: faithful to the paper.

**Cons**: ~1.5–2 k extra lines for the structure alone before any theorems; pervasive case-splits
on partial subtraction; no integration with mathcomp's `Linear`, `linear_zero`, `bilinear`,
`NormedModule` — every adjacent lemma must be re-proved by hand.

**Decision rule**: spend 10–15 working days on Phase 0 prototype (M0 below). At day 10 reassess; at
day 15 abort if blocked. The two paths diverge at M1 and never recombine; commit early.

### 3.2 Whether to construct `⊗` and `!` or postulate them

The paper builds `⊗` and `!` by invoking the **Special Adjoint Functor Theorem** (Thm 4.19), which
relies on `ICones` being complete, well-powered, and cogenerated. SAFT itself is essentially Axiom
of Choice over proper-class subobject lattices, and the *consequences* of SAFT in the paper are an
adjunction `(- ⊗ B) ⊣ (B ⊸ -)` and an exponential comonad `!`.

In Rocq we have three options:

| Option | What we get | Cost | Trust |
|---|---|---|---|
| **A. Construct `⊗` concretely** | Full constructive development. | ~12 person-months for `⊗` alone. | Low risk of axiom error. |
| **B. Axiomatise the universal property** | Drop-in `⊗`, `!`. | ~3 person-months for axioms + naturality + coherence. | High: ~10 axioms, easy to mis-state. |
| **C. Skip `⊗` and `!` from the MVP entirely** | A working `ICones` with `⊸` only. Kernel embedding Thm 6.5 still goes through. | Zero. | Highest: no new axioms. |

**MVP choice = C.** The internal hom `⊸` is constructed *concretely* in §5.1 (Defs 5.2, 5.4, Lemma
5.4 proves `C ⊸ D` is itself integrable). `Path` is concrete (§3.2.2). Theorem 6.1 only needs `⊸`
and `Path` and `FMeas`. Theorem 6.5 follows from 6.1 plus an embedding `Skern ↪ ICones`.

**Stretch choice = B.** When (if) we go beyond the MVP, postulate the adjunction `(- ⊗ B) ⊣ (B ⊸ -)`
together with a natural-iso witness and the SMC coherence diagrams (pentagon, hexagon, units), and
derive `(B ⊗ C) ⊸ D ≃ B ⊸ (C ⊸ D)` (paper Thm 5.12). Each axiom carries a paper-equation reference
in the source. Reviewers can audit the axiom file in isolation.

**Never choose A** (constructive `⊗`) unless this becomes a multi-engineer multi-year project.

---

## 4. HB structure hierarchy

Assuming Phase 0 succeeds. Each box is one HB mixin; arrows are inheritance.

```
   completeNormedModule R              -- inherited from mathcomp-analysis
            │
            ▼
       isCone V P            (R≥0-closed sub-semigroup, scale, pos, ω-complete unit ball)
            │
            ▼
   ConePack V (= V + P + cone axioms)               -- HB.structure Cone V
            │
            ▼
       isMCone (Cone V) M     (measurability structure: family M_X of [0,1]-valued tests, Ar-indexed)
            │
            ▼
       isICone (MCone V M)    (Pettis existence for every X∈Ar, every path, every finite μ)
            │
            ▼
       ICone V M     (the integrable-cone packed structure)
```

Above `ICone`:

```
   internal hom    : ICone × ICone → ICone     -- §5.1, concrete, MVP
   path            : Ar × ICone → ICone        -- §3.2.2
   FMeas           : Ar → ICone                -- §3.2.1
   product (&)     : ICone × ICone → ICone     -- §4.4, MVP
   coproduct (⊕)   : ICone × ICone → ICone     -- §4.4, MVP
   tensor (⊗)      : ICone × ICone → ICone     -- §5.4, STRETCH (axiomatised)
   exponential (!) : ICone → ICone             -- §9,   STRETCH (axiomatised)
```

Key design notes:

- **`Ar` is a section variable** of every file from `mcone.v` onwards. For the MVP we fix
  `Ar := {R^n | n ∈ ℕ}` (or, more precisely, the set of standard products `R × R × …` built in
  mathcomp-analysis via `\bigotimes_i M_i`). This avoids universe headaches and is sufficient for
  Thm 6.1 and Thm 6.5.
- **The measurability structure** `M = (M_X)_{X ∈ Ar}` is a single dependent record indexed by `Ar`.
  Each `M_X` is a set of test functions `B → [0,1]`. Concretely, given `Ar` finite-product-closed,
  it suffices to specify `M_0 ⊆ Cone(B, ⊥)` and derive the family by the closure condition (Mscomp).
- **The integral operator** `I_X^B : Path(X, B) × FMeas(X) → B` is defined as the unique witness of
  Pettis existence, recovered via `xchoose` against the separation axiom (Mssep).
- **Subtype proof-irrelevance**: every cone morphism is a quadruple (function + measurability +
  integrability + norm bound). Equality of morphisms is equality of underlying functions; we lean on
  `boolp.Prop_irrelevance` for the witnesses.

---

## 5. File and module layout

```
/home/rocq/icones
├── _CoqProject
├── dune-project
├── icones.opam                          -- dev opam file
├── Makefile.coq                          -- generated
├── PLAN.md                                -- this file
├── README.md
└── theories/
    ├── prelude/
    │   ├── classical_extra.v              -- boolp extensions, ProofIrrelevance helpers
    │   ├── ereal_extra.v                  -- \bar R ↔ R plumbing
    │   ├── nonneg_extra.v                 -- {nonneg R} arithmetic
    │   └── omegacpo.v                     -- ω-cpo HB structure on the unit ball
    ├── cones/
    │   ├── precone.v                      -- M1 (Phase 0 may merge this into cone.v)
    │   ├── cone.v                         -- M1: HB structure Cone, ω-completeness, examples
    │   ├── cone_cat.v                     -- M1: category Cones, products, equalisers
    │   ├── examples_cone.v                -- M1: \bar R≥0, R^n≥0, sequence cones
    │   └── basic_lemmas.v                 -- M1: Lemmas 2.8 – 2.23
    ├── mcones/
    │   ├── ar.v                           -- M2: the section variable Ar : MeasSubcat
    │   ├── mcone.v                        -- M2: HB structure MCone
    │   ├── path.v                         -- M2: Path(X, B) as a measurable cone
    │   ├── fmeas.v                        -- M2: FMeas(X) as a measurable cone
    │   └── mcone_cat.v                    -- M2: category MCones
    ├── icones/
    │   ├── pettis.v                       -- M3: Pettis existence as the defining axiom
    │   ├── icone.v                        -- M3: HB structure ICone
    │   ├── icone_integral.v               -- M3: lemma 4.7 (bilinear, ω-cont, measurable)
    │   ├── fubini.v                       -- M3: cone Fubini (Thm 4.15)
    │   ├── icone_cat.v                    -- M3: category ICones, products, equalisers, completeness
    │   └── examples.v                     -- M3: FMeas, Path, sums, products as integrable cones
    ├── homs/
    │   ├── linhom.v                       -- M4: C ⊸ D concrete construction (§5.1)
    │   ├── bilin.v                        -- M4: bilinear maps, Path ≃ FMeas ⊸ B (Thm 6.1)
    │   └── (deferred) tensor.v            -- post-MVP: ⊗ axiomatised
    └── kernels/
        ├── skern.v                        -- M5: substochastic kernel cone (Def 6.x)
        ├── skern_to_icone.v               -- M5: functor Skern → ICones
        └── thm65.v                        -- M5: Skern → ICones is fully faithful
```

Conventions:

- HB structure namespaces `pcone`, `cone`, `mcone`, `icone`. `Cone` already collides with
  mathcomp's category-theoretic "cone of a diagram" — avoid the bare identifier in `Notation`s.
- Files import `mathcomp.classical.boolp`, `mathcomp.analysis.measure`,
  `mathcomp.analysis.lebesgue_integral`, etc. — never the omnibus `all_classical`/`all_analysis`
  imports.
- Each definition that appears in the paper has its `Definition`/`Lemma`/`Theorem` annotated with
  the paper section and number, e.g. `(* Paper Def 3.2 *)`.
- Each axiom (every `Axiom`, `Parameter`, `Hypothesis` outside a `Section`) sits in
  `theories/axioms/` (initially empty for the MVP) with the paper equation/theorem reference
  inline. The MVP target is **zero `Axiom` lines** in this directory.

---

## 6. Milestones

| ID | Title | Calendar (1 FTE) | Lines | Paper coverage |
|---|---|---|---|---|
| M0 | Phase-0 prototype | 2–3 weeks | 300 | `FMeas(X)` as a cone via Banach embedding, smoke test |
| M1 | Cones | 3–4 months | 2–3 k | §2 (precone, cone, ω-cpo, category), Lemmas 2.8–2.23 |
| M2 | Measurable cones | 2 months | 1.0–1.5 k | §3 (M_X family, Path, FMeas, MCones) |
| M3 | Integrable cones | 3–4 months | 2–3 k | §4 (Pettis, Lem 4.7, Fubini 4.15, completeness 4.16, well-poweredness 4.18) |
| M4 | Internal hom `⊸` | 1.5–2 months | 0.6–1 k | §5.1, §5.2 bilinear, Thm 6.1 |
| M5 | Kernel embedding | 2 months | 0.8–1 k | §6.1, Thm 6.5 (the MVP money theorem) |
| **MVP total** | | **~12 months** | **~7–9 k** | §2–4 + §5.1 + §6 |
| S6 | Tensor & SMCC (axiomatised) | 4–6 months | 3–4 k | §5 with ~10 documented axioms |
| S7 | Stable functions, CCC `SCones` | 6–8 months | 4–6 k | §7 |
| S8 | `!`-comonad (axiomatised) | 4–6 months | 2–3 k | §9 with additional axioms |
| S9 | PCS embedding | 4–6 months | 2–3 k | §10 |
| (—) | Analytic functions | 12+ months | 6–10 k | §8 — explicitly out of scope |

### M0 — Phase-0 prototype (2–3 weeks)

- Define `cone_of (V : completeNormedModuleType R) (P : set V)` HB mixin.
- Realise `FMeas(X)` as `{µ : finite_signed_measure X | µ ≥ 0}` inside a Banach space of signed
  measures. (Alternative: as `{µ : R-valued σ-additive set function | µ ≥ 0 ∧ µ(X) < ∞}` if signed
  measures don't sit well.)
- Verify the five cone axioms; verify ω-completeness via monotone convergence.
- **Go/no-go decision**: if the `\bar R`-vs-`R` plumbing is tolerable and the ω-completeness proof
  is < 200 lines, commit to Phase 0. Otherwise abort and start Phase 0′ (extra ~3 months).

### M1 — Cones (3–4 months, ~2–3 k lines)

- Per Phase decision, build the cone HB structure (Phase 0: as a sub-Banach-space; Phase 0′: as an
  independent `R≥0`-semimodule + norm + order + ω-completeness).
- Derived order `x ≤ y ⇔ ∃ z, y = x + z` and its basic properties (Lemma 2.11, 2.13).
- Continuity = ω-continuity on the unit ball; Lemma 2.10 (uniqueness of ω-continuous extensions),
  Lemma 2.19 (separate-cont ⇒ joint cont, ~150 lines).
- Category `Cones`: morphisms are linear, ω-continuous, `‖f‖ ≤ 1`. Thm 2.18 (products), Thm 2.20
  (equalisers).
- Examples: `\bar R≥0` (the cone `⊥`), `R^n≥0`, sequence cones (paper §2.2 archetypal example
  baseline).

### M2 — Measurable cones (2 months, ~1.0–1.5 k lines)

- Fix `Ar := {R^n | n ∈ ℕ}` (or a richer family if needed — Boolean-decidable).
- Encode the measurability structure `M = (M_X)_{X ∈ Ar}` as a dependent record. Mssep, Mscomp,
  Msmeas, Msnorm.
- Define measurable paths `Path(X, C)` (§3.2.2): a path is a bounded function `X → C` such that
  every test of `C` composes measurably.
- Construct `FMeas(X)` as a measurable cone (§3.2.1): tests are `µ ↦ µ(U)` for `U ∈ σX`. Verify
  Msnorm (the norm equals the sup over tests, here `µ(X) = sup_U µ(U)`).
- Category `MCones` (Def 3.13) and the rescaling functor `αB` (Def 3.15).

### M3 — Integrable cones (3–4 months, ~2–3 k lines)

- **Def 4.1**: the integral as a Pettis-style witness, recovered via `xchoose` + (Mssep).
- **Def 4.3**: integrable cone (`xchoose` succeeds for every path / finite measure).
- **Lemma 4.7** (the workhorse): `I_X^B` is bilinear, ω-continuous, and measurable. This is where
  monotone convergence and dominated convergence get exercised. Cost: ~300–500 lines.
- **Lemma 4.6**: measurability of `s ↦ ∫ φ(s, r) κ(s, dr)` for `κ` a bounded kernel. Check whether
  `mathcomp-analysis.theories.kernel` provides this; otherwise reproduce it.
- **Thm 4.5**: `FMeas(X)` is integrable (reduces to Tonelli for kernels).
- **Thm 4.12**: `Path(X, B)` is integrable (pointwise).
- **Thm 4.15** (Fubini for cones): reduces to scalar Fubini through tests + Mssep.
- **Thm 4.16**: `ICones` is complete (build equaliser's measurability structure carefully).
- **Thm 4.18**: `1` is a separator and coseparator; `ICones` is well-powered.

### M4 — Internal hom `⊸` (1.5–2 months, ~0.6–1 k lines)

- **Def 5.2**: cone `C ⊸ D` of integrable linear maps with `‖·‖ = sup_{‖x‖≤1} ‖f(x)‖` and pointwise
  algebra.
- **Lemma 5.3, 5.4**: `C ⊸ D` is a measurable cone (tests are `γ ▷ m` for paths and `D`-tests) and
  is integrable.
- **§5.2**: bilinear maps `C₁ × C₂ → D` as morphisms `C₁ → C₂ ⊸ D`.

### M5 — Kernel embedding (2 months, ~0.8–1 k lines)

- **Thm 6.1** (the technical heart, ~600 lines): `I_X^B : Path(X, B) ≃ FMeas(X) ⊸ B` is a natural
  isomorphism in `MCones`. Two directions and naturality.
- **Def of `Skern`**: substochastic kernel category, `Skern(X, Y) = B(Path(X, FMeas(Y)))`.
- **Thm 6.5**: the functor `Skern → ICones` sending `X` to `FMeas(X)` and a kernel to its associated
  integrable linear map is fully faithful. Direct corollary of Thm 6.1.

### Stretch milestones

Only attempted after the MVP is shipped, reviewed, and a clear path to deliverable polish exists.
Each is described in 1–2 sentences here; a separate plan document will accompany each when
prioritised.

- **S6** Tensor & SMCC: axiomatise `(- ⊗ B) ⊣ (B ⊸ -)` via ~10 documented Rocq axioms; derive the
  SMC structure (associator, unitors, braiding, pentagon, hexagon) and Thm 5.12, Thm 5.15.
- **S7** Stable functions: the local cone `B_x`, finite differences, total-monotonicity (Def 7.5),
  Thm 7.19 (total monotonicity ↔ n-increasing), Thm 7.30/7.32 (`SCones` CCC).
- **S8** `!`-comonad: axiomatise the SAFT-derived exponential `!` and its co-Kleisli adjunction;
  prove Thm 9.5 (Seely category) and Thm 9.7 (`FMeas(X)` coalgebra).
- **S9** PCS embedding: Definitions 10.2 ff., Thms 10.5–10.10 (PCS as integrable cones, Cantor
  equaliser).

---

## 7. Axiom and trust budget

**MVP target = zero project-level axioms.** Everything sits on top of `mathcomp-analysis` + `boolp`
(which itself uses excluded middle, function extensionality, propositional extensionality, and
`xchoose`/indefinite description). No `Axiom` line in `theories/icones/` or downstream.

The MVP uses, transitively:

- Function and propositional extensionality (`boolp`).
- Excluded middle (`boolp.classic`).
- Indefinite description (`boolp.xchoose`, used to extract the Pettis witness).
- Proof irrelevance (`boolp.Prop_irrelevance`) for subtype HB instances.
- Constructive countable choice for ω-suprema (mathcomp-analysis sequences).
- The Lebesgue integral and its standard theorems (MCT, DCT, Fatou, Tonelli, Fubini) from
  mathcomp-analysis.

**Stretch target (S6, S8) = ~10–12 documented axioms.** Each axiom is a single Rocq statement in a
file `theories/axioms/tensor.v` or `theories/axioms/exp.v`, accompanied by the precise paper
reference. A reviewer can audit the axiom files in isolation; the rest of the development is
constructive given those axioms. Sample shape:

```coq
(* §5, Theorem 5.9 + Mac Lane CWM IV.7.3, adjunction with a parameter.
   Postulated because the paper invokes SAFT (Thm 4.19). *)
Axiom tensor : ICone -> ICone -> ICone.
Axiom tensor_curry : forall (B C D : ICone),
  ICone_iso (icone_lin (tensor B C) D) (icone_lin B (icone_lin C D)).
Axiom tensor_curry_nat : (* naturality in B, C, D *)
  ...
(* Pentagon, hexagon, unit triangles each get their own Axiom. *)
```

---

## 8. Risks and mitigations

| # | Risk | Likelihood | Impact | Mitigation |
|---|------|------------|--------|------------|
| 1 | Phase 0 prototype fails: `FMeas(X)` does not sit cleanly in a Rocq Banach space carrier. | Medium | High (1–3 month delay) | Time-box M0 to 3 weeks; have Phase 0′ Nmodule blueprint ready. |
| 2 | `\bar R` ↔ `R` boundary plumbing dominates proof noise. | High | Medium | Build a `theories/prelude/ereal_extra.v` early; copy idioms from Boldo–Clément–Faissole and from mathcomp-analysis's own kernel chapter. |
| 3 | Lemma 4.7 (bilinearity / ω-continuity of integral) blows up: monotone-convergence-in-the-measure-argument needs new lemmas. | High | Medium | Budget 200 extra lines for the auxiliary "MC under a varying μ" lemma; align with mathcomp-analysis's `Giry` join. |
| 4 | Universe issues when `Ar` varies. | Medium | Medium | Fix `Ar := R^n` family from day one; document scope. Generalisation is a stretch task. |
| 5 | The S6 SMCC axiomatisation misses a coherence diagram. | Medium | Catastrophic (unsoundness) | Cross-check against Mac Lane CWM Ch. VII §1, against Melliès LL semantics survey, and against UniMath's *Displayed Monoidal Categories* (CPP 2024) library. Have a second reviewer audit each axiom. |
| 6 | mathcomp-analysis 1.16 ⇒ 1.17 breakage during the project. | Low | Low | Pin to 1.16.0 in `icones.opam`; have a CI job track 1.17+. |
| 7 | The naming clash with mathcomp's category-theoretic `Cone` (of a diagram) confuses contributors. | Low | Low | Always namespace (`cone.zero`, `cone.add`), and never `Open Scope cone_scope.` in `theories/cones/cone_cat.v`. |
| 8 | M5 (Thm 6.1) takes 1500 lines instead of 800. | Medium | Low | The MVP scope absorbs it; extending to 4 months for M5 is acceptable. |
| 9 | The stretch goals (S6–S9) get demanded before the MVP is solid. | High | Medium | Document scope publicly. Refuse to start S6 until M5 is reviewed and a code-quality pass on M1–M5 is done. |
| 10 | Single-engineer bus factor. | Medium | High | Write detailed `(* Paper §x.y, Lemma z *)` annotations on every nontrivial proof; maintain a `paper-map.md` index. Encourage pair review from a mathcomp-analysis contributor early. |

---

## 9. Open questions / decision points

Items the user (Guillaume Baudart, INRIA) should weigh in on **before M0 starts**:

1. **MVP scope confirmation.** Is "Skern → ICones fully faithful" a satisfying first deliverable, or
   do you want the SMCC structure (with axiomatised `⊗`) included in the MVP? The latter doubles
   the calendar.
2. **Phase 0 vs Phase 0′ default.** Should we try the Banach-positive-cone trick first, or go
   straight to the parallel Nmodule tower?
3. **`Ar` generality.** Acceptable to fix `Ar = {R^n}` for the MVP, or must we keep `Ar` abstract?
   (The kernel embedding works in either case; abstract `Ar` mostly adds section-variable noise.)
4. **Engineer availability.** This is realistically a 9–12 month project for one expert. Is that
   the resourcing? If less, scope down further to "M1+M2+M3 done, M4/M5 deferred".
5. **License & repo.** RESOLVED: CC BY 4.0, matching the underlying LMCS paper.
6. **Communication with the authors.** Ehrhard and Geoffroy are at IRIF; do you want to engage them
   early so the formalisation effort is visible / supported? This may help with axiomatisation
   sanity-checks for §5 SMCC and §9 `!`.
7. **Probabilistic-programming hook.** The motivation for this formalisation presumably ties into a
   broader probabilistic-programming-language verification project (cf. the user's email). Should
   the deliverable include an interpretation of a toy PPL on top of `ICones`, or stop at the
   semantic structure? The toy interpretation is a 1–2 month additional milestone that justifies
   the abstract development.

---

## 10. Immediate next actions (week 0)

1. Set up the repo skeleton: `_CoqProject`, `dune-project`, `Makefile.coq.local`, `icones.opam`,
   `.github/workflows/ci.yml` (Rocq 9.1 + mathcomp 2.5 + mathcomp-analysis 1.16 build matrix).
2. Open `theories/prelude/classical_extra.v`, `ereal_extra.v`, `nonneg_extra.v`, `omegacpo.v` and
   stub them.
3. Start M0: write `theories/cones/phase0_prototype.v` realising `FMeas(R)` as a positive cone in a
   Banach space; aim for "cone axioms verified" within 3 weeks. Either commit to Phase 0 at day 15
   or switch to Phase 0′.
4. Open issues in the repo for each milestone, linked to the paper sections.

---

## Appendix A. Paper navigation index

| Paper element | Source-text line | Rocq target |
|---|---|---|
| Def precone | §2.1, ~paper p. 1:9, txt line 397 | `theories/cones/cone.v` |
| Def cone (norm + ω-cpo) | §2.1 cont., txt line 460 | `theories/cones/cone.v` |
| Thm 2.18 products in Cones | §2.4, txt line 720 | `theories/cones/cone_cat.v` |
| Thm 2.20 equalisers | §2.4, txt line 770 | `theories/cones/cone_cat.v` |
| Def 3.2 measurability struct | §3, txt line 818 | `theories/mcones/mcone.v` |
| §3.2.1 `FMeas(X)` | txt line 951 | `theories/mcones/fmeas.v` |
| §3.2.2 `Path(X, C)` | txt line 981 | `theories/mcones/path.v` |
| Def 4.1 integral | §4, txt line 1142 | `theories/icones/pettis.v` |
| Lemma 4.7 integral bilinear/cont/meas | §4, ~ p. 1:25 | `theories/icones/icone_integral.v` |
| Thm 4.15 Fubini for cones | §4.2, txt ~line 1450 | `theories/icones/fubini.v` |
| Thm 4.16 ICones complete | §4.3, txt line 1540 | `theories/icones/icone_cat.v` |
| Thm 4.18 ICones well-powered | §4.3 | `theories/icones/icone_cat.v` |
| Def 5.2 `C ⊸ D` | §5.1, txt line 2041 | `theories/homs/linhom.v` |
| Lemma 5.4 `C ⊸ D` integrable | §5.1, txt line 2160 | `theories/homs/linhom.v` |
| Thm 6.1 `Path ≃ FMeas ⊸ B` | §6, txt line 2835 | `theories/homs/bilin.v` |
| Thm 6.5 Skern ↪ ICones full+faithful | §6.1, txt line 3038 | `theories/kernels/thm65.v` |

(Indices for §7–§10 deferred to stretch-milestone plan documents.)

---

## Appendix B. What the four expert agents found

- **Mathematics digest** (deep paper read): paper has ~176 numbered statements, hierarchy
  precone → cone → measurable cone → integrable cone is clean and HB-tractable, SAFT is the only
  genuinely non-constructive ingredient. MVP roadmap M1–M5 (this plan revises it).
- **mathcomp-analysis survey**: 1.16.0 installs cleanly on Rocq 9.1 + mathcomp 2.5 + HB 1.10. Has
  full Lebesgue integration, MCT/DCT/Fubini, Giry monad, finite/sfinite/subprobability kernels, but
  no Pettis/Bochner integral, no Scott / ω-cpo, no positive-cone hierarchy, no SMCC / category
  infrastructure. The Nmodule mismatch is real (`Norm` requires Lmodule).
- **Ecosystem survey**: mathcomp-qbs (LLM4Rocq) is the closest analog and a stylistic model.
  Boldo–Clément–Faissole's Bochner integral is the methodological template for the Pettis
  existence proof. No Ehrhard/Geoffroy companion code. Yalla provides LL proof-theory but not
  semantics.
- **Devil's-advocate critique**: rejected the original "build `⊗` axiomatically + parallel Nmodule
  tower" plan. Recommended (a) try Banach-positive-cone first, (b) drop `⊗`/`!` from the MVP,
  (c) target Thm 6.5 as the minimum publishable deliverable, (d) realistic budget is 9–12 months
  for one mathcomp-analysis-grade engineer (~2× the original estimate), (e) flagged Lemma 4.7 and
  Thm 6.1 as the two technical bottlenecks. All of this is reflected in §3 and §6 above.

---

## 11. Iteration 1 retrospective — MVP **delivered** (journal entry, 2026-05)

> This section closes the iteration-1 plan (§0–§10 + Appendices A–B). Nothing
> above is rewritten; this is the honest "what actually happened" record so the
> document reads as a journal across iterations.

**Outcome: shipped.** Paper §2–§6 are formalized in Rocq 9.1.1 + mathcomp-analysis
1.16 + HB 1.10. The headline **Theorem 6.5** — the substochastic-kernel category
`Skern` embeds fully and faithfully into `ICones` — is proved as
`Icones.kernels.thm65.Skern_to_ICones_fully_faithful`, **axiom-clean**: it depends
only on the three classical axioms inherited from `mathcomp-analysis`/`boolp`
(`propositional_extensionality`, `functional_extensionality_dep`,
`constructive_indefinite_description`), with **zero project `Axiom`s and zero
`Admitted`**. ~19.3 k lines across 24 files in `theories/`.

**What matched the plan.** The HB tower precone → cone → MCone → ICone (§4) was
realized as designed; the internal hom `C ⊸ D` was built **concretely** (§5.1, no
axioms); `FMeas`, `Path`, Lemma 4.7, Fubini (Thm 4.15), completeness +
well-poweredness (Thm 4.16/4.18), Thm 6.1 and Thm 6.5 all landed. The three §3
strategic bets held up: the Phase 0′ Nmodule tower was the right call, `Ar` was
kept parametric, and the "state categorical facts concretely on the objects"
approach (what §12 below names *Strategy C*) was validated.

**Honest deviations (corrections to §4/§6).**
- **Coproducts `⊕` were _not_ built.** §4 (line ~224) and §6 list `⊕` as MVP, but
  only products `&` (`icones_prod`) and equalisers (`icones_eq`) were needed for
  completeness and Thm 6.5, and only those exist in `theories/icones/icone_cat.v`.
  `⊕` (paper Thm 4.21 / §4.4) remains a TODO. It is *not* a prerequisite for `⊗`;
  it would only matter if a later development needs coproduct-shaped objects.
- **Well-poweredness (Thm 4.18) is a stub.** `icones_well_powered_bound`
  (`icone_cat.v:1287`) is `:= set B` with no proof that the subobject class injects
  into it, and `icones_subobject_inj` is a one-line restatement of injectivity.
  Harmless for the MVP (Thm 6.5 never uses it) but a **genuine prerequisite** for the
  SAFT route — §13.1 (SA0) must complete it. Completeness, local smallness, and the
  coseparator `1` *are* genuinely proven.
- **`Path` `isICone` cast** was partially deferred during M3 (a representation
  cast left for later); revisit if a downstream proof needs the full instance.
- **File layout** settled as `prelude/ cones/ mcones/ icones/ homs/ kernels/`,
  matching the plan's intent.

**Post-MVP polish (after §2–§6 closed).** A `mathcomp-rocq-guide` style audit; a
6-chapter LaTeX **blueprint** + GitHub Pages CI (`build.yml` gating Rocq build +
`blueprint.yml`); relicense to **CC BY 4.0**; the paper PDF scrubbed from git
history (references point to arXiv/LMCS); and an idiomatic `[set: T] → setT`
notation sweep across the 82 `measurable_fun` sites.

**Effort reality.** The devil's-advocate "~2× the first estimate" rule (Appendix B)
held; budget iteration 2 accordingly (§12.7).

---

## 12. Iteration 2 — Tensor `⊗` and Exponential `!` (**planned**)

> **⚠ Superseded by §13 (decision 2026-05-21).** The project chose the *axiom-free*
> path: prove SAFT and **construct** `⊗`/`!` from it (§13). This §12 (axiomatized) is
> **retained**, not deleted: its universal-property interface is reused verbatim as
> §13's staging contract, and it remains the recommended *fallback* / staged-first
> path if the SAFT proof bogs down. Read §13 for the live plan.

**Goal.** Extend `ICones` from a (multiplicative-additive) linear structure with a
concrete `⊸` to a full **symmetric monoidal closed category** (`⊗`, §5) carrying an
**exponential `!`** via a linear-non-linear adjunction (§7+§9). These are the
structures a higher-order probabilistic language needs: `⊗` gives the SMC/MELL
core; the co-Kleisli of `!` is the **call-by-name** model, and the monad induced by
the LNL adjunction on the cartesian side is the **call-by-value** model. Fixpoints
(§9.2) give recursion.

This iteration *refines* (does not replace) §3.2's "stretch choice B". The plan
below is the synthesis of a 4-expert planning pass (see **Appendix C**).

### 12.0 Strategy decisions (team consensus)

- **D1 — Axiomatize `⊗`/`!` _minimally_, then _derive_ coherence.** The paper builds
  both via the Special Adjoint Functor Theorem (Thm 4.19), whose existence step is
  irreducibly non-constructive; no concrete carrier for `B ⊗ C` is given (Remark
  5.1). So a constructive `⊗` is rejected (still §3.2 option A — "never"). But the
  axiom surface is far smaller than §7's "~10 coherence axioms": postulate **only**
  the representing object + the universal homset bijection + its naturality, and
  **derive** the associator/unitors/braiding and pentagon/hexagon/triangle as
  *theorems* — for `⊗` via **Prop 5.14** (agreement on pure tensors ⇒ equal), for
  `!` via **Lemma 9.2/9.3**. Net: ~3–4 axioms for `⊗`, ~4–6 for `!`, all in
  isolated `theories/axioms/*.v` files. This removes risk #5's "missed coherence
  diagram → unsoundness" by not hand-stating coherence at all.
- **D2 — Strategy C: stay concrete; no foreign category library.** The MVP, the
  closest precedent (`LLM4Rocq/mathcomp-qbs`, a concrete CCC in HB), and the paper
  itself (§5 intro: the direct approach is tractable "because our morphisms are
  functions") all argue for stating SMCC/`!`/Seely concretely on `ICone` +
  `icones_hom`. Surveyed alternatives are all worse fits: **UniMath** (best
  monoidal/LL infrastructure but univalent foundations — incompatible carriers),
  **jwiegley/category-theory** (complete drop-in but `Equations` + `crelation`
  setoids, no HB/mathcomp interop, universe clashes), **affeldt-aist/monae**
  (HB+mathcomp concrete categories — the only stack-compatible one, but no
  monoidal/closed/comonad). Use external libs **only** as machine-checked
  coherence-law inventories to diff our axioms against.
- **D3 — Stable route; defer analytic.** Build `!` over the CCC of **stable**
  measurable functions `SCones` (§7). Defer **analytic** functions `ACones` (§8 —
  the paper's hardest section: polarisation, Taylor/homogeneous-polynomial
  expansion) and the **PCS** embedding (§10). §9 is written route-agnostically, so
  analytic can be slotted later by *re-instantiating* §9, not rewriting it.
- **D4 — Construct fixpoints, don't axiomatize.** The ω-cpo enrichment
  (`prelude/omegacpo.v`) already supports least fixed points; `Y` lives in the CCC
  and needs no new axioms.

### 12.1 Prerequisites / gap-closing (before S6)

| Item | Why | Paper / code |
|---|---|---|
| `icones_iso` record (fwd+bwd `icones_hom` + round-trips) | no iso record exists yet | infra (Yoneda/Lemma 1.1) |
| Functorial action `h ⊸ g : (C₁⊸D₁) → (C₂⊸D₂)` | absent (`grep` finds no `linhom_map`) | Def 5.7 / Prop 5.8, txt 2416 |
| Thm 5.9: `C ⊸ −` preserves products & equalisers | the *soundness justification* the `⊗` axiom cites | §5.3, txt 2466–2538 |
| (deferred) coproducts `⊕` | only if a later object needs it; **not** needed for `⊗` | Thm 4.21, txt 1808 |

### 12.2 S6 — Tensor `⊗` + SMCC (paper §5.2–§5.5) — *the minimum publishable deliverable*

- **Axioms** (`theories/axioms/tensor.v`, ~3–4): `tensor : ICone→ICone→ICone`; the
  natural bijection `Φ : ICones(B⊗C,D) ≃ ICones(B, C⊸D)` (Thm 5.9 / Eq 5.1, txt
  2553); `Φ` naturality in `D` and in `B,C`.
- **Derived as theorems**: `τ` and `x⊗y := τ x y`; **Thm 5.12** `Φ` is an iso ⇒ SMC
  closure `(B⊗C)⊸D ≃ B⊸(C⊸D)` (txt 2619); **Thm 5.13** `‖x⊗y‖=‖x‖·‖y‖` (txt 2700);
  **Prop 5.14** tree-extensionality (txt 2730); associator/unitors/braiding (via
  `Φ`, Eqs 5.2–5.4); pentagon/hexagon/triangle; **Thm 5.15** SMCC packaging.
- **Unit object**: the scalar cone `R≥0` (the registered `cone_one_car`, the paper's
  `1`/`⊥`), already an `ICone` (`examples_icone.v`).
- **Files**: `homs/linhom.v` (+ `linhom_map`), new `homs/linhom_lim.v` (Thm 5.9),
  `axioms/tensor.v`, `homs/tensor.v`, `homs/smcc.v`.
- **Headline**: "the cone-integral model is a mechanized SMCC (a model of
  MELL-without-`!`)". Self-contained; reuses the concrete `⊸`/bilinear layer.

### 12.3 S7 — Stable CCC `SCones` (paper §7) — fully constructive, no axioms

| Sub | Content | Paper | txt |
|---|---|---|---|
| S7a | local cone `B_x`, gauge norm | §7.1, Lem 7.1–7.2 | 3131 |
| S7b | total monotonicity, stable cone `B ⇒s C` (built like `linhom.v`) | Def 7.5/7.7/7.10 | 3211 |
| S7c | finite differences `Δ`, Thm 7.19, composition keystones — **the time sink** | §7.3 | 3419 |
| S7d | CCC `SCones`: `Ev`/curry, `Der` preserves limits | Thm 7.30/7.32/7.34 | 3890 |

Files: `theories/stable/{local_cone,totmono,stablehom,findiff,scones_cat}.v`.
Independent of `⊗`/`!` — a standalone **cartesian-closed** model (CBN λ-calculus).

**Reusable assets & de-risking (scout, 2026-05).** No proof assistant has a
formalized stable/analytic CCC or `!` (first-of-kind), but the §7.3 combinatorics
— the time sink — can lean on existing tooling rather than be built from nothing:
- *Native mathcomp infrastructure* turns the sign-split power-sets `P⁻(n)/P⁺(n)`
  and alternating-sum identities into routine `bigop` algebra: `finset.powerset` +
  `card_powerset`, `bigID`/`reindex`/`telescope_big`, `ssralg.signrE`/`exprNn`,
  `binomial`'s `'C(n,k)` + Vandermonde; the **`multinomials` package** (`mpoly`,
  installed 2.4.0 — add to `icones.opam`) covers the symmetric/multilinear side.
- *mathlib4 as a vetted spec to PORT* (not import): `Algebra.Group.ForwardDiff`
  (finite differences, Gregory–Newton, the alternating-binomial `n`-th difference)
  and `…/IteratedDeriv/FaaDiBruno`. Load-bearing transferable idea: index the higher
  chain rule by **ordered partitions of `Fin n`**, not raw subsets — this sidesteps
  the nested double induction of the Lem 7.26/7.27 composition keystones.
This downgrades §7.3 (risk #2) from "build from scratch" to "port a known-good
blueprint onto solid mathcomp infrastructure". See Appendix D.

### 12.4 S8 — Exponential `!` + LNL + Seely (paper §9)

- **Axioms** (`theories/axioms/exp.v`, ~4–6): the left adjoint `E` of `Der`, the
  natural bijection `Θ`, the unit `nl`, and their naturality (`!B := E(Der B)`,
  txt 5064; no concrete `E` — Remark 9.1).
- **Derived**: `der`/`dig`/`!f` + comonad laws (Lem 9.2/9.3); Seely isos
  `!(A&B) ≅ !A⊗!B`, `!⊤ ≅ I` + **Thm 9.5** (needs S6's `⊗`); the `FMeas(X)`
  coalgebra **Thm 9.7** (reuses `dirac_path`/Thm 6.1 from `bilin.v`).
- **Files**: `theories/exp/{comonad,seely,coalgebra}.v` + `axioms/exp.v`.
- **Depends on**: S6 (`⊗`, for Seely) **and** S7 (the CCC).
- **Axiom-free alternative (recorded, _not_ the path)**: the Melliès–Tabareau–Tasson
  *free exponential* gives `!A = limₙ A^{≤n}`, with `A^{≤n}` the equalizer of the
  `n!` symmetries on `(A & I)^⊗n` — needing `⊗`, products, equalisers, countable
  limits (ICones has all via completeness) **plus two `⊗`-distributivity
  conditions**. Crubille–Ehrhard–Pagani–Tasson (FoSSaCS 2017) proved PCS's `!` *is*
  exactly this free comonoid, and PCS embeds in ICones, so the cone `!` is morally
  free. **But** it does not remove the `⊗` axiom, it adds the `Sₙ`-actions and two
  distributivity theorems over an *opaque* SAFT tensor, and Ehrhard–Geoffroy
  deliberately avoid it ("the special adjoint functor theorem … avoids providing
  explicit combinatorial constructions"). Verdict: optional future *hardening* of
  the de-axiomatization goal, attractive only once `⊗` has an explicit description —
  **axiomatized-SAFT stays the path**. (mathcomp-analysis ships `completeType`
  predicates but no completion *functor* à la mathlib `UniformSpace.Completion`, so a
  completion-based `⊗`/`!` starts from scratch.) See Appendix D.

### 12.5 Fixpoints (§9.2) + optional capstone

- `theories/exp/fixpoint.v`: least fixed point `Y` in the CCC via `omegacpo`.
  **Constructed**; depends only on S7d + `omegacpo` (**not** on `!`), so it can ship
  right after S7.
- *Optional* capstone (defer): a toy CBV/CBPV PPL interpreted on `ICones`/`SCones`,
  closing open question §9-#7. Tie the value/computation split to "values = cone
  elements, computations = sub-distributions"; this is where CBN (co-Kleisli of `!`)
  vs CBV (Kleisli of the LNL-induced monad) is made concrete.
- *In-stack scaffolding for the capstone (scout, 2026-05)*: Affeldt–Cohen–Saito's
  **s-finite kernels + measure monad in mathcomp-analysis** (CPP 2023 / TOPLAS 2025)
  is reusable monad/kernel infrastructure in our exact stack and supplies an
  intrinsically-typed PPL-syntax pattern (first-order, no `!`). Paper-only *recipes*
  for the higher-order layer: Hamano's linear-exponential-comonad over s-finite
  kernels (via integration-orthogonality) and Vákár–Kammar–Staton ωQBS (cpo ⊕ base,
  for recursion + higher-order). See Appendix D.

### 12.6 Dependency DAG

```
 MVP (done): ICone tower, ICones cat (& products, equalisers, completeness,
             well-poweredness), ⊸ (concrete), FMeas, Path, Thm 6.1, ω-cpo, SAFT
        │
 12.1 prereqs: icones_iso · h⊸g (Def 5.7) · Thm 5.9 (⊸ preserves lim)
        │
 S6  ⊗ + SMCC (axioms/tensor.v + derived coherence)         ── min. publishable
        │                                  │
        │                                  └────────────┐
 S7  stable CCC SCones (constructive, independent of ⊗)   │
        │                                                 │
        ├──► S7d ──► S9d fixpoints (ω-cpo only; NOT !)     │
        │                                                 ▼
        └──────────────────────────►  S8  ! + LNL + comonad (axioms/exp.v)
                                            ├─ Seely isos  (needs S6 ⊗ + S8)
                                            └─ FMeas coalgebra (needs Thm 6.1)
   (§8 analytic ACones hangs to the side: re-instantiate §9 with C = ACones)
```

### 12.7 Axiom budget & effort

**New axioms: ~7–10**, all in `theories/axioms/{tensor,exp}.v`, each annotated with
its paper equation; everything else (coherence, comonad/Seely laws, the stable CCC,
fixpoints) is constructive. A reviewer audits the two axiom files in isolation
against the **coherence checklist**: Mac Lane *CWM* Ch. VII (pentagon/triangle/
hexagon + naturality), Melliès' LL-semantics survey and Bierman's new-Seely
coherence (Seely-iso naturality + comonad laws), with UniMath `Monoidal.*` and
jwiegley `Monoidal.v`/`Closed.v` as machine-checked law inventories to diff against.

| Milestone | Nominal | Realistic (~2×, one expert) |
|---|---|---|
| 12.1 prereqs + **S6** `⊗`+SMCC | 4–5.5 mo | **8–11 mo** |
| **S7** stable `SCones` (§7.3 dominant) | 6–8 mo | 11–15 mo |
| **S8** `!` + LNL/Seely | 4–6 mo | 7–11 mo |
| §9.2 fixpoints | within S8 | 1–2 mo |
| toy PPL (optional) | 1–2 mo | 2–4 mo |

Minimum deliverable (S6) ≈ **8–11 months**. S6 + S7 (strongest standalone story)
≈ 18–24 months. **Defer/cut**: §8 analytic `ACones`, §10 PCS.

### 12.8 Risks (iteration 2)

| # | Risk | Lik. | Impact | Mitigation |
|---|------|------|--------|------------|
| 1 | A coherence/naturality axiom is mis-stated → silent unsoundness | Med | Catastrophic | Derive coherence (Prop 5.14 / Lem 9.2) instead of postulating it; isolate axioms in `axioms/*.v`; second-reviewer audit; cross-check Mac Lane/Melliès; sanity-test `⊗` against `Skern`'s tensor on `FMeas`. |
| 2 | §7.3 finite-difference / `n`-increasing combinatorics balloons | High | High | Prototype Lem 7.16/7.17/7.26/7.27 in week 1 of S7 *before committing*; build `Pᵉ(n)`/`Δ` as standalone `bigop`/`finset` lemmas; if blocked at 6 wk, ship S6 alone. |
| 3 | Scope creep into §8 analytic or a full PPL | High | High | Publicly fix scope at "S6, optionally S7"; §8/PPL only as labelled optional capstones. |
| 4 | Pressure to *construct* `⊗`/`!` (option A) | Med | High | Document: SAFT existence is non-constructive and no category/SAFT layer exists in `theories/`; option B is the deliverable. |
| 5 | An abstract category layer triggers HB universe issues | Low–Med | Med | Strategy C: concrete `Record` morphisms + pointwise isos (as in `icone_cat.v`); no generic `Category`/`Functor` tower; keep `Ar` fixed where possible. |

### 12.9 Open questions for iteration 2

1. Is the **toy PPL** capstone in scope, and if so **CBV (CBPV)** or **CBN**? (CBV
   is the natural target for probabilistic programming; see the CBN/CBV discussion —
   `!`-co-Kleisli is CBN, the LNL-induced monad is CBV.)
2. Engage **Ehrhard & Geoffroy** to sanity-check the §5/§9 axiom files? (Recommended
   given the soundness stakes of D1.)
3. Build coproducts `⊕` now (close the §11 gap) or only on demand?

---

## 13. Iteration 2 (revised) — axiom-free path: tensor → SAFT → exponential (**live plan**)

**Decision (2026-05-21).** Pursue the **axiom-free** route: *prove* SAFT for `ICones`
(Riehl, *Category Theory in Context*, Thm 4.6.10 / Cor 4.6.14 — the paper's Thm 4.19)
and **construct** the tensor `⊗` and the exponential `!` from it, rather than
postulating them. End state: zero project axioms (only the inherited `boolp` classical
base, as in the MVP). Supersedes the axiomatized §12, which is retained as the staging
contract / fallback. Synthesized from a second 4-expert pass (Appendix E).

### 13.0 Strategy, the well-poweredness gap, and the staging decision

- **Strategy C unchanged**: build everything *concretely* on `ICone`/`icones_hom`; no
  abstract `Category` typeclass, no foreign category library.
- **⚠ Prerequisite correction — well-poweredness is a stub.** SAFT needs `ICones`
  complete + locally small + a small coseparating set + intersections of subobjects.
  The MVP genuinely proves completeness (`icones_prod` over arbitrary `I : Type` +
  `icones_eq`, with uniqueness `icones_tuple_unique`/`icones_eq_med_unique`), local
  smallness (homs are a type), and the coseparator `1` (`icones_coseparator`). **But
  `icones_well_powered_bound` (`icone_cat.v:1287`) is a stub** (`:= set B`, no injection
  proof). So well-poweredness + the subobject-intersection machinery are *not* done;
  completing them is the bulk of M-SAFT (13.1), not free.
- **Recommended sequencing — decouple via the interface.** Proving SAFT is the
  riskiest, lowest-leverage piece, and a SAFT-built `⊗`/`!` is an *opaque* object used
  only through its universal property (Riehl p.165; paper Remark 5.1/9.1) — so
  downstream proofs are identical whether that property is *asserted* or *derived*.
  Therefore specify the SAFT conclusion as a **section-local interface** (`==` §12's
  axioms), build tensor (13.2), stable CCC (13.3) and exponential (13.4) against it,
  and run **M-SAFT (13.1) as its own track that discharges the interface** → fully
  axiom-free, no downstream rework. This reaches the axiom-free goal while letting
  `⊗`/`SCones`/`!` progress in parallel. (Strict alternative: make M-SAFT a hard gate
  first — front-loads ~5–8 months before any `⊗` result.)

### 13.1 M-SAFT — proved representability for ICones (Riehl 4.6.10/4.6.11/4.6.14)

**Approach: option B — a bespoke representability theorem stated directly on
`icones_hom`** (no abstract category layer; matches MVP style and sidesteps universe
machinery, since homs are types, the coseparating set is the single object `1`, and the
subobject family of `p` is indexed by `set p`). Construction (Lemma 4.6.11 with
`Φ = {1}`): form the power `p := icones_prod (fun _ : J => 1)` over `J := U(1)`
(resp. `F 1`), then the intersection `i ↪ p` of all subobjects of `p`; `i` is initial
in the inlined comma `s ↓ U`. Encode the wide intersection as a **single binary
`icones_eq` of two product maps** (keeps HB instances on the existing `cones_eq_car`,
avoiding universe trouble). Initiality: existence from completeness (`icones_eq_med`),
uniqueness from the coseparator.

| # | Sub-milestone | Reuses / fixes |
|---|---|---|
| SA0 | **Complete the well-poweredness proof** (Thm 4.18): subobjects of `B` inject into `set B` | replaces the `icone_cat.v:1287` stub |
| SA1 | `is_icones_mono`, `icones_subobject` record | SA0 |
| SA2 | wide equalizer via binary `icones_eq` of two product maps; mediating arrow + uniqueness | `icones_prod`, `icones_eq`, `icones_eq_med` |
| SA3 | power `p = ∏_J 1`; intersection `i ↪ p` | `icones_prod` (arb. `I`), `icones_coseparator` |
| SA4 | initiality of `i` in `s ↓ U` (the key lemma) | `icones_coseparator`, `icones_hom_eq` |
| SA5 | package `icones_left_adjoint` (4.6.10) + `icones_continuous_representable` (4.6.14); export | SA1–SA4 |

**Exported interface** (consumed by 13.2/13.4; `==` §12's axioms once proved):
`icones_left_adjoint : ∀ (U : ICones→C continuous), { L & L ⊣ U }` and
`icones_continuous_representable : ∀ (F : ICones→Set continuous), { r & ICones(r,−) ≅ F }`.
File: `theories/icones/representable.v`. Effort ≈ 2.5–3.5 mo nominal / **5–8 mo
realistic**; the highest-risk milestone of the iteration (the subobject-intersection
machinery does not exist yet).

### 13.2 Tensor `⊗` + SMCC via SAFT (route b) — paper §5.2–§5.5

Prove `(C ⊸ −) : ICones → ICones` continuous (**Thm 5.9**, concrete/pointwise on
`icones_prod`/`icones_eq`), feed it to `icones_left_adjoint`, and *define* `(− ⊗ C)` as
the resulting left adjoint with the natural bijection
`Φ : ICones(B⊗C,D) ≃ ICones(B, C⊸D)`. Route (b) is the paper's literal path and does
less work than representing the bilinear functor (which needs Def 5.6's
`Bilin = B⊸(C⊸D)` — route (b)'s codomain). Prereqs: `icones_iso` record; `linhom_map`
(`h ⊸ g`, Def 5.7, absent today); **Thm 5.9**. Derived as theorems: `τ`/`x⊗y`;
**Thm 5.12** closure; **Thm 5.13** `‖x⊗y‖=‖x‖‖y‖`; **Prop 5.14** pure-tensor
extensionality; associator/unitors/braiding (unit `= cone_one_car`);
pentagon/hexagon/triangle (via Prop 5.14); **Thm 5.15** SMCC. Opaque carrier is fine —
every proof goes through `Φ`/`τ` + Prop 5.14, as the paper does. Files:
`homs/linhom.v`(+`linhom_map`), `homs/icones_iso.v`, `homs/linhom_lim.v` (Thm 5.9),
`homs/tensor.v`, `homs/smcc.v`. Effort ≈ 8–11 mo realistic. Top risks: norm-wrapper
friction at the `icones_hom` (`‖f x‖≤‖x‖`) boundary; Thm 5.9 *equaliser* preservation
(prototype first).

### 13.3 Stable CCC `SCones` (§7) — constructive, the mountain

Independent of `⊗`/`!`/SAFT. `B ⇒ₛ C` clones the `linhom.v` skeleton.

| Sub | Content | Paper · txt | Effort |
|---|---|---|---|
| S7a | local cone `B_x`, gauge norm | §7.1, 3131 | 3–4 wk |
| S7b | total monotonicity, stable cone `B ⇒ₛ C` | §7.2, 3211 | 4–6 wk |
| S7c | finite differences `Δ`, Thm 7.19, composition keystones — **the time sink** | §7.3, 3419 | **10–16 wk** |
| S7d | CCC `SCones`, `Ev`/curry, `Der` continuous (Thm 7.34) | §7.4, 3890 | 4–6 wk |

S7c: **port** mathlib4 `ForwardDiff` + `FaaDiBruno` onto native
`bigop`/`finset`/`binomial`/`multinomials`(`mpoly`), indexing the higher chain rule by
**ordered partitions of `Fin n`** (not raw subsets) to kill the nested double-induction.
Files: `theories/stable/{local_cone,totmono,stablehom,findiff,scones_cat}.v`. Effort
≈ 11–15 mo realistic (S7c dominant).

> **✅ DONE (2026-05-22) — carrier redesign + S7b complete.** The stable cone needed a
> **B_B-restricted carrier** (the paper's stable functions are `f : B_P → Q`): the
> original `stablehom` wrapped a *total* function with unconstrained off-`B_B` values, so
> `(Normz)` failed. Resolved via a **canonical 0-extension field** `sh_offball`
> (`theories/stable/stablehom.v`; `totmono.v` untouched), carried all the way through
> `isPrecone → isCone → isMCone → isICone`: **`B ⇒ₛ C` is now a full `iconeType`** (S7b
> done, axiom-clean). Any later S7c/S7d code builds on this carrier. This was the third
> of *five* recurring §7 "MVP linear-tailoring" gaps fixed en route ((Msnorm)→strict
> interior; ω-cont→radius-aware `cone_sup_at`; carrier→0-extension;
> difference-is-stable→Lemma 7.12 backward; integral ω-cont→`test_of_sup_at`).

### 13.4 Exponential `!` via SAFT — paper §9, axiom-free

`!B := E(Der B)` with `E ⊣ Der` from `icones_left_adjoint` applied to the forgetful
`Der : ICones → SCones`. The single input to feed SAFT is **Thm 7.34 (`Der` preserves
small limits, from S7d)**. Derived as theorems (no axioms): `der`/`dig`/`!f` + comonad
laws (Lem 9.2/9.3) — SAFT only; Seely isos `!(A&B)≅!A⊗!B`, `!⊤≅I` + **Thm 9.5** — need
`⊗` (13.2); `FMeas(X)` coalgebra **Thm 9.7** — reuses Thm 6.1 (`bilin.v`).
**SAFT-for-`!` is recommended over the MTT free exponential**, which even with `⊗`
constructed still needs the `Sₙ`-actions, the limit tower, and two `⊗`-distributivity
coherences (more work); keep MTT only as future hardening (Remark 9.6). Files:
`theories/exp/{comonad,seely,coalgebra}.v`. Effort ≈ 7–11 mo realistic.

### 13.5 Fixpoints (§9.2) — constructive

`theories/stable/fixpoint.v`: `Y(f) = sup_n fⁿ(0)` via the existing `omegacpo`; depends
only on **S7d + ω-cpo** (not on `!`/`⊗`), ships right after S7. Effort 2–3 wk. Note (per
the PPL analysis): a small higher-order PPL needs only `SCones` + fixpoints — *not*
`⊗`/`!` — so this plus 13.3 already suffices for a CBN/CBV PPL semantics if that, rather
than the linear-logic structure, is the goal.

### 13.6 Dependency order

```
MVP (done) ─► SAFT interface (13.0 contract, == §12 axioms, temporary)
   │                                              │
   ▼                                              └─► M-SAFT (13.1) discharges it
13.2 ⊗+SMCC (Thm 5.9 → left adjoint)                  (incl. fixing the well-powered stub)
13.3 SCones (§7, constructive, independent) ─► S7d ─► fixpoints (ω-cpo only)
                                                 │
                                                 └─► 13.4 ! (feed Thm 7.34 to SAFT)
                                                        ├─ der/dig/comonad  (SAFT only)
                                                        ├─ Seely / Thm 9.5  (needs ⊗)
                                                        └─ FMeas coalgebra  (needs Thm 6.1)
```

### 13.7 Effort, risks & the staged recommendation

| Milestone | Realistic (~2×, one expert) |
|---|---|
| M-SAFT (13.1, **new**, incl. well-powered proof) | 5–8 mo |
| ⊗ + SMCC (13.2) | 8–11 mo |
| SCones (13.3, §7.3 dominant) | 11–15 mo |
| ! + Seely (13.4) | 7–11 mo |
| fixpoints (13.5) | 1–2 mo |

Axiom-free end-to-end ≈ **31–45 months** (one expert). Staged: a conservative
axiomatized `⊗` (S6) ships at **8–11 mo**, with M-SAFT discharging it later.

| # | Risk | Lik. | Impact | Mitigation |
|---|---|---|---|---|
| 1 | Gating the iteration on proving SAFT first triples time-to-first-result | High | Schedule | Stage: build against the SAFT *interface*; M-SAFT discharges it later (13.0). |
| 2 | Subobject-intersection / well-powered proof doesn't exist, underestimated (stub today) | High | High | Scope M-SAFT honestly (5–8 mo); prototype `i ↪ 1^J` in week 1. |
| 3 | §7.3 finite-difference combinatorics balloons | High | High | Port mathlib `FaaDiBruno` (ordered-partition indexing); build the `bigop` sign-split layer first. |
| 4 | HB universe/size blow-up in the wide-equalizer carrier | Med | Med | Keep HB instances on `cones_eq_car`; confine `set p` to map definitions; no abstract `Category` tower. |
| 5 | SAFT buys only soundness/cleanliness (opaque object) — over-investment vs §7.3 | High | Low–Med | Accept consciously; don't let M-SAFT starve the §7.3 critical path. |

**Independent review's bottom line.** The axiom-free end state is the right *goal*, but
the cheapest route to it is to **build `⊗`/`!` against the §12 axiomatized interface
first** (sound, conservative, ~8–11 mo to a citable SMCC result), **then discharge those
axioms via M-SAFT** — rather than front-loading the riskiest, opaquest,
lowest-downstream-content proof. Either ordering reaches the identical destination:
axiom-free `⊗` and `!`.

---

## Appendix C. Iteration-2 expert team findings

- **Tensor architect** (§5.2–§5.5): reassessed construct-vs-axiomatize given the
  concrete `⊸`/bilinear layer ⇒ **"Option B-minimal"**: axiomatize only `Φ` +
  naturality (~3–4 axioms), derive all SMC coherence via Prop 5.14. Flagged the
  three real prereqs (`icones_iso`, `h⊸g`, Thm 5.9) and the **coproducts-`⊕` gap**
  in the code. Norm-wrapper friction at the `icones_hom` boundary is the subtle
  technical risk.
- **Exponential architect** (§7–§9): `!` is never built directly — it is the SAFT
  left adjoint over a CCC of non-linear maps. **Take the stable route (§7), defer
  analytic (§8)**; §9 is route-agnostic. Detailed S7a–d / S9a–d split; only ~4–6
  axioms (the adjunction), the rest constructive; **fixpoints don't depend on `!`**.
  §7.3 finite differences is the dominant cost (~3–4 mo).
- **Rocq/HB scaffolding + ecosystem**: confirmed **Strategy C** is already in force
  (no abstract `Category` typeclass in `theories/`); surveyed UniMath / jwiegley /
  monae / mathcomp-qbs — all corroborate concrete over a foreign library. Provided
  HB/axiom-file sketches and the coherence-audit checklist. Fixpoints: construct.
- **Devil's-advocate / sequencing**: `⊗` and `!` **axiomatized, not constructed**
  (SAFT existence is irreducible). Minimum publishable = **S6 alone**; order
  prereqs → S6 → S7 → S8 → fixpoints → optional PPL. Realistic effort with the ~2×
  rule: S6 ≈ 8–11 mo, S6+S7 ≈ 18–24 mo. Top calendar risk is §7.3; top soundness
  risk is a mis-stated coherence axiom. **Defer §8 analytic and §10 PCS.**

---

## Appendix D. Iteration-2 reusable-assets scouting (web search, 2026-05)

A 4-scout web search for anything that helps build `!`. **Headline: nothing
importable builds `!` for us** — no proof assistant has a formalized LL exponential
/ Seely / Lafont / linear-non-linear category, nor any cone/PCS exponential, in any
foundation (let alone mathcomp/HB). But three useful assets surfaced:

- **§7.3 de-risking (the practical win).** mathcomp's
  `bigop`/`finset`/`binomial`/`ssralg` + the installed `multinomials` (`mpoly`,
  2.4.0) cover the subset/alternating-sum and symmetric/multilinear infrastructure;
  **mathlib4** has fully formalized finite differences (`ForwardDiff`,
  Gregory–Newton) and **Faà di Bruno** (via `OrderedFinpartition`) as a spec to
  *port* — index by ordered partitions of `Fin n`, not raw subsets. ⇒ folded into
  §12.3.
- **MTT free exponential (axiom-free `!`, expensive).** Explicit formula
  `!A = limₙ`(equalizer of `Sₙ` on `(A & I)^⊗n`); *proven* to be PCS's `!` (Crubille
  et al., FoSSaCS 2017), and PCS embeds in ICones — but it adds distributivity
  theorems over an opaque `⊗` and is *not* what Ehrhard–Geoffroy use. ⇒ folded into
  §12.4 as optional hardening.
- **In-stack scaffolding & blueprints.** Affeldt–Cohen–Saito s-finite kernels +
  measure monad in mathcomp-analysis (our exact stack; first-order, no `!`); and the
  paper-only recipes Hamano (`!` over s-finite kernels via integration-orthogonality)
  and Vákár–Kammar–Staton ωQBS (recursion + higher-order); the Isabelle/HOL QBS stack
  (exponentials over a measure base); UniMath's CPP-2024 *Displayed Monoidal
  Categories for LL* (architectural template for the comonoid/LNL target — univalent,
  not importable). ⇒ §12.5.
- **To verify before relying on:** a claimed Rocq free-CCC universal-property
  formalization (arXiv:2402.11727, library/foundation unconfirmed); the absence of a
  completion *functor* in mathcomp-analysis (only `completeType`).

Key sources: mathlib `Algebra.Group.ForwardDiff` and `…/IteratedDeriv/FaaDiBruno`;
Melliès–Tabareau–Tasson, *An explicit formula for the free exponential modality of
LL* (ICALP 2009 / MSCS 2018, hal-01992148); Crubille–Ehrhard–Pagani–Tasson, *The
Free Exponential Modality of PCS* (FoSSaCS 2017); Hamano, arXiv:1909.07589;
Affeldt–Cohen–Saito, s-finite kernels in mathcomp-analysis (CPP 2023); Ahrens–
Matthes–van der Weide–Wullaert, *Displayed Monoidal Categories for the Semantics of
LL* (CPP 2024, hal-04375376); Ehrhard–Pagani–Tasson, *Measurable Cones and Stable,
Measurable Functions* (arXiv:1711.09640).

---

## Appendix E. Iteration-2 (revised) axiom-free expert team findings

The second 4-expert pass that produced §13 (the axiom-free SAFT path).

- **SAFT-for-ICones architect**: recommend a *bespoke concrete* representability theorem
  on `icones_hom` (option B), not an abstract category layer — coseparator `{1}`,
  intersection of subobjects of a power of `1` encoded as one binary `icones_eq` of
  product maps (keeps HB instances on `cones_eq_car`, sidesteps universes). Exports
  `icones_left_adjoint` / `icones_continuous_representable`. SA0–SA5; ~2.5–3.5 mo
  nominal.
- **Tensor-via-SAFT architect**: route (b) — prove `(C⊸−)` continuous (Thm 5.9), read
  off `(−⊗C)` as the SAFT left adjoint; derive the SMCC via Prop 5.14. Opaque carrier
  handled through `Φ`/`τ`. Risks: norm-wrapper friction, Thm 5.9 equaliser preservation.
- **Exponential-via-SAFT architect**: build the §7 stable CCC, then `!` = SAFT applied
  to `Der` (feed Thm 7.34); comonad/Seely/coalgebra derived. SAFT-for-`!` beats MTT even
  with `⊗` constructed. §7.3 is the dominant cost (port mathlib `ForwardDiff`/
  `FaaDiBruno`, ordered-partition indexing).
- **Devil's-advocate**: **found that `icones_well_powered_bound` is a stub** (so a SAFT
  hypothesis is unproven — now §13.1 SA0); a SAFT-built object is opaque and buys only
  soundness/cleanliness; axiom-free-first ≈ 31–45 mo vs axiomatized S6 ≈ 8–11 mo.
  **Recommends staging**: ship `⊗`/`!` against the axiomatized interface first, discharge
  via M-SAFT later — same axiom-free destination, far less schedule risk.

End of plan.
