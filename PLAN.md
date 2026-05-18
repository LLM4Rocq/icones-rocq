# Formalization plan: *Integration in Cones* (Ehrhard & Geoffroy, LMCS 2025)

Paper: <https://arxiv.org/abs/2212.02371> · LMCS DOI 10.46298/LMCS-21(1:1)2025 · 98 pages
Source extracted at `paper/icones.txt`. Project root: `/home/rocq/icones`.

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
├── paper/
│   ├── icones.pdf
│   └── icones.txt                         -- extracted, source of truth
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
5. **License & repo.** Likely MIT / CECILL-C to match mathcomp's licensing — confirm.
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

End of plan.
