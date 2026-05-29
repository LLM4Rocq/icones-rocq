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
`Admitted`** anywhere (~57k lines across 58 files). Run [`./verify.sh`](./verify.sh) to
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

## Beyond the paper: a call-by-value model

The Ehrhard–Geoffroy paper stops at the §9 LNL / Seely model; a **call-by-value** (CBV)
reading is its explicitly stated *future work* (the conclusion: *"In future work we will
explain how this model can be used for interpreting call-by-value or even call-by-push-value
… languages …"*). This repository takes a step in that direction along the
**Eilenberg–Moore / coalgebra route** of **Melliès, *Categorical Semantics of Linear Logic*,
§7.4** (the EM route gives CBV; the co-Kleisli route gives CBN, which is the cartesian closed
`SCones` above). It is *beyond* the paper — not a paper-§ result.

The CBV model is built and **axiom-free** (the five files below depend only on the same three
classical `boolp` axioms as everything else — verified by `Print Assumptions` on `ICones_CBV`,
`ICones_EM_cartesian`, `EMComon_all`, and `cpD_sample_var_dirac`):

- **`theories/homs/em_cat.v`** — the **Eilenberg–Moore category** of the `!` comonad
  (`ICones_EM`), the cofree functor `!̃ = bang_cofree` with `!̃B = (!B, dig B)`, the forgetful
  functor `U`, and the **cofree adjunction `U ⊣ !̃`** (`adj_phi`/`adj_psi`, the round-trips
  `adj_phiK`/`adj_psiK`, naturality, and the triangle identities
  `adj_triangleL`/`adj_triangleR`).
- **`theories/homs/em_seely_comonoid.v`** — the **commutative-comonoid** maps `d_bang`/`e_bang`
  on `!A`, transported from the cartesian `(&, ⊤)` through the Seely isos `Seely2`/`Seely0`,
  with the comonoid laws and the coalgebra / comonoid-morphism conditions (Melliès's LC2–LC4),
  plus the symmetric-monoidal `tens_cofree`/`unit_cofree`.
- **`theories/homs/em_cartesian.v`** — **the full `EM(!)` is cartesian**, with the product
  carried by the linear `⊗` (not `&`) and the terminal object the tensor unit `1`: the
  headline `ICones_EM_cartesian` (`EM_prod`, `EM_term`, projections, pairing, β-laws), the
  lax-monoidal comparison `m_bang`, and — crucially — the **unconditional** comonoidality
  `EMComon_all : forall P, EMComon P`. This is Melliès Prop 26–28 / Cor 17/20, proved by the
  **structural retraction-and-lifting argument** (`diagram81` = Prop 26 retraction,
  `coalg_mor_lift` = Cor 20 lifting, `coalg_d_is_mor_gen` the transported diagonal as a
  coalgebra morphism) — **not** by reducing to promoted points (which would only compute on
  `x!`; for a general coalgebra `(A,a)` the image `a x` is not promoted, which is exactly
  why the naïve approach stalls and the retraction route is needed).
- **`theories/homs/cbv_adjunction.v`** — the **(lax symmetric) monoidal adjunction `U ⊣ !̃`
  between `ICones` and the (full) category `EM(!)` of `!`-coalgebras** (Melliès Prop. 29),
  bundled as the record **`CBV_Model`** with the witness **`ICones_CBV`**. With `EMComon_all`
  in hand, this is a genuine **linear/non-linear adjunction** (Benton-style) with the *full*
  `!`-coalgebra category as the cartesian non-linear / value side.
- **`theories/programs/cbv.v`** — a small **first-order CBV calculus** (unit, base, products,
  `let`-sequencing, `sample`) interpreted into the model. The monad of the adjunction
  `T = !̃∘U` (`Tobj`, `tunit_eta`, `kcomp`); a structural interpretation of well-typed terms
  (`vlD`/`cpD`); and the soundness core — the monad/`let` laws
  (`kcomp_etaR`/`kcomp_etaL`/`kcomp_A`), the product β-laws (`vlD_fst_pair`/`vlD_snd_pair`),
  and **`sample` = the integral** (`cpD_sample_var_dirac`: `⟦sample⟧(δ_r) = (δ_r)!`, via
  the FMeas coalgebra `Coalg_dirac` + `dirac_dense`).
- **`theories/programs/ppl.v`** — a **higher-order**, direct-style, **multi-variable** Moggi-CBV
  calculus faithfully porting the [`mathcomp-qbs` ppl branch](https://github.com/LLM4Rocq/mathcomp-qbs/tree/ppl).
  Single-sort `expr Γ t` with intrinsically-typed De Bruijn contexts (`has_var Γ t`); direct
  application `e_app : expr Γ (tfun A B) → expr Γ A → expr Γ B`; the QBS constructors
  `e_var`/`e_pair`/`e_fst`/`e_snd`/`e_lam`/`e_app`/`e_ret`/`e_bind`/`e_sample`, plus `e_real`
  (Dirac literal), `e_score` (scalar rescaling), `e_score_tm` (**term-level** score by a
  measurable `f : R → R` pointwise in `[0,1]` applied to the value of an `expr Γ tR` — the
  load-bearing constructor for Bayesian inference, where the score factor depends on a
  bound variable), and **`e_add` / `e_mul`** (real arithmetic on `tbase R` via the FMeas
  lax-monoidal map and the Dirac/integration view — see below). Every term denotes a
  Kleisli arrow `coalg_hom (ctxD Γ) (T (tyD t))` with `T = !̃ ∘ U`; function types use the
  **EM(!) Kleisli exponential** `⟦tfun A B⟧ = !̃(U A ⊸ U B)` (no value-CCC required, and
  none exists). Three headline examples:
  - **`ex_random_constant`** — `do c ← sample N(0,1); return (λx. c) : P (R → R)`. The QBS
    paper cites this exact program as impossible in classical measure semantics; here
    `ex_random_constant_denot_E` is axiom-free.
  - **`ex_random_linear`** — `do m, b ← sample N(0,1); return (λx. m·x + b) : P (R → R)`,
    the killer demo. `e_add` / `e_mul` are interpreted by composing `FMeas_fmap` of the
    measurable arithmetic with the **FMeas lax-monoidal map** `fmeas_lax X Y : (FMeas X) ⊗
    (FMeas Y) → FMeas (X × Y)` (`theories/homs/fmeas_lax.v`). On Dirac inputs the lift
    reduces to scalar arithmetic (`add_lift_dirac`, `mul_lift_dirac`); under bind, the
    standard Moggi-Kleisli `bind(m, k) = ∫ k(a) dm(a)` integrates pointwise, so the cones
    interpretation recovers the QBS-style "distribution of `λx. m·x + b` for `m, b ~ N(0,1)`"
    reading axiom-free. `ex_random_linear_denot_E` connects the denotation to the joint
    pushforward.
  - **`ex_bayes_linear`** — `do m ← sample mu; do _ ← score_tm f m; return m : P R`, the
    textbook prior/score/return Bayesian shape and the first example exercising
    `e_score_tm`. The score factor `f : R → R` (think a clipped Gaussian likelihood
    `gaussian_lik y` of a fixed observation `y`, restricted to `[0,1]`) is applied to the
    bound variable `m`. The `e_score_tm` denotation packages `f` as a path into the unit
    cone via the §6 follow-up `int_to_linhom_pres_path_in_cone`, with Dirac identity
    `score_tm_lift_dirac` reducing `score_tm f` on `δ_r` to `f(r) · one1` (the same
    `score_value` packaging the scalar `e_score` uses, but with `r` coming from a bound
    variable rather than a syntactic literal). `ex_bayes_linear_denot_E` exposes the outer
    `kbind_ext score_then_return_denot sample_denot` form, axiom-free. **Honest scope
    note**: this is the **unnormalised** posterior — the denotation is a sub-probability
    measure of total mass `∫ f(m) dµ(m)`; no `qbs_normalize`-style downstream pass is
    introduced, and we make no Bayes-optimality claim.
- **`theories/programs/ppl_named.v`** — a **Saito–Affeldt-style named-variable surface
  syntax** for the De Bruijn PPL of `ppl.v` (APLAS 2023 §5.1–§5.3, §6). The named context
  `named_ctx := seq (string * ppl_type Ar)` pairs each slot with a string identifier; a
  structural translation `nexp_to_dexp : named_expr Γ t → expr (drop_names Γ) t` delegates
  the semantics one-to-one to `eD` of `ppl.v` (`neD e := eD (nexp_to_dexp e)`), so nothing
  is re-interpreted and the axiom-clean reductions
  `ex_random_constant_denot_E` / `ex_random_linear_denot_E` carry over verbatim. Variable
  lookup `#"x"` uses **canonical structures** (`find_nv` / `found_nv` / `recurse_nv` with
  mathcomp-analysis' `infer` typeclass on `String.eqb`) so Coq's elaborator infers the
  context slot, the type, and the `named_var` witness simultaneously; the
  bidirectionality hints `&` on every binding / context-shared constructor are crucial
  for the canonical-structure resolution to fire on the right metavariable. A custom
  entry `ppl_named` provides the surface notation
  `let "x" := M in N` / `\"x" ::: A => M` / `Sample (mu, Hmu)` / `Score (r, Hr0, Hr1)`
  / `Score' { f, Hf_meas, Hf_ge0, Hf_le1 } e` (the term-level Bayesian-score surface
  form built on `ne_score_tm`, the named counterpart of `e_score_tm`)
  / `Ret e` / `# "x"` / `M @ N` / `M + N` / `M * N` / `(e1, e2)` / `fst e` / `snd e`
  / `()` / `[|r|]` / `{x}`-escape; the three flagship examples re-cast as
  `ex_named_random_constant`, `ex_named_random_linear`, and
  `ex_named_bayes_linear` discharge their equivalence to the De Bruijn versions
  with `Proof. by [].`
- **`theories/homs/fmeas_lax.v`** — the **FMeas lax symmetric monoidal map** as a genuine
  `icones_hom`: `fmeas_lax X Y : FMeas X ⊗ FMeas Y → FMeas (X × Y)`, sending `µ ⊗ ν` to the
  product measure `µ × ν`. Built via `tensor_uncurry` of the bilinear lift; the outer
  linhom's path-preservation in the cone variable (the previously-deferred follow-up of
  `bilin.v`) is now discharged as `int_to_linhom_pres_path_in_cone`. The Dirac identity
  `fmeas_lax_dirac : fmeas_lax(δ_x ⊗ δ_y) = δ_{(x,y)}` is what makes the PPL's
  `e_add`/`e_mul` reductions match QBS on point masses.

**One honest scope note.** The value category `EM(!)` is cartesian but **not** cartesian
closed — and is not expected to be (this is a structural fact about EM categories of
linear-exponential comonads, not a missing diagram chase). What `EM(!)` *does* have, and
what Moggi-CBV actually needs, are the **Kleisli exponentials** for `T = !̃ ∘ U` described
above. `cbv.v` interprets a first-order fragment (no function types — minimal Moggi-CBV
demo); `ppl.v` interprets higher-order via the Kleisli exponentials. Adequacy /
normalization / full-abstraction are out of scope here.

## Status

Paper **§2–§9** are formalized: the entire linear-logic model, axiom-free. Beyond the paper,
the call-by-value model structure above is also built and axiom-free (with the three caveats
stated).

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
│              the Seely category, the FMeas !-coalgebra;
│              the call-by-value model structure (beyond the paper,        (CBV)
│              Melliès §7.4):
│                em_cat.v            EM(!) + the cofree adjunction U ⊣ !̃
│                em_seely_comonoid.v the Seely comonoid d/e on !A (LC2–4)
│                em_cartesian.v      full EM(!) cartesian via ⊗ (Cor 20)
│                cbv_adjunction.v    the LNL monoidal adjunction, ICones_CBV
│                fmeas_lax.v         FMeas is lax symmetric monoidal
│                                    (µ ⊗ ν ↦ µ × ν as an icones_hom)
├── stable/    stable functions, the CCC SCones, fixpoints, Lemma 9.4     (§7, §9.2)
├── kernels/   substochastic kernels Skern and the embedding (Thm 6.5)    (§6)
└── programs/  small calculi INTERPRETED into the model (demonstrations,   (CBV)
               not part of the model itself):
                 cbv.v               a first-order Moggi-CBV calculus
                                     (sample = the integral)
                 ppl.v               a higher-order, direct-style multi-var
                                     QBS-mirror PPL with sample + score +
                                     term-level score + real arithmetic;
                                     random_constant, random_linear and
                                     bayes_linear all interpreted axiom-free
                 ppl_named.v         Saito-Affeldt-style named-variable
                                     surface syntax for ppl.v: custom
                                     entry + canonical-structures lookup,
                                     semantics delegated structurally
                                     (nexp_to_dexp) to eD of ppl.v
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
