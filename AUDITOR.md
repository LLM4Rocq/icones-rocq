# AUDITOR.md — paper-to-Rocq correspondence

This document is for a **paper reviewer / mathematician** auditing the Icones
formalisation. It maps each definition / lemma / theorem of the paper to its
Rocq counterpart, so you can verify *what is formalised* without having to read
the proof scripts themselves. Notable mathematical content we had to add to
make the paper machine-checkable (SAFT mechanisation, the Cor-20 retraction-
and-lifting, the LNL/Seely structure, the CBV calculi) is in a separate section.

The paper is:

> **Thomas Ehrhard and Guillaume Geoffroy**, *Integration in Cones*, LMCS **21**(1:1), 2025 —
> [DOI 10.46298/LMCS-21(1:1)2025](https://doi.org/10.46298/LMCS-21(1:1)2025) /
> [arXiv 2212.02371](https://arxiv.org/abs/2212.02371).

---

## How to read the Rocq references

Each Rocq name is given as `Module.path.name` plus the source file. To inspect
any of them in your local checkout:

```sh
# Type and definition
echo 'Print Icones.homs.seely.ICones_Seely.' | rocq top -Q theories Icones

# Axiom dependencies
echo 'Print Assumptions Icones.homs.seely.ICones_Seely.' \
  | rocq top -Q theories Icones
```

The whole formalisation depends only on the **three classical-logic axioms**
inherited from `mathcomp-analysis`: `propositional_extensionality`,
`functional_extensionality_dep`, `constructive_indefinite_description`.
There are **no project-specific axioms**, no `Admitted` proofs, no
`Parameter` interfaces anywhere in `theories/`. The script
[`./verify.sh`](./verify.sh) runs `Print Assumptions` on the
regression-anchor lemma `Skern_to_ICones_fully_faithful` (paper Theorem 6.5)
and a small set of downstream headline results.

---

## Paper § 2 — Cones

The paper introduces *positive cones* (an additive monoid with a non-negative
scalar action and a complete norm in the Selinger style). The formalisation
follows the same definitional path, packaged as a Hierarchy Builder tower.

| Paper | English statement | Rocq |
|---|---|---|
| Def 2.1 | A *precone* is an additive commutative monoid with a non-negative real scalar action satisfying distributivity and bilinearity. | `precone`, `PreCone.type` — `theories/cones/precone.v` |
| Def 2.2 | A *cone* is a precone with a partial order ≤ (Selinger's), the supremum of every increasing norm-bounded ω-chain, and the norm acting as a continuous semi-norm. | `Cone.type` — `theories/cones/cone.v` |
| Cat 2 | The category **Cones** has cones as objects and norm-≤ 1 continuous linear maps as morphisms. | `cones_hom`, `cones_comp`, `Cones` (the category) — `theories/cones/cone_cat.v` |
| Lem 2.8 / 2.10 | ω-continuity of inverse / of the difference operator on the unit ball. | `invf_omega_continuous`, `diff_omega_continuous` — `theories/cones/basic_lemmas.v` |

Notable design choice: ω-continuity comes in two flavours — `is_omega_continuous`
(input and output chains live in the unit ball; linear-tailored) and
`is_scott_continuous_unit` (input chain in the ball, output at any radius;
the *general* notion needed for non-linear stable maps in §7). Both are
proved equivalent for linear maps.

---

## Paper § 3 — Measurable cones (MCones)

The paper bases measurability on a small full subcategory `ARCAT` of `MEAS`
(measurable spaces with measure-1 elements and finite products). The
formalisation packages `ARCAT` as a record so the entire §3+ tower is
*parametric in the chosen subcategory*.

| Paper | English statement | Rocq |
|---|---|---|
| `ARCAT` | A small full subcategory of `MEAS` whose objects have a 1-element and whose binary products live in the subcategory. | `MeasSubcat`, `ar_obj`, `ar_carrier`, `ar_point`, `ar_zero`, `ar_prod` — `theories/mcones/ar.v` |
| Def 3.5 | A *measurable cone* is a cone equipped with a family of measurable tests (continuous, ≤ 1, separating). | `MCone.type` (via `isMCone` mixin) — `theories/mcones/mcone.v` |
| Def 3.13 | An *mcones morphism* is a `Cones`-morphism preserving the test family. | `mcones_hom`, `mcones_comp`, `MCones` — `theories/mcones/mcone_cat.v` |
| Prop 3.11 | Dual norm separation: `‖x‖ ≤ sup_{t∈Mtest} ⟨t,x⟩`, with the supremum attained as an adherent point. | `mcone_norm_le_pairing_ub`, `mcone_test_pairing_adherent` — `theories/mcones/mcone_cat.v` (`Section Proposition311`) |
| Def 3.16 | The *measure cone* `FMeas(X)` of finite measures on `X ∈ ARCAT`, with test `t ↦ ∫ t dµ`. | `fmeas`, the `FMeas` HB instance — `theories/mcones/fmeas.v` |
| Def 3.20 | A *path* is a measurable map `r ↦ η(r) : X → C` whose pointwise test pairings are measurable. | `path_car`, `path_int_exists` — `theories/mcones/path.v` |
| Cat 3 | `MCones` is a category. | `MCones` (above) — `theories/mcones/mcone_cat.v` |

The Rocq encoding faithfully treats `ARCAT` as a parameter (`MeasSubcat R`)
just as the paper does (paper §3, around `content.tex:1029`).

---

## Paper § 4 — Integrable cones (ICones)

The paper makes a cone *integrable* by demanding that every probability
measure / path can be Pettis-integrated against the cone. The formalisation
builds the full HB tower `Precone → Cone → MCone → ICone`.

| Paper | English statement | Rocq |
|---|---|---|
| Def 4.1 | An *integrable cone* (`ICone`) is a measurable cone in which every path admits a Pettis integral with respect to every (sub-)probability measure. | `ICone.type` (via `isICone` mixin) — `theories/icones/icone.v` |
| Def 4.2 | The Pettis integral `∫_µ η : C` is the unique element pairing with every test `t` as `∫ ⟨t, η(r)⟩ dµ`. | `icone_integral`, `icone_integral_eqP` (uniqueness) — `theories/icones/icone.v` |
| Lem 4.7 | The Pettis integral satisfies the natural change-of-variable / Fubini-type identities (the conversion lemma threading all integrability arguments). | `icone_integral_*` family + `bilin.v` — `theories/icones/pettis.v`, `theories/homs/bilin.v` |
| Thm 4.5 | The set of paths into a cone is itself an `ICone`. | `path_isICone` (via `path_int_exists`) — `theories/mcones/path.v`, `theories/icones/examples_icone.v` |
| Thm 4.12 | `FMeas(X)` and the dual cone `⊥` are integrable. | `FMeas` is an `ICone`; `Bottom`-cone instances — `theories/icones/examples_icone.v` |
| Cat 4 | The category `ICones` has integrable cones and `MCones`-morphisms preserving the integral. | `icones_hom`, `icones_comp`, `ICones` — `theories/icones/icone_cat.v` |
| Fubini (§4) | The Fubini / iterated-integral identity for paths over a product space. | `fubini_iter_fun_X` — `theories/icones/fubini.v` |
| Thm 4.18 | `ICones` is well-powered. | `icones_well_powered` (full proof, no stub) — `theories/icones/representable.v` |
| Thm 4.19 | `ICones` is complete with `1` a coseparator; therefore every limit-preserving functor `ICones → C` has a left adjoint (by SAFT). | The completeness data (products, equalisers, the coseparator) is in `icone_cat.v`; the bespoke **SAFT engine** is `representable.v` (`wi_obj`, `wi_med`, `is_icones_left_adjoint`) — see *Beyond the paper* below |

---

## Paper § 5 — Internal hom, tensor, and SMCC

| Paper | English statement | Rocq |
|---|---|---|
| Def 5.1 / 5.7 | The internal hom `C ⊸ D` carrier (the cone of `Cones`-morphisms `C → D`); its action `(h ⊸ g) : (C₁ ⊸ D₁) → (C₂ ⊸ D₂)`. | `linhom_car`, `linhom_postc`, `linhom_prec`, `linhom_map` — `theories/homs/linhom.v` |
| Prop 5.8 | The internal-hom action lifts to an `icones` morphism. | `linhom_map_icones` — `theories/homs/linhom_functor.v` |
| Thm 5.9 | The functor `(C ⊸ −)` preserves all limits. | `limpl_preserves_prod`, `limpl_preserves_limits` — `theories/homs/limpl_continuous.v` |
| Thm 5.12 | The currying isomorphism `(B ⊗ C) ⊸ D ≃ B ⊸ (C ⊸ D)`. | `tensor_hom_iso` — `theories/homs/tensor_iso.v` |
| Thm 5.13 | Norm identity: `‖m‖ = ‖curry m‖` for `m : B ⊗ C → D`. | `tensor_norm_le` (≤) + the ≥ direction via Prop 3.11 — `theories/homs/tensor.v` / `tensor_iso.v` |
| Prop 5.14 | The tensor is determined on pure tensors `x ⊗ y`. | `tensor_ext`, `tensor_ext3`, `tensor_ext4` — `theories/homs/tensor.v`, `theories/homs/smcc.v` |
| Thm 5.15 | `(ICones, ⊗, 1)` is a symmetric monoidal closed category. | `ICones_SMCC`, `ICones_smcc` — `theories/homs/smcc.v` |
| Rem 5.1 | The tensor object is given by SAFT, without an explicit carrier. | The paper's invocation of SAFT is *mechanised* concretely in `representable.v` + `tensor_construct.v` — see *Beyond the paper* below |

---

## Paper § 6 — Substochastic kernels and the embedding theorem

| Paper | English statement | Rocq |
|---|---|---|
| Cat 6 | The category `Skern` of substochastic kernels: objects in `ARCAT`, morphisms `κ : X ⇝ FMeas(Y)`. | `Skern_hom`, `Skern_id`, `Skern_comp`, `Skern` — `theories/kernels/skern.v` |
| Thm 6.1 | Bijection `Path(X, B) ≃ FMeas(X) ⊸ B` (cone iso) given by the integration map `I^B_X`. | `int_to_linhom`, `int_to_linhom_iso` — `theories/homs/bilin.v` |
| Thm 6.5 | The functor `Klin : Skern → ICones`, sending `X ↦ FMeas(X)` and a kernel to its integration map, is **fully faithful**. | `Skern_to_ICones_fully_faithful` (= the *regression anchor*) — `theories/kernels/kernel_embedding.v` |

`Skern_to_ICones_fully_faithful` is the lemma checked by `./verify.sh` and is
load-bearing for the whole development's axiom budget. It depends only on the
3 classical `boolp` axioms.

---

## Paper § 7 — Stable functions and the cartesian-closed category SCones

| Paper | English statement | Rocq |
|---|---|---|
| Def 7.5 | A function is *totally monotonic* if its iterated finite differences over the inclusion lattice are positive. | `is_totmono`, `Pneg`/`Ppos`, `\sumP` — `theories/stable/totmono.v` |
| Def 7.7 | A function is *stable* if it is totally monotonic, bounded, and ω-continuous on the unit ball. | `is_stable` (uses `is_scott_continuous_unit`) — `theories/stable/totmono.v` |
| Def 7.10 | A *measurable stable* function additionally preserves measurable paths. | `is_meas_stable` — `theories/stable/totmono.v` |
| Lem 7.11 | The class of stable functions is closed under zero, addition, and non-negative scaling. | `stable_zero`, `stable_add`, `stable_scale` — `theories/stable/totmono.v` |
| Lem 7.12 | Pointwise order on stable maps = the alternating-sum order. | `sh_le_of_alt` — `theories/stable/stablehom.v` |
| Thm 7.19 | A function is totally monotonic iff it is *n-increasing* (for all `n ≥ 1`). | `totmono_is_n_increasing` (forward), `is_n_increasing_totmono` (converse) — `theories/stable/findiff.v` |
| Lem 7.20–7.25 | The finite-difference / sign-split machinery `Δε`, `Δ`, `SD` used to prove Thm 7.19 and §7.3 closure properties. | `totmono_Delta_pos/_neg`, `SD`, `SD_cons`, `SnB`, `SnB_increasing`, etc. — `theories/stable/findiff.v` + `theories/stable/compose.v` |
| Lem 7.27 | If `f` is linear in arg 1 and totally monotonic in arg 2, it is totally monotonic. | `ev_totmono` (delivered in the form actually needed by the CCC) — `theories/stable/scones_ccc.v` |
| Thm 7.30 | Stable functions are closed under composition. | `stable_comp`, `meas_stable_comp` — `theories/stable/compose.v` |
| Thm 7.32 | The category `SCones` of stable functions is cartesian closed. | `SCones_ccc`, `SCones_CCC` (record + witness) — `theories/stable/scones_ccc.v` |
| Thm 7.34 | The forgetful functor `Der : ICones → SCones` preserves all limits. | `der_preserves_prod_proj`, `der_preserves_limits` — `theories/stable/der_continuous.v` |
| (also) | Stable functions admit a least-fixpoint via the cone unit-ball ω-cpo (paper §9.2). | `lfp_fixpoint`, `sfix_fixpoint`, `Yfix`, `Yfix_fix` — `theories/stable/fixpoint.v` |

The `is_stable` predicate uses `is_scott_continuous_unit` (unit-ball input,
any-radius output sup) because the strictly-linear `is_omega_continuous`
(both ω-chains in the unit ball) is **not preserved under non-negative
scaling for non-linear maps** — a faithful reading of the paper's setting,
not a weakening.

---

## Paper § 9 — Linear exponential, Seely category, FMeas coalgebra

| Paper | English statement | Rocq |
|---|---|---|
| LL `!` | The linear-exponential comonad `! : ICones → ICones`, obtained as the right adjoint of `Der` via SAFT. | `Bang`, `nl`, `lin`, `lin_beta`, `lin_unique` (the adjunction data) — `theories/homs/exp_adjunction.v`; `Bang_comonad` — `theories/homs/bang.v` |
| Comonad | `(!, der, dig)` is a comonad with the standard counit / coassociativity. | `der`, `dig`, `der_prom`, `dig_prom`, the comonad laws — `theories/homs/bang.v` |
| Lem 9.4 | The natural iso `(B ⇒ₛ (C ⊸ D)) ≃ (C ⊸ (B ⇒ₛ D))` ("swap a stable outer and a linear inner"). | `stab_lin_swap` (a fully spelled-out `icones_iso`; paper gives the map + "pattern seen many times", no proof) — `theories/stable/stab_lin_swap.v` |
| Thm 9.5 | `(ICones, ⊗, 1, !)` is a **Seely category** (i.e. has the Seely isos `Seely2 : !A ⊗ !B ≃ !(A & B)` and `Seely0 : 1 ≃ !⊤`, and the comonad / SMC coherence). | `Seely2`, `Seely2E`, `Seely2_natural`, `Seely0`, `Seely0E`, the full `SeelyCategory` record + the witness `ICones_Seely` — `theories/homs/seely.v` |
| Thm 9.7 | For each `X ∈ ARCAT`, `FMeas(X)` is a `!`-coalgebra (with structure map `Coalg_X(µ) = ∫_r (δ_r)! dµ`); the assignment `X ↦ FMeas(X)` is a functor into `EM(!)`. | `Coalg`, `Coalg_dirac`, `dirac_dense`, `FMeas_coalgebra`, `FMeas_fmap` — `theories/homs/coalgebra.v` |
| Sect 9.2 | Fixpoint combinator `Y` on the cartesian closed `SCones`. | `Yfix`, `Yfix_fix` (the paper's CCC construction) — `theories/stable/fixpoint.v` |

---

## Beyond the paper — notable mathematical content we had to add

The paper *cites* a number of categorical / linear-logic results as black
boxes (SAFT, Lack's lifting, Mellies §7.4) which a textbook reader can take
on trust. A machine-checked development cannot cite a black box; the
following constructions are real mathematical content the formalisation
adds, each justified by an external reference.

### Mechanisation of the Special Adjoint Functor Theorem (paper §4.3, §5, §7, §9)

The paper builds `⊗`, `!`, and the Seely isos via Freyd's SAFT (Riehl,
*Category Theory in Context* Thm 4.6.10 / Cor 4.6.14) — a complete,
well-powered category with a coseparator has a left adjoint to every
continuous functor. Rather than postulate SAFT, we **mechanise the SAFT
argument concretely**: the left adjoint of `F` at `c` is the (wide)
intersection of the subobjects of a power of the coseparator `1` over which
`c → F-` factors.

| Construction | Rocq |
|---|---|
| Subobject classifier on `ICones` (Thm 4.18 fully proved, not stubbed) | `SubobjClassifier`, `icones_subobject_classP`, `icones_well_powered` — `theories/icones/representable.v` |
| Binary intersection (pullback) of subobjects + UMP | `pb_med`, `pb_med_proj1/2`, `pb_med_unique` — same file |
| Wide intersection of a small family of subobjects + cone UMP | `wi_obj`, `wi_med`, `wi_med_proj`, `wi_med_unique` — same file |
| Initiality engine (intersection embeds in each member; mono if members are) | `wi_factors_each`, `wi_incl_inj` — same file |
| Export contract: hom-bijection a left-adjoint candidate must satisfy | `is_icones_left_adjoint` — same file |

The tensor `⊗` and the exponential `!` are then **discharged** against this
SAFT engine:

| What | Rocq |
|---|---|
| `−⊗C` is the SAFT left adjoint of `(C⊸−)` (Thm 5.9 + the SAFT engine) | `tensor_construct.v` (the tensor itself + curry/uncurry + naturality) — `theories/homs/tensor_construct.v` |
| The Thm 5.12 measurability core (the analytic crux) | `tensor_hom_iso.v` + `tensor_iso.v` (the `path_tens_to_X` / `lfun_path_swap` / `swap_lin_lin_hom` chain) |
| `E` is the SAFT left adjoint of `Der` (Thm 7.34 feeding the SAFT engine) | `der_continuous.v` (Thm 7.34) + `bang_construct.v` (Bang/nl/lin discharged) |
| The Seely isos (Thm 9.5) are discharged via Lem 9.4 + tensor-hom-iso | `theories/stable/stab_lin_swap.v` + the construction in `seely.v` |

The strategy is the paper's (§4.3 explicitly invokes SAFT); the formalisation
adds the *concrete* SAFT construction so the tree carries no `Parameter` /
`Axiom` interfaces and the whole development is axiom-free.

### EM(!) is fully cartesian — Mellies §7.4 Prop 28 / Cor 20

Beyond §9, the formalisation also delivers Mellies' result that the
Eilenberg–Moore category of `!` (the value category of a linear-logic CBV
interpretation) is cartesian, with product carried by the linear `⊗`
(not the cartesian `&`). The non-trivial part is **Cor 20**, the step
Mellies himself flags as *"does not seem to follow from general abstract
properties"*: the transported comonoid diagonal must be shown to be a
coalgebra morphism, on *every* coalgebra.

| Lemma | English statement | Rocq |
|---|---|---|
| Mellies Prop 26 | Every coalgebra `(A,a)` is a retract of its cofree `(!A, dig)` in `EM(!)`. | `diagram81` (records the key Eq 88 retraction-square) — `theories/homs/em_cartesian.v` |
| Mellies §6.11 Prop 20 / Cor 20 | If `i` is a coalgebra morphism with a carrier retraction `r∘i = id` and `i∘f` is a coalgebra morphism, then `f` is. | `coalg_mor_lift` (the diagram (66)/(67) chase Mellies flags as *"not so immediate"*) — same file |
| Mellies Prop 27 (transport) | A retract of a commutative comonoid is a commutative comonoid. | The four transported laws (`transp_counitL/_R/_cocomm/_coassoc`) — same file |
| Mellies Prop 28 | `EM(!)` is cartesian on **every** coalgebra (`EMComon` holds unconditionally). | `EMComon_all : forall P : Coalgebra Ar, EMComon P` — same file |
| Mellies Cor 17 | A symmetric monoidal category in which every object has a natural commutative comonoid is cartesian. | The headline `ICones_EM_cartesian` (with `cart_prod`, `cart_term`, the projections, pairing, β-laws) — same file |

The naïve approach — reducing to *promoted points* `x!` via `d_bang_prom`
— cannot work for a general carrier (an arbitrary `a x` is not promoted).
The structural retraction proof is what Mellies' §7.4 actually requires;
it is mechanised here.

### Linear/non-linear monoidal adjunction `U ⊣ !̃` (Mellies §7.4 Prop 29)

| Result | English statement | Rocq |
|---|---|---|
| LNL adjunction | The cofree-coalgebra adjunction `U ⊣ !̃ : ICones ⇄ EM(!)` is a lax symmetric monoidal adjunction (Lack's lifting). With Cor 20 in hand, this is a genuine *linear/non-linear* adjunction with the **full** category of `!`-coalgebras as the cartesian non-linear / value side. | `CBV_Model` record + `ICones_CBV` witness — `theories/homs/cbv_adjunction.v` |

### Call-by-value calculi (beyond the paper, future work)

The paper's conclusion lists *"future work: interpreting call-by-value or
call-by-push-value … languages"*. The formalisation takes a step in that
direction with two small calculi, both interpreted axiom-free.

| What | Rocq |
|---|---|
| A small first-order fine-grain Moggi-CBV calculus (unit, base, products, `let`, `sample`), interpreted via the CBV monad `T = !̃ ∘ U`; soundness includes the monad/`let` laws, product β, and `sample` = the integral. | `cbv.v` — `theories/programs/cbv.v` |
| A higher-order, direct-style, multi-variable Moggi-CBV calculus faithfully porting the QBS PPL — single-sort `expr Γ t` with intrinsically-typed De Bruijn contexts, direct application `e_app : expr Γ (tfun A B) → expr Γ A → expr Γ B`, plus `e_real`/`e_score`/`e_add`/`e_mul`. Function types via the EM(!) Kleisli exponential `!̃(U A ⊸ U B)` (no value-CCC required). Two headline examples reproduced from the [`mathcomp-qbs` `ppl` branch](https://github.com/LLM4Rocq/mathcomp-qbs/tree/ppl): `ex_random_constant` = `do c ← sample N(0,1); return (λx. c) : P(R → R)` (the QBS paper's flagship); and `ex_random_linear` = `do m, b ← N(0,1); return (λx. m·x + b)` (the killer demo — distribution over linear functions). Both interpreted axiom-free. The arithmetic primitives are interpreted via the FMeas lax-monoidal map (see next row); on Dirac inputs the lifts reduce to scalar arithmetic, and under the Moggi-Kleisli bind `bind(m, k) = ∫ k(a) dm(a)` they recover the QBS-style "distribution over deterministic linear functions" reading. | `ppl.v` (`expr`/`has_var`/`tyD`/`ctxD`/`eD`, `ex_random_constant`, `ex_random_constant_denot_E`, `ex_random_linear`, `ex_random_linear_denot_E`) — `theories/programs/ppl.v` |
| The **FMeas lax symmetric monoidal map** — `(FMeas X) ⊗ (FMeas Y) → FMeas (X × Y)`, sending the pure tensor `µ ⊗ ν` to the product measure `µ × ν` — as a genuine `icones_hom`. Built via `tensor_uncurry` of the bilinear lift; its existence depends on the previously-deferred follow-up of `bilin.v` (path-preservation of `int_to_linhom` in the cone variable), now discharged as `int_to_linhom_pres_path_in_cone`. The Dirac identity `fmeas_lax_dirac : fmeas_lax(δ_x ⊗ δ_y) = δ_{(x,y)}` is what makes the PPL's `e_add` / `e_mul` Dirac arithmetic reductions match QBS. | `fmeas_lax`, `fmeas_lax_E`, `fmeas_lax_dirac`, `int_to_linhom_pres_path_in_cone` — `theories/homs/fmeas_lax.v`, `theories/homs/bilin.v` |

The Kleisli-exponential structure arises from the natural-bijection chain

`Hom_EM(C × A, T B) ≅ Hom_IC(U(C × A), U B) ≅ Hom_IC(U C ⊗ U A, U B) ≅ Hom_IC(U C, U A ⊸ U B) ≅ Hom_EM(C, !̃(U A ⊸ U B))`

using only the cofree adjunction, `U` strict monoidal (`cbv_U_prod`), and
the SMCC closure of `ICones`. `EM(!)` is *not* cartesian closed (a
structural fact about EM categories of linear-exponential comonads, not a
missing diagram chase); Kleisli exponentials are what Moggi-CBV actually
needs, and that holds here axiom-free.

---

## What is **not** formalised

These are paper sections we have not (yet) formalised. The choices are
deliberate; each requires substantial infrastructure outside the current
scope.

| Paper | What it is | Why not yet |
|---|---|---|
| § 8 | *Analytic* functions, the cartesian closed `ACONES`; the analytic exponential `!ₐ`. | A separate analytic layer (radius-of-convergence, complex analyticity, Taylor expansions of stable functions) is required. |
| § 9 (post-9.7) | The full-subcategory theorem: for Polish / standard-Borel `X`, `FMeas(X) ↪ EM(!)` is full. | Requires a Polish / standard-Borel layer in mathcomp-analysis and two folklore measure-theoretic lemmas (regularity of finite Borel measures, image-measure determination); not yet in inventory. |
| § 10 | Embedding into probabilistic coherence spaces. | Requires a separate PCS formalisation. |

---

## How to verify the development for yourself

```sh
# 1. Clone and build (Rocq 9.1.1 + mathcomp-analysis 1.16).
opam install --deps-only ./icones.opam
make -j

# 2. Run the axiom-budget check on the regression anchor.
./verify.sh

# 3. Spot-check any headline result yourself.
echo 'From Icones.homs Require Import seely. Print Assumptions Icones.homs.seely.ICones_Seely.' \
  | rocq top -Q theories Icones

# Or for the higher-order PPL example:
echo 'From Icones.programs Require Import ppl. Print Assumptions Icones.programs.ppl.ex_random_linear_denot_E.' \
  | rocq top -Q theories Icones
```

In each case the only axioms printed should be the three classical-logic
axioms `propositional_extensionality`, `functional_extensionality_dep`,
`constructive_indefinite_description`. No project-specific axiom should
appear, and there are no `Admitted` proofs in `theories/`.

A short tour for a paper reviewer who wants to verify the headline results:

1. **Theorem 6.5** (`Skern_to_ICones_fully_faithful` in
   `theories/kernels/kernel_embedding.v`) — the embedding theorem; the
   regression anchor of the whole tree.
2. **Theorem 5.15** (`ICones_smcc` in `theories/homs/smcc.v`) — the linear
   logic core: `(ICones, ⊗, 1)` is a SMCC.
3. **Theorem 7.32** (`SCones_ccc` in `theories/stable/scones_ccc.v`) — the
   cartesian closed `SCones`.
4. **Theorem 9.5** (`ICones_Seely` in `theories/homs/seely.v`) — the Seely
   category structure (the full LL / intuitionistic-linear model).
5. **Theorem 9.7** (`FMeas_coalgebra` in `theories/homs/coalgebra.v`) — the
   measure cone is a `!`-coalgebra; `X ↦ FMeas(X)` is a functor into `EM(!)`.
6. **Beyond §9** (`EMComon_all` and `ICones_CBV` in
   `theories/homs/em_cartesian.v` / `theories/homs/cbv_adjunction.v`) —
   Mellies' Cor 20 (full cartesianness of `EM(!)`) and the LNL adjunction.
7. **The CBV / PPL examples** (`cbv.v` and `ppl.v` in `theories/programs/`) —
   small calculi exercising the structure.

For deeper inspection, the `blueprint/` directory contains a
LaTeX/Patrick-Massot-style overview that mirrors this table chapter by
chapter, with clickable links to each Rocq definition.
