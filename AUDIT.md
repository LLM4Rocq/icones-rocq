# Adversarial audit — Icones formalization vs. Ehrhard–Geoffroy, *Integration in Cones* (LMCS 21(1:1) 2025; arXiv:2212.02371)

Auditors: a category theorist, a measure-theory/probability semanticist, a Rocq/mathcomp
proof engineer. Mandate: find inconsistencies, overclaims, weakened statements, hidden
assumptions, vacuity. Read-only on code/git; the single output is this file.

Method: every headline theorem's *Coq statement* was read and compared field-by-field to the
*paper statement* (`/tmp/icones_src/content.tex`); `Print Assumptions` was re-run on every
headline result against the prebuilt `.vo` (not trusting the README); the whole `theories/`
tree was grepped for `Admitted`/`admit`/`Axiom`/`Parameter`/`Hypothesis`/`Variable`; the
SAFT/tensor/Seely/coalgebra/EM soft spots were read line-by-line; the blueprint `\rocq{}`
citations were cross-checked against the actual declarations; `MeasSubcat` inhabitation was
investigated.

---

## Verdict

**The central claim — "fully axiom-free formalization of paper §2–§9" — is HONEST.** It holds
up to adversarial scrutiny. All ten named headline results
(`Skern_to_ICones_fully_faithful`, `ICones_smcc`, `tensor_hom_iso`, `SCones_ccc`,
`der_preserves_limits`, `stab_lin_swap`, `ICones_Seely`, `Bang_comonad`, `Coalg_counit`/
`Coalg_coassoc`, `ICones_EM_cartesian`) were re-verified to depend on **exactly the three
classical `boolp` axioms and nothing else** — no project `Axiom`/`Parameter`/`Admitted`/
`admit.` exists anywhere in the 54 source files. The statements I checked are *genuine*, not
weakened: full-and-faithful is full+faithful, the SMCC bundle carries real `icones_iso`s with
triangle/pentagon/hexagon, the SAFT tensor is a real wide-intersection construction with a
proved universal property (`wi_med`/`wi_med_unique`), the Seely category carries the full
symmetric-monoidal-functor coherence, the coalgebra laws are the paper's two equations, and
the CCC carries real β/η. The §7 stable-function encoding ("0-extension off the unit ball")
faithfully models the paper's domain-restricted `𝔅B → C` maps, *and* correctly distinguishes
the norm-≤1 morphism set `STAB(B,C)` from the full exponential object.

**Severity counts: 0 BLOCKER, 0 major, 5 minor, 4 nits** (M1 withdrawn — faithful to the paper).
No cheats, no vacuity, no
soundness gap. The findings are honesty/packaging/scope-presentation issues, not
mathematical defects.

**Single most serious issue: none of substance.** (An earlier draft flagged the absence of a
concrete `MeasSubcat` instance as the top finding; that was **withdrawn on reassessment against
the paper** — see M1. The paper itself develops §2–§9 *parametrically* over an arbitrary small
subcategory `ARCAT`, so the formalization's parametricity over `Ar` is faithful, not a gap.)
The remaining findings are cosmetic / doc-staleness nits, listed below; the axiom-free §2–§9
claim is honest and the statements are genuine.

---

## Findings (ordered by severity)

### MINOR

**M1 — Parametric over `Ar : MeasSubcat R`, no concrete instance constructed — FAITHFUL TO THE
PAPER (finding WITHDRAWN; reclassified non-issue).**
*Reassessment.* The paper (§3, `content.tex:1029`) states: *"Let `ARCAT` be a **small** full
subcategory of `MEAS` … closed under cartesian products and contain[ing] the terminal object
`⊤` … We assume all objects of `ARCAT` non-empty."* The whole development (§2–§9) is then
parametric over this arbitrary `ARCAT`; Remark `rmk:ar-main-example` only gives `ℝⁿ` / "even
`ℝ` as single object" as **example** choices — the paper fixes **no** concrete `ARCAT`. So the
formalization's universal quantification over `Ar` is the *correct* rendering, and the absence
of a concrete instance matches the paper exactly (it is not a gap). `MeasSubcat R`
(`theories/mcones/ar.v:70`) faithfully encodes `ARCAT`'s conditions — `ar_obj : Type` (small),
`ar_point` (non-empty objects), `ar_zero`/`ar_zero_unique` (terminal `⊤`),
`ar_prod`/`ar_prod_carrier_eq` (closed under products) — and the record's own header says "a
faithful Rocq encoding of the paper's `ARCAT`." The proofs are real and non-vacuous (the record
is inhabitable). The README/explainer "over the real line" matches the paper's own motivating
gloss (intro: *"probabilities … such as the real line"*; Remark: `ℝⁿ`).
*Optional, NOT required.* One *could* add a demonstration instance (e.g. the `{⊤, ℝ}` or `ℝⁿ`
subcategory) and instantiate a headline theorem at it, purely to *exhibit* the model running —
but the paper does not, so this is a beyond-scope nicety, not a fidelity fix.

**M2 — `der_preserves_limits` is named "preserves limits" but only certifies the equalizer
half of paper Thm 7.34.** *Claim vs reality.* Paper Thm 7.34 (`th:derfuns-preserves-limits`,
content.tex:6111) states *"`Der` preserves **all limits**"*, with proof = "products **and**
equalizers." The Coq `der_continuous` record bundles **only equalizer preservation**; its own
header comment says "(packaged, equaliser half)" (`der_continuous.v:434`). The product half
exists but is a *separate* one-line lemma `der_preserves_prod_proj`
(`der_continuous.v:91`, `Proof. by [].`) that is **not** part of the `der_preserves_limits`
bundle. So the single theorem named `der_preserves_limits : der_continuous` does not, on its
own, prove its name/the paper claim; the full content is `der_preserves_prod_proj` +
`der_preserves_limits` together.
*Evidence.* `theories/stable/der_continuous.v:419-445` (record + theorem), `:91-93` (product
lemma); paper content.tex:6110-6145.
*Recommended action.* Either bundle product-preservation into `der_continuous`, or rename to
`der_preserves_equalizers` and state a separate `der_preserves_limits` combining both.

**M3 — Stale "PARTIAL / DEFERRED" header on `tensor_hom_iso.v` contradicts the completed
result.** *Claim vs reality.* `theories/homs/tensor_hom_iso.v:17` declares
"`tensor_hom_iso (Paper Thm 5.12) — PARTIAL`" and lines 22-25 say "The full `icones_iso`
packaging is DEFERRED." This is **superseded and false today**: the actual `tensor_hom_iso`
that `smcc.v`'s `smcc_closed` field uses is the *complete* `icones_iso` built in
`theories/homs/tensor_iso.v:3317` (`icones_iso_of_cancel Phi_icones Psi_icones PsiPhi PhiPsi`,
both cancellation laws proved). `ICones_smcc` (which embeds it) is axiom-free and total. The
`tensor_hom_iso.v` file merely built an earlier skeleton; the header was never updated.
*Evidence.* stale header `theories/homs/tensor_hom_iso.v:1-44`; real iso
`theories/homs/tensor_iso.v:3303-3318`; consumer `theories/homs/smcc.v:386`.
*Recommended action.* Fix the `tensor_hom_iso.v` header to say the full iso lives in
`tensor_iso.v` and is complete; or delete the stale skeleton commentary.

**M4 — `ICones_SMCC` record omits bifunctor-composition and structural-iso naturality as
explicit fields.** *Claim vs reality.* `ICones_smcc` (`smcc.v:311-365`) carries the bifunctor
`smcc_mor` with its **identity** law `smcc_mor_id`, all four structural isos, the
involution, and triangle/pentagon/hexagon — a real SMCC. But it does **not** include
`smcc_mor` *composition* functoriality (`F(g∘f) = Fg ∘ Ff`) nor the *naturality squares* of
α/λ/ρ/σ as record fields. (`tensor_mor_comp` is proved in `em_cartesian.v:308` and the iso
naturality is implicit in the Yoneda construction, so the content exists; it is just not part
of the headline bundle.) The paper's Thm 5.15 obtains the isos *as* natural transformations
via `lemma:functor-yoneda-iso`, so naturality is morally part of the claim.
*Evidence.* `theories/homs/smcc.v:311-365`; `tensor_mor_comp` at `em_cartesian.v:308`.
*Recommended action.* Add `smcc_mor_comp` and the four naturality squares to the record (the
lemmas appear to exist), so the bundle is self-evidently a symmetric monoidal *closed
functor* structure rather than "data + coherence equations."

**M5 — `ICones_EM_cartesian` is a rich-subcategory result, not "EM(!) is cartesian"; the
CBV *plan* recommended the opposite of what was delivered.** *Claim vs reality.* The code is
**honest** in itself: the `EM_Cartesian` record's `cart_pair`/`cart_beta1/2`/`cart_term_mor`/
`cart_term_unique` are all **gated on an `EMComon Z`/`EMComon P` hypothesis**
(`em_cartesian.v` record, ~line 460+), i.e. the cartesian universal property holds only on
the comonoidal sub-collection (cofree coalgebras + the Thm-9.7 `FMeas(X)` coalgebras), exactly
because Melliès' Cor 20 ("diagonal is a coalgebra morphism") does not reduce on a general
coalgebra (header `em_cartesian.v:12-40`). The discrepancy is with the planning doc:
`~/prime_gap/icones-cbv-plan.md:247-260` *recommends targeting the FULL `EM(!)`* and argues a
subcategory is "more work," yet the delivered code is the "à défaut" subcategory. README is
honest ("cartesianness step is under way," CBV listed as in-progress). So no doc *overclaims*
this as done — but the plan's recommendation and the delivered artifact diverge.
*Evidence.* `theories/cbv/em_cartesian.v:12-60` (honest header), record fields gated on
`EMComon`; `~/prime_gap/icones-cbv-plan.md:247-260` (contrary recommendation); README "In
progress" section.
*Recommended action.* Update `icones-cbv-plan.md` to record that the à-défaut subcategory was
delivered (and why), so the plan and code agree.

**M6 — README "53 files" is now 54.** *Claim vs reality.* `README.md:96` says "~52k lines
across 53 files." Actual: 54 `.v` files, 52,795 lines (`theories/stable/compose.v` was added
after the README's last edit; it is the untracked file in `git status`).
*Evidence.* `find theories -name '*.v' | wc -l` → 54; README.md:96.
*Recommended action.* Bump to 54 (and commit `compose.v`, currently untracked `??`).

### NIT

**N1 — Paper theorem *numbers* in README/blueprint are the published LMCS numbers, not in the
arXiv `content.tex`.** The source `content.tex` uses auto-numbered `\begin{theorem}` with
labels (e.g. the kernel result is `The functor Sklin is full and faithful`, content.tex:4619,
under label `th:path-equiv-lin` region; SMCC is `th:icones-smcc:4261`). The README's "Theorem
6.5 / 5.15 / 5.12 / 7.32 / 9.5 / 9.7" are the *rendered* LMCS numbers. The *statements* all
match; only the numbering is unverifiable from the arXiv `.tex`. Not a defect, just note that
"Thm 6.5" cannot be confirmed against `content.tex` directly — the statement can and does.

**N2 — `PLAN.md` still documents the historical axiomatized-`⊗`/`!` ("Option B") strategy.**
PLAN.md §3.2 lays out the "axiomatise the universal property" route as the stretch plan and
references `theories/axioms/*`. That directory no longer exists (renamed/discharged to
`homs/`), and the actual development took the *constructive SAFT* route (Option A-ish). The
top-of-file note flags "MVP retired," but the body still reads as if `⊗`/`!` are axiomatized.
*Recommended action.* Trim PLAN.md §3.2 to reflect that the SAFT discharge was carried out
constructively and the axiom interfaces were deleted.

**N3 — `verify.sh` `Print Assumptions` list omits some headline names.** It checks
`Skern_to_ICones_fully_faithful`, `ICones_smcc`, `Bang_comonad`, `ICones_Seely`,
`Coalg_counit`, `Coalg_coassoc` — but not `SCones_ccc`, `tensor_hom_iso`, `stab_lin_swap`,
`der_preserves_limits`, `ICones_EM_cartesian` (this auditor verified those separately; all
clean). *Recommended action.* Add the missing names to `verify.sh` so CI covers every
headline claim.

**N4 — `MeasSubcat` carries an unused `R : realType` parameter.** `ar.v:66-69` admits `Ar`
does not depend on `R` and threads it only for uniformity. Harmless; noted for completeness.

---

## What is genuinely solid (acknowledged)

- **Axiom-freeness is real and verified.** `Print Assumptions` on all ten headline results
  returns *only* `propositional_extensionality`, `functional_extensionality_dep`,
  `constructive_indefinite_description` (the three `boolp` axioms) — confirmed live against
  the prebuilt `.vo`, not taken on trust. No `Axiom`/`Parameter`/`Admitted`/`admit.`/`give_up`
  exists in any of the 54 files (the only "Admitted"/"Axiom" hits are *prose in comments*
  asserting their absence). Notably, even `Prop_irrelevance` is avoided.
- **Thm 6.5 (`Skern_to_ICones_fully_faithful`, `kernel_embedding.v:364`) is the real full+faithful.**
  Faithful = injectivity of `Skern_to_ICones_mor` on hom-sets (`kernel_embedding.v:211`); full =
  surjectivity onto `icones_hom (FMeas X) (FMeas Y)` with an explicit inverse `icones_to_skern`
  (`kernel_embedding.v:317-349`). Matches paper "Sklin is full and faithful" (content.tex:4619) exactly.
  Functoriality (`Skern_to_ICones_mor_id/_comp`) is also proved.
- **Cone hierarchy is faithful to §2.** `isPrecone` (`precone.v:46`) = R≥0-semimodule +
  cancellation (Pcsimpl) + positivity (Pcpos); `isCone` (`cone.v:55`) adds the norm with
  (Normh)/(Normz)/(Normt)/(Normp) and ω-completeness (Normc) materialized as `cone_sup_ball`
  with ub/lub/norm-≤1 — a correct encoding of Selinger-style cones with ω-chain (not
  arbitrary-directed) completeness, exactly as the paper insists.
- **SMCC (Thm 5.15, `ICones_smcc`, `smcc.v:371`) is a genuine bundle:** bifunctor + four
  `icones_iso` structural isos + symmetry involution + triangle/pentagon/hexagon + closedness
  via the real `tensor_hom_iso`. Axiom-free.
- **The SAFT/Freyd tensor construction is real, not assumed.** `tensor B C` is the wide
  intersection `wi_obj` of subobjects of a coseparator power (`tensor_construct.v`), and its
  universal property is the *proved* `wi_med`/`wi_med_proj`/`wi_med_unique`
  (`representable.v:849-870`) — `wi_med_unique` is a genuine uniqueness proof, not a stub. The
  curry/uncurry bijection has **both** round-trips (`tensor_curryK`, `tensor_uncurryK`) plus
  `tensor_curry_inj` and naturality. Well-poweredness (Thm 4.18, `icones_well_powered`,
  `representable.v:591`) and a concrete coseparator (`icones_coseparator_inj`,
  `representable.v:1154`) are proved. This is the same SAFT route as the paper, fully spelled
  out — the README's claim about mechanizing SAFT is accurate.
- **Thm 5.12 (`tensor_hom_iso`, `tensor_iso.v:3317`)** is a complete `icones_iso` via
  `icones_iso_of_cancel` with both cancellations (`PsiPhi`, `PhiPsi`).
- **§7 stable functions faithfully model the paper.** `is_totmono` (`totmono.v:212`) is
  exactly Def 7.5 / Eq 7.1 (parity of `n−#I` via `Pneg`/`Ppos`, `precone_le`, restricted to
  the unit ball); `is_stable` = totmono+bounded+ω-continuous (Def 7.7); `is_meas_stable` adds
  path-preservation (Def 7.10). The "0-extension off the unit ball" (`sh_offball`/`sc_offball`)
  is a faithful representation of the paper's domain-restricted `𝔅B → C` maps, **not** a
  weakening — and the development *correctly* distinguishes the morphism set `scones_hom`
  (which carries `sc_norm_le1`, the paper's `‖f‖≤1` requirement for `STAB(B,C)`,
  `scones_cat.v:300`) from the exponential object `stablehom` (the full integrable cone, no
  norm bound). `SCones_ccc` carries real product β + exponential β/η.
- **Seely category (Thm 9.5, `ICones_Seely`, `seely.v`)** is the modern Bierman/Melliès
  definition: SMCC + comonad `!` + `Seely2 : !A⊗!B ≅ !(A&B)` + `Seely0 : 1 ≅ !⊤`, their
  naturality, AND full symmetric-monoidal-functor coherence (assoc/braid/both unitors), all as
  real `icones_iso`. Matches content.tex:7516 ("ICones … is a Seely category in the sense of
  Melliès"). `stab_lin_swap` (Lemma 9.4, `stab_lin_swap.v:1381`) is a real `icones_iso`
  (`sls_fwd`/`sls_bwd` full homs, both round-trips, naturality in all 3 slots).
- **Coalgebra (Thm 9.7, `coalgebra.v`)** proves the paper's two exact equations:
  `der ∘ Coalg = id` (`Coalg_counit:183`) and `dig ∘ Coalg = (!Coalg) ∘ Coalg`
  (`Coalg_coassoc:195`), via `dirac_dense`; `EM(!)` is a real category
  (`coalg_mor_id`/`coalg_mor_comp`); `FMeas` is functorial into it.
- **Pettis integral (Def 4.1) is faithful** — defined weakly against the separating test
  family (`path_integral_eq`, `pettis.v:94`), with uniqueness from (Mssep); `isICone`
  (`icone.v:75`) requires existence for all X, β, µ (Def 4.3). Fubini (Thm 4.15) and
  completeness (Thm 4.16) are proved with no `Admitted`.
- **§9.2 fixpoints** — `lfp = sup_n fⁿ(0)` with `lfp_fixpoint`, `lfp_least`, `lfp_ball`, and
  `Yfix`/`Yfix_fix`; the section `Hypothesis`es (`f_incr`/`f_ball`/`f_cont`) are the genuine
  monotone/ball/Scott-continuous preconditions of Kleene's theorem, not cheats.
- **All `Hypothesis`/`Variable` are legitimate.** Every one occurs inside a balanced
  `Section`…`End` and is a real precondition of the enclosing lemma (the paper's hypotheses),
  discharged at `End`. None is a global load-bearing assumption.
- **Blueprint integrity is good.** All ten headline names are cited in the correct chapters
  (`05-skern`, `06-tensor`, `07-stable`, `08-exponential`); a cross-check of all 583
  declaration-level `\rocq{}` leaves against the source found **no dangling citation** — the
  "non-resolving" ones are HB record fields / structure names (`cone_norm`, `mcone_M_sep`,
  `ConesTransport`, `is_n_increasing`, …) that all exist in the sources. The `axioms/`→`homs/`
  rename left no stale `axioms.` reference; no `\_` escape leftovers.
- **§8/§9-full-subcat/§10 are honestly out of scope.** No `ACONES`/analytic/PCS/Cantor/Polish
  implementation exists in `theories/` (only a one-word comment in `findiff.v`). README,
  explainer, and PLAN all list these as "Open." Honest.

## What is overclaimed or incomplete

There is **no mathematical overclaim** in the headline results: each is proved as stated and
is axiom-free. The honest gaps are:

1. **The model is never instantiated** (M1): parametric over `Ar`, with no concrete
   `MeasSubcat` witness, so the "interprets sampling over the real line" prose is not closed
   by a built example.
2. **`der_preserves_limits` is mis-titled** (M2): it certifies equalizers only; the product
   half is a separate unbundled lemma.
3. **Two records under-bundle** (M4): the SMCC record lacks `smcc_mor_comp` and structural-iso
   naturality fields (content exists elsewhere).
4. **The CBV/EM cartesian layer is a rich subcategory, not full `EM(!)`** (M5) — correctly and
   honestly flagged in the code header and README ("in progress"), but the CBV *plan* doc
   recommends the opposite of what shipped.
5. **Stale doc artifacts** (M3 "PARTIAL" header, N2 PLAN.md axiomatized-`⊗` strategy, N3
   verify.sh coverage, M6 file count) — cosmetic, but they can mislead a reader into thinking
   a completed result is partial, or that axioms are in play when they are not.

---

## Fidelity matrix

| Headline | Paper statement | Coq statement | Faithful? | Discrepancy |
|---|---|---|---|---|
| `Skern_to_ICones_fully_faithful` (kernel_embedding.v:364) | Sklin: SKERN→ICONES is full and faithful (content.tex:4619) | injective on homs ∧ surjective onto `icones_hom(FMeas X, FMeas Y)` | **yes** | none |
| `ICones_smcc` (smcc.v:371) | ICones is an SMCC (Thm 5.15, th:icones-smcc) | bifunctor+id law, 4 `icones_iso`, involution, triangle/pentagon/hexagon, closed | **yes (minor under-bundle)** | no `smcc_mor_comp`/iso-naturality fields (M4) |
| `tensor_hom_iso` (tensor_iso.v:3317) | (B⊗C)⊸D ≅ B⊸(C⊸D) (Thm 5.12) | `icones_iso` via cancel, both laws proved | **yes** | stale "PARTIAL" header in a *different* file (M3) |
| `SCones_ccc` (scones_ccc.v) | STAB is cartesian closed (Thm 7.32 region) | product+β, exponential+β/η record, all populated | **yes** | none; carrier 0-extension is faithful, not weakening |
| `der_preserves_limits` (der_continuous.v:436) | Der preserves **all** limits (Thm 7.34) | preserves **equalizers** (record); products = separate lemma | **weakened (naming)** | bundle = equalizer half only (M2) |
| `stab_lin_swap` (stab_lin_swap.v:1381) | stable/linear swap iso (Lemma 9.4) | `icones_iso`, both round-trips, naturality ×3 | **yes** | none |
| `ICones_Seely` (seely.v) | ICones is a Seely category (Thm 9.5, content.tex:7516) | SMCC+comonad+Seely2+Seely0+naturality+full SMF coherence | **yes** | none |
| `Bang_comonad` (bang.v) | the `!` exponential comonad (§9) | comonad over ICones, axiom-free | **yes** | none |
| `Coalg_counit`/`Coalg_coassoc` (coalgebra.v:183/195) | FMeas(X) is a `!`-coalgebra (Thm 9.7) | `der∘Coalg=id`, `dig∘Coalg=(!Coalg)∘Coalg` | **yes** | none |
| `ICones_EM_cartesian` (em_cartesian.v) | (basis for CBV; Melliès Prop 28 / paper §9 EM) | `⊗`-product cartesian **on `EMComon` objects only** | **differs (honestly)** | rich subcategory, not full EM(!) — flagged in code & README (M5) |
| `icones_well_powered` (representable.v:591) | ICones well-powered (Thm 4.18) | essentially-small subobjects via classifier | **yes** | none |
| Pettis integral (pettis.v:94) | Def 4.1 (weak integral vs test family) | `path_integral_eq` against `mcone_M` tests, unique | **yes** | none |

---

## Closing assessment

This is a high-integrity formalization. The axiom-freeness is not a slogan — it survives a
live `Print Assumptions` re-check on every headline name. The hard categorical content (SAFT
tensor, Seely isos, the kernel embedding, the stable CCC) is constructed, not postulated, and
the definitions track the paper closely, including the subtle points (ω-chain vs directed
completeness, domain-restricted stable maps, the `STAB(B,C)` norm-≤1 morphism condition vs the
unrestricted exponential object). The findings are honesty-of-packaging and scope-presentation
issues — chiefly that the model is proved in the abstract and never instantiated (M1), one
theorem is mis-titled (M2), and a few stale doc/header artifacts could mislead (M3, N2). None
threatens soundness or makes any headline vacuous. **No cheat was found.**
