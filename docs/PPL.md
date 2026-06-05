# PPL.md — A probabilistic programming language on top of Icones

This document describes the **probabilistic programming language (PPL)**
built on top of the Icones formalization. It is a development *beyond the
paper* — the paper formalizes the categorical setting; this document
describes the language we built inside it, what works today, what is
missing, and why.

The paper-side correspondence (paper §§ 2–9 ↔ Rocq) is on the
[Paper tab](../paper/) of this dashboard.

The intended audience: a reader who knows what a probabilistic program is,
knows roughly what Ehrhard–Geoffroy "Integration in Cones" is about, and
wants a precise picture of the language we can currently denote.

---

## 1. What we are trying to do

The paper gives a categorical model of probabilistic computation
(`ICones`) where every type is a cone with measurable structure, and
every morphism is a linear, Scott-continuous, measurable map. The model
is rich enough to interpret a **typed probabilistic functional language
with effects** — sampling, scoring (soft constraint), conditioning, and
**recursion**.

The development in this dashboard does that interpretation. Concretely:

- A surface syntax `named_expr` of programs in named-variable style,
  modelled on the calculus of Saito–Affeldt (APLAS 2023), close to
  what a user actually writes in a probabilistic-programming dialect
  of OCaml or Haskell.
- **Two parallel denotations** of the same surface syntax:
  - **Call-by-value (CBV)** through the Eilenberg–Moore category
    `EM(!)` of the linear-exponential comonad — Moggi-style with the
    exponential `!` as the value modality. This is the canonical CBV
    semantics in a linear-logic model.
  - **Call-by-name (CBN)** directly inside the stable-functions category
    `SCones` (the co-Kleisli of `!`), which is cartesian closed and has
    a free fixed-point combinator. This is the "lazy QBS reading"
    (Heunen–Kammar–Staton–Yang).
- A growing library of **example programs** with closed-form proofs of
  their denotations — Bernoulli, scoring, Bayesian conditioning,
  geometric recursion — each axiom-free.

### 1.1 Why two interpretations?

Because they have **complementary strengths and weaknesses** in this
model:

| Property | CBV via `EM(!)` | CBN via `SCones` |
|---|---|---|
| Recursion at function type | Hard (needs Bang-level Kleene) | Free (`Yfix` in `stable/fixpoint.v`) |
| `let`-binding | Kleisli bind via `kbind_ext` | Plain composition |
| Substitution laws | Asymmetric η problem (Law 2 open) | No issue (substitution = composition) |
| Score with a real-valued weight | Lifts cleanly through `coalg_hom` | Trivial — terminal codomain forces uniqueness |
| Arithmetic (`add`, `mul`) on measures | Bilinear into the tensor `⊗`, with `add_lift` / `mul_lift` axiom-free | Needs a sprod→tensor bridge, not in the library |
| Fits the paper's framing | Yes — `EM(!)` is the canonical CBV setting | Adjacent — uses §7 SCones directly |

So:

- **CBV** is the principal interpretation for non-recursive programs:
  sampling, scoring, conditioning, marginals, all axiom-free, all
  matched against the QBS-style references.
- **CBN** is the principal interpretation for **recursive** programs:
  the geometric distribution and similar examples that need a
  fixed-point combinator. CBN reaches this via a single axiom-free
  `Yfix`; CBV requires per-example Bang-level constructions.
- The two interpretations are NOT (yet) connected by a soundness
  theorem. They are best read as **two parallel views** of the same
  surface syntax that play to different strengths.

### 1.2 Why this is non-trivial

A standard textbook would say "use the Eilenberg–Moore category and
you're done". In this concrete model, three things make it real
mathematical work:

1. **The exponential `!` is built by SAFT** (the Special Adjoint
   Functor Theorem) — a non-constructive existence proof of the right
   adjoint of dereliction. There is no closed-form formula for `!X`
   except via a universal property. This blocks several natural
   computations (e.g. `cone_norm (prom x) = cone_norm x` is provably
   **false** in the SAFT-built `Bang`).
2. **CBV value-fixpoint at function type** is folklore but,
   to our knowledge, not previously formalized in Rocq/Coq.
   The expert recipe (variant of `f^n` with promotions, dereliction at
   the right places, seed at `!0`) had to be built from scratch.
   Validated structurally; gives the headline `ex_geom_arr_mass_one`
   axiom-free.
3. **Cartesian-η of `EM(!)`** (Melliès §7.4 Prop 28 / Cor 20) is a
   meta-theorem the paper cites as a black box. To trust the
   formalization we built it from first principles — the lemma
   `em_pair_mor_proj_id` is, to our knowledge, the first machine
   verification.

---

## 2. The surface language

Defined in `theories/programs/ppl.v` as the inductive `named_expr`.

| Constructor | Surface notation | Meaning |
|---|---|---|
| `ne_var x` | `# "x"` | named variable |
| `ne_tt` | `()` | unit value |
| `ne_pair M N` | `( M , N )` | pairing |
| `ne_fst M` / `ne_snd M` | `fst M`, `snd M` | projections |
| `ne_lam x M` | `\ "x" ::: τ => M` | lambda |
| `ne_app F X` | `F @ X` | application |
| `ne_let x M K` | `let "x" := M in K` | let-binding |
| `ne_fix x M` | `fix "f" ::: τ in M` | recursive value (function-type body) |
| `ne_real r` | `[ \| r \| ]` | constant real |
| `ne_sample µ Hµ` | `sample µ` | sample from a normalised measure |
| `ne_score f Hf Hge Hle e` | `score f e` | soft constraint (multiply weight by `f e`) |
| `ne_add M N` / `ne_mul M N` | `M + N`, `M * N` | arithmetic on measures |
| `ne_true` / `ne_false` | `true`, `false` | boolean literals |
| `ne_bernoulli p H₀ H₁` | `Bernoulli { p, … }` | Bernoulli sample |
| `ne_if e M N` | `if e then M else N` | boolean elimination |

The syntax is **invariant under the choice of interpretation**: `eD`
(CBV) and `eD_CBN` (CBN) consume the same `named_expr` and produce a
denotation in their respective categories.

---

## 3. CBV — what works today

`eD : named_expr Γ τ → coalg_hom (ctxD Γ) (Tobj (tyD τ))` in
`theories/programs/ppl.v`.

The codomain `Tobj (tyD τ)` is the `!`-coalgebra-monad lift:
substochastic measures over the type. Composition is Kleisli bind. The
unit is `eta_T` (Dirac).

### 3.1 Non-recursive programs — axiom-free

Every non-recursive constructor has a definitional reduction lemma
(`eD_<ctor>_E`). All clauses are axiom-free.

Examples in `theories/programs/examples.v` with closed-form proofs of
their denotations:

| Example | Statement | Status |
|---|---|---|
| `ex_random_constant` | constant-output function ignores its sample input | ✅ axiom-free (Gap B headline) |
| `ex_random_linear` | linear-output function maps measures point-wise | ✅ axiom-free |
| `ex_bayes_linear` | Bayesian conditioning by a linear weight | ✅ axiom-free |
| `ex_bayes_linear_is_weighted` | Bayes posterior equals a weighted prior — measure-level | ✅ axiom-free (Gap D headline) |
| `ex_*_bernoulli_*` | Bernoulli conditional + `case_em_bernoulli` convex combination | ✅ axiom-free |

The headlines are **measure-level identities**: they say that the
denotation, viewed as an `FMeas` (substochastic measure), agrees with a
hand-written reference measure. This is the strongest correctness
statement we can make without an explicit semantic equivalence with QBS.

### 3.2 Recursive programs — the achievement

`ex_geom : tunit → tR'` is the geometric distribution:

```coq
fix "g" ::: tfun tunit tR' in
  \ "_" ::: tunit =>
    if Bernoulli { 1/2 } then
      [| 0 |]
    else
      [| 1 |] + # "g" @ ()
```

The headline theorem:

```coq
Theorem ex_geom_arr_mass_one :
  fmeas_mu
    (Lfun (der (FMeas R_obj))
       (linhom_fun (Lfun (der L_geom) Yfix_arr')
                   (one1 : cone_one_car Ar)))
    [set: ar_carrier Ar R_obj]
  = 1%:E.
```

This is the **first formal mass-1 identity for a non-trivial recursive
PPL example in Icones**, axiom-free. It lives in
`theories/programs/infra/em_fix_arr.v`.

### 3.3 How the headline was built

The CBV value-fixpoint recipe (expert-validated, folklore-not-in-the-literature):

1. **`Yfix_arr`** — Bang-level Kleene iteration: `f^n ∘ prom 0`, with
   promotion `prom = nl_B` at each step and seed at the promoted zero.
2. **Per-iterate cascade** — `Step_geom` (in
   `theories/programs/infra/ex_geom_step.v`) gives a structural
   reduction of one Kleene step into a sum of two FMeas convolutions.
3. **Kleene chain monotonicity** — `kleene_arr_chain` proves
   `f^n ≤p f^(n+1)`.
4. **Sup mass = 1** — `F_arr_sup_mass` adds up the mass of each iterate
   via the geometric series `∑ (1/2)^n = 1` from mathcomp-analysis.
5. **Headline** — `ex_geom_arr_mass_one` chains it all through
   `derL_Yfix_E`, `linhom_at_one_sup_E`, `derFMeas_one_sup_E`.

Each of these is short (1–10 lines once the right reduction lemma is
applied), but identifying the right reduction lemma was real
mathematical work.

### 3.4 Generic recursion — partial

`Yfix_arr_g` (in `em_fix_arr.v` after the `ex_geom` headline)
generalizes the construction to an **arbitrary** coalgebra morphism
`M : EM_prod G funT → Tobj funT`:

- **Stages 1–3** (Phi, Kleene chain, Yfix existence + norm bound) —
  ✅ axiom-free.
- **Stage 3a** (fixpoint equation) — ✅ axiom-free **under a
  `seed_order` hypothesis** that is automatically discharged for
  `ex_geom` (by `Step_geom_one_prom_zero_via_convex_E`).
- **Sanity check** `Phi_arr_eq_Phi_arr_g_one1` confirms the generic
  structure faithfully generalizes the `ex_geom`-specific work
  (by definitional reduction).

This is enough to write down `Yfix_arr_g` for any concrete coalgebra
morphism the user supplies; what is **not** enough is to wire it into
`eD ne_fix` as the universal recursion combinator. That needs Stage 4.

---

## 4. CBV — what is missing, and why

### 4.1 `eD ne_fix` is still wired to a broken operator

`eD_fix` in `theories/programs/ppl.v` calls `Yfix_fun_T` (defined in
`theories/programs/infra/em_fix.v`), which is the **linhom-level Kleene
iterate at the unit-ball CPO**.

This is provably wrong for probabilistic semantics: for `ex_geom`,
`Yfix_fun_T` collapses to mass 0 (see `F_n_mass_zero` in
`em_fix_arr.v`). The structural reason: linhom-level iteration loses
mass at each step because the linhom CPO sup is taken on the unit-ball
truncation, which truncates contributions.

**Why we did not rewire it.** Two reasons:

1. **`Yfix_arr_g` Stage 4 blocks.** To replace `Yfix_fun_T` with the
   correct `Yfix_arr`-level construction *as a generic combinator* on
   the surface language, we need `Yfix_arr_g γ` to be a `coalg_hom`,
   which requires it to be a SCones-stable map of `γ`. The
   stability proof relies on §7.3 finite-difference machinery
   adapted to the **ICones tensor** target — that machinery exists in
   the library only for the **SCones product** `sprod`. See
   [§ 7 below](#7-the-blocker-the-scones↔icones-tensor-bridge) for
   the precise gap.
2. **The CBN track exists.** Once CBN's M6 ships (the CBN headline
   `ex_geom_CBN_mass_one`, currently pending — see
   [§ 6 below](#6-cbn-what-works-and-what-is-missing)), it provides
   free recursion *as a generic combinator* via the axiom-free
   `Yfix : scones_hom (stablehom B B) B` from `stable/fixpoint.v`.
   At that point users who want free recursion can use the CBN
   interpretation; CBV stays the principal interpretation for
   non-recursive programs.

So: closed-form recursive programs **can be denoted in CBV today** by
manually using `Yfix_arr` + the per-example assembly pattern of
`ex_geom_arr_mass_one`. Each such example is ~150–300 lines of careful
chasing. There is no surface-language shortcut.

### 4.2 Mutual recursion at free-coalgebra types

`ne_fix x M` requires the fix-body's type to be a function type
(`tfun τ₁ τ₂`). Heunen–Kammar–Staton–Yang's framing allows recursion
at any *free coalgebra*, which would include `tprod (tfun …) (tfun …)`
for mutually-recursive function pairs. Not in scope today; tracked as
task #141.

### 4.3 Law 2 (`kbind_ext_A`) — open but worked around

The CBV Kleisli bind has an asymmetric η law that does not close
cleanly via the standard chase. The Bayes-marginal headline
`ex_bayes_linear_is_weighted` (Gap D #136) is proved at the
measure level (via `weighted_mu_preimage`), which sidesteps Law 2
entirely. No active blocker for current examples.

---

## 5. CBN — what works today

`eD_CBN : named_expr Γ τ → scones_hom (ctxD_CBN Γ) (tyD_CBN τ)` in
`theories/programs/ppl_cbn.v` + `ppl_cbn_eff.v` + `ppl_cbn_bool.v`.

The codomain is a plain `scones_hom` — **no `Tobj` wrap**. Effects live
in the type interpretation itself (the base type already carries the
measure).

### 5.1 Type interpretation (option B)

```
tyD_CBN tunit       = Stop Ar             (* terminal of ICones *)
tyD_CBN (tbase X)   = FMeas X
tyD_CBN (tprod s t) = sprod ⟦s⟧ ⟦t⟧
tyD_CBN (tfun A B)  = stablehom ⟦A⟧ ⟦B⟧
tyD_CBN tbool       = bool_cone_car Ar
tyD_CBN tR'         = FMeas R_obj
```

This is the **pragmatic QBS reading**: a probabilistic value IS a
measure. The alternative ("faithful Melliès §7.4 reading", `tbase X =
Bang(FMeas X)`) is recorded but not chosen.

### 5.2 Trunk — axiom-free

`theories/programs/ppl_cbn.v` (544 lines):

- All structural clauses: var, tt, pair, fst, snd, lam (via `curry`),
  app (via `Ev`), let (via `scones_comp`).
- **Recursion**: `eD_CBN ne_fix := scones_comp Yfix (curry ⟦body⟧)`
  — one line. The fixpoint equation
  `sh_fun (sc_fun (curry ⟦body⟧) g) (sc_fun ⟦ne_fix⟧ g) = sc_fun ⟦ne_fix⟧ g`
  is `eD_CBN_fix_E`, proved by `Yfix_fix` in four lines.

The smoke test `ex_random_constant_CBN_denot_E` reduces the CBN
denotation of `ex_random_constant` definitionally to a recognisable
SCones composite.

### 5.3 Boolean cascade — axiom-free, FULL

`theories/programs/infra/bool_case_scones.v` + `ppl_cbn_bool.v`
(658 lines total):

- `scones_const c Hc` — standalone constant SCones-arrow at a unit-ball
  point (totmono via `big_Pneg_le_Ppos`, boundedness, Scott continuity,
  path preservation via `const_path_measurable`).
- `bool_case_fixed_scones` — fixed-branch lift of `bool_case_icones_hom`
  via `ders`, with true/false-Dirac reduction lemmas.
- **The key insight** for variable-branch if-then-else: promote
  branches `M, N : scones_hom G A` to **points of the internal hom**
  `stablehom G A` via `sc_to_sh`. Then `bool_case_linhom` applies
  verbatim — the bilinearity-in-`(a, b)` obstruction is sidestepped
  without `Bang` and without SAFT.
- Four clauses (true / false / bernoulli / if), five reduction lemmas,
  all axiom-free.

---

## 6. CBN — what is missing, and why

### 6.1 `score` at unit type is structurally trivial

`tyD_CBN tunit = Stop Ar` is the **terminal of ICones**. By terminal
uniqueness, any morphism `_ → Stop Ar` equals `Stop_mor`. So
`cbn_score_clause_def G f H_meas H_ge H_le e` is forced equal to
`ders (Stop_mor _)`, **regardless of the weight function `f`**.

This is **intrinsic to the option-B type translation** — not a bug. A
faithful score-in-CBN interpretation would need `tunit_CBN ≠ Stop`,
for example `tunit_CBN = FMeas unit` (a one-point measure space).

### 6.2 `add` and `mul` are degenerate constants

`cbn_add_clause_def` and `cbn_mul_clause_def` are shipped as
constants at `precone_zero : FMeas R_obj`. A faithful port of the CBV
`add_lift` / `mul_lift` (linear morphism on the tensor) requires a
bilinear stable map
`scones_hom (sprod (FMeas) (FMeas)) → tensor (FMeas) (FMeas)` —
the same SCones↔tensor bridge that blocks CBV Stage 4
(see [§ 7](#7-the-blocker-the-scones↔icones-tensor-bridge)).

### 6.3 No headline mass identity yet — pending

The CBN counterpart of `ex_geom_arr_mass_one` is task #166. It would
read approximately:

```coq
Theorem ex_geom_CBN_mass_one :
  fmeas_mu (sc_fun ex_geom_CBN_denot precone_zero) [set: …] = 1%:E.
```

This goes through `Yfix_fix` + the standard geometric-series identity.
The work involves writing the CBN-side derivation of one Kleene
iteration and verifying the mass adds up. Estimated 200–400 lines based
on the size of the CBV equivalent.

### 6.4 No CBV/CBN soundness theorem

No proof that `eD M ≅ eD_CBN M` in any sense. The two interpretations
are best read as two parallel views. Building the connection would
require commuting `Bang` with the effect-bearing types (i.e. `Bang
(FMeas X) ≅ FMeas X` in a suitable sense), which is non-trivial in
SAFT-built `Bang`.

---

## 7. The blocker: the SCones↔ICones-tensor bridge

The most important open structural problem on the PPL side. It blocks
three things simultaneously:

- CBV `Yfix_arr_g` Stage 4 (`γ ↦ Yfix_arr_g γ` is meas-stable) —
  blocks generic CBV recursion as a combinator.
- CBV-style `add_lift` / `mul_lift` ported to CBN.
- Any future bilinear-into-tensor stable combinator.

**The gap.** `theories/stable/compose.v` proves
"bilinear-into-`sprod` composed-with-stable-via-diagonal is stable" by
the §7.3 finite-difference machinery. The analogous statement with
`sprod` replaced by the ICones tensor `⊗` is true but not built.

Concretely, what is needed is something like:

```coq
Lemma meas_stable_diag_bilinear_tensor
    (G A B : ICone.type Ar)
    (Kn : G -> Bang Ar A)
    (Phi : (G * Bang Ar A) -> Bang Ar B) :
  is_meas_stable Kn ->
  (* Phi linear in each slot (i.e., a bilinear ICones map) *)
  is_bilinear_icones_tensor Phi ->
  is_meas_stable (fun γ => Phi (γ, Kn γ)).
```

The proof would mirror the SCones-product proof in `compose.v`,
substituting `tensor` for `sprod` wherever the cone-sum machinery
appears. Estimated 200–400 lines. The reason we have not built it yet
is that the per-example workaround (manual `Yfix_arr` chase, as in
`ex_geom_arr_mass_one`) is cheaper for each concrete headline, and
CBN gives free recursion for the non-arithmetic part.

---

## 8. Deliberate non-goals

Things that are not formalised because they were never the target:

- **Paper § 8 ACONES (analytic cones, multi-set semantics).**
  Out of scope for this development. The Polish-space refinement of
  paper § 9 (post-Theorem 9.7) is similarly deferred.
- **Paper § 10 — PCS (probabilistic coherence spaces) embedding.**
  Out of scope.
- **Higher-order recursion at free-coalgebra types.**
  Tracked as task #141 — not blocked, just not done.
- **A direct connection between this PPL and an external one
  (QBS, ProbProg, Pyro, Stan).** The marginals/headlines reference
  hand-written measure-level statements (Saito–Affeldt-style), which
  is the strongest correctness statement available without an explicit
  semantic equivalence.

---

## 9. How to verify the development for yourself

```sh
# Build everything.
make -j

# Check axiom dependencies on the regression anchor and the headlines.
echo "Print Assumptions Skern_to_ICones_fully_faithful." | rocq top -Q theories Icones -l theories/kernels/kernel_embedding.v
echo "Print Assumptions ex_geom_arr_mass_one."           | rocq top -Q theories Icones -l theories/programs/infra/em_fix_arr.v
echo "Print Assumptions eD_CBN_fix_E."                   | rocq top -Q theories Icones -l theories/programs/ppl_cbn.v
echo "Print Assumptions eD_CBN_bool_if_E."               | rocq top -Q theories Icones -l theories/programs/ppl_cbn_bool.v
```

Each command should report only the three `boolp` axioms
(`propositional_extensionality`, `functional_extensionality_dep`,
`constructive_indefinite_description`) — these come from
mathcomp-analysis and are not Icones project axioms.

The dashboard's per-entry pages embed the exact identifier name, the
file path, and a GitHub link to the Rocq source, so you can spot-check
any individual headline without compiling the whole project.

---

## Beyond the paper — Boolean cascade and CBV value-fixpoint

The two PPL-specific paper-supporting constructions extracted from the
original AUDITOR.md.

### Boolean cascade: `tbool`, `bool_case`, and `case_em`

To support `ne_if` in the PPL we add a 2-point ICone, its co-pairing as an
icones-hom, and an EM(!) Kleisli-level case combinator. The 2-point cone
itself is paper §4.4 / Theorem 4.24's coproduct `cone_one ⊕ cone_one` (an
existing paper concept), but its concrete construction as
`bool_cone_car Ar : {nonneg R} × {nonneg R}` and its full HB tower are added
here, and the icones-hom packaging `bool_case_linhom` / `bool_case_icones_hom`
+ the unit-ball-free generalisations are new infrastructure.

| Lemma | English statement | Rocq |
|---|---|---|
| The 2-point ICone | A thin record `{nonneg R} × {nonneg R}` with pointwise operations, norm `‖(p, q)‖ = p + q`. Full HB tower `isPrecone` → `isCone` → `isMCone` → `isICone`. Recognised as the paper §4.4 / Thm 4.24 coproduct `cone_one_car ⊕ cone_one_car`. | `bool_cone_car`, `bool_dirac_true`, `bool_dirac_false`, `bool_case` — `theories/programs/infra/bool_cone.v` |
| Universal co-pairing | `bool_case x a b = bc_t(x) · a + bc_f(x) · b` is linear in `x`, ω-continuous on the unit ball, norm `≤ 1` when `‖a‖ ≤ 1` and `‖b‖ ≤ 1`, and preserves measurable paths and integrals. Unit-ball-free variants drop the bounds on `a, b`. | `bool_case_linear`, `bool_case_omega_continuous`, `bool_case_norm_le1`, `bool_case_pres_path`, `bool_case_pres_int`, plus the generalisations `bool_case_omega_continuous_gen`, `bool_case_norm_le_max`, `bool_case_pres_path_gen`, `bool_case_pres_int_gen` — same file |
| Test measurability, generalised | The Mellies-style measurability of `bool_test x` originally required the unit ball; `test_meas_gen` drops the assumption by scaling, exposing the test for *arbitrary* cone elements. | `test_meas_gen` — `theories/mcones/mcone.v` |
| Icones-hom packaging | The co-pairing is packaged first as a `linhom_car` (`bool_case_linhom`) and then as an `icones_hom` (`bool_case_icones_hom`) via the `linhom_icones` bridge. The unit-ball-free version `bool_case_linhom_gen` drops the `‖a‖ ≤ 1` / `‖b‖ ≤ 1` hypotheses on the branches. | `bool_case_linhom`, `bool_case_icones_hom`, `bool_case_linhom_gen` — `theories/programs/infra/bool_case_hom.v` |
| α / β decomposition | `bool_case x a b = bc_t(x) · a + bc_f(x) · b` decomposes as `α(x, a) + β(x, b)` with each piece *separately* bilinear in its two variables (although the whole is not bilinear in `(a, b)`). The two linhoms are the specialisations `bool_case_linhom_gen a 0` and `bool_case_linhom_gen 0 b`. | `alpha_linhom`, `beta_linhom`, `bool_case_linhom_gen_alpha_beta` — same file |
| `case_em` (EM-Kleisli `if-then-else`) | The EM(!) value-level if-then-else: given `a, b : coalg_hom (EM_prod G A) (Tobj B)`, produce `case_em a b : coalg_hom (EM_prod G (Tobj tbool)) (Tobj B)` dispatching on a Kleisli-bool scrutinee. Hom-cone insight: branches `a`, `b` are auto-unit-ball *as coalg homs* — that is what lets `bool_case_linhom` consume them with no ad-hoc bound. | `case_em` — `theories/programs/ppl.v` |

#### Code

```coq
(* theories/programs/infra/bool_cone.v *)

Record bool_cone_car (dummy : MeasSubcat R) : Type :=
  MkBoolCone { bc_t : {nonneg R}; bc_f : {nonneg R} }.

Definition bool_dirac_true  : bool_cone_car Ar := MkBoolCone Ar 1%:nng 0%:nng.
Definition bool_dirac_false : bool_cone_car Ar := MkBoolCone Ar 0%:nng 1%:nng.

(** The universal co-pairing — paper §4.4 / Thm 4.24 universal-property
    formula, [a, b](x) = bc_t(x)·a + bc_f(x)·b. *)
Definition bool_case (x : bool_cone_car Ar) (a b : A) : A :=
  precone_add (precone_scale (bc_t x) a) (precone_scale (bc_f x) b).

Lemma bool_case_true  (a b : A) : bool_case bool_dirac_true  a b = a.
Lemma bool_case_false (a b : A) : bool_case bool_dirac_false a b = b.

(** Linearity, ω-continuity, norm bound, path / integral preservation —
    upgrading the co-pairing to a full ICones morphism (paper Def 4.10). *)
Lemma bool_case_linear (a b : A) : is_linear (fun x => bool_case x a b).
Lemma bool_case_omega_continuous (Ha : cone_norm a <= 1) (Hb : cone_norm b <= 1) :
  is_omega_continuous (fun x : bool_cone_car Ar => bool_case x a b).
Lemma bool_case_norm_le1
    (Ha : cone_norm a <= 1) (Hb : cone_norm b <= 1) (x : bool_cone_car Ar) :
  cone_norm (bool_case x a b) <= cone_norm x.
Lemma bool_case_pres_path
    (Ha : cone_norm a <= 1) (Hb : cone_norm b <= 1)
    (X : ar_obj Ar) (γ : ar_carrier Ar X -> bool_cone_car Ar) :
  is_measurable_path γ ->
  is_measurable_path (fun r => bool_case (γ r) a b).
Lemma bool_case_pres_int
    (Ha : cone_norm a <= 1) (Hb : cone_norm b <= 1)
    (X : ar_obj Ar) (β : ar_carrier Ar X -> bool_cone_car Ar)
    (Hβ : is_measurable_path β)
    (µ : fmeas R (ar_carrier Ar X)) :
  bool_case (icone_integral β Hβ µ) a b =
  icone_integral
    (fun r => bool_case (β r) a b)
    (bool_case_pres_path Ha Hb β Hβ) µ.

(** Unit-ball-free variants: drop ‖a‖ ≤ 1 / ‖b‖ ≤ 1, the operator norm
    bound becomes [≤ max(‖a‖, ‖b‖) ∨ 0]. *)
Lemma bool_case_omega_continuous_gen (a b : A) :
  is_omega_continuous (fun x : bool_cone_car Ar => bool_case x a b).
Lemma bool_case_norm_le_max (a b : A) (M : R)
    (HMa : cone_norm a <= M) (HMb : cone_norm b <= M) (HM0 : 0 <= M)
    (x : bool_cone_car Ar) :
  cone_norm (bool_case x a b) <= M * cone_norm x.
Lemma bool_case_pres_path_gen (a b : A)
    (X : ar_obj Ar) (γ : ar_carrier Ar X -> bool_cone_car Ar) :
  is_measurable_path γ ->
  is_measurable_path (fun r => bool_case (γ r) a b).
Lemma bool_case_pres_int_gen (a b : A)
    (X : ar_obj Ar) (β : ar_carrier Ar X -> bool_cone_car Ar)
    (Hβ : is_measurable_path β)
    (µ : fmeas R (ar_carrier Ar X)) :
  bool_case (icone_integral β Hβ µ) a b =
  icone_integral
    (fun r => bool_case (β r) a b)
    (bool_case_pres_path_gen a b β Hβ) µ.
```

```coq
(* theories/programs/infra/bool_case_hom.v *)

(** linhom_car packaging (unit-ball on a, b). *)
Definition bool_case_linhom
    (a b : A) (Ha : cone_norm a <= 1) (Hb : cone_norm b <= 1) :
    linhom_car Ar (bool_cone_car Ar) A.

(** linhom_car packaging (unit-ball-free on a, b). *)
Definition bool_case_linhom_gen (a b : A) : linhom_car Ar (bool_cone_car Ar) A.

(** Operator-norm bound on the unit-ball-free variant. *)
Lemma bool_case_linhom_gen_norm_le (a b : A) :
  cone_norm (bool_case_linhom_gen a b) <=
    Num.max (Num.max (cone_norm a) (cone_norm b)) 0%R.

(** icones_hom packaging (unit-ball on a, b). *)
Definition bool_case_icones_hom
    (a b : A) (Ha : cone_norm a <= 1) (Hb : cone_norm b <= 1) :
    icones_hom Ar (bool_cone_car Ar) A.

(** α(x, a) = bc_t(x) · a, β(x, b) = bc_f(x) · b. *)
Definition alpha_linhom (a : A) : linhom_car Ar (bool_cone_car Ar) A :=
  bool_case_linhom_gen a precone_zero.
Definition beta_linhom (b : A) : linhom_car Ar (bool_cone_car Ar) A :=
  bool_case_linhom_gen precone_zero b.

Lemma bool_case_linhom_gen_alpha_beta (a b : A) (x : bool_cone_car Ar) :
  linhom_fun (bool_case_linhom_gen a b) x =
  precone_add (linhom_fun (alpha_linhom a) x) (linhom_fun (beta_linhom b) x).
```

```coq
(* theories/programs/ppl.v *)

(** [case_em] — the EM(!) value-level [if-then-else] combinator.
    Branches [a, b : coalg_hom (EM_prod G A) (Tobj B)] are
    auto-unit-ball as coalg_homs (hom-cone insight: the operator norm
    of a coalg_hom is bounded by 1 by construction).  Build via the
    [bool_case_linhom] of [a_lh = adj_phi a] / [b_lh = adj_phi b] on
    the Kleisli-bool source, then tensor-uncurry to consume the
    [bool_cone_car] source, then [adj_psi] back into the [Tobj B]
    codomain (with a [der] step to peel one layer of [!̃]). *)
Definition case_em (G : Coalgebra Ar) (A : ppl_type Ar)
    (a b : coalg_hom (EM_prod G (tyD A))
                     (Tobj (tyD A))) :
    coalg_hom (EM_prod G (bang_cofree (bool_cone_car Ar)))
              (Tobj (tyD A)).
```

### CBV value-fixpoint at function types: a first Coq/Rocq formalisation

The fixpoint operators of paper §9.2 (`lfp`, `Yfix`) live on `SCones` (the
CBN side) and operate on stable maps. The CBV value-fixpoint at function
types is genuinely additional content: P.-A. Melliès in 2026-05-31
consultation describes it as *"folklore, not in the literature"*, and to
our knowledge this is the first Coq / Rocq formalisation. The construction
follows OCaml's `let rec` convention — recursion is restricted to function
types — which is the user-authorised restriction.

| Lemma | English statement | Rocq |
|---|---|---|
| ω-continuity infrastructure | The supremum of an ω-chain of `linhom_car`s in the unit ball passes through post-composition by an `icones_hom`, pre-composition by an `icones_hom`, `bang_fmap` of a linear map, and `prom`-style action; the right-tensor action `tensor_mor (id, ·)` is ω-continuous and monotone in its right argument. | `linhom_pre_icones_sup`, `linhom_post_icones_sup`, `bang_fmap_lin_omega_cont`, `prom_omega_cont`, `tensor_mor_omega_cont_R`, `tensor_mor_R_lin_incr` — `theories/programs/infra/em_continuity.v` |
| Linhom-level Kleene fixpoint | The Kleene iteration `Φ_fun(prev) = bang_fmap (der L) ∘ ch_mor M ∘ tensor_mor (id_G, prev) ∘ coalg_d G` is ball-preserving, monotone and ω-continuous; its Kleene supremum `Yfix_fun_lin` satisfies `Φ_fun(Yfix_fun_lin) = Yfix_fun_lin` and has norm `≤ 1`. | `Phi_fun`, `Yfix_fun_lin`, `Yfix_fun_lin_norm_le1`, `Yfix_fun_lin_fixpoint` — `theories/programs/infra/em_fix.v` |
| The coalg_hom packaging | The linhom-level fixpoint is packaged into a `coalg_hom G (Tobj funT)` via `adj_psi` of the cofree adjunction (which is unconditionally available on any norm-≤-1 icones_hom). This is `Yfix_fun_T M`, the CBV value-fixpoint at function types used by `ne_fix`. | `Yfix_fun_T`, `Yfix_fun_T_mor`, `Yfix_fun_T_unfolding` — same file |

#### Code

```coq
(* theories/programs/infra/em_continuity.v *)

(** Headline ω-continuity facts at the linhom-cone level. *)
Lemma linhom_post_icones_sup (C D1 D2 : ICone.type Ar)
    (g : icones_hom Ar D1 D2)
    (u : nat -> linhom_car Ar C D1)
    (uch : is_omega_chain u)
    (ub1 : forall n, cone_norm (u n) <= 1) :
  linhom_post g (cone_sup_ball u uch ub1) =
    cone_sup_ball (fun n => linhom_post g (u n)) _ _.

Lemma bang_fmap_lin_omega_cont (B C : ICone.type Ar)
    (f : icones_hom Ar B C) :
  is_omega_continuous (bang_fmap_lin f).

Lemma tensor_mor_omega_cont_R (G C1 C2 : ICone.type Ar) :
  is_omega_continuous
    (fun lh : linhom_car Ar C1 C2 => tensor_mor_R_lin G lh).
```

```coq
(* theories/programs/infra/em_fix.v *)

(** The Kleene iteration on the linhom cone at the function-value level.
    [L = U A ⊸ U(T B)] (the Kleisli exponential), [funT = !̃ L] = the
    function-value coalgebra. *)
Definition Phi_fun
    (prev : linhom_car Ar (coalg_obj G) (coalg_obj funT)) :
    linhom_car Ar (coalg_obj G) (coalg_obj funT).

(** The Kleene supremum of the iterates of [Phi_fun] on the unit ball. *)
Definition Yfix_fun_lin : linhom_car Ar (coalg_obj G) (coalg_obj funT) := …
Lemma Yfix_fun_lin_norm_le1 : cone_norm Yfix_fun_lin <= 1.
Lemma Yfix_fun_lin_fixpoint : Phi_fun Yfix_fun_lin = Yfix_fun_lin.

(** Packaging into a coalg_hom via [adj_psi] of the cofree adjunction.
    [adj_psi] is unconditionally available on any norm-≤-1 icones_hom,
    so no separate is_coalg_mor obligation arises. *)
Definition Yfix_fun_T : coalg_hom G (TT funT) :=
  adj_psi (linhom_icones (Yfix_fun_lin M) (Yfix_fun_lin_norm_le1 M)).

Lemma Yfix_fun_T_unfolding : Phi_fun M (Yfix_fun_lin M) = Yfix_fun_lin M.
```


---

## Beyond the paper — CBV / CBN calculi and examples

### Call-by-value calculi (beyond the paper, future work)

The paper's conclusion lists *"future work: interpreting call-by-value or
call-by-push-value … languages"*. The formalisation takes a step in that
direction with two small calculi, both interpreted axiom-free.

| What | Rocq |
|---|---|
| A small first-order fine-grain Moggi-CBV calculus (unit, base, products, `let`, `sample`), interpreted via the CBV monad `T = !̃ ∘ U`; soundness includes the monad/`let` laws, product β, and `sample` = the integral. | `cbv.v` — `theories/programs/cbv.v` |
| A higher-order, **direct-style** (Plotkin/Girard CBV), multi-variable, **named-variable** PPL — the cones-model port of the QBS PPL ([`mathcomp-qbs` `ppl` branch](https://github.com/LLM4Rocq/mathcomp-qbs/tree/ppl)) in the surface style of Saito–Affeldt's APLAS 2023 named-variable embedding. The probability monad lives in the *interpretation* `eD`, **not in the source-language types** — there is no `tprob` type marker, no syntactic `return`, no `bind`. A function that samples has source type `tfun tunit tR`, not `tfun tunit (tprob tR)`. A single intrinsically-typed inductive `named_expr Γ τ` indexed by a named context `named_ctx Ar = seq (string * ppl_type Ar)` and a type `τ : ppl_type Ar`, with `ppl_type ::= tunit | tbase X | tprod | tfun | tbool`; constructors split into three groups — **pure**: `ne_var` / `ne_tt` / `ne_pair` / `ne_fst` / `ne_snd` / `ne_lam` (string binder, body in the extended named context, NOT marked as a computation) / `ne_app` (direct application, `ne_app : named_expr Γ (tfun A B) → named_expr Γ A → named_expr Γ B`) / `ne_fix` (OCaml-style `let rec`, restricted to function types: `ne_fix : named_expr ((s, tfun A B) :: Γ) (tfun A B) → named_expr Γ (tfun A B)`, semantically the CBV value-fixpoint `Yfix_fun_T` of `programs/infra/em_fix.v`) / `ne_real` (real literal at `r : R`, type `tR`) / `ne_add` / `ne_mul` / `ne_true` / `ne_false` (boolean constants of type `tbool`); **sequencer**: `ne_let` (direct-style CBV `let x = M in K` with a string binder; semantically the extended-context Kleisli bind `kbind_ext`); **effects**: `ne_sample : named_expr Γ tR` (sample from a unit-ball `µ : FMeas R_obj` — DIRECT STYLE: returns a pure `tR`, the monad is hidden in `eD`) / `ne_bernoulli p Hp_ge0 Hp_le1 : named_expr Γ tbool` (sample from the 2-point sub-probability `(p, 1-p)` on `bool_cone`, returning a pure `tbool`) / `ne_if : named_expr Γ tbool → named_expr Γ t → named_expr Γ t → named_expr Γ t` (boolean elimination, semantically dispatched via the `case_em` EM-Kleisli combinator built on `bool_case_linhom`) / `ne_score f Hf_meas Hf_ge0 Hf_le1 e : named_expr Γ tunit` (**term-level** Bayesian score by a measurable `f : R → R` pointwise in `[0,1]` applied to the value of a `named_expr Γ tR` — DIRECT STYLE: returns a pure `tunit`; the load-bearing constructor for genuine Bayesian inference, the score factor depends on a bound variable). Function types via the EM(!) Kleisli exponential `tyD (tfun A B) = !̃(U A ⊸ U(T B))` — the `T` on the codomain encodes that every function call is potentially effectful, and this is the SOLE function space in the source language. The boolean type `tyD tbool = !̃(bool_cone_car Ar)` (cofree over the 2-point cone of `programs/infra/bool_cone.v`). The term denotation `eD : named_expr Γ τ → coalg_hom (ctxD (drop_names Γ)) (Tobj (tyD τ))` is defined **directly** by structural recursion on `named_expr` (no two-step encoding) with uniform `Tobj`-wrapped codomain; pure constructors are made into Kleisli arrows by post-composition with `tunit_eta` (the implicit-return that direct style needs — no syntactic `return` is exposed). Variable lookup `#"x"` uses **canonical structures** (`tagged_nctx` / `find_nv` / `found_nctx` / `recurse_nctx` / `ne_var'`, with mathcomp-analysis' `infer` typeclass on `String.eqb`) so Coq's elaborator infers the context slot, type, and `named_var` witness simultaneously; **bidirectionality hints `&`** on every binding / context-shared constructor are crucial for canonical-structure resolution to fire on the right metavariable (exactly the Saito–Affeldt `Arguments exp_letin {g} & {t1 t2}` pattern). A custom entry `ppl_named` provides the surface notation `[ … ]` covering `let "x" := M in N` (desugars to `ne_let`) / `\ "x" ::: A => M` / `fix "f" ::: tfun A B in M` (desugars to `ne_fix`, OCaml-style `let rec`) / `Sample (mu, Hmu)` / `Score { f, Hf_meas, Hf_ge0, Hf_le1 } e` (the ONLY score surface form, desugaring to `ne_score`) / `True` / `False` / `Bernoulli { p, Hp_ge0, Hp_le1 }` / `if e then M else N` (desugars to `ne_if`) / `# "x"` / `M @ N` / `M + N` / `M * N` / `(e1, e2)` / `fst e` / `snd e` / `()` / `[|r|]` / `{x}`-escape (no `Ret` — direct style has no syntactic return). The arithmetic primitives are interpreted via the FMeas lax-monoidal map (see next-but-one row); on Dirac inputs the lifts reduce to scalar arithmetic (`add_lift_dirac` / `mul_lift_dirac`), and the term-level score's Dirac identity `score_lift_dirac` reduces `score_lift f` on `δ_r` to `f(r) · one1` via the §6 follow-up `int_to_linhom_pres_path_in_cone`. The extended-context Kleisli bind `kbind_ext` is the load-bearing equation for the `ne_let` denotation. | `ppl.v` (`ppl_type`/`named_ctx`/`drop_names`/`named_var`/`named_expr`/`tyD`/`ctxD`/`eD`, the constructors `ne_var`/`ne_tt`/`ne_pair`/`ne_fst`/`ne_snd`/`ne_lam`/`ne_app`/`ne_fix`/`ne_let`/`ne_sample`/`ne_real`/`ne_score`/`ne_add`/`ne_mul`/`ne_true`/`ne_false`/`ne_bernoulli`/`ne_if`, the EM-Kleisli `case_em` combinator, the canonical structures `tagged_nctx`/`find_nv`/`found_nctx`/`recurse_nctx`/`found_nv`/`recurse_nv`/`ne_var'`, the meta-lemmas `add_lift_dirac`/`mul_lift_dirac`/`score_lift_dirac`/`kbind_ext`, the custom entry `ppl_named`) — `theories/programs/ppl.v` |
| Six end-to-end examples in the named direct-style surface notation, axiom-free. The first three are the QBS-style headlines, each paired with a structural reduction lemma exposing the outer `kbind_ext` shape of its denotation; the next three are **Phase 4 productive partial-termination** programs combining `ne_fix` with `ne_if` / `ne_bernoulli`. The examples show the direct-style framing concretely — a function that samples has source type `tfun tR tR` (NOT `tprob (tfun tR tR)`), and a probabilistic real-valued program has source type `tR` (NOT `tprob tR`): **(QBS)** `ex_random_constant` = `[ let "c" := Sample (mu, Hmu) in \ "x" ::: tR => # "c" ] : tfun tR tR` (the QBS paper's flagship "distribution over a function space" — and notice the type really is `tfun tR tR`, with the probability monad living entirely in the interpretation `eD`); `ex_random_linear` = `[ let "m" := Sample (mu, Hmu) in let "b" := Sample (mu, Hmu) in \ "x" ::: tR => # "m" * # "x" + # "b" ] : tfun tR tR` (the killer demo: exercises `ne_add` and `ne_mul` via the FMeas lax-monoidal map; on Dirac inputs the lifts reduce to scalar arithmetic, recovering the QBS-style "distribution over `λx. m·x + b` for `m, b ~ µ`" reading); and `ex_bayes_linear` = `[ let "m" := Sample (mu, Hmu) in let "_" := Score { f, … } # "m" in # "m" ] : tR` (the textbook prior/score/observe shape, the only example exercising `ne_score`; the **unnormalised** posterior of total mass `∫ f(m) dµ(m)`, with `f : R → R` a clipped likelihood — no `qbs_normalize` downstream pass). **(Phase 4)** `ex_loop` = `[ (fix "l" ::: tfun tunit tunit in \ "_" ::: tunit => # "l" @ ()) @ () ] : tunit` (bare divergence `(let rec l = λ_. l ()) ()`, total mass 0); `ex_geom` = `[ (fix "g" ::: tfun tunit tR in \ "_" ::: tunit => if Bernoulli { ½, … } then [|0|] else [|1|] + # "g" @ ()) @ () ] : tR` (geometric counter, total mass 1, almost-surely terminating); `ex_almost_loop p Hp_ge0 Hp_le1` = `[ (fix "l" ::: tfun tunit tunit in \ "_" ::: tunit => if Bernoulli { p, … } then () else # "l" @ ()) @ () ] : tunit` (parameterised partial termination, total mass `p`). Each Phase 4 example has its own `_denot_E` structural reduction lemma exposing the outer `kcomp (app_pair _ _) (bang_m ∘ em_pair (Yfix_fun_T (eD body)) (eD ne_tt))` form (no closed form for the `Yfix_fun_T` iterate is claimed). All six interpreted axiom-free; examples are written **exclusively** in the `[ … ]` direct-style surface notation. | `examples.v` (`ex_random_constant`/`ex_random_constant_denot_E`, `ex_random_linear`/`ex_random_linear_denot_E`, `ex_bayes_linear`/`ex_bayes_linear_denot_E`, plus Phase 4: `ex_loop`/`ex_loop_denot`, `ex_geom`/`ex_geom_denot_E`, `ex_almost_loop`/`ex_almost_loop_denot_E`) — `theories/programs/examples.v` |
| The **FMeas lax symmetric monoidal map** — `(FMeas X) ⊗ (FMeas Y) → FMeas (X × Y)`, sending the pure tensor `µ ⊗ ν` to the product measure `µ × ν` — as a genuine `icones_hom`. Built via `tensor_uncurry` of the bilinear lift; its existence depends on the previously-deferred follow-up of `bilin.v` (path-preservation of `int_to_linhom` in the cone variable), now discharged as `int_to_linhom_pres_path_in_cone`. The Dirac identity `fmeas_lax_dirac : fmeas_lax(δ_x ⊗ δ_y) = δ_{(x,y)}` is what makes the PPL's `ne_add` / `ne_mul` Dirac arithmetic reductions match QBS. The same `int_to_linhom_pres_path_in_cone` is what `score_lift` of `ppl.v` reuses to package the term-level score density as an `icones_hom (FMeas R_obj) (cone_one_car Ar)`. | `fmeas_lax`, `fmeas_lax_E`, `fmeas_lax_dirac`, `int_to_linhom_pres_path_in_cone` — `theories/homs/fmeas_lax.v`, `theories/homs/bilin.v` |

#### Code: `theories/programs/cbv.v` — Moggi-CBV fine-grain calculus

```coq
(* theories/programs/cbv.v — Section CBVMonad,
   Variables (R : realType) (Ar : MeasSubcat R) *)

(** [T P = !̃(U P)]. *)
Definition Tobj (P : Coalgebra Ar) : Coalgebra Ar := bang_cofree (U_obj P).

(** Kleisli extension and composition. *)
Definition kbind (P Q : Coalgebra Ar) (f : coalg_hom P (Tobj Q)) :
    coalg_hom (Tobj P) (Tobj Q) := coalg_comp (tmul Q) (Tmap f).

Definition kcomp (P Q S : Coalgebra Ar)
    (g : coalg_hom Q (Tobj S)) (f : coalg_hom P (Tobj Q)) :
    coalg_hom P (Tobj S) := coalg_comp (kbind g) f.

(** sample's denotation, on a Dirac, is the promoted Dirac. *)
Lemma cpD_sample_var_dirac (X : ar_obj Ar) (r : ar_carrier Ar X) :
  Lfun (ch_mor (cpD (c_sample (G := tbase X) (X := X) v_var))) (dirac_fmeas r)
    = prom (dirac_fmeas r).

(** And, more sharply, [⟦sample⟧] integrates the promoted Dirac path
    against the measure value. *)
Lemma cpD_sample_is_integral (X : ar_obj Ar) :
  ch_mor (tunit_eta (FMeas_coalgebra X)) = Coalg X.
Proof. by []. Qed.
```

#### Code: `theories/programs/ppl.v` — the higher-order named direct-style PPL

The file's header docstring captures the design philosophy:

> **A single intrinsically-typed inductive `named_expr Γ τ` indexed by a
> named context `named_ctx Ar = seq (string * ppl_type Ar)` and a type
> `τ : ppl_type Ar`. DIRECT-STYLE CBV (Plotkin/Girard): the source
> language never mentions the probability monad. Function types are
> `tfun A B` (NOT `tprob (tfun ...)`); there is no `Ret`, no `tprob`, no
> `bind`. Variable lookup `#"x"` resolves by canonical-structure
> search (Saito–Affeldt APLAS 2023 §5.1–§5.3, §6). The denotation `eD`
> is defined DIRECTLY by structural recursion on `named_expr` with
> uniform `Tobj`-wrapped codomain (pure constructors implicit-return
> via `tunit_eta` post-composition); the value category is the FULL
> Eilenberg–Moore category `EM(!)` of the exponential comonad
> (`em_cartesian.v`), the CBV computation monad is `T = !̃ ∘ U`
> (`Tobj` in `cbv.v`), and the Kleisli exponential for `T` gives the
> higher-order arrow type denotation
> `⟦tfun A B⟧ := !̃(U A ⊸ U(T B)) = bang_cofree (linhom_car Ar
> (coalg_obj ⟦A⟧) (coalg_obj (Tobj ⟦B⟧)))` — with the `Tobj` on the
> codomain encoding the fact that every function call is potentially
> effectful in CBV. See the header of `cbv.v` for the full
> discussion of the natural-bijection chain `Hom_EM(C×A, T B) ≅
> Hom_EM(C, !̃(U A ⊸ U(T B)))` realising lambda + application.**

```coq
(* theories/programs/ppl.v *)

(** Types — direct-style CBV: no [tprob] marker. *)
Inductive ppl_type : Type :=
  | tunit
  | tbase (X : ar_obj Ar)
  | tprod (t1 t2 : ppl_type)
  | tfun  (t1 t2 : ppl_type).

(** Named contexts: each binding slot carries a string identifier.
    The PRIVATE projection [drop_names] forgets the names; it is the
    carrier on which the categorical interpretation [ctxD] lives. *)
Definition named_ctx : Type := list (string * ppl_type Ar).

Definition drop_names (G : named_ctx) : ppl_ctx Ar :=
  map snd G.

(** Named-variable witness: head, or in the tail (no string disequality
    in the WITNESS — the disequality lives in the canonical-structure
    search at the [#"x"] sites). *)
Inductive named_var : named_ctx -> ppl_type Ar -> Type :=
  | nv_head (x : string) (t : ppl_type Ar) (G : named_ctx) :
      named_var ((x, t) :: G) t
  | nv_tail (y : string) (s : ppl_type Ar) (G : named_ctx)
            (t : ppl_type Ar) (v : named_var G t) :
      named_var ((y, s) :: G) t.

(** The single inductive of expressions, named and direct-style.
    DIRECT STYLE: no [ne_ret], no [ne_bind] (replaced by the
    sequencer [ne_let]); the effectful constructors [ne_sample] and
    [ne_score] return PURE types ([tR] and [tunit] respectively) — the
    monad lives entirely in [eD], not in the source types. *)
Inductive named_expr : named_ctx Ar -> T -> Type :=
  | ne_var   (G : named_ctx Ar) (t : T) :
      named_var G t -> named_expr G t
  | ne_tt    (G : named_ctx Ar) : named_expr G tunit
  | ne_pair  (G : named_ctx Ar) (t1 t2 : T) :
      named_expr G t1 -> named_expr G t2 -> named_expr G (tprod t1 t2)
  | ne_fst   (G : named_ctx Ar) (t1 t2 : T) :
      named_expr G (tprod t1 t2) -> named_expr G t1
  | ne_snd   (G : named_ctx Ar) (t1 t2 : T) :
      named_expr G (tprod t1 t2) -> named_expr G t2
  | ne_lam   (G : named_ctx Ar) (x : string) (t1 t2 : T) :
      named_expr ((x, t1) :: G) t2 -> named_expr G (tfun t1 t2)
  | ne_app   (G : named_ctx Ar) (t1 t2 : T) :
      named_expr G (tfun t1 t2) -> named_expr G t1 -> named_expr G t2
  | ne_let   (G : named_ctx Ar) (x : string) (t1 t2 : T) :
      named_expr G t1 ->
      named_expr ((x, t1) :: G) t2 ->
      named_expr G t2
  | ne_sample (G : named_ctx Ar)
              (mu : fmeas R (ar_carrier Ar R_obj))
              (Hmu : (cone_norm mu <= 1)%R) :
      named_expr G tR'
  | ne_real  (G : named_ctx Ar) (r : R) : named_expr G tR'
  | ne_score (G : named_ctx Ar)
             (f : R -> R)
             (Hf_meas : measurable_fun [set: R] f)
             (Hf_ge0 : forall r : R, (0 <= f r)%R)
             (Hf_le1 : forall r : R, (f r <= 1)%R)
             (e : named_expr G tR') : named_expr G tunit
  | ne_add   (G : named_ctx Ar) :
      named_expr G tR' -> named_expr G tR' -> named_expr G tR'
  | ne_mul   (G : named_ctx Ar) :
      named_expr G tR' -> named_expr G tR' -> named_expr G tR'.

(** Type / context interpretation.  Direct-style CBV: the function
    type is the Kleisli exponential, with [Tobj] on the codomain. *)
Fixpoint tyD (t : ppl_type Ar) : Coalgebra Ar :=
  match t with
  | tunit       => EM_term
  | tbase X     => FMeas_coalgebra X
  | tprod s1 s2 => EM_prod (tyD s1) (tyD s2)
  | tfun A B    => bang_cofree (linhom_car Ar (coalg_obj (tyD A))
                                              (coalg_obj (Tobj (tyD B))))
  end.

Fixpoint ctxD (G : ppl_ctx Ar) : Coalgebra Ar :=
  match G with
  | nil       => EM_term
  | t :: G'   => EM_prod (ctxD G') (tyD t)
  end.

(** Arithmetic lifts via the FMeas lax-monoidal map. *)
Definition add_lift :
    icones_hom Ar
      (tensor Ar (FMeas R_obj) (FMeas R_obj))
      (FMeas R_obj) :=
  icones_comp (FMeas_fmap add_meas) (fmeas_lax R_obj R_obj).

Definition mul_lift :
    icones_hom Ar
      (tensor Ar (FMeas R_obj) (FMeas R_obj))
      (FMeas R_obj) :=
  icones_comp (FMeas_fmap mul_meas) (fmeas_lax R_obj R_obj).

Lemma add_lift_dirac (a b : R) :
  Lfun add_lift
    (ptensor (dirac_fmeas (R_to_carrier R_carrier_eq a))
             (dirac_fmeas (R_to_carrier R_carrier_eq b))) =
  dirac_fmeas (R_to_carrier R_carrier_eq (a + b)).

Lemma mul_lift_dirac (a b : R) :
  Lfun mul_lift
    (ptensor (dirac_fmeas (R_to_carrier R_carrier_eq a))
             (dirac_fmeas (R_to_carrier R_carrier_eq b))) =
  dirac_fmeas (R_to_carrier R_carrier_eq (a * b)).

(** The term-level score lift as an [icones_hom], packaging the
    measurable density [f : R -> R] (pointwise in [0,1]) as a path
    into the unit cone via the §6 follow-up
    [int_to_linhom_pres_path_in_cone]. *)
Definition score_lift :
    icones_hom Ar (FMeas R_obj) (cone_one_car Ar) :=
  linhom_icones (int_to_linhom score_path) score_int_norm_le1.

(** Load-bearing Dirac identity: on [δ_(R_to_carrier r)], the
    score lift evaluates to [f r · one1] (packaged as a
    [cone_one_car]). *)
Lemma score_lift_dirac (r : R) :
  Lfun score_lift (dirac_fmeas (R_to_carrier R_carrier_eq r)) =
  MkConeOne Ar (NngNum (Hf_ge0 r)).

(** The term interpretation [eD] — every expression is interpreted
    directly as a coalgebra Kleisli arrow
    [coalg_hom (ctxD (drop_names G)) (Tobj (tyD t))], by structural
    recursion on [named_expr]; pure constructors are wrapped through
    [tunit_eta] (the implicit return); [ne_let] is direct-style CBV
    sequencing via [kbind_ext]. *)
Fixpoint eD (G : named_ctx Ar) (t : T)
    (M : @named_expr R Ar R_obj G t) {struct M}
  : coalg_hom (ctxD (drop_names G)) (Tobj (tyD t)) :=
  match M in named_expr G0 t0
  return coalg_hom (ctxD (drop_names G0)) (Tobj (tyD t0)) with
  | ne_var _ _ v =>
      coalg_comp (tunit_eta (tyD _))
                 (var_lookup (named_var_to_has_var v))
  | ne_tt G0 =>
      coalg_comp (tunit_eta EM_term) (em_term_mor (ctxD (drop_names G0)))
  | ne_pair _ _ _ M1 M2 =>
      coalg_comp (bang_m _ _) (em_pair (eD M1) (eD M2))
  | ne_fst _ _ _ M0 => coalg_comp (Tmap (em_proj1 _ _)) (eD M0)
  | ne_snd _ _ _ M0 => coalg_comp (Tmap (em_proj2 _ _)) (eD M0)
  | ne_lam _ _ _ _ body =>
      coalg_comp (tunit_eta (tyD (tfun _ _))) (lam_coalg (eD body))
  | ne_app _ _ _ Vf Va =>
      kcomp (app_pair _ _)
        (coalg_comp (bang_m _ _) (em_pair (eD Vf) (eD Va)))
  (* Direct-style CBV [let]: same shape as the old monadic [ne_bind],
     minus the [tprob] markers on the types. *)
  | ne_let _ _ _ _ M0 K => kbind_ext (eD K) (eD M0)
  | ne_sample _ mu Hmu => @sample_kleisli _ _ mu Hmu
  | ne_real _ r        => @real_kleisli _ r
  | ne_score _ f Hf_meas Hf_ge0 Hf_le1 e0 =>
      coalg_comp (bang_cofree_hom (score_lift Hf_meas Hf_ge0 Hf_le1))
                 (eD e0)
  | ne_add _ M0 N0 =>
      coalg_comp (bang_cofree_hom add_lift)
                 (coalg_comp (bang_m _ _) (em_pair (eD M0) (eD N0)))
  | ne_mul _ M0 N0 =>
      coalg_comp (bang_cofree_hom mul_lift)
                 (coalg_comp (bang_m _ _) (em_pair (eD M0) (eD N0)))
  end.

(** The direct-style [let] reduction lemma — no [eD_ret] exists: in
    direct style every expression already denotes a Kleisli arrow,
    and there is no syntactic [return] constructor. *)
Lemma eD_let (G : named_ctx Ar) (x : string) (t1 t2 : ppl_type Ar)
    (M : named_expr G t1) (K : named_expr ((x, t1) :: G) t2) :
  eD (ne_let x M K) = kbind_ext (eD K) (eD M).
Proof. by []. Qed.

(** Variable-lookup encoding via CANONICAL STRUCTURES (Saito-Affeldt §5.2).
    [tagged_nctx] wraps [named_ctx]; [find_nv s t] pairs a tagged
    context with a [named_var]-witness; [found_nctx]/[recurse_nctx]
    drive head-first / tail-recursive search; [found_nv] is the head
    case and [recurse_nv] the tail case with an
    [infer (String.eqb s y = false)] disequality witness. *)
Structure tagged_nctx (R : realType) (Ar : MeasSubcat R) :=
  Tag_nctx { untag_nctx : named_ctx Ar }.

Structure find_nv (R : realType) (Ar : MeasSubcat R)
    (s : string) (t : ppl_type Ar) : Type := Find_nv {
  fn_ctx  : tagged_nctx Ar;
  fn_proof : named_var (untag_nctx fn_ctx) t
}.

Definition recurse_nctx (R : realType) (Ar : MeasSubcat R)
    (G : named_ctx Ar) := Tag_nctx G.
Canonical found_nctx (R : realType) (Ar : MeasSubcat R)
    (G : named_ctx Ar) := recurse_nctx G.

Canonical found_nv (R : realType) (Ar : MeasSubcat R)
    (s : string) (t : ppl_type Ar) (G : named_ctx Ar) :
    find_nv s t :=
  @Find_nv R Ar s t (found_nctx ((s, t) :: G)) (nv_head s t G).

Canonical recurse_nv (R : realType) (Ar : MeasSubcat R)
    (s : string) (t : ppl_type Ar) (y : string)
    (sty : ppl_type Ar) (Hneq : infer (String.eqb s y = false))
    (g : find_nv s t) : find_nv s t :=
  @Find_nv R Ar s t
    (recurse_nctx ((y, sty) :: untag_nctx (fn_ctx g)))
    (nv_tail y sty (untag_nctx (fn_ctx g)) (fn_proof g)).

Definition ne_var' (R : realType) (Ar : MeasSubcat R) (R_obj : ar_obj Ar)
    (s : string) (t : ppl_type Ar) (g : find_nv s t) :
    @named_expr R Ar R_obj (untag_nctx (fn_ctx g)) t :=
  ne_var (fn_proof g).

(** Surface notation — custom entry [ppl_named].  Brackets [...]
    enter the grammar, curly braces {...} escape back to Coq.
    Direct style: no [Ret] notation; [let "x" := M in N] desugars
    to [ne_let] (NOT [ne_bind]). *)
Declare Custom Entry ppl_named.

Notation "[ e ]" := e (e custom ppl_named at level 90).
Notation "{ x }" := x (in custom ppl_named at level 0, x constr).
Notation "( e )" := e
  (in custom ppl_named at level 0, e custom ppl_named).
Notation "()" := ne_tt (in custom ppl_named at level 0).
Notation "# x" :=
  (ne_var' x%string _)
  (in custom ppl_named at level 1, x constr at level 0).
Notation "[| r |]" := (ne_real r)
  (in custom ppl_named at level 1, r constr).
Notation "'Sample' ( mu , Hmu )" :=
  (ne_sample mu Hmu)
  (in custom ppl_named at level 1, mu constr, Hmu constr).
(** The ONLY score surface form, desugaring to [ne_score]. *)
Notation "'Score' '{' f ',' Hf_meas ',' Hf_ge0 ',' Hf_le1 '}' e" :=
  (ne_score f Hf_meas Hf_ge0 Hf_le1 e)
  (in custom ppl_named at level 60, e custom ppl_named at level 60,
   f constr, Hf_meas constr, Hf_ge0 constr, Hf_le1 constr,
   right associativity).
Notation "( e1 , e2 )" := (ne_pair e1 e2)
  (in custom ppl_named at level 0,
   e1 custom ppl_named at level 60,
   e2 custom ppl_named at level 60).
Notation "'fst' e" := (ne_fst e)
  (in custom ppl_named at level 10, e custom ppl_named at level 10).
Notation "'snd' e" := (ne_snd e)
  (in custom ppl_named at level 10, e custom ppl_named at level 10).
Notation "M @ N" := (ne_app M N)
  (in custom ppl_named at level 20, left associativity,
   M custom ppl_named, N custom ppl_named).
Notation "M + N" := (ne_add M N)
  (in custom ppl_named at level 40, left associativity,
   N custom ppl_named at level 39).
Notation "M * N" := (ne_mul M N)
  (in custom ppl_named at level 30, left associativity,
   N custom ppl_named at level 29).
Notation "'\' x ':::' A '=>' M" :=
  (ne_lam x%string (t1 := A) M)
  (in custom ppl_named at level 70, x constr at level 0,
   A constr at level 0,
   M custom ppl_named at level 60, right associativity).
(** Direct-style CBV let — desugars to [ne_let] (NOT [ne_bind]). *)
Notation "'let' x ':=' M 'in' N" :=
  (ne_let x%string M N)
  (in custom ppl_named at level 80, x constr at level 0,
   M custom ppl_named at level 70,
   N custom ppl_named at level 80,
   right associativity).
```

The bidirectionality hints `&` on every binding / context-shared
constructor of `named_expr` are crucial: without them,
canonical-structure lookup at `#"x"` sites would fire with an open
context metavariable and pick the wrong `find_nv` instance.

#### Code: `theories/programs/examples.v` — three QBS-style direct-style examples

The file's header docstring:

> **Three end-to-end examples for the DIRECT-STYLE named-variable PPL
> of `theories/programs/ppl.v`, each written in the `ppl_named` custom
> entry and paired with a `_denot_E` structural reduction lemma
> exposing the outer `kbind_ext`-shape of its denotation.  Direct
> style: the source language exposes no probability-monad marker.  The
> function type `tfun tR tR` (NOT `tprob (tfun tR tR)`) is itself the
> Kleisli exponential at the semantic level; all effects are implicit,
> and the `kbind_ext` structure surfaces only at the level of `eD`.**

```coq
(* theories/programs/examples.v *)

Section RandomConstant.
Variables (R : realType) (Ar : MeasSubcat R).
Variable (R_obj : ar_obj Ar).
Hypothesis R_carrier_eq : ar_carrier Ar R_obj = R :> Type.
Hypothesis R_carrier_meas :
  measurable_fun [set: ar_carrier Ar R_obj]
    (fun c : ar_carrier Ar R_obj =>
       eq_rect _ (fun T : Type => T) c _ R_carrier_eq : R).
Hypothesis R_to_carrier_meas :
  measurable_fun [set: R] (R_to_carrier R_carrier_eq).

Variable (mu : fmeas R (ar_carrier Ar R_obj)).
Hypothesis Hmu : (cone_norm mu <= 1)%R.

(** Example 1 — [ex_random_constant] in direct-style surface syntax:
    [let "c" := sample mu in λ x. c].  Note the type [tfun tR tR],
    not [tprob (tfun tR tR)]: the monad is in [eD], not the source. *)
Definition ex_random_constant :
    @named_expr R Ar R_obj nil (tfun tR' tR') :=
  [ let "c" := Sample (mu , Hmu) in \ "x" ::: tR' => # "c" ].

Lemma ex_random_constant_denot_E :
  ex_random_constant_denot =
  kbind_ext
    (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _ ex_rc_lam)
    (sample_kleisli (ctxD (drop_names nil)) mu Hmu).
End RandomConstant.

Section RandomLinear.
(* same hypothesis block as RandomConstant *)
(** Example 2 — [ex_random_linear] in direct-style surface syntax:
    [let "m" := sample mu in let "b" := sample mu in λx. m*x + b].
    Type [tfun tR tR], not [tprob (tfun tR tR)]. *)
Definition ex_random_linear :
    @named_expr R Ar R_obj nil (tfun tR' tR') :=
  [ let "m" := Sample (mu , Hmu) in
    let "b" := Sample (mu , Hmu) in
    \ "x" ::: tR' => # "m" * # "x" + # "b" ].

Lemma ex_random_linear_denot_E :
  ex_random_linear_denot =
  kbind_ext
    (kbind_ext
       (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas _ _
            ex_rl_lam)
       (sample_kleisli
          (ctxD (drop_names (("m"%string, tR') :: nil))) mu Hmu))
    (sample_kleisli (ctxD (drop_names nil)) mu Hmu).
End RandomLinear.

Section BayesLinear.
(* hypothesis block plus the score-density [f : R -> R],
   measurability, and the [0,1] pointwise bounds. *)
Variable (f : R -> R).
Hypothesis Hf_meas : measurable_fun [set: R] f.
Hypothesis Hf_ge0 : forall r : R, (0 <= f r)%R.
Hypothesis Hf_le1 : forall r : R, (f r <= 1)%R.

(** Example 3 — [ex_bayes_linear] in direct-style surface syntax:
    [let "m" := sample mu in let "_" := score { f, … } #"m" in #"m"].
    Type [tR], not [tprob tR]: the unnormalised posterior of the
    prior/score/observe shape, all effects implicit. *)
Definition ex_bayes_linear :
    @named_expr R Ar R_obj nil tR' :=
  [ let "m" := Sample (mu , Hmu) in
    let "_" := Score { f , Hf_meas , Hf_ge0 , Hf_le1 } # "m" in
    # "m" ].

Lemma ex_bayes_linear_denot_E :
  ex_bayes_linear_denot =
  kbind_ext
    (@eD R Ar R_obj R_carrier_eq R_carrier_meas R_to_carrier_meas
         _ _ ex_bl_cont)
    (sample_kleisli (ctxD (drop_names nil)) mu Hmu).
End BayesLinear.
```

The three reduction lemmas reduce by the definitional unfoldings
`eD_let` / `eD_sample` / `eD_score` of `ppl.v` (no `eD_ret` — there is
no syntactic `return` in direct style); each proof closes with
`by [].`. The examples are written **exclusively** in the `[ ... ]`
direct-style surface notation — there is no underlying De Bruijn
surface form to translate from, and no `Ret` marker at any layer.

#### Code: `theories/homs/fmeas_lax.v` + `theories/homs/bilin.v`

```coq
(* theories/homs/fmeas_lax.v *)

(** The FMeas lax symmetric monoidal comparison
    (FMeas X) ⊗ (FMeas Y) → FMeas (X × Y),
    built via [tensor_uncurry] of the bilinear outer lift. *)
Definition fmeas_lax :
    icones_hom Ar
      (tensor Ar (fmeas R (ar_carrier Ar X))
                 (fmeas R (ar_carrier Ar Y)))
      (fmeas R (ar_carrier Ar (ar_prod Ar X Y))) :=
  tensor_uncurry (fmeas_lax_outer_icones X Y).

(** Pointwise value on a pure tensor: agrees with [fmeas_lax_pre]. *)
Lemma fmeas_lax_E
    (µ : fmeas R (ar_carrier Ar X))
    (ν : fmeas R (ar_carrier Ar Y)) :
  Lfun (fmeas_lax X Y) (ptensor µ ν) = fmeas_lax_pre µ ν.

(** The load-bearing Dirac identity: makes [e_add]/[e_mul] reduce to
    scalar arithmetic on Diracs. *)
Lemma fmeas_lax_dirac (x : ar_carrier Ar X) (y : ar_carrier Ar Y) :
  Lfun (fmeas_lax X Y)
    (ptensor (dirac_fmeas x) (dirac_fmeas y)) =
  dirac_fmeas (X := ar_prod Ar X Y) (ar_prod_cast (x, y)).
```

```coq
(* theories/homs/bilin.v — the previously-deferred follow-up *)

(** Path preservation of [int_to_linhom] in the *cone* variable
    (a path of paths gives a path of integration maps). *)
Lemma int_to_linhom_pres_path_in_cone
    (Y : ar_obj Ar) (η : ar_carrier Ar Y -> path_car Ar X B) :
  is_measurable_path η ->
  is_measurable_path
    (Ar:=Ar) (C:=linhom_car Ar (fmeas R (ar_carrier Ar X)) B)
    (fun r => int_to_linhom (η r)).
```

The Kleisli-exponential structure arises from the natural-bijection chain

`Hom_EM(C × A, T B) ≅ Hom_IC(U(C × A), U B) ≅ Hom_IC(U C ⊗ U A, U B) ≅ Hom_IC(U C, U A ⊸ U B) ≅ Hom_EM(C, !̃(U A ⊸ U B))`

using only the cofree adjunction, `U` strict monoidal (`cbv_U_prod`), and
the SMCC closure of `ICones`. `EM(!)` is *not* cartesian closed (a
structural fact about EM categories of linear-exponential comonads, not a
missing diagram chase); Kleisli exponentials are what Moggi-CBV actually
needs, and that holds here axiom-free.

---

