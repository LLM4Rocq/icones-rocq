# Design note — hard (boolean) rejection sampling & conditioning

**Status:** design discussion, *not yet implemented*. This note records the
reasoning behind a proposed reformulation of the rejection-sampling /
conditioning combinators. The current code (soft, `Bernoulli`/`Score`-based)
remains as-is; nothing here has been built.

**Files referenced:**
`theories/programs/ex_reject_model.v`,
`theories/programs/examples.v`,
`theories/programs/ppl.v`,
`theories/homs/bilin.v`, `theories/homs/coalgebra.v`.

---

## 1. Starting point — what exists today

The current combinators are **soft**: acceptance/observation is a density
`f : R → [0,1]` (a `testfn R`), fed through a `Bernoulli` coin (rejection) or a
`Score` node (conditioning).

```
(* examples.v:777 — ex_reject_comb : (ta → tR) → (ta → tR) *)
reject_comb = fix rs. λ m. λ a.
  let x = m a in
  if Bernoulli (test f x) then x else rs m a

(* examples.v:874 — ex_condition_comb : (ta → tR) → (ta → tR) *)
condition_comb = λ m. λ a.
  let x = m a in
  let _ = Score (test f x) in
  x
```

with `f : testfn R` a bundled record (`ppl.v:1421`):

```coq
Record testfn := MkTestfn {
  test_fun : R -> R ;                         (* domain hardwired to R *)
  test_meas : measurable_fun [set: R] test_fun ;
  test_ge0  : forall r, 0 <= test_fun r ;
  test_le1  : forall r, test_fun r <= 1 }.
```

The model is, semantically, the promotion `g!` of a unit-ball linear map
`g : U⟦ta⟧ ⊸ FMeas`, the **only** hypothesis being
`Hg_ball : cone_norm g <= 1` (`ex_reject_model.v:314`) — i.e. the model is a
*sub-probability-honest* measure-valued map (it may sample, score, recurse, or
diverge). Its output sub-distribution at the input is
`ν_M := g(a₀) = linhom_fun g a0` (`ex_reject_model.v:385`).

Key proved results (all in `ex_reject_model.v`):

| Lemma | Statement |
|---|---|
| `reject_model_master` (:1000) | `(1 − m₀ + ∫f dν_M) · ν(U) = ∫_U f dν_M` (unconditional) |
| `reject_model_is_normalised` (:1059) | if `0 < Z` then `ν(U) = (∫_U f dν_M)/Z` |
| `reject_model_mass` (:1081) | `ν(setT) = ∫f dν_M / Z` |
| `reject_model_mass_one` (:1098) | probability model (`m₀=1`) + `0<∫f` ⟹ `ν(setT)=1` |
| `reject_model_zero` (:1115) | `f ≡ 0 ⟹ ν = precone_zero` |
| `condition_model_E` (:1692) | `⟦condition M f⟧(a)(U) = ∫_U f dν_M` |
| `reject_normalises_condition` (:2020) | `Z · ⟦reject⟧(U) = ⟦condition⟧(U)` |

with normaliser `Z := 1 − ν_M(setT) + ∫ f dν_M`.

---

## 2. Observation 1 — the return type is *not* a hypothesis

There is no `Hypothesis` that the model returns a real. The constraint is
enforced one level lower, in the **type** of the combinator. In
`ex_reject_comb` (`examples.v:780`) the model binder is `\ "m" ::: tfun ta tR'`,
so the combinator has type `(ta → tR) → (ta → tR)`, and the body only
typechecks with `x : tR` because:

- `test f # "x"` (the coin/score density) needs `# "x" : tR` (since
  `test_fun : R → R`);
- the `if` forces both branches (`# "x"` and the recursive call) to the common
  result type `tR`.

So "the model returns a real" is a **well-typedness** constraint, strictly
stronger than a logical hypothesis — a non-`tR` model cannot even be applied to
the combinator. This is why no hypothesis appears (and none could).

---

## 3. Observation 2 — the theorem holds for an arbitrary return type

Mathematically, rejection sampling is space-agnostic. For a measurable space
`B`, a sub-probability `ν_M` on `B`, and a measurable `f : B → [0,1]`:

```
(1 − ν_M(B) + ∫_B f dν_M) · ν(U) = ∫_U f dν_M,   for measurable U ⊆ B.
```

Reals appear only as the codomain `[0,1] ⊂ R` of `f` and as the scalar field of
the measures — never as the type of the produced values. The only requirements
on `B` are: it is a measurable space, and Diracs `δ_x` exist (to "return x").

The formalization is already mostly set up for this:

- The measure backbone treats the produced value abstractly — in
  `rm_case_mass` (:911), `reject_model_iter_mass` (:931), `rm_int_onem` (:883)
  the value `r` is only ever fed to `dirac_fmeas r`, `\1_U r`, and `f (cR r)`.
  No arithmetic/order/ring structure on `r` is used.
- The FMeas monad (Dirac unit + coalgebra) is **already object-generic**:
  - `dirac_fmeas (r : ar_carrier Ar X) : fmeas R (ar_carrier Ar X)` (`bilin.v:263`)
  - `Coalg_dirac (X : ar_obj Ar) r` (`coalgebra.v:141`)
  - `FMeas_coalgebra (X : ar_obj Ar)` (`coalgebra.v:317`)

The **only** `R`-specific ingredient is the test function: `testfn` is
`R → R`, and the proof applies it via the real-cast `cR := carrier_to_R`
as `f (cR r)` — `cR` exists only because the return object is *the real object*
(with its `R ≃ carrier` equation). Generalizing `testfn` to a `[0,1]`-valued
measurable map on `ar_carrier Ar B` and dropping `cR` lifts everything to an
arbitrary return type.

Note: `probObj P` stays, but only for the **coin's** `[0,1]` parameter, which is
orthogonal to the return type. A fully general version would carry two
independent parameters: the coin's real object `P` and the return object `B`.

---

## 4. Observation 3 — drop the coin/score: go boolean

For *hard* constraints we don't need the soft `[0,1]` machinery at all. Replace
the density `f : B → [0,1]` with a predicate `f : B → Bool`. A boolean predicate
is the indicator `f = 1_A` of the accept set `A := f⁻¹(true) ⊆ B`. This is the
`{0,1}` specialization of the existing soft theorem — `rm_case_mass` already
covers `f r ∈ {0,1}` (it returns `δ_r` on accept, the recursion/zero on reject).

- **Rejection** becomes a direct boolean `if` (no `Bernoulli`):
  the scrutinee `f x` is a deterministic `tBool`, dispatched by `bool_case` on a
  Dirac-on-bool.
- **Conditioning** becomes a hard `assert` (no `Score`/`testfn`):
  scoring by the `{0,1}` indicator.

---

## 5. The final combinators

```
fail      = (fix fail ::: tunit → t in λ(). fail ()) ()
assert b  = if b then () else fail            (* assert : tBool → tunit, t := tunit *)

reject    = fix rx. λ m. λ a. let x = m a in if f x then x else rx m a
condition =          λ m. λ a. let x = m a in let _ = assert (f x) in x
```

with `f : B → Bool`. Built entirely from `fix`, `λ`, `@`, `if`, `()`, `let` —
**no `Bernoulli`, `Score`, `testfn`, or `probObj` density anywhere.**

### `fail` is divergence = the zero measure

`fail` is a guarded diverging fixpoint. Why this exact shape:

- **The λ-guard is required in CBV.** `fix fail. fail` would loop at definition
  time; recursion must pass through a *value* (the lambda `λ(). fail ()`), and
  the trailing `()` triggers the unbounded unfolding `fail () → fail () → …`.
  (Same pattern as `ex_reject_comb`'s `fix "rs"`, whose body is a lambda.)
- **Denotation `⟦fail⟧ = ⊥ = precone_zero`.** The Kleene chain of
  `W = λfail. λ(). fail ()` from bottom is constant (`g₀ = ⊥`, `gₙ = ⊥`), so the
  fixpoint is `⊥`, and `⊥ () = 0` (the zero sub-distribution). This is exactly
  the `n = 0` base of the fix-sup machinery `reject` already uses
  (`fix_chain_0` / `rm_iter_0 = precone_zero`, `ex_reject_model.v:978`).

So `assert (f x); x` denotes, via the `let`-law (bind against `⟦assert (f x)⟧`):

```
bool_case (f x) δ_x 0 = [f x = true] · δ_x
```

and integrating over `ν_M` gives `ν_M(· ∩ A)`.

The `if`/`True`/`False` constructs are already in the surface
(`ppl.v:2532–2535`); `assert`/`fail` need no genuinely new primitive — only
`bool_case` + the zero measure, both already generic. (Whether `assert` is a
standalone primitive `ne_assert : tBool-expr → tunit` or pure sugar is an
ergonomics choice; semantically identical.)

---

## 6. The unifying picture

The two combinators are **the same program modulo the else-branch**:

```
reject:     if f x then x else rx m a     (* failure → retry      *)
condition:  if f x then x else fail        (* failure → give up = 0 *)
```

(`let _ = assert (f x) in x` is `if f x then x else fail`, since `assert false`
zeroes the mass regardless of the returned value.) The master identity is
precisely the bookkeeping that recursing renormalises the give-up version.

Degenerate check (always reject, `f ≡ false`): both collapse to the zero
measure — `condition = fail = 0`, `reject = retry forever = 0`. This is
`reject_model_zero` (:1115) read through the boolean lens; `fail` is not bolted
on, it is the same "divergence = zero measure" that underlies the whole story.

---

## 7. Semantics — everything is indexed by the input `a`

The denotational shorthand must carry the model input `a` (the §5 readable
statements use `M()` only because they hardwire `a := ()`/`one1`; the §2 lemmas
already quantify over an arbitrary setlike unit-ball `a₀ : U⟦ta⟧`).

For a fixed input `a`, write `ν_M^a := ⟦m⟧(a) = g(a) = linhom_fun g a` and let
`f(m a)` be the `Bool`-valued program `let x = m a in f x`. With
`A := f⁻¹(true) ⊆ B`:

```
⟦f(m a)⟧_true  = ν_M^a(A)               (model returns, test accepts)
⟦f(m a)⟧_false = ν_M^a(B ∖ A)  = q(a)   (model returns, test rejects)
m₀(a)          = ν_M^a(setT)            (model terminates at all)

Z(a)           = 1 − m₀(a) + ν_M^a(A) = 1 − ⟦f(m a)⟧_false

⟦condition m f⟧(a)(U) = ν_M^a(U ∩ A)
⟦reject    m f⟧(a)(U) = ν_M^a(U ∩ A) / Z(a)
master:  Z(a) · ⟦reject m f⟧(a)(U) = ⟦condition m f⟧(a)(U)
```

Per-trial mass decomposition (one execution of the loop body at input `a`):

```
1 = ⟦f(m a)⟧_true  +  ⟦f(m a)⟧_false  +  (1 − m₀(a))
    └ accept ──┘      └ reject/retry ┘   └ diverge ──┘
Z(a) = 1 − ⟦f(m a)⟧_false = ⟦f(m a)⟧_true + (1 − m₀(a))
```

`Z(a) = 1 − ⟦f(m a)⟧_false` is the robust form: it folds the divergence mass in
correctly (a diverging run produces *no* boolean, so it counts as neither true
nor false, hence is not subtracted).

### Evidence vs. normaliser

- **Evidence** (marginal likelihood) `= ν_M^a(A) = ⟦f(m a)⟧_true`.
- **Normaliser** `Z(a) = 1 − ⟦f(m a)⟧_false = ⟦f(m a)⟧_true + (1 − m₀(a))`.

They differ by the divergence mass `1 − m₀(a)`, and **coincide for a
probability model** (`m₀ = 1`): then `⟦f(m a)⟧_true + ⟦f(m a)⟧_false = 1`, so
`Z = ⟦f(m a)⟧_true = ν_M^a(A) =` evidence, and `reject` returns the conditional
`ν_M^a(· | A)`. This matches `reject_normalises_condition_prob` (:2055).

---

## 8. What this buys / what it costs

**Buys (relative to the soft combinators):**

- No `Bernoulli` coin in `reject`; no `Score`/`testfn` density in `condition`.
- The test no longer drags in the real object — the `po_into` / `ToProb` /
  `po_density` / `R_to_carrier_meas` plumbing drops out.
- The return type becomes free: `(ta → tb) → (ta → tb)` for arbitrary `tb`
  (nothing constrains `x`'s type but `f : tb → Bool`).
- Correctness proofs shed the density hypotheses; `rm_case_mass` etc. specialize
  to `f x ∈ {0,1}` and `rm_int_onem` becomes `ν_M(B ∖ A)` directly.
- `probObj P` is needed only if the *model* `m` samples/scores internally; the
  reject/condition *layer* is otherwise P-free.

**Costs:**

- Loses **soft** conditioning — genuine densities `f x ∈ (0,1)` (e.g. a Gaussian
  likelihood) need the `[0,1]` score, not a boolean. The boolean `assert` is the
  *hard* fragment (constraints like `x > 0`, `x = obs`).
- If both are wanted: keep `Score : tProb → tunit` as the soft core and *define*
  `assert : tBool → tunit := λ b. Score [b]` (or via `if … else fail`) on top —
  then the boolean forms are derived and the soft theorems stay intact.

---

## 9. Implementation checklist (when we build it)

1. Decide `assert` as standalone primitive (`ne_assert`) vs. sugar for
   `if b then () else fail`; either way provide `fail = (fix fail. λ(). fail ()) ()`.
2. Generalize `testfn` (or add a sibling) from `R → R` to a predicate /
   `[0,1]`-map on `ar_carrier Ar B`; drop the `carrier_to_R` cast at use sites.
3. Separate the coin/score real object (`probObj P`) from the return object `B`
   in the combinator and the §2 section variables.
4. Re-state `reject_model_master` & friends at arbitrary `B` with `f = 1_A`;
   the measure backbone and Dirac monad are already object-generic, so the
   reuse should be largely mechanical.
5. State the boolean headline: `Z(a) = 1 − ⟦f(m a)⟧_false`, evidence
   `= ⟦f(m a)⟧_true`, `⟦condition⟧(a)(U) = ν_M^a(U ∩ A)`.
