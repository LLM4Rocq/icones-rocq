# Design — rejection sampling & conditioning via a program predicate

**Status: FINAL (decided). This document is the reference for the refactor.**
If the implementation and this document disagree, this document wins.

The goal is one clean `reject` and one clean `condition` combinator, with the
acceptance test a **program** (exactly like the model), a single master theorem
that covers both hard and soft conditioning, and **no `ne_test`/`Test`, no
`test`/`Score` plumbing, and no `Bernoulli` inside the combinators**. Legacy
machinery (the soft `testfn`-based combinators, `ne_test`, the intermediate
bridge files) is removed — not kept around.

---

## 1. The core idea

A model is a program `m : a → b` (effectful: it may sample, score, recurse,
diverge). The acceptance test is **also a program**, a predicate on the model's
output value:

> `f : b → tbool`  — supplied as an argument, exactly parallel to `m`.

`f x` is then ordinary object-language application (`# "f" @ # "x"`); nothing
special is needed to "apply the test".

The one fact that makes everything work: **`tbool` is not `bool`.** It denotes a
point of the 2-point sub-probability cone (`tyD_cbv tbool = bool_cone_coalg`) —
a sub-distribution over `{true,false}`. So `f x` is the *acceptance
distribution* at `x`, and its true-mass

> `t(x) := true-mass ⟦f x⟧ ∈ [0,1]`  — the **acceptance probability** at `x`

is the only thing the combinators care about. Two regimes, one mechanism:

- `f` **deterministic** (`⟦f x⟧` a Dirac) ⇒ `t = 1_A`, the indicator of the
  accept set `A := { x | f x = true }` — **hard** conditioning.
- `f` a **coin** (`⟦f x⟧` a non-Dirac) ⇒ `t` is a density — **soft**
  conditioning.

---

## 2. The combinators (final)

```
fail      = (fix fail ::: tunit → t in λ(). fail ()) ()   -- diverges; denotes the zero measure
assert b  = if b then () else fail                        -- assert : tbool → tunit

reject    = λ f. fix rx. λ m. λ a. let x = m a in if (f x) then x else rx m a
condition = λ f.         λ m. λ a. let x = m a in let _ = assert (f x) in x
```

with `f : b → tbool` and `m : a → b` both **program arguments**. Built entirely
from `fix`, `λ`, `@`, `if`, `()`, `let`. The two combinators are the same
program modulo the else-branch:

```
reject:     if (f x) then x else rx m a     (* failure → retry      *)
condition:  if (f x) then x else fail        (* failure → give up = 0 *)
```

(`let _ = assert (f x) in x` is `if (f x) then x else fail`, since a failed
`assert` zeroes the mass whatever value follows.)

### `fail` = divergence = the zero measure

`fail` is a guarded diverging fixpoint. The λ-guard is mandatory in CBV (`fix
fail. fail` would loop at definition time; recursion must pass through a value).
Its Kleene chain from `⊥` is constant, so `⟦fail⟧ = ⊥ = precone_zero` — the zero
sub-distribution. This is the same "divergence = zero measure" already used by
the fixpoint semantics.

### No `Test`, no `test`, no `Bernoulli`, no `Score` in the combinators

- **`Test`/`ne_test` is deleted.** It only ever existed to apply a *meta-level*
  Coq predicate `carrier b → bool` to a runtime value. With `f` a **program**
  `b → tbool`, `f x` is ordinary application — no lift node is needed, so
  `ne_test` has no role and is removed (constructor, `eD_cbv` clause,
  `TestTmLiftG` section, `Test{…}` notation).
- **No `test` / `Score` plumbing.** `assert (f x)` already covers conditioning:
  it reweights by `t(x)` (see §3). When `f x` is a coin `bernoulli(s)`,
  `assert (f x); x` is definitionally `Score s; x` — so soft conditioning is the
  coin-valued case of the *same* combinator, not a separate `Score`-based one.
- **`Bernoulli`/`Score` remain as primitives** for *building* models and
  predicates (e.g. a soft predicate `f := λx. Bernoulli (density x)`), and for
  other examples — there `Bernoulli` names a genuine distribution, which is its
  only legitimate use (see §6). They are simply not part of `reject`/`condition`.

---

## 3. Semantics

Fix an input `a`; write `ν_M := ⟦m a⟧` (the model's output sub-distribution) and
`m₀ := ν_M(setT)` (its total mass; `m₀ < 1` ⇔ the model can diverge). Recall
`t(x) = true-mass ⟦f x⟧`.

One trial of `reject`/`condition` splits the unit mass three ways:

```
1  =   ∫ t dν_M    +   (m₀ − ∫ t dν_M)   +   (1 − m₀)
       └ accept ┘      └ reject / retry ┘     └ diverge ┘
```

- `condition` keeps the accepted part: `⟦condition f m⟧(a)(U) = ∫_U t dν_M`.
- `reject` retries the rejected part; summing the geometric series gives the
  normaliser `Z := 1 − m₀ + ∫ t dν_M = 1 − (retry mass)`, and
  `⟦reject f m⟧(a)(U) = (∫_U t dν_M) / Z`.

At each Dirac `δ_r` the continuation reduces by `bool_case` on `⟦f r⟧`: accept
weight `t(r) → δ_r`, reject weight `→ retry` (for `reject`) or `→ fail = 0` (for
`condition`); `fail` contributes the zero measure. This is the existing
reduction (object-generic let-law + affine cascade + `bool_case`), now with the
predicate value `f` quantified over alongside the model value `m`.

---

## 4. The master theorem (unified — one statement covers hard and soft)

For program values `m`, `f` (both unit-ball), input `a`, and `ν_M := ⟦m a⟧`,
`Z := 1 − m₀ + ∫ t dν_M`:

| name | statement |
|---|---|
| **master** | `Z · ⟦reject f m⟧(a)(U) = ∫_U t dν_M` (division-free, unconditional) |
| **normalised** | `Z > 0 ⟹ ⟦reject f m⟧(a)(U) = (∫_U t dν_M) / Z` |
| **mass** | `⟦reject f m⟧(a)(setT) = (∫ t dν_M) / Z` |
| **mass-one** | `m₀ = 1 ∧ 0 < ∫ t dν_M ⟹ ⟦reject f m⟧(a)(setT) = 1` (a.s. termination) |
| **condition** | `⟦condition f m⟧(a)(U) = ∫_U t dν_M` |
| **equivalence** | `Z · ⟦reject f m⟧(a)(U) = ⟦condition f m⟧(a)(U)` |

**Hard case** (`f` deterministic, `t = 1_A`): `⟦condition⟧(U) = ν_M(U ∩ A)` and
`⟦reject⟧(U) = ν_M(U ∩ A) / Z` — conditioning on the accept set `A`, with
`Z = 1 − m₀ + ν_M(A)`; for a probability model (`m₀ = 1`) this is the conditional
`ν_M(· | A)`. The set form needs the side fact "`f` is deterministic"
(`⟦f x⟧` a Dirac), which holds for any genuine boolean predicate.

**Soft case** (`f` a coin, `t` a density): the same identities with `t` the
density — soft conditioning / weighted rejection, no separate machinery.

---

## 5. Generality

- **Input `a` and return `b` are arbitrary** (`a → b`): `m : a → b`,
  `f : b → tbool`, `reject f m : a → b`.
- `m` and `f` are arbitrary unit-ball program values; the measure backbone
  (`dirac_fmeas`, `Coalg_dirac`, `FMeas_coalgebra`, the affine cascade, the
  object-generic let-law `eD_let_mu_E_obj`) is already object-generic, so the
  proof reuses it.

---

## 6. Terminology rule (firm)

"Bernoulli" names the genuine **Bernoulli distribution / coin** only — real
`[0,1]` randomness. A deterministic boolean test of a value is **never** a
Bernoulli; it is just a `tbool`-valued program (a `bool`-Dirac). `Bernoulli`
appears only where a genuine distribution is meant (building a soft predicate or
a model), never in `reject`/`condition`.

---

## 7. Refactor / cleanup plan

Build a clean end state; remove legacy.

**Delete**
- `ne_test` constructor + its `eD_cbv` clause + the `TestTmLiftG`/`test_lift`
  section + the `Test{…}` notation (`ppl.v`, `ppl_cbv.v`).
- The soft `testfn`-based combinators `ex_reject_comb` / `ex_condition_comb` and
  their `cbv` forms (`examples.v`), superseded by the program-predicate ones.
- The intermediate bridge files `hard_reject.v`, `hard_reject_denot.v`,
  `ex_reject_bool.v` — their content is subsumed by the clean combinators + the
  unified master theorem.

**Add / rewrite**
- The clean `reject` / `condition` / `assert` / `fail` combinators (§2), with the
  predicate a program `f : b → tbool`.
- The unified master theorem (§4) over the accept-probability
  `t(x) = true-mass ⟦f x⟧`, quantified over the program values `m`, `f`. Re-prove
  by reusing the object-generic let-law + affine cascade + `bool_case` reduction
  (the same skeleton as the current proof, with `f` an extra abstract value
  instead of a baked-in `testfn`).

**Keep**
- `Bernoulli`, `Score`, `sample` and the rest of the surface as primitives for
  building models/predicates and for the other examples.
- The measure backbone (object-generic) and the affine-cascade infrastructure.

**End state:** one `reject`, one `condition`, one master theorem, `a → b`, no
`ne_test`/`Test`, no legacy. Whole project builds; no admits; axiom budget = the
3 `boolp` classical axioms; auditor `--strict` and the auditor tests all
green.
