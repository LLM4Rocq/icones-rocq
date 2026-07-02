# Goldens — Beyond chapter grounded with Source/Difference notes

## Beyond the paper — paper-cited meta-theorems we mechanised in full

Chapter intro.

| Item | English statement | Rocq |
|---|---|---|
| SAFT engine | Freyd's SAFT, mechanised concretely. | `wi_obj`, `wi_med` — `theories/icones/representable.v` |
| Melliès Prop 26 | Every coalgebra is a retract of its cofree. | `diagram81` — `theories/homs/em_cartesian.v` |

### SAFT engine (`wi_obj`, `wi_med`)

The left adjoint is a wide intersection of subobjects.

> **Source — Riehl, *Category Theory in Context*, Theorem 4.6.10.** Let $U$ be
> a continuous functor whose domain is complete; then $U$ admits a left adjoint.

> **Difference.** We mechanise the construction concretely.

```coq
(* theories/icones/representable.v *)
Definition wi_obj : ICone.type Ar := icones_eq wi_u wi_v.
```

### Melliès Prop 26 (`diagram81`)

Every coalgebra is a retract of its cofree coalgebra.

> **Source — Melliès, *Categorical Semantics of Linear Logic*, Proposition 26.**
> Every coalgebra induces a retraction making the retraction square commute.

> **Difference.** Records the key retraction square.

```coq
(* theories/homs/em_cartesian.v *)
Lemma diagram81 (P : Coalgebra Ar) : True.
```
