# Goldens — 3-column overview table

## Paper § 2 — Cones

Intro paragraph.

| Paper | English statement | Rocq |
|---|---|---|
| Def 2.1 | A *precone* is an additive commutative monoid. | `precone`, `PreCone.type` — `theories/cones/precone.v` |
| Def 2.2 | A *cone* is a precone with order and norm. | `Cone.type` — `theories/cones/cone.v` |

### Def 2.1 (`isPrecone` / `Precone`)

Detail prose.

```coq
(* theories/cones/precone.v *)
HB.mixin Record isPrecone (R : realType) (P : Type) := { precone_zero : P }.
```
