# Goldens — H3 with multiple Coq snippets

## Paper § 3 — Measurable cones

| Paper | English statement | Rocq |
|---|---|---|
| Def 3.5 | A measurable cone has a family of measurable tests. | `MCone.type` — `theories/mcones/mcone.v` |

### Def 3.5 (`isMCone` / `MCone`)

Prose A.

```coq
(* theories/mcones/mcone.v *)
HB.mixin Record isMCone := { mcone_M : Type }.
```

Prose B.

```coq
(* theories/mcones/mcone.v *)
HB.structure Definition MCone := { C of isMCone C }.
```
