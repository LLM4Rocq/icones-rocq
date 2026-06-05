# Goldens — 2-col Beyond contributions

## Beyond the paper — notable mathematical content we had to add

Chapter intro.

### Mechanisation of SAFT

Sub-section prose.

| Construction | Rocq |
|---|---|
| Subobject classifier | `SubobjClassifier`, `icones_subobject_classP` — `theories/icones/representable.v` |
| Wide intersection | `wi_obj`, `wi_med` — same file |

```coq
(* theories/icones/representable.v *)
Definition wi_obj : ICone.type Ar := icones_eq wi_u wi_v.
```
