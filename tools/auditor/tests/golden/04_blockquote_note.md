# Goldens — blockquote note inside an H3

## Paper § 3 — Measurable cones

| Paper | English statement | Rocq |
|---|---|---|
| Def 3.20 | Path. | `path_car` — `theories/mcones/path.v` |

### Def 3.20 (`path_car`)

> **Path note.** The original table cited a wrong file; the fix is in
> this revision.

```coq
(* theories/mcones/path.v *)
Record path_car := MkPath { path_fun :> X -> B }.
```
