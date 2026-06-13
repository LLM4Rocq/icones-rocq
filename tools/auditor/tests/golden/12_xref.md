# Goldens — snippet identifier cross-references

## Paper § 2 — Cones

Intro paragraph.

| Paper | English statement | Rocq |
|---|---|---|
| Def 2.1 | The alpha gadget. | `alpha_thing`, `mu` — `theories/cones/alpha.v` |
| Def 2.2 | The beta gadget. | `beta_gadget` — `theories/cones/beta.v` |

### Def 2.1 (`alpha_thing`)

Alpha detail prose: `beta_gadget` is referenced here, as is `alpha_thing`
itself (self, suppressed), plus short `mu`, unknown `unknown_zzz` and a
math span `⟦ M ⟧ x`.

```coq
(* theories/cones/alpha.v *)
Definition alpha_thing := mu.
Lemma alpha_uses_beta : beta_gadget = alpha_thing.
Proof. by rewrite unknown_zzz. Qed.
```

### Def 2.2 (`beta_gadget`)

Beta detail prose.

```coq
(* theories/cones/beta.v -- alpha_thing in a comment stays plain *)
Definition beta_gadget := alpha_thing.
Definition beta_str := "alpha_thing in a string stays plain".
```
